import PrimeGapNormality.Prime.EndAPI
import PrimeGapNormality.Prime.Fourier
import PrimeGapNormality.Prime.Independence
import PrimeGapNormality.Prime.JointWeyl
import PrimeGapNormality.Prime.JointLift
import PrimeGapNormality.Prime.GapAbel
import PrimeGapNormality.Prime.GapPolynomialPhase
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Basic

/-!
# Algebraic Weyl packaging of gap-power components

Clock-power interleaving (`C = B^k` Weyl ⇒ base-`B` Weyl), the scalar
Wall lift, common-clock Q-independence of
`1, W_{r,d}`, periodic leading-coefficient non-cancellation, and the
coefficient identity for `mapRatPoly`. No prime-normality end theorem:
analytic Weyl means of `gapPowerComponent` remain an input.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` (eq:theta),
(eq:thetashift), (eq:noncancel), rational-coefficients subsection
(Wall lift and last-paragraph interleaving).
Contract: API
Audit: GREEN
-/

open Finset Polynomial
open Filter (Tendsto atTop)
open Function (Periodic)
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000

/-! ### Circle character and clock arithmetic -/

private theorem two_pi_I_mul (x : ℝ) :
    (2 * Real.pi * Complex.I * (x : ℂ) : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) := by
  simp [mul_comm, mul_left_comm, Complex.ofReal_mul]

private theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [two_pi_I_mul, Complex.norm_exp_I_mul_ofReal]

/-- `C = B^k ≥ 2` for integer `B ≥ 2` and `k ≥ 1`. -/
private theorem clock_pow_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) : 2 ≤ B ^ k := by
  have hsplit : k = k - 1 + 1 := (Nat.sub_add_cancel hk).symm
  rw [hsplit, pow_succ]
  have hBpos : 0 < B := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hB
  have hpowpos : 0 < B ^ (k - 1) := pow_pos hBpos _
  exact hB.trans (Nat.le_mul_of_pos_left B hpowpos)

/-- Block decomposition of a length-`k*Q` sum into `k` residue classes. -/
private theorem sum_range_mul_block (a : ℕ → ℂ) (k Q : ℕ) :
    ∑ n ∈ range (k * Q), a n =
      ∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    have hsplit :
        ∑ n ∈ range (k * (Q + 1)), a n =
          ∑ n ∈ range (k * Q), a n + ∑ r ∈ range k, a (k * Q + r) := by
      rw [Nat.mul_succ, sum_range_add]
    rw [hsplit, ih]
    have hadd :
        ∑ r ∈ range k, ∑ m ∈ range (Q + 1), a (k * m + r) =
          ∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r) +
            ∑ r ∈ range k, a (k * Q + r) := by
      simp_rw [sum_range_succ]
      rw [sum_add_distrib]
    rw [hadd]

/-- Split a length-`N` sum into complete residue blocks plus a remainder. -/
private theorem sum_range_mod_split (a : ℕ → ℂ) (k N : ℕ) :
    ∑ n ∈ range N, a n =
      ∑ r ∈ range k, ∑ m ∈ range (N / k), a (k * m + r) +
        ∑ r ∈ range (N % k), a (k * (N / k) + r) := by
  have hN : k * (N / k) + N % k = N := Nat.div_add_mod N k
  nth_rw 1 [← hN]
  rw [sum_range_add, sum_range_mul_block]

/-- Cesàro means along `k` residue classes imply the full Cesàro mean. -/
private theorem tendsto_cesaro_of_residues {k : ℕ} (hk : 0 < k) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (hres : ∀ r < k, Tendsto (fun M : ℕ =>
      (∑ m ∈ range M, a (k * m + r)) / M) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, a n) / N) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hEv :
      ∀ᶠ M in atTop, ∀ r ∈ range k,
        dist ((∑ m ∈ range M, a (k * m + r)) / M) 0 < ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro r hr
    exact (hres r (mem_range.mp hr)).eventually (Metric.ball_mem_nhds 0 hε2)
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp hEv
  obtain ⟨Nbound, hNbound⟩ := exists_nat_gt ((2 * (k : ℝ)) / ε)
  filter_upwards [Filter.eventually_ge_atTop (max (k * M0) (Nbound + 1))] with N hNge
  have hN1 : 1 ≤ N :=
    (Nat.succ_le_succ (Nat.zero_le Nbound)).trans (le_trans (le_max_right _ _) hNge)
  have hNpos : 0 < N := Nat.succ_le_iff.mp hN1
  have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hNk : k * M0 ≤ N := le_trans (le_max_left _ _) hNge
  have hQle : M0 ≤ N / k := by
    have : k * M0 / k ≤ N / k := Nat.div_le_div_right hNk
    rwa [Nat.mul_div_cancel_left M0 hk] at this
  have hNgt : Nbound + 1 ≤ N := le_trans (le_max_right _ _) hNge
  have hkN : (k : ℝ) / N < ε / 2 := by
    have hgt : (2 * (k : ℝ)) / ε < N :=
      hNbound.trans (Nat.cast_lt.mpr (Nat.lt_of_succ_le hNgt))
    have hmul : 2 * (k : ℝ) < ε * N := by
      have := (div_lt_iff₀ hε).mp hgt
      linarith
    rw [div_lt_div_iff₀ hNposR (by norm_num : (0 : ℝ) < 2)]
    linarith
  let Q : ℕ := N / k
  let R : ℕ := N % k
  have hQN : (Q : ℝ) / N ≤ 1 / k := by
    by_cases hQ0 : Q = 0
    · have : (Q : ℝ) / N = 0 := by simp [hQ0]
      rw [this]
      exact div_nonneg (by norm_num) hkR.le
    · have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ0)
      have hNeq : (N : ℝ) = (k : ℝ) * Q + (R : ℝ) := by
        exact_mod_cast (Nat.div_add_mod N k).symm
      have hge : (k : ℝ) * Q ≤ N := by
        have : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
        linarith
      have hle : (Q : ℝ) / N ≤ (Q : ℝ) / ((k : ℝ) * Q) :=
        div_le_div_of_nonneg_left hQpos.le (mul_pos hkR hQpos) hge
      have hsimp : (Q : ℝ) / ((k : ℝ) * Q) = 1 / k := by
        field_simp [hQpos.ne', hkR.ne']
      exact hle.trans_eq hsimp
  have hinner : ∀ r ∈ range k,
      ‖∑ m ∈ range Q, a (k * m + r)‖ ≤ (Q : ℝ) * (ε / 2) := by
    intro r hr
    by_cases hQ0 : Q = 0
    · simp [hQ0]
    · have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ0)
      have havg : ‖(∑ m ∈ range Q, a (k * m + r)) / Q‖ < ε / 2 := by
        simpa [dist_zero_right] using hM0 Q hQle r hr
      have hnorm :
          ‖∑ m ∈ range Q, a (k * m + r)‖ =
            (Q : ℝ) * ‖(∑ m ∈ range Q, a (k * m + r)) / Q‖ := by
        have hdiv := norm_div (∑ m ∈ range Q, a (k * m + r)) (Q : ℂ)
        have hQn : ‖(Q : ℂ)‖ = (Q : ℝ) := by simp
        rw [hdiv, hQn]
        exact (mul_div_cancel₀ _ hQpos.ne').symm
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left havg.le hQpos.le
  have hmain :
      ‖∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)‖ ≤
        (k : ℝ) * (Q : ℝ) * (ε / 2) := by
    have hle :=
      (norm_sum_le (range k) fun r => ∑ m ∈ range Q, a (k * m + r)).trans
        (sum_le_sum hinner)
    have hsumc :
        ∑ r ∈ range k, (Q : ℝ) * (ε / 2) = (k : ℝ) * (Q : ℝ) * (ε / 2) := by
      rw [sum_const, card_range, nsmul_eq_mul]
      ring
    exact hle.trans_eq hsumc
  have hrem : ‖∑ r ∈ range R, a (k * Q + r)‖ ≤ k := by
    have hsum1 : ∑ r ∈ range R, (1 : ℝ) = (R : ℝ) := by
      simp [sum_const, nsmul_eq_mul, card_range]
    have hle :=
      (norm_sum_le (range R) fun r => a (k * Q + r)).trans
        ((sum_le_sum fun _ _ => ha _).trans_eq hsum1)
    have hRle : (R : ℝ) ≤ k := (Nat.cast_lt.mpr (Nat.mod_lt N hk)).le
    exact hle.trans hRle
  have havgbound : ‖(∑ n ∈ range N, a n) / N‖ < ε := by
    have hdecomp :
        (∑ n ∈ range N, a n) / N =
          ((∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)) +
            ∑ r ∈ range R, a (k * Q + r)) / N := by
      change (∑ n ∈ range N, a n) / N =
          ((∑ r ∈ range k, ∑ m ∈ range (N / k), a (k * m + r)) +
            ∑ r ∈ range (N % k), a (k * (N / k) + r)) / N
      rw [sum_range_mod_split]
    rw [hdecomp, norm_div]
    have hNnorm : ‖(N : ℂ)‖ = N := by simp
    rw [hNnorm]
    have htri :
        ‖(∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)) +
            ∑ r ∈ range R, a (k * Q + r)‖ / N ≤
          ‖∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)‖ / N +
            ‖∑ r ∈ range R, a (k * Q + r)‖ / N := by
      have := div_le_div_of_nonneg_right
        (norm_add_le (∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r))
          (∑ r ∈ range R, a (k * Q + r))) (Nat.cast_nonneg N)
      simpa [add_div] using this
    have hmainN :
        ‖∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)‖ / N ≤ ε / 2 := by
      have hle :
          ‖∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)‖ / N ≤
            ((k : ℝ) * (Q : ℝ) * (ε / 2)) / N :=
        div_le_div_of_nonneg_right hmain (Nat.cast_nonneg N)
      have hrew : ((k : ℝ) * (Q : ℝ) * (ε / 2)) / N =
          (k : ℝ) * ((Q : ℝ) / N) * (ε / 2) := by
        ring
      have hscale :
          (k : ℝ) * ((Q : ℝ) / N) * (ε / 2) ≤
            (k : ℝ) * (1 / k) * (ε / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQN (Nat.cast_nonneg k))
          (div_nonneg hε.le (by norm_num))
      have hcancel : (k : ℝ) * (1 / k) * (ε / 2) = ε / 2 := by
        field_simp [hkR.ne']
      exact (hle.trans_eq hrew).trans (hscale.trans_eq hcancel)
    have hremN : ‖∑ r ∈ range R, a (k * Q + r)‖ / N < ε / 2 :=
      lt_of_le_of_lt (div_le_div_of_nonneg_right hrem (Nat.cast_nonneg N)) hkN
    have hεsplit : ε / 2 + ε / 2 = ε := add_halves ε
    exact lt_of_le_of_lt htri (hεsplit ▸ add_lt_add_of_le_of_lt hmainN hremN)
  simpa [dist_zero_right] using havgbound

/-- Residue-class characters for base `B` are Weyl characters for `B^k`. -/
private theorem weyl_pow_residue_phase (τ : ℤ) (B k r m : ℕ) (θ : ℝ) :
    (τ : ℝ) * (B : ℝ) ^ (k * m + r) * θ =
      (Int.cast (τ * ((B ^ r : ℕ) : ℤ)) : ℝ) * ((B ^ k : ℕ) : ℝ) ^ m * θ := by
  have hpow : (B : ℝ) ^ (k * m + r) = ((B : ℝ) ^ k) ^ m * (B : ℝ) ^ r := by
    rw [pow_add, pow_mul]
  have hk : ((B ^ k : ℕ) : ℝ) = (B : ℝ) ^ k := Nat.cast_pow B k
  have hr : ((B ^ r : ℕ) : ℝ) = (B : ℝ) ^ r := Nat.cast_pow B r
  have hτ : (Int.cast (τ * ((B ^ r : ℕ) : ℤ)) : ℝ) = (τ : ℝ) * (B ^ r : ℕ) := by
    rw [Int.cast_mul, Int.cast_natCast]
  rw [hpow, hk, hτ, hr]
  ring

/-- Residue Cesàro of `e(τ B^n θ)` is the Weyl mean at frequency `τ B^r`. -/
private theorem tendsto_weyl_residue_pow {B k : ℕ} (hB : 2 ≤ B) {θ : ℝ}
    {τ : ℤ} (hτ : τ ≠ 0) (h : weylCriterion (B ^ k) θ) (r : ℕ) :
    Tendsto (fun M : ℕ =>
      (∑ m ∈ range M, e ((τ : ℝ) * (B : ℝ) ^ (k * m + r) * θ)) / M)
      atTop (𝓝 0) := by
  have hBpos : 0 < B := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hB
  have hτ' : τ * ((B ^ r : ℕ) : ℤ) ≠ 0 :=
    mul_ne_zero hτ (Int.natCast_ne_zero.mpr (pow_ne_zero r hBpos.ne'))
  have hmode := h (τ * ((B ^ r : ℕ) : ℤ)) hτ'
  refine Tendsto.congr (fun M => ?_) hmode
  congr 1
  refine sum_congr rfl fun m _ => congrArg e ?_
  exact (weyl_pow_residue_phase τ B k r m θ).symm

/-! ### Clock power and Wall scaling -/

/-- Base-`B^k` Weyl implies base-`B` Weyl by interleaving the `k`
geometric residue sequences `B^j (B^k)^N θ`. Paper, last paragraph of
the rational-coefficients subsection.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients
(interleaving).
Contract: API
Audit: GREEN -/
theorem weylCriterion_of_pow {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) {θ : ℝ}
    (h : weylCriterion (B ^ k) θ) : weylCriterion B θ := by
  intro τ hτ
  have hkpos : 0 < k := Nat.succ_le_iff.mp hk
  let a : ℕ → ℂ := fun n => e ((τ : ℝ) * (B : ℝ) ^ n * θ)
  have ha : ∀ n, ‖a n‖ ≤ 1 := fun n => (norm_e _).le
  have hres : ∀ r < k, Tendsto (fun M : ℕ => (∑ m ∈ range M, a (k * m + r)) / M)
      atTop (𝓝 0) :=
    fun r _ => tendsto_weyl_residue_pow hB hτ h r
  simpa [a] using tendsto_cesaro_of_residues hkpos a ha hres

/-- Paper Lemma (rational affine invariance, scalar Wall): Weyl of
`q θ` to base `C ≥ 2` with integer `q ≥ 1` implies Weyl of `θ`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` Lemma (lem:wall);
`Independence.weylCriterion_of_mul`.
Contract: API
Audit: GREEN -/
theorem weylCriterion_of_nat_mul {q C : ℕ} (hq : 1 ≤ q) (hC : 2 ≤ C) {θ : ℝ}
    (h : weylCriterion C ((q : ℝ) * θ)) : weylCriterion C θ :=
  weylCriterion_of_mul hq hC h

/-- Diagonal `q_i = C-1` lift on a common clock `C = B^k`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` Lemma (lem:wall)
(invertible rational affine, common scalar clock);
`JointLift.jointWeyl_of_scaled`.
Contract: API
Audit: GREEN -/
theorem jointWeyl_of_clockScaled {B k : ℕ} {I : Type*} [Fintype I]
    [DecidableEq I] (hB : 2 ≤ B) (hk : 1 ≤ k) {θ : I → ℝ}
    (h : JointWeyl (fun _ : I => B ^ k)
      (fun i => (((B ^ k : ℕ) : ℝ) - 1) * θ i)) :
    JointWeyl (fun _ : I => B ^ k) θ :=
  jointWeyl_of_scaled (fun _ => clock_pow_ge hB hk) h

/-! ### Common-clock Q-independence of gap-power components -/

/-- Paper `W_{r+1,d}` on Lean 0-based residue `rd.1 : Fin k` and
degree `d = rd.2 + 1` (so `1 ≤ d ≤ D`).

Source: `rounds/round104/01_gpt_paper_v0_2.tex` (eq:components),
(eq:thetashift).
Contract: API
Audit: GREEN -/
noncomputable def gapPowerComponentVec (B k D : ℕ) (rd : Fin k × Fin D) : ℝ :=
  gapPowerComponent B k rd.1.val (rd.2.val + 1)

/-- `1` together with the `k D` gap-power components.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` Theorem (thm:prime)
(Q-linear independence).
Contract: API
Audit: GREEN -/
noncomputable def gapPowerComponentOne (B k D : ℕ) :
    Option (Fin k × Fin D) → ℝ :=
  fun i => Option.elim i (1 : ℝ) (gapPowerComponentVec B k D)

/-- Common-clock `JointWeyl` of the gap-power components packages
`ℚ`-independence of `1` and the components. Analytic Weyl means are
an input, not proved here.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` Theorem (thm:prime);
`JointWeyl.linearIndependent_one_jointWeyl`.
Contract: API
Audit: GREEN -/
theorem linearIndependent_one_gapPowerComponent
    {B k D : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (hW : JointWeyl (fun _ : Fin k × Fin D => B ^ k)
      (gapPowerComponentVec B k D)) :
    LinearIndependent ℚ (fun i : Option (Fin k × Fin D) =>
      Option.elim i (1 : ℝ)
        (fun rd => gapPowerComponent B k rd.1.val (rd.2.val + 1))) := by
  have hBk : 2 ≤ B ^ k := clock_pow_ge hB hk
  convert linearIndependent_one_jointWeyl (I := Fin k × Fin D)
    (θ := gapPowerComponentVec B k D) hBk hW using 1
  funext j
  cases j with
  | none => rfl
  | some _ => rfl

/-- Nonzero rational combinations of jointly Weyl gap-power components
are Weyl-normal to the common clock `B^k`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients;
`JointWeyl.weylCriterion_linearCombination`.
Contract: API
Audit: GREEN -/
theorem weylCriterion_gapPowerComponent_linearCombination
    {B k D : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) {q : Fin k × Fin D → ℚ}
    (hW : JointWeyl (fun _ : Fin k × Fin D => B ^ k)
      (gapPowerComponentVec B k D))
    (hq : ∃ i, q i ≠ 0) :
    weylCriterion (B ^ k)
      (∑ rd : Fin k × Fin D, (q rd : ℝ) * gapPowerComponentVec B k D rd) :=
  weylCriterion_linearCombination (clock_pow_ge hB hk) hW hq

/-- Interleave the common clock: a nonzero rational combination of the
components is Weyl-normal to base `B`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients
(last paragraph).
Contract: API
Audit: GREEN -/
theorem weylCriterion_gapPowerComponent_base
    {B k D : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) {q : Fin k × Fin D → ℚ}
    (hW : JointWeyl (fun _ : Fin k × Fin D => B ^ k)
      (gapPowerComponentVec B k D))
    (hq : ∃ i, q i ≠ 0) :
    weylCriterion B
      (∑ rd : Fin k × Fin D, (q rd : ℝ) * gapPowerComponentVec B k D rd) :=
  weylCriterion_of_pow hB hk
    (weylCriterion_gapPowerComponent_linearCombination hB hk hW hq)

/-! ### Periodic leading-coefficient non-cancellation -/

private theorem one_add_neg_one_pow_div_ne_zero {B R : ℕ} (hB : 2 ≤ B) :
    1 + (-1 : ℝ) ^ R / B ≠ 0 := by
  have hb0 : (B : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hB))
  have hB1 : (1 : ℝ) < B :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hB)
  have hBsub : (B : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hB1.ne'
  have hBadd : (B : ℝ) + 1 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) < 1)).ne'
  by_cases hEven : Even R
  · have h1 : (-1 : ℝ) ^ R = 1 := Even.neg_one_pow hEven
    rw [h1]
    have : 1 + (1 : ℝ) / B = (B + 1) / B := by field_simp [hb0]
    rw [this]
    exact div_ne_zero hBadd hb0
  · have hOdd : Odd R := Nat.not_even_iff_odd.mp hEven
    have h1 : (-1 : ℝ) ^ R = -1 := Odd.neg_one_pow hOdd
    rw [h1]
    have : 1 + (-1 : ℝ) / B = (B - 1) / B := by
      field_simp [hb0]
      ring
    rw [this]
    exact div_ne_zero hBsub hb0

/-- Paper (eq:noncancel): at a maximizer residue,
`|a_r + (-1)^R a_{r+1}/B| ≥ (1-1/B) max |a|`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` (eq:noncancel);
`GapAbel.maxNorm_twoTerm_ge`.
Contract: API
Audit: GREEN -/
theorem maxNorm_signedTwoTerm_ge {B k r R : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (a : ℕ → ℝ) (ha : Periodic a k) (hr : r ∈ Icc 1 k)
    (hmax : ∀ i ∈ Icc 1 k, |a i| ≤ |a r|) :
    (1 - (1 : ℝ) / B) * |a r| ≤
      |a r + (-1 : ℝ) ^ R * a (r + 1) / B| := by
  obtain ⟨hplus, hminus⟩ := maxNorm_twoTerm_ge hB hk a ha hr hmax
  by_cases hE : Even R
  · have h1 : (-1 : ℝ) ^ R = 1 := Even.neg_one_pow hE
    simpa [h1] using hplus
  · have hO : Odd R := Nat.not_even_iff_odd.mp hE
    have h1 : (-1 : ℝ) ^ R = -1 := Odd.neg_one_pow hO
    have hrew :
        a r + (-1 : ℝ) * a (r + 1) / B = a r - a (r + 1) / B := by
      ring
    rw [h1, hrew]
    exact hminus

/-- Strict non-cancellation when the maximizer mass is nonzero.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` (eq:noncancel);
`GapAbel.maxNorm_twoTerm_ne_zero`.
Contract: API
Audit: GREEN -/
theorem maxNorm_signedTwoTerm_ne_zero {B k r R : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (a : ℕ → ℝ) (ha : Periodic a k) (hr : r ∈ Icc 1 k)
    (hmax : ∀ i ∈ Icc 1 k, |a i| ≤ |a r|) (hM : a r ≠ 0) :
    a r + (-1 : ℝ) ^ R * a (r + 1) / B ≠ 0 := by
  have hB1 : (1 : ℝ) < B :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hB)
  have hfac : 0 < 1 - (1 : ℝ) / B := by
    have : (1 : ℝ) / B < 1 :=
      (div_lt_one (lt_trans (by norm_num : (0 : ℝ) < 1) hB1)).mpr hB1
    linarith
  have hpos : 0 < (1 - (1 : ℝ) / B) * |a r| :=
    mul_pos hfac (abs_pos.mpr hM)
  have hge := maxNorm_signedTwoTerm_ge (R := R) hB hk a ha hr hmax
  exact abs_pos.mp (hpos.trans_le hge)

/-- Re-export: the free two-term leading coefficient is never zero for
`B ≥ 2` and `natDegree P ≥ 1`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` (eq:freephase);
`GapPolynomialPhase.freeGapPolyPoly_leadingCoeff`.
Contract: API
Audit: GREEN -/
theorem freeGapPolyPoly_leadingCoeff_ne_zero (P : ℝ[X]) {B j : ℕ}
    (hB : 2 ≤ B) (hR : 1 ≤ natDegree P) (a c : ℝ) :
    leadingCoeff (freeGapPolyPoly P B j a c) ≠ 0 := by
  rw [freeGapPolyPoly_leadingCoeff P hB hR a c]
  have hb0 : (B : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hB))
  have hP0 : P ≠ 0 := ne_zero_of_natDegree_gt (Nat.succ_le_iff.mp hR)
  exact mul_ne_zero
    (mul_ne_zero (leadingCoeff_ne_zero.mpr hP0) (inv_ne_zero (pow_ne_zero _ hb0)))
    (one_add_neg_one_pow_div_ne_zero (R := natDegree P) hB)

/-! ### Rational polynomials: evaluation and clearing denominators -/

/-- `mapRatPoly` evaluates as `eval₂ (algebraMap ℚ ℝ)`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients.
Contract: API
Audit: GREEN -/
theorem eval_mapRatPoly (P : ℚ[X]) (x : ℝ) :
    eval x (mapRatPoly P) = eval₂ (algebraMap ℚ ℝ) x P := by
  unfold mapRatPoly
  exact eval_map (algebraMap ℚ ℝ) x

/-- Same identity as `aeval`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients.
Contract: API
Audit: GREEN -/
theorem eval_mapRatPoly_aeval (P : ℚ[X]) (x : ℝ) :
    eval x (mapRatPoly P) = aeval x P := by
  rw [eval_mapRatPoly, aeval_def]

/-- Coefficients of `mapRatPoly P` are the coerced rational coefficients.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients.
Contract: API
Audit: GREEN -/
theorem mapRatPoly_coeff (P : ℚ[X]) (n : ℕ) :
    (mapRatPoly P).coeff n = (P.coeff n : ℝ) := by
  unfold mapRatPoly
  rw [coeff_map]
  simp

/-- Coefficient expansion of a rational polynomial over `ℝ`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients.
Contract: API
Audit: GREEN -/
theorem eval_mapRatPoly_sum (P : ℚ[X]) (x : ℝ) :
    eval x (mapRatPoly P) =
      ∑ i ∈ range (P.natDegree + 1), (P.coeff i : ℝ) * x ^ i := by
  rw [eval_mapRatPoly, eval₂_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  simp

/-- Product of coefficient denominators, used to clear denominators.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients
(clearing denominators).
Contract: API
Audit: GREEN -/
noncomputable def ratPolyDenProd (P : ℚ[X]) : ℕ :=
  ∏ i ∈ range (P.natDegree + 1), (P.coeff i).den

private theorem ratPolyDenProd_mul_coeff (P : ℚ[X]) {i : ℕ}
    (hi : i ∈ range (P.natDegree + 1)) :
    (ratPolyDenProd P : ℝ) * (P.coeff i : ℝ) =
      (((P.coeff i).num *
        (∏ j ∈ (range (P.natDegree + 1)).erase i, (P.coeff j).den : ℕ) : ℤ) : ℝ) := by
  unfold ratPolyDenProd
  have hprod :
      (∏ j ∈ range (P.natDegree + 1), (P.coeff j).den) =
        (P.coeff i).den *
          ∏ j ∈ (range (P.natDegree + 1)).erase i, (P.coeff j).den :=
    (mul_prod_erase (range (P.natDegree + 1)) (fun j => (P.coeff j).den) hi).symm
  rw [hprod]
  have hden : ((P.coeff i).den : ℝ) * (P.coeff i : ℝ) = ((P.coeff i).num : ℝ) := by
    exact_mod_cast (P.coeff i).den_mul_eq_num
  push_cast
  calc
    ((P.coeff i).den : ℝ) *
          (∏ j ∈ (range (P.natDegree + 1)).erase i, (P.coeff j).den : ℝ) *
          (P.coeff i : ℝ)
        = (((P.coeff i).den : ℝ) * (P.coeff i : ℝ)) *
            (∏ j ∈ (range (P.natDegree + 1)).erase i, (P.coeff j).den : ℝ) := by
          ring
    _ = ((P.coeff i).num : ℝ) *
            (∏ j ∈ (range (P.natDegree + 1)).erase i, (P.coeff j).den : ℝ) := by
          rw [hden]

/-- Clearing denominators: a rational polynomial evaluation is a
rational multiple of an integer linear combination of monomials.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients
(clearing denominators).
Contract: API
Audit: GREEN -/
theorem eval_mapRatPoly_clearDenoms (P : ℚ[X]) (x : ℝ) :
    (ratPolyDenProd P : ℝ) * eval x (mapRatPoly P) =
      ∑ i ∈ range (P.natDegree + 1),
        (((P.coeff i).num *
          (∏ j ∈ (range (P.natDegree + 1)).erase i, (P.coeff j).den : ℕ) : ℤ) : ℝ) *
          x ^ i := by
  rw [eval_mapRatPoly_sum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_assoc, ratPolyDenProd_mul_coeff P hi]

/-- Coefficient identity for one gap-polynomial summand.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients.
Contract: API
Audit: GREEN -/
theorem gapRatPoly_eval_sum (P : ℕ → ℚ[X]) (B n : ℕ) :
    eval (primeGap n : ℝ) (mapRatPoly (P n)) / (B : ℝ) ^ (n + 1) =
      ∑ i ∈ range ((P n).natDegree + 1),
        ((P n).coeff i : ℝ) *
          ((primeGap n : ℝ) ^ i / (B : ℝ) ^ (n + 1)) := by
  rw [eval_mapRatPoly_sum, sum_div]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_div_assoc]

/-- A constant rational polynomial series is the corresponding rational
linear combination of integer-power gap series, assuming summability of
each power series.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` rational coefficients.
Contract: API
Audit: GREEN -/
theorem gapRatPolySeries_eq_linearCombination (P : ℚ[X]) (B : ℕ)
    (hsm : ∀ i ∈ range (P.natDegree + 1),
      Summable fun n : ℕ =>
        ((primeGap n : ℝ) ^ i) / (B : ℝ) ^ (n + 1)) :
    gapRatPolySeries (fun _ => P) B =
      ∑ i ∈ range (P.natDegree + 1),
        (P.coeff i : ℝ) * primeGapPowerSeries B i := by
  unfold gapRatPolySeries gapPolySeries primeGapPowerSeries
  have hterm : ∀ n : ℕ,
      eval (primeGap n : ℝ) (mapRatPoly P) / (B : ℝ) ^ (n + 1) =
        ∑ i ∈ range (P.natDegree + 1),
          (P.coeff i : ℝ) *
            ((primeGap n : ℝ) ^ i / (B : ℝ) ^ (n + 1)) :=
    fun n => gapRatPoly_eval_sum (fun _ => P) B n
  simp_rw [hterm]
  have hf : ∀ i ∈ range (P.natDegree + 1),
      Summable fun n : ℕ =>
        (P.coeff i : ℝ) *
          ((primeGap n : ℝ) ^ i / (B : ℝ) ^ (n + 1)) :=
    fun i hi => (hsm i hi).mul_left (P.coeff i : ℝ)
  rw [Summable.tsum_finsetSum hf]
  refine sum_congr rfl fun i hi => ?_
  exact (hsm i hi).tsum_mul_left (P.coeff i : ℝ)

/-! ### Named end-proposition (definition only) -/

/-- Conditional gap-polynomial normality: `AHL κ d0` implies base-`B`
Weyl normality of `gapPolySeries P B`. The paper parameters `D` and `k`
record the intended degree/period; they do not enter the proposition.
This is not an axiom and is not proved here.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` Theorem (thm:prime).
Contract: API
Audit: GREEN -/
def PrimeGapPolyNormal (κ d0 : ℝ) (B D k : ℕ) (P : ℕ → ℝ[X]) : Prop :=
  let _ := D
  let _ := k
  AHL κ d0 → weylCriterion B (gapPolySeries P B)

end PrimeGapNormality.Prime
