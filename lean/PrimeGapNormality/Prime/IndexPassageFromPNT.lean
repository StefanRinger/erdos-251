import PrimeGapNormality.Prime.PrimeSTD
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pack hyp `IndexPassageD nthPrime` from `ψ(N)/N → 1`

Does not import `PrimeNumberTheoremAnd.Wiener.WeakPNT`. The analytic
input is an explicit hypothesis
`Tendsto (fun N => cumsum (fun n => Λ n) N / N) atTop (𝓝 1)`,
i.e. the discrete Chebyshev function `ψ(N)/N → 1`.

Chain: `ψ(N)/N → 1` ⇒ `ψ(x) ∼ x` ⇒ `θ(x) ∼ x` (mathlib
`|ψ-θ| = O(√x)`) ⇒ `π(⌊x⌋) ∼ x/log x` (mathlib Chebyshev identity
remainder `π - θ/log = O(x/log² x) = o(x/log x)`) ⇒
`π(p_M) = M+1 ∼ p_M/log p_M` ⇒ `π(2 p_M)/M → 2`, which is
`IndexPassageD nthPrime` via `indexPassageD_nthPrime_iff_tendsto_two`.

Indexing: Lean `nthPrime 0 = 2` is paper `p_1`, so `π(p_M) = M+1`.
No claim Kuperberg → Weyl.

Source: `PrimeSTD.indexPassageD_nthPrime_iff_tendsto_two`;
`ChebyshevNthPrime`; mathlib `NumberTheory.Chebyshev`.
Contract: API
Audit: GREEN
-/

open Finset Filter Asymptotics
open scoped Topology Asymptotics ArithmeticFunction

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### Discrete Chebyshev prefix (`cumsum` matches PNT+ `range`) -/

/-- Prefix sum on `range`, matching PNT+ `cumsum`. `Λ 0 = 0`. -/
def cumsum {E : Type*} [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E :=
  ∑ i ∈ range n, u i

/-- `π(⌊x⌋) / (x / log x) → 1`. Isolated so the index inversion can
cite it independently of the `ψ → θ → π` Chebyshev identity. -/
def PrimeCountingAsymp : Prop :=
  Tendsto (fun x : ℝ =>
      (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x))
    atTop (𝓝 1)

private theorem psi_nat_eq_cumsum_succ (N : ℕ) :
    Chebyshev.psi (N : ℝ) = cumsum (fun n => Λ n) (N + 1) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, cumsum,
    ← Nat.range_succ_eq_Icc_zero]

private theorem tendsto_succ_div_self :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / N) atTop (𝓝 1) := by
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) + 1 / N) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      tendsto_one_div_atTop_nhds_zero_nat
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  have hN1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := Nat.cast_add_one N
  rw [hN1]
  field_simp [hN0]

/-- Discrete `ψ(N)/N → 1` from the `cumsum Λ` form of Weak PNT. -/
theorem tendsto_psi_nat_div_of_cumsum
    (hψ : Tendsto (fun N : ℕ => cumsum (fun n => Λ n) N / N) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => Chebyshev.psi (N : ℝ) / N) atTop (𝓝 1) := by
  have hsucc :
      Tendsto (fun N : ℕ =>
        cumsum (fun n => Λ n) (N + 1) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 1) :=
    hψ.comp (tendsto_add_atTop_nat 1)
  have heq :
      (fun N : ℕ => Chebyshev.psi (N : ℝ) / N) =ᶠ[atTop]
        fun N =>
          cumsum (fun n => Λ n) (N + 1) / ((N + 1 : ℕ) : ℝ) *
            (((N + 1 : ℕ) : ℝ) / N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
    have hN1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero N
    rw [psi_nat_eq_cumsum_succ]
    field_simp [hN0, hN1]
  have hmul := hsucc.mul tendsto_succ_div_self
  have hg := hmul.congr' heq.symm
  simpa [mul_one] using hg

/-- Real `ψ(x)/x → 1` by the floor sandwich `ψ(x) = ψ(⌊x⌋)`. -/
theorem tendsto_psi_div_self_of_cumsum
    (hψ : Tendsto (fun N : ℕ => cumsum (fun n => Λ n) N / N) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  have hnat := tendsto_psi_nat_div_of_cumsum hψ
  have hfloor :
      Tendsto (fun x : ℝ => Chebyshev.psi (⌊x⌋₊ : ℝ) / (⌊x⌋₊ : ℝ))
        atTop (𝓝 1) :=
    hnat.comp tendsto_nat_floor_atTop
  have heq :
      (fun x : ℝ => Chebyshev.psi x / x) =ᶠ[atTop]
        fun x =>
          Chebyshev.psi (⌊x⌋₊ : ℝ) / (⌊x⌋₊ : ℝ) * ((⌊x⌋₊ : ℝ) / x) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hψx : Chebyshev.psi x = Chebyshev.psi (⌊x⌋₊ : ℝ) :=
      Chebyshev.psi_eq_psi_coe_floor x
    have hfloor1 : (1 : ℕ) ≤ ⌊x⌋₊ :=
      (Nat.le_floor_iff (by linarith)).2 (by simpa [Nat.cast_one] using hx)
    have hpos : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hfloor1
    have hx0 : x ≠ 0 := by linarith
    rw [hψx]
    field_simp [hpos.ne', hx0]
  have hmul := hfloor.mul tendsto_nat_floor_div_atTop
  have hg := hmul.congr' heq.symm
  simpa [mul_one] using hg

theorem isEquivalent_psi_id_of_cumsum
    (hψ : Tendsto (fun N : ℕ => cumsum (fun n => Λ n) N / N) atTop (𝓝 1)) :
    Chebyshev.psi ~[atTop] fun x : ℝ => x :=
  isEquivalent_of_tendsto_one (tendsto_psi_div_self_of_cumsum hψ)

private theorem isLittleO_sqrt_id :
    (Real.sqrt : ℝ → ℝ) =o[atTop] fun x : ℝ => x := by
  refine (isLittleO_iff_tendsto fun x hx => ?_).mpr ?_
  · change x = 0 at hx
    rw [hx, Real.sqrt_zero]
  · have hinv : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
    have hsq : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx.le).symm
    calc
      (Real.sqrt x)⁻¹ = (1 : ℝ) / Real.sqrt x := inv_eq_one_div _
      _ = (Real.sqrt x / Real.sqrt x) / Real.sqrt x := by rw [← div_self hne]
      _ = Real.sqrt x / (Real.sqrt x * Real.sqrt x) := div_div _ _ _
      _ = Real.sqrt x / x := by rw [← hsq]

/-- `θ(x) ∼ x` from `ψ ∼ x` and mathlib `ψ - θ = O(√x)`. -/
theorem isEquivalent_theta_id_of_cumsum
    (hψ : Tendsto (fun N : ℕ => cumsum (fun n => Λ n) N / N) atTop (𝓝 1)) :
    Chebyshev.theta ~[atTop] fun x : ℝ => x := by
  have hψid := isEquivalent_psi_id_of_cumsum hψ
  have hdiff : (Chebyshev.psi - Chebyshev.theta) =o[atTop] fun x : ℝ => x :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO isLittleO_sqrt_id
  have h := hψid.sub_isLittleO hdiff
  refine h.congr_left ?_
  refine Eventually.of_forall fun x => ?_
  simp only [Pi.sub_apply]
  ring

private theorem isLittleO_id_div_log_sq :
    (fun x : ℝ => x / Real.log x ^ 2) =o[atTop]
      fun x => x / Real.log x := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx hg
    have hpos : 0 < x / Real.log x :=
      div_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)
    exact (hpos.ne' hg).elim
  · have hinv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp [hx0, hlog]

/-- Chebyshev identity: `θ ∼ id` ⇒ `π(⌊x⌋) ∼ x / log x`. -/
theorem primeCountingAsymp_of_theta
    (hθ : Chebyshev.theta ~[atTop] fun x : ℝ => x) :
    PrimeCountingAsymp := by
  have hx0 : ∀ᶠ x : ℝ in atTop, x ≠ 0 :=
    (eventually_gt_atTop (0 : ℝ)).mono fun _ hx => hx.ne'
  have hθdiv : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hx0).mp hθ
  have hθlog :
      (fun x : ℝ => Chebyshev.theta x / Real.log x) ~[atTop]
        fun x => x / Real.log x := by
    refine isEquivalent_of_tendsto_one ?_
    refine hθdiv.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0' : x ≠ 0 := by linarith
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    simp only [Pi.div_apply]
    rw [div_div_eq_mul_div, div_mul_cancel₀ _ hlog]
  have hrem :
      (fun x : ℝ =>
          (Nat.primeCounting ⌊x⌋₊ : ℝ) -
            Chebyshev.theta x / Real.log x) =o[atTop]
        fun x => x / Real.log x :=
    Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO
      isLittleO_id_div_log_sq
  have hπeq :
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
        fun x => x / Real.log x := by
    have hadd := hθlog.add_isLittleO hrem
    refine hadd.congr_left ?_
    refine Eventually.of_forall fun x => ?_
    simp only [Pi.add_apply]
    ring
  have hne : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_ne_zero (by linarith) (Real.log_pos hx).ne'
  have hT := (isEquivalent_iff_tendsto_one hne).mp hπeq
  exact hT

theorem primeCountingAsymp_of_psi
    (hψ : Tendsto (fun N : ℕ => cumsum (fun n => Λ n) N / N) atTop (𝓝 1)) :
    PrimeCountingAsymp :=
  primeCountingAsymp_of_theta (isEquivalent_theta_id_of_cumsum hψ)

/-! ### Inversion: `π ∼ x/log x` ⇒ `π(2 p_M)/M → 2` -/

/-- `a / c = (a / b) * (b / c)`. -/
private theorem div_mul_div_cancel_right_of_ne (a b c : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    a / c = a / b * (b / c) := by
  field_simp [hb, hc]

private theorem one_lt_two_mul_nthPrime (M : ℕ) :
    (1 : ℝ) < 2 * (nthPrime M : ℝ) := by
  have h : (1 : ℝ) < nthPrime M := nthPrime_one_lt_cast M
  linarith

private theorem two_mul_nthPrime_div_log_ne_zero (M : ℕ) :
    (2 : ℝ) * nthPrime M / Real.log (2 * (nthPrime M : ℝ)) ≠ 0 :=
  div_ne_zero (mul_ne_zero (by norm_num) (nthPrime_cast_pos M).ne')
    (Real.log_pos (one_lt_two_mul_nthPrime M)).ne'

private theorem tendsto_succ_self_div :
    Tendsto (fun M : ℕ => ((M : ℝ) + 1) / M) atTop (𝓝 1) := by
  have h := tendsto_succ_div_self
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  rw [Nat.cast_add_one]

/-- `π(p_M)/(p_M/log p_M) → 1`, hence `(M+1) log p_M / p_M → 1`. -/
theorem tendsto_succ_mul_log_div_nthPrime_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    Tendsto (fun M : ℕ =>
        ((M : ℝ) + 1) /
          ((nthPrime M : ℝ) / Real.log (nthPrime M : ℝ)))
      atTop (𝓝 1) := by
  have hcomp := hπ.comp tendsto_nthPrime_cast_atTop
  refine hcomp.congr' ?_
  filter_upwards with M
  simp [Function.comp_apply, Nat.floor_natCast, primeCounting_nthPrime,
    Nat.cast_add_one]

theorem tendsto_nthPrime_div_log_div_self_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    Tendsto (fun M : ℕ =>
        ((nthPrime M : ℝ) / Real.log (nthPrime M : ℝ)) / M)
      atTop (𝓝 1) := by
  have hmain :=
    tendsto_succ_mul_log_div_nthPrime_of_primeCountingAsymp hπ
  have hinv : Tendsto (fun M : ℕ =>
      (((M : ℝ) + 1) /
          ((nthPrime M : ℝ) / Real.log (nthPrime M : ℝ)))⁻¹)
      atTop (𝓝 1) := by
    simpa using hmain.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hinv1 : Tendsto (fun M : ℕ =>
      ((nthPrime M : ℝ) / Real.log (nthPrime M : ℝ)) / ((M : ℝ) + 1))
      atTop (𝓝 1) := by
    refine hinv.congr' ?_
    filter_upwards with M
    rw [inv_div]
  have heq :
      (fun M : ℕ =>
          ((nthPrime M : ℝ) / Real.log (nthPrime M : ℝ)) / M) =ᶠ[atTop]
        fun M =>
          ((nthPrime M : ℝ) / Real.log (nthPrime M : ℝ)) / ((M : ℝ) + 1) *
            (((M : ℝ) + 1) / M) := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)
    have hM1 : (M : ℝ) + 1 ≠ 0 := by linarith
    exact div_mul_div_cancel_right_of_ne
      ((nthPrime M : ℝ) / Real.log (nthPrime M : ℝ))
      ((M : ℝ) + 1) (M : ℝ) hM1 hM0
  have hmul := hinv1.mul tendsto_succ_self_div
  have hg := hmul.congr' heq.symm
  simpa [mul_one] using hg

private theorem two_mul_div_log_div_self_eq (M : ℕ) (hM : (M : ℝ) ≠ 0) :
    ((2 : ℝ) * nthPrime M / Real.log (2 * (nthPrime M : ℝ))) / M =
      (2 : ℝ) *
        (((nthPrime M : ℝ) / Real.log (nthPrime M : ℝ)) / M) *
        (Real.log (nthPrime M : ℝ) /
          Real.log (2 * (nthPrime M : ℝ))) := by
  set p : ℝ := (nthPrime M : ℝ)
  set L : ℝ := Real.log p
  set L2 : ℝ := Real.log (2 * p)
  set m : ℝ := (M : ℝ)
  have hp : p ≠ 0 := (nthPrime_cast_pos M).ne'
  have hL : L ≠ 0 := (Real.log_pos (nthPrime_one_lt_cast M)).ne'
  have hL2 : L2 ≠ 0 := (Real.log_pos (one_lt_two_mul_nthPrime M)).ne'
  have hleft : (2 * p / L2) / m = 2 * p / (L2 * m) := div_div _ _ _
  have hright :
      (2 : ℝ) * ((p / L) / m) * (L / L2) = 2 * p / (L2 * m) := by
    have hinner : (p / L) / m = p / (L * m) := div_div _ _ _
    rw [hinner]
    field_simp [hp, hL, hL2, hM]
  exact hleft.trans hright.symm

theorem tendsto_two_nthPrime_div_log_div_self_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    Tendsto (fun M : ℕ =>
        ((2 : ℝ) * nthPrime M / Real.log (2 * (nthPrime M : ℝ))) / M)
      atTop (𝓝 2) := by
  have hp := tendsto_nthPrime_div_log_div_self_of_primeCountingAsymp hπ
  have hlog := tendsto_log_nthPrime_div_log_two_mul
  have hmul :
      Tendsto (fun M : ℕ =>
          (2 : ℝ) *
            (((nthPrime M : ℝ) / Real.log (nthPrime M : ℝ)) / M) *
            (Real.log (nthPrime M : ℝ) /
              Real.log (2 * (nthPrime M : ℝ))))
        atTop (𝓝 2) := by
    have h := ((tendsto_const_nhds (x := (2 : ℝ))).mul hp).mul hlog
    simpa using h
  have heq :
      (fun M : ℕ =>
          ((2 : ℝ) * nthPrime M / Real.log (2 * (nthPrime M : ℝ))) / M) =ᶠ[atTop]
        fun M =>
          (2 : ℝ) *
            (((nthPrime M : ℝ) / Real.log (nthPrime M : ℝ)) / M) *
            (Real.log (nthPrime M : ℝ) /
              Real.log (2 * (nthPrime M : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    exact two_mul_div_log_div_self_eq M
      (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM))
  exact hmul.congr' heq.symm

theorem tendsto_primeCounting_two_nthPrime_div_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    Tendsto (fun M : ℕ => (Nat.primeCounting (2 * nthPrime M) : ℝ) / M)
      atTop (𝓝 2) := by
  have hxNat : Tendsto (fun M : ℕ => ((2 * nthPrime M : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_two_mul_nthPrime_atTop
  have hx : Tendsto (fun M : ℕ => (2 : ℝ) * (nthPrime M : ℝ)) atTop atTop :=
    hxNat.congr fun M => two_mul_nthPrime_cast M
  have hcomp := hπ.comp hx
  have hratio :
      Tendsto (fun M : ℕ =>
          (Nat.primeCounting (2 * nthPrime M) : ℝ) /
            ((2 : ℝ) * nthPrime M / Real.log (2 * (nthPrime M : ℝ))))
        atTop (𝓝 1) := by
    refine hcomp.congr' ?_
    filter_upwards with M
    have hfloor : ⌊(2 : ℝ) * nthPrime M⌋₊ = 2 * nthPrime M := by
      rw [← two_mul_nthPrime_cast, Nat.floor_natCast]
    simp [Function.comp_apply, hfloor]
  have hscale :=
    tendsto_two_nthPrime_div_log_div_self_of_primeCountingAsymp hπ
  have heq :
      (fun M : ℕ => (Nat.primeCounting (2 * nthPrime M) : ℝ) / M) =ᶠ[atTop]
        fun M =>
          (Nat.primeCounting (2 * nthPrime M) : ℝ) /
              ((2 : ℝ) * nthPrime M / Real.log (2 * (nthPrime M : ℝ))) *
            (((2 : ℝ) * nthPrime M / Real.log (2 * (nthPrime M : ℝ))) / M) := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)
    exact div_mul_div_cancel_right_of_ne
      (Nat.primeCounting (2 * nthPrime M) : ℝ)
      ((2 : ℝ) * nthPrime M / Real.log (2 * (nthPrime M : ℝ)))
      (M : ℝ) (two_mul_nthPrime_div_log_ne_zero M) hM0
  have hmul := hratio.mul hscale
  have hg := hmul.congr' heq.symm
  simpa [one_mul] using hg

/-- Paper D on `nthPrime` from the Chebyshev-identity form `π ∼ x/log x`. -/
theorem indexPassageD_nthPrime_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    IndexPassageD nthPrime := by
  rw [indexPassageD_nthPrime_iff, indexPassage_iff_tendsto_two]
  exact tendsto_primeCounting_two_nthPrime_div_of_primeCountingAsymp hπ

/-- Pack hyp `IndexPassageD nthPrime` from `ψ(N)/N → 1`. -/
theorem indexPassageD_nthPrime_of_psi
    (hψ : Tendsto (fun N : ℕ => cumsum (fun n => Λ n) N / N) atTop (𝓝 1)) :
    IndexPassageD nthPrime :=
  indexPassageD_nthPrime_of_primeCountingAsymp (primeCountingAsymp_of_psi hψ)

end PrimeGapNormality.Prime
