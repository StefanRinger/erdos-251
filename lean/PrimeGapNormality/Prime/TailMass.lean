import PrimeGapNormality.Prime.PrimeSeries
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive tail-mass identity (paper `lem:tailmass`)

For `ρ > 1` and a geometrically summable sequence,
`F_ρ(n) = ∑_{j≥0} a_{n+j} ρ^{-j-1}` and
`T_ρ(n) = ∑_{h≥1} g_{n+h-1} ρ^{-h}` satisfy
`F_ρ(n+1) - F_ρ(n) = T_ρ(n)`. Telescoping and nonnegativity bound any
finite set of distinct indices by the last mass. No higher gap moment.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` Lemma `lem:tailmass`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Filter
open scoped Topology

set_option maxHeartbeats 800000

/-- Truncated position mass `∑_{j < N} a_{n+j} ρ^{-j-1}`. -/
noncomputable def posMassTrunc (ρ : ℝ) (a : ℕ → ℝ) (n N : ℕ) : ℝ :=
  ∑ j ∈ range N, a (n + j) / ρ ^ (j + 1)

/-- Truncated gap tail `∑_{h < N} g_{n+h} ρ^{-h-1}`. -/
noncomputable def gapTailTrunc (ρ : ℝ) (g : ℕ → ℝ) (n N : ℕ) : ℝ :=
  ∑ h ∈ range N, g (n + h) / ρ ^ (h + 1)

/-- Position tail `F_ρ(n)`. Lean `n` is 0-based. -/
noncomputable def posMass (ρ : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, a (n + j) / ρ ^ (j + 1)

/-- Gap tail `T_ρ(n)`. Lean `g k` is paper `g_{k+1}`. -/
noncomputable def gapTail (ρ : ℝ) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' h : ℕ, g (n + h) / ρ ^ (h + 1)

private theorem rho_pos {ρ : ℝ} (hρ : 1 < ρ) : 0 < ρ :=
  lt_trans (by norm_num) hρ

/-- Finite identity, no summability. -/
theorem gapTailTrunc_eq_sub (ρ : ℝ) (a : ℕ → ℝ) (n N : ℕ) :
    gapTailTrunc ρ (fun k => a (k + 1) - a k) n N =
      posMassTrunc ρ a (n + 1) N - posMassTrunc ρ a n N := by
  unfold gapTailTrunc posMassTrunc
  simp only [sub_div]
  rw [sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  simp [add_assoc, add_comm x 1]

private theorem summable_posMass_terms {ρ : ℝ} (hρ : 1 < ρ) {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => a n / ρ ^ n) (k : ℕ) :
    Summable fun j : ℕ => a (k + j) / ρ ^ (j + 1) := by
  have hshift : Summable fun j : ℕ => a (j + k) / ρ ^ (j + k) :=
    (summable_nat_add_iff (f := fun n : ℕ => a n / ρ ^ n) k).mpr ha
  have hshift' : Summable fun j : ℕ => a (k + j) / ρ ^ (k + j) := by
    simpa [add_comm k] using hshift
  have hρ0 : ρ ≠ 0 := (rho_pos hρ).ne'
  refine (hshift'.mul_left (ρ ^ k / ρ)).congr fun j => ?_
  have hk : ρ ^ (k + j) = ρ ^ k * ρ ^ j := pow_add _ _ _
  have hj : ρ ^ (j + 1) = ρ ^ j * ρ := pow_succ _ _
  field_simp [hρ0, hk, hj, pow_ne_zero k hρ0, pow_ne_zero j hρ0]
  ring

/-- Infinite one-step identity: `F_ρ(n+1) - F_ρ(n) = T_ρ(n)`. -/
theorem gapTail_eq_sub {ρ : ℝ} (hρ : 1 < ρ) (a : ℕ → ℝ)
    (ha : Summable fun n : ℕ => a n / ρ ^ n) (n : ℕ) :
    gapTail ρ (fun k => a (k + 1) - a k) n =
      posMass ρ a (n + 1) - posMass ρ a n := by
  have hf := summable_posMass_terms hρ ha (n + 1)
  have hg := summable_posMass_terms hρ ha n
  unfold gapTail posMass
  have hfun :
      (fun h : ℕ => (a (n + h + 1) - a (n + h)) / ρ ^ (h + 1)) =
        fun h : ℕ => a (n + 1 + h) / ρ ^ (h + 1) - a (n + h) / ρ ^ (h + 1) := by
    funext h
    rw [sub_div]
    simp [add_assoc, add_comm h 1]
  rw [hfun]
  exact hf.tsum_sub hg

/-- Telescoping over a finite index block. -/
theorem sum_gapTail_telescope {ρ : ℝ} (hρ : 1 < ρ) (a : ℕ → ℝ)
    (ha : Summable fun n : ℕ => a n / ρ ^ n) (n J : ℕ) :
    ∑ i ∈ range J, gapTail ρ (fun k => a (k + 1) - a k) (n + i) =
      posMass ρ a (n + J) - posMass ρ a n := by
  have hstep (i : ℕ) := gapTail_eq_sub hρ a ha (n + i)
  simp_rw [hstep]
  have hcongr :
      ∀ i ∈ range J,
        posMass ρ a (n + i + 1) - posMass ρ a (n + i) =
          posMass ρ a (n + (i + 1)) - posMass ρ a (n + i) := by
    intro i _
    simp [add_assoc]
  rw [sum_congr rfl hcongr, sum_range_sub (fun t => posMass ρ a (n + t)) J]
  simp

theorem posMass_nonneg {ρ : ℝ} (hρ : 1 < ρ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (n : ℕ) : 0 ≤ posMass ρ a n :=
  tsum_nonneg fun j =>
    div_nonneg (ha0 (n + j)) (pow_nonneg (rho_pos hρ).le _)

theorem gapTail_nonneg {ρ : ℝ} (hρ : 1 < ρ) (a : ℕ → ℝ)
    (hmon : Monotone a) (n : ℕ) :
    0 ≤ gapTail ρ (fun k => a (k + 1) - a k) n :=
  tsum_nonneg fun h =>
    div_nonneg (sub_nonneg.mpr (hmon (Nat.le_succ (n + h))))
      (pow_nonneg (rho_pos hρ).le _)

/-- A subset of `{0,…,J-1}` cannot exceed the last mass. Paper last
display of `lem:tailmass`. -/
theorem sum_gapTail_le_posMass {ρ : ℝ} (hρ : 1 < ρ) (a : ℕ → ℝ)
    (ha : Summable fun n : ℕ => a n / ρ ^ n)
    (hmon : Monotone a) (ha0 : ∀ t, 0 ≤ a t)
    {n J : ℕ} (s : Finset ℕ) (hs : s ⊆ range J) :
    ∑ i ∈ s, gapTail ρ (fun k => a (k + 1) - a k) (n + i) ≤
      posMass ρ a (n + J) := by
  have hT (i : ℕ) := gapTail_nonneg hρ a hmon (n + i)
  have hsub :
      ∑ i ∈ s, gapTail ρ (fun k => a (k + 1) - a k) (n + i) ≤
        ∑ i ∈ range J, gapTail ρ (fun k => a (k + 1) - a k) (n + i) :=
    sum_le_sum_of_subset_of_nonneg hs fun i _ _ => hT i
  have htel := sum_gapTail_telescope hρ a ha n J
  have hFn := posMass_nonneg hρ a ha0 n
  exact hsub.trans (htel.trans_le (sub_le_self _ hFn))

/-! ### Prime specialisation -/

theorem nthPrime_div_pow_summable {ρ : ℝ} (hρ : 1 < ρ) :
    Summable fun n : ℕ => (nthPrime n : ℝ) / ρ ^ n := by
  have hr : ‖ρ⁻¹‖ < 1 := by
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos (rho_pos hρ)]
    exact inv_lt_one_of_one_lt₀ hρ
  have hpow :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  have hshift :=
    (summable_nat_add_iff
        (f := fun n : ℕ => (n : ℝ) ^ 2 * ρ⁻¹ ^ n) 1).2 hpow
  have hsucc :
      Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * ρ⁻¹ ^ n := by
    refine (hshift.mul_left ρ).congr fun n => ?_
    have hρ0 : ρ ≠ 0 := (rho_pos hρ).ne'
    have hpows : ρ⁻¹ ^ (n + 1) = ρ⁻¹ ^ n * ρ⁻¹ := pow_succ _ _
    have hscale : ρ * ρ⁻¹ ^ (n + 1) = ρ⁻¹ ^ n := by
      rw [hpows]
      have hcomm : ρ⁻¹ ^ n * ρ⁻¹ = ρ⁻¹ * ρ⁻¹ ^ n := mul_comm _ _
      rw [hcomm, ← mul_assoc, mul_inv_cancel₀ hρ0, one_mul]
    calc
      ρ * (((n + 1 : ℕ) : ℝ) ^ 2 * ρ⁻¹ ^ (n + 1))
          = ((n + 1 : ℕ) : ℝ) ^ 2 * (ρ * ρ⁻¹ ^ (n + 1)) := by
            ring
      _ = ((n + 1 : ℕ) : ℝ) ^ 2 * ρ⁻¹ ^ n := by rw [hscale]
  have hdom :
      Summable fun n : ℕ => (144 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 * ρ⁻¹ ^ n := by
    simpa [mul_assoc] using hsucc.mul_left (144 : ℝ)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hdom
  · exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (rho_pos hρ).le _)
  · have hbound : (nthPrime n : ℝ) ≤ 144 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
      have := nthPrime_le_succ_sq n
      have hcast : ((144 * (n + 1) ^ 2 : ℕ) : ℝ) = 144 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
        simp [Nat.cast_mul, Nat.cast_pow]
      exact (Nat.cast_le.mpr this).trans_eq hcast
    have : (nthPrime n : ℝ) / ρ ^ n ≤
        144 * ((n + 1 : ℕ) : ℝ) ^ 2 * ρ⁻¹ ^ n := by
      have hle :=
        div_le_div_of_nonneg_right hbound (pow_nonneg (rho_pos hρ).le n)
      have hrew : 144 * ((n + 1 : ℕ) : ℝ) ^ 2 / ρ ^ n =
          144 * ((n + 1 : ℕ) : ℝ) ^ 2 * ρ⁻¹ ^ n := by
        rw [div_eq_mul_inv, inv_pow]
      exact hle.trans_eq hrew
    exact this

theorem primeGapTail_eq {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    gapTail ρ (fun k => (primeGap k : ℝ)) n =
      posMass ρ (fun k => (nthPrime k : ℝ)) (n + 1) -
        posMass ρ (fun k => (nthPrime k : ℝ)) n := by
  have hfun : (fun k : ℕ => (primeGap k : ℝ)) =
      fun k => (nthPrime (k + 1) : ℝ) - nthPrime k := by
    funext k
    exact_mod_cast primeGap_cast k
  rw [hfun]
  exact gapTail_eq_sub hρ (fun k => (nthPrime k : ℝ))
    (nthPrime_div_pow_summable hρ) n

/-- Block average of prime gap tails is controlled by the last position
mass. This is the T-ready form of `lem:tailmass`; the PNT density
`m_X ≍ X/G` is not used here. -/
theorem sum_primeGapTail_le_posMass {ρ : ℝ} (hρ : 1 < ρ)
    {n J : ℕ} (s : Finset ℕ) (hs : s ⊆ range J) :
    ∑ i ∈ s, gapTail ρ (fun k => (primeGap k : ℝ)) (n + i) ≤
      posMass ρ (fun k => (nthPrime k : ℝ)) (n + J) := by
  have hfun : (fun k : ℕ => (primeGap k : ℝ)) =
      fun k => (nthPrime (k + 1) : ℝ) - nthPrime k := by
    funext k
    exact_mod_cast primeGap_cast k
  simp_rw [hfun]
  refine sum_gapTail_le_posMass hρ (fun k => (nthPrime k : ℝ))
    (nthPrime_div_pow_summable hρ) ?_ (fun t => Nat.cast_nonneg _) s hs
  intro i j hij
  exact Nat.cast_le.mpr (nthPrime_mono hij)

end PrimeGapNormality.Prime
