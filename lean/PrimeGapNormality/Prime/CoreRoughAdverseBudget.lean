import PrimeGapNormality.Prime.StoppedPrime
import Mathlib.Analysis.Complex.Exponential

/-!
# Summing relative and additive rough-tuple errors

The relative error is charged to genuine model factorial moments, not
to the number of configurations. The additive CRT error is retained in
its own explicit layer sum. Neither mass equality nor positivity of an
individual tuple main term is assumed.
-/

namespace PrimeGapNormality.Prime.CoreRoughAdverseBudget

open Finset
open scoped Classical
noncomputable section

theorem adverseLayer_le_relative_additive
    (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) (L j : ℕ) {δ E : ℝ}
    (herr : ∀ H ∈ Ω.powerset.filter (fun H ↦ H.card = j),
      |Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H| ≤
        δ * Stopped.inclusionMass Ω ν H + E) :
    Stopped.adverseLayer Ω μ ν L j ≤ δ * Stopped.countMoment Ω ν j +
      (Ω.card.choose j : ℝ) * E := by
  have hsgn (H : Finset ℕ) :
      max (((-1 : ℝ) ^ (j - L + 1)) *
        (Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H)) 0 ≤
        |Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H| := by
    apply max_le
    · calc
        _ ≤ |((-1 : ℝ) ^ (j - L + 1)) *
          (Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H)| := le_abs_self _
        _ = _ := by simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    · exact abs_nonneg _
  unfold Stopped.adverseLayer
  calc
    _ ≤ ∑ H ∈ Ω.powerset.filter (fun H ↦ H.card = j),
        (δ * Stopped.inclusionMass Ω ν H + E) :=
      Finset.sum_le_sum fun H hH ↦ (hsgn H).trans (herr H hH)
    _ = δ * Stopped.countMoment Ω ν j + (Ω.card.choose j : ℝ) * E := by
      rw [sum_add_distrib, ← mul_sum, ← countMoment_eq_sum_inclusionMass]
      congr 1
      rw [sum_const, nsmul_eq_mul]
      congr 1
      rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]

theorem adverseBudget_le_relative_additive
    (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) (L r : ℕ)
    (δ : ℝ) (E : ℕ → ℝ)
    (herr : ∀ j ∈ Icc L r, ∀ H ∈ Ω.powerset.filter (fun H ↦ H.card = j),
      |Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H| ≤
        δ * Stopped.inclusionMass Ω ν H + E j) :
    Stopped.adverseBudget Ω μ ν L r ≤
      δ * (∑ j ∈ Icc L r, (Nat.choose (j - 1) (L - 1) : ℝ) *
        Stopped.countMoment Ω ν j) +
      ∑ j ∈ Icc L r, (Nat.choose (j - 1) (L - 1) : ℝ) *
        (Ω.card.choose j : ℝ) * E j := by
  unfold Stopped.adverseBudget
  calc
    _ ≤ ∑ j ∈ Icc L r, (Nat.choose (j - 1) (L - 1) : ℝ) *
        (δ * Stopped.countMoment Ω ν j + (Ω.card.choose j : ℝ) * E j) :=
      Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_left
        (adverseLayer_le_relative_additive Ω μ ν L j (herr j hj)) (Nat.cast_nonneg _)
    _ = _ := by
      simp_rw [mul_add]
      rw [sum_add_distrib, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j hj ↦ by ring
      · exact Finset.sum_congr rfl fun j hj ↦ by ring

/-- A simple exponential envelope is sufficient for the existential
roughness slope. It is deliberately not the paper's sharper constant. -/
theorem weighted_countMoment_le_exp
    (Ω : Finset ℕ) (ν : Finset ℕ → ℝ) (L r : ℕ)
    (hm : ∀ j ∈ Icc L r, Stopped.countMoment Ω ν j ≤
      2 * (((5 : ℝ) * (L : ℝ)) ^ j / (j.factorial : ℝ))) :
    (∑ j ∈ Icc L r, (Nat.choose (j - 1) (L - 1) : ℝ) *
      Stopped.countMoment Ω ν j) ≤ 2 * Real.exp (10 * (L : ℝ)) := by
  have hpoint (j : ℕ) (hj : j ∈ Icc L r) :
      (Nat.choose (j - 1) (L - 1) : ℝ) * Stopped.countMoment Ω ν j ≤
        2 * ((10 * (L : ℝ)) ^ j / (j.factorial : ℝ)) := by
    have hc : (Nat.choose (j - 1) (L - 1) : ℝ) ≤ (2 : ℝ) ^ j := by
      have hh := (Nat.choose_le_two_pow (j - 1) (L - 1)).trans
        (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.sub_le j 1))
      exact_mod_cast hh
    have hnn : 0 ≤ 2 * (((5 : ℝ) * (L : ℝ)) ^ j / (j.factorial : ℝ)) := by positivity
    calc
      _ ≤ (Nat.choose (j - 1) (L - 1) : ℝ) *
          (2 * (((5 : ℝ) * (L : ℝ)) ^ j / (j.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left (hm j hj) (Nat.cast_nonneg _)
      _ ≤ (2 : ℝ) ^ j * (2 * (((5 : ℝ) * (L : ℝ)) ^ j / (j.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_right hc hnn
      _ = 2 * ((10 * (L : ℝ)) ^ j / (j.factorial : ℝ)) := by
        have hp : (10 * (L : ℝ)) ^ j = (2 : ℝ) ^ j * (5 * (L : ℝ)) ^ j := by
          rw [← mul_pow]
          congr 1
          ring
        rw [hp]
        ring
  have hsub : Icc L r ⊆ range (r + 1) := by
    intro j hj
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hj).2)
  have hsum := Finset.sum_le_sum hpoint
  have hmore : (∑ j ∈ Icc L r, (10 * (L : ℝ)) ^ j / (j.factorial : ℝ)) ≤
      ∑ j ∈ range (r + 1), (10 * (L : ℝ)) ^ j / (j.factorial : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj hnot ↦ by positivity)
  rw [← Finset.mul_sum] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left
    (hmore.trans (Real.sum_le_exp_of_nonneg (by positivity) (r + 1))) (by norm_num))

end
end PrimeGapNormality.Prime.CoreRoughAdverseBudget
