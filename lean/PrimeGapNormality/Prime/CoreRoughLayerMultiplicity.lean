import PrimeGapNormality.Prime.CoreRoughAdverseBudget
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# An explicit additive layer multiplicity bound

The relative part of the stopped sieve error uses factorial moments.
Only the additive CRT part uses this purely finite configuration count.
In particular a discarded physical interval is not charged by this bound:
its contribution must be restored once, after the stopped comparison.
-/

namespace PrimeGapNormality.Prime.CoreRoughLayerMultiplicity

open Finset
noncomputable section

theorem sum_powers_le_binomial (S r : ℕ) :
    (∑ j ∈ range (r + 1), S ^ j) ≤ (1 + S) ^ r := by
  calc
    _ ≤ ∑ j ∈ range (r + 1), S ^ j * r.choose j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr : j ≤ r := by simpa only [mem_range, Nat.lt_succ_iff] using hj
      exact Nat.le_mul_of_pos_right _ (Nat.choose_pos hjr)
    _ = _ := by
      simpa only [add_pow, one_pow, mul_one, Nat.cast_id, add_comm] using
        (add_pow S 1 r).symm

/-- The full configuration cost is bounded without an extra rank factor. -/
theorem layerMultiplicity_nat_le (S L r : ℕ) :
    (∑ j ∈ Icc L r, (j - 1).choose (L - 1) * S.choose j) ≤
      2 ^ r * (1 + S) ^ r := by
  have hpoint (j : ℕ) (hj : j ∈ Icc L r) :
      (j - 1).choose (L - 1) * S.choose j ≤ 2 ^ r * S ^ j := by
    have hcr : (j - 1).choose (L - 1) ≤ 2 ^ r :=
      (Nat.choose_le_two_pow _ _).trans
        (Nat.pow_le_pow_right (by norm_num : 0 < 2)
          ((Nat.sub_le _ _).trans (mem_Icc.mp hj).2))
    exact Nat.mul_le_mul hcr (Nat.choose_le_pow S j)
  have hsub : Icc L r ⊆ range (r + 1) := by
    intro j hj
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hj).2)
  calc
    _ ≤ ∑ j ∈ Icc L r, 2 ^ r * S ^ j := Finset.sum_le_sum hpoint
    _ = 2 ^ r * ∑ j ∈ Icc L r, S ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 ^ r * ∑ j ∈ range (r + 1), S ^ j :=
      Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset hsub)
    _ ≤ _ := Nat.mul_le_mul_left _ (sum_powers_le_binomial S r)

theorem layerMultiplicity_le (S L r : ℕ) :
    (∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * (S.choose j : ℝ)) ≤
      (2 : ℝ) ^ r * (1 + (S : ℝ)) ^ r := by
  exact_mod_cast layerMultiplicity_nat_le S L r

theorem additiveLayerSum_le (S L r : ℕ) (E : ℕ → ℝ) {Emax : ℝ}
    (hEmax : 0 ≤ Emax) (hE : ∀ j ∈ Icc L r, E j ≤ Emax) :
    (∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * (S.choose j : ℝ) * E j) ≤
      (2 : ℝ) ^ r * (1 + (S : ℝ)) ^ r * Emax := by
  calc
    _ ≤ ∑ j ∈ Icc L r,
        ((j - 1).choose (L - 1) : ℝ) * (S.choose j : ℝ) * Emax := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hE j hj) (by positivity)
    _ = (∑ j ∈ Icc L r,
        ((j - 1).choose (L - 1) : ℝ) * (S.choose j : ℝ)) * Emax :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (layerMultiplicity_le S L r) hEmax

theorem adverseBudget_le_exp_additive
    (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) (L r : ℕ)
    {δ Emax : ℝ} (hδ : 0 ≤ δ) (hEmax : 0 ≤ Emax)
    (herr : ∀ j ∈ Icc L r, ∀ H ∈ Ω.powerset.filter (fun H ↦ H.card = j),
      |Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H| ≤
        δ * Stopped.inclusionMass Ω ν H + Emax)
    (hm : ∀ j ∈ Icc L r, Stopped.countMoment Ω ν j ≤
      2 * (((5 : ℝ) * (L : ℝ)) ^ j / (j.factorial : ℝ))) :
    Stopped.adverseBudget Ω μ ν L r ≤
      2 * δ * Real.exp (10 * (L : ℝ)) +
        (2 : ℝ) ^ r * (1 + (Ω.card : ℝ)) ^ r * Emax := by
  have ha := CoreRoughAdverseBudget.adverseBudget_le_relative_additive
    Ω μ ν L r δ (fun _ ↦ Emax) herr
  have hr := mul_le_mul_of_nonneg_left
    (CoreRoughAdverseBudget.weighted_countMoment_le_exp Ω ν L r hm) hδ
  have he := additiveLayerSum_le Ω.card L r (fun _ ↦ Emax) hEmax
    (fun _ _ ↦ le_rfl)
  calc
    _ ≤ _ := ha
    _ ≤ δ * (2 * Real.exp (10 * (L : ℝ))) +
        (2 : ℝ) ^ r * (1 + (Ω.card : ℝ)) ^ r * Emax := add_le_add hr he
    _ = _ := by ring

end
end PrimeGapNormality.Prime.CoreRoughLayerMultiplicity
