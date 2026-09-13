import PrimeGapNormality.Prime.CoreRoughSliceLaws
import PrimeGapNormality.Prime.CoreRoughModelCosts
import PrimeGapNormality.Prime.CrtNestedCutoffL1Theta

/-!
# Exact moment and bounded-law controls for the true slice mixture

Higher moments use their exact multiplicative cutoff law. Only bounded
tests and failure events use full configuration distance. The latter's
finite Euler defect is displayed separately from its rooted correction.
-/

namespace PrimeGapNormality.Prime.CoreRoughSliceModelBounds

open Finset CoreRoughSliceLaws CoreRoughCutoffInclusion CoreRoughCutoffBounds
open scoped Classical
noncomputable section

set_option maxHeartbeats 1000000

def weight (y : ℕ → ℕ) (H q i : ℕ) : ℝ :=
  ((H : ℝ) * eulerProdNat (y i)) / normalization H q y

theorem weight_nonneg (y : ℕ → ℕ) (H q i : ℕ) : 0 ≤ weight y H q i :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (eulerProdNat_pos _).le) (normalization_nonneg H q y)

theorem weight_sum (y : ℕ → ℕ) (H q : ℕ) (hZ : 0 < normalization H q y) :
    (∑ i ∈ range q, weight y H q i) = 1 := by
  unfold weight
  rw [← Finset.sum_div]
  exact div_self hZ.ne'

theorem modelLaw_eq_weighted (y : ℕ → ℕ) (H q S : ℕ) (U : Finset ℕ) :
    modelLaw y H q S U = ∑ i ∈ range q, weight y H q i * actualRootLaw (y i) S U := by
  unfold modelLaw weight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem model_countMoment_eq (y : ℕ → ℕ) (H q S j : ℕ) :
    Stopped.countMoment (offsetWindow S) (modelLaw y H q S) j =
      (∑ i ∈ range q, (H : ℝ) * eulerProdNat (y i) *
        Stopped.countMoment (offsetWindow S) (actualRootLaw (y i) S) j) /
          normalization H q y :=
  modelLaw_eval y H q S (fun U => (U.card.choose j : ℝ))

/-- Every higher cutoff decreases the actual factorial moment. This is
the exact factor law, without a moment denominator or L1 estimate. -/
theorem actual_countMoment_mono {z u S j : ℕ} (hSz : S < z) (hzu : z ≤ u) (hj : j ≤ z) :
    Stopped.countMoment (offsetWindow S) (actualRootLaw u S) j ≤
      Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j := by
  rw [actualRootLaw_countMoment_cutoff hSz hzu]
  have hM : 0 ≤ Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j := by
    unfold Stopped.countMoment
    exact Finset.sum_nonneg fun U hU => mul_nonneg (actualRootLaw_nonneg _ _ _) (Nat.cast_nonneg _)
  exact mul_le_of_le_one_right hM (cutoffInclusionFactor_bounds (y := u) hj).2

/-- The literal slice mixture inherits the old moment without a TV loss,
uniformly in every j up to the old cutoff. -/
theorem model_countMoment_le (y : ℕ → ℕ) (H q S z j : ℕ)
    (hZ : 0 < normalization H q y) (hSz : S < z)
    (hy : ∀ i ∈ range q, z ≤ y i) (hj : j ≤ z) :
    Stopped.countMoment (offsetWindow S) (modelLaw y H q S) j ≤
      Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j := by
  rw [model_countMoment_eq]
  apply (div_le_iff₀ hZ).mpr
  calc
    _ ≤ ∑ i ∈ range q, (H : ℝ) * eulerProdNat (y i) *
        Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (actual_countMoment_mono hSz (hy i hi) hj)
        (mul_nonneg (Nat.cast_nonneg _) (eulerProdNat_pos _).le)
    _ = _ := by rw [← Finset.sum_mul]; unfold normalization; ring

theorem old_sub_model_eq (y : ℕ → ℕ) (H q S z : ℕ)
    (hZ : 0 < normalization H q y) (U : Finset ℕ) :
    actualRootLaw z S U - modelLaw y H q S U =
      ∑ i ∈ range q, weight y H q i * (actualRootLaw z S U - actualRootLaw (y i) S U) := by
  rw [modelLaw_eq_weighted]
  calc
    _ = (∑ i ∈ range q, weight y H q i) * actualRootLaw z S U -
        ∑ i ∈ range q, weight y H q i * actualRootLaw (y i) S U := by rw [weight_sum y H q hZ, one_mul]
    _ = _ := by rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i hi => by ring)

/-- Convex averaging of the actual per-cutoff nested CRT distance. The
uniform Euler defect and the rooted 1/(z-1) correction are both explicit. -/
theorem massL1_le (y : ℕ → ℕ) (H q S z : ℕ)
    (hZ : 0 < normalization H q y) (hz : 2 ≤ z) (hSz : S ≤ z)
    (hy : ∀ i ∈ range q, z ≤ y i) {δ : ℝ}
    (hδ : ∀ i ∈ range q, 1 - eulerProdNat (y i) / eulerProdNat z ≤ δ) :
    (∑ U ∈ (offsetWindow S).powerset, |actualRootLaw z S U - modelLaw y H q S U|) ≤
      2 * CoreRoughMixtureComparison.roughFirstMoment z S * (δ + 1 / ((z : ℝ) - 1)) := by
  have hM : 0 ≤ CoreRoughMixtureComparison.roughFirstMoment z S := by
    unfold CoreRoughMixtureComparison.roughFirstMoment
    exact Finset.sum_nonneg fun U hU => mul_nonneg (Nat.cast_nonneg _) (actualRootLaw_nonneg _ _ _)
  have hpoint (U : Finset ℕ) : |actualRootLaw z S U - modelLaw y H q S U| ≤
      ∑ i ∈ range q, weight y H q i * |actualRootLaw z S U - actualRootLaw (y i) S U| := by
    rw [old_sub_model_eq y H q S z hZ U]
    apply (abs_sum_le_sum_abs _ _).trans_eq
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_mul, abs_of_nonneg (weight_nonneg y H q i)]
  calc
    _ ≤ ∑ U ∈ (offsetWindow S).powerset, ∑ i ∈ range q,
        weight y H q i * |actualRootLaw z S U - actualRootLaw (y i) S U| :=
      Finset.sum_le_sum fun U hU => hpoint U
    _ = ∑ i ∈ range q, weight y H q i *
        (∑ U ∈ (offsetWindow S).powerset, |actualRootLaw z S U - actualRootLaw (y i) S U|) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i hi => (Finset.mul_sum _ _ _).symm)
    _ ≤ ∑ i ∈ range q, weight y H q i *
        (2 * CoreRoughMixtureComparison.roughFirstMoment z S * (δ + 1 / ((z : ℝ) - 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg y H q i)
      have hh := crtNestL1Th_massL1_le z (y i) S hz (hy i hi) hSz
      exact hh.trans (mul_le_mul_of_nonneg_left
        (_root_.add_le_add (hδ i hi) le_rfl) (mul_nonneg (by norm_num) hM))
    _ = _ := by rw [← Finset.sum_mul, weight_sum y H q hZ, one_mul]

/-- The uniform Euler defect can itself be supplied by the actual finite
new-prime reciprocal sum. This does not use a moment bound. -/
theorem eulerDefect_le_prime_sum {z u : ℕ} (hzu : z ≤ u) :
    1 - eulerProdNat u / eulerProdNat z ≤
      ∑ p ∈ Nat.primesLE u \ Nat.primesLE z, (p : ℝ)⁻¹ := by
  have hs := CoreRoughEulerStability.finiteTupleSieveProduct_bounds ({0} : Finset ℕ) hzu
    (δ := ∑ p ∈ Nat.primesLE u \ Nat.primesLE z, (p : ℝ)⁻¹) (by
      apply Finset.sum_le_sum
      intro p hp
      simp [residueCount, one_div])
  have hsingle (v : ℕ) : finiteTupleSieveProduct ({0} : Finset ℕ) v = eulerProdNat v := by
    unfold finiteTupleSieveProduct eulerProdNat
    simp [residueCount, one_div]
  rw [hsingle z, hsingle u] at hs
  have hdiv := (le_div_iff₀ (eulerProdNat_pos z)).mpr hs.1
  linarith

theorem bounded_test_error (y : ℕ → ℕ) (H q S z : ℕ)
    (hZ : 0 < normalization H q y) (hz : 2 ≤ z) (hSz : S ≤ z)
    (hy : ∀ i ∈ range q, z ≤ y i) {δ C : ℝ} (hC : 0 ≤ C)
    (hδ : ∀ i ∈ range q, 1 - eulerProdNat (y i) / eulerProdNat z ≤ δ)
    (f : Finset ℕ → ℝ) (hf : ∀ U ∈ (offsetWindow S).powerset, |f U| ≤ C) :
    |(∑ U ∈ (offsetWindow S).powerset, actualRootLaw z S U * f U) -
      ∑ U ∈ (offsetWindow S).powerset, modelLaw y H q S U * f U| ≤
      C * (2 * CoreRoughMixtureComparison.roughFirstMoment z S * (δ + 1 / ((z : ℝ) - 1))) :=
  (CoreRoughMixtureComparison.bounded_test_abs_sub_le_massL1 _ _ _ f hC hf).trans
    (mul_le_mul_of_nonneg_left (massL1_le y H q S z hZ hz hSz hy hδ) hC)

theorem failureMass_error (y : ℕ → ℕ) (H q S z L : ℕ)
    (hZ : 0 < normalization H q y) (hz : 2 ≤ z) (hSz : S ≤ z)
    (hy : ∀ i ∈ range q, z ≤ y i) {δ : ℝ}
    (hδ : ∀ i ∈ range q, 1 - eulerProdNat (y i) / eulerProdNat z ≤ δ) :
    |Stopped.failureMass (offsetWindow S) (actualRootLaw z S) L -
      Stopped.failureMass (offsetWindow S) (modelLaw y H q S) L| ≤
        2 * CoreRoughMixtureComparison.roughFirstMoment z S * (δ + 1 / ((z : ℝ) - 1)) :=
  (CoreRoughModelCosts.failureMass_abs_sub_le _ _ _ L).trans
    (massL1_le y H q S z hZ hz hSz hy hδ)

theorem massL1_le_prime_hazard (y : ℕ → ℕ) (H q S z : ℕ)
    (hZ : 0 < normalization H q y) (hz : 2 ≤ z) (hSz : S ≤ z)
    (hy : ∀ i ∈ range q, z ≤ y i) {δ : ℝ}
    (hδ : ∀ i ∈ range q,
      ∑ p ∈ Nat.primesLE (y i) \ Nat.primesLE z, (p : ℝ)⁻¹ ≤ δ) :
    (∑ U ∈ (offsetWindow S).powerset, |actualRootLaw z S U - modelLaw y H q S U|) ≤
      2 * CoreRoughMixtureComparison.roughFirstMoment z S * (δ + 1 / ((z : ℝ) - 1)) :=
  massL1_le y H q S z hZ hz hSz hy
    (fun i hi => (eulerDefect_le_prime_sum (hy i hi)).trans (hδ i hi))

/-- All actual slice mixtures above the old cutoff inherit the proved
growing factorial-moment envelope, with no cutoff-hazard multiplier. -/
theorem eventually_profile_moment_bound {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ (H q : ℕ) (y : ℕ → ℕ),
      0 < normalization H q y → (∀ i ∈ range q, z ≤ y i) →
      ∀ j : ℕ, j ≤ profileR (CoreRoughProfileError.roughProfileL κ z) 20 + 1 →
        Stopped.countMoment (offsetWindow (CoreRoughProfileError.roughProfileS κ z))
          (modelLaw y H q (CoreRoughProfileError.roughProfileS κ z)) j ≤
            2 * (((5 : ℝ) * (CoreRoughProfileError.roughProfileL κ z : ℝ)) ^ j / (j.factorial : ℝ)) := by
  filter_upwards [CoreRoughModelCosts.eventually_actual_countMoment_le_two_five hκ,
    CoreRoughModelCosts.eventually_rank_succ_le_cutoff hκ,
    CoreRoughSmallWindow.eventually_ahlSmall_window_roughSyntheticScale_lt hκ] with z hm hr hS
  intro H q y hZ hy j hj
  exact (model_countMoment_le y H q (CoreRoughProfileError.roughProfileS κ z) z j
    hZ hS hy (hj.trans hr)).trans (hm j hj)

end
end PrimeGapNormality.Prime.CoreRoughSliceModelBounds
