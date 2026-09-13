import PrimeGapNormality.Prime.CoreRoughSyntheticComparison
import PrimeGapNormality.Prime.CoreRoughCutoffInclusion

/-!
# Convex comparison with the synthetic finite root mixture

The comparison with each cutoff in the synthetic mixture is already an
actual full-configuration `L1` estimate.  This file averages that estimate
with the literal positive `V(y_t)` weights from `ExactRootMix`.  Consequently
bounded configuration tests, including stopped first-`L` tests, are compared
directly; no growing Janossy factor occurs.
-/

namespace PrimeGapNormality.Prime.CoreRoughMixtureComparison

open Finset CoreRoughSyntheticScale
open scoped BigOperators Classical

noncomputable section

/-- The first count moment of the old rooted law. -/
def roughFirstMoment (z S : ℕ) : ℝ :=
  ∑ U ∈ (offsetWindow S).powerset,
    (U.card : ℝ) * actualRootLaw z S U

/-- The uniform rooted-retention defect on the synthetic mixture. -/
def roughMixtureError (z : ℕ) : ℝ :=
  Real.log 4 / roughGapScale z + 1 / (z : ℝ) + 1 / ((z : ℝ) - 1)

private theorem syntheticMixZ_pos (z : ℕ) :
    0 < mixZ (roughSyntheticScale z) := by
  have hT : 0 < roughSyntheticScale z := roughSyntheticScale_pos z
  unfold mixZ
  apply sum_pos'
  · intro t ht
    exact mixWeightV_nonneg t
  · refine ⟨2 * roughSyntheticScale z, ?_, ?_⟩
    · simp only [mixScale, mem_Ioc]
      omega
    · exact eulerProdNat_pos
        (sieveCutoff ((2 * roughSyntheticScale z : ℕ) : ℝ))

private theorem normalizedWeight_nonneg (z t : ℕ) :
    0 ≤ mixWeightV t / mixZ (roughSyntheticScale z) :=
  div_nonneg (mixWeightV_nonneg t) (syntheticMixZ_pos z).le

private theorem normalizedWeight_sum (z : ℕ) :
    ∑ t ∈ mixScale (roughSyntheticScale z),
        mixWeightV t / mixZ (roughSyntheticScale z) = 1 := by
  rw [← sum_div]
  change mixZ (roughSyntheticScale z) / mixZ (roughSyntheticScale z) = 1
  exact div_self (syntheticMixZ_pos z).ne'

private theorem finiteRootMix_eq_weightedAverage
    (z S : ℕ) (U : Finset ℕ) :
    finiteRootMix (roughSyntheticScale z) S U =
      ∑ t ∈ mixScale (roughSyntheticScale z),
        (mixWeightV t / mixZ (roughSyntheticScale z)) *
          actualRootLaw (sieveCutoff (t : ℝ)) S U := by
  unfold finiteRootMix
  rw [sum_div]
  apply sum_congr rfl
  intro t ht
  ring

private theorem old_sub_mix_eq_weightedDifference
    (z S : ℕ) (U : Finset ℕ) :
    actualRootLaw z S U - finiteRootMix (roughSyntheticScale z) S U =
      ∑ t ∈ mixScale (roughSyntheticScale z),
        (mixWeightV t / mixZ (roughSyntheticScale z)) *
          (actualRootLaw z S U -
            actualRootLaw (sieveCutoff (t : ℝ)) S U) := by
  rw [finiteRootMix_eq_weightedAverage]
  calc
    actualRootLaw z S U -
        ∑ t ∈ mixScale (roughSyntheticScale z),
          (mixWeightV t / mixZ (roughSyntheticScale z)) *
            actualRootLaw (sieveCutoff (t : ℝ)) S U =
      (∑ t ∈ mixScale (roughSyntheticScale z),
          mixWeightV t / mixZ (roughSyntheticScale z)) *
          actualRootLaw z S U -
        ∑ t ∈ mixScale (roughSyntheticScale z),
          (mixWeightV t / mixZ (roughSyntheticScale z)) *
            actualRootLaw (sieveCutoff (t : ℝ)) S U := by
      rw [normalizedWeight_sum, one_mul]
    _ = _ := by
      rw [Finset.sum_mul, ← sum_sub_distrib]
      apply sum_congr rfl
      intro t ht
      ring

/-- Convex averaging of the actual per-cutoff comparison. -/
theorem actualRootLaw_finiteRootMix_massL1_le
    {z S : ℕ} (hz : 2 ≤ z) (hS : S ≤ z)
    (hG : 16 ≤ roughGapScale z) :
    (∑ U ∈ (offsetWindow S).powerset,
      |actualRootLaw z S U -
        finiteRootMix (roughSyntheticScale z) S U|) ≤
      2 * roughFirstMoment z S * roughMixtureError z := by
  let q : ℕ → ℝ :=
    fun t ↦ mixWeightV t / mixZ (roughSyntheticScale z)
  have hpoint (U : Finset ℕ) :
      |actualRootLaw z S U - finiteRootMix (roughSyntheticScale z) S U| ≤
        ∑ t ∈ mixScale (roughSyntheticScale z), q t *
          |actualRootLaw z S U -
            actualRootLaw (sieveCutoff (t : ℝ)) S U| := by
    rw [old_sub_mix_eq_weightedDifference]
    calc
      |∑ t ∈ mixScale (roughSyntheticScale z),
          q t * (actualRootLaw z S U -
            actualRootLaw (sieveCutoff (t : ℝ)) S U)| ≤
        ∑ t ∈ mixScale (roughSyntheticScale z),
          |q t * (actualRootLaw z S U -
            actualRootLaw (sieveCutoff (t : ℝ)) S U)| :=
        abs_sum_le_sum_abs _ _
      _ = _ := by
        apply sum_congr rfl
        intro t ht
        rw [abs_mul, abs_of_nonneg]
        exact normalizedWeight_nonneg z t
  calc
    (∑ U ∈ (offsetWindow S).powerset,
      |actualRootLaw z S U -
        finiteRootMix (roughSyntheticScale z) S U|) ≤
        ∑ U ∈ (offsetWindow S).powerset,
          ∑ t ∈ mixScale (roughSyntheticScale z), q t *
            |actualRootLaw z S U -
              actualRootLaw (sieveCutoff (t : ℝ)) S U| :=
      sum_le_sum fun U _ ↦ hpoint U
    _ = ∑ t ∈ mixScale (roughSyntheticScale z), q t *
        (∑ U ∈ (offsetWindow S).powerset,
          |actualRootLaw z S U -
            actualRootLaw (sieveCutoff (t : ℝ)) S U|) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro t ht
      rw [mul_sum]
    _ ≤ ∑ t ∈ mixScale (roughSyntheticScale z), q t *
        (2 * roughFirstMoment z S * roughMixtureError z) := by
      apply sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_left _ (normalizedWeight_nonneg z t)
      simpa only [roughFirstMoment, roughMixtureError] using
        CoreRoughSyntheticComparison.actualRootLaw_massL1_le hz hS hG ht
    _ = 2 * roughFirstMoment z S * roughMixtureError z := by
      rw [← sum_mul, show (∑ t ∈ mixScale (roughSyntheticScale z), q t) = 1 by
        simpa only [q] using normalizedWeight_sum z, one_mul]

/-- Any bounded real configuration test pays only its supremum times the
full-configuration `L1` distance. -/
theorem bounded_test_abs_sub_le_massL1
    (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ)
    (f : Finset ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ U ∈ Ω.powerset, |f U| ≤ C) :
    |∑ U ∈ Ω.powerset, μ U * f U -
        ∑ U ∈ Ω.powerset, ν U * f U| ≤
      C * ∑ U ∈ Ω.powerset, |μ U - ν U| := by
  rw [← sum_sub_distrib]
  calc
    |∑ U ∈ Ω.powerset, (μ U * f U - ν U * f U)| ≤
        ∑ U ∈ Ω.powerset, |μ U * f U - ν U * f U| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ U ∈ Ω.powerset, |μ U - ν U| * |f U| := by
      apply sum_congr rfl
      intro U hU
      rw [← sub_mul, abs_mul]
    _ ≤ ∑ U ∈ Ω.powerset, |μ U - ν U| * C := by
      exact sum_le_sum fun U hU ↦
        mul_le_mul_of_nonneg_left (hf U hU) (abs_nonneg _)
    _ = C * ∑ U ∈ Ω.powerset, |μ U - ν U| := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro U hU
      ring

theorem actualRootLaw_finiteRootMix_bounded_test
    {z S : ℕ} (hz : 2 ≤ z) (hS : S ≤ z)
    (hG : 16 ≤ roughGapScale z)
    (f : Finset ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ U ∈ (offsetWindow S).powerset, |f U| ≤ C) :
    |∑ U ∈ (offsetWindow S).powerset, actualRootLaw z S U * f U -
        ∑ U ∈ (offsetWindow S).powerset,
          finiteRootMix (roughSyntheticScale z) S U * f U| ≤
      C * (2 * roughFirstMoment z S * roughMixtureError z) := by
  exact (bounded_test_abs_sub_le_massL1 (offsetWindow S)
    (actualRootLaw z S) (finiteRootMix (roughSyntheticScale z) S)
    f hC hf).trans (mul_le_mul_of_nonneg_left
      (actualRootLaw_finiteRootMix_massL1_le hz hS hG) hC)

/-- The stopped first-`L` pushforward is a bounded whole-configuration
test, so its comparison has the same `L1` cost. -/
theorem actualRootLaw_finiteRootMix_stopped_test
    {z S L : ℕ} (hz : 2 ≤ z) (hS : S ≤ z)
    (hG : 16 ≤ roughGapScale z)
    (f : Finset ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf0 : ∀ K, 0 ≤ f K) (hfC : ∀ K, f K ≤ C) :
    |∑ U ∈ (offsetWindow S).powerset, actualRootLaw z S U *
          (if L ≤ U.card then f (Stopped.firstL L U) else 0) -
        ∑ U ∈ (offsetWindow S).powerset,
          finiteRootMix (roughSyntheticScale z) S U *
            (if L ≤ U.card then f (Stopped.firstL L U) else 0)| ≤
      C * (2 * roughFirstMoment z S * roughMixtureError z) := by
  apply actualRootLaw_finiteRootMix_bounded_test hz hS hG _ hC
  intro U hU
  by_cases hcard : L ≤ U.card
  · simp only [hcard, if_true, abs_of_nonneg (hf0 _)]
    exact hfC _
  · simp [hcard, hC]

end
end PrimeGapNormality.Prime.CoreRoughMixtureComparison
