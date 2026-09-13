import PrimeGapNormality.Prime.CoreRoughMixtureComparison
import PrimeGapNormality.Prime.CoreRoughCutoffBounds

/-! Growing factorial moments are compared by their exact multiplicative
cutoff law, not by bounded total variation. No division by a moment occurs,
so vanishing moments and locally covered shapes are included. -/

namespace PrimeGapNormality.Prime.CoreRoughMixtureMoments

open Finset CoreRoughSyntheticScale CoreRoughMixtureComparison
open CoreRoughCutoffInclusion CoreRoughCutoffBounds
open scoped Classical
noncomputable section

theorem factor_one_eq_rooted (z y : ℕ) :
    cutoffInclusionFactor z y 1 = rootedEulerProdNat z y := by
  unfold cutoffInclusionFactor rootedEulerProdNat
  apply prod_congr rfl
  intro p hp
  have hp1 : 1 ≤ p := (Nat.prime_of_mem_primesLE (sdiff_subset hp)).one_lt.le
  rw [Nat.cast_sub hp1]
  simp only [Nat.cast_one, one_div]

theorem countMoment_finiteRootMix (X S j : ℕ) :
    Stopped.countMoment (offsetWindow S) (finiteRootMix X S) j =
      (∑ t ∈ mixScale X, mixWeightV t *
        Stopped.countMoment (offsetWindow S)
          (actualRootLaw (sieveCutoff (t : ℝ)) S) j) / mixZ X := by
  unfold Stopped.countMoment finiteRootMix
  simp_rw [div_mul_eq_mul_div, sum_mul]
  rw [← sum_div, sum_comm]
  congr 1
  apply sum_congr rfl
  intro t ht
  rw [mul_sum]
  apply sum_congr rfl
  intro U hU
  ring

private theorem mixZ_pos (z : ℕ) : 0 < mixZ (roughSyntheticScale z) := by
  unfold mixZ
  apply sum_pos'
  · intro t ht
    exact mixWeightV_nonneg t
  · refine ⟨2 * roughSyntheticScale z, ?_, ?_⟩
    · have hT := roughSyntheticScale_pos z
      simp only [mixScale, mem_Ioc]
      omega
    · exact eulerProdNat_pos _

private theorem weightedMean_bounds (z : ℕ) (f : ℕ → ℝ) {a b : ℝ}
    (hf : ∀ t ∈ mixScale (roughSyntheticScale z), a ≤ f t ∧ f t ≤ b) :
    a ≤ (∑ t ∈ mixScale (roughSyntheticScale z), mixWeightV t * f t) /
        mixZ (roughSyntheticScale z) ∧
      (∑ t ∈ mixScale (roughSyntheticScale z), mixWeightV t * f t) /
        mixZ (roughSyntheticScale z) ≤ b := by
  have hZ := mixZ_pos z
  constructor
  · apply (le_div_iff₀ hZ).2
    calc
      a * mixZ (roughSyntheticScale z) =
          ∑ t ∈ mixScale (roughSyntheticScale z), mixWeightV t * a := by
        unfold mixZ
        rw [mul_comm, sum_mul]
      _ ≤ _ := sum_le_sum fun t ht ↦
        mul_le_mul_of_nonneg_left (hf t ht).1 (mixWeightV_nonneg t)
  · apply (div_le_iff₀ hZ).2
    calc
      _ ≤ ∑ t ∈ mixScale (roughSyntheticScale z), mixWeightV t * b :=
        sum_le_sum fun t ht ↦
          mul_le_mul_of_nonneg_left (hf t ht).2 (mixWeightV_nonneg t)
      _ = b * mixZ (roughSyntheticScale z) := by
        unfold mixZ
        rw [← sum_mul, mul_comm]

/-- A single uniform loss controls every moment order through r. The
actual source of the loss is the rooted one-point retention, whose bound
was derived from ordinary Euler calibration plus its rooting correction. -/
theorem actual_mixture_countMoment_bounds
    {z S j r : ℕ} (hz : 2 ≤ z) (hSz : S < z) (hjr : j ≤ r) (hrz : r ≤ z)
    (hG : 16 ≤ roughGapScale z) (he : roughMixtureError z ≤ 1 / 2) :
    (1 - 2 * (r : ℝ) * roughMixtureError z) *
        Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j ≤
      Stopped.countMoment (offsetWindow S)
        (finiteRootMix (roughSyntheticScale z) S) j ∧
    Stopped.countMoment (offsetWindow S)
        (finiteRootMix (roughSyntheticScale z) S) j ≤
      Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j := by
  rw [countMoment_finiteRootMix]
  apply weightedMean_bounds
  intro t ht
  have hzy := lt_sieveCutoff_of_mem_mixScale ht
  have herr := CoreRoughSyntheticComparison.rooted_retention_error hz hG ht
  change 1 - rootedEulerProdNat z (sieveCutoff (t : ℝ)) ≤ roughMixtureError z at herr
  have hhalf : (1 : ℝ) / 2 ≤
      cutoffInclusionFactor z (sieveCutoff (t : ℝ)) 1 := by
    rw [factor_one_eq_rooted]
    linarith
  have hb := actualRootLaw_countMoment_cutoff_bounds_of_le_rank
    hSz hzy.le hz hjr hrz hhalf
  have hM : 0 ≤ Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j := by
    unfold Stopped.countMoment
    exact sum_nonneg fun U hU ↦
      mul_nonneg (actualRootLaw_nonneg z S U) (Nat.cast_nonneg _)
  have hcoef : 1 - 2 * (r : ℝ) * roughMixtureError z ≤
      1 - 2 * (r : ℝ) *
        (1 - cutoffInclusionFactor z (sieveCutoff (t : ℝ)) 1) := by
    rw [factor_one_eq_rooted]
    exact sub_le_sub_left
      (mul_le_mul_of_nonneg_left herr (by positivity)) 1
  exact ⟨(mul_le_mul_of_nonneg_right hcoef hM).trans hb.1, hb.2⟩

end
end PrimeGapNormality.Prime.CoreRoughMixtureMoments
