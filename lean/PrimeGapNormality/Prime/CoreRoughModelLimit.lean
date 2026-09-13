import PrimeGapNormality.Prime.CoreRoughMixtureComparison
import PrimeGapNormality.Prime.CoreRoughProfileError

/-! Actual bounded-law comparison at the growing rough profile.
The finite coupling is combined with a proved first-count estimate. No
bounded-TV statement is used for unbounded growing factorial moments. -/

namespace PrimeGapNormality.Prime.CoreRoughModelLimit

open Finset Filter CoreRoughSyntheticScale CoreRoughProfileError
open CoreRoughMixtureComparison
open scoped Topology
noncomputable section

def modelMassL1 (κ : ℝ) (z : ℕ) : ℝ :=
  ∑ U ∈ (offsetWindow (roughProfileS κ z)).powerset,
    |actualRootLaw z (roughProfileS κ z) U -
      finiteRootMix (roughSyntheticScale z) (roughProfileS κ z) U|

theorem firstMoment_eq_countMoment (z S : ℕ) :
    roughFirstMoment z S =
      Stopped.countMoment (offsetWindow S) (actualRootLaw z S) 1 := by
  unfold roughFirstMoment Stopped.countMoment
  apply sum_congr rfl
  intro U hU
  rw [Nat.choose_one_right]
  ring

theorem eventually_firstMoment_le {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ z : ℕ in atTop,
      roughFirstMoment z (roughProfileS κ z) ≤
        (3 / eulerProdLowerConst) * ((roughProfileS κ z : ℝ) / roughGapScale z) := by
  have hM := (tendsto_roughProfileS_atTop hκ).eventually
    CoreRoughMeanCount.eventually_countMoment_one_le
  filter_upwards [hM, eventually_roughProfile_scales hκ] with z hz hs
  have hh := hz z hs.2.2
  rw [← firstMoment_eq_countMoment] at hh
  exact hh.trans_eq (by
    unfold roughGapScale
    field_simp [(eulerProdNat_pos z).ne'] <;> ring)

/-- Full configuration distance tends to zero at the growing physical
window. This is an actual model-to-model theorem, not arithmetic transfer. -/
theorem tendsto_modelMassL1_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (modelMassL1 κ) atTop (𝓝 0) := by
  have hlim := (tendsto_roughProfileS_div_gapScale_mul_error_zero hκ).const_mul
    (2 * (3 / eulerProdLowerConst))
  simp only [mul_zero] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall fun z ↦ sum_nonneg fun U _ ↦ abs_nonneg _
  · filter_upwards [eventually_roughProfile_scales hκ,
      eventually_firstMoment_le hκ] with z hs hM
    have hG := roughGapScale_pos z
    have hzpos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
    have hzpred : (0 : ℝ) < (z : ℝ) - 1 := by
      have hz2 : (2 : ℝ) ≤ z := Nat.cast_le.mpr hs.1
      linarith
    have he : 0 ≤ roughMixtureError z := by
      unfold roughMixtureError
      exact add_nonneg
        (add_nonneg (div_nonneg (Real.log_nonneg (by norm_num)) hG.le)
          (div_nonneg zero_le_one hzpos.le))
        (div_nonneg zero_le_one hzpred.le)
    have hfinite := actualRootLaw_finiteRootMix_massL1_le hs.1 hs.2.2 hs.2.1
    have hscaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 2)) he
    exact hfinite.trans (hscaled.trans_eq (by
      change 2 * ((3 / eulerProdLowerConst) *
          ((roughProfileS κ z : ℝ) / roughGapScale z)) * roughProfileError z = _
      ring))

/-- Uniformity includes tests chosen after z and the whole growing window.
It never conditions on a rare configuration. -/
theorem bounded_tests_eventually_close {κ C ε : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ z : ℕ in atTop, ∀ f : Finset ℕ → ℝ,
      (∀ U ∈ (offsetWindow (roughProfileS κ z)).powerset, |f U| ≤ C) →
      |∑ U ∈ (offsetWindow (roughProfileS κ z)).powerset,
          actualRootLaw z (roughProfileS κ z) U * f U -
        ∑ U ∈ (offsetWindow (roughProfileS κ z)).powerset,
          finiteRootMix (roughSyntheticScale z) (roughProfileS κ z) U * f U| < ε := by
  have hlim := (tendsto_modelMassL1_zero hκ).const_mul C
  simp only [mul_zero] at hlim
  have he := (tendsto_order.mp hlim).2 ε hε
  filter_upwards [he] with z hz
  intro f hf
  exact (bounded_test_abs_sub_le_massL1 _ _ _ f hC hf).trans_lt hz

end
end PrimeGapNormality.Prime.CoreRoughModelLimit
