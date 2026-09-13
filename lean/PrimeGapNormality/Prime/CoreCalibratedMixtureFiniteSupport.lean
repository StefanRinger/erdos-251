import PrimeGapNormality.Prime.CoreRoughScaleLimits
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.ENNReal.BigOperators

/-!
# Uniform calibration forces finite natural-cutoff support

The actual inverse Euler product tends to infinity. Hence its bounded
sublevel sets in the natural cutoffs are finite. Support-uniform relative
calibration at the single tolerance 1 bounds every supported inverse Euler
product by 2G, so each calibrated mixture is exactly finitely supported.
The support bound may depend arbitrarily on the model scale. No total
variation approximation or quantitative calibration rate is introduced.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedMixtureFiniteSupport

open Filter Finset
open CoreRoughSyntheticScale CoreRoughScaleLimits
open scoped Topology Classical
noncomputable section

/-- The actual inverse Euler scale has finite bounded sublevel sets. -/
theorem finite_gapScale_sublevel (R : ℝ) :
    {y : ℕ | roughGapScale y ≤ R}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_roughGapScale_atTop.eventually_gt_atTop R)
  apply (Finset.range N).finite_toSet.subset
  intro y hy
  apply Finset.mem_range.mpr
  by_contra hnot
  exact (not_le_of_gt (hN y (by omega))) hy

/-- A coefficient function supported on an actual Euler sublevel vanishes
identically beyond some natural cutoff. No summability assumption is needed. -/
theorem exists_tail_zero_of_bounded_support {α : Type*} [Zero α]
    (w : ℕ → α) (R : ℝ)
    (hbound : ∀ y : ℕ, w y ≠ 0 → roughGapScale y ≤ R) :
    ∃ N : ℕ, ∀ y : ℕ, N ≤ y → w y = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_roughGapScale_atTop.eventually_gt_atTop R)
  refine ⟨N, ?_⟩
  intro y hy
  by_contra hwy
  exact (not_le_of_gt (hN y hy)) (hbound y hwy)

theorem gapScale_le_two_mul_of_calibrated {G : ℝ} (hG : 0 < G) (y : ℕ)
    (hcal : |roughGapScale y / G - 1| ≤ 1) : roughGapScale y ≤ 2 * G := by
  have hupper := (abs_le.mp hcal).2
  exact (div_le_iff₀ hG).mp (by linarith : roughGapScale y / G ≤ 2)

theorem real_weight_tail_zero (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y)
    {G : ℝ} (hG : 0 < G)
    (hcal : ∀ y : ℕ, 0 < w y → |roughGapScale y / G - 1| ≤ 1) :
    ∃ N : ℕ, ∀ y : ℕ, N ≤ y → w y = 0 :=
  exists_tail_zero_of_bounded_support w (2 * G) (fun y hy =>
    gapScale_le_two_mul_of_calibrated hG y (hcal y (lt_of_le_of_ne (hw y) (Ne.symm hy))))

theorem real_weight_support_finite (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y)
    {G : ℝ} (hG : 0 < G)
    (hcal : ∀ y : ℕ, 0 < w y → |roughGapScale y / G - 1| ≤ 1) :
    (Function.support w).Finite := by
  apply (finite_gapScale_sublevel (2 * G)).subset
  intro y hy
  exact gapScale_le_two_mul_of_calibrated hG y
    (hcal y (lt_of_le_of_ne (hw y) (Ne.symm hy)))

/-- Exact finite reduction for every integrand, not an approximation and
not limited to bounded tests. In particular all factorial moments reduce
to the same finite cutoff sum. -/
theorem weighted_tsum_eq_sum_of_tail_zero (w f : ℕ → ℝ) {N : ℕ}
    (hzero : ∀ y : ℕ, N ≤ y → w y = 0) :
    (∑' y : ℕ, w y * f y) = ∑ y ∈ Finset.range N, w y * f y := by
  apply tsum_eq_sum
  intro y hy
  rw [hzero y (by simpa only [Finset.mem_range, not_lt] using hy), zero_mul]

/-- The finite representation of a calibrated nonnegative real weight law.
The input normalization is unchanged by exact truncation. -/
theorem exists_real_finite_representation (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hsum : ∑' y : ℕ, w y = 1) {G : ℝ} (hG : 0 < G)
    (hcal : ∀ y : ℕ, 0 < w y → |roughGapScale y / G - 1| ≤ 1) :
    ∃ N : ℕ, (∀ y : ℕ, N ≤ y → w y = 0) ∧
      (∑ y ∈ Finset.range N, w y) = 1 ∧
      ∀ f : ℕ → ℝ, (∑' y : ℕ, w y * f y) = ∑ y ∈ Finset.range N, w y * f y := by
  obtain ⟨N, hN⟩ := real_weight_tail_zero w hw hG hcal
  refine ⟨N, hN, ?_, fun f => weighted_tsum_eq_sum_of_tail_zero w f hN⟩
  have hh := weighted_tsum_eq_sum_of_tail_zero w (fun _ => 1) hN
  simp only [mul_one] at hh
  exact hh.symm.trans hsum

/-- The paper's support-uniform qualitative calibration, expressed without
an auxiliary supremum. -/
def UniformCalibration (w : ℕ → ℕ → ℝ) (G : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
    ∀ y : ℕ, 0 < w X y → |roughGapScale y / G X - 1| ≤ ε

theorem eventually_real_finite_representation
    (w : ℕ → ℕ → ℝ) (G : ℕ → ℝ)
    (hw : ∀ X y, 0 ≤ w X y) (hsum : ∀ X, ∑' y : ℕ, w X y = 1)
    (hG : ∀ᶠ X : ℕ in atTop, 0 < G X) (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, ∃ N : ℕ,
      (∀ y : ℕ, N ≤ y → w X y = 0) ∧
      (∑ y ∈ Finset.range N, w X y) = 1 ∧
      ∀ f : ℕ → ℝ, (∑' y : ℕ, w X y * f y) = ∑ y ∈ Finset.range N, w X y * f y := by
  filter_upwards [hG, hcal 1 (by norm_num)] with X hGX hcalX
  exact exists_real_finite_representation (w X) (hw X) (hsum X) hGX hcalX

/-- PMFs require no real-weight summability conversion to establish finite
support: their literal nonzero atoms satisfy the same cutoff bound. -/
theorem pmf_support_finite (p : PMF ℕ) {G : ℝ} (hG : 0 < G)
    (hcal : ∀ y ∈ p.support, |roughGapScale y / G - 1| ≤ 1) :
    p.support.Finite := by
  apply (finite_gapScale_sublevel (2 * G)).subset
  intro y hy
  exact gapScale_le_two_mul_of_calibrated hG y (hcal y hy)

theorem exists_pmf_finite_representation (p : PMF ℕ) {G : ℝ} (hG : 0 < G)
    (hcal : ∀ y ∈ p.support, |roughGapScale y / G - 1| ≤ 1) :
    ∃ N : ℕ, (∀ y : ℕ, N ≤ y → p y = 0) ∧
      (∑ y ∈ Finset.range N, (p y).toReal) = 1 ∧
      ∀ f : ℕ → ℝ, (∑' y : ℕ, (p y).toReal * f y) =
        ∑ y ∈ Finset.range N, (p y).toReal * f y := by
  obtain ⟨N, hN⟩ := exists_tail_zero_of_bounded_support p (2 * G)
    (fun y hy => gapScale_le_two_mul_of_calibrated hG y (hcal y hy))
  have hzeroReal : ∀ y : ℕ, N ≤ y → (p y).toReal = 0 := by
    intro y hy
    rw [hN y hy, ENNReal.toReal_zero]
  refine ⟨N, hN, ?_, fun f => weighted_tsum_eq_sum_of_tail_zero _ f hzeroReal⟩
  have hsum : (∑ y ∈ Finset.range N, p y) = 1 := by
    have hh : (∑' y : ℕ, p y) = ∑ y ∈ Finset.range N, p y := by
      apply tsum_eq_sum
      intro y hy
      exact hN y (by simpa only [Finset.mem_range, not_lt] using hy)
    exact hh.symm.trans p.tsum_coe
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum (fun y _ => p.apply_ne_top y), ENNReal.toReal_one] at hreal
  exact hreal

theorem eventually_pmf_finite_representation (p : ℕ → PMF ℕ) (G : ℕ → ℝ)
    (hG : ∀ᶠ X : ℕ in atTop, 0 < G X)
    (hcal : ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      ∀ y ∈ (p X).support, |roughGapScale y / G X - 1| ≤ ε) :
    ∀ᶠ X : ℕ in atTop, ∃ N : ℕ,
      (∀ y : ℕ, N ≤ y → p X y = 0) ∧
      (∑ y ∈ Finset.range N, (p X y).toReal) = 1 ∧
      ∀ f : ℕ → ℝ, (∑' y : ℕ, (p X y).toReal * f y) =
        ∑ y ∈ Finset.range N, (p X y).toReal * f y := by
  filter_upwards [hG, hcal 1 (by norm_num)] with X hGX hcalX
  exact exists_pmf_finite_representation (p X) hGX hcalX

end
end PrimeGapNormality.Prime.CoreCalibratedMixtureFiniteSupport
