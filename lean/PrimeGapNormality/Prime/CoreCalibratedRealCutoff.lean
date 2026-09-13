import PrimeGapNormality.Prime.CoreCalibratedMixtureFiniteSupport
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Real-cutoff probabilities reduced to actual natural cutoffs

An arbitrary real-cutoff probability can be nonatomic. Its pushforward by
the measurable natural floor is a genuine probability on natural cutoffs.
An almost-everywhere uniform calibration passes to every nonzero atom.
Calibration then gives exact finite support, not a truncation estimate.
All nonnegative integrands reduce to the same finite sum, including
unbounded factorial moments. Source pending central compilation.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedRealCutoff

open Filter MeasureTheory
open CoreRoughSyntheticScale CoreCalibratedMixtureFiniteSupport
open scoped Topology ENNReal Classical
noncomputable section

def cutoffLaw (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℕ :=
  μ.map (Nat.measurable_floor : Measurable (Nat.floor : ℝ → ℕ)).aemeasurable

def cutoffPMF (μ : ProbabilityMeasure ℝ) : PMF ℕ :=
  (cutoffLaw μ : Measure ℕ).toPMF

theorem real_weights_nonneg (μ : ProbabilityMeasure ℝ) (y : ℕ) :
    0 ≤ (cutoffPMF μ y).toReal := ENNReal.toReal_nonneg

theorem real_weights_sum (μ : ProbabilityMeasure ℝ) :
    (∑' y : ℕ, (cutoffPMF μ y).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun y ↦ (cutoffPMF μ).apply_ne_top y),
    (cutoffPMF μ).tsum_coe, ENNReal.toReal_one]

theorem cutoffPMF_toMeasure (μ : ProbabilityMeasure ℝ) :
    (cutoffPMF μ).toMeasure = (μ : Measure ℝ).map Nat.floor := by
  unfold cutoffPMF
  rw [Measure.toPMF_toMeasure]
  rfl

theorem cutoffPMF_apply (μ : ProbabilityMeasure ℝ) (y : ℕ) :
    cutoffPMF μ y = (μ : Measure ℝ) {x : ℝ | Nat.floor x = y} := by
  calc
    cutoffPMF μ y = (cutoffPMF μ).toMeasure {y} :=
      (PMF.toMeasure_apply_singleton (cutoffPMF μ) y (measurableSet_singleton y)).symm
    _ = (μ : Measure ℝ) {x : ℝ | Nat.floor x = y} := by
      rw [cutoffPMF_toMeasure,
        Measure.map_apply Nat.measurable_floor (measurableSet_singleton y)]
      rfl

/-- An ae assertion about the cutoff becomes a pointwise assertion on all
positive natural atoms. No point in the real support has to be selected. -/
theorem predicate_on_support (μ : ProbabilityMeasure ℝ) (P : ℕ → Prop)
    (hP : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), P (Nat.floor x)) :
    ∀ y : ℕ, cutoffPMF μ y ≠ 0 → P y := by
  have hmap : ∀ᵐ y : ℕ ∂((μ : Measure ℝ).map Nat.floor), P y :=
    (ae_map_iff Nat.measurable_floor.aemeasurable (Set.to_countable _).measurableSet).2 hP
  have hpoint := ae_iff_of_countable.mp hmap
  intro y hy
  apply hpoint y
  rw [← cutoffPMF_toMeasure μ,
    PMF.toMeasure_apply_singleton (cutoffPMF μ) y (measurableSet_singleton y)]
  exact hy

/-- Exact expectation of any nonnegative cutoff-dependent integrand. -/
theorem lintegral_floor_eq_tsum (μ : ProbabilityMeasure ℝ) (f : ℕ → ℝ≥0∞) :
    (∫⁻ x : ℝ, f (Nat.floor x) ∂(μ : Measure ℝ)) =
      ∑' y : ℕ, cutoffPMF μ y * f y := by
  rw [← lintegral_map (measurable_of_countable f) Nat.measurable_floor,
    lintegral_countable']
  apply tsum_congr
  intro y
  change f y * cutoffPMF μ y = cutoffPMF μ y * f y
  exact mul_comm _ _

/-- The same finite cutoff set works for every nonnegative integrand.
In particular no separate uniform-integrability hypothesis is introduced
when passing from pattern tests to factorial moments. -/
theorem exists_finite_floor_representation
    (μ : ProbabilityMeasure ℝ) {G : ℝ} (hG : 0 < G)
    (hcal : ∀ᵐ x : ℝ ∂(μ : Measure ℝ),
      |roughGapScale (Nat.floor x) / G - 1| ≤ 1) :
    ∃ N : ℕ, (∀ y : ℕ, N ≤ y → cutoffPMF μ y = 0) ∧
      (∑ y ∈ Finset.range N, (cutoffPMF μ y).toReal) = 1 ∧
      ∀ f : ℕ → ℝ≥0∞,
        (∫⁻ x : ℝ, f (Nat.floor x) ∂(μ : Measure ℝ)) =
          ∑ y ∈ Finset.range N, cutoffPMF μ y * f y := by
  obtain ⟨N, hzero, hsum, _⟩ := exists_pmf_finite_representation
    (cutoffPMF μ) hG
    (predicate_on_support μ (fun y ↦ |roughGapScale y / G - 1| ≤ 1) hcal)
  refine ⟨N, hzero, hsum, ?_⟩
  intro f
  rw [lintegral_floor_eq_tsum]
  apply tsum_eq_sum
  intro y hy
  rw [hzero y (by simpa only [Finset.mem_range, not_lt] using hy), zero_mul]

/-- A support-uniform (hence in particular ae) real-cutoff calibration
passes to the existing natural-weight model interface without a rate. -/
theorem uniformCalibration_of_ae
    (μ : ℕ → ProbabilityMeasure ℝ) (G : ℕ → ℝ)
    (hcal : ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      ∀ᵐ x : ℝ ∂(μ X : Measure ℝ),
        |roughGapScale (Nat.floor x) / G X - 1| ≤ ε) :
    UniformCalibration (fun X y ↦ (cutoffPMF (μ X) y).toReal) G := by
  intro ε hε
  filter_upwards [hcal ε hε] with X hX
  intro y hy
  apply predicate_on_support (μ X) _ hX y
  intro hz
  rw [hz, ENNReal.toReal_zero] at hy
  exact (lt_irrefl (0 : ℝ)) hy

end
end PrimeGapNormality.Prime.CoreCalibratedRealCutoff
