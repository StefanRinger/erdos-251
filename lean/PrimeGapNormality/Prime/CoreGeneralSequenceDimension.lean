import PrimeGapNormality.Prime.CoreGeneralSequenceRelations
import PrimeGapNormality.Prime.CoreSequenceSTDimension
import PrimeGapNormality.Prime.CoreGeneralRealCutoff

/-!
# Actual series-span dimension under arbitrary-mixture S/T

Reuses the existing evaluation map and exact range/span identification.
Only injectivity needs the new general-mixture scalar classification.
There are H variables indexed by Fin H, not H+1; H,D,k are positive in
the paper endpoint. No independence or dimension is supplied as input.
-/
namespace PrimeGapNormality.Prime.CoreGeneralSequenceDimension
open Finset Filter MeasureTheory MvPolynomial CoreCyclic CoreNormalMonomialDimension
open CoreGeneralSequenceST CoreGeneralSequenceClassification CoreSequenceSTMeanTail
open CoreCalibratedMixtureFiniteSupport CoreSequenceSubexponentialGrowth
open CorePrimeLocalDimensionEnd
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem evaluation_injective
    {a : ℕ → ℕ} (ha : StrictMono a) {B H D k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k) (hH : 0 < H)
    (hg : HasSubexponentialGrowth (fun n => (seqGap a n : ℝ)))
    {κ : ℝ} (hκp : 0 < κ) (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    Function.Injective (CoreSequenceSTDimension.evaluation hB hk phase hH D hg) := by
  have hker : ∀ v, CoreSequenceSTDimension.evaluation hB hk phase hH D hg v = 0 → v = 0 := by
    rintro ⟨q, F⟩ hz
    have hκF : (topDegree (normalForm hB hk (embedRooted hH D k F)) : ℝ) /
        Real.log (B : ℝ) ≤ κ := by
      rw [normalForm_embedRooted]
      exact (div_le_div_of_nonneg_right (Nat.cast_le.2 (topDegree_embedRooted_le hH F))
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega)))).trans hκ
    have hNF := (CoreGeneralSequenceClassification.local_rational_iff_normalForm_zero
      ha hB hk phase (embedRooted hH D k F) hκp hκF hG hω hsum hcal hS hT).1
      (show ∃ r : ℚ, coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ))
        (embedRooted hH D k F) = (r : ℝ) from by
          refine ⟨-q, ?_⟩
          rw [CoreSequenceSTDimension.evaluation_apply] at hz
          push_cast
          linarith)
    rw [normalForm_embedRooted] at hNF
    have hF : F = 0 := by
      apply embedRooted_injective hH D k
      simpa only [map_zero] using hNF
    subst F
    have hq : q = 0 := by
      change (q : ℝ) + CoreSequenceSTRelations.sequenceSeriesLinear hB hk phase hg
        (embedRooted hH D k 0) = 0 at hz
      simp only [map_zero, add_zero] at hz
      exact Rat.cast_eq_zero.1 hz
    subst q
    rfl
  intro v w hvw
  exact sub_eq_zero.1 (hker (v - w) (by rw [map_sub, hvw, sub_self]))

/-- Literal rational span of 1 and all period-k, H-variable, degree-at-most-D
actual series, under the same complex S, bare T and qualitative calibration. -/
theorem finrank_seriesSpan
    {a : ℕ → ℕ} (ha : StrictMono a) {B H D k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k) (hH : 0 < H) (hD : 0 < D)
    {κ : ℝ} (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    Module.finrank ℚ (CoreSequenceSTDimension.seriesSpan a B H D hk phase) =
      1 + k * (H + D - 1).choose (D - 1) := by
  have hκp : 0 < κ := (div_pos (Nat.cast_pos.2 hD)
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hg := gap_growth ha hκp hG hω hsum hcal hS hT
  rw [← CoreSequenceSTDimension.evaluation_range_eq_seriesSpan hB hk phase hH hg,
    LinearMap.finrank_range_of_inj
      (evaluation_injective ha hB hk phase hH hg hκp hκ hG hω hsum hcal hS hT)]
  exact finrank_constant_and_labelled_rootedSpace hH hD k

theorem finrank_seriesSpan_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B H D k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k) (hH : 0 < H) (hD : 0 < D)
    {κ : ℝ} (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) (μ : ℕ → ProbabilityMeasure ℝ)
    (hcal : CoreGeneralRealCutoff.Calibration μ G) (hS : CoreGeneralRealCutoff.PatternS a κ G μ)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    Module.finrank ℚ (CoreSequenceSTDimension.seriesSpan a B H D hk phase) =
      1 + k * (H + D - 1).choose (D - 1) :=
  finrank_seriesSpan ha hB hk phase hH hD hκ hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRealCutoff.patternS_nat hG hcal hS) hT

end
end PrimeGapNormality.Prime.CoreGeneralSequenceDimension
