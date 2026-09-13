import PrimeGapNormality.Prime.CoreRoughAdverseLimit
import PrimeGapNormality.Prime.CoreRoughMeanTail
import PrimeGapNormality.Prime.CoreSequenceSTMeanTail
import PrimeGapNormality.Prime.CoreSequenceSTRelations

/-!
# Local-series classification for the literal moving-rough sequence

This is the source-level end assembly of the unconditional rough backend.
The actual adverse-budget theorem supplies concrete positive Shape S at
`T_X = roughSyntheticScale (zPsi Ψ X)`, while the adjacent-window theorem
supplies the bare first-gap Mean T estimate at the same scale.  Count growth,
subexponential growth, summability, boundary decay, and reference-model
normality are all conclusions of the compiled generic sequence machinery.

The only analytic assumptions left are the literal slope budget with the
explicit coefficient `1000000 * κ` and the weighted derivative regularity
used by the actual rough sieve.  There is no Shape S, Tail T, count, density,
growth, model, or reference premise in the public endpoints below.
-/

namespace PrimeGapNormality.Prime.CoreRoughLocalNormality

open Filter Finset MvPolynomial CoreCyclic
open CoreRoughThreshold CoreRoughSyntheticScale
open CoreMovingRoughSequence CoreSequenceSTConsumer
open scoped Topology Classical

noncomputable section

/-- The actual synthetic model index tends to infinity. -/
theorem tendsto_movingRoughModelScale
    {Ψ : ℝ → ℝ} {κ : ℝ}
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) :
    Tendsto (fun X : ℕ ↦ roughSyntheticScale (zPsi Ψ X)) atTop atTop :=
  CoreRoughScaleLimits.tendsto_roughSyntheticScale_atTop.comp
    hSlope.tendsto_zPsi_atTop

/-- Actual positive Shape S and the adjacent-window mean estimate reconstruct
the complete legacy Tail T bundle, without exposing its redundant summability
field as an assumption. -/
theorem movingRough_gapTailT
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C) :
    GapTailT (movingRoughSequence (zPsi Ψ)) (localTailBase κ)
      (windowG ∘ fun X ↦ roughSyntheticScale (zPsi Ψ X)) := by
  let a := movingRoughSequence (zPsi Ψ)
  let T : ℕ → ℕ := fun X ↦ roughSyntheticScale (zPsi Ψ X)
  have ha : StrictMono a := movingRoughSequence_strictMono
    hSlope.eventually_zPsi_lt
  have hT : Tendsto T atTop atTop := by
    simpa only [T] using tendsto_movingRoughModelScale hSlope
  have hS : SequencePositiveShapeS a T κ 1 := by
    simpa only [a, T] using
      CoreRoughAdverseLimit.sequencePositiveShapeS hκ hSlope hC hreg
  have hMean : CoreSequenceSTMeanTail.MeanGapTailT a (localTailBase κ)
      (windowG ∘ T) := by
    simpa only [a, T] using
      CoreRoughMeanTail.movingRough_meanGapTailT hκ hSlope hC hreg
  exact CoreSequenceSTMeanTail.gapTailT_of_shapeS_and_meanTail
    ha hκ (by norm_num : (0 : ℝ) < 1) hT hS hMean

/-- Rationality is equivalent to vanishing of the canonical normal form for
the literal moving-rough gap series. -/
theorem movingRough_local_rational_iff_normalForm_zero
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ) :
    (∃ q : ℚ,
      coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) F =
        (q : ℝ)) ↔
      normalForm hB hk F = 0 := by
  let a := movingRoughSequence (zPsi Ψ)
  let T : ℕ → ℕ := fun X ↦ roughSyntheticScale (zPsi Ψ X)
  have ha : StrictMono a := movingRoughSequence_strictMono
    hSlope.eventually_zPsi_lt
  have hT : Tendsto T atTop atTop := by
    simpa only [T] using tendsto_movingRoughModelScale hSlope
  have hTail : GapTailT a (localTailBase κ) (windowG ∘ T) := by
    simpa only [a, T] using movingRough_gapTailT hκpos hSlope hC hreg
  have hS : SequencePositiveShapeS a T κ 1 := by
    simpa only [a, T] using
      CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
  simpa only [a] using
    CoreSequenceSTClassification.local_rational_iff_normalForm_zero
      ha hB hk phase F hκ (by norm_num : (0 : ℝ) < 1) hT hTail hS

/-- Literal rational-or-normal classification.  In the nonzero-normal-form
branch the value is normal both to the common clock `B^k` and to `B`. -/
theorem movingRough_local_classification
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ) :
    (normalForm hB hk F = 0 ∧
      ∃ q : ℚ,
        coreCyclicFullSeries B hk phase
            (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) F =
          (q : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k)
        (coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) F)) := by
  let a := movingRoughSequence (zPsi Ψ)
  let T : ℕ → ℕ := fun X ↦ roughSyntheticScale (zPsi Ψ X)
  have ha : StrictMono a := movingRoughSequence_strictMono
    hSlope.eventually_zPsi_lt
  have hT : Tendsto T atTop atTop := by
    simpa only [T] using tendsto_movingRoughModelScale hSlope
  have hS : SequencePositiveShapeS a T κ 1 := by
    simpa only [a, T] using
      CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
  have hMean : CoreSequenceSTMeanTail.MeanGapTailT a (localTailBase κ)
      (windowG ∘ T) := by
    simpa only [a, T] using
      CoreRoughMeanTail.movingRough_meanGapTailT hκpos hSlope hC hreg
  simpa only [a] using
    CoreSequenceSTMeanTail.local_classification_of_shapeS_and_meanTail
      ha hB hk phase F hκpos hκ (by norm_num : (0 : ℝ) < 1) hT hS hMean

/-- Rational relations among a finite family of actual moving-rough local
series are exactly the rational relations among their normal forms. -/
theorem movingRough_rational_relation_iff
    {I : Type*} [Fintype I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) (q : I → ℚ) :
    (∃ r : ℚ, (∑ i, (q i : ℝ) *
      coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) (F i)) =
          (r : ℝ)) ↔
      (∑ i, q i • normalForm hB hk (F i)) = 0 := by
  let a := movingRoughSequence (zPsi Ψ)
  let T : ℕ → ℕ := fun X ↦ roughSyntheticScale (zPsi Ψ X)
  have ha : StrictMono a := movingRoughSequence_strictMono
    hSlope.eventually_zPsi_lt
  have hT : Tendsto T atTop atTop := by
    simpa only [T] using tendsto_movingRoughModelScale hSlope
  have hTail : GapTailT a (localTailBase κ) (windowG ∘ T) := by
    simpa only [a, T] using movingRough_gapTailT hκpos hSlope hC hreg
  have hS : SequencePositiveShapeS a T κ 1 := by
    simpa only [a, T] using
      CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
  simpa only [a] using
    CoreSequenceSTRelations.rational_relation_iff_of_shapeS
      ha hB hk phase F hdeg hκ (by norm_num : (0 : ℝ) < 1) hT hTail hS q

/-- Independent normal forms give actual joint Weyl cancellation for the
moving-rough local series at the common clock `B^k`. -/
theorem movingRough_jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i ↦ normalForm hB hk (F i)))
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    JointWeyl (fun _ : I ↦ B ^ k)
      (fun i ↦ coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) (F i)) := by
  let a := movingRoughSequence (zPsi Ψ)
  let T : ℕ → ℕ := fun X ↦ roughSyntheticScale (zPsi Ψ X)
  have ha : StrictMono a := movingRoughSequence_strictMono
    hSlope.eventually_zPsi_lt
  have hT : Tendsto T atTop atTop := by
    simpa only [T] using tendsto_movingRoughModelScale hSlope
  have hTail : GapTailT a (localTailBase κ) (windowG ∘ T) := by
    simpa only [a, T] using movingRough_gapTailT hκpos hSlope hC hreg
  have hS : SequencePositiveShapeS a T κ 1 := by
    simpa only [a, T] using
      CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
  simpa only [a] using
    CoreSequenceSTRelations.jointWeyl_of_independent_normalForms_of_shapeS
      ha hB hk phase F hdeg hlin hκ (by norm_num : (0 : ℝ) < 1) hT hTail hS

/-- Consequently `1` and every member of the actual moving-rough family are
rationally linearly independent. -/
theorem movingRough_linearIndependent_one
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i ↦ normalForm hB hk (F i)))
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    LinearIndependent ℚ (fun i : Option I ↦ match i with
      | none => (1 : ℝ)
      | some i => coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) (F i)) := by
  let a := movingRoughSequence (zPsi Ψ)
  let T : ℕ → ℕ := fun X ↦ roughSyntheticScale (zPsi Ψ X)
  have ha : StrictMono a := movingRoughSequence_strictMono
    hSlope.eventually_zPsi_lt
  have hT : Tendsto T atTop atTop := by
    simpa only [T] using tendsto_movingRoughModelScale hSlope
  have hTail : GapTailT a (localTailBase κ) (windowG ∘ T) := by
    simpa only [a, T] using movingRough_gapTailT hκpos hSlope hC hreg
  have hS : SequencePositiveShapeS a T κ 1 := by
    simpa only [a, T] using
      CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
  convert
    CoreSequenceSTRelations.linearIndependent_one_of_independent_normalForms_of_shapeS
      ha hB hk phase F hdeg hlin hκ (by norm_num : (0 : ℝ) < 1) hT hTail hS
      using 1
  funext i
  cases i <;> rfl

end
end PrimeGapNormality.Prime.CoreRoughLocalNormality
