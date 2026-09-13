import PrimeGapNormality.Prime.CoreSequenceTailAgreement
import PrimeGapNormality.Prime.CoreRoughLocalNormality
import PrimeGapNormality.Prime.CoreRoughEveryWindow

/-!
# Fixed finite conventions for the moving-rough sequence

The paper allows any fixed finite initial convention for the increasing
enumeration of the moving-rough integers.  This file packages that statement
without turning Shape S, Tail T, density, or growth into hypotheses.

The only comparison premise is literal eventual equality between the range of
the supplied strictly increasing sequence and the actual moving-rough
predicate.  Exact physical pattern laws and future gap tails then transfer
from the canonical `Nat.nth` enumeration.  The same exact pattern-law identity
also transports the every-window complex prefix comparison.
-/

namespace PrimeGapNormality.Prime.CoreRoughFiniteConvention

open Filter Set Finset MvPolynomial CoreCyclic
open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSyntheticScale
  CoreSequenceSTConsumer CoreSequenceSTMeanTail
open scoped Topology Classical

noncomputable section

/-- Convert literal eventual agreement with the moving-rough predicate into
eventual range agreement with its canonical `Nat.nth` enumeration. -/
theorem eventually_movingRough_range_iff
    {a : ℕ → ℕ} {Ψ : ℝ → ℝ} {A : ℝ}
    (hSlope : HasSlopeBudget Ψ A)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v)) :
    ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range (movingRoughSequence (zPsi Ψ)) ↔ v ∈ Set.range a) := by
  filter_upwards [hrange] with v hv
  have hcanon :
      (v ∈ Set.range (movingRoughSequence (zPsi Ψ)) ↔
        IsMovingRough (zPsi Ψ) v) := by
    rw [range_movingRoughSequence hSlope.eventually_zPsi_lt]
    rfl
  exact hcanon.trans hv.symm

/-- The actual positive Shape-S input is invariant under a fixed finite
change of the moving-rough enumeration. -/
theorem sequencePositiveShapeS
    {a : ℕ → ℕ} (ha : StrictMono a)
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v)) :
    CoreSequenceSTConsumer.SequencePositiveShapeS a
      (fun X ↦ roughSyntheticScale (zPsi Ψ X)) κ 1 := by
  have hb : StrictMono (movingRoughSequence (zPsi Ψ)) :=
    movingRoughSequence_strictMono hSlope.eventually_zPsi_lt
  have hcanon := CoreRoughAdverseLimit.sequencePositiveShapeS
    hκ hSlope hC hreg
  exact CoreSequenceRangeAgreement.sequencePositiveShapeS_of_range_agreement
    hb ha (eventually_movingRough_range_iff hSlope hrange) hcanon

/-- The bare actual mean-tail estimate transfers by aligning equal physical
roots and their entire future gap sequences. -/
theorem meanGapTailT
    {a : ℕ → ℕ} (ha : StrictMono a)
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v)) :
    CoreSequenceSTMeanTail.MeanGapTailT a (localTailBase κ)
      (windowG ∘ fun X ↦ roughSyntheticScale (zPsi Ψ X)) := by
  have hb : StrictMono (movingRoughSequence (zPsi Ψ)) :=
    movingRoughSequence_strictMono hSlope.eventually_zPsi_lt
  have hcanon := CoreRoughMeanTail.movingRough_meanGapTailT
    hκ hSlope hC hreg
  exact (CoreSequenceTailAgreement.meanGapTailT_iff_of_range_agreement
    hb ha (eventually_movingRough_range_iff hSlope hrange)
      (localTailBase κ)
      (windowG ∘ fun X ↦ roughSyntheticScale (zPsi Ψ X))).mp hcanon

/-- Shape S and the transferred bare mean estimate reconstruct the full tail
bundle, including count growth and summability, without exposing either as a
premise. -/
theorem gapTailT
    {a : ℕ → ℕ} (ha : StrictMono a)
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v)) :
    GapTailT a (localTailBase κ)
      (windowG ∘ fun X ↦ roughSyntheticScale (zPsi Ψ X)) := by
  have hT : Tendsto (fun X : ℕ ↦ roughSyntheticScale (zPsi Ψ X)) atTop atTop :=
    CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope
  exact CoreSequenceSTMeanTail.gapTailT_of_shapeS_and_meanTail
    ha hκ (by norm_num : (0 : ℝ) < 1) hT
      (sequencePositiveShapeS ha hκ hSlope hC hreg hrange)
      (meanGapTailT ha hκ hSlope hC hreg hrange)

/-- Rationality is equivalent to vanishing of the same canonical normal
form for every fixed finite initial convention. -/
theorem local_rational_iff_normalForm_zero
    {a : ℕ → ℕ} (ha : StrictMono a)
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v))
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ) :
    (∃ q : ℚ,
      coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F =
        (q : ℝ)) ↔
      normalForm hB hk F = 0 := by
  have hT : Tendsto (fun X : ℕ ↦ roughSyntheticScale (zPsi Ψ X)) atTop atTop :=
    CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope
  exact CoreSequenceSTClassification.local_rational_iff_normalForm_zero
    ha hB hk phase F hκ (by norm_num : (0 : ℝ) < 1) hT
      (gapTailT ha hκpos hSlope hC hreg hrange)
      (sequencePositiveShapeS ha hκpos hSlope hC hreg hrange)

/-- Literal rational-or-normal classification, with the same effective top
degree budget as for the canonical moving-rough enumeration. -/
theorem local_classification
    {a : ℕ → ℕ} (ha : StrictMono a)
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v))
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ) :
    (normalForm hB hk F = 0 ∧
      ∃ q : ℚ,
        coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F =
          (q : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F)) := by
  have hT : Tendsto (fun X : ℕ ↦ roughSyntheticScale (zPsi Ψ X)) atTop atTop :=
    CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope
  exact CoreSequenceSTMeanTail.local_classification_of_shapeS_and_meanTail
    ha hB hk phase F hκpos hκ (by norm_num : (0 : ℝ) < 1) hT
      (sequencePositiveShapeS ha hκpos hSlope hC hreg hrange)
      (meanGapTailT ha hκpos hSlope hC hreg hrange)

/-- Exact equality of literal truncated prefix means after a fixed finite
change of an increasing sequence. It holds uniformly in the span, rank, and
complex test once the physical scale is beyond the changed range. -/
theorem eventually_prefixMean_eq_of_range_agreement
    {a b : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ v ∈ Set.range b)) :
    ∀ᶠ X : ℕ in atTop, ∀ S M : ℕ, ∀ f : Finset ℕ → ℂ,
      1 ≤ M →
      CoreRoughEveryWindow.prefixMean a X S M f =
        CoreRoughEveryWindow.prefixMean b X S M f := by
  filter_upwards [CoreSequenceRangeAgreement.eventually_patternMass_eq_of_range_agreement
    ha hb hrange] with X hmass
  intro S M f hM
  calc
    CoreRoughEveryWindow.prefixMean a X S M f =
        CoreRoughEveryWindow.complexMean S M
          (CoreSequencePatternLaw.patternMass a X (offsetWindow S)) f :=
      (CoreRoughEveryWindow.complexMean_actual_eq_prefix ha X S hM f).symm
    _ = CoreRoughEveryWindow.complexMean S M
          (CoreSequencePatternLaw.patternMass b X (offsetWindow S)) f := by
      rw [hmass (offsetWindow S)]
    _ = CoreRoughEveryWindow.prefixMean b X S M f :=
      CoreRoughEveryWindow.complexMean_actual_eq_prefix hb X S hM f

/-- The frozen paper's literal every-M complex prefix comparison is unchanged
by any fixed finite initial convention. No density, model comparison, or
small-span failure statement is added as a premise. -/
theorem eventually_prefix_comparison
    {a : ℕ → ℕ} (ha : StrictMono a)
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (2000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v))
    (M : ℕ → ℕ)
    (hM : Tendsto (fun X ↦ (M X : ℝ) / CoreRoughEveryWindow.logGap Ψ X)
      atTop (𝓝 κ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ f : Finset ℕ → ℂ,
      (∀ K ∈ (offsetWindow (CoreRoughEveryWindow.smallSpan Ψ M X)).powerset.filter
        (fun K ↦ K.card = M X), ‖f K‖ ≤ 1) →
      ‖CoreRoughEveryWindow.prefixMean a X
          (CoreRoughEveryWindow.smallSpan Ψ M X) (M X) f -
        CoreRoughEveryWindow.complexMean
          (CoreRoughEveryWindow.smallSpan Ψ M X) (M X)
          (actualRootLaw (zPsi Ψ X)
            (CoreRoughEveryWindow.smallSpan Ψ M X)) f‖ < ε := by
  have hb : StrictMono (movingRoughSequence (zPsi Ψ)) :=
    movingRoughSequence_strictMono hSlope.eventually_zPsi_lt
  have hsame := eventually_prefixMean_eq_of_range_agreement hb ha
    (eventually_movingRough_range_iff hSlope hrange)
  have hpos := CoreRoughEveryWindow.eventually_rank_pos hSlope hκ M hM
  have hcanon := CoreRoughEveryWindow.eventually_prefix_comparison
    hκ hSlope hC hreg M hM hε
  filter_upwards [hsame, hpos, hcanon] with X hsameX hposX hcanonX
  intro f hf
  have hh := hcanonX f hf
  rw [hsameX (CoreRoughEveryWindow.smallSpan Ψ M X) (M X) f hposX] at hh
  exact hh

/-- The explicit `O(sqrt(log G))` every-window profile in the frozen paper,
again for any fixed finite initial convention. -/
theorem eventually_prefix_comparison_of_sqrt_error
    {a : ℕ → ℕ} (ha : StrictMono a)
    {Ψ dΨ : ℝ → ℝ} {κ C D : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (2000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v))
    (M : ℕ → ℕ) (hD : 0 ≤ D)
    (hM : ∀ᶠ X : ℕ in atTop,
      |(M X : ℝ) - κ * CoreRoughEveryWindow.logGap Ψ X| ≤
        D * Real.sqrt (CoreRoughEveryWindow.logGap Ψ X))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ f : Finset ℕ → ℂ,
      (∀ K ∈ (offsetWindow (CoreRoughEveryWindow.smallSpan Ψ M X)).powerset.filter
        (fun K ↦ K.card = M X), ‖f K‖ ≤ 1) →
      ‖CoreRoughEveryWindow.prefixMean a X
          (CoreRoughEveryWindow.smallSpan Ψ M X) (M X) f -
        CoreRoughEveryWindow.complexMean
          (CoreRoughEveryWindow.smallSpan Ψ M X) (M X)
          (actualRootLaw (zPsi Ψ X)
            (CoreRoughEveryWindow.smallSpan Ψ M X)) f‖ < ε :=
  eventually_prefix_comparison ha hκ hSlope hC hreg hrange M
    (CoreRoughEveryWindow.tendsto_rank_ratio_of_sqrt_error
      hSlope M hD hM) hε

end

end PrimeGapNormality.Prime.CoreRoughFiniteConvention
