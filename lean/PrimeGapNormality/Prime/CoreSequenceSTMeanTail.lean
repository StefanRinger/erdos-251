import PrimeGapNormality.Prime.CoreSequenceSTClassification
import PrimeGapNormality.Prime.CoreSequenceWindowGrowthFromS

/-!
# Concrete sequence S/T with a bare mean-tail input

The historical `GapTailT` bundle includes geometric summability of the
sequence positions.  For the paper interface that field is redundant:
concrete ShapeS plus eventual nonempty physical windows gives growing window
counts, hence subexponential positions and the required summability.

We retain eventual nonemptiness explicitly.  With the project's zero-on-empty
empirical convention, positive ShapeS alone cannot imply it.  This file is
still specifically about `SequencePositiveShapeS` and `finiteRootMix (T X)`,
not arbitrary calibrated mixtures.
-/

namespace PrimeGapNormality.Prime.CoreSequenceSTMeanTail

open Finset Filter MvPolynomial CoreCyclic
open CoreSequenceSTConsumer CoreSequenceSTClassification
open CoreSequenceSubexponentialGrowth
open scoped Topology Classical

noncomputable section

/-- The actual first-gap mean bound, with eventual nonempty windows but no
separate summability field. -/
def MeanGapTailT (a : ℕ → ℕ) (rho : ℝ) (G : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ X : ℕ in atTop,
      0 < (seqWindow a X).card ∧
        windowAvgReal (seqWindow a X)
            (fun n ↦ seqGapTail rho a (n + stdProfileL rho (G X))) ≤
          C * G X

theorem meanGapTail_eventually_nonempty
    {a : ℕ → ℕ} {rho : ℝ} {G : ℕ → ℝ}
    (h : MeanGapTailT a rho G) :
    ∀ᶠ X : ℕ in atTop, 0 < (seqWindow a X).card := by
  obtain ⟨C, hC, htail⟩ := h
  exact htail.mono fun X hX ↦ hX.1

/-- ShapeS and the bare mean-tail estimate reconstruct the legacy `GapTailT`
bundle; its summability component is proved, not assumed. -/
theorem gapTailT_of_shapeS_and_meanTail
    {a T : ℕ → ℕ} (ha : StrictMono a) {κ c : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hS : SequencePositiveShapeS a T κ c)
    (hMean : MeanGapTailT a (localTailBase κ) (windowG ∘ T)) :
    GapTailT a (localTailBase κ) (windowG ∘ T) := by
  have hrho : 1 < localTailBase κ := localTailBase_one_lt hκ
  have hG : Tendsto (windowG ∘ T) atTop atTop :=
    tendsto_windowG_atTop.comp hmodelScale
  have hcount : WindowCountToInfinity a :=
    CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS
      ha hκ hc hmodelScale hS (meanGapTail_eventually_nonempty hMean)
  have hsub := sequence_hasSubexponentialGrowth ha hcount
  have hsum : Summable (fun n : ℕ ↦
      (a n : ℝ) / localTailBase κ ^ n) :=
    hsub.summable_div_pow hrho
  obtain ⟨C, hC, htail⟩ := hMean
  exact ⟨hrho, hG, hsum, C, hC, htail⟩

/-- Rational-or-normal classification with only the bare actual mean-tail
estimate.  Count growth and geometric summability are internal conclusions. -/
theorem local_classification_of_shapeS_and_meanTail
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {κ c : ℝ} (hκpos : 0 < κ)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hS : SequencePositiveShapeS a T κ c)
    (hMean : MeanGapTailT a (localTailBase κ) (windowG ∘ T)) :
    (normalForm hB hk F = 0 ∧
      ∃ q : ℚ,
        coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F =
          (q : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k)
        (coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap a n : ℝ)) F)) := by
  have hTail := gapTailT_of_shapeS_and_meanTail
    ha hκpos hc hmodelScale hS hMean
  exact local_classification_of_shapeS ha hB hk phase F hκ hc
    hmodelScale hTail hS

end
end PrimeGapNormality.Prime.CoreSequenceSTMeanTail
