import PrimeGapNormality.Prime.CoreRoughLocalNormality
import PrimeGapNormality.Prime.CoreSequenceSTDimension

/-!
# Dimension of the actual moving-rough series space

Only the literal slope and cutoff regularity enter the arithmetic end
theorem. The space is the genuine rational span of 1 and all local series
of the given width, degree and period. Source pending central acceptance.
-/

namespace PrimeGapNormality.Prime.CoreRoughDimensionEnd

open Filter CoreCyclic CoreRoughThreshold CoreRoughSyntheticScale
open CoreMovingRoughSequence CoreSequenceSTConsumer
open scoped Topology Classical
noncomputable section

theorem finrank_seriesSpan
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hH : 0 < H) (hD : 0 < D)
    (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ) :
    Module.finrank ℚ (CoreSequenceSTDimension.seriesSpan
      (movingRoughSequence (zPsi Ψ)) B H D hk phase) =
        1 + k * (H + D - 1).choose (D - 1) := by
  let a := movingRoughSequence (zPsi Ψ)
  let T : ℕ → ℕ := fun X ↦ roughSyntheticScale (zPsi Ψ X)
  have ha : StrictMono a := movingRoughSequence_strictMono hSlope.eventually_zPsi_lt
  have hT : Tendsto T atTop atTop :=
    CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope
  have hTail : GapTailT a (localTailBase κ) (windowG ∘ T) :=
    CoreRoughLocalNormality.movingRough_gapTailT hκpos hSlope hC hreg
  have hS : SequencePositiveShapeS a T κ 1 :=
    CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
  exact CoreSequenceSTDimension.finrank_seriesSpan_of_shapeS
    ha hB hk phase hH hD hκ (by norm_num : (0 : ℝ) < 1) hT hTail hS

end
end PrimeGapNormality.Prime.CoreRoughDimensionEnd
