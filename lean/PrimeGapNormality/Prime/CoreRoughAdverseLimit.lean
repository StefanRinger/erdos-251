import PrimeGapNormality.Prime.CoreRoughCellCountBounds
import PrimeGapNormality.Prime.CoreRoughCellErrorLimit
import PrimeGapNormality.Prime.CoreRoughSliceAdditiveBudget
import PrimeGapNormality.Prime.CoreRoughShapeConclusion

/-!
# Actual growing-order sliced adverse budget

The arithmetic tuple in a j-point inclusion is insert 0 E, hence has j+1
sites. The finite bound below retains this exact root convention and the
complete-cell normalization. Relative and additive costs are distinct.
The final endpoint discharges the actual adverse budget and gives literal
positive ShapeS without any count, density, model, or shape premise.
-/

namespace PrimeGapNormality.Prime.CoreRoughAdverseLimit

open Finset Filter
open CoreRoughThreshold CoreRoughSyntheticScale CoreRoughProfileError
  CoreRoughCellAsymptotics CoreRoughPhysicalSlices CoreRoughSieveBudget
  CoreRoughSliceLaws CoreRoughStoppedTransfer CoreRoughCellCountBounds
  CoreRoughSliceAdditiveBudget
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1000000

def adverse (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) : ℝ :=
  Stopped.adverseBudget (offsetWindow (roughProfileS κ (zPsi Ψ X)))
    (empirical κ Ψ J X) (model κ Ψ J X)
    (roughProfileL κ (zPsi Ψ X)) (profileRank κ Ψ X)

theorem adverse_nonneg (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) :
    0 ≤ adverse κ Ψ J X := by
  unfold adverse Stopped.adverseBudget Stopped.adverseLayer
  exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun E _ => le_max_right _ _)

theorem adverse_le_uniform_cell_bound (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ)
    (hZ : 0 < rootNormalization J Ψ X) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcell : ∀ i ∈ range (cellCount J X), ∀ F : Finset ℕ,
      F ⊆ insert 0 (offsetWindow (roughProfileS κ (zPsi Ψ X))) →
      1 ≤ F.card → F.card ≤ profileRank κ Ψ X + 1 →
      |((CoreRoughMovingCount.movingTupleInterval (zPsi Ψ) F (cellStart J X i)
          (roughCellLength J X)).card : ℝ) -
        (roughCellLength J X : ℝ) * finiteTupleSieveProduct F (cellCutoff J Ψ X i)| ≤
          δ * ((roughCellLength J X : ℝ) * finiteTupleSieveProduct F (cellCutoff J Ψ X i)) +
            cellCRTError κ Ψ X)
    (hm : ∀ j : ℕ, j ≤ profileRank κ Ψ X + 1 →
      Stopped.countMoment (offsetWindow (roughProfileS κ (zPsi Ψ X)))
        (model κ Ψ J X) j ≤
          2 * (((5 : ℝ) * (roughProfileL κ (zPsi Ψ X) : ℝ)) ^ j / (j.factorial : ℝ))) :
    adverse κ Ψ J X ≤
      2 * δ * Real.exp (10 * (roughProfileL κ (zPsi Ψ X) : ℝ)) + layeredCost κ J Ψ X := by
  have hE0 : 0 ≤ uniformCRT κ J Ψ X := by
    have hlog := Real.log_natCast_nonneg (cubeRootLevel X)
    unfold uniformCRT
    positivity
  have hh := CoreRoughLayerMultiplicity.adverseBudget_le_exp_additive
    (offsetWindow (roughProfileS κ (zPsi Ψ X))) (empirical κ Ψ J X) (model κ Ψ J X)
    (roughProfileL κ (zPsi Ψ X)) (profileRank κ Ψ X) hδ hE0 (by
      intro j hj E hE
      have hsub := mem_powerset.mp (mem_filter.mp hE).1
      have hcard := inserted_card hE
      have hb := inclusion_le_of_cell_errors (zPsi Ψ) (cellCutoff J Ψ X) (X + 1)
        (roughCellLength J X) (cellCount J X) (roughProfileS κ (zPsi Ψ X)) hZ hsub
        δ (cellCRTError κ Ψ X) (by
          intro i hi
          have hs : insert 0 E ⊆ insert 0 (offsetWindow (roughProfileS κ (zPsi Ψ X))) := by
            intro n hn
            rcases mem_insert.mp hn with rfl | hn
            · exact mem_insert_self _ _
            · exact mem_insert_of_mem (hsub hn)
          exact hcell i hi (insert 0 E) hs (by omega) (by
            have hju := (mem_Icc.mp hj).2
            omega))
      convert hb using 1 <;>
        simp only [empirical, model, uniformCRT, cellCRTError, rootNormalization] <;>
        ring)
    (fun j hj => hm j ((mem_Icc.mp hj).2.trans (Nat.le_succ _)))
  simpa only [adverse, layeredCost, offsetWindow, Nat.card_Icc, Nat.add_sub_cancel] using hh

theorem tendsto_adverse_zero {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) (hJrank : 168 * κ < (J : ℝ) + 1) :
    Tendsto (adverse κ Ψ J) atTop (𝓝 0) := by
  have hrel := (CoreRoughCellErrorLimit.tendsto_uniformCellRelativeError_weighted_zero
    hκ hSlope hC hJrank).const_mul 2
  have hlim := hrel.add (tendsto_layeredCost_zero hκ hSlope hC hreg hJ)
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun X => adverse_nonneg κ Ψ J X) ?_ hlim
  filter_upwards [CoreRoughCellErrorLimit.eventually_cell_tuple_error_uniform
      hκ hSlope hC hreg hJ hJrank,
    eventually_rootNormalization_pos hSlope hC hreg hJ,
    eventually_model_moments hκ hSlope hC hreg hJ] with X hcell hZ hm
  have hh := adverse_le_uniform_cell_bound κ Ψ J X hZ
    (CoreRoughCellErrorLimit.uniformCellRelativeError_nonneg κ hC J Ψ X) hcell hm
  exact hh.trans_eq (by ring)

/-- Genuine positive shape transfer for the actual moving-rough sequence.
The slicing exponent is chosen from κ alone; the fixed slope coefficient
is independent of any eventual polynomial width, period, or coefficients.
No density, moment, normality, or comparison estimate is an input. -/
theorem sequencePositiveShapeS
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    CoreSequenceSTConsumer.SequencePositiveShapeS
      (CoreMovingRoughSequence.movingRoughSequence (zPsi Ψ))
      (fun X => roughSyntheticScale (zPsi Ψ X)) κ 1 := by
  let J := CoreRoughRelativeHazardBudget.slicingExponent κ
  have hJ := CoreRoughRelativeHazardBudget.slicingExponent_large κ
  exact CoreRoughShapeConclusion.sequencePositiveShapeS_of_actual_adverse_zero
    hκ hSlope hC hreg (J := J) hJ.1
    (tendsto_adverse_zero hκ hSlope hC hreg hJ.1 hJ.2)

end
end PrimeGapNormality.Prime.CoreRoughAdverseLimit
