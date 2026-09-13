import PrimeGapNormality.Prime.CoreRoughStoppedTransfer
import PrimeGapNormality.Prime.CoreRoughPhysicalTestTransfer
import PrimeGapNormality.Prime.CoreSequenceSTConsumer

/-!
# Literal positive ShapeS after the actual sliced adverse budget

This is the final normalization/test consumer. Its one remaining arithmetic
premise is the explicitly displayed adverse budget of the actual sliced
laws. It is not yet an unconditional rough theorem: the cell-count and
additive-envelope assembly must discharge that premise. All density,
model failure/remainder, bounded-model comparison, and discarded-cell costs
are supplied by actual preceding results.
-/

namespace PrimeGapNormality.Prime.CoreRoughShapeConclusion

open Finset Filter
open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSyntheticScale
  CoreRoughProfileError CoreRoughCellAsymptotics CoreRoughPhysicalSlices
  CoreRoughSliceLaws CoreRoughStoppedTransfer CoreSequencePatternLaw
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1000000

def stoppedError (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) : ℝ :=
  Stopped.shapeL1 (offsetWindow (roughProfileS κ (zPsi Ψ X)))
    (empirical κ Ψ J X) (model κ Ψ J X) (roughProfileL κ (zPsi Ψ X)) +
  Stopped.failureMass (offsetWindow (roughProfileS κ (zPsi Ψ X)))
    (empirical κ Ψ J X) (roughProfileL κ (zPsi Ψ X))

theorem tendsto_stoppedError_zero {Ψ dΨ : ℝ → ℝ} {A C κ : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J)
    (hAdverse : Tendsto (fun X : ℕ => Stopped.adverseBudget
      (offsetWindow (roughProfileS κ (zPsi Ψ X))) (empirical κ Ψ J X) (model κ Ψ J X)
      (roughProfileL κ (zPsi Ψ X)) (profileR (roughProfileL κ (zPsi Ψ X)) 20))
      atTop (𝓝 0)) :
    Tendsto (stoppedError κ Ψ J) atTop (𝓝 0) := by
  have hmass := ((tendsto_empirical_mass_one (κ := κ) hSlope hC hreg hJ).sub
    (tendsto_const_nhds (x := (1 : ℝ)))).abs
  simp only [sub_self, abs_zero] at hmass
  have hlim := (((tendsto_model_failure_zero hκ hSlope hC hreg hJ).add
    ((tendsto_model_remainder_zero hκ hSlope hC hreg hJ).const_mul 2)).add
    (hAdverse.const_mul 2)).add hmass
  simp only [mul_zero, add_zero] at hlim
  have hL : Tendsto (fun X => roughProfileL κ (zPsi Ψ X)) atTop atTop :=
    ((tendsto_profileL_atTop hκ).comp
      CoreRoughScaleLimits.tendsto_roughSyntheticScale_atTop).comp hSlope.tendsto_zPsi_atTop
  refine squeeze_zero' (Eventually.of_forall fun X => ?_) ?_ hlim
  · unfold stoppedError Stopped.shapeL1 Stopped.failureMass
    exact add_nonneg (Finset.sum_nonneg fun K _ => abs_nonneg _)
      (Finset.sum_nonneg fun U _ => empirical_nonneg _ _ _ _ _)
  · filter_upwards [eventually_rootNormalization_pos hSlope hC hreg hJ,
      hL.eventually_ge_atTop 1] with X hZ hLX
    exact stopped_comparison κ Ψ J X hZ hLX

def shortMean (Ω : Finset ℕ) (μ : Finset ℕ → ℝ) (L : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ U ∈ Ω.powerset.filter (fun U => U.card = L), f U * Stopped.shortShapeMass Ω μ L U

def configurationTest (bad : ℝ) (L : ℕ) (f : Finset ℕ → ℝ) (U : Finset ℕ) : ℝ :=
  if L ≤ U.card then f (Stopped.firstL L U) else bad

theorem configurationTest_abs_le (Ω : Finset ℕ) (L : ℕ) (f : Finset ℕ → ℝ)
    {bad : ℝ} (hb : |bad| ≤ 1)
    (hf : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), |f K| ≤ 1) :
    ∀ U ∈ Ω.powerset, |configurationTest bad L f U| ≤ 1 := by
  intro U hU
  unfold configurationTest
  split_ifs with hL
  · exact hf _ (mem_filter.mpr ⟨mem_powerset.mpr
      (Stopped.firstL_subset.trans (mem_powerset.mp hU)), Stopped.firstL_card hL⟩)
  · exact hb

theorem configurationTest_zero_eval (Ω : Finset ℕ) (μ : Finset ℕ → ℝ)
    (L : ℕ) (f : Finset ℕ → ℝ) :
    (∑ U ∈ Ω.powerset, μ U * configurationTest 0 L f U) = shortMean Ω μ L f :=
  (firstL_test_eq_pushforward Ω μ L f).symm

theorem configurationTest_one_eval (Ω : Finset ℕ) (μ : Finset ℕ → ℝ)
    (L : ℕ) (f : Finset ℕ → ℝ) :
    (∑ U ∈ Ω.powerset, μ U * configurationTest 1 L f U) =
      Stopped.failureMass Ω μ L + shortMean Ω μ L f := by
  unfold shortMean
  rw [firstL_test_eq_pushforward]
  unfold Stopped.failureMass
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro U hU
  by_cases hL : L ≤ U.card
  · simp only [configurationTest, if_pos hL, if_neg (Nat.not_lt.mpr hL), zero_add]
  · simp only [configurationTest, if_neg hL, if_pos (Nat.lt_of_not_ge hL),
      mul_one, mul_zero, add_zero]

/-- The remaining hypothesis is a literal actual-law arithmetic limit, not
a new shape/reference oracle. It will be discharged by uniform cell sieve
estimates and the actual relative/additive budgets. -/
theorem sequencePositiveShapeS_of_actual_adverse_zero
    {Ψ dΨ : ℝ → ℝ} {A C κ : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J)
    (hAdverse : Tendsto (fun X : ℕ => Stopped.adverseBudget
      (offsetWindow (roughProfileS κ (zPsi Ψ X))) (empirical κ Ψ J X) (model κ Ψ J X)
      (roughProfileL κ (zPsi Ψ X)) (profileR (roughProfileL κ (zPsi Ψ X)) 20))
      atTop (𝓝 0)) :
    CoreSequenceSTConsumer.SequencePositiveShapeS
      (movingRoughSequence (zPsi Ψ)) (fun X => roughSyntheticScale (zPsi Ψ X)) κ 1 := by
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  have hstop := (tendsto_order.mp (tendsto_stoppedError_zero hκ hSlope hC hreg hJ hAdverse)).2
    (ε / 3) he
  have hmodel := (tendsto_order.mp (tendsto_modelDistance_zero hκ hSlope hC hreg hJ)).2
    (ε / 3) he
  have hphysical := CoreRoughPhysicalTestTransfer.eventually_bounded_test_error hSlope hC hreg hJ
    (fun X => roughProfileS κ (zPsi Ψ X)) he
  filter_upwards [hstop, hmodel, hphysical] with X hstopX hmodelX hphysicalX
  intro f hf0 hf1
  let Ω := offsetWindow (roughProfileS κ (zPsi Ψ X))
  let L := roughProfileL κ (zPsi Ψ X)
  let μ := patternMass (movingRoughSequence (zPsi Ψ)) X Ω
  let ν := finiteRootMix (roughSyntheticScale (zPsi Ψ X)) (roughProfileS κ (zPsi Ψ X))
  have hf : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), |f K| ≤ 1 := by
    intro K hK
    rw [abs_of_nonneg (hf0 K hK)]
    exact hf1 K hK
  have hone := configurationTest_abs_le Ω L f (bad := 1) (by norm_num) hf
  have hzero := configurationTest_abs_le Ω L f (bad := 0) (by norm_num) hf
  have hactual := hphysicalX (configurationTest 1 L f) hone
  change |(∑ U ∈ Ω.powerset, μ U * configurationTest 1 L f U) -
    (∑ U ∈ Ω.powerset, empirical κ Ψ J X U * configurationTest 1 L f U)| < ε / 3 at hactual
  have hstopped := Stopped.abs_stopped_eval_sub_le (Ω := Ω)
    (μ := empirical κ Ψ J X) (ν := model κ Ψ J X) (L := L)
    (φ := f) (ψ := fun _ => 1) hf (fun U _ => by norm_num)
    (fun U _ => empirical_nonneg _ _ _ _ _)
  have hstopped' : |(∑ U ∈ Ω.powerset,
      empirical κ Ψ J X U * configurationTest 1 L f U) -
        shortMean Ω (model κ Ψ J X) L f| ≤ stoppedError κ Ψ J X := by
    simpa only [configurationTest, shortMean, mul_comm, stoppedError] using hstopped
  have hmix := CoreRoughMixtureComparison.bounded_test_abs_sub_le_massL1 Ω
    (model κ Ψ J X) ν (configurationTest 0 L f) (by norm_num : (0 : ℝ) ≤ 1) hzero
  rw [configurationTest_zero_eval, configurationTest_zero_eval, one_mul] at hmix
  change |shortMean Ω (model κ Ψ J X) L f - shortMean Ω ν L f| ≤
    modelDistance κ Ψ J X at hmix
  have ha := (le_abs_self _).trans_lt hactual
  have hs := (le_abs_self _).trans hstopped'
  have hm := (le_abs_self _).trans hmix
  rw [configurationTest_one_eval] at ha
  change Stopped.failureMass Ω μ L + shortMean Ω μ L f ≤
    1 * shortMean Ω ν L f + ε
  linarith

end
end PrimeGapNormality.Prime.CoreRoughShapeConclusion
