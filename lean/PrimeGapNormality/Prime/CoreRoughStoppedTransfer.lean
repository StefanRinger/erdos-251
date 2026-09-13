import PrimeGapNormality.Prime.CoreRoughPhysicalSlices
import PrimeGapNormality.Prime.CoreRoughAdverseBudget
import PrimeGapNormality.Prime.CoreRoughRemainderScalar
import PrimeGapNormality.Prime.CoreRoughRelativeHazardBudget
import PrimeGapNormality.Prime.CoreRoughAdditiveBudget
import PrimeGapNormality.Prime.CoreRoughLayerMultiplicity
import PrimeGapNormality.Prime.CoreRoughModelLimit
import PrimeGapNormality.Prime.CrtProfileRParity
import PrimeGapNormality.Prime.StoppedUnequalMass

/-!
# Actual sliced laws in the unequal-mass stopped comparison

This module keeps the literal full-cell empirical law and the Euler-weighted
rooted mixture on the same normalization. Relative tuple errors are charged
to model factorial moments; the additive CRT term is charged separately.
The final short physical interval does not occur in these inclusion errors.
-/

namespace PrimeGapNormality.Prime.CoreRoughStoppedTransfer

open Finset Filter
open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSyntheticScale
  CoreRoughProfileError CoreRoughCellAsymptotics CoreRoughPhysicalSlices
  CoreRoughSliceLaws CoreRoughSliceModelBounds CoreRoughAdverseBudget
  CoreRoughRemainderScalar CoreRoughMovingCount
open scoped Topology Classical
noncomputable section

set_option maxHeartbeats 1000000

/-- Exact finite inclusion bound for the genuine laws. `hcell` is the
finite arithmetic estimate to be supplied by the actual cell sieve; it is
not a field in either probability law. -/
theorem inclusion_le_of_cell_errors
    (z y : ℕ → ℕ) (a H q S : ℕ) (hZ : 0 < normalization H q y)
    {E : Finset ℕ} (hE : E ⊆ offsetWindow S) (δ Eadd : ℝ)
    (hcell : ∀ i ∈ range q,
      |((movingTupleInterval z (insert 0 E) (a + i * H) H).card : ℝ) -
        (H : ℝ) * finiteTupleSieveProduct (insert 0 E) (y i)| ≤
          δ * ((H : ℝ) * finiteTupleSieveProduct (insert 0 E) (y i)) + Eadd) :
    |Stopped.inclusionMass (offsetWindow S) (empiricalLaw z y a H q S) E -
      Stopped.inclusionMass (offsetWindow S) (modelLaw y H q S) E| ≤
        δ * Stopped.inclusionMass (offsetWindow S) (modelLaw y H q S) E +
          (q : ℝ) * Eadd / normalization H q y := by
  have hh := inclusion_error_of_cell_errors z y a H q S hZ hE
    (fun i => δ * ((H : ℝ) * finiteTupleSieveProduct (insert 0 E) (y i)) + Eadd) hcell
  refine hh.trans_eq ?_
  rw [modelLaw_inclusion y H q S hE, sum_add_distrib, ← mul_sum,
    sum_const, card_range, nsmul_eq_mul]
  ring

/-- Finite actual sieve errors feed the genuine sliced adverse budget.
Arithmetic tuples have size `j+1`, because zero is not in offsetWindow S. -/
theorem adverse_le_of_cell_errors
    (z y : ℕ → ℕ) (a H q S L r : ℕ) (hZ : 0 < normalization H q y)
    {δ : ℝ} (hδ : 0 ≤ δ) (Eadd : ℕ → ℝ)
    (hcell : ∀ j ∈ Icc L r, ∀ E ∈ (offsetWindow S).powerset.filter
        (fun E => E.card = j), ∀ i ∈ range q,
      |((movingTupleInterval z (insert 0 E) (a + i * H) H).card : ℝ) -
        (H : ℝ) * finiteTupleSieveProduct (insert 0 E) (y i)| ≤
          δ * ((H : ℝ) * finiteTupleSieveProduct (insert 0 E) (y i)) + Eadd j)
    (hm : ∀ j ∈ Icc L r,
      Stopped.countMoment (offsetWindow S) (modelLaw y H q S) j ≤
        2 * (((5 : ℝ) * L) ^ j / (j.factorial : ℝ))) :
    Stopped.adverseBudget (offsetWindow S) (empiricalLaw z y a H q S)
        (modelLaw y H q S) L r ≤
      2 * δ * Real.exp (10 * (L : ℝ)) +
        ∑ j ∈ Icc L r, (Nat.choose (j - 1) (L - 1) : ℝ) *
          ((offsetWindow S).card.choose j : ℝ) *
            ((q : ℝ) * Eadd j / normalization H q y) := by
  have hh := adverseBudget_le_relative_additive (offsetWindow S)
    (empiricalLaw z y a H q S) (modelLaw y H q S) L r δ
    (fun j => (q : ℝ) * Eadd j / normalization H q y) (by
      intro j hj E hE
      exact inclusion_le_of_cell_errors z y a H q S hZ
        (mem_powerset.mp (mem_filter.mp hE).1) δ (Eadd j) (hcell j hj E hE))
  have hmoment := mul_le_mul_of_nonneg_left
    (weighted_countMoment_le_exp (offsetWindow S) (modelLaw y H q S) L r hm) hδ
  exact hh.trans ((_root_.add_le_add hmoment le_rfl).trans_eq (by ring))

theorem inserted_card {S j : ℕ} {E : Finset ℕ}
    (hE : E ∈ (offsetWindow S).powerset.filter (fun E => E.card = j)) :
    (insert 0 E).card = j + 1 := by
  have hsub := mem_powerset.mp (mem_filter.mp hE).1
  have hzero : 0 ∉ E := by
    intro hz
    have h := hsub hz
    simp only [offsetWindow, mem_Icc] at h
    omega
  rw [card_insert_of_notMem hzero, (mem_filter.mp hE).2]

def empirical (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) : Finset ℕ → ℝ :=
  empiricalLaw (zPsi Ψ) (cellCutoff J Ψ X) (X + 1)
    (roughCellLength J X) (cellCount J X) (roughProfileS κ (zPsi Ψ X))

def model (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) : Finset ℕ → ℝ :=
  modelLaw (cellCutoff J Ψ X) (roughCellLength J X) (cellCount J X)
    (roughProfileS κ (zPsi Ψ X))

theorem empirical_nonneg (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) (U : Finset ℕ) :
    0 ≤ empirical κ Ψ J X U := empiricalLaw_nonneg _ _ _ _ _ _ _

theorem model_nonneg (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) (U : Finset ℕ) :
    0 ≤ model κ Ψ J X U := modelLaw_nonneg _ _ _ _ _

theorem model_total (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ)
    (hZ : 0 < rootNormalization J Ψ X) :
    (∑ U ∈ (offsetWindow (roughProfileS κ (zPsi Ψ X))).powerset,
      model κ Ψ J X U) = 1 := modelLaw_total _ _ _ _ hZ

theorem tendsto_empirical_mass_one {Ψ dΨ : ℝ → ℝ} {A C κ : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    Tendsto (fun X : ℕ => ∑ U ∈ (offsetWindow (roughProfileS κ (zPsi Ψ X))).powerset,
      empirical κ Ψ J X U) atTop (𝓝 1) :=
  tendsto_empirical_total_one hSlope hC hreg hJ (fun X => roughProfileS κ (zPsi Ψ X))

theorem eventually_cellCutoff_ge {Ψ dΨ : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) (J : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ i ∈ range (cellCount J X),
      zPsi Ψ X ≤ cellCutoff J Ψ X i := by
  filter_upwards [CoreRoughDyadicDensity.eventually_zPsi_mono_on_triple hC hreg]
    with X hX
  intro i hi
  have hs := cellStart_mem hi
  exact hX X ⟨le_rfl, by omega⟩ (cellStart J X i)
    ⟨hs.1, hs.2.trans (by omega)⟩ hs.1

theorem eventually_model_moments {Ψ dΨ : ℝ → ℝ} {A C κ : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    ∀ᶠ X : ℕ in atTop, ∀ j : ℕ,
      j ≤ profileR (roughProfileL κ (zPsi Ψ X)) 20 + 1 →
      Stopped.countMoment (offsetWindow (roughProfileS κ (zPsi Ψ X)))
        (model κ Ψ J X) j ≤
          2 * (((5 : ℝ) * (roughProfileL κ (zPsi Ψ X) : ℝ)) ^ j / (j.factorial : ℝ)) := by
  filter_upwards [hSlope.tendsto_zPsi_atTop.eventually (eventually_profile_moment_bound hκ),
    eventually_rootNormalization_pos hSlope hC hreg hJ,
    eventually_cellCutoff_ge hC hreg J] with X hm hZ hy
  exact hm (roughCellLength J X) (cellCount J X) (cellCutoff J Ψ X) hZ hy

theorem tendsto_model_remainder_zero {Ψ dΨ : ℝ → ℝ} {A C κ : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    Tendsto (fun X : ℕ => Stopped.modelRemainder
      (offsetWindow (roughProfileS κ (zPsi Ψ X))) (model κ Ψ J X)
      (roughProfileL κ (zPsi Ψ X)) (profileR (roughProfileL κ (zPsi Ψ X)) 20))
      atTop (𝓝 0) := by
  have hL : Tendsto (fun X => roughProfileL κ (zPsi Ψ X)) atTop atTop :=
    ((tendsto_profileL_atTop hκ).comp
      CoreRoughScaleLimits.tendsto_roughSyntheticScale_atTop).comp hSlope.tendsto_zPsi_atTop
  have hs := (tendsto_small_remainder_scalar.comp hL).const_mul 2
  simp only [mul_zero] at hs
  refine squeeze_zero' (Eventually.of_forall fun X => ?_) ?_ hs
  · unfold Stopped.modelRemainder
    exact Finset.sum_nonneg fun U hU => mul_nonneg (model_nonneg _ _ _ _ _)
      (crtMixUnnormRem_countEnvelope_nonneg _ _ _)
  · filter_upwards [eventually_model_moments hκ hSlope hC hreg hJ,
      hL.eventually_ge_atTop 1] with X hm hLX
    have hh := Stopped.modelRemainder_le
      (Ω := offsetWindow (roughProfileS κ (zPsi Ψ X))) (ν := model κ Ψ J X)
      hLX (profileR_ge (roughProfileL κ (zPsi Ψ X)) 20)
      (fun U _ => model_nonneg _ _ _ _ _)
    have hbound := hh.trans (mul_le_mul_of_nonneg_left (hm _ le_rfl) (Nat.cast_nonneg _))
    exact hbound.trans_eq (by dsimp only [Function.comp_apply]; ring)

/-- Literal unequal-mass stopped comparison on all full cells. The final
physical remainder is deliberately absent; restore it only after this
comparison and the scalar mass normalization. -/
theorem stopped_comparison (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ)
    (hZ : 0 < rootNormalization J Ψ X)
    (hL : 1 ≤ roughProfileL κ (zPsi Ψ X)) :
    let Ω := offsetWindow (roughProfileS κ (zPsi Ψ X))
    let L := roughProfileL κ (zPsi Ψ X)
    let r := profileR L 20
    Stopped.shapeL1 Ω (empirical κ Ψ J X) (model κ Ψ J X) L +
        Stopped.failureMass Ω (empirical κ Ψ J X) L ≤
      Stopped.failureMass Ω (model κ Ψ J X) L +
        2 * Stopped.modelRemainder Ω (model κ Ψ J X) L r +
        2 * Stopped.adverseBudget Ω (empirical κ Ψ J X) (model κ Ψ J X) L r +
        |(∑ U ∈ Ω.powerset, empirical κ Ψ J X U) - 1| := by
  dsimp only
  have hh := Stopped.stoppedShapeL1_add_failure_le_unequalMass
    (Ω := offsetWindow (roughProfileS κ (zPsi Ψ X))) hL
    (profileR_ge (roughProfileL κ (zPsi Ψ X)) 20)
    (crtMixProf_odd (roughProfileL κ (zPsi Ψ X)) 20)
    (fun U _ => empirical_nonneg κ Ψ J X U)
    (fun U _ => model_nonneg κ Ψ J X U)
  rwa [model_total κ Ψ J X hZ] at hh

def oldModelDistance (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) : ℝ :=
  ∑ U ∈ (offsetWindow (roughProfileS κ (zPsi Ψ X))).powerset,
    |actualRootLaw (zPsi Ψ X) (roughProfileS κ (zPsi Ψ X)) U - model κ Ψ J X U|

private theorem profileL_le_weightedRank (κ : ℝ) (z : ℕ) :
    (roughProfileL κ z : ℝ) ≤ CoreRoughRelativeHazardBudget.weightedRank κ z := by
  have hr : (roughProfileL κ z : ℝ) ≤ ((profileR (roughProfileL κ z) 20 + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr ((profileR_ge _ _).trans (Nat.le_succ _))
  have he : (1 : ℝ) ≤ Real.exp (10 * (roughProfileL κ z : ℝ)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  exact hr.trans (by
    unfold CoreRoughRelativeHazardBudget.weightedRank
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he
      (Nat.cast_nonneg (profileR (roughProfileL κ z) 20 + 1)))

theorem tendsto_global_depth_cost_zero {Ψ : ℝ → ℝ} {A C κ : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ A) :
    Tendsto (fun X : ℕ => (roughProfileL κ (zPsi Ψ X) : ℝ) *
      (CoreRoughDyadicDensity.dyadicRootHazard C Ψ X +
        1 / ((zPsi Ψ X : ℝ) - 1))) atTop (𝓝 0) := by
  have hz := hSlope.tendsto_zPsi_atTop
  have hbase := (CoreRoughRelativeHazardBudget.tendsto_profileL_div_log_zero hκ).comp hz
  have hfirst : Tendsto (fun X : ℕ => (roughProfileL κ (zPsi Ψ X) : ℝ) /
      Real.log (X : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hbase
    · filter_upwards [eventually_ge_atTop 1] with X hX
      exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (Nat.one_le_cast.mpr hX))
    · filter_upwards [hSlope.eventually_zPsi_lt, hz.eventually_ge_atTop 2]
        with X hzx hz2
      have hzp : (1 : ℝ) < zPsi Ψ X := by exact_mod_cast (show 1 < zPsi Ψ X by omega)
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Real.log_pos hzp)
        (Real.log_le_log (by linarith) (Nat.cast_le.mpr hzx.le))
  have hsecond : Tendsto (fun X : ℕ => (roughProfileL κ (zPsi Ψ X) : ℝ) /
      Real.sqrt (zPsi Ψ X : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun X => by positivity)
      (Eventually.of_forall fun X => div_le_div_of_nonneg_right
        (profileL_le_weightedRank κ _) (Real.sqrt_nonneg _))
      ((CoreRoughRelativeHazardBudget.tendsto_weightedRank_div_sqrt_zero hκ).comp hz)
  have hthird : Tendsto (fun X : ℕ => (roughProfileL κ (zPsi Ψ X) : ℝ) /
      ((zPsi Ψ X : ℝ) - 1)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hbase
    · filter_upwards [hz.eventually_ge_atTop 2] with X hz2
      have hzR : (2 : ℝ) ≤ zPsi Ψ X := Nat.cast_le.mpr hz2
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · filter_upwards [hz.eventually_ge_atTop 2] with X hz2
      have hzR : (1 : ℝ) < zPsi Ψ X := by exact_mod_cast (show 1 < zPsi Ψ X by omega)
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Real.log_pos hzR)
        (Real.log_le_sub_one_of_pos (by linarith))
  have hh := ((hfirst.const_mul (CoreRoughGlobalCutoff.globalCutoffConstant C)).add
    (hsecond.const_mul (CoreRoughGlobalCutoff.globalCutoffConstant C))).add hthird
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall fun X => by
    unfold CoreRoughDyadicDensity.dyadicRootHazard
    ring

theorem tendsto_oldModelDistance_zero {Ψ dΨ : ℝ → ℝ} {A C κ : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    Tendsto (oldModelDistance κ Ψ J) atTop (𝓝 0) := by
  have hlim := (tendsto_global_depth_cost_zero (C := C) hκ hSlope).const_mul 20
  simp only [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun X => Finset.sum_nonneg fun U _ => abs_nonneg _) ?_ hlim
  have hglobal := CoreRoughGlobalCutoff.eventually_global_cutoff_and_primeLoss hSlope hC
    (show CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative Ψ dΨ C from hreg)
  filter_upwards [eventually_rootNormalization_pos hSlope hC hreg hJ,
    hSlope.tendsto_zPsi_atTop.eventually_ge_atTop 2,
    hSlope.tendsto_zPsi_atTop.eventually
      (CoreRoughSmallWindow.eventually_ahlSmall_window_roughSyntheticScale_lt hκ),
    hSlope.tendsto_zPsi_atTop.eventually (CoreRoughModelCosts.eventually_actual_countMoment_le_two_five hκ),
    hglobal, eventually_ge_atTop 2] with X hZ hz2 hS hm hglobalX hX2
  have hy : ∀ i ∈ range (cellCount J X), zPsi Ψ X ≤ cellCutoff J Ψ X i := by
    intro i hi
    have hs := cellStart_mem hi
    exact (hglobalX (cellStart J X i) ⟨hs.1, hs.2.trans (by omega)⟩).1
  have hδ : ∀ i ∈ range (cellCount J X),
      (∑ p ∈ Nat.primesLE (cellCutoff J Ψ X i) \ Nat.primesLE (zPsi Ψ X), (p : ℝ)⁻¹) ≤
        CoreRoughDyadicDensity.dyadicRootHazard C Ψ X := by
    intro i hi
    have hs := cellStart_mem hi
    exact (hglobalX (cellStart J X i) ⟨hs.1, hs.2.trans (by omega)⟩).2.2
  have hh := massL1_le_prime_hazard (cellCutoff J Ψ X) (roughCellLength J X)
    (cellCount J X) (roughProfileS κ (zPsi Ψ X)) (zPsi Ψ X)
    hZ hz2 hS.le hy hδ
  have hmoment : CoreRoughMixtureComparison.roughFirstMoment (zPsi Ψ X)
      (roughProfileS κ (zPsi Ψ X)) ≤ 10 * (roughProfileL κ (zPsi Ψ X) : ℝ) := by
    rw [CoreRoughModelLimit.firstMoment_eq_countMoment]
    have hm1 := hm 1 (Nat.succ_le_succ (Nat.zero_le _))
    norm_num only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hm1
    linarith
  have hδ0 : 0 ≤ CoreRoughDyadicDensity.dyadicRootHazard C Ψ X +
      1 / ((zPsi Ψ X : ℝ) - 1) := by
    have hzR : (2 : ℝ) ≤ zPsi Ψ X := Nat.cast_le.mpr hz2
    have hl : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr (by omega))
    have hzsub : 0 ≤ (zPsi Ψ X : ℝ) - 1 := by linarith
    have hcoef : 0 ≤ CoreRoughGlobalCutoff.globalCutoffConstant C := by
      unfold CoreRoughGlobalCutoff.globalCutoffConstant
      positivity
    exact add_nonneg
      (add_nonneg (div_nonneg hcoef hl) (div_nonneg hcoef (Real.sqrt_nonneg _)))
      (div_nonneg zero_le_one hzsub)
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmoment (by norm_num : (0 : ℝ) ≤ 2)) hδ0
  exact hh.trans (hmul.trans_eq (by ring))

def modelDistance (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) : ℝ :=
  ∑ U ∈ (offsetWindow (roughProfileS κ (zPsi Ψ X))).powerset,
    |model κ Ψ J X U -
      finiteRootMix (roughSyntheticScale (zPsi Ψ X)) (roughProfileS κ (zPsi Ψ X)) U|

theorem tendsto_modelDistance_zero {Ψ dΨ : ℝ → ℝ} {A C κ : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    Tendsto (modelDistance κ Ψ J) atTop (𝓝 0) := by
  have hh := (tendsto_oldModelDistance_zero hκ hSlope hC hreg hJ).add
    ((CoreRoughModelLimit.tendsto_modelMassL1_zero hκ).comp hSlope.tendsto_zPsi_atTop)
  simp only [add_zero] at hh
  refine squeeze_zero' (Eventually.of_forall fun X => Finset.sum_nonneg fun U _ => abs_nonneg _)
    (Eventually.of_forall fun X => ?_) hh
  unfold modelDistance oldModelDistance CoreRoughModelLimit.modelMassL1
  simp only [Function.comp_apply, ← sum_add_distrib]
  exact Finset.sum_le_sum fun U _ => by
    simpa only [abs_sub_comm] using abs_sub_le
      (model κ Ψ J X U) (actualRootLaw (zPsi Ψ X) (roughProfileS κ (zPsi Ψ X)) U)
      (finiteRootMix (roughSyntheticScale (zPsi Ψ X)) (roughProfileS κ (zPsi Ψ X)) U)

theorem tendsto_model_failure_zero {Ψ dΨ : ℝ → ℝ} {A C κ : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    Tendsto (fun X : ℕ => Stopped.failureMass
      (offsetWindow (roughProfileS κ (zPsi Ψ X))) (model κ Ψ J X)
      (roughProfileL κ (zPsi Ψ X))) atTop (𝓝 0) := by
  have hh := ((CoreRoughModelCosts.tendsto_actual_failureMass_zero hκ).comp
    hSlope.tendsto_zPsi_atTop).add (tendsto_oldModelDistance_zero hκ hSlope hC hreg hJ)
  simp only [add_zero] at hh
  refine squeeze_zero' (Eventually.of_forall fun X => ?_)
    (Eventually.of_forall fun X => ?_) hh
  · unfold Stopped.failureMass
    exact Finset.sum_nonneg fun U _ => model_nonneg _ _ _ _ _
  · have hb := CoreRoughModelCosts.failureMass_abs_sub_le
      (offsetWindow (roughProfileS κ (zPsi Ψ X)))
      (actualRootLaw (zPsi Ψ X) (roughProfileS κ (zPsi Ψ X))) (model κ Ψ J X)
      (roughProfileL κ (zPsi Ψ X))
    have hdiff := (neg_le_abs _).trans hb
    change _ ≤ oldModelDistance κ Ψ J X at hdiff
    dsimp only [Function.comp_apply]
    linarith

end
end PrimeGapNormality.Prime.CoreRoughStoppedTransfer
