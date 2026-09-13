import PrimeGapNormality.Prime.CoreRoughAdverseLimit
import PrimeGapNormality.Prime.CoreRoughPhysicalTestTransfer
import Mathlib.Analysis.Complex.Basic

/-!
# Full short-shape comparison for the actual rough law

Uniform bounded configuration tests recover finite L1 by their sign
optimizer. Projection to first-L shapes contracts that L1. The actual
sliced stopped comparison, model L1 bridge and one-time physical remainder
then give shapeL1 + actual failure -> 0, not just positive domination.
The profile and gap scale here remain the exact synthetic ones.
-/

namespace PrimeGapNormality.Prime.CoreRoughFullShapeComparison

open Finset Filter
open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSyntheticScale
  CoreRoughProfileError CoreRoughCellAsymptotics CoreRoughPhysicalSlices
  CoreRoughStoppedTransfer CoreRoughShapeConclusion CoreSequencePatternLaw
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1000000

def signTest (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem abs_signTest (x : ℝ) : |signTest x| = 1 := by
  unfold signTest
  split_ifs <;> norm_num

theorem mul_signTest (x : ℝ) : x * signTest x = |x| := by
  unfold signTest
  split_ifs with hx
  · simp only [mul_one, abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    ring

def massL1 (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) : ℝ :=
  ∑ U ∈ Ω.powerset, |μ U - ν U|

theorem massL1_nonneg (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) : 0 ≤ massL1 Ω μ ν :=
  Finset.sum_nonneg fun U _ => abs_nonneg _

theorem massL1_eq_sign_test (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) :
    massL1 Ω μ ν =
      (∑ U ∈ Ω.powerset, μ U * signTest (μ U - ν U)) -
        (∑ U ∈ Ω.powerset, ν U * signTest (μ U - ν U)) := by
  unfold massL1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro U hU
  rw [← sub_mul, mul_signTest]

theorem shapeL1_nonneg (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) (L : ℕ) :
    0 ≤ Stopped.shapeL1 Ω μ ν L := Finset.sum_nonneg fun K _ => abs_nonneg _

theorem shapeL1_triangle (Ω : Finset ℕ) (μ ν ξ : Finset ℕ → ℝ) (L : ℕ) :
    Stopped.shapeL1 Ω μ ξ L ≤ Stopped.shapeL1 Ω μ ν L + Stopped.shapeL1 Ω ν ξ L := by
  unfold Stopped.shapeL1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun K _ => abs_sub_le _ _ _

/-- First-L projection contracts full configuration L1, including the
zero-on-failure convention. No probability/mass-equality premise is needed. -/
theorem shapeL1_le_massL1 (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) (L : ℕ) :
    Stopped.shapeL1 Ω μ ν L ≤ massL1 Ω μ ν := by
  let f := fun K => signTest (Stopped.shortShapeMass Ω μ L K - Stopped.shortShapeMass Ω ν L K)
  have hf : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), |f K| ≤ 1 :=
    fun K _ => (abs_signTest _).le
  have hh := CoreRoughMixtureComparison.bounded_test_abs_sub_le_massL1 Ω μ ν
    (configurationTest 0 L f) (by norm_num : (0 : ℝ) ≤ 1)
    (configurationTest_abs_le Ω L f (by norm_num) hf)
  rw [configurationTest_zero_eval, configurationTest_zero_eval, one_mul] at hh
  have hid : shortMean Ω μ L f - shortMean Ω ν L f = Stopped.shapeL1 Ω μ ν L := by
    unfold shortMean Stopped.shapeL1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro K hK
    rw [← mul_sub, mul_comm]
    exact mul_signTest _
  rw [hid, abs_of_nonneg (shapeL1_nonneg Ω μ ν L)] at hh
  exact hh

def actualLaw (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) : Finset ℕ → ℝ :=
  patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow (roughProfileS κ (zPsi Ψ X)))

def syntheticLaw (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) : Finset ℕ → ℝ :=
  finiteRootMix (roughSyntheticScale (zPsi Ψ X)) (roughProfileS κ (zPsi Ψ X))

def physicalDistance (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) : ℝ :=
  massL1 (offsetWindow (roughProfileS κ (zPsi Ψ X)))
    (actualLaw κ Ψ X) (empirical κ Ψ J X)

theorem tendsto_physicalDistance_zero {Ψ dΨ : ℝ → ℝ} {A C κ : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    Tendsto (physicalDistance κ Ψ J) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun X => ha.trans_le (massL1_nonneg _ _ _)
  · intro ε hε
    filter_upwards [CoreRoughPhysicalTestTransfer.eventually_bounded_test_error
      hSlope hC hreg hJ (fun X => roughProfileS κ (zPsi Ψ X)) hε] with X hX
    let Ω := offsetWindow (roughProfileS κ (zPsi Ψ X))
    let μ := actualLaw κ Ψ X
    let ν := empirical κ Ψ J X
    have hh := hX (fun U => signTest (μ U - ν U))
      (fun U _ => (abs_signTest _).le)
    change |(∑ U ∈ Ω.powerset, μ U * signTest (μ U - ν U)) -
      (∑ U ∈ Ω.powerset, ν U * signTest (μ U - ν U))| < ε at hh
    rw [← massL1_eq_sign_test, abs_of_nonneg (massL1_nonneg Ω μ ν)] at hh
    exact hh

def fullShapeError (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  Stopped.shapeL1 (offsetWindow (roughProfileS κ (zPsi Ψ X)))
    (actualLaw κ Ψ X) (syntheticLaw κ Ψ X) (roughProfileL κ (zPsi Ψ X)) +
  Stopped.failureMass (offsetWindow (roughProfileS κ (zPsi Ψ X)))
    (actualLaw κ Ψ X) (roughProfileL κ (zPsi Ψ X))

theorem fullShapeError_nonneg (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) :
    0 ≤ fullShapeError κ Ψ X := by
  unfold fullShapeError
  apply add_nonneg (shapeL1_nonneg _ _ _ _)
  unfold Stopped.failureMass
  exact Finset.sum_nonneg fun U _ => patternMass_nonneg _ _ _ _

theorem fullShapeError_le (κ : ℝ) (Ψ : ℝ → ℝ) (J X : ℕ) :
    fullShapeError κ Ψ X ≤
      2 * physicalDistance κ Ψ J X + stoppedError κ Ψ J X + modelDistance κ Ψ J X := by
  let Ω := offsetWindow (roughProfileS κ (zPsi Ψ X))
  let L := roughProfileL κ (zPsi Ψ X)
  have h1 := shapeL1_triangle Ω (actualLaw κ Ψ X) (empirical κ Ψ J X) (syntheticLaw κ Ψ X) L
  have h2 := shapeL1_triangle Ω (empirical κ Ψ J X) (model κ Ψ J X) (syntheticLaw κ Ψ X) L
  have h3 := shapeL1_le_massL1 Ω (actualLaw κ Ψ X) (empirical κ Ψ J X) L
  have h4 := shapeL1_le_massL1 Ω (model κ Ψ J X) (syntheticLaw κ Ψ X) L
  have h5 := CoreRoughModelCosts.failureMass_abs_sub_le Ω
    (actualLaw κ Ψ X) (empirical κ Ψ J X) L
  have hf := (le_abs_self _).trans h5
  change _ ≤ physicalDistance κ Ψ J X at h3 hf
  change _ ≤ modelDistance κ Ψ J X at h4
  unfold fullShapeError stoppedError
  change Stopped.shapeL1 Ω (actualLaw κ Ψ X) (syntheticLaw κ Ψ X) L +
    Stopped.failureMass Ω (actualLaw κ Ψ X) L ≤
      2 * physicalDistance κ Ψ J X +
        (Stopped.shapeL1 Ω (empirical κ Ψ J X) (model κ Ψ J X) L +
          Stopped.failureMass Ω (empirical κ Ψ J X) L) + modelDistance κ Ψ J X
  linarith

/-- Full actual short-shape L1 plus actual span failure tends to zero.
Only the literal rough slope/regularity data remain. The exact window is
the canonical small profile at the synthetic model scale. -/
theorem tendsto_fullShapeError_zero {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fullShapeError κ Ψ) atTop (𝓝 0) := by
  let J := CoreRoughRelativeHazardBudget.slicingExponent κ
  have hJ := CoreRoughRelativeHazardBudget.slicingExponent_large κ
  have hp := tendsto_physicalDistance_zero (κ := κ) hSlope hC hreg (J := J) hJ.1
  have hs := tendsto_stoppedError_zero hκ hSlope hC hreg (J := J) hJ.1
    (CoreRoughAdverseLimit.tendsto_adverse_zero hκ hSlope hC hreg hJ.1 hJ.2)
  have hm := tendsto_modelDistance_zero hκ hSlope hC hreg (J := J) hJ.1
  have hlim : Tendsto (fun X : ℕ ↦
      2 * physicalDistance κ Ψ J X + stoppedError κ Ψ J X +
        modelDistance κ Ψ J X) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using ((hp.const_mul 2).add hs).add hm
  exact squeeze_zero' (Eventually.of_forall fun X => fullShapeError_nonneg κ Ψ X)
    (Eventually.of_forall fun X => fullShapeError_le κ Ψ J X) hlim

theorem complex_short_test_le_shapeL1 (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ)
    (L : ℕ) (f : Finset ℕ → ℂ)
    (hf : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), ‖f K‖ ≤ 1) :
    ‖(∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * (Stopped.shortShapeMass Ω μ L K : ℂ)) -
      (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * (Stopped.shortShapeMass Ω ν L K : ℂ))‖ ≤ Stopped.shapeL1 Ω μ ν L := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro K hK
  rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hf K hK) (abs_nonneg _)).trans_eq (one_mul _)

/-- Uniform complex short-shape tests, chosen after X, have vanishing
actual/model discrepancy. This follows from full L1 without a cardinality
factor (indeed the multiplier is one, not two). -/
theorem eventually_complex_short_test_error {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ f : Finset ℕ → ℂ,
      (∀ K ∈ (offsetWindow (roughProfileS κ (zPsi Ψ X))).powerset.filter
        (fun K => K.card = roughProfileL κ (zPsi Ψ X)), ‖f K‖ ≤ 1) →
      ‖(∑ K ∈ (offsetWindow (roughProfileS κ (zPsi Ψ X))).powerset.filter
          (fun K => K.card = roughProfileL κ (zPsi Ψ X)),
          f K * (Stopped.shortShapeMass (offsetWindow (roughProfileS κ (zPsi Ψ X)))
            (actualLaw κ Ψ X) (roughProfileL κ (zPsi Ψ X)) K : ℂ)) -
        (∑ K ∈ (offsetWindow (roughProfileS κ (zPsi Ψ X))).powerset.filter
          (fun K => K.card = roughProfileL κ (zPsi Ψ X)),
          f K * (Stopped.shortShapeMass (offsetWindow (roughProfileS κ (zPsi Ψ X)))
            (syntheticLaw κ Ψ X) (roughProfileL κ (zPsi Ψ X)) K : ℂ))‖ < ε := by
  filter_upwards [(tendsto_order.mp (tendsto_fullShapeError_zero hκ hSlope hC hreg)).2 ε hε]
    with X hX
  intro f hf
  have hh := complex_short_test_le_shapeL1
    (offsetWindow (roughProfileS κ (zPsi Ψ X))) (actualLaw κ Ψ X) (syntheticLaw κ Ψ X)
    (roughProfileL κ (zPsi Ψ X)) f hf
  have hfail : 0 ≤ Stopped.failureMass (offsetWindow (roughProfileS κ (zPsi Ψ X)))
      (actualLaw κ Ψ X) (roughProfileL κ (zPsi Ψ X)) := by
    unfold Stopped.failureMass
    exact Finset.sum_nonneg fun U _ => patternMass_nonneg _ _ _ _
  exact hh.trans_lt (lt_of_le_of_lt (le_add_of_nonneg_right hfail) hX)

end
end PrimeGapNormality.Prime.CoreRoughFullShapeComparison
