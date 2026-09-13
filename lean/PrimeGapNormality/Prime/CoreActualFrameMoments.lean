import PrimeGapNormality.Prime.CoreActualFrameJoint
import PrimeGapNormality.Prime.CoreAuxiliaryMixtureMean
import PrimeGapNormality.Prime.CoreLinearMixtureScales

/-! First moments of the actual auxiliary joint law, not a postulated frame
law. Completing missing mass at the empty frame adds zero to these moments.
No independence or uniform integrability is asserted. -/

open MeasureTheory Finset Filter
open scoped Classical ENNReal Topology
namespace PrimeGapNormality.Prime.CoreActualFrameJoint
noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency false in
theorem integrable_jointLaw (X S L w j : ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    (f : CoreJointFrameLimit.Joint (2 * w + 1) → ℝ) (hf : Measurable f) :
    Integrable f (jointLaw X S L w j G θ O hSy hZ : Measure _) := by
  have hm : Measurable
      (fun F : ↥((offsetWindow S).powerset) ↦ jointPoint w j G θ O F) :=
    measurable_of_finite _
  change Integrable f (((coreAuxiliaryFramePMF X S L hSy hZ).map
    (fun F : ↥((offsetWindow S).powerset) ↦ jointPoint w j G θ O F)).toMeasure)
  rw [← PMF.toMeasure_map
    (fun F : ↥((offsetWindow S).powerset) ↦ jointPoint w j G θ O F)
    (coreAuxiliaryFramePMF X S L hSy hZ) hm]
  exact (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).2
    Integrable.of_finite

theorem integral_coordinate (X S L w j : ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    (i : Fin (2 * w + 1)) :
    (∫ z, CoreJointFrameLimit.frame z i
      ∂(jointLaw X S L w j G θ O hSy hZ : Measure _)) =
      ((∑ t ∈ mixScale X, mixWeightV t *
        coreAuxiliaryLayerPhysicalGapMean S (sieveCutoff (t : ℝ)) L
          (CoreCyclic.OnePoint.FiniteExterior.frameRank w j i)) / mixZ X) / G := by
  rw [integral_jointLaw X S L w j G θ O hSy hZ
    (fun z ↦ CoreJointFrameLimit.frame z i)
    ((continuous_apply i).comp CoreJointFrameLimit.continuous_frame).measurable]
  simp only [jointPoint, CoreJointFrameLimit.frame, Pi.zero_apply,
    mul_zero, add_zero, localFrame, ← mul_div_assoc, ← Finset.sum_div]
  rw [coreAuxiliaryFrameMass_subsetGap_expectation]

theorem integral_coordinate_le (X S L w j : ℕ) {G C : ℝ} (θ : ℝ)
    (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    (hG : 0 < G) (hj : w + 1 ≤ j) (hL : j + w < L)
    (hcal : ∀ t ∈ mixScale X, (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / G ≤ C)
    (i : Fin (2 * w + 1)) :
    (∫ z, CoreJointFrameLimit.frame z i
      ∂(jointLaw X S L w j G θ O hSy hZ : Measure _)) ≤ 2 * C := by
  rw [integral_coordinate]
  have hidx := CoreCyclic.OnePoint.FiniteExterior.frameRank_valid hj hL i
  have hsum :
      (∑ t ∈ mixScale X, mixWeightV t *
        coreAuxiliaryLayerPhysicalGapMean S (sieveCutoff (t : ℝ)) L
          (CoreCyclic.OnePoint.FiniteExterior.frameRank w j i)) / G ≤
      mixZ X * (2 * C) := by
    rw [Finset.sum_div]
    calc
      _ ≤ ∑ t ∈ mixScale X, mixWeightV t * (2 * C) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (mixWeightV_nonneg t)
        calc
          _ ≤ (2 * (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹) / G :=
            div_le_div_of_nonneg_right
              (coreAuxiliaryLayerPhysicalGapMean_le S _ L _ (hSy t ht) hidx) hG.le
          _ = 2 * ((eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / G) := by ring
          _ ≤ 2 * C := mul_le_mul_of_nonneg_left (hcal t ht) (by norm_num)
      _ = mixZ X * (2 * C) := by rw [← Finset.sum_mul]; rfl
  rw [div_right_comm]
  exact (div_le_iff₀ hZ).2 (by simpa only [mul_comm] using hsum)

theorem norm_localFrame_le_sum (w j : ℕ) {G : ℝ} (hG : 0 ≤ G) (F : Finset ℕ) :
    ‖localFrame w j G F‖ ≤ ∑ i, localFrame w j G F i := by
  apply (pi_norm_le_iff_of_nonneg
    (sum_nonneg fun i _ ↦ localFrame_nonneg w j hG F i)).2
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (localFrame_nonneg w j hG F i)]
  exact single_le_sum (fun i _ ↦ localFrame_nonneg w j hG F i) (mem_univ i)

theorem integral_frame_norm_le (X S L w j : ℕ) {G C : ℝ} (θ : ℝ)
    (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    (hG : 0 < G) (hj : w + 1 ≤ j) (hL : j + w < L)
    (hcal : ∀ t ∈ mixScale X, (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / G ≤ C) :
    (∫ z, ‖CoreJointFrameLimit.frame z‖
      ∂(jointLaw X S L w j G θ O hSy hZ : Measure (CoreJointFrameLimit.Joint (2 * w + 1)))) ≤
      (2 * w + 1 : ℕ) * (2 * C) := by
  have hcompare :
      (∫ z, ‖CoreJointFrameLimit.frame z‖
        ∂(jointLaw X S L w j G θ O hSy hZ : Measure (CoreJointFrameLimit.Joint (2 * w + 1)))) ≤
      ∫ z, ∑ i, CoreJointFrameLimit.frame z i
        ∂(jointLaw X S L w j G θ O hSy hZ : Measure (CoreJointFrameLimit.Joint (2 * w + 1))) := by
    rw [integral_jointLaw X S L w j G θ O hSy hZ (fun z ↦ ‖CoreJointFrameLimit.frame z‖)
      (continuous_norm.comp CoreJointFrameLimit.continuous_frame).measurable,
      integral_jointLaw X S L w j G θ O hSy hZ (fun z ↦ ∑ i, CoreJointFrameLimit.frame z i)
      (Finset.measurable_sum _ (fun i _ ↦
        ((continuous_apply i).comp CoreJointFrameLimit.continuous_frame).measurable))]
    simp only [jointPoint, CoreJointFrameLimit.frame, localFrame_empty, norm_zero,
      Pi.zero_apply, sum_const_zero, mul_zero, add_zero]
    apply sum_le_sum
    intro F hF
    exact mul_le_mul_of_nonneg_left (norm_localFrame_le_sum w j hG.le F)
      (coreAuxiliaryFrameMass_nonneg X S L hSy hZ F)
  have hint (i : Fin (2 * w + 1)) :
      Integrable (fun z ↦ CoreJointFrameLimit.frame z i)
        (jointLaw X S L w j G θ O hSy hZ : Measure _) :=
    integrable_jointLaw X S L w j G θ O hSy hZ _
      ((continuous_apply i).comp CoreJointFrameLimit.continuous_frame).measurable
  calc
    _ ≤ ∫ z, ∑ i, CoreJointFrameLimit.frame z i
        ∂(jointLaw X S L w j G θ O hSy hZ : Measure (CoreJointFrameLimit.Joint (2 * w + 1))) := hcompare
    _ = ∑ i, ∫ z, CoreJointFrameLimit.frame z i
        ∂(jointLaw X S L w j G θ O hSy hZ : Measure (CoreJointFrameLimit.Joint (2 * w + 1))) := by
      simpa using integral_finsetSum univ (fun i _ ↦ hint i)
    _ ≤ ∑ _i : Fin (2 * w + 1), (2 * C) := sum_le_sum fun i _ ↦
      integral_coordinate_le X S L w j θ O hSy hZ hG hj hL hcal i
    _ = (2 * w + 1 : ℕ) * (2 * C) := by simp

theorem lintegral_frame_norm_le (X S L w j : ℕ) {G C : ℝ} (θ : ℝ)
    (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    (hG : 0 < G) (hj : w + 1 ≤ j) (hL : j + w < L)
    (hcal : ∀ t ∈ mixScale X, (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / G ≤ C) :
    (∫⁻ z, ENNReal.ofReal ‖CoreJointFrameLimit.frame z‖
      ∂(jointLaw X S L w j G θ O hSy hZ : Measure (CoreJointFrameLimit.Joint (2 * w + 1)))) ≤
      ENNReal.ofReal ((2 * w + 1 : ℕ) * (2 * C)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_jointLaw X S L w j G θ O hSy hZ (fun z ↦ ‖CoreJointFrameLimit.frame z‖)
      (continuous_norm.comp CoreJointFrameLimit.continuous_frame).measurable)
    (ae_of_all _ fun z ↦ norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal
    (integral_frame_norm_le X S L w j θ O hSy hZ hG hj hL hcal)

end
end PrimeGapNormality.Prime.CoreActualFrameJoint
