import PrimeGapNormality.Prime.CoreCalibratedFrameLimit
import PrimeGapNormality.Prime.CoreJointFrameLimit
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Genuine joint probabilities for arbitrary calibrated cutoff mixtures

The finite PMF uses the completed actual auxiliary masses. The cutoff,
presieve and retained original survivor count are not replaced by an
independent model. A harmless point mass defines the law at invalid initial
indices only; qualitative calibration proves that this branch is eventually
never used. The joint limit is selected before every test and cutoff.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedFrameProbability

open MeasureTheory Filter Finset
open CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
  CoreCalibratedAuxiliaryFrame CoreCalibratedFrameLimit CoreRoughSyntheticScale
open scoped Classical Topology ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev Circle := AddCircle (1 : ℝ)
abbrev Joint (r : ℕ) := CoreJointFrameLimit.Joint r

/-- A finite probability certificate, derived eventually from calibration. -/
def Weights (w : ℕ → ℝ) (S : ℕ) : Prop :=
  (∀ y, 0 ≤ w y) ∧ Valid w S ∧
    ∃ N : ℕ, (∀ y, N ≤ y → w y = 0) ∧ (∑ y ∈ range N, w y) = 1

def completedPMF (w : ℕ → ℝ) (S M : ℕ) (h : Weights w S) :
    PMF ↥((offsetWindow S).powerset) :=
  PMF.ofFintype (fun F => ENNReal.ofReal (completed w S M F)) (by
    rw [Finset.sum_coe_sort ((offsetWindow S).powerset)
      (fun F : Finset ℕ => ENNReal.ofReal (completed w S M F))]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun F _ => completed_nonneg w h.1 S M h.2.1 F)]
    obtain ⟨N, hz, hs⟩ := h.2.2
    rw [completed_total w S M hz hs h.2.1]
    simp)

theorem integral_completedPMF (w : ℕ → ℝ) (S M : ℕ) (h : Weights w S)
    (f : Finset ℕ → ℝ) :
    (∫ F, f F ∂(completedPMF w S M h).toMeasure) =
      ∑ F ∈ (offsetWindow S).powerset, completed w S M F * f F := by
  rw [PMF.integral_eq_sum]
  have hr (F : ↥((offsetWindow S).powerset)) :
      (completedPMF w S M h F).toReal = completed w S M F := by
    change (ENNReal.ofReal (completed w S M F)).toReal = completed w S M F
    exact ENNReal.toReal_ofReal (completed_nonneg w h.1 S M h.2.1 F)
  simp only [hr, smul_eq_mul]
  exact Finset.sum_coe_sort ((offsetWindow S).powerset)
    (fun F : Finset ℕ => completed w S M F * f F)

def jointPoint {r : ℕ} (q : Fin r → ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle) (F : Finset ℕ) : Joint r :=
  (O F, (CoreCalibratedAuxiliaryFrame.frame q G F, θ))

def jointLaw {r : ℕ} (w : ℕ → ℝ) (S M : ℕ) (q : Fin r → ℕ)
    (G θ : ℝ) (O : Finset ℕ → Circle) : ProbabilityMeasure (Joint r) :=
  if h : Weights w S then
    ⟨((completedPMF w S M h).map
      (fun F : ↥((offsetWindow S).powerset) => jointPoint q G θ O F)).toMeasure,
      inferInstance⟩
  else ⟨(PMF.pure (O ∅, ((0 : Fin r → ℝ), θ))).toMeasure, inferInstance⟩

theorem integral_jointLaw {r : ℕ} (w : ℕ → ℝ) (S M : ℕ)
    (h : Weights w S) (q : Fin r → ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle) (f : Joint r → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂(jointLaw w S M q G θ O : Measure (Joint r))) =
      ∑ F ∈ (offsetWindow S).powerset,
        completed w S M F * f (jointPoint q G θ O F) := by
  have hm : Measurable
      (fun F : ↥((offsetWindow S).powerset) => jointPoint q G θ O F) :=
    measurable_of_finite _
  rw [jointLaw, dif_pos h]
  change (∫ z, f z ∂((completedPMF w S M h).map
    (fun F : ↥((offsetWindow S).powerset) => jointPoint q G θ O F)).toMeasure) = _
  rw [← PMF.toMeasure_map
      (fun F : ↥((offsetWindow S).powerset) => jointPoint q G θ O F)
      (completedPMF w S M h) hm,
    integral_map hm.aemeasurable hf.aestronglyMeasurable]
  exact integral_completedPMF w S M h (fun F => f (jointPoint q G θ O F))

theorem integrable_jointLaw {r : ℕ} (w : ℕ → ℝ) (S M : ℕ)
    (h : Weights w S) (q : Fin r → ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle) (f : Joint r → ℝ) (hf : Measurable f) :
    Integrable f (jointLaw w S M q G θ O : Measure (Joint r)) := by
  have hm : Measurable
      (fun F : ↥((offsetWindow S).powerset) => jointPoint q G θ O F) :=
    measurable_of_finite _
  rw [jointLaw, dif_pos h]
  change Integrable f (((completedPMF w S M h).map
    (fun F : ↥((offsetWindow S).powerset) => jointPoint q G θ O F)).toMeasure)
  rw [← PMF.toMeasure_map
    (fun F : ↥((offsetWindow S).powerset) => jointPoint q G θ O F)
    (completedPMF w S M h) hm]
  exact (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).2
    Integrable.of_finite

theorem ae_jointLaw {r : ℕ} (w : ℕ → ℝ) (S M : ℕ)
    (h : Weights w S) (q : Fin r → ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle) (p : Joint r → Prop)
    (hp : MeasurableSet {z | p z})
    (hpoint : ∀ F ∈ (offsetWindow S).powerset, p (jointPoint q G θ O F)) :
    ∀ᵐ z ∂(jointLaw w S M q G θ O : Measure (Joint r)), p z := by
  have hm : Measurable
      (fun F : ↥((offsetWindow S).powerset) => jointPoint q G θ O F) :=
    measurable_of_finite _
  rw [jointLaw, dif_pos h]
  change ∀ᵐ z ∂(((completedPMF w S M h).map
    (fun F : ↥((offsetWindow S).powerset) => jointPoint q G θ O F)).toMeasure), p z
  rw [← PMF.toMeasure_map
    (fun F : ↥((offsetWindow S).powerset) => jointPoint q G θ O F)
    (completedPMF w S M h) hm]
  exact (ae_map_iff hm.aemeasurable hp).2
    (ae_of_all _ fun F => hpoint F F.property)

theorem ae_nonnegative_frame {r : ℕ} (w : ℕ → ℝ) (S M : ℕ)
    (h : Weights w S) (q : Fin r → ℕ) {G : ℝ} (hG : 0 ≤ G)
    (θ : ℝ) (O : Finset ℕ → Circle) :
    ∀ᵐ z ∂(jointLaw w S M q G θ O : Measure (Joint r)),
      ∀ i, 0 ≤ CoreJointFrameLimit.frame z i := by
  apply ae_jointLaw w S M h q G θ O
  · have hc : IsClosed {z : Joint r | ∀ i, 0 ≤ CoreJointFrameLimit.frame z i} := by
      have hi : IsClosed (⋂ i : Fin r,
          {z : Joint r | (0 : ℝ) ≤ CoreJointFrameLimit.frame z i}) :=
        isClosed_iInter fun i : Fin r =>
          isClosed_le (show Continuous (fun _ : Joint r => (0 : ℝ)) from continuous_const)
            ((continuous_apply i).comp CoreJointFrameLimit.continuous_frame)
      simpa only [Set.ofPred_forall] using hi
    exact hc.measurableSet
  · intro F hF i
    exact frame_nonneg q hG F i

theorem ae_scale_range {r : ℕ} (w : ℕ → ℝ) (S M : ℕ)
    (h : Weights w S) (q : Fin r → ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle) {C : ℝ} (hθ : θ ∈ Set.Icc 1 C) :
    ∀ᵐ z ∂(jointLaw w S M q G θ O : Measure (Joint r)),
      CoreJointFrameLimit.scale z ∈ Set.Icc 1 C := by
  apply ae_jointLaw w S M h q G θ O
  · exact (isClosed_Icc.preimage CoreJointFrameLimit.continuous_scale).measurableSet
  · intro F hF
    exact hθ

theorem lintegral_norm_le {r : ℕ} (w : ℕ → ℝ) (S M : ℕ)
    (h : Weights w S) (q : Fin r → ℕ) {G : ℝ} (hG : 0 < G)
    (θ : ℝ) (O : Finset ℕ → Circle) (hq : ∀ i, q i + 1 < M)
    (hcal : ∀ y, w y ≠ 0 → roughGapScale y / G ≤ 2) :
    (∫⁻ z, ENNReal.ofReal ‖CoreJointFrameLimit.frame z‖
      ∂(jointLaw w S M q G θ O : Measure (Joint r))) ≤ ENNReal.ofReal (4 * (r : ℝ)) := by
  have hf : Measurable (fun z : Joint r => ‖CoreJointFrameLimit.frame z‖) := by
    simpa only [Function.comp_def] using
      (continuous_norm.comp CoreJointFrameLimit.continuous_frame).measurable
  rw [← ofReal_integral_eq_lintegral_ofReal
    (f := fun z : Joint r => ‖CoreJointFrameLimit.frame z‖)
    (integrable_jointLaw w S M h q G θ O
      (fun z : Joint r => ‖CoreJointFrameLimit.frame z‖) hf)
    (ae_of_all _ fun z : Joint r => norm_nonneg (CoreJointFrameLimit.frame z)),
    integral_jointLaw w S M h q G θ O
      (fun z : Joint r => ‖CoreJointFrameLimit.frame z‖) hf]
  obtain ⟨N, hz, hs⟩ := h.2.2
  apply ENNReal.ofReal_le_ofReal
  change (∑ F ∈ (offsetWindow S).powerset,
    completed w S M F * ‖CoreCalibratedAuxiliaryFrame.frame q G F‖) ≤ 4 * (r : ℝ)
  exact (completed_norm_mean_le q w h.1 S M hz hs h.2.1 hq hG hcal).trans_eq (by ring)

theorem lintegral_coordinate_le {r : ℕ} (w : ℕ → ℝ) (S M : ℕ)
    (h : Weights w S) (q : Fin r → ℕ) {G : ℝ} (hG : 0 < G)
    (θ : ℝ) (O : Finset ℕ → Circle) (hq : ∀ i, q i + 1 < M)
    (hcal : ∀ y, w y ≠ 0 → roughGapScale y / G ≤ 2) (i : Fin r) :
    (∫⁻ z, ENNReal.ofReal (CoreJointFrameLimit.frame z i)
      ∂(jointLaw w S M q G θ O : Measure (Joint r))) ≤ ENNReal.ofReal 4 := by
  have hf : Measurable (fun z : Joint r => CoreJointFrameLimit.frame z i) := by
    simpa only [Function.comp_def] using
      ((continuous_apply i).comp CoreJointFrameLimit.continuous_frame).measurable
  rw [← ofReal_integral_eq_lintegral_ofReal
    (f := fun z : Joint r => CoreJointFrameLimit.frame z i)
    (integrable_jointLaw w S M h q G θ O
      (fun z : Joint r => CoreJointFrameLimit.frame z i) hf)
    ((ae_nonnegative_frame w S M h q hG.le θ O).mono fun z hz => hz i),
    integral_jointLaw w S M h q G θ O
      (fun z : Joint r => CoreJointFrameLimit.frame z i) hf]
  change ENNReal.ofReal (∑ F ∈ (offsetWindow S).powerset,
    completed w S M F * CoreCalibratedAuxiliaryFrame.frame q G F i) ≤ _
  rw [completed_expectation]
  simp only [frame_empty, Pi.zero_apply, mul_zero, add_zero]
  obtain ⟨N, hz, hs⟩ := h.2.2
  exact ENNReal.ofReal_le_ofReal (by
    simpa only [CoreCalibratedAuxiliaryFrame.frame,
      show (2 : ℝ) * 2 = 4 by norm_num] using
      coordinate_mean_le w h.1 S M (q i) hz hs h.2.1 (hq i) hG hcal)

def profileLaw {r : ℕ} (G : ℕ → ℝ) (M : ℕ → ℕ) (w : ℕ → ℕ → ℝ)
    (q : ℕ → Fin r → ℕ) (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → Circle)
    (X : ℕ) : ProbabilityMeasure (Joint r) :=
  jointLaw (w X) (physicalSpan G M X) (M X) (q X) (G X) (θ X) (O X)

theorem eventually_weights {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G) :
    ∀ᶠ X in atTop, Weights (w X) (physicalSpan G M X) := by
  filter_upwards [eventually_profile_data hG hκ hM hw hsum hcal] with X hX
  exact ⟨hw X, hX.2.1, hX.2.2.2⟩

theorem eventually_rectangle {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧ ∀ i, q X i + 1 < M X)
    (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → Circle)
    (a b : Fin r → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᶠ X in atTop,
      (CoreJointFrameLimit.frameMarginal (profileLaw G M w q θ O X) : Measure (Fin r → ℝ))
        (Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))) ≤
      ENNReal.ofReal (rectangleConstant r * ∏ i, (b i - a i)) +
        ENNReal.ofReal (rectangleError G M w X) := by
  filter_upwards [eventually_weights hG hκ hM hw hsum hcal, hq,
    eventually_completed_rectangle_bound hG hκ hM hw hsum hcal r a b hab] with X hW hqX hrect
  rw [CoreActualFrameRectangleLimit.frame_rectangle_mass_eq_integral]
  have hf : Measurable (fun z : Joint r =>
      if ∀ i, CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i) then (1 : ℝ) else 0) := by
    have hs : MeasurableSet {z : Joint r |
        ∀ i, CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i)} := by
      have hi : MeasurableSet (⋂ i : Fin r,
          {z : Joint r | CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i)}) :=
        MeasurableSet.iInter fun i => measurableSet_Ioo.preimage
          ((continuous_apply i).comp CoreJointFrameLimit.continuous_frame).measurable
      simpa only [Set.ofPred_forall] using hi
    exact Measurable.ite hs measurable_const measurable_const
  rw [profileLaw, integral_jointLaw _ _ _ hW _ _ _ _ _ hf]
  have he : (∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
      completed (w X) (physicalSpan G M X) (M X) F *
        (if ∀ i, CoreJointFrameLimit.frame (jointPoint (q X) (G X) (θ X) (O X) F) i ∈
          Set.Ioo (a i) (b i) then (1 : ℝ) else 0)) =
      ∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
        completed (w X) (physicalSpan G M X) (M X) F * rectangleTest (q X) (G X) a b F := by
    apply Finset.sum_congr rfl
    intro F hF
    unfold rectangleTest jointPoint CoreJointFrameLimit.frame
    congr 1
  rw [he]
  exact (ENNReal.ofReal_le_ofReal (hrect (q X) hqX.1 hqX.2)).trans ENNReal.ofReal_add_le

/-- The actual calibrated joint extraction. Only the physical profile,
qualitative calibration and deterministic valid ranks/compact scale enter.
No tightness, rectangle, moment or reference hypothesis is supplied. -/
theorem exists_joint_limit {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧ ∀ i, q X i + 1 < M X)
    (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → Circle) {C : ℝ}
    (hθ : ∀ᶠ X in atTop, θ X ∈ Set.Icc 1 C) (i : Fin r) :
    ∃ ν : ProbabilityMeasure (Joint r), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun n => profileLaw G M w q θ O (φ n)) atTop (𝓝 ν) ∧
      (CoreJointFrameLimit.frameMarginal ν : Measure (Fin r → ℝ)) ≪ volume ∧
      (∀ᵐ z ∂(ν : Measure (Joint r)), ∀ a, 0 ≤ CoreJointFrameLimit.frame z a) ∧
      (∀ᵐ z ∂(ν : Measure (Joint r)), CoreJointFrameLimit.scale z ∈ Set.Icc 1 C) ∧
      Integrable (fun z => CoreJointFrameLimit.frame z i) (ν : Measure (Joint r)) ∧
      (∫ z, CoreJointFrameLimit.frame z i ∂(ν : Measure (Joint r))) ≤ 4 := by
  have hall := (eventually_profile_data hG hκ hM hw hsum hcal).and (hq.and hθ)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hall
  let μ : ℕ → ProbabilityMeasure (Joint r) :=
    fun n => profileLaw G M w q θ O (n + n₀)
  have hdata (n : ℕ) := hn₀ (n + n₀) (Nat.le_add_left _ _)
  have hW (n : ℕ) : Weights (w (n + n₀)) (physicalSpan G M (n + n₀)) :=
    ⟨hw _, (hdata n).1.2.1, (hdata n).1.2.2.2⟩
  have hshift : Tendsto (fun n : ℕ => n + n₀) atTop atTop :=
    tendsto_atTop.2 fun b => eventually_atTop.2 ⟨b, fun n hn => hn.trans (Nat.le_add_right _ _)⟩
  have herror : Tendsto (fun n => rectangleError G M w (n + n₀)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_rectangleError_zero hG hκ hM hw hsum hcal).comp hshift
  obtain ⟨ν, χ, hχ, hweak, hνac, hν0, hνθ, hint, hmean⟩ :=
    CoreJointFrameLimit.exists_joint_limit μ
      (M := 4 * (r : ℝ)) (C := C) (K := rectangleConstant r) (H := 4)
      (by positivity) (rectangleConstant_pos r) (by norm_num)
      (fun n => lintegral_norm_le _ _ _ (hW n) _ (hdata n).1.1 _ _
        (hdata n).2.1.2 (hdata n).1.2.2.1)
      (fun n => ae_nonnegative_frame _ _ _ (hW n) _ (hdata n).1.1.le _ _)
      (fun n => ae_scale_range _ _ _ (hW n) _ _ _ _ (hdata n).2.2)
      (fun n => rectangleError G M w (n + n₀))
      herror
      (fun a b hab => hshift.eventually
        (eventually_rectangle hG hκ hM hw hsum hcal q hq θ O a b hab)) i
      (fun n => lintegral_coordinate_le _ _ _ (hW n) _ (hdata n).1.1 _ _
        (hdata n).2.1.2 (hdata n).1.2.2.1 i)
  refine ⟨ν, (fun n => χ n + n₀), (fun a b hab => Nat.add_lt_add_right (hχ hab) n₀),
    ?_, hνac, hν0, hνθ, hint, hmean⟩
  change Tendsto (fun n => profileLaw G M w q θ O (χ n + n₀)) atTop (𝓝 ν) at hweak
  exact hweak

end
end PrimeGapNormality.Prime.CoreCalibratedFrameProbability
