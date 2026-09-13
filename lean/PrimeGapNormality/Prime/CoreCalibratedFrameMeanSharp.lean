import PrimeGapNormality.Prime.CoreCalibratedFrameProbability

/-!
# The auxiliary-frame limiting mean is at most two

The coarse extraction uses a fixed bound four for compactness. This does
not lose the paper's sharper limiting mean: for every positive epsilon,
qualitative calibration gives the actual finite bound two plus epsilon.
Nonnegative Portmanteau applies to the SAME already selected weak limit.
No new extraction depending on epsilon, quantitative calibration rate, or
uniform integrability is used. Source pending central compilation.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedFrameMeanSharp

open Finset Filter MeasureTheory
open CoreCalibratedMixtureProfile CoreCalibratedAuxiliaryFrame
open CoreCalibratedMixtureFiniteSupport
open CoreCalibratedFrameProbability CoreRoughSyntheticScale
open scoped Classical Topology
noncomputable section

/-- Finite first-coordinate estimate with the calibration constant still
free; specializing it to two too early only obscures the limiting bound. -/
theorem lintegral_coordinate_le_general {r : ℕ}
    (w : ℕ → ℝ) (S M : ℕ) (h : Weights w S) (q : Fin r → ℕ)
    {G : ℝ} (hG : 0 < G) (θ : ℝ) (O : Finset ℕ → (AddCircle (1 : ℝ)))
    (hq : ∀ i, q i + 1 < M) {C : ℝ}
    (hcal : ∀ y, w y ≠ 0 → roughGapScale y / G ≤ C) (i : Fin r) :
    (∫⁻ z, ENNReal.ofReal (CoreJointFrameLimit.frame z i)
      ∂(jointLaw w S M q G θ O : Measure (Joint r))) ≤
      ENNReal.ofReal (2 * C) := by
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
    simpa only [CoreCalibratedAuxiliaryFrame.frame] using coordinate_mean_le w h.1 S M (q i) hz hs h.2.1 (hq i) hG hcal)

theorem eventually_coordinate_le_two_add
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, ∀ i, q X i + 1 < M X)
    (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, ∀ i : Fin r,
      (∫⁻ z, ENNReal.ofReal (CoreJointFrameLimit.frame z i)
        ∂(profileLaw G M w q θ O X : Measure (Joint r))) ≤
        ENNReal.ofReal (2 + ε) := by
  filter_upwards [eventually_weights hG hκ hM hw hsum hcal,
    hG.eventually_gt_atTop 0, hq, hcal (ε / 2) (half_pos hε)]
    with X hW hg hqX hcalX
  have hc : ∀ y, w X y ≠ 0 → roughGapScale y / G X ≤ 1 + ε / 2 := by
    intro y hy
    have hh := (abs_le.mp (hcalX y (lt_of_le_of_ne (hw X y) (Ne.symm hy)))).2
    linarith
  intro i
  have hh := lintegral_coordinate_le_general (w X) (physicalSpan G M X) (M X)
    hW (q X) hg (θ X) (O X) hqX hc i
  have heq : 2 * (1 + ε / 2) = (2 + ε : ℝ) := by ring
  simpa only [profileLaw, heq] using hh

/-- Portmanteau only needs an eventual bound. No modification of the
finite initial measures and no second subsequence are necessary. -/
theorem coordinate_moment_of_eventual_bound {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) (ν : ProbabilityMeasure (Joint r))
    (hweak : Tendsto μ atTop (𝓝 ν)) (i : Fin r) {H : ℝ}
    (hbound : ∀ᶠ j in atTop,
      (∫⁻ z, ENNReal.ofReal (CoreJointFrameLimit.frame z i)
        ∂(μ j : Measure (Joint r))) ≤ ENNReal.ofReal H) :
    (∫⁻ z, ENNReal.ofReal (CoreJointFrameLimit.frame z i)
      ∂(ν : Measure (Joint r))) ≤ ENNReal.ofReal H := by
  have hf : Continuous (fun z : Joint r => max (CoreJointFrameLimit.frame z i) 0) :=
    (((continuous_apply i).comp CoreJointFrameLimit.continuous_frame).max continuous_const)
  have hp := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (ν : Measure (Joint r))) (μs := fun j => (μ j : Measure (Joint r)))
    hf (fun z => le_max_right _ _)
    (fun _ hs => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hs)
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, _root_.max_zero] at hp
  exact hp.trans ((Filter.liminf_le_liminf hbound).trans_eq
    tendsto_const_nhds.liminf_eq)

/-- The honest Bochner mean at ANY chosen nonnegative weak limit is at
most two. The bound is derived after fixing that limit. -/
theorem coordinate_integral_le_two
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, ∀ i, q X i + 1 < M X)
    (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ)))
    (ν : ProbabilityMeasure (Joint r)) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop)
    (hweak : Tendsto (fun n => profileLaw G M w q θ O (φ n)) atTop (𝓝 ν))
    (i : Fin r)
    (hnonneg : ∀ᵐ z ∂(ν : Measure (Joint r)), 0 ≤ CoreJointFrameLimit.frame z i) :
    Integrable (fun z => CoreJointFrameLimit.frame z i) (ν : Measure (Joint r)) ∧
      (∫ z, CoreJointFrameLimit.frame z i ∂(ν : Measure (Joint r))) ≤ 2 := by
  have hbound (ε : ℝ) (hε : 0 < ε) :
      Integrable (fun z => CoreJointFrameLimit.frame z i) (ν : Measure (Joint r)) ∧
      (∫ z, CoreJointFrameLimit.frame z i ∂(ν : Measure (Joint r))) ≤ 2 + ε := by
    have he := hφ.eventually
      (eventually_coordinate_le_two_add hG hκ hM hw hsum hcal q hq θ O hε)
    have hm := coordinate_moment_of_eventual_bound _ ν hweak i
      (he.mono fun n hn => hn i)
    exact CoreJointFrameLimit.coordinate_integrable_and_integral_le ν i
      (by positivity : (0 : ℝ) ≤ 2 + ε) hnonneg hm
  refine ⟨(hbound 1 (by norm_num)).1, ?_⟩
  by_contra hbad
  have hpos : 0 < (∫ z, CoreJointFrameLimit.frame z i ∂(ν : Measure (Joint r))) - 2 :=
    sub_pos.mpr (lt_of_not_ge hbad)
  have hhalf := (hbound
    (((∫ z, CoreJointFrameLimit.frame z i ∂(ν : Measure (Joint r))) - 2) / 2)
    (half_pos hpos)).2
  linarith

/-- Same actual joint extraction as before, now with the sharp mean two.
This does not yet sharpen the separate rectangle density to 8^r. -/
theorem exists_joint_limit_mean_two
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧ ∀ i, q X i + 1 < M X)
    (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ))) {C : ℝ}
    (hθ : ∀ᶠ X in atTop, θ X ∈ Set.Icc 1 C) (i : Fin r) :
    ∃ ν : ProbabilityMeasure (Joint r), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun n => profileLaw G M w q θ O (φ n)) atTop (𝓝 ν) ∧
      (CoreJointFrameLimit.frameMarginal ν : Measure (Fin r → ℝ)) ≪ volume ∧
      (∀ᵐ z ∂(ν : Measure (Joint r)), ∀ a, 0 ≤ CoreJointFrameLimit.frame z a) ∧
      (∀ᵐ z ∂(ν : Measure (Joint r)), CoreJointFrameLimit.scale z ∈ Set.Icc 1 C) ∧
      Integrable (fun z => CoreJointFrameLimit.frame z i) (ν : Measure (Joint r)) ∧
      (∫ z, CoreJointFrameLimit.frame z i ∂(ν : Measure (Joint r))) ≤ 2 := by
  obtain ⟨ν, φ, hφ, hweak, hac, hnonneg, hscale, _, _⟩ :=
    CoreCalibratedFrameProbability.exists_joint_limit
      hG hκ hM hw hsum hcal q hq θ O hθ i
  have hm := coordinate_integral_le_two hG hκ hM hw hsum hcal q
    (hq.mono fun _ hx => hx.2) θ O ν φ hφ.tendsto_atTop hweak i
    (hnonneg.mono fun _ hz => hz i)
  exact ⟨ν, φ, hφ, hweak, hac, hnonneg, hscale, hm⟩

end
end PrimeGapNormality.Prime.CoreCalibratedFrameMeanSharp
