import PrimeGapNormality.Prime.CoreActualFrameMoments

/-! Support and tightness for the actual auxiliary frame measures. The
scale restriction is supplied by the proved critical-rank selection. -/

open MeasureTheory Finset Filter Set
open scoped Classical ENNReal Topology
namespace PrimeGapNormality.Prime.CoreActualFrameJoint
noncomputable section

set_option backward.isDefEq.respectTransparency false in
theorem ae_jointLaw (X S L w j : ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    (p : CoreJointFrameLimit.Joint (2 * w + 1) → Prop)
    (hp : MeasurableSet {z | p z})
    (hpoint : ∀ F ∈ (offsetWindow S).powerset, p (jointPoint w j G θ O F)) :
    ∀ᵐ z ∂(jointLaw X S L w j G θ O hSy hZ : Measure (CoreJointFrameLimit.Joint (2 * w + 1))), p z := by
  have hm : Measurable
      (fun F : ↥((offsetWindow S).powerset) ↦ jointPoint w j G θ O F) :=
    measurable_of_finite _
  change ∀ᵐ z ∂(((coreAuxiliaryFramePMF X S L hSy hZ).map
    (fun F : ↥((offsetWindow S).powerset) ↦ jointPoint w j G θ O F)).toMeasure), p z
  rw [← PMF.toMeasure_map
    (fun F : ↥((offsetWindow S).powerset) ↦ jointPoint w j G θ O F)
    (coreAuxiliaryFramePMF X S L hSy hZ) hm]
  exact (ae_map_iff hm.aemeasurable hp).2
    (ae_of_all _ fun F ↦ hpoint F F.property)

theorem ae_nonnegative_frame (X S L w j : ℕ) {G : ℝ} (hG : 0 ≤ G)
    (θ : ℝ) (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X) :
    ∀ᵐ z ∂(jointLaw X S L w j G θ O hSy hZ : Measure (CoreJointFrameLimit.Joint (2 * w + 1))),
      ∀ i, 0 ≤ CoreJointFrameLimit.frame z i := by
  apply ae_jointLaw X S L w j G θ O hSy hZ
  · have hclosed : IsClosed {z : CoreJointFrameLimit.Joint (2 * w + 1) |
        ∀ i, 0 ≤ CoreJointFrameLimit.frame z i} := by
      have h : IsClosed (⋂ i : Fin (2 * w + 1),
          {z : CoreJointFrameLimit.Joint (2 * w + 1) |
            0 ≤ CoreJointFrameLimit.frame z i}) :=
        isClosed_iInter fun i ↦ isClosed_le continuous_const
          ((continuous_apply i).comp CoreJointFrameLimit.continuous_frame)
      convert h using 1
      ext z
      simp only [mem_iInter, mem_setOf_eq]
    exact hclosed.measurableSet
  · intro F _ i
    exact localFrame_nonneg w j hG F i

theorem ae_scale_range (X S L w j : ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    {C : ℝ} (hθ : θ ∈ Set.Icc 1 C) :
    ∀ᵐ z ∂(jointLaw X S L w j G θ O hSy hZ : Measure (CoreJointFrameLimit.Joint (2 * w + 1))),
      CoreJointFrameLimit.scale z ∈ Set.Icc 1 C := by
  apply ae_jointLaw X S L w j G θ O hSy hZ
  · exact (isClosed_Icc.preimage CoreJointFrameLimit.continuous_scale).measurableSet
  · intro F _
    exact hθ

/-- The coordinate moment bound is uniform in the chosen valid slot and
in the entire outer phase. The actual cutoff supplies the fixed number 8. -/
theorem eventually_actual_frame_moments {κ : ℝ} (hκ : 0 < κ) (w : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ j θ (O : Finset ℕ → Circle)
      (hSy : ∀ t ∈ mixScale X, ahlSmall_window κ X ≤ sieveCutoff (t : ℝ))
      (hZ : 0 < mixZ X),
      w + 1 ≤ j → j + w < profileL κ X →
      (∫⁻ z, ENNReal.ofReal ‖CoreJointFrameLimit.frame z‖
        ∂(jointLaw X (ahlSmall_window κ X) (profileL κ X) w j
          (windowG X) θ O hSy hZ : Measure (CoreJointFrameLimit.Joint (2 * w + 1)))) ≤
        ENNReal.ofReal ((2 * w + 1 : ℕ) * (8 : ℝ)) := by
  filter_upwards [eventually_coreLinearMixtureScales hκ] with X hscale
  intro j θ O hSy hZ hj hL
  simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using lintegral_frame_norm_le X (ahlSmall_window κ X) (profileL κ X)
    w j θ O hSy hZ (zero_lt_one.trans hscale.1) hj hL
    (fun t ht ↦ (hscale.2.2.2.2 t ht).2.2.2.2)

/-- An actual joint subsequence, without assuming that the frame and
outer phase are independent. Uniform finite calibration is an explicit
intermediate contract; `eventually_actual_frame_moments` supplies it at
the physical profile. -/
theorem exists_actual_joint_subsequence
    (X S L j : ℕ → ℕ) (w : ℕ) (G θ : ℕ → ℝ)
    (O : ℕ → Finset ℕ → Circle)
    (hSy : ∀ n, ∀ t ∈ mixScale (X n), S n ≤ sieveCutoff (t : ℝ))
    (hZ : ∀ n, 0 < mixZ (X n))
    (hG : ∀ n, 0 < G n) (hj : ∀ n, w + 1 ≤ j n)
    (hL : ∀ n, j n + w < L n)
    (hcal : ∀ n, ∀ t ∈ mixScale (X n),
      (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / G n ≤ 4)
    {C : ℝ} (hθ : ∀ n, θ n ∈ Set.Icc 1 C) :
    ∃ ν : ProbabilityMeasure (CoreJointFrameLimit.Joint (2 * w + 1)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n ↦ jointLaw (X (φ n)) (S (φ n)) (L (φ n)) w (j (φ n))
          (G (φ n)) (θ (φ n)) (O (φ n)) (hSy (φ n)) (hZ (φ n))) atTop (𝓝 ν) := by
  let μ := fun n ↦ jointLaw (X n) (S n) (L n) w (j n) (G n) (θ n) (O n)
    (hSy n) (hZ n)
  apply CoreJointFrameLimit.exists_joint_subsequence μ
    (M := (2 * w + 1 : ℕ) * (8 : ℝ)) (C := C) (by positivity)
  · intro n
    simpa only [μ, show (2 : ℝ) * 4 = 8 by norm_num] using
      lintegral_frame_norm_le (X n) (S n) (L n) w (j n) (θ n) (O n)
        (hSy n) (hZ n) (hG n) (hj n) (hL n) (hcal n)
  · intro n
    exact ae_scale_range (X n) (S n) (L n) w (j n) (G n) (θ n) (O n)
      (hSy n) (hZ n) (hθ n)

end
end PrimeGapNormality.Prime.CoreActualFrameJoint
