import PrimeGapNormality.Prime.CoreActualFrameTightness
import PrimeGapNormality.Prime.CoreActualFrameRectangleLimit

/-! The fixed joint limit of the actual auxiliary sieve law. All rectangle
and first-moment inputs are discharged by the concrete preceding modules.
Finite profile-validity assumptions can be arranged by deleting a finite
initial segment; they are not additional arithmetic limit hypotheses. -/

namespace PrimeGapNormality.Prime.CoreActualFrameJoint
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem lintegral_coordinate_le (X S L w j : ℕ) {G C : ℝ} (θ : ℝ)
    (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    (hG : 0 < G) (hj : w + 1 ≤ j) (hL : j + w < L)
    (hcal : ∀ t ∈ mixScale X, (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / G ≤ C)
    (i : Fin (2 * w + 1)) :
    (∫⁻ z, ENNReal.ofReal (CoreJointFrameLimit.frame z i)
      ∂(jointLaw X S L w j G θ O hSy hZ :
        Measure (CoreJointFrameLimit.Joint (2 * w + 1)))) ≤ ENNReal.ofReal (2 * C) := by
  have hnonneg := ae_nonnegative_frame X S L w j hG.le θ O hSy hZ
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_jointLaw X S L w j G θ O hSy hZ
      (fun z ↦ CoreJointFrameLimit.frame z i)
      ((continuous_apply i).comp CoreJointFrameLimit.continuous_frame).measurable)
    (hnonneg.mono fun z hz ↦ hz i)]
  exact ENNReal.ofReal_le_ofReal
    (integral_coordinate_le X S L w j θ O hSy hZ hG hj hL hcal i)

theorem exists_actual_profile_joint_limit
    {κ : ℝ} (hκ : 0 < κ) (X : ℕ → ℕ) (hX : Tendsto X atTop atTop)
    (w : ℕ) (j : ℕ → ℕ) (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → Circle)
    (hSy : ∀ n, ∀ t ∈ mixScale (X n), ahlSmall_window κ (X n) ≤ sieveCutoff (t : ℝ))
    (hZ : ∀ n, 0 < mixZ (X n)) (hG : ∀ n, 0 < windowG (X n))
    (hj : ∀ n, w + 1 ≤ j n) (hL : ∀ n, j n + w < profileL κ (X n))
    (hcal : ∀ n, ∀ t ∈ mixScale (X n),
      (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / windowG (X n) ≤ 4)
    {C : ℝ} (hθ : ∀ n, θ n ∈ Set.Icc 1 C) (i : Fin (2 * w + 1)) :
    ∃ ν : ProbabilityMeasure (CoreJointFrameLimit.Joint (2 * w + 1)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n ↦ jointLaw (X (φ n)) (ahlSmall_window κ (X (φ n)))
          (profileL κ (X (φ n))) w (j (φ n)) (windowG (X (φ n))) (θ (φ n))
          (O (φ n)) (hSy (φ n)) (hZ (φ n))) atTop (𝓝 ν) ∧
        (CoreJointFrameLimit.frameMarginal ν : Measure (Fin (2 * w + 1) → ℝ)) ≪ volume ∧
        (∀ᵐ z ∂(ν : Measure (CoreJointFrameLimit.Joint (2 * w + 1))),
          ∀ a, 0 ≤ CoreJointFrameLimit.frame z a) ∧
        (∀ᵐ z ∂(ν : Measure (CoreJointFrameLimit.Joint (2 * w + 1))),
          CoreJointFrameLimit.scale z ∈ Set.Icc 1 C) ∧
        Integrable (fun z ↦ CoreJointFrameLimit.frame z i)
          (ν : Measure (CoreJointFrameLimit.Joint (2 * w + 1))) ∧
        (∫ z, CoreJointFrameLimit.frame z i
          ∂(ν : Measure (CoreJointFrameLimit.Joint (2 * w + 1)))) ≤ 8 := by
  let μ := fun n ↦ jointLaw (X n) (ahlSmall_window κ (X n)) (profileL κ (X n))
    w (j n) (windowG (X n)) (θ n) (O n) (hSy n) (hZ n)
  apply CoreJointFrameLimit.exists_joint_limit μ
    (M := (2 * w + 1 : ℕ) * (8 : ℝ)) (C := C)
    (K := CoreActualFrameRectangleLimit.rectangleConstant w) (H := 8)
    (ε := fun n ↦ CoreActualFrameRectangleLimit.rectangleError κ (X n)) (i := i)
    (by positivity) (CoreActualFrameRectangleLimit.rectangleConstant_pos w) (by norm_num)
  · intro n
    simpa only [μ, show (2 : ℝ) * 4 = 8 by norm_num] using
      lintegral_frame_norm_le (X n) (ahlSmall_window κ (X n)) (profileL κ (X n))
        w (j n) (θ n) (O n) (hSy n) (hZ n) (hG n) (hj n) (hL n) (hcal n)
  · intro n
    exact ae_nonnegative_frame (X n) (ahlSmall_window κ (X n)) (profileL κ (X n))
      w (j n) (hG n).le (θ n) (O n) (hSy n) (hZ n)
  · intro n
    exact ae_scale_range (X n) (ahlSmall_window κ (X n)) (profileL κ (X n))
      w (j n) (windowG (X n)) (θ n) (O n) (hSy n) (hZ n) (hθ n)
  · exact (CoreActualFrameRectangleLimit.tendsto_rectangleError hκ).comp hX
  · intro a b hab
    filter_upwards [hX.eventually
      (CoreActualFrameRectangleLimit.eventually_jointLaw_rectangle_bound hκ w a b hab)]
      with n hn
    exact hn (j n) (θ n) (O n) (hSy n) (hZ n) (hj n) (hL n)
  · intro n
    simpa only [μ, show (2 : ℝ) * 4 = 8 by norm_num] using
      lintegral_coordinate_le (X n) (ahlSmall_window κ (X n)) (profileL κ (X n))
        w (j n) (θ n) (O n) (hSy n) (hZ n) (hG n) (hj n) (hL n) (hcal n) i

end
end PrimeGapNormality.Prime.CoreActualFrameJoint
