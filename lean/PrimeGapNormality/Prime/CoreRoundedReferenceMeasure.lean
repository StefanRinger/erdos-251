import PrimeGapNormality.Prime.CoreRealPowerImageAC
import PrimeGapNormality.Prime.CoreRestrictedFibreImageAC
import PrimeGapNormality.Prime.CoreActualFrameLimit
import PrimeGapNormality.Prime.CoreRoundedCriticalRank

/-!
# The actual finite reference for a rounded leading action

The parameter is the width-zero joint law: circle outer phase, one real
merged gap W, and real scale theta. No independence or real phase lift is
used. The reference is the image of the actual restricted product region.
The final theorem extracts one joint subsequence and constructs this
reference before any subsequent test, cutoff or epsilon is selected.
-/

namespace PrimeGapNormality.Prime.CoreRoundedReferenceMeasure

open MeasureTheory Set Filter CoreCyclic
open CoreRoundedCriticalRank
open scoped Topology ENNReal
noncomputable section
set_option maxHeartbeats 1000000

abbrev Circle := AddCircle (1 : ℝ)
abbrev Joint := CoreJointFrameLimit.Joint 1
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def width (z : Joint) : ℝ := CoreJointFrameLimit.frame z 0

theorem continuous_width : Continuous width :=
  (continuous_apply (0 : Fin 1)).comp CoreJointFrameLimit.continuous_frame

def phase (a A C : ℝ) (z : Joint × ℝ) : Circle :=
  z.1.1 + ((CoreJointFrameLimit.scale z.1 *
    CoreRealPowerImageAC.action (width z.1) a A C z.2 : ℝ) : Circle)

theorem continuous_phase {a : ℝ} (ha : 0 < a) (A C : ℝ) : Continuous (phase a A C) := by
  have hw : Continuous (fun z : Joint × ℝ => width z.1) := continuous_width.comp continuous_fst
  have ht : Continuous (fun z : Joint × ℝ => CoreJointFrameLimit.scale z.1) :=
    CoreJointFrameLimit.continuous_scale.comp continuous_fst
  have hp : Continuous (fun z : Joint × ℝ =>
      CoreRealPowerImageAC.action (width z.1) a A C z.2) :=
    (continuous_const.mul ((Real.continuous_rpow_const ha.le).comp continuous_snd)).add
      (continuous_const.mul ((Real.continuous_rpow_const ha.le).comp (hw.sub continuous_snd)))
  exact (continuous_fst.comp continuous_fst).add
    ((AddCircle.continuous_mk' (1 : ℝ)).comp (ht.mul hp))

theorem circle_image_of_real_ac (f : ℝ → ℝ) (hf : Measurable f) (I : Set ℝ)
    (hreal : Measure.map f (volume.restrict I) ≪ (volume : Measure ℝ)) (O : Circle) :
    Measure.map (fun t => O + ((f t : ℝ) : Circle)) (volume.restrict I) ≪
      (volume : Measure Circle) := by
  have hcoe : Measurable (fun t : ℝ => (t : Circle)) := AddCircle.measurable_mk'
  have hcircle := (hreal.map hcoe).trans CorePolynomialImage.circle_projection_absolutelyContinuous
  rw [Measure.map_map hcoe hf] at hcircle
  have hadd : Measurable (fun x : Circle => O + x) := (continuous_const.add continuous_id).measurable
  have hh := hcircle.map hadd
  rw [(measurePreserving_add_left (volume : Measure Circle) O).map_eq,
    Measure.map_map hadd (hcoe.comp hf)] at hh
  exact hh

/-- The usable coefficient condition, with the correct exceptional linear
case. It is derived from the integer cyclic label below. -/
def UsableCoefficients (a A C : ℝ) : Prop := if a = 1 then A - C ≠ 0 else A ≠ 0

theorem fibre_absolutelyContinuous {a A C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hcoeff : UsableCoefficients a A C) (z : Joint)
    (hW : 0 < width z) (hθ : CoreJointFrameLimit.scale z ≠ 0) :
    Measure.map (fun t : ℝ => phase a A C (z, t))
      (volume.restrict (Ioo 0 (width z))) ≪ (volume : Measure Circle) := by
  let θ := CoreJointFrameLimit.scale z
  have heq : (fun t : ℝ => θ * CoreRealPowerImageAC.action (width z) a A C t) =
      CoreRealPowerImageAC.action (width z) a (θ * A) (θ * C) := by
    funext t
    unfold CoreRealPowerImageAC.action
    ring
  have hreal : Measure.map (CoreRealPowerImageAC.action (width z) a (θ * A) (θ * C))
      (volume.restrict (Ioo 0 (width z))) ≪ (volume : Measure ℝ) := by
    by_cases he : a = 1
    · have hAC : A - C ≠ 0 := by simpa only [UsableCoefficients, if_pos he] using hcoeff
      have hc : θ * A - θ * C ≠ 0 := by
        rw [← mul_sub]
        exact mul_ne_zero hθ hAC
      rw [he]
      exact CoreRealPowerImageAC.map_interval_absolutelyContinuous_one _ _ _ hc
    · have hA : A ≠ 0 := by simpa only [UsableCoefficients, if_neg he] using hcoeff
      exact CoreRealPowerImageAC.map_interval_absolutelyContinuous hW ha
        (lt_of_le_of_ne ha1 he) (mul_ne_zero hθ hA)
  have hh := circle_image_of_real_ac _
    (CoreRealPowerImageAC.continuous_action (width z) (θ * A) (θ * C) ha.le).measurable
    (Ioo 0 (width z)) hreal z.1
  rw [← heq] at hh
  exact hh

def referenceMeasure (ν : ProbabilityMeasure Joint) (a A C : ℝ) : Measure Circle :=
  CoreRestrictedFibreImageAC.referenceMeasure (ν : Measure Joint) width (phase a A C)

theorem referenceMeasure_mass (ν : ProbabilityMeasure Joint) {a : ℝ}
    (ha : 0 < a) (A C : ℝ) :
    referenceMeasure ν a A C univ = ∫⁻ z, ENNReal.ofReal (width z) ∂(ν : Measure Joint) :=
  CoreRestrictedFibreImageAC.referenceMeasure_mass (ν : Measure Joint) continuous_width.measurable
    (phase a A C) (continuous_phase ha A C).measurable

theorem referenceMeasure_mass_eq_integral (ν : ProbabilityMeasure Joint) {a : ℝ}
    (ha : 0 < a) (A C : ℝ) (hW : ∀ᵐ z ∂(ν : Measure Joint), 0 ≤ width z)
    (hWi : Integrable width (ν : Measure Joint)) :
    referenceMeasure ν a A C univ = ENNReal.ofReal (∫ z, width z ∂(ν : Measure Joint)) :=
  CoreRestrictedFibreImageAC.referenceMeasure_mass_eq_integral (ν : Measure Joint)
    continuous_width.measurable hW hWi (phase a A C) (continuous_phase ha A C).measurable

theorem referenceMeasure_finite (ν : ProbabilityMeasure Joint) {a : ℝ}
    (ha : 0 < a) (A C : ℝ) (hW : ∀ᵐ z ∂(ν : Measure Joint), 0 ≤ width z)
    (hWi : Integrable width (ν : Measure Joint)) : IsFiniteMeasure (referenceMeasure ν a A C) :=
  CoreRestrictedFibreImageAC.referenceMeasure_isFinite (ν : Measure Joint)
    continuous_width.measurable hW hWi (phase a A C) (continuous_phase ha A C).measurable

theorem referenceMeasure_absolutelyContinuous (ν : ProbabilityMeasure Joint)
    {a A C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hcoeff : UsableCoefficients a A C)
    (hθ : ∀ᵐ z ∂(ν : Measure Joint), CoreJointFrameLimit.scale z ≠ 0) :
    referenceMeasure ν a A C ≪ (volume : Measure Circle) := by
  apply CoreRestrictedFibreImageAC.referenceMeasure_absolutelyContinuous_of_pos_fibres
    (ν : Measure Joint) volume continuous_width.measurable (phase a A C)
    (continuous_phase ha A C).measurable
  filter_upwards [hθ] with z hz
  exact fun hW => fibre_absolutelyContinuous ha ha1 hcoeff z hW hz

theorem referenceMeasure_mass_le_eight (ν : ProbabilityMeasure Joint) {a : ℝ}
    (ha : 0 < a) (A C : ℝ) (hW : ∀ᵐ z ∂(ν : Measure Joint), 0 ≤ width z)
    (hWi : Integrable width (ν : Measure Joint))
    (hM : ∫ z, width z ∂(ν : Measure Joint) ≤ 8) :
    referenceMeasure ν a A C univ ≤ ENNReal.ofReal 8 :=
  CoreRestrictedFibreImageAC.referenceMeasure_mass_le (ν : Measure Joint)
    continuous_width.measurable hW hWi (phase a A C) (continuous_phase ha A C).measurable hM

theorem usableCoefficients_of_label {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {a : ℝ} (b : Fin k → ℤ) (s : Fin k) (hs : UsableLeadingLabel B hk a b s) :
    UsableCoefficients a ((B : ℝ) * (b s : ℝ)) (b (cyclicSucc hk s) : ℝ) := by
  by_cases he : a = 1
  · have hh : (B : ℤ) * b s - b (cyclicSucc hk s) ≠ 0 := by
      simpa only [UsableLeadingLabel, if_pos he] using hs
    simp only [UsableCoefficients, if_pos he]
    exact_mod_cast hh
  · have hh : b s ≠ 0 := by simpa only [UsableLeadingLabel, if_neg he] using hs
    simp only [UsableCoefficients, if_neg he]
    exact mul_ne_zero (by exact_mod_cast (show B ≠ 0 by omega)) (by exact_mod_cast hh)

def labelledReference (ν : ProbabilityMeasure Joint) (B : ℕ) {k : ℕ} (hk : 0 < k)
    (a : ℝ) (b : Fin k → ℤ) (s : Fin k) : Measure Circle :=
  referenceMeasure ν a ((B : ℝ) * (b s : ℝ)) (b (cyclicSucc hk s) : ℝ)

/-- Extraction from the TRUE width-zero auxiliary joint laws. The outer
phase is arbitrary and can depend on the whole completed frame. Finite
admissibility hypotheses are the same ones as the existing actual joint
limit theorem; no reference, moment, AC, independence or model-comparison
hypothesis is supplied. The label is fixed before extracting the law. -/
theorem exists_actual_profile_reference
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) {a κ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hκ : 0 < κ)
    (b : Fin k → ℤ) (s : Fin k) (hs : UsableLeadingLabel B hk a b s)
    (X : ℕ → ℕ) (hX : Tendsto X atTop atTop) (j : ℕ → ℕ)
    (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → Circle)
    (hSy : ∀ n, ∀ t ∈ mixScale (X n), ahlSmall_window κ (X n) ≤ sieveCutoff (t : ℝ))
    (hZ : ∀ n, 0 < mixZ (X n)) (hG : ∀ n, 0 < windowG (X n))
    (hj : ∀ n, 1 ≤ j n) (hL : ∀ n, j n < profileL κ (X n))
    (hcal : ∀ n, ∀ t ∈ mixScale (X n),
      (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / windowG (X n) ≤ 4)
    (hθ : ∀ n, θ n ∈ Set.Icc 1 ((B : ℝ) ^ k)) :
    ∃ ν : ProbabilityMeasure Joint, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => CoreActualFrameJoint.jointLaw (X (φ n))
        (ahlSmall_window κ (X (φ n))) (profileL κ (X (φ n))) 0 (j (φ n))
        (windowG (X (φ n))) (θ (φ n)) (O (φ n)) (hSy (φ n)) (hZ (φ n))) atTop (𝓝 ν) ∧
      (∀ᵐ z ∂(ν : Measure Joint), 0 ≤ width z) ∧
      (∀ᵐ z ∂(ν : Measure Joint), CoreJointFrameLimit.scale z ∈ Set.Icc 1 ((B : ℝ) ^ k)) ∧
      Integrable width (ν : Measure Joint) ∧
      IsFiniteMeasure (labelledReference ν B hk a b s) ∧
      labelledReference ν B hk a b s ≪ (volume : Measure Circle) ∧
      labelledReference ν B hk a b s univ ≤ ENNReal.ofReal 8 := by
  obtain ⟨ν, φ, hφ, hconv, hframeAC, hnonneg, hscale, hint, hmoment⟩ :=
    CoreActualFrameJoint.exists_actual_profile_joint_limit hκ X hX 0 j θ O hSy hZ hG
      (fun n => by simpa only [Nat.zero_add] using hj n)
      (fun n => by simpa only [Nat.add_zero] using hL n) hcal hθ (0 : Fin (2 * 0 + 1))
  have hW : ∀ᵐ z ∂(ν : Measure Joint), 0 ≤ width z := hnonneg.mono fun z hz => hz 0
  have hθ0 : ∀ᵐ z ∂(ν : Measure Joint), CoreJointFrameLimit.scale z ≠ 0 :=
    hscale.mono fun z hz => (zero_lt_one.trans_le hz.1).ne'
  refine ⟨ν, φ, hφ, hconv, hW, hscale, hint, ?_, ?_, ?_⟩
  · exact referenceMeasure_finite ν ha _ _ hW hint
  · exact referenceMeasure_absolutelyContinuous ν ha ha1 (usableCoefficients_of_label hB hk b s hs) hθ0
  · exact referenceMeasure_mass_le_eight ν ha _ _ hW hint hmoment

end
end PrimeGapNormality.Prime.CoreRoundedReferenceMeasure
