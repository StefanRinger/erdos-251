import PrimeGapNormality.Prime.CoreJointFrameLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Bounded continuous insertion tests for weak passage. Both the width and
frame cutoff are explicit. The unbounded auxiliary width is never passed
through weak convergence using only a first-moment bound. -/

namespace PrimeGapNormality.Prime.CoreCompactFrameTest
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
abbrev Circle := AddCircle (1 : ℝ)

def cutoff (A : ℝ) {r : ℕ} (Y : Fin r → ℝ) : ℝ :=
  max 0 (min 1 (A + 1 - ‖Y‖))

theorem cutoff_nonneg (A : ℝ) {r : ℕ} (Y : Fin r → ℝ) :
    0 ≤ cutoff A Y := le_max_left _ _

theorem cutoff_le_one (A : ℝ) {r : ℕ} (Y : Fin r → ℝ) :
    cutoff A Y ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem cutoff_eq_one {A : ℝ} {r : ℕ} {Y : Fin r → ℝ} (hY : ‖Y‖ ≤ A) :
    cutoff A Y = 1 := by
  simp [cutoff, min_eq_left (by linarith : 1 ≤ A + 1 - ‖Y‖)]

theorem cutoff_eq_zero {A : ℝ} {r : ℕ} {Y : Fin r → ℝ} (hY : A + 1 ≤ ‖Y‖) :
    cutoff A Y = 0 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem continuous_cutoff (A : ℝ) (r : ℕ) : Continuous (cutoff A (r := r)) := by
  unfold cutoff
  fun_prop

def clippedWidth (A W : ℝ) : ℝ := min (max W 0) (A + 1)

theorem clippedWidth_nonneg {A : ℝ} (hA : 0 ≤ A) (W : ℝ) :
    0 ≤ clippedWidth A W := le_min (le_max_right _ _) (by linarith)

theorem clippedWidth_le (A W : ℝ) : clippedWidth A W ≤ A + 1 := min_le_right _ _

theorem clippedWidth_le_self (A : ℝ) {W : ℝ} (hW : 0 ≤ W) :
    clippedWidth A W ≤ W := by
  simpa only [clippedWidth, max_eq_left hW] using min_le_left W (A + 1)

theorem clippedWidth_eq_self {A W : ℝ} (hW : 0 ≤ W) (hWA : W ≤ A + 1) :
    clippedWidth A W = W := by simp [clippedWidth, max_eq_left hW, min_eq_left hWA]

variable {α : Type*} [TopologicalSpace α]

def rawTest (A : ℝ) {r : ℕ} (Y : α → Fin r → ℝ) (W : α → ℝ)
    (H : α → ℝ → Circle) (f : Circle →ᵇ ℝ) (a : α) : ℝ :=
  cutoff A (Y a) * ∫ t in (0 : ℝ)..clippedWidth A (W a), f (H a t)

theorem continuous_rawTest (A : ℝ) {r : ℕ}
    (Y : α → Fin r → ℝ) (W : α → ℝ) (H : α → ℝ → Circle)
    (hY : Continuous Y) (hW : Continuous W) (hH : Continuous H.uncurry)
    (f : Circle →ᵇ ℝ) : Continuous (rawTest A Y W H f) := by
  apply ((continuous_cutoff A r).comp hY).mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact f.continuous.comp hH
  · exact (hW.max continuous_const).min continuous_const

theorem norm_rawTest_le {A : ℝ} (hA : 0 ≤ A) {r : ℕ}
    (Y : α → Fin r → ℝ) (W : α → ℝ) (H : α → ℝ → Circle)
    (f : Circle →ᵇ ℝ) (a : α) :
    ‖rawTest A Y W H f a‖ ≤ ‖f‖ * (A + 1) := by
  have hI : ‖∫ t in (0 : ℝ)..clippedWidth A (W a), f (H a t)‖ ≤
      ‖f‖ * clippedWidth A (W a) := by
    simpa only [sub_zero, abs_of_nonneg (clippedWidth_nonneg hA (W a))] using
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := clippedWidth A (W a))
        (fun t _ ↦ f.norm_coe_le_norm (H a t))
  unfold rawTest
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg A (Y a))]
  calc
    _ ≤ 1 * ‖∫ t in (0 : ℝ)..clippedWidth A (W a), f (H a t)‖ :=
      mul_le_mul_of_nonneg_right (cutoff_le_one A (Y a)) (norm_nonneg _)
    _ ≤ ‖f‖ * clippedWidth A (W a) := by simpa only [one_mul] using hI
    _ ≤ ‖f‖ * (A + 1) := mul_le_mul_of_nonneg_left (clippedWidth_le A (W a)) (norm_nonneg f)

def boundedTest {A : ℝ} (hA : 0 ≤ A) {r : ℕ}
    (Y : α → Fin r → ℝ) (W : α → ℝ) (H : α → ℝ → Circle)
    (hY : Continuous Y) (hW : Continuous W) (hH : Continuous H.uncurry)
    (f : Circle →ᵇ ℝ) : α →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (rawTest A Y W H f)
    (continuous_rawTest A Y W H hY hW hH f) (‖f‖ * (A + 1))
    (norm_rawTest_le hA Y W H f)

theorem rawTest_eq_fullIntegral_of_small {A : ℝ} {r : ℕ}
    (Y : α → Fin r → ℝ) (W : α → ℝ) (H : α → ℝ → Circle)
    (f : Circle →ᵇ ℝ) (a : α) (hY : ‖Y a‖ ≤ A)
    (hW : 0 ≤ W a) (hWA : W a ≤ A) :
    rawTest A Y W H f a = ∫ t in (0 : ℝ)..W a, f (H a t) := by
  rw [rawTest, cutoff_eq_one hY, one_mul,
    clippedWidth_eq_self hW (by linarith)]

theorem rawTest_nonneg_le_fullIntegral {A : ℝ} (hA : 0 ≤ A) {r : ℕ}
    (Y : α → Fin r → ℝ) (W : α → ℝ) (H : α → ℝ → Circle)
    (hH : Continuous H.uncurry) (f : Circle →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x)
    (a : α) (hW : 0 ≤ W a) :
    0 ≤ rawTest A Y W H f a ∧
      rawTest A Y W H f a ≤ ∫ t in (0 : ℝ)..W a, f (H a t) := by
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..clippedWidth A (W a), f (H a t) :=
    intervalIntegral.integral_nonneg (clippedWidth_nonneg hA _) (fun t _ ↦ hf _)
  constructor
  · exact mul_nonneg (cutoff_nonneg A (Y a)) hI0
  · calc
      rawTest A Y W H f a ≤
          1 * (∫ t in (0 : ℝ)..clippedWidth A (W a), f (H a t)) :=
        mul_le_mul_of_nonneg_right (cutoff_le_one A (Y a)) hI0
      _ ≤ ∫ t in (0 : ℝ)..W a, f (H a t) := by
        rw [one_mul]
        apply intervalIntegral.integral_mono_interval le_rfl
          (clippedWidth_nonneg hA _) (clippedWidth_le_self A hW)
        · exact ae_of_all _ fun t ↦ hf _
        · exact (f.continuous.comp (hH.comp (continuous_const.prodMk continuous_id))).intervalIntegrable _ _

end
end PrimeGapNormality.Prime.CoreCompactFrameTest
