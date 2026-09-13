import PrimeGapNormality.Prime.CoreRoughScaleLimits
import PrimeGapNormality.Prime.CoreRoughSmallWindow
import PrimeGapNormality.Prime.CoreRoughMeanCount
import PrimeGapNormality.Prime.CoreRoughSyntheticComparison
import PrimeGapNormality.Prime.SmallPresieveMeanFive
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Vanishing synthetic-profile comparison errors

This file collects the scalar limits needed to turn the finite rough-root
comparison into a growing-profile comparison.  All inputs are the proved
Euler scale and the fixed positive profile parameter `κ`.
-/

namespace PrimeGapNormality.Prime.CoreRoughProfileError

open Filter
open scoped Topology

open CoreRoughSyntheticScale CoreRoughScaleLimits CoreRoughSmallWindow

noncomputable section

/-- Profile depth at the literal synthetic scale. -/
def roughProfileL (κ : ℝ) (z : ℕ) : ℕ :=
  profileL κ (roughSyntheticScale z)

/-- Small AHL window at the literal synthetic scale. -/
def roughProfileS (κ : ℝ) (z : ℕ) : ℕ :=
  ahlSmall_window κ (roughSyntheticScale z)

/-- Uniform finite comparison error from the rooted-retention estimate. -/
def roughProfileError (z : ℕ) : ℝ :=
  Real.log 4 / roughGapScale z + 1 / (z : ℝ) + 1 / ((z : ℝ) - 1)

private theorem roughProfileError_nonneg {z : ℕ} (hz : 2 ≤ z) :
    0 ≤ roughProfileError z := by
  have hzR : (2 : ℝ) ≤ z := Nat.cast_le.mpr hz
  have hz0 : (0 : ℝ) ≤ z := by positivity
  have hpred : (0 : ℝ) ≤ (z : ℝ) - 1 := by linarith
  unfold roughProfileError
  exact add_nonneg
    (add_nonneg
      (div_nonneg (Real.log_nonneg (by norm_num)) (roughGapScale_pos z).le)
      (div_nonneg zero_le_one hz0))
    (div_nonneg zero_le_one hpred)

private theorem tendsto_inv_nat_sub_one :
    Tendsto (fun z : ℕ ↦ (1 : ℝ) / ((z : ℝ) - 1)) atTop (nhds 0) := by
  have hsub : Tendsto (fun z : ℕ ↦ (z : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv := tendsto_inv_atTop_zero.comp hsub
  apply hinv.congr'
  exact Eventually.of_forall fun z ↦ by
    simp only [Function.comp_apply, one_div]

private theorem tendsto_log_nat_div_nat :
    Tendsto (fun z : ℕ ↦ Real.log (z : ℝ) / (z : ℝ)) atTop (nhds 0) := by
  have hreal : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hnat.congr'
  exact Eventually.of_forall fun z ↦ rfl

private theorem tendsto_nat_div_nat_sub_one :
    Tendsto (fun z : ℕ ↦ (z : ℝ) / ((z : ℝ) - 1)) atTop (nhds 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_nat_sub_one
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with z hz
  have hne : (z : ℝ) - 1 ≠ 0 := by
    have hzR : (2 : ℝ) ≤ z := Nat.cast_le.mpr hz
    linarith
  field_simp [hne]
  ring

private theorem tendsto_log_nat_div_nat_sub_one :
    Tendsto (fun z : ℕ ↦ Real.log (z : ℝ) / ((z : ℝ) - 1))
      atTop (nhds 0) := by
  have hmul := tendsto_log_nat_div_nat.mul tendsto_nat_div_nat_sub_one
  simp only [zero_mul] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop 2] with z hz
  have hz0 : (z : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hz))
  have hpred : (z : ℝ) - 1 ≠ 0 := by
    have hzR : (2 : ℝ) ≤ z := Nat.cast_le.mpr hz
    linarith
  field_simp [hz0, hpred] <;> ring

/-- The displayed finite comparison error tends to zero. -/
theorem tendsto_roughProfileError_zero :
    Tendsto roughProfileError atTop (nhds 0) := by
  have hGinv : Tendsto (fun z : ℕ ↦ (roughGapScale z)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_roughGapScale_atTop
  have hfirst : Tendsto (fun z : ℕ ↦
      Real.log 4 / roughGapScale z) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hGinv.const_mul (Real.log 4)
  have hsecond : Tendsto (fun z : ℕ ↦ (1 : ℝ) / (z : ℝ))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hsum := (hfirst.add hsecond).add tendsto_inv_nat_sub_one
  simp only [add_zero] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun z ↦ rfl

private theorem tendsto_windowG_synthetic_atTop :
    Tendsto (fun z : ℕ ↦ windowG (roughSyntheticScale z)) atTop atTop :=
  tendsto_windowG_atTop.comp tendsto_roughSyntheticScale_atTop

/-- The physical logarithmic scale at `T(z)` is asymptotic to `G(z)`. -/
theorem tendsto_windowG_synthetic_div_gapScale :
    Tendsto (fun z : ℕ ↦
      windowG (roughSyntheticScale z) / roughGapScale z)
      atTop (nhds 1) := by
  apply tendsto_log_roughSyntheticScale_div_roughGapScale.congr'
  have heq := tendsto_roughSyntheticScale_atTop.eventually
    crtWindowG_eventually_eq_log
  filter_upwards [heq] with z hz
  rw [hz]

private theorem sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ 1 + x := by
  rcases le_total (Real.sqrt x) 1 with h | h
  · exact h.trans (le_add_of_nonneg_right hx)
  · have hmul : Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
      le_mul_of_one_le_left (Real.sqrt_nonneg x) h
    have hle : Real.sqrt x ≤ x := by
      rwa [Real.mul_self_sqrt hx] at hmul
    exact hle.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

private theorem profileL_le_two_mul_log_add_two
    {κ : ℝ} (hκ : 0 ≤ κ) (X : ℕ) :
    (profileL κ X : ℝ) ≤ 2 * κ * Real.log (windowG X) + 2 := by
  have hlog : 0 ≤ Real.log (windowG X) :=
    Real.log_nonneg (le_max_right _ _)
  have hx : 0 ≤ κ * Real.log (windowG X) := mul_nonneg hκ hlog
  have hraw := profileL_cast_le hκ X
  have hsqrt := sqrt_le_one_add hx
  linarith

/-- The profile depth is negligible compared with the synthetic gap scale. -/
theorem tendsto_roughProfileL_div_gapScale_zero
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun z : ℕ ↦
      (roughProfileL κ z : ℝ) / roughGapScale z) atTop (nhds 0) := by
  let H : ℕ → ℝ := fun z ↦ windowG (roughSyntheticScale z)
  let G : ℕ → ℝ := roughGapScale
  have hlogSelfReal : Tendsto (fun x : ℝ ↦ Real.log x / x)
      atTop (nhds 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogHH : Tendsto (fun z : ℕ ↦ Real.log (H z) / H z)
      atTop (nhds 0) := hlogSelfReal.comp tendsto_windowG_synthetic_atTop
  have hHG : Tendsto (fun z : ℕ ↦ H z / G z) atTop (nhds 1) := by
    simpa only [H, G] using tendsto_windowG_synthetic_div_gapScale
  have hlogHG : Tendsto (fun z : ℕ ↦ Real.log (H z) / G z)
      atTop (nhds 0) := by
    have hmul := hlogHH.mul hHG
    simp only [zero_mul] at hmul
    apply hmul.congr'
    exact Eventually.of_forall fun z ↦ by
      have hH : 0 < H z := by
        dsimp only [H]
        exact zero_lt_one.trans_le (le_max_right _ _)
      field_simp [hH.ne']
  have hGinv : Tendsto (fun z : ℕ ↦ (G z)⁻¹) atTop (nhds 0) := by
    have hraw := tendsto_inv_atTop_zero.comp tendsto_roughGapScale_atTop
    apply hraw.congr'
    exact Eventually.of_forall fun z ↦ rfl
  have hmajor : Tendsto (fun z : ℕ ↦
      2 * κ * (Real.log (H z) / G z) + 2 * (G z)⁻¹)
      atTop (nhds 0) := by
    have h1 := hlogHG.const_mul (2 * κ)
    have h2 := hGinv.const_mul (2 : ℝ)
    simpa only [mul_zero, add_zero] using h1.add h2
  refine squeeze_zero' ?_ ?_ hmajor
  · exact Eventually.of_forall fun z ↦
      div_nonneg (Nat.cast_nonneg _) (roughGapScale_pos z).le
  · exact Eventually.of_forall fun z ↦ by
      have hL := profileL_le_two_mul_log_add_two hκ.le
        (roughSyntheticScale z)
      have hG := roughGapScale_pos z
      have hG' : G z ≠ 0 := by simpa only [G] using hG.ne'
      apply (div_le_iff₀ hG).2
      have hform :
          (2 * κ * (Real.log (H z) / G z) + 2 * (G z)⁻¹) * G z =
            2 * κ * Real.log (H z) + 2 := by
        field_simp [hG'] <;> ring
      rw [hform]
      simpa only [roughProfileL, H, G] using hL

private theorem tendsto_gapScale_div_nat_zero :
    Tendsto (fun z : ℕ ↦ roughGapScale z / (z : ℝ)) atTop (nhds 0) := by
  have hupper : Tendsto (fun z : ℕ ↦
      (Real.log (z : ℝ) / eulerProdLowerConst) / (z : ℝ))
      atTop (nhds 0) := by
    have h := tendsto_log_nat_div_nat.const_mul eulerProdLowerConst⁻¹
    simp only [mul_zero] at h
    apply h.congr'
    exact Eventually.of_forall fun z ↦ by ring
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 1] with z hz
    exact div_nonneg (roughGapScale_pos z).le (Nat.cast_nonneg z)
  · filter_upwards [eventually_ge_atTop 16] with z hz
    exact div_le_div_of_nonneg_right
      (roughGapScale_le_log_div_lowerConst hz) (Nat.cast_nonneg z)

private theorem tendsto_gapScale_div_nat_sub_one_zero :
    Tendsto (fun z : ℕ ↦ roughGapScale z / ((z : ℝ) - 1))
      atTop (nhds 0) := by
  have hupper : Tendsto (fun z : ℕ ↦
      (Real.log (z : ℝ) / eulerProdLowerConst) / ((z : ℝ) - 1))
      atTop (nhds 0) := by
    have h := tendsto_log_nat_div_nat_sub_one.const_mul eulerProdLowerConst⁻¹
    simp only [mul_zero] at h
    apply h.congr'
    exact Eventually.of_forall fun z ↦ by ring
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 2] with z hz
    have hden : 0 ≤ (z : ℝ) - 1 := by
      have hzR : (2 : ℝ) ≤ z := Nat.cast_le.mpr hz
      linarith
    exact div_nonneg (roughGapScale_pos z).le hden
  · filter_upwards [eventually_ge_atTop 16] with z hz
    have hden : 0 ≤ (z : ℝ) - 1 := by
      have hzR : (16 : ℝ) ≤ z := Nat.cast_le.mpr hz
      linarith
    exact div_le_div_of_nonneg_right
      (roughGapScale_le_log_div_lowerConst hz) hden

/-- After multiplication by `G(z)`, the comparison error stays bounded and
in fact tends to `log 4`. -/
theorem tendsto_gapScale_mul_roughProfileError :
    Tendsto (fun z : ℕ ↦ roughGapScale z * roughProfileError z)
      atTop (nhds (Real.log 4)) := by
  have hsum := (tendsto_const_nhds (x := Real.log 4)).add
    (tendsto_gapScale_div_nat_zero.add
      tendsto_gapScale_div_nat_sub_one_zero)
  simp only [add_zero] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun z ↦ by
    dsimp only
    have hG := roughGapScale_pos z
    have hcancel :
        roughGapScale z * (Real.log 4 / roughGapScale z) = Real.log 4 := by
      field_simp [hG.ne']
    unfold roughProfileError
    rw [mul_add, mul_add, hcancel]
    ring

/-- The profile-depth-weighted finite comparison error vanishes. -/
theorem tendsto_roughProfileL_mul_error_zero
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun z : ℕ ↦
      (roughProfileL κ z : ℝ) * roughProfileError z)
      atTop (nhds 0) := by
  have hmul := (tendsto_roughProfileL_div_gapScale_zero hκ).mul
    tendsto_gapScale_mul_roughProfileError
  simp only [zero_mul] at hmul
  apply hmul.congr'
  exact Eventually.of_forall fun z ↦ by
    have hG := roughGapScale_pos z
    field_simp [hG.ne'] <;> ring

/-- The small-window-over-gap-scale weighted comparison error vanishes. -/
theorem tendsto_roughProfileS_div_gapScale_mul_error_zero
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun z : ℕ ↦
      ((roughProfileS κ z : ℝ) / roughGapScale z) * roughProfileError z)
      atTop (nhds 0) := by
  have hmajor : Tendsto (fun z : ℕ ↦
      ((6 : ℝ) / 5) *
        (windowG (roughSyntheticScale z) / roughGapScale z) *
          ((roughProfileL κ z : ℝ) * roughProfileError z))
      atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := (6 : ℝ) / 5)).mul
      tendsto_windowG_synthetic_div_gapScale |>.mul
        (tendsto_roughProfileL_mul_error_zero hκ)
    simpa only [mul_zero] using h
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop 2] with z hz
    have he : 0 ≤ roughProfileError z := roughProfileError_nonneg hz
    exact mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (roughGapScale_pos z).le) he
  · filter_upwards [eventually_ge_atTop 2] with z hz
    have hG := roughGapScale_pos z
    have he : 0 ≤ roughProfileError z := roughProfileError_nonneg hz
    have hS : (roughProfileS κ z : ℝ) ≤
        ((6 : ℝ) / 5) * (roughProfileL κ z : ℝ) *
          windowG (roughSyntheticScale z) := by
      dsimp only [roughProfileS, roughProfileL]
      exact Nat.floor_le (ahlSmall_arg_nonneg κ (roughSyntheticScale z))
    have hdiv := div_le_div_of_nonneg_right hS hG.le
    have hmul := mul_le_mul_of_nonneg_right hdiv he
    calc
      ((roughProfileS κ z : ℝ) / roughGapScale z) * roughProfileError z ≤
          (((6 : ℝ) / 5) * (roughProfileL κ z : ℝ) *
            windowG (roughSyntheticScale z) / roughGapScale z) *
              roughProfileError z := hmul
      _ = ((6 : ℝ) / 5) *
          (windowG (roughSyntheticScale z) / roughGapScale z) *
            ((roughProfileL κ z : ℝ) * roughProfileError z) := by ring

/-- Eventual scale package used by the finite rough comparison. -/
theorem eventually_roughProfile_scales
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ z : ℕ in atTop,
      2 ≤ z ∧ 16 ≤ roughGapScale z ∧ roughProfileS κ z ≤ z := by
  filter_upwards [eventually_ge_atTop 2,
    tendsto_roughGapScale_atTop.eventually_ge_atTop 16,
    eventually_ahlSmall_window_roughSyntheticScale_lt hκ] with z hz hG hS
  exact ⟨hz, hG, hS.le⟩

/-- The actual small profile window tends to infinity. -/
theorem tendsto_roughProfileS_atTop
    {κ : ℝ} (hκ : 0 < κ) : Tendsto (roughProfileS κ) atTop atTop := by
  have h := (tendsto_ahlSmall_window_atTop hκ).comp
    tendsto_roughSyntheticScale_atTop
  apply h.congr'
  exact Eventually.of_forall fun z ↦ rfl

/-- Any fixed linear rank envelope inherits the vanishing error. -/
theorem tendsto_linearRank_mul_error_zero
    {κ C D : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    {r : ℕ → ℕ}
    (hr : ∀ᶠ z : ℕ in atTop,
      (r z : ℝ) ≤ C * (roughProfileL κ z : ℝ) + D) :
    Tendsto (fun z : ℕ ↦ (r z : ℝ) * roughProfileError z)
      atTop (nhds 0) := by
  have hmajor : Tendsto (fun z : ℕ ↦
      C * ((roughProfileL κ z : ℝ) * roughProfileError z) +
        D * roughProfileError z) atTop (nhds 0) := by
    have h1 := (tendsto_roughProfileL_mul_error_zero hκ).const_mul C
    have h2 := tendsto_roughProfileError_zero.const_mul D
    simpa only [mul_zero, add_zero] using h1.add h2
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop 2] with z hz
    have he : 0 ≤ roughProfileError z := roughProfileError_nonneg hz
    exact mul_nonneg (Nat.cast_nonneg _) he
  · filter_upwards [hr, eventually_ge_atTop 2] with z hrz hz
    have he : 0 ≤ roughProfileError z := roughProfileError_nonneg hz
    have hmul := mul_le_mul_of_nonneg_right hrz he
    calc
      (r z : ℝ) * roughProfileError z ≤
          (C * (roughProfileL κ z : ℝ) + D) * roughProfileError z := hmul
      _ = C * ((roughProfileL κ z : ℝ) * roughProfileError z) +
          D * roughProfileError z := by ring

/-- In particular the paper rank `profileR L 20` has vanishing comparison
error. -/
theorem tendsto_profileR_twenty_mul_error_zero
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun z : ℕ ↦
      (profileR (roughProfileL κ z) 20 : ℝ) * roughProfileError z)
      atTop (nhds 0) := by
  apply tendsto_linearRank_mul_error_zero hκ
    (C := 21) (D := 2) (by norm_num) (by norm_num)
  exact Eventually.of_forall fun z ↦ by
    have h := profileR_cast_le (roughProfileL κ z) (d0 := (20 : ℝ))
      (by norm_num)
    nlinarith

end

end PrimeGapNormality.Prime.CoreRoughProfileError
