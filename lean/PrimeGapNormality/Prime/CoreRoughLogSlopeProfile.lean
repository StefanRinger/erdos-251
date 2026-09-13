import PrimeGapNormality.Prime.CoreRoughCellAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The explicit logarithmic-slope roughness profile

This instantiates the threshold/regularity conditions with Ψ(t)=c*t/log t.
The resulting natural cutoff is literally floor(n^(c/log log n)). Only
eventual regularity is relevant; the totalized formula at small t is kept
explicit rather than concealing a choice of finite initial convention.
-/

namespace PrimeGapNormality.Prime.CoreRoughLogSlopeProfile

open Filter CoreRoughThreshold
open scoped Topology
noncomputable section

def profile (c t : ℝ) : ℝ := c * t / Real.log t

def profileDerivative (c t : ℝ) : ℝ :=
  c * (Real.log t - 1) / Real.log t ^ 2

theorem tendsto_profile_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (profile c) atTop atTop := by
  have hnorm := (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).eventuallyLE
  have hroot : Tendsto (fun t : ℝ => c * t ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_atTop hc
  refine tendsto_atTop_mono' atTop ?_ hroot
  filter_upwards [hnorm, eventually_gt_atTop (1 : ℝ)] with t hnorm ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hl : 0 < Real.log t := Real.log_pos ht
  have hroot0 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
  have hlogle : Real.log t ≤ t ^ (1 / 2 : ℝ) := by
    simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hl.le,
      abs_of_nonneg hroot0] using hnorm
  have hsq : t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) = t := by
    rw [← Real.rpow_add ht0]
    norm_num
  have hbound : t ^ (1 / 2 : ℝ) ≤ t / Real.log t :=
    (le_div_iff₀ hl).mpr ((mul_le_mul_of_nonneg_left hlogle hroot0).trans_eq hsq)
  simpa only [profile, mul_div_assoc] using mul_le_mul_of_nonneg_left hbound hc.le

theorem hasSlopeBudget {c A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (hAc : A * c ≤ 1) : HasSlopeBudget (profile c) A := by
  refine ⟨hA, tendsto_profile_atTop hc, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (3 * c),
    eventually_gt_atTop (1 : ℝ)] with t hlc ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hl : 0 < Real.log t := Real.log_pos ht
  have hP : 0 < profile c t := div_pos (mul_pos hc ht0) hl
  have hthree : 3 * profile c t ≤ t := by
    unfold profile
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hl).mpr
    nlinarith
  have hlog : Real.log (3 * profile c t) ≤ Real.log t :=
    Real.log_le_log (by positivity) hthree
  have hAinv : A ≤ 1 / c := (le_div_iff₀ hc).mpr hAc
  calc
    A * Real.log (3 * profile c t) ≤ A * Real.log t :=
      mul_le_mul_of_nonneg_left hlog hA.le
    _ ≤ (1 / c) * Real.log t := mul_le_mul_of_nonneg_right hAinv hl.le
    _ = t / profile c t := by
      unfold profile
      field_simp [hc.ne', ht0.ne', hl.ne']

theorem profile_hasDerivAt (c : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (profile c) (profileDerivative c t) t := by
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hh := ((hasDerivAt_id t).const_mul c).div (Real.hasDerivAt_log ht0) hl
  have hcancel : c * t * t⁻¹ = c := by
    rw [mul_assoc, mul_inv_cancel₀ ht0, mul_one]
  have hderiv : (c * 1 * Real.log t - c * id t * t⁻¹) /
      Real.log t ^ 2 = profileDerivative c t := by
    simp only [id_eq, mul_one, hcancel, profileDerivative]
    congr 1
    ring
  rw [hderiv] at hh
  exact hh

theorem weightedDerivative {c : ℝ} (hc : 0 < c) :
    CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      (profile c) (profileDerivative c) 1 := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with t hl1 ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hl : 0 < Real.log t := Real.log_pos ht
  refine ⟨div_pos (mul_pos hc ht0) hl, profile_hasDerivAt c ht, ?_, ?_⟩
  · unfold profileDerivative
    exact mul_nonneg ht0.le (div_nonneg
      (mul_nonneg hc.le (sub_nonneg.mpr hl1)) (sq_nonneg _))
  · unfold profileDerivative profile
    rw [one_mul, ← mul_div_assoc]
    apply (div_le_div_iff₀ (sq_pos_of_pos hl) hl).mpr
    have hn : 0 ≤ c * t * Real.log t := by positivity
    nlinarith

theorem zPsi_eq_rpow_cutoff (c : ℝ) {n : ℕ} (hn : 0 < n) :
    zPsi (profile c) n =
      ⌊(n : ℝ) ^ (c / Real.log (Real.log (n : ℝ)))⌋₊ := by
  unfold zPsi profile
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
  congr 2
  ring

end
end PrimeGapNormality.Prime.CoreRoughLogSlopeProfile
