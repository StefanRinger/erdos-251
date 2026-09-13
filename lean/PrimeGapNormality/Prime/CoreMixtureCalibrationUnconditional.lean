import PrimeGapNormality.Prime.CoreMixtureCalibrationLimit
import PrimeGapNormality.Prime.CorePrimeDensityBounds

/-!
# Unconditional main/model calibration

The normalized arithmetic count is bounded using quantitative Bertrand.
The proof below is the exact existing calibration calculation with the
density factor increased from 4 to 16. All relative model errors and
growing Janossy costs are unchanged; no prime-pattern assumption is used.
-/

open Filter Finset
open scoped Classical Topology
namespace PrimeGapNormality.Prime.CoreCalibrationUnconditional
noncomputable section
set_option maxHeartbeats 800000

private theorem eventually_two_loglog_pow_six_le_log_limit :
    ∀ᶠ X : ℕ in atTop,
      2 * Real.log (Real.log (X : ℝ)) ^ 6 ≤ Real.log (X : ℝ) := by
  have hreal :=
    (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 6 (by norm_num)).comp
      Real.tendsto_log_atTop
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [one_mul, add_zero, Function.comp_apply] at hnat
  filter_upwards [eventually_ge_atTop 16,
    hnat.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))]
      with X hX hball
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16)
      (Nat.cast_le.mpr hX))
  have hll : 0 < Real.log (Real.log (X : ℝ)) :=
    zero_lt_one.trans (one_lt_log_log_of_sixteen_le hX)
  have hratio0 : 0 ≤
      Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ) :=
    div_nonneg (pow_nonneg hll.le 6) hlog.le
  have hratio :
      Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ) < 1 / 2 := by
    have habs :
        |Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ) - 0| < 1 / 2 :=
      hball
    rw [sub_zero, abs_of_nonneg hratio0] at habs
    exact habs
  have := (div_lt_iff₀ hlog).mp hratio
  linarith

private theorem eventually_log_ge_two :
    ∀ᶠ X : ℕ in atTop, (2 : ℝ) ≤ Real.log (X : ℝ) :=
  (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop 2)

theorem tendsto_calibration
    {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    Tendsto (coreMixtureJanossyCalibration κ d0) atTop (nhds 0) := by
  have hfirst : Tendsto (fun X : ℕ =>
      96 * (Real.exp (13 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-eulerProdLowerConst))) atTop (nhds 0) := by
    have h :=
      (tendsto_exp_loglog_pow_four_mul_rpow_neg
        (A := (13 : ℝ)) (ε := eulerProdLowerConst) (by norm_num)
        eulerProdLowerConst_pos).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hc := h.const_mul (96 : ℝ)
    simpa only [Function.comp_apply, mul_zero] using hc
  have hsecond : Tendsto (fun X : ℕ =>
      64 * (Real.exp (11 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-(1 : ℝ)))) atTop (nhds 0) := by
    have h :=
      (tendsto_exp_loglog_pow_four_mul_rpow_neg
        (A := (11 : ℝ)) (ε := (1 : ℝ)) (by norm_num) (by norm_num)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
    have hc := h.const_mul (64 : ℝ)
    simpa only [Function.comp_apply, mul_zero] using hc
  have hupper : Tendsto (fun X : ℕ =>
      96 * (Real.exp (13 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-eulerProdLowerConst)) +
      64 * (Real.exp (11 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-(1 : ℝ)))) atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  have hle : ∀ᶠ X : ℕ in atTop,
      coreMixtureJanossyCalibration κ d0 X ≤
        96 * (Real.exp (13 * Real.log (Real.log (X : ℝ)) ^ 4) *
          (X : ℝ) ^ (-eulerProdLowerConst)) +
        64 * (Real.exp (11 * Real.log (Real.log (X : ℝ)) ^ 4) *
          (X : ℝ) ^ (-(1 : ℝ))) := by
    filter_upwards [eventually_coreMixture_small_janossy_calibration_le hκ hd0,
      eventually_profileFits hκ hd0,
      CorePrimeDensity.eventually_X_div_windowNX_le,
      eventually_log_ge_two,
      eventually_two_loglog_pow_six_le_log_limit]
        with X hfinite hfit hN hG2 hloglog
    let r := profileR (profileL κ X) d0
    let G : ℝ := Real.log (X : ℝ)
    let ell : ℝ := Real.log G
    let δ := coreMixtureRelativeError κ d0 X
    let C : ℝ := (((r + 1) * ((ahlSmall_omega κ X).card + 1) ^ r : ℕ) : ℝ)
    have hX3 : 3 ≤ X := le_trans (by norm_num) hfit.1
    have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
    have hGpos : 0 < G := by dsimp only [G]; exact zero_lt_two.trans_le hG2
    have hell1 : 1 < ell := by
      dsimp only [ell, G]
      exact one_lt_log_log_of_sixteen_le hfit.1
    have hell0 : 0 ≤ ell := (zero_lt_one.trans hell1).le
    have hδ0 : 0 ≤ δ := by
      dsimp only [δ, coreMixtureRelativeError]
      positivity
    have hC : C ^ 2 ≤ Real.exp (10 * ell ^ 4) := by
      dsimp only [C, r, ell, G]
      exact small_combination_cost_le_exp hfit hG2
    have hlog2 : 0 < Real.log (2 * (X : ℝ)) := by
      have hX3r : (3 : ℝ) ≤ X := by exact_mod_cast hX3
      exact Real.log_pos (by nlinarith)
    have hNpos : 0 < (windowNX X : ℝ) :=
      Nat.cast_pos.mpr (windowNX_pos (by omega : 0 < X))
    have hXN : (X : ℝ) / (windowNX X : ℝ) ≤ 16 * G := hN
    have hr1 : ((r + 1 : ℕ) : ℝ) ≤ ell ^ 3 := by
      dsimp only [r, ell, G]
      simpa only [Nat.cast_add, Nat.cast_one] using hfit.2.2.1
    have hrsq : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ell ^ 6 := by
      have hr0 : 0 ≤ ((r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      calc
        ((r + 1 : ℕ) : ℝ) ^ 2 ≤ (ell ^ 3) ^ 2 :=
          pow_le_pow_left₀ hr0 hr1 2
        _ = ell ^ 6 := by ring
    have hrsqG : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ G ^ 2 := by
      have htwo : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ G :=
        (mul_le_mul_of_nonneg_left hrsq (by norm_num)).trans
          (by simpa only [ell, G] using hloglog)
      have hG1 : 1 ≤ G := (by norm_num : (1 : ℝ) ≤ 2).trans hG2
      exact (le_trans (by linarith)
        (le_self_pow₀ hG1 (by omega : 2 ≠ 0)))
    have hδ : δ ≤ 3 * G ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst) +
        (2 : ℝ) / X := by
      dsimp only [δ, coreMixtureRelativeError, r]
      have hrsq' :
          (profileR (profileL κ X) d0 + 1 : ℝ) ^ 2 ≤ G ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hrsqG
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrsq' (by norm_num))
          (Real.rpow_nonneg (Nat.cast_nonneg X) _)) le_rfl
    have hrate : 2 * δ * (X : ℝ) / (windowNX X : ℝ) ≤ 32 * δ * G := by
      rw [mul_div_assoc]
      calc
        2 * δ * ((X : ℝ) / (windowNX X : ℝ)) ≤ 2 * δ * (16 * G) :=
          mul_le_mul_of_nonneg_left hXN (mul_nonneg (by norm_num) hδ0)
        _ = 32 * δ * G := by ring
    have hδG : 32 * δ * G ≤
        96 * G ^ 3 * (X : ℝ) ^ (-eulerProdLowerConst) +
          64 * G * ((X : ℝ)⁻¹) := by
      have hmul := mul_le_mul_of_nonneg_right hδ
        (show (0 : ℝ) ≤ 32 * G by positivity)
      calc
        32 * δ * G = (32 * G) * δ := by ring
        _ ≤ (32 * G) *
            (3 * G ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst) +
              (2 : ℝ) / X) := by simpa only [mul_comm] using hmul
        _ = 96 * G ^ 3 * (X : ℝ) ^ (-eulerProdLowerConst) +
            64 * G * ((X : ℝ)⁻¹) := by rw [div_eq_mul_inv]; ring
    have hGexp : G = Real.exp ell := by
      dsimp only [ell]
      exact (Real.exp_log hGpos).symm
    have hellle4 : ell ≤ ell ^ 4 :=
      le_self_pow₀ hell1.le (by omega : 4 ≠ 0)
    have hGle : G ≤ Real.exp (ell ^ 4) := by
      rw [hGexp]
      exact Real.exp_le_exp.mpr hellle4
    have hG3 : G ^ 3 ≤ Real.exp (3 * ell ^ 4) := by
      calc
        G ^ 3 ≤ (Real.exp (ell ^ 4)) ^ 3 :=
          pow_le_pow_left₀ hGpos.le hGle 3
        _ = Real.exp (3 * ell ^ 4) := by
          rw [← Real.exp_nat_mul]
          norm_num
    have hexp13 : Real.exp (10 * ell ^ 4) * G ^ 3 ≤
        Real.exp (13 * ell ^ 4) := by
      calc
        Real.exp (10 * ell ^ 4) * G ^ 3 ≤
            Real.exp (10 * ell ^ 4) * Real.exp (3 * ell ^ 4) :=
          mul_le_mul_of_nonneg_left hG3 (Real.exp_nonneg _)
        _ = Real.exp (13 * ell ^ 4) := by rw [← Real.exp_add]; ring_nf
    have hexp11 : Real.exp (10 * ell ^ 4) * G ≤
        Real.exp (11 * ell ^ 4) := by
      calc
        Real.exp (10 * ell ^ 4) * G ≤
            Real.exp (10 * ell ^ 4) * Real.exp (ell ^ 4) :=
          mul_le_mul_of_nonneg_left hGle (Real.exp_nonneg _)
        _ = Real.exp (11 * ell ^ 4) := by rw [← Real.exp_add]; ring_nf
    have hboundRate : C ^ 2 *
        (2 * δ * (X : ℝ) / (windowNX X : ℝ)) ≤
        96 * (Real.exp (13 * ell ^ 4) *
          (X : ℝ) ^ (-eulerProdLowerConst)) +
        64 * (Real.exp (11 * ell ^ 4) * (X : ℝ) ^ (-(1 : ℝ))) := by
      calc
        C ^ 2 * (2 * δ * (X : ℝ) / (windowNX X : ℝ)) ≤
            Real.exp (10 * ell ^ 4) * (32 * δ * G) :=
          mul_le_mul hC hrate
            (div_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) hδ0) hXpos.le) hNpos.le)
            (Real.exp_nonneg _)
        _ ≤ Real.exp (10 * ell ^ 4) *
            (96 * G ^ 3 * (X : ℝ) ^ (-eulerProdLowerConst) +
              64 * G * ((X : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hδG (Real.exp_nonneg _)
        _ = 96 * (Real.exp (10 * ell ^ 4) * G ^ 3) *
              (X : ℝ) ^ (-eulerProdLowerConst) +
            64 * (Real.exp (10 * ell ^ 4) * G) * ((X : ℝ)⁻¹) := by ring
        _ ≤ 96 * (Real.exp (13 * ell ^ 4) *
              (X : ℝ) ^ (-eulerProdLowerConst)) +
            64 * (Real.exp (11 * ell ^ 4) * ((X : ℝ)⁻¹)) := by
          have hfirstBound :
              96 * (Real.exp (10 * ell ^ 4) * G ^ 3) *
                  (X : ℝ) ^ (-eulerProdLowerConst) ≤
                96 * (Real.exp (13 * ell ^ 4) *
                  (X : ℝ) ^ (-eulerProdLowerConst)) := by
            have hi := mul_le_mul_of_nonneg_right hexp13
              (Real.rpow_nonneg hXpos.le (-eulerProdLowerConst))
            have ho := mul_le_mul_of_nonneg_left hi
              (show (0 : ℝ) ≤ 96 by norm_num)
            simpa only [mul_assoc] using ho
          have hsecondBound :
              64 * (Real.exp (10 * ell ^ 4) * G) * ((X : ℝ)⁻¹) ≤
                64 * (Real.exp (11 * ell ^ 4) * ((X : ℝ)⁻¹)) := by
            have hi := mul_le_mul_of_nonneg_right hexp11
              (inv_nonneg.mpr hXpos.le)
            have ho := mul_le_mul_of_nonneg_left hi
              (show (0 : ℝ) ≤ 64 by norm_num)
            simpa only [mul_assoc] using ho
          exact add_le_add hfirstBound hsecondBound
        _ = 96 * (Real.exp (13 * ell ^ 4) *
              (X : ℝ) ^ (-eulerProdLowerConst)) +
            64 * (Real.exp (11 * ell ^ 4) * (X : ℝ) ^ (-(1 : ℝ))) := by
          rw [Real.rpow_neg_one]
    have hfinite' : coreMixtureJanossyCalibration κ d0 X ≤
        C ^ 2 * (2 * δ * (X : ℝ) / (windowNX X : ℝ)) := by
      simpa only [coreMixtureJanossyCalibration, C, δ, r] using hfinite
    exact hfinite'.trans (hboundRate.trans_eq (by simp only [ell, G]))
  refine squeeze_zero' ?_ hle hupper
  exact Eventually.of_forall fun X => by
    unfold coreMixtureJanossyCalibration
    exact sum_nonneg fun K _ => abs_nonneg _

end
end PrimeGapNormality.Prime.CoreCalibrationUnconditional

