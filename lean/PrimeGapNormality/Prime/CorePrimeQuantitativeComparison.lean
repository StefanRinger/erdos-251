import PrimeGapNormality.Prime.CoreLinearQuantitativeModel
import PrimeGapNormality.Prime.CorePrimePositiveWindow
import PrimeGapNormality.Prime.CoreMixtureCalibrationUnconditional
import PrimeGapNormality.Prime.CoreLinearMeanNormalization
import PrimeGapNormality.Prime.CoreLocalTailAtProfile
import PrimeGapNormality.Prime.CorePrimeGapTailUnconditional

/-!
# Quantitative positive comparison on the actual prime window

This is the finite-scale form of the paper's quantitative linear lemma.
The arithmetic discrepancy remains the literal
`corePrimeComparisonQuantity`; no convergence or rate for it is assumed.
The main/model Janossy error is instead bounded from the concrete
polynomial-saving cutoff calibration, and the infinite linear phase is
restored from the actual first-gap tail estimate.

All scale thresholds precede the bounded continuous test and its Lipschitz
constant.
-/

namespace PrimeGapNormality.Prime.CorePrimeQuantitativeComparison

open Filter Finset MeasureTheory
open CoreLinearQuantitativeModel
open scoped Topology NNReal Classical BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1200000

private theorem eventually_two_loglog_pow_six_le_log :
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
  have hh := (div_lt_iff₀ hlog).mp hratio
  linarith

private theorem eventually_log_ge_two :
    ∀ᶠ X : ℕ in atTop, (2 : ℝ) ≤ Real.log (X : ℝ) :=
  (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop 2)

/-! ## Polynomial-saving calibration at the `1/L` scale -/

/-- The actual unnormalized main/model Janossy calibration is smaller than
`1 / profileL`.  This is a consequence of its concrete power saving and
the actual unconditional lower bound for `windowNX`; it is not extracted
from the qualitative convergence theorem. -/
theorem eventually_coreMixtureJanossyCalibration_le_inv_profileL
    {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    ∀ᶠ X : ℕ in atTop,
      coreMixtureJanossyCalibration κ d0 X ≤
        (profileL κ X : ℝ)⁻¹ := by
  have hfirst : Tendsto (fun X : ℕ ↦
      96 * (Real.exp (14 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-eulerProdLowerConst))) atTop (𝓝 0) := by
    have h :=
      (tendsto_exp_loglog_pow_four_mul_rpow_neg
        (A := (14 : ℝ)) (ε := eulerProdLowerConst) (by norm_num)
        eulerProdLowerConst_pos).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_apply, mul_zero] using h.const_mul (96 : ℝ)
  have hsecond : Tendsto (fun X : ℕ ↦
      64 * (Real.exp (12 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    have h :=
      (tendsto_exp_loglog_pow_four_mul_rpow_neg
        (A := (12 : ℝ)) (ε := (1 : ℝ)) (by norm_num) (by norm_num)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_apply, mul_zero] using h.const_mul (64 : ℝ)
  have hupper : Tendsto (fun X : ℕ ↦
      96 * (Real.exp (14 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-eulerProdLowerConst)) +
      64 * (Real.exp (12 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    simpa using hfirst.add hsecond
  have hweighted : ∀ᶠ X : ℕ in atTop,
      (profileL κ X : ℝ) * coreMixtureJanossyCalibration κ d0 X ≤
        96 * (Real.exp (14 * Real.log (Real.log (X : ℝ)) ^ 4) *
          (X : ℝ) ^ (-eulerProdLowerConst)) +
        64 * (Real.exp (12 * Real.log (Real.log (X : ℝ)) ^ 4) *
          (X : ℝ) ^ (-(1 : ℝ))) := by
    filter_upwards [
      eventually_coreMixture_small_janossy_calibration_le hκ hd0,
      eventually_profileFits hκ hd0,
      CorePrimeDensity.eventually_X_div_windowNX_le,
      eventually_log_ge_two,
      eventually_two_loglog_pow_six_le_log] with
        X hfinite hfit hXN hG2 hloglog
    let r := profileR (profileL κ X) d0
    let G : ℝ := Real.log (X : ℝ)
    let ell : ℝ := Real.log G
    let δ := coreMixtureRelativeError κ d0 X
    let comb : ℝ :=
      (((r + 1) * ((ahlSmall_omega κ X).card + 1) ^ r : ℕ) : ℝ)
    have hXnat : 0 < X := lt_of_lt_of_le (by norm_num : 0 < 16) hfit.1
    have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hXnat
    have hGpos : 0 < G := by
      dsimp only [G]
      exact zero_lt_two.trans_le hG2
    have hell1 : 1 < ell := by
      dsimp only [ell, G]
      exact one_lt_log_log_of_sixteen_le hfit.1
    have hell0 : 0 ≤ ell := (zero_lt_one.trans hell1).le
    have hδ0 : 0 ≤ δ := by
      dsimp only [δ, coreMixtureRelativeError]
      positivity
    have hcomb : comb ^ 2 ≤ Real.exp (10 * ell ^ 4) := by
      dsimp only [comb, r, ell, G]
      exact small_combination_cost_le_exp hfit hG2
    have hNpos : 0 < (windowNX X : ℝ) :=
      Nat.cast_pos.mpr (windowNX_pos hXnat)
    have hr1 : ((r + 1 : ℕ) : ℝ) ≤ ell ^ 3 := by
      dsimp only [r, ell, G]
      simpa only [Nat.cast_add, Nat.cast_one] using hfit.2.2.1
    have hrsq : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ell ^ 6 := by
      calc
        ((r + 1 : ℕ) : ℝ) ^ 2 ≤ (ell ^ 3) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hr1 2
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
      exact _root_.add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrsq' (by norm_num))
          (Real.rpow_nonneg (Nat.cast_nonneg X) _)) le_rfl
    have hrate : 2 * δ * (X : ℝ) / (windowNX X : ℝ) ≤ 32 * δ * G := by
      rw [mul_div_assoc]
      calc
        2 * δ * ((X : ℝ) / (windowNX X : ℝ)) ≤ 2 * δ * (16 * G) :=
          mul_le_mul_of_nonneg_left hXN
            (mul_nonneg (by norm_num) hδ0)
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
    have hLr : profileL κ X ≤ r := by
      dsimp only [r]
      exact profileR_ge (profileL κ X) d0
    have hLell : (profileL κ X : ℝ) ≤ ell ^ 3 := by
      have hLr' : (profileL κ X : ℝ) ≤ (r : ℝ) :=
        Nat.cast_le.mpr hLr
      have hr1' : (r : ℝ) + 1 ≤ ell ^ 3 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hr1
      exact hLr'.trans (by linarith)
    have hell3le4 : ell ^ 3 ≤ ell ^ 4 :=
      pow_le_pow_right₀ hell1.le (by omega : 3 ≤ 4)
    have hLexp : (profileL κ X : ℝ) ≤ Real.exp (ell ^ 4) :=
      hLell.trans (hell3le4.trans
        ((le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
          (Real.add_one_le_exp (ell ^ 4))))
    have hcalFinite : coreMixtureJanossyCalibration κ d0 X ≤
        comb ^ 2 * (2 * δ * (X : ℝ) / (windowNX X : ℝ)) := by
      simpa only [coreMixtureJanossyCalibration, comb, δ, r] using hfinite
    have hcalUpper : coreMixtureJanossyCalibration κ d0 X ≤
        96 * (Real.exp (13 * ell ^ 4) *
          (X : ℝ) ^ (-eulerProdLowerConst)) +
        64 * (Real.exp (11 * ell ^ 4) * (X : ℝ) ^ (-(1 : ℝ))) := by
      have hraw : comb ^ 2 *
          (2 * δ * (X : ℝ) / (windowNX X : ℝ)) ≤
          Real.exp (10 * ell ^ 4) *
            (96 * G ^ 3 * (X : ℝ) ^ (-eulerProdLowerConst) +
              64 * G * ((X : ℝ)⁻¹)) := by
        exact (mul_le_mul hcomb hrate
          (div_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hδ0) hXpos.le) hNpos.le)
          (Real.exp_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hδG (Real.exp_nonneg _))
      have hexp13 : Real.exp (10 * ell ^ 4) * G ^ 3 ≤
          Real.exp (13 * ell ^ 4) := by
        calc
          _ ≤ Real.exp (10 * ell ^ 4) * Real.exp (3 * ell ^ 4) :=
            mul_le_mul_of_nonneg_left hG3 (Real.exp_nonneg _)
          _ = Real.exp (13 * ell ^ 4) := by
            rw [← Real.exp_add]
            ring_nf
      have hexp11 : Real.exp (10 * ell ^ 4) * G ≤
          Real.exp (11 * ell ^ 4) := by
        calc
          _ ≤ Real.exp (10 * ell ^ 4) * Real.exp (ell ^ 4) :=
            mul_le_mul_of_nonneg_left hGle (Real.exp_nonneg _)
          _ = Real.exp (11 * ell ^ 4) := by
            rw [← Real.exp_add]
            ring_nf
      calc
        coreMixtureJanossyCalibration κ d0 X ≤
            comb ^ 2 * (2 * δ * (X : ℝ) / (windowNX X : ℝ)) := hcalFinite
        _ ≤ Real.exp (10 * ell ^ 4) *
            (96 * G ^ 3 * (X : ℝ) ^ (-eulerProdLowerConst) +
              64 * G * ((X : ℝ)⁻¹)) := hraw
        _ = 96 * (Real.exp (10 * ell ^ 4) * G ^ 3) *
              (X : ℝ) ^ (-eulerProdLowerConst) +
            64 * (Real.exp (10 * ell ^ 4) * G) * ((X : ℝ)⁻¹) := by ring
        _ ≤ 96 * (Real.exp (13 * ell ^ 4) *
              (X : ℝ) ^ (-eulerProdLowerConst)) +
            64 * (Real.exp (11 * ell ^ 4) * ((X : ℝ)⁻¹)) := by
          simpa only [mul_assoc] using _root_.add_le_add
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hexp13
                (Real.rpow_nonneg hXpos.le (-eulerProdLowerConst)))
              (show (0 : ℝ) ≤ 96 by norm_num))
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hexp11
                (inv_nonneg.mpr hXpos.le))
              (show (0 : ℝ) ≤ 64 by norm_num))
        _ = 96 * (Real.exp (13 * ell ^ 4) *
              (X : ℝ) ^ (-eulerProdLowerConst)) +
            64 * (Real.exp (11 * ell ^ 4) * (X : ℝ) ^ (-(1 : ℝ))) := by
          rw [Real.rpow_neg_one]
    have hcal0 : 0 ≤ coreMixtureJanossyCalibration κ d0 X := by
      unfold coreMixtureJanossyCalibration
      exact sum_nonneg fun K _ ↦ abs_nonneg _
    have hmul := mul_le_mul hLexp hcalUpper hcal0 (Real.exp_nonneg _)
    have hfirstBound : Real.exp (ell ^ 4) *
        (96 * (Real.exp (13 * ell ^ 4) *
          (X : ℝ) ^ (-eulerProdLowerConst))) =
        96 * (Real.exp (14 * ell ^ 4) *
          (X : ℝ) ^ (-eulerProdLowerConst)) := by
      rw [show 14 * ell ^ 4 = ell ^ 4 + 13 * ell ^ 4 by ring, Real.exp_add]
      ring
    have hsecondBound : Real.exp (ell ^ 4) *
        (64 * (Real.exp (11 * ell ^ 4) * (X : ℝ) ^ (-(1 : ℝ)))) =
        64 * (Real.exp (12 * ell ^ 4) * (X : ℝ) ^ (-(1 : ℝ))) := by
      rw [show 12 * ell ^ 4 = ell ^ 4 + 11 * ell ^ 4 by ring, Real.exp_add]
      ring
    calc
      (profileL κ X : ℝ) * coreMixtureJanossyCalibration κ d0 X ≤
          Real.exp (ell ^ 4) *
            (96 * (Real.exp (13 * ell ^ 4) *
                (X : ℝ) ^ (-eulerProdLowerConst)) +
              64 * (Real.exp (11 * ell ^ 4) * (X : ℝ) ^ (-(1 : ℝ)))) := hmul
      _ = 96 * (Real.exp (14 * ell ^ 4) *
            (X : ℝ) ^ (-eulerProdLowerConst)) +
          64 * (Real.exp (12 * ell ^ 4) * (X : ℝ) ^ (-(1 : ℝ))) := by
        rw [mul_add, hfirstBound, hsecondBound]
      _ = _ := by simp only [ell, G]
  have hprod : Tendsto (fun X : ℕ ↦
      (profileL κ X : ℝ) * coreMixtureJanossyCalibration κ d0 X)
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ hweighted hupper
    exact Eventually.of_forall fun X ↦ mul_nonneg (Nat.cast_nonneg _)
      (by unfold coreMixtureJanossyCalibration
          exact sum_nonneg fun K _ ↦ abs_nonneg _)
  filter_upwards [hprod.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_one_le_profileL hκ] with X hprodOne hL
  have hLpos : (0 : ℝ) < profileL κ X := Nat.cast_pos.mpr (by omega)
  rw [← one_div]
  apply (le_div_iff₀ hLpos).2
  simpa only [mul_comm] using hprodOne

/-! ## Quantitative restoration of the infinite linear phase -/

private theorem one_le_log_nat_of_three_le {X : ℕ} (hX : 3 ≤ X) :
    (1 : ℝ) ≤ Real.log X := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
    rwa [Real.log_exp] at h
  exact hlog3.trans
    (Real.log_le_log (by positivity : (0 : ℝ) < 3) (by exact_mod_cast hX))

private theorem log_six_add_one_le_three_log_three :
    Real.log 6 + 1 ≤ 3 * Real.log 3 := by
  have h1 : (1 : ℝ) ≤ Real.log 3 := by
    exact (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).2
      Real.exp_one_lt_three.le
  have h18 : Real.log 6 + 1 ≤ Real.log 6 + Real.log 3 :=
    _root_.add_le_add le_rfl h1
  have hmul : Real.log 6 + Real.log 3 = Real.log (18 : ℝ) := by
    have h := Real.log_mul (by norm_num : (6 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0)
    have h18 : (6 : ℝ) * 3 = 18 := by norm_num
    rw [h18] at h
    exact h.symm
  have h18_27 : Real.log (18 : ℝ) ≤ Real.log (27 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have h27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    have hp : (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [hp, Real.log_pow]
    norm_cast
  exact (h18.trans_eq hmul).trans (h18_27.trans_eq h27)

private theorem eventually_profileL_add_one_le_X_div_log
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      (profileL κ X : ℝ) + 1 ≤ (X : ℝ) / Real.log X := by
  have hlogSq : Tendsto (fun X : ℕ ↦
      Real.log (X : ℝ) ^ 2 / (X : ℝ)) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 2 (by norm_num)
    have hn := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [one_mul, add_zero, Function.comp_def] using hn
  have hlog : Tendsto (fun X : ℕ ↦
      Real.log (X : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 1 (by norm_num)
    have hn := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using hn
  have hsum : Tendsto (fun X : ℕ ↦
      (Real.log (X : ℝ) + 1) * Real.log (X : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
    have hh := hlogSq.add hlog
    simpa only [add_zero] using hh.congr' (Eventually.of_forall fun X ↦ by ring)
  filter_upwards [crtLogSLogX_eventually_profileL_le_log hκ,
    hsum.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 3] with X hL hsmall hX
  have hx : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hlogX : 0 < Real.log X :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hmul : ((profileL κ X : ℝ) + 1) * Real.log X < (X : ℝ) := by
    have hleft := mul_le_mul_of_nonneg_right
      (_root_.add_le_add hL (le_rfl : (1 : ℝ) ≤ 1)) hlogX.le
    have hright : (Real.log (X : ℝ) + 1) * Real.log (X : ℝ) < X :=
      (div_lt_one hx).mp hsmall
    exact hleft.trans_lt hright
  exact ((le_div_iff₀ hlogX).2 hmul.le)

/-- The actual first-gap tail remains `O_B(G)` when shifted by the supplied
paper rank `profileL κ X`.  The proof uses the finite Chebyshev tail bound,
not an assumed uniform-tail statement. -/
theorem eventually_primeGapTail_avg_profileL
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      0 < (seqWindow nthPrime X).card ∧
        windowAvgReal (seqWindow nthPrime X)
            (fun n ↦ seqGapTail (B : ℝ) nthPrime
              (n + profileL κ X)) ≤
          CorePrimeGapTailUnconditional.gapTailCoeff (B : ℝ) * windowG X := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  filter_upwards [CorePrimeDensity.eventually_primeCounting_two_mul_le,
    eventually_profileL_add_one_le_X_div_log hκ,
    CorePrimeDensity.eventually_seqWindow_card_ge,
    eventually_ge_atTop 3] with X hπbd hLle hcardge hX
  have hm : 0 < (seqWindow nthPrime X).card :=
    card_seqWindow_nthPrime_pos (by omega)
  refine ⟨hm, ?_⟩
  have hx : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hx0 : (0 : ℝ) < X := zero_lt_one.trans hx
  have hlogX : 0 < Real.log X := Real.log_pos hx
  have hlogge1 : (1 : ℝ) ≤ Real.log X := one_le_log_nat_of_three_le hX
  have hG : windowG X = Real.log X := windowG_eq_log hX
  let L := profileL κ X
  let N : ℕ := Nat.primeCounting (2 * X) + L
  have htail : windowAvgReal (seqWindow nthPrime X)
        (fun n ↦ seqGapTail (B : ℝ) nthPrime (n + L)) ≤
      posMassChebyshevCoeff (B : ℝ) * ((N + 1 : ℕ) : ℝ) *
          (Real.log ((N + 2 : ℕ) : ℝ) + 1) /
        ((seqWindow nthPrime X).card : ℝ) := by
    simpa [seqWindowMul_two, N] using
      (conditionT_seqWindowMul_nthPrime_chebyshev_log hBr 2 X L
        (by simpa [seqWindowMul_two] using hm))
  have hN1 : ((N + 1 : ℕ) : ℝ) =
      (Nat.primeCounting (2 * X) : ℝ) + (L : ℝ) + 1 := by
    dsimp only [N]
    rw [Nat.cast_add_one (Nat.primeCounting (2 * X) + L), Nat.cast_add]
  have hNbd : ((N + 1 : ℕ) : ℝ) ≤ 5 * (X : ℝ) / Real.log X := by
    have hadd := _root_.add_le_add hπbd
      (by simpa only [L] using hLle)
    rw [hN1]
    calc
      (Nat.primeCounting (2 * X) : ℝ) + (L : ℝ) + 1 =
          (Nat.primeCounting (2 * X) : ℝ) + ((L : ℝ) + 1) := by ring
      _ ≤ 4 * (X : ℝ) / Real.log X + (X : ℝ) / Real.log X := hadd
      _ = 5 * (X : ℝ) / Real.log X := by ring
  have hN2le : ((N + 2 : ℕ) : ℝ) ≤ 6 * (X : ℝ) := by
    have h5 : ((N + 1 : ℕ) : ℝ) ≤ 5 * (X : ℝ) :=
      hNbd.trans (div_le_self
        (mul_nonneg (by norm_num) hx0.le) hlogge1)
    rw [show ((N + 2 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) + 1 by norm_cast]
    linarith
  have hlogN : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤
      4 * Real.log X := by
    have hNpos : (0 : ℝ) < (N + 2 : ℕ) := by positivity
    have hlog6 : Real.log ((N + 2 : ℕ) : ℝ) ≤
        Real.log (6 * (X : ℝ)) := Real.log_le_log hNpos hN2le
    have hlog6X : Real.log (6 * (X : ℝ)) =
        Real.log 6 + Real.log X := Real.log_mul (by norm_num) hx0.ne'
    have hcomb : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤
        Real.log 6 + Real.log X + 1 :=
      _root_.add_le_add (hlog6.trans_eq hlog6X) le_rfl
    have h3 : 3 * Real.log 3 ≤ 3 * Real.log X :=
      mul_le_mul_of_nonneg_left
        (Real.log_le_log (by norm_num) (by exact_mod_cast hX)) (by norm_num)
    calc
      Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤
          Real.log 6 + Real.log X + 1 := hcomb
      _ = (Real.log 6 + 1) + Real.log X := by ring
      _ ≤ 3 * Real.log 3 + Real.log X :=
        _root_.add_le_add log_six_add_one_le_three_log_three le_rfl
      _ ≤ 3 * Real.log X + Real.log X := _root_.add_le_add h3 le_rfl
      _ = 4 * Real.log X := by ring
  have hprod : ((N + 1 : ℕ) : ℝ) *
      (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤ 20 * (X : ℝ) := by
    have hh := mul_le_mul hNbd hlogN
      (_root_.add_nonneg (Real.log_natCast_nonneg _) (by norm_num))
      (div_nonneg (mul_nonneg (by norm_num) hx0.le) hlogX.le)
    exact hh.trans_eq (by field_simp [hlogX.ne'] <;> ring)
  have hnum : posMassChebyshevCoeff (B : ℝ) * ((N + 1 : ℕ) : ℝ) *
      (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤
      posMassChebyshevCoeff (B : ℝ) * 20 * (X : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hprod
      (posMassChebyshevCoeff_nonneg hBr)
    simpa only [mul_assoc] using hh
  have hmR : (0 : ℝ) < (seqWindow nthPrime X).card := by exact_mod_cast hm
  have hdenPos : 0 < CoreDyadicPrimeCounting.dyadicCountConstant *
      ((X : ℝ) / Real.log X) :=
    mul_pos CoreDyadicPrimeCounting.dyadicCountConstant_pos
      (div_pos hx0 hlogX)
  have havg : windowAvgReal (seqWindow nthPrime X)
      (fun n ↦ seqGapTail (B : ℝ) nthPrime (n + L)) ≤
      posMassChebyshevCoeff (B : ℝ) * 20 * (X : ℝ) /
        ((seqWindow nthPrime X).card : ℝ) :=
    htail.trans (div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _))
  have hinv : 1 / ((seqWindow nthPrime X).card : ℝ) ≤
      1 / (CoreDyadicPrimeCounting.dyadicCountConstant *
        ((X : ℝ) / Real.log X)) :=
    one_div_le_one_div_of_le hdenPos hcardge
  have hquot : posMassChebyshevCoeff (B : ℝ) * 20 * (X : ℝ) /
        ((seqWindow nthPrime X).card : ℝ) ≤
      posMassChebyshevCoeff (B : ℝ) * 20 * (X : ℝ) *
        (1 / (CoreDyadicPrimeCounting.dyadicCountConstant *
          ((X : ℝ) / Real.log X))) := by
    have hcoef0 : 0 ≤ posMassChebyshevCoeff (B : ℝ) * 20 * (X : ℝ) :=
      mul_nonneg (mul_nonneg (posMassChebyshevCoeff_nonneg hBr) (by norm_num))
        hx0.le
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using hinv) hcoef0
  have hsimp : posMassChebyshevCoeff (B : ℝ) * 20 * (X : ℝ) *
      (1 / (CoreDyadicPrimeCounting.dyadicCountConstant *
        ((X : ℝ) / Real.log X))) =
      CorePrimeGapTailUnconditional.gapTailCoeff (B : ℝ) * Real.log X := by
    unfold CorePrimeGapTailUnconditional.gapTailCoeff
    field_simp [hx0.ne', hlogX.ne',
      CoreDyadicPrimeCounting.dyadicCountConstant_pos.ne']
  simpa only [L, hG] using havg.trans (hquot.trans_eq hsimp)

/-- Uniform finite bound for restoring the infinite linear phase at the
unchanged supplied profile. -/
theorem eventually_corePrime_positiveTail_le
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      ∀ (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0),
        LipschitzWith K f →
        windowAvgReal (seqWindow nthPrime X) (fun n ↦
          |f (corePrimeGapCircleOrbit B n) -
            f (seqGapPolyTailTrunc nthPrime (fun _ ↦ Polynomial.X) B
              (profileL κ X) n : AddCircle (1 : ℝ))|) ≤
          CorePrimeGapTailUnconditional.gapTailCoeff (B : ℝ) *
            windowG X * ((B : ℝ) ^ profileL κ X)⁻¹ * (K : ℝ) := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  filter_upwards [eventually_primeGapTail_avg_profileL B hB hκ]
      with X htail
  intro f K hK
  have hpoint : ∀ n ∈ seqWindow nthPrime X,
      |f (corePrimeGapCircleOrbit B n) -
          f (seqGapPolyTailTrunc nthPrime (fun _ ↦ Polynomial.X) B
            (profileL κ X) n : AddCircle (1 : ℝ))| ≤
        (K : ℝ) * scaledGapTail (B : ℝ)
          (fun j ↦ (seqGap nthPrime j : ℝ)) n (profileL κ X) := by
    intro n _
    simpa only [corePrimeGapCircleOrbit] using
      corePositiveTest_tail_le hB hBr le_rfl
        (nthPrime_div_pow_summable hBr) f hK n (profileL κ X)
  have hsum := sum_le_sum hpoint
  have havg : windowAvgReal (seqWindow nthPrime X) (fun n ↦
        |f (corePrimeGapCircleOrbit B n) -
          f (seqGapPolyTailTrunc nthPrime (fun _ ↦ Polynomial.X) B
            (profileL κ X) n : AddCircle (1 : ℝ))|) ≤
      (K : ℝ) * windowAvgReal (seqWindow nthPrime X) (fun n ↦
        scaledGapTail (B : ℝ) (fun j ↦ (seqGap nthPrime j : ℝ)) n
          (profileL κ X)) := by
    unfold windowAvgReal
    rw [← mul_div_assoc, mul_sum]
    exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
  rw [windowAvgReal_scaledGapTail_eq] at havg
  have hmul := mul_le_mul_of_nonneg_left htail.2
    (mul_nonneg K.coe_nonneg
      (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg B) (profileL κ X))))
  exact havg.trans (by
    rw [← mul_assoc] at hmul
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul)

/-- The shrinking-mesh norm error is absorbed by the already present
`1 / profileL` count scale. -/
theorem eventually_windowG_rpow_neg_half_le_inv_profileL
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      windowG X ^ (-(1 / 2 : ℝ)) ≤ (profileL κ X : ℝ)⁻¹ := by
  have hlogSqrt : Tendsto (fun G : ℝ ↦
      Real.log G / Real.sqrt G) atTop (𝓝 0) := by
    have h :=
      (isLittleO_log_rpow_atTop
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with G hG
    rw [Real.sqrt_eq_rpow]
  have hinvSqrt : Tendsto (fun G : ℝ ↦ (Real.sqrt G)⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hupperLim : Tendsto (fun X : ℕ ↦
      (2 * κ * Real.log (windowG X) + 2) /
        Real.sqrt (windowG X)) atTop (𝓝 0) := by
    have h₁ := (hlogSqrt.comp tendsto_windowG_atTop).const_mul (2 * κ)
    have h₂ := (hinvSqrt.comp tendsto_windowG_atTop).const_mul (2 : ℝ)
    have h := h₁.add h₂
    simpa only [mul_zero, add_zero, div_eq_mul_inv, Function.comp_def] using
      h.congr' (Eventually.of_forall fun X ↦ by
        dsimp only [Function.comp_def]
        ring)
  filter_upwards [hupperLim.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_one_le_profileL hκ,
    tendsto_windowG_atTop.eventually_gt_atTop 1] with X hsmall hL hG
  have hlogG : 0 ≤ Real.log (windowG X) := Real.log_nonneg hG.le
  have harg : 0 ≤ κ * Real.log (windowG X) := mul_nonneg hκ.le hlogG
  have hs0 := Real.sqrt_nonneg (κ * Real.log (windowG X))
  have hs2 := Real.sq_sqrt harg
  have hs : Real.sqrt (κ * Real.log (windowG X)) ≤
      κ * Real.log (windowG X) + 1 := by
    nlinarith [sq_nonneg (Real.sqrt (κ * Real.log (windowG X)) - 1)]
  have hprofile : (profileL κ X : ℝ) ≤
      κ * Real.log (windowG X) +
        Real.sqrt (κ * Real.log (windowG X)) + 1 := by
    set a := κ * Real.log (windowG X) +
      Real.sqrt (κ * Real.log (windowG X))
    have ha : 0 ≤ a := _root_.add_nonneg harg (Real.sqrt_nonneg _)
    exact (Nat.ceil_lt_add_one (R := ℝ) ha).le
  have hLbound : (profileL κ X : ℝ) ≤
      2 * κ * Real.log (windowG X) + 2 := by linarith
  have hsqrt : 0 < Real.sqrt (windowG X) := Real.sqrt_pos.mpr
    (zero_lt_one.trans hG)
  have hprodOne : (profileL κ X : ℝ) /
      Real.sqrt (windowG X) ≤ 1 := by
    exact (div_le_div_of_nonneg_right hLbound hsqrt.le).trans hsmall.le
  have hLpos : (0 : ℝ) < profileL κ X := Nat.cast_pos.mpr (by omega)
  have htarget : (Real.sqrt (windowG X))⁻¹ ≤
      1 / (profileL κ X : ℝ) := by
    apply (le_div_iff₀ hLpos).2
    have hh := hprodOne
    rw [div_eq_mul_inv] at hh
    simpa only [mul_comm] using hh
  rw [Real.rpow_neg (zero_lt_one.trans hG).le, ← Real.sqrt_eq_rpow]
  simpa only [one_div] using htarget

/-! ## Final finite positive comparison -/

private theorem mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos'
  · intro t _
    exact mixWeightV_nonneg t
  · refine ⟨2 * X, ?_, ?_⟩
    · simp only [mixScale, mem_Ioc]
      omega
    · exact eulerProdNat_pos (sieveCutoff ((2 * X : ℕ) : ℝ))

/-- Nonnegativity of the literal discrepancy for every multiplier `c`.
The proof uses only that the stopped Janossy truncation is dominated by the
actual short-shape mass; the reference transform may be signed. -/
theorem corePrimeComparisonQuantity_nonneg_general
    {X L r : ℕ} {Ω : Finset ℕ} {c : ℝ}
    (hN : 0 < windowNX X) (hL : 1 ≤ L) (hr : L ≤ r)
    (hpar : Odd (r - L)) :
    0 ≤ corePrimeComparisonQuantity X Ω L r c := by
  let μ := coreActualPatternMass X Ω
  have hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U := fun U _ ↦
    coreActualPatternMass_nonneg X Ω U
  have hJ :
      (∑ K ∈ Ω.powerset.filter (fun K ↦ K.card = L),
        Stopped.janossyTrunc Ω μ L r K) ≤
      ∑ K ∈ Ω.powerset.filter (fun K ↦ K.card = L),
        Stopped.shortShapeMass Ω μ L K := by
    exact sum_le_sum fun K hK ↦
      Stopped.janossyTrunc_le_shortShapeMass hL hr hpar
        (mem_filter.mp hK).2 hμ
  have hfail : 0 ≤ Stopped.failureMass Ω μ L := by
    unfold Stopped.failureMass
    exact sum_nonneg fun U hU ↦ hμ U (mem_filter.mp hU).1
  have hmass := Stopped.shortShapeMass_add_failureMass
    (Ω := Ω) (μ := μ) (L := L)
  have hfirst : 0 ≤
      (∑ U ∈ Ω.powerset, μ U) -
        ∑ K ∈ Ω.powerset.filter (fun K ↦ K.card = L),
          Stopped.janossyTrunc Ω μ L r K := by
    linarith
  have hmax : 0 ≤
      ∑ K ∈ Ω.powerset.filter (fun K ↦ K.card = L),
        max (Stopped.janossyTrunc Ω μ L r K -
          c * (coreJanossyTransform Ω (rootedMainTerm X) L r K /
            (windowNX X : ℝ))) 0 :=
    sum_nonneg fun K _ ↦ le_max_right _ _
  rw [← corePrimeComparisonQuantity_eq_budget hN Ω L r c]
  unfold Stopped.stoppedPositiveBudgetAgainst
  exact _root_.add_nonneg hfirst hmax

/-- Quantitative prime-window positive comparison.  The arithmetic
quantity is left completely visible.  All other errors have their actual
finite rates, and the eventual threshold is uniform over `f` and `K`. -/
theorem corePrimeGap_positive_window_quantitative
    (B : ℕ) (hB : 2 ≤ B) {κ c : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hc : 1 ≤ c) :
    ∃ Cvol Cerr : ℝ, 0 ≤ Cvol ∧ 0 ≤ Cerr ∧
      ∀ᶠ X : ℕ in atTop,
        ∀ (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0),
          LipschitzWith K f → (∀ x, 0 ≤ f x) →
          windowAvgReal (seqWindow nthPrime X)
              (fun n ↦ f (corePrimeGapCircleOrbit B n)) ≤
            Cvol * c * (∫ x : AddCircle (1 : ℝ), f x) +
              Cerr *
                ((corePrimeComparisonQuantity X (ahlSmall_omega κ X)
                    (profileL κ X) (profileR (profileL κ X) 20) c +
                    (profileL κ X : ℝ)⁻¹) * ‖f‖ +
                  (windowG X ^ (-(1 / 2 : ℝ)) +
                    windowG X * ((B : ℝ) ^ profileL κ X)⁻¹) * (K : ℝ)) := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hκpos : 0 < κ :=
    (div_pos zero_lt_one (Real.log_pos hBr)).trans_le hκ
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  obtain ⟨Avol, Aerr, hAvol, hAerr, hmodel⟩ :=
    coreLinearFiniteRootMean_quantitative_bound B hB hκ
  let Cvol : ℝ := 16 * Avol
  let tailC : ℝ :=
    CorePrimeGapTailUnconditional.gapTailCoeff (B : ℝ)
  let Cerr : ℝ := 32 * c * Aerr + c + tailC + 1
  have htailC : 0 ≤ tailC := by
    dsimp only [tailC]
    exact CorePrimeGapTailUnconditional.gapTailCoeff_nonneg hBr
  have hCvol : 0 ≤ Cvol := by
    dsimp only [Cvol]
    exact mul_nonneg (by norm_num) hAvol
  have hCerr : 0 ≤ Cerr := by
    dsimp only [Cerr]
    positivity
  refine ⟨Cvol, Cerr, hCvol, hCerr, ?_⟩
  filter_upwards [hmodel,
    eventually_coreMixtureJanossyCalibration_le_inv_profileL hκpos
      (by norm_num : (0 : ℝ) < 20),
    CorePrimeDensity.eventually_mixZeta_le_sixteen,
    eventually_corePrime_positiveTail_le B hB hκpos,
    eventually_windowG_rpow_neg_half_le_inv_profileL hκpos,
    eventually_one_le_profileL hκpos,
    eventually_ge_atTop 1] with
      X hmodelX hcal hζ htail heL hL hX
  intro f K hK hf0
  let L := profileL κ X
  let S := ahlSmall_window κ X
  let r := profileR L 20
  let q : ℝ := (L : ℝ)⁻¹
  let e : ℝ := windowG X ^ (-(1 / 2 : ℝ))
  let t : ℝ := windowG X * ((B : ℝ) ^ L)⁻¹
  let D : ℝ := corePrimeComparisonQuantity X (ahlSmall_omega κ X) L r c
  let C : ℝ := ‖f‖
  have hN : 0 < windowNX X := windowNX_pos (by omega : 0 < X)
  have hZ : 0 < mixZ X := mixZ_pos hX
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have he0 : 0 ≤ e := by
    dsimp only [e]
    exact Real.rpow_nonneg (zero_le_one.trans (crtWindowG_one_le X)) _
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    exact mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans
      (crtWindowG_one_le X))
      (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg B) _))
  have hD0 : 0 ≤ D := by
    dsimp only [D, L, r]
    exact corePrimeComparisonQuantity_nonneg_general hN hL
      (crtMixProf_le_at κ 20 X) (crtMixProf_odd_at κ 20 X)
  have hC0 : 0 ≤ C := by dsimp only [C]; exact norm_nonneg _
  by_cases hCeq : C = 0
  · have hfzero : f = 0 := norm_eq_zero.mp (by simpa only [C] using hCeq)
    subst f
    have hright : 0 ≤ Cvol * c * 0 +
        Cerr * ((D + q) * 0 + (e + t) * (K : ℝ)) := by
      simp only [mul_zero, add_zero, zero_add]
      exact mul_nonneg hCerr
        (mul_nonneg (_root_.add_nonneg he0 ht0) K.coe_nonneg)
    simpa [windowAvgReal, D, q, e, t, L, C] using hright
  · have hCpos : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hCeq)
    have hfC : ∀ x, f x ≤ C := fun x ↦ by
      dsimp only [C]
      exact f.apply_le_norm x
    have hfull := corePrime_full_positive_window_le_comparisonQuantity
      (B := B) (X := X) (S := S) (L := L) (r := r)
      (ν := finiteRootMixUnnorm X S) (c := c) (C := C)
      hN hL (crtMixProf_le_at κ 20 X) (crtMixProf_odd_at κ 20 X)
      hc0 hCpos
      (fun U _ ↦ crtMixUnnorm_finiteRootMixUnnorm_nonneg X S U)
      f hf0 hfC
    have hmNorm : coreLinearStoppedMean B S L (finiteRootMix X S) f ≤
        Avol * (∫ x : AddCircle (1 : ℝ), f x) +
          Aerr * ((q + e) * C + e * (K : ℝ)) := by
      simpa only [coreLinearFiniteRootMean, coreLinearStoppedMean,
        offsetWindow, S, L, q, e, C] using hmodelX f K hK hf0
    have hmain0 : 0 ≤ Avol * (∫ x : AddCircle (1 : ℝ), f x) +
        Aerr * ((q + e) * C + e * (K : ℝ)) := by
      exact _root_.add_nonneg
        (mul_nonneg hAvol (integral_nonneg hf0))
        (mul_nonneg hAerr (_root_.add_nonneg
          (mul_nonneg (_root_.add_nonneg hq0 he0) hC0)
          (mul_nonneg he0 K.coe_nonneg)))
    have hmUnnorm : coreLinearStoppedMean B S L
        (finiteRootMixUnnorm X S) f ≤
      16 * (Avol * (∫ x : AddCircle (1 : ℝ), f x) +
        Aerr * ((q + e) * C + e * (K : ℝ))) := by
      rw [coreLinearStoppedMean_finiteRootMixUnnorm_eq_mixZeta_mul
        hN hZ]
      exact (mul_le_mul_of_nonneg_left hmNorm
        (crtMixUnnormRem_mixZeta_nonneg X)).trans
          (mul_le_mul_of_nonneg_right hζ hmain0)
    have hfull' : windowAvgReal (seqWindow nthPrime X)
          (fun n ↦ f (corePrimeGapCircleOrbit B n)) ≤
        c * coreLinearStoppedMean B S L (finiteRootMixUnnorm X S) f +
          C * (D + c * coreMixtureJanossyCalibration κ 20 X) +
          windowAvgReal (seqWindow nthPrime X) (fun n ↦
            |f (corePrimeGapCircleOrbit B n) -
              f (seqGapPolyTailTrunc nthPrime (fun _ ↦ Polynomial.X) B L n :
                AddCircle (1 : ℝ))|) := by
      simpa only [coreLinearStoppedMean, coreMixtureJanossyCalibration,
        ahlSmall_omega, offsetWindow, S, L, r, D, C, add_assoc] using hfull
    have hmodelScaled := mul_le_mul_of_nonneg_left hmUnnorm hc0
    have hcalScaled : C * (D + c * coreMixtureJanossyCalibration κ 20 X) ≤
        C * (D + c * q) := by
      exact mul_le_mul_of_nonneg_left
        (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (by simpa only [q, L] using hcal) hc0)) hC0
    have htail' : windowAvgReal (seqWindow nthPrime X) (fun n ↦
          |f (corePrimeGapCircleOrbit B n) -
            f (seqGapPolyTailTrunc nthPrime (fun _ ↦ Polynomial.X) B L n :
              AddCircle (1 : ℝ))|) ≤ tailC * t * (K : ℝ) := by
      simpa only [tailC, t, L, mul_assoc] using htail f K hK
    have heq : e ≤ q := by simpa only [e, q, L] using heL
    have hraw := hfull'.trans (_root_.add_le_add
      (_root_.add_le_add hmodelScaled hcalScaled) htail')
    have hcollect :
        c * (16 * (Avol * (∫ x : AddCircle (1 : ℝ), f x) +
            Aerr * ((q + e) * C + e * (K : ℝ)))) +
          C * (D + c * q) + tailC * t * (K : ℝ) ≤
        Cvol * c * (∫ x : AddCircle (1 : ℝ), f x) +
          Cerr * ((D + q) * C + (e + t) * (K : ℝ)) := by
      have hI0 : 0 ≤ ∫ x : AddCircle (1 : ℝ), f x := integral_nonneg hf0
      dsimp only [Cvol, Cerr]
      rw [← sub_nonneg]
      have hidentity :
          16 * Avol * c * (∫ x : AddCircle (1 : ℝ), f x) +
              (32 * c * Aerr + c + tailC + 1) *
                ((D + q) * C + (e + t) * (K : ℝ)) -
            (c * (16 * (Avol * (∫ x : AddCircle (1 : ℝ), f x) +
                Aerr * ((q + e) * C + e * (K : ℝ)))) +
              C * (D + c * q) + tailC * t * (K : ℝ)) =
            16 * c * Aerr * (q - e) * C +
              (32 * c * Aerr + c + tailC) * D * C +
              (tailC + 1) * q * C +
              (16 * c * Aerr + c + tailC + 1) * e * (K : ℝ) +
              (32 * c * Aerr + c + 1) * t * (K : ℝ) := by
        ring
      rw [hidentity]
      have hqe : 0 ≤ q - e := sub_nonneg.mpr heq
      positivity
    exact hraw.trans hcollect

end

end PrimeGapNormality.Prime.CorePrimeQuantitativeComparison
