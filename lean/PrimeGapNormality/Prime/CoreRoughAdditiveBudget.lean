import PrimeGapNormality.Prime.CoreRoughSieveBudgetLimits
import PrimeGapNormality.Prime.CoreRoughSubpower

/-!
# Decay of the actual aggregated additive sieve envelope

The profile bounds are derived from the literal threshold and synthetic
model. The final comparison is exponential in a quadratic polynomial in
log log X, versus the remaining negative multiple of log X.
-/

namespace PrimeGapNormality.Prime.CoreRoughAdditiveBudget

open Filter CoreRoughThreshold CoreRoughSyntheticScale CoreRoughProfileError
open CoreRoughSieveBudget CoreRoughSieveBudgetLimits
open scoped Topology
noncomputable section

set_option maxHeartbeats 1200000

def rankConstant (κ : ℝ) : ℝ := 256 * κ

def envelope (κ C J : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  (Real.log (X : ℝ)) ^ J *
    2 ^ (profileRank κ Ψ X + 1) *
    (1 + (roughProfileS κ (zPsi Ψ X) : ℝ)) ^ (profileRank κ Ψ X + 1) *
    Real.exp (C * ((profileRank κ Ψ X + 1 : ℕ) : ℝ)) *
    (cubeRootLevel X : ℝ) * (1 + Real.log (cubeRootLevel X : ℝ)) ^ profileRank κ Ψ X *
    roughGapScale (zPsi Ψ X) / (X : ℝ)

/-- The actual growing rank is logarithmic in log X. -/
theorem eventually_rank_le_loglog {Ψ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSlopeBudget Ψ (1000000 * κ)) :
    ∀ᶠ X : ℕ in atTop,
      ((profileRank κ Ψ X + 1 : ℕ) : ℝ) ≤ rankConstant κ * Real.log (Real.log (X : ℝ)) := by
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_profileRank_bound h.2.1 hκ,
    ht.eventually (CoreRoughSubpower.eventually_psi_le_mul h (by norm_num : (0 : ℝ) < 1)),
    ht.eventually_ge_atTop 3, (h.2.1.comp ht).eventually_ge_atTop 1] with X hr hP ht3 hP1
  simp only [Function.comp_apply, one_mul] at hP hP1
  have ht0 : 0 < Real.log (X : ℝ) := by linarith
  have hlog : Real.log (3 * Ψ (Real.log (X : ℝ))) ≤ 2 * Real.log (Real.log (X : ℝ)) := by
    have hh := Real.log_le_log (by linarith : 0 < 3 * Ψ (Real.log (X : ℝ)))
      (mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 3))
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) ht0.ne'] at hh
    have hthree := Real.log_le_log (by norm_num : (0 : ℝ) < 3) ht3
    linarith
  have hs := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 128 * κ by positivity)
  unfold rankConstant
  nlinarith

/-- Generous explicit polynomial bounds for the actual small window and
gap scale in the variable t=log X. Constants do not enter their exponents. -/
theorem eventually_window_gap_bounds {Ψ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSlopeBudget Ψ (1000000 * κ)) :
    ∀ᶠ X : ℕ in atTop,
      1 + (roughProfileS κ (zPsi Ψ X) : ℝ) ≤ (Real.log (X : ℝ)) ^ (5 : ℕ) ∧
        roughGapScale (zPsi Ψ X) ≤ (Real.log (X : ℝ)) ^ (2 : ℕ) := by
  let K := rankConstant κ
  let D := eulerProdLowerConst⁻¹ + Real.log 2 + 1
  have hK : 0 < K := mul_pos (by norm_num) hκ
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hz := h.tendsto_zPsi_atTop
  have hwin := (CoreRoughScaleLimits.tendsto_roughSyntheticScale_atTop.comp hz).eventually
    crtWindowG_eventually_eq_log
  filter_upwards [eventually_rank_le_loglog hκ h, CoreRoughSubpower.eventually_model_gap_le_log h,
    hwin, ht.eventually_ge_atTop (max 2 (max D ((6 / 5 : ℝ) * K)))] with X hr hG hw hlarge
  simp only [Function.comp_apply] at hw
  let t := Real.log (X : ℝ)
  have ht2 : 2 ≤ t := (le_max_left _ _).trans hlarge
  have htD : D ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have htK : (6 / 5 : ℝ) * K ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have ht0 : 0 < t := by linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogt : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  have hDinv : eulerProdLowerConst⁻¹ ≤ D := by dsimp only [D]; linarith
  have hgap : roughGapScale (zPsi Ψ X) ≤ t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (hDinv.trans htD) ht0.le
    rw [div_eq_mul_inv] at hG
    nlinarith
  have hwindow : windowG (roughSyntheticScale (zPsi Ψ X)) ≤ t ^ 2 := by
    rw [hw]
    have hupper := (CoreRoughScaleLimits.roughGapScale_le_log_synthetic_and_le (zPsi Ψ X)).2
    have hlog2t := mul_le_mul_of_nonneg_left (show 1 ≤ t by linarith) hlog2
    have hDt := mul_le_mul_of_nonneg_right htD ht0.le
    dsimp only [D] at hDt
    rw [div_eq_mul_inv] at hG
    nlinarith
  have hL : (roughProfileL κ (zPsi Ψ X) : ℝ) ≤ K * t := by
    have hnat := (profileR_ge (roughProfileL κ (zPsi Ψ X)) 20).trans (Nat.le_succ _)
    have hcast : (roughProfileL κ (zPsi Ψ X) : ℝ) ≤
        ((profileRank κ Ψ X + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    exact hcast.trans (hr.trans (mul_le_mul_of_nonneg_left hlogt hK.le))
  have hS : (roughProfileS κ (zPsi Ψ X) : ℝ) ≤ t ^ 4 := by
    have hfloor : (roughProfileS κ (zPsi Ψ X) : ℝ) ≤
        (6 / 5 : ℝ) * (roughProfileL κ (zPsi Ψ X) : ℝ) *
          windowG (roughSyntheticScale (zPsi Ψ X)) := by
      have harg : 0 ≤ (6 / 5 : ℝ) *
          (profileL κ (roughSyntheticScale (zPsi Ψ X)) : ℝ) *
          windowG (roughSyntheticScale (zPsi Ψ X)) :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          (zero_le_one.trans (le_max_right _ _))
      simpa only [roughProfileS, roughProfileL, ahlSmall_window] using Nat.floor_le harg
    have hprod := mul_le_mul hL hwindow
      (zero_lt_one.trans_le (le_max_right _ _)).le (mul_nonneg hK.le ht0.le)
    have hscaled := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 6 / 5)
    have hlast := mul_le_mul_of_nonneg_right htK (pow_nonneg ht0.le 3)
    nlinarith
  have hp4 : 1 ≤ t ^ (4 : ℕ) := one_le_pow₀ (by linarith : 1 ≤ t)
  have hstep := mul_le_mul_of_nonneg_right ht2 (pow_nonneg ht0.le 4)
  refine ⟨?_, hgap⟩
  change 1 + (roughProfileS κ (zPsi Ψ X) : ℝ) ≤ t ^ 5
  rw [show (5 : ℕ) = 4 + 1 by rfl, pow_succ]
  nlinarith

def logarithmicError (K C J t : ℝ) : ℝ :=
  8 * K * (Real.log t) ^ 2 + (C * K + J + 2) * Real.log t

theorem tendsto_logarithmicError_div_zero (K C J : ℝ) :
    Tendsto (fun t : ℝ => logarithmicError K C J t / t) atTop (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ => (Real.log t) ^ (2 : ℕ) / t) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 2 (by norm_num)
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hh := (hsq.const_mul (8 * K)).add (hlog.const_mul (C * K + J + 2))
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall fun t => by unfold logarithmicError; ring

theorem finite_envelope_le {X S r R : ℕ} {G K C J : ℝ}
    (hX : 0 < X) (ht : 2 ≤ Real.log (X : ℝ)) (hR : 1 ≤ R)
    (hRupper : (R : ℝ) ≤ (X : ℝ) ^ (1 / 3 : ℝ))
    (hG0 : 0 < G) (hG : G ≤ (Real.log (X : ℝ)) ^ (2 : ℕ))
    (hS : 1 + (S : ℝ) ≤ (Real.log (X : ℝ)) ^ (5 : ℕ))
    (hr : ((r + 1 : ℕ) : ℝ) ≤ K * Real.log (Real.log (X : ℝ)))
    (hC : 0 ≤ C) (hJ : 0 ≤ J) :
    (Real.log (X : ℝ)) ^ J * 2 ^ (r + 1) * (1 + (S : ℝ)) ^ (r + 1) *
      Real.exp (C * ((r + 1 : ℕ) : ℝ)) * (R : ℝ) * (1 + Real.log (R : ℝ)) ^ r * G / (X : ℝ) ≤
        Real.exp (logarithmicError K C J (Real.log (X : ℝ)) - (2 / 3 : ℝ) * Real.log (X : ℝ)) := by
  let t := Real.log (X : ℝ)
  have hX0 : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have ht0 : 0 < t := by dsimp only [t]; linarith
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by dsimp only [t]; linarith)
  have hR0 : 0 < (R : ℝ) := Nat.cast_pos.mpr hR
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hlogR0 : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg hR1
  have hlogR : Real.log (R : ℝ) ≤ (1 / 3 : ℝ) * t := by
    simpa only [Real.log_rpow hX0] using Real.log_le_log hR0 hRupper
  have htwo : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hsumS : Real.log (1 + (S : ℝ)) ≤ 5 * Real.log t := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < 1 + (S : ℝ)) hS
  have hsumR : Real.log (1 + Real.log (R : ℝ)) ≤ 2 * Real.log t := by
    have hinner : 1 + Real.log (R : ℝ) ≤ 2 * t := by dsimp only [t] at *; linarith
    have hh := Real.log_le_log (by linarith : 0 < 1 + Real.log (R : ℝ)) hinner
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne'] at hh
    linarith
  have hgap : Real.log G ≤ 2 * Real.log t := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hG0 hG
  have hpos : 0 < t ^ J * 2 ^ (r + 1) * (1 + (S : ℝ)) ^ (r + 1) *
      Real.exp (C * ((r + 1 : ℕ) : ℝ)) * (R : ℝ) * (1 + Real.log (R : ℝ)) ^ r * G / (X : ℝ) := by
    positivity
  apply (Real.log_le_iff_le_exp hpos).mp
  have heq : Real.log (t ^ J * 2 ^ (r + 1) * (1 + (S : ℝ)) ^ (r + 1) *
      Real.exp (C * ((r + 1 : ℕ) : ℝ)) * (R : ℝ) * (1 + Real.log (R : ℝ)) ^ r * G / (X : ℝ)) =
      J * Real.log t + ((r + 1 : ℕ) : ℝ) * Real.log 2 +
      ((r + 1 : ℕ) : ℝ) * Real.log (1 + (S : ℝ)) + C * ((r + 1 : ℕ) : ℝ) +
      Real.log (R : ℝ) + (r : ℝ) * Real.log (1 + Real.log (R : ℝ)) + Real.log G - t := by
    rw [Real.log_div (by positivity) hX0.ne']
    repeat rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_rpow ht0, Real.log_pow, Real.log_pow, Real.log_exp, Real.log_pow]
  rw [heq]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hrp0 : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha := mul_le_mul_of_nonneg_left htwo hrp0
  have hb := mul_le_mul_of_nonneg_left hsumS hrp0
  have hc := mul_le_mul_of_nonneg_left hsumR hr0
  have hd := mul_le_mul_of_nonneg_right hr (show 0 ≤ 8 * Real.log t + C by positivity)
  have he := mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hlogt0
  unfold logarithmicError
  push_cast at ha hb hc hd ⊢
  nlinarith

/-- The complete requested additive envelope vanishes for every fixed
nonnegative real C,J. All rank/window bounds were derived above. -/
theorem tendsto_envelope_zero {Ψ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSlopeBudget Ψ (1000000 * κ)) {C J : ℝ} (hC : 0 ≤ C) (hJ : 0 ≤ J) :
    Tendsto (envelope κ C J Ψ) atTop (𝓝 0) := by
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have herr := (tendsto_logarithmicError_div_zero (rankConstant κ) C J).comp ht
  have hsmall := herr.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 6)
  have hdecay : Tendsto (fun X : ℕ => Real.exp (-(Real.log (X : ℝ)) / 2)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) ht))
    apply hh.congr'
    exact Eventually.of_forall fun X => by dsimp only [Function.comp_apply]; congr 1; ring
  apply squeeze_zero' _ _ hdecay
  · filter_upwards [ht.eventually_ge_atTop 2,
      tendsto_cubeRootLevel_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℕ)] with X ht2 hR hX
    have ht0 : 0 < Real.log (X : ℝ) := by linarith
    have hRreal : (1 : ℝ) ≤ cubeRootLevel X := by exact_mod_cast hR
    have hlogR : 0 ≤ Real.log (cubeRootLevel X : ℝ) := Real.log_nonneg hRreal
    have hG := roughGapScale_pos (zPsi Ψ X)
    unfold envelope
    positivity
  · filter_upwards [eventually_rank_le_loglog hκ h, eventually_window_gap_bounds hκ h,
      hsmall, ht.eventually_ge_atTop 2, tendsto_cubeRootLevel_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℕ)] with X hr hSG herr ht2 hR hX
    simp only [Function.comp_apply] at herr
    have ht0 : 0 < Real.log (X : ℝ) := by linarith
    have hX0 : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
    have hRupper : (cubeRootLevel X : ℝ) ≤ (X : ℝ) ^ (1 / 3 : ℝ) :=
      Nat.floor_le (Real.rpow_pos_of_pos hX0 _).le
    have hfinite := finite_envelope_le hX ht2 hR hRupper
      (roughGapScale_pos (zPsi Ψ X)) hSG.2 hSG.1 hr hC hJ
    have herror : logarithmicError (rankConstant κ) C J (Real.log (X : ℝ)) ≤
        (1 / 6 : ℝ) * Real.log (X : ℝ) := (div_le_iff₀ ht0).mp herr
    exact hfinite.trans (Real.exp_le_exp.mpr (by linarith))

end
end PrimeGapNormality.Prime.CoreRoughAdditiveBudget
