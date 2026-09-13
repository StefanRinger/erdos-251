import PrimeGapNormality.Prime.CoreRoughSieveBudget
import PrimeGapNormality.Prime.CoreRoughSubpower

/-!
# Weighted local-cutoff hazard decay, including slowly growing thresholds

The inverse-square-root term is handled in the independent cutoff variable
z before composition with zPsi. It therefore requires no lower rate for Ψ.
The fixed slicing exponent depends only on κ, not on local polynomial width.
-/

namespace PrimeGapNormality.Prime.CoreRoughRelativeHazardBudget

open Filter CoreRoughThreshold CoreRoughSyntheticScale CoreRoughProfileError
open CoreRoughSieveBudget
open scoped Topology
noncomputable section

set_option maxHeartbeats 1000000

def weightedRank (κ : ℝ) (z : ℕ) : ℝ :=
  ((profileR (roughProfileL κ z) 20 + 1 : ℕ) : ℝ) * Real.exp (10 * (roughProfileL κ z : ℝ))

def slicingExponent (κ : ℝ) : ℕ := ⌈168 * κ⌉₊ + 3

theorem weightedRank_nonneg (κ : ℝ) (z : ℕ) : 0 ≤ weightedRank κ z :=
  mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le

theorem weightedRank_le_exp (κ : ℝ) (z : ℕ) :
    weightedRank κ z ≤ Real.exp (31 * (roughProfileL κ z : ℝ) + 3) := by
  have hr := profileR_cast_le (roughProfileL κ z) (d0 := (20 : ℝ)) (by norm_num)
  have he : ((profileR (roughProfileL κ z) 20 + 1 : ℕ) : ℝ) ≤
      Real.exp ((profileR (roughProfileL κ z) 20 + 1 : ℕ) : ℝ) := by
    linarith [Real.add_one_le_exp ((profileR (roughProfileL κ z) 20 + 1 : ℕ) : ℝ)]
  calc
    _ ≤ Real.exp ((profileR (roughProfileL κ z) 20 + 1 : ℕ) : ℝ) *
        Real.exp (10 * (roughProfileL κ z : ℝ)) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      linarith

theorem tendsto_profileL_div_log_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun z : ℕ => (roughProfileL κ z : ℝ) / Real.log (z : ℝ)) atTop (𝓝 0) := by
  have hlim := (tendsto_roughProfileL_div_gapScale_zero hκ).mul_const eulerProdLowerConst⁻¹
  simp only [zero_mul] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (16 : ℕ)] with z hz
    have hzR : (16 : ℝ) ≤ z := by exact_mod_cast hz
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_pos (by linarith)).le
  · filter_upwards [eventually_ge_atTop (16 : ℕ)] with z hz
    have hzR : (16 : ℝ) ≤ z := by exact_mod_cast hz
    have hlog : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
    have hG := roughGapScale_pos z
    have hbound := CoreRoughScaleLimits.roughGapScale_le_log_div_lowerConst hz
    have hratio : roughGapScale z / Real.log (z : ℝ) ≤ eulerProdLowerConst⁻¹ := by
      apply (div_le_iff₀ hlog).mpr
      simpa only [div_eq_mul_inv, mul_comm] using hbound
    calc
      _ = ((roughProfileL κ z : ℝ) / roughGapScale z) *
          (roughGapScale z / Real.log (z : ℝ)) := by field_simp [hG.ne', hlog.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio (div_nonneg (Nat.cast_nonneg _) hG.le)

/-- Arbitrarily slow growth of Ψ is harmless: this limit is first proved
in z, using only that the model depth is o(log z). -/
theorem tendsto_weightedRank_div_sqrt_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun z : ℕ => weightedRank κ z / Real.sqrt (z : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun z : ℕ => Real.log (z : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv : Tendsto (fun z : ℕ => (Real.log (z : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hfrac : Tendsto (fun z : ℕ =>
      (31 * (roughProfileL κ z : ℝ) + 3) / Real.log (z : ℝ)) atTop (𝓝 0) := by
    have hh := ((tendsto_profileL_div_log_zero hκ).const_mul 31).add (hinv.const_mul 3)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun z => by
      dsimp only
      simp only [div_eq_mul_inv]
      ring
  have hpow : Tendsto (fun z : ℕ => (z : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    exact (_root_.tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero' _ _ hpow
  · exact Eventually.of_forall fun z => div_nonneg (weightedRank_nonneg κ z) (Real.sqrt_nonneg _)
  · filter_upwards [hfrac.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4),
      eventually_ge_atTop (2 : ℕ)] with z hfrac hz
    have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
    have hz0 : (0 : ℝ) < z := by linarith
    have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
    have hnum := (div_le_iff₀ hlogz).mp hfrac
    calc
      _ ≤ Real.exp ((1 / 4 : ℝ) * Real.log (z : ℝ)) / Real.sqrt (z : ℝ) :=
        div_le_div_of_nonneg_right
          ((weightedRank_le_exp κ z).trans (Real.exp_le_exp.mpr hnum)) (Real.sqrt_nonneg _)
      _ = _ := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hz0, Real.rpow_def_of_pos hz0, ← Real.exp_sub]
        congr 1
        ring

/-- A coarse but width-independent polynomial envelope in Ψ for the
weighted rank. Its exponent is fixed once κ is fixed. -/
theorem eventually_weightedRank_le_psi {Ψ : ℝ → ℝ} (hΨ : Tendsto Ψ atTop atTop)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, weightedRank κ (zPsi Ψ X) ≤
      Real.exp (20 + 168 * κ * Real.log (3 * Ψ (Real.log (X : ℝ)))) := by
  filter_upwards [eventually_profileRank_bound hΨ hκ, eventually_log_windowG_le hΨ] with X hr hlog
  have hL := profileL_le_two_log_add_two hκ.le (roughSyntheticScale (zPsi Ψ X))
  have hscale := mul_le_mul_of_nonneg_left hlog hκ.le
  have he : ((profileRank κ Ψ X + 1 : ℕ) : ℝ) ≤ Real.exp ((profileRank κ Ψ X + 1 : ℕ) : ℝ) := by
    linarith [Real.add_one_le_exp ((profileRank κ Ψ X + 1 : ℕ) : ℝ)]
  calc
    _ ≤ Real.exp ((profileRank κ Ψ X + 1 : ℕ) : ℝ) *
        Real.exp (10 * (roughProfileL κ (zPsi Ψ X) : ℝ)) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      change (roughProfileL κ (zPsi Ψ X) : ℝ) ≤ _ at hL
      nlinarith

theorem tendsto_power_hazard_zero {Ψ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSlopeBudget Ψ (1000000 * κ)) (J : ℕ) (hJ : 168 * κ < (J : ℝ) + 1) :
    Tendsto (fun X : ℕ => weightedRank κ (zPsi Ψ X) *
      (Real.log (X : ℝ)) ^ (-(J : ℝ) - 1)) atTop (𝓝 0) := by
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  let d := (J : ℝ) + 1 - 168 * κ
  have hd : 0 < d := by dsimp only [d]; linarith
  have hlim := ((_root_.tendsto_rpow_neg_atTop hd).comp ht).const_mul
    (Real.exp (20 + 168 * κ * Real.log 3))
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall fun X => mul_nonneg (weightedRank_nonneg κ _)
      (Real.rpow_nonneg (Real.log_natCast_nonneg X) _)
  · filter_upwards [eventually_weightedRank_le_psi h.2.1 hκ,
      ht.eventually (CoreRoughSubpower.eventually_psi_le_mul h (by norm_num : (0 : ℝ) < 1)),
      ht.eventually_ge_atTop 1, (h.2.1.comp ht).eventually_ge_atTop 1] with X hcost hP ht1 hP1
    simp only [Function.comp_apply, one_mul] at hP hP1
    have ht0 : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le ht1
    have hlogs := Real.log_le_log (by linarith : 0 < 3 * Ψ (Real.log (X : ℝ)))
      (mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 3))
    have hbound := hcost.trans (Real.exp_le_exp.mpr
      (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogs (by positivity : 0 ≤ 168 * κ))))
    calc
      _ ≤ Real.exp (20 + 168 * κ * Real.log (3 * Real.log (X : ℝ))) *
          (Real.log (X : ℝ)) ^ (-(J : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg ht0.le _)
      _ = _ := by
        dsimp only [d, Function.comp_apply]
        rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) ht0.ne',
          Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

theorem slicingExponent_large (κ : ℝ) : 2 < slicingExponent κ ∧
    168 * κ < (slicingExponent κ : ℝ) + 1 := by
  have hh := Nat.le_ceil (168 * κ)
  constructor
  · unfold slicingExponent
    omega
  · unfold slicingExponent
    push_cast
    linarith

/-- Complete local hazard cost at a fixed slicing exponent. The second
term uses only zPsi→∞, so arbitrarily slow Ψ remains covered. -/
theorem tendsto_weighted_local_hazard_zero {Ψ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSlopeBudget Ψ (1000000 * κ)) :
    Tendsto (fun X : ℕ => ((profileRank κ Ψ X + 1 : ℕ) : ℝ) *
      ((Real.log (X : ℝ)) ^ (-(slicingExponent κ : ℝ) - 1) +
        1 / Real.sqrt (zPsi Ψ X : ℝ)) *
      Real.exp (10 * (roughProfileL κ (zPsi Ψ X) : ℝ))) atTop (𝓝 0) := by
  have h1 := tendsto_power_hazard_zero hκ h (slicingExponent κ) (slicingExponent_large κ).2
  have h2 := (tendsto_weightedRank_div_sqrt_zero hκ).comp h.tendsto_zPsi_atTop
  have hh := h1.add h2
  simp only [add_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall fun X => by
    dsimp only [Function.comp_apply, weightedRank, profileRank]
    ring

end
end PrimeGapNormality.Prime.CoreRoughRelativeHazardBudget
