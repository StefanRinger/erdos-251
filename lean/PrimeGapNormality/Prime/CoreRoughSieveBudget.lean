import PrimeGapNormality.Prime.CoreRoughThreshold
import PrimeGapNormality.Prime.CoreRoughProfileError
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Explicit growing-rank and sieve-level budgets

All profiles below are the actual synthetic rough profiles. No Big-O,
moment-growth, or distribution bound is assumed in their derivation.
-/

namespace PrimeGapNormality.Prime.CoreRoughSieveBudget

open Filter CoreRoughThreshold CoreRoughSyntheticScale CoreRoughScaleLimits
open CoreRoughProfileError
open scoped Topology
noncomputable section

set_option maxHeartbeats 1000000

def profileRank (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) : ℕ :=
  profileR (roughProfileL κ (zPsi Ψ X)) 20

def cubeRootLevel (X : ℕ) : ℕ := ⌊(X : ℝ) ^ (1 / 3 : ℝ)⌋₊

theorem profileL_le_two_log_add_two {κ : ℝ} (hκ : 0 ≤ κ) (T : ℕ) :
    (profileL κ T : ℝ) ≤ 2 * κ * Real.log (windowG T) + 2 := by
  have hlog : 0 ≤ Real.log (windowG T) := Real.log_nonneg (le_max_right _ _)
  have hx : 0 ≤ κ * Real.log (windowG T) := mul_nonneg hκ hlog
  have hs0 := Real.sqrt_nonneg (κ * Real.log (windowG T))
  have hs2 := Real.sq_sqrt hx
  have hs : Real.sqrt (κ * Real.log (windowG T)) ≤ κ * Real.log (windowG T) + 1 := by
    nlinarith [sq_nonneg (Real.sqrt (κ * Real.log (windowG T)) - 1)]
  have hp := profileL_cast_le hκ T
  linarith

theorem rank_le_of_log_bound {κ P : ℝ} (hκ : 0 ≤ κ) (T : ℕ)
    (hlog : Real.log (windowG T) ≤ 2 * Real.log (3 * P))
    (hlarge : 45 ≤ 44 * κ * Real.log (3 * P)) :
    ((profileR (profileL κ T) 20 + 1 : ℕ) : ℝ) ≤ 128 * κ * Real.log (3 * P) := by
  have hL := profileL_le_two_log_add_two hκ T
  have hr := profileR_cast_le (profileL κ T) (d0 := (20 : ℝ)) (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hlog hκ
  push_cast
  nlinarith

theorem log_zPsi_le {Ψ : ℝ → ℝ} {X : ℕ} (hz : 0 < zPsi Ψ X) :
    Real.log (zPsi Ψ X : ℝ) ≤ Ψ (Real.log (X : ℝ)) := by
  have hfloor : (zPsi Ψ X : ℝ) ≤ Real.exp (Ψ (Real.log (X : ℝ))) :=
    Nat.floor_le (Real.exp_pos _).le
  simpa only [Real.log_exp] using Real.log_le_log (Nat.cast_pos.mpr hz) hfloor

/-- The Euler upper gap bound, the actual synthetic cutoff, and the
floor-defined threshold supply the logarithmic rank scale. -/
theorem eventually_log_windowG_le {Ψ : ℝ → ℝ} (hΨ : Tendsto Ψ atTop atTop) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (windowG (roughSyntheticScale (zPsi Ψ X))) ≤
        2 * Real.log (3 * Ψ (Real.log (X : ℝ))) := by
  let D : ℝ := eulerProdLowerConst⁻¹ + Real.log 2
  have hlogX : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hz := tendsto_zPsi_atTop hΨ
  have hwindow := (tendsto_roughSyntheticScale_atTop.comp hz).eventually crtWindowG_eventually_eq_log
  filter_upwards [hz.eventually_ge_atTop 16, (hΨ.comp hlogX).eventually_ge_atTop (max 1 D),
    hwindow] with X hz16 hP hw
  simp only [Function.comp_apply] at hP hw
  let P := Ψ (Real.log (X : ℝ))
  have hP1 : 1 ≤ P := (le_max_left _ _).trans hP
  have hPD : D ≤ P := (le_max_right _ _).trans hP
  have hP0 : 0 < P := zero_lt_one.trans_le hP1
  have hfloor := log_zPsi_le (by omega : 0 < zPsi Ψ X)
  have hG := roughGapScale_le_log_div_lowerConst hz16
  have hT := (roughGapScale_le_log_synthetic_and_le (zPsi Ψ X)).2
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hG' : roughGapScale (zPsi Ψ X) ≤ P / eulerProdLowerConst :=
    hG.trans (div_le_div_of_nonneg_right hfloor eulerProdLowerConst_pos.le)
  have hfirst : windowG (roughSyntheticScale (zPsi Ψ X)) ≤ D * P := by
    rw [hw]
    have hh := mul_le_mul_of_nonneg_left hP1 hlog2
    dsimp only [D]
    rw [div_eq_mul_inv] at hG'
    nlinarith
  have hsq : windowG (roughSyntheticScale (zPsi Ψ X)) ≤ (3 * P) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hPD hP0.le
    nlinarith [sq_nonneg P]
  have hpos : 0 < windowG (roughSyntheticScale (zPsi Ψ X)) :=
    zero_lt_one.trans_le (le_max_right _ _)
  have hh := Real.log_le_log hpos hsq
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

/-- Actual growing rank, including the extra point used by tuple moments.
Only Ψ→∞ and the fixed positive profile coefficient are required. -/
theorem eventually_profileRank_bound {Ψ : ℝ → ℝ} (hΨ : Tendsto Ψ atTop atTop)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, ((profileRank κ Ψ X + 1 : ℕ) : ℝ) ≤
      128 * κ * Real.log (3 * Ψ (Real.log (X : ℝ))) := by
  have hlogX : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge : Tendsto (fun X : ℕ => 44 * κ * Real.log (3 * Ψ (Real.log (X : ℝ)))) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (mul_pos (by norm_num) hκ)
      (Real.tendsto_log_atTop.comp
        (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3) (hΨ.comp hlogX)))
  filter_upwards [eventually_log_windowG_le hΨ, hlarge.eventually_ge_atTop 45] with X hlog hbig
  exact rank_le_of_log_bound hκ.le (roughSyntheticScale (zPsi Ψ X)) hlog hbig

/-- The actual floor cube-root level has the advertised logarithmic
reserve. Floor rounding costs only log 2 after the cube root exceeds two. -/
theorem eventually_log_cubeRootLevel_ge :
    ∀ᶠ X : ℕ in atTop, (3 / 10 : ℝ) * Real.log (X : ℝ) ≤
      Real.log (cubeRootLevel X : ℝ) := by
  have hX : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hroot := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hX
  have hlog := Real.tendsto_log_atTop.comp hX
  filter_upwards [hroot.eventually_ge_atTop 2, hlog.eventually_ge_atTop (30 * Real.log 2),
    eventually_ge_atTop (1 : ℕ)] with X htwo hlarge hX1
  simp only [Function.comp_apply] at htwo hlarge
  have hX0 : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hpow : 0 < (X : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hfloor := Nat.lt_floor_add_one ((X : ℝ) ^ (1 / 3 : ℝ))
  have hhalf : (X : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ (cubeRootLevel X : ℝ) := by
    change (X : ℝ) ^ (1 / 3 : ℝ) < (cubeRootLevel X : ℝ) + 1 at hfloor
    linarith
  have hh := Real.log_le_log (div_pos hpow (by norm_num)) hhalf
  rw [Real.log_div hpow.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_rpow hX0] at hh
  linarith

/-- A finite bound for the permitted upper cutoff range. -/
theorem log_cutoff_le {P Z : ℝ} (hP : 5 ≤ P) (hZ : 1 < Z)
    (hupper : Z ≤ Real.exp (2 * P) + 1) : Real.log Z ≤ (12 / 5 : ℝ) * P := by
  have he : 1 ≤ Real.exp (2 * P) := Real.one_le_exp_iff.mpr (by linarith)
  have hz : Z ≤ 2 * Real.exp (2 * P) := by linarith
  have hh := Real.log_le_log (zero_lt_one.trans hZ) hz
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos _).ne', Real.log_exp] at hh
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem sieve_s_ge {t P Z R : ℝ} (ht : 0 ≤ t) (hP : 0 < P) (hZ : 1 < Z)
    (hlogR : (3 / 10 : ℝ) * t ≤ Real.log R)
    (hlogZ : Real.log Z ≤ (12 / 5 : ℝ) * P) :
    t / (8 * P) ≤ Real.log R / Real.log Z := by
  have hq : 0 ≤ t / (8 * P) := div_nonneg ht (by positivity)
  have hh := mul_le_mul_of_nonneg_right hlogZ hq
  have hcancel : (8 * P) * (t / (8 * P)) = t := by field_simp [hP.ne']
  apply (le_div_iff₀ (Real.log_pos hZ)).mpr
  nlinarith

/-- The explicit million-slope budget pays the beta relative error and
an additional exp(10L) model moment envelope, retaining half the decay. -/
theorem relative_exponent_budget {κ P t s : ℝ} {r L : ℕ}
    (hκ : 0 ≤ κ) (hlog : 0 ≤ Real.log (3 * P)) (hP : 0 < P)
    (hr : ((r + 1 : ℕ) : ℝ) ≤ 128 * κ * Real.log (3 * P))
    (hL : L ≤ r + 1) (hs : t / (8 * P) ≤ s)
    (hslope : 1000000 * κ * Real.log (3 * P) ≤ t / P) :
    299 * ((r + 1 : ℕ) : ℝ) + 10 * (L : ℝ) - s ≤ -(t / P) / 16 := by
  have hL' : (L : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hL
  have hdiv : t / (8 * P) = (t / P) / 8 := by ring
  rw [hdiv] at hs
  have hpos := mul_nonneg hκ hlog
  nlinarith

/-- The actual cube-root level and every admissible upper cutoff satisfy
the quantitative lower bound for the sieve parameter. -/
theorem eventually_sieve_s_ge {Ψ : ℝ → ℝ} (hΨ : Tendsto Ψ atTop atTop)
    (Z : ℕ → ℝ)
    (hZ : ∀ᶠ X : ℕ in atTop, 1 < Z X ∧
      Z X ≤ Real.exp (2 * Ψ (Real.log (X : ℝ))) + 1) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) / (8 * Ψ (Real.log (X : ℝ))) ≤
        Real.log (cubeRootLevel X : ℝ) / Real.log (Z X) := by
  have hlogX : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [(hΨ.comp hlogX).eventually_ge_atTop 5,
    hlogX.eventually_ge_atTop 0, eventually_log_cubeRootLevel_ge, hZ] with X hP ht hR hz
  simp only [Function.comp_apply] at hP
  exact sieve_s_ge ht (by linarith) hz.1 hR (log_cutoff_le hP hz.1 hz.2)

/-- The actual profile exponent has a fixed quantitative negative margin
under the explicit slope budget; no moment or relative-error premise is
inserted here. -/
theorem eventually_relative_exponent_budget {Ψ : ℝ → ℝ} (hΨ : Tendsto Ψ atTop atTop)
    {κ : ℝ} (hκ : 0 < κ) (Z : ℕ → ℝ)
    (hZ : ∀ᶠ X : ℕ in atTop, 1 < Z X ∧
      Z X ≤ Real.exp (2 * Ψ (Real.log (X : ℝ))) + 1)
    (hslope : ∀ᶠ t : ℝ in atTop,
      1000000 * κ * Real.log (3 * Ψ t) ≤ t / Ψ t) :
    ∀ᶠ X : ℕ in atTop,
      299 * ((profileRank κ Ψ X + 1 : ℕ) : ℝ) +
        10 * (roughProfileL κ (zPsi Ψ X) : ℝ) -
          Real.log (cubeRootLevel X : ℝ) / Real.log (Z X) ≤
        -(Real.log (X : ℝ) / Ψ (Real.log (X : ℝ))) / 16 := by
  have hlogX : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_profileRank_bound hΨ hκ, eventually_sieve_s_ge hΨ Z hZ,
    hlogX.eventually hslope, (hΨ.comp hlogX).eventually_ge_atTop 1] with X hr hs hb hP
  simp only [Function.comp_apply] at hb hP
  apply relative_exponent_budget hκ.le (Real.log_nonneg (by linarith))
    (by linarith) hr _ hs hb
  exact (profileR_ge (roughProfileL κ (zPsi Ψ X)) 20).trans (Nat.le_succ _)

end
end PrimeGapNormality.Prime.CoreRoughSieveBudget
