import PrimeGapNormality.Prime.CoreRoughScaleLimits
import PrimeGapNormality.Prime.CrtLogProfileSDivLogX
import PrimeGapNormality.Prime.AhlSmallOfLarge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The small AHL window fits below the synthetic rough cutoff

At the literal synthetic scale `T(z)=ceil(exp(V(z)⁻¹))`, the proved
Euler-product lower bound makes `log T(z)=O(log z)`.  The existing profile
estimate `L(T)≤log T` then reduces the small-window comparison to the
elementary limit `(log z)^2/z→0`.

No distributional rough-number or prime-pattern premise is used.
-/

namespace PrimeGapNormality.Prime.CoreRoughSmallWindow

open Filter
open scoped Topology

open CoreRoughSyntheticScale CoreRoughScaleLimits

noncomputable section

private theorem tendsto_log_sq_div_self :
    Tendsto (fun z : ℕ ↦ Real.log (z : ℝ) ^ 2 / (z : ℝ))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun x : ℝ ↦ Real.log x ^ 2 / x)
      atTop (nhds 0) :=
    (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hnat.congr'
  exact Eventually.of_forall fun z ↦ rfl

/-- For every fixed positive profile parameter, the literal small AHL
window at the synthetic scale eventually lies strictly below the original
rough cutoff `z`. -/
theorem eventually_ahlSmall_window_roughSyntheticScale_lt
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ z : ℕ in atTop,
      ahlSmall_window κ (roughSyntheticScale z) < z := by
  let c := eulerProdLowerConst
  let D := c⁻¹ + Real.log 2
  let A := 4 * D ^ 2
  have hc : 0 < c := by
    dsimp only [c]
    exact eulerProdLowerConst_pos
  have hsmall : Tendsto (fun z : ℕ ↦
      A * (Real.log (z : ℝ) ^ 2 / (z : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_log_sq_div_self.const_mul A
  have hprofile : ∀ᶠ z : ℕ in atTop,
      (profileL κ (roughSyntheticScale z) : ℝ) ≤
        Real.log (roughSyntheticScale z : ℝ) :=
    tendsto_roughSyntheticScale_atTop.eventually
      (crtLogSLogX_eventually_profileL_le_log hκ)
  have hwindow : ∀ᶠ z : ℕ in atTop,
      windowG (roughSyntheticScale z) =
        Real.log (roughSyntheticScale z : ℝ) :=
    tendsto_roughSyntheticScale_atTop.eventually crtWindowG_eventually_eq_log
  have hlogOne : ∀ᶠ z : ℕ in atTop,
      (1 : ℝ) ≤ Real.log (z : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
        (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 16, hprofile, hwindow, hlogOne,
    hsmall.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))]
      with z hz hL hwindowEq hlogOne' hball
  let G := roughGapScale z
  let T := roughSyntheticScale z
  let lz := Real.log (z : ℝ)
  let lT := Real.log (T : ℝ)
  have hzpos : (0 : ℝ) < z :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 16) hz)
  have hlz1 : (1 : ℝ) ≤ lz := by
    simpa only [lz] using hlogOne'
  have hlz0 : 0 ≤ lz := zero_le_one.trans hlz1
  have hlT0 : 0 ≤ lT := by
    dsimp only [lT, T]
    exact (roughGapScale_pos z).le.trans
      (roughGapScale_le_log_synthetic_and_le z).1
  have hGupper : G ≤ lz / c := by
    dsimp only [G, lz, c]
    exact roughGapScale_le_log_div_lowerConst hz
  have hlogUpper : lT ≤ lz / c + Real.log 2 := by
    calc
      lT ≤ G + Real.log 2 := by
        simpa only [lT, T, G] using
          (roughGapScale_le_log_synthetic_and_le z).2
      _ ≤ lz / c + Real.log 2 := _root_.add_le_add hGupper le_rfl
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlinear : lz / c + Real.log 2 ≤ D * lz := by
    have htwo : Real.log 2 ≤ Real.log 2 * lz := by
      have := mul_le_mul_of_nonneg_left hlz1 hlogTwo
      simpa only [mul_one] using this
    dsimp only [D]
    rw [div_eq_mul_inv]
    calc
      lz * c⁻¹ + Real.log 2 ≤ lz * c⁻¹ + Real.log 2 * lz :=
        _root_.add_le_add le_rfl htwo
      _ = (c⁻¹ + Real.log 2) * lz := by ring
  have hlTD : lT ≤ D * lz := hlogUpper.trans hlinear
  have hsq : lT ^ 2 ≤ (D * lz) ^ 2 :=
    pow_le_pow_left₀ hlT0 hlTD 2
  have hscaled : 4 * lT ^ 2 ≤ A * lz ^ 2 := by
    calc
      4 * lT ^ 2 ≤ 4 * (D * lz) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = A * lz ^ 2 := by
        dsimp only [A]
        ring
  have habs :
      |A * (Real.log (z : ℝ) ^ 2 / (z : ℝ)) - 0| < 1 := hball
  have hratio : A * (lz ^ 2 / (z : ℝ)) < 1 := by
    have hleabs : A * (lz ^ 2 / (z : ℝ)) ≤
        |A * (lz ^ 2 / (z : ℝ))| := le_abs_self _
    dsimp only [lz] at hleabs ⊢
    rw [sub_zero] at habs
    exact hleabs.trans_lt habs
  have hAz : A * lz ^ 2 < (z : ℝ) := by
    have hdiv : A * lz ^ 2 / (z : ℝ) < 1 := by
      convert hratio using 1 <;> ring
    exact (div_lt_one hzpos).mp hdiv
  have hsmallProfile :
      (ahlSmall_window κ T : ℝ) ≤ 4 * lT ^ 2 := by
    have hsub : (ahlSmall_window κ T : ℝ) ≤ (profileS κ T : ℝ) :=
      Nat.cast_le.mpr (ahlSmall_window_le_profileS κ T)
    have hprof := crtLogSLogX_profileS_le_four κ T
    have hL' : (profileL κ T : ℝ) ≤ lT := by
      simpa only [T, lT] using hL
    calc
      (ahlSmall_window κ T : ℝ) ≤ (profileS κ T : ℝ) := hsub
      _ ≤ 4 * (profileL κ T : ℝ) * windowG T := hprof
      _ = 4 * (profileL κ T : ℝ) * lT := by rw [hwindowEq]
      _ ≤ 4 * lT * lT :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL' (by norm_num)) hlT0
      _ = 4 * lT ^ 2 := by ring
  have hcast : (ahlSmall_window κ T : ℝ) < (z : ℝ) :=
    hsmallProfile.trans_lt (hscaled.trans_lt hAz)
  exact_mod_cast hcast

end

end PrimeGapNormality.Prime.CoreRoughSmallWindow
