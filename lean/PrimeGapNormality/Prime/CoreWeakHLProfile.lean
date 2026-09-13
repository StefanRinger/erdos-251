import PrimeGapNormality.Prime.CoreWeakHLFinite
import PrimeGapNormality.Prime.CrtFailureMassLimit

namespace PrimeGapNormality.Prime.CoreWeakHL
open Filter Finset
open scoped Topology
noncomputable section

def ell (X : ℕ) : ℝ := Real.log (windowG X)

theorem ell_eq_loglog {X : ℕ} (hX : 3 ≤ X) :
    ell X = Real.log (Real.log (X : ℝ)) := by
  rw [ell, windowG_eq_log hX]

theorem ell_atTop : Tendsto ell atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_windowG_atTop

theorem inv_ell_zero : Tendsto (fun X => (ell X)⁻¹) atTop (𝓝 0) :=
  ell_atTop.inv_tendsto_atTop

theorem log_ell_div_ell_zero :
    Tendsto (fun X => Real.log (ell X) / ell X) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  exact h.comp ell_atTop

theorem profileL_ratio {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X => (profileL κ X : ℝ) / ell X) atTop (𝓝 κ) := by
  have hs : Tendsto (fun X => Real.sqrt κ * (Real.sqrt (ell X))⁻¹)
      atTop (𝓝 0) := by
    simpa using ((Real.tendsto_sqrt_atTop.comp ell_atTop).inv_tendsto_atTop).const_mul
      (Real.sqrt κ)
  have hu : Tendsto (fun X => κ + Real.sqrt κ * (Real.sqrt (ell X))⁻¹ +
      (ell X)⁻¹) atTop (𝓝 κ) := by
    simpa using (tendsto_const_nhds.add hs).add inv_ell_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [ell_atTop.eventually_gt_atTop 0] with X hX
    have hl : κ * ell X ≤ (profileL κ X : ℝ) :=
      (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (Nat.le_ceil _)
    exact (le_div_iff₀ hX).mpr hl
  · filter_upwards [ell_atTop.eventually_gt_atTop 0] with X hX
    have hl := profileL_cast_le hκ.le X
    change (profileL κ X : ℝ) ≤ κ * ell X + Real.sqrt (κ * ell X) + 1 at hl
    have he : Real.sqrt (κ * ell X) / ell X =
        Real.sqrt κ * (Real.sqrt (ell X))⁻¹ := by
      rw [Real.sqrt_mul hκ.le, mul_div_assoc, Real.sqrt_div_self]
    have hh := (div_le_div_of_nonneg_right hl hX.le)
    rw [add_div, add_div, mul_div_cancel_right₀ κ hX.ne', he, one_div] at hh
    exact hh

theorem rank_bounds (L : ℕ) :
    20 * L ≤ profileR L 20 ∧ profileR L 20 ≤ 20 * L + 1 := by
  have hc : ⌈(20 : ℝ) * (L : ℝ)⌉₊ = 20 * L := by
    have he : (20 : ℝ) * (L : ℝ) = ((20 * L : ℕ) : ℝ) := by norm_num
    rw [he, Nat.ceil_natCast]
  dsimp [profileR]
  rw [hc, max_eq_right (show L ≤ 20 * L by omega)]
  split_ifs <;> omega

theorem rank_ratio {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X => (profileR (profileL κ X) 20 : ℝ) / ell X)
      atTop (𝓝 (20 * κ)) := by
  have hlo := (profileL_ratio hκ).const_mul 20
  have hhi := hlo.add inv_ell_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo (by simpa using hhi) ?_ ?_
  · filter_upwards [ell_atTop.eventually_gt_atTop 0] with X hX
    have h : (20 : ℝ) * profileL κ X ≤ profileR (profileL κ X) 20 := by
      exact_mod_cast (rank_bounds (profileL κ X)).1
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h hX.le
  · filter_upwards [ell_atTop.eventually_gt_atTop 0] with X hX
    have h : (profileR (profileL κ X) 20 : ℝ) ≤ 20 * profileL κ X + 1 := by
      exact_mod_cast (rank_bounds (profileL κ X)).2
    simpa only [add_div, mul_div_assoc, one_div] using
      div_le_div_of_nonneg_right h hX.le

theorem rooted_rank_ratio {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X => ((profileR (profileL κ X) 20 : ℝ) + 1) / ell X)
      atTop (𝓝 (20 * κ)) := by
  simpa only [add_div, one_div, add_zero] using (rank_ratio hκ).add inv_ell_zero

theorem eventually_window_ge_G {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, windowG X ≤ (profileS κ X : ℝ) := by
  filter_upwards [(tendsto_profileL_atTop hκ).eventually_ge_atTop 1] with X hL
  have hL' : (1 : ℝ) ≤ profileL κ X := by exact_mod_cast hL
  have hG : 1 ≤ windowG X := le_max_right _ _
  have hf := Nat.lt_floor_add_one (4 * (profileL κ X : ℝ) * windowG X)
  change 4 * (profileL κ X : ℝ) * windowG X < (profileS κ X : ℝ) + 1 at hf
  nlinarith [mul_le_mul_of_nonneg_right hL' (show 0 ≤ windowG X by linarith)]

theorem log_window_ratio {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X => Real.log (profileS κ X : ℝ) / ell X) atTop (𝓝 1) := by
  have hupper : Tendsto (fun X =>
      Real.log (4 * (κ + 1)) * (ell X)⁻¹ + Real.log (ell X) / ell X + 1)
      atTop (𝓝 1) := by
    simpa using ((inv_ell_zero.const_mul (Real.log (4 * (κ + 1)))).add
      log_ell_div_ell_zero).add_const 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_window_ge_G hκ, ell_atTop.eventually_gt_atTop 0] with X hS hX
    have hG : 0 < windowG X := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    exact (le_div_iff₀ hX).mpr (by simpa [ell] using Real.log_le_log hG hS)
  · filter_upwards [eventually_window_ge_G hκ, ell_atTop.eventually_gt_atTop 0,
      (profileL_ratio hκ).eventually (gt_mem_nhds (show κ < κ + 1 by linarith))]
      with X hS hX hL
    have hL' : (profileL κ X : ℝ) ≤ (κ + 1) * ell X :=
      ((div_lt_iff₀ hX).mp hL).le
    have hG : 0 < windowG X := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hSpos : 0 < (profileS κ X : ℝ) := hG.trans_le hS
    have hb : (profileS κ X : ℝ) ≤ (4 * (κ + 1)) * ell X * windowG X := by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL' (show (0 : ℝ) ≤ 4 by norm_num)) hG.le
      exact (profileS_cast_le κ X).trans (by nlinarith [hm])
    have hh := div_le_div_of_nonneg_right (Real.log_le_log hSpos hb) hX.le
    rw [Real.log_mul (by positivity) hG.ne',
      Real.log_mul (by positivity) hX.ne', add_div, add_div,
      show Real.log (windowG X) / ell X = 1 from div_self hX.ne'] at hh
    simpa only [div_eq_mul_inv] using hh

def profileExponent (κ : ℝ) (X : ℕ) : ℝ :=
  let r : ℝ := profileR (profileL κ X) 20
  (r + 1) + r * Real.log 2 + r * Real.log (profileS κ X : ℝ)

theorem exponent_ratio {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X => profileExponent κ X / (ell X) ^ 2)
      atTop (𝓝 (20 * κ)) := by
  have h₁ := (rooted_rank_ratio hκ).mul inv_ell_zero
  have h₂ := ((rank_ratio hκ).mul_const (Real.log 2)).mul inv_ell_zero
  have h₃ := (rank_ratio hκ).mul (log_window_ratio hκ)
  have hh := (h₁.add h₂).add h₃
  simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one] at hh
  convert hh using 1
  ext X
  unfold profileExponent
  ring

theorem combEnvelope_le_exp {S r : ℕ} (hS : 1 ≤ S) :
    combEnvelope S r ≤ Real.exp (((r : ℝ) + 1) +
      (r : ℝ) * Real.log 2 + (r : ℝ) * Real.log (S : ℝ)) := by
  have hSpos : 0 < (S : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hS)
  rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hSpos]
  unfold combEnvelope
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith [Real.add_one_le_exp ((r : ℝ) + 1)]

end
end PrimeGapNormality.Prime.CoreWeakHL
