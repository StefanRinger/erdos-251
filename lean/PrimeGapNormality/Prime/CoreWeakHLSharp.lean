import PrimeGapNormality.Prime.CoreWeakHLSupplier

namespace PrimeGapNormality.Prime.CoreWeakHL
open Filter Finset
open scoped Topology
noncomputable section

theorem eventually_small_window_ge_G {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, windowG X ≤ (ahlSmall_window κ X : ℝ) := by
  filter_upwards [(tendsto_profileL_atTop hκ).eventually_ge_atTop 2] with X hL
  have hL' : (2 : ℝ) ≤ profileL κ X := by exact_mod_cast hL
  have hG : 1 ≤ windowG X := le_max_right _ _
  have hf := Nat.lt_floor_add_one (((6 : ℝ) / 5) * (profileL κ X : ℝ) * windowG X)
  change ((6 : ℝ) / 5) * (profileL κ X : ℝ) * windowG X <
    (ahlSmall_window κ X : ℝ) + 1 at hf
  nlinarith [mul_le_mul_of_nonneg_right hL' (show 0 ≤ windowG X by linarith)]

/-- The logarithmic window asymptotic for the literal factor-6/5 paper window. -/
theorem log_small_window_ratio {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X => Real.log (ahlSmall_window κ X : ℝ) / ell X)
      atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (log_window_ratio hκ) ?_ ?_
  · filter_upwards [eventually_small_window_ge_G hκ, ell_atTop.eventually_gt_atTop 0]
      with X hS hX
    have hG : 0 < windowG X := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    exact (le_div_iff₀ hX).mpr (by simpa [ell] using Real.log_le_log hG hS)
  · filter_upwards [eventually_small_window_ge_G hκ, ell_atTop.eventually_gt_atTop 0]
      with X hS hX
    have hG : 0 < windowG X := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (hG.trans_le hS) (Nat.cast_le.mpr (ahlSmall_window_le_profileS κ X))) hX.le

theorem log_rank_div_square_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X => Real.log ((profileR (profileL κ X) 20 : ℝ) + 1) / ell X ^ 2)
      atTop (𝓝 0) := by
  have hu := (rooted_rank_ratio hκ).mul inv_ell_zero
  simp only [mul_zero] at hu
  have hu' : Tendsto (fun X => ((profileR (profileL κ X) 20 : ℝ) + 1) / ell X ^ 2)
      atTop (𝓝 0) := by
    convert hu using 1
    ext X
    ring
  refine squeeze_zero' (Eventually.of_forall (fun X => ?_))
    (Eventually.of_forall (fun X => ?_)) hu'
  · exact div_nonneg (Real.log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) (profileR (profileL κ X) 20)
      linarith)) (sq_nonneg _)
  · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have h := Real.log_le_sub_one_of_pos
      (show 0 < (profileR (profileL κ X) 20 : ℝ) + 1 by positivity)
    linarith

/-- Exact logarithmic equivalent for `(r+1)2^rS^r` at the literal paper window;
thus the coefficient twenty is an equality, not merely an upper bound. -/
theorem log_small_combEnvelope_ratio {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X => Real.log (combEnvelope (ahlSmall_window κ X)
      (profileR (profileL κ X) 20)) / ell X ^ 2) atTop (𝓝 (20 * κ)) := by
  have h₁ := log_rank_div_square_zero hκ
  have h₂ := ((rank_ratio hκ).mul_const (Real.log 2)).mul inv_ell_zero
  have h₃ := (rank_ratio hκ).mul (log_small_window_ratio hκ)
  have hh := (h₁.add h₂).add h₃
  simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_small_window_ge_G hκ] with X hS
  have hG : 0 < windowG X := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hSp : 0 < (ahlSmall_window κ X : ℝ) := hG.trans_le hS
  unfold combEnvelope
  rw [Real.log_mul (by positivity) (pow_ne_zero _ hSp.ne'),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  ring

theorem small_binomial_sum_le (κ : ℝ) (X : ℕ) (hS : 1 ≤ ahlSmall_window κ X) :
    ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) 20),
      ((j - 1).choose (profileL κ X - 1) : ℝ) * ((ahlSmall_window κ X).choose j : ℝ) ≤
      combEnvelope (ahlSmall_window κ X) (profileR (profileL κ X) 20) :=
  binomial_sum_le _ _ _ hS

/-- The displayed paper rate with the actual `log log X`, including all
constant and uniformity quantifiers. -/
theorem quantitative_envelope_loglog {κ A : ℝ} (hκ : 0 < κ)
    (hA : 40 * κ < A) (hHL : UniformError A) :
    ∃ C > 0, ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ahlSmall_budget κ 20 X ≤
        C * Real.exp (-(A - 20 * κ + η X) * Real.log (Real.log (X : ℝ)) ^ 2) := by
  obtain ⟨C, hC, η, hη, hb⟩ := quantitative_envelope hκ hA hHL
  refine ⟨C, hC, η, hη, ?_⟩
  filter_upwards [hb, eventually_ge_atTop 3] with X hX h3
  simpa only [ell_eq_loglog h3] using hX

end
end PrimeGapNormality.Prime.CoreWeakHL
