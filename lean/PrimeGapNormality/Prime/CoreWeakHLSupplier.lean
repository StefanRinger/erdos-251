import PrimeGapNormality.Prime.CoreWeakHLRooted
import PrimeGapNormality.Prime.CorePrimeDensityBounds
import PrimeGapNormality.Prime.CoreAHLToD

namespace PrimeGapNormality.Prime.CoreWeakHL
open Filter Finset
open scoped Topology
noncomputable section

def errorExponent (κ A : ℝ) (X : ℕ) : ℝ :=
  profileExponent κ X + ell X - A * ell X ^ 2

theorem errorExponent_ratio {κ : ℝ} (hκ : 0 < κ) (A : ℝ) :
    Tendsto (fun X => errorExponent κ A X / ell X ^ 2)
      atTop (𝓝 (20 * κ - A)) := by
  have h := ((exponent_ratio hκ).add inv_ell_zero).sub_const A
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [ell_atTop.eventually_gt_atTop 0] with X hX
  unfold errorExponent
  field_simp [hX.ne']
  <;> ring

theorem eventually_budget_envelope {κ A : ℝ} (hκ : 0 < κ)
    (hA : 40 * κ < A) (hHL : UniformError A) :
    ∃ C > 0, ∀ᶠ X : ℕ in atTop,
      ahlBudget κ 20 X ≤ C * Real.exp (errorExponent κ A X) := by
  obtain ⟨C, hC, x₀, hbound⟩ := hHL
  refine ⟨48 * C, by positivity, ?_⟩
  filter_upwards [eventually_profileFits hκ (by norm_num : (0 : ℝ) < 20),
    eventually_order_fits hκ hA, eventually_window_ge_G hκ,
    CorePrimeDensity.eventually_X_div_windowNX_le,
    eventually_ge_atTop x₀] with X hfit hord hS hNX hx₀
  have hX3 : 3 ≤ X := by have := hfit.1; omega
  have hXpos : 0 < X := by omega
  have hlogpos : 0 < Real.log (X : ℝ) :=
    lt_trans (by norm_num) (one_lt_log_of_three_le hX3)
  have hN : windowNX X ≠ 0 := (windowNX_pos hXpos).ne'
  have hS' : 1 ≤ profileS κ X := by
    have h : (1 : ℝ) ≤ profileS κ X := (le_max_right _ _).trans hS
    exact_mod_cast h
  have hraw := budget_le_raw_error (κ := κ) (d := 20) (X := X) hN hS'
    (show 0 ≤ 3 * C * (X : ℝ) * Real.exp (-A * ell X ^ 2) by positivity)
    (fun H hH hr => rooted_error_of_uniform_bound (A := A) (C := C) (by linarith) hC.le
      hbound hfit hx₀ hord hH hr)
  have he := combEnvelope_le_exp (r := profileR (profileL κ X) 20) hS'
  change combEnvelope (profileS κ X) (profileR (profileL κ X) 20) ≤
    Real.exp (profileExponent κ X) at he
  calc
    ahlBudget κ 20 X ≤ (1 / (windowNX X : ℝ)) *
      (combEnvelope (profileS κ X) (profileR (profileL κ X) 20) *
        (3 * C * (X : ℝ) * Real.exp (-A * ell X ^ 2))) := hraw
    _ = 3 * C * ((X : ℝ) / (windowNX X : ℝ)) *
      combEnvelope (profileS κ X) (profileR (profileL κ X) 20) *
        Real.exp (-A * ell X ^ 2) := by ring
    _ ≤ 3 * C * (16 * Real.log (X : ℝ)) * Real.exp (profileExponent κ X) *
        Real.exp (-A * ell X ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul _ he (by unfold combEnvelope; positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hNX (by positivity)
    _ = 48 * C * Real.exp (errorExponent κ A X) := by
      have hg : Real.log (X : ℝ) = Real.exp (ell X) := by
        rw [ell_eq_loglog hX3, Real.exp_log]
        exact lt_trans (by norm_num) (one_lt_log_of_three_le hX3)
      rw [hg]
      unfold errorExponent
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
      ring

theorem exp_errorExponent_zero {κ A : ℝ} (hκ : 0 < κ) (hA : 20 * κ < A) :
    Tendsto (fun X => Real.exp (errorExponent κ A X)) atTop (𝓝 0) := by
  have hratio := errorExponent_ratio hκ A
  have hsq : Tendsto (fun X => ell X ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp ell_atTop
  have hc : (20 * κ - A) / 2 < 0 := by linarith
  have hlim := hsq.const_mul_atTop_of_neg hc
  have hupper : ∀ᶠ X : ℕ in atTop,
      errorExponent κ A X ≤ ((20 * κ - A) / 2) * ell X ^ 2 := by
    filter_upwards [ell_atTop.eventually_gt_atTop 0,
      hratio.eventually (gt_mem_nhds (show 20 * κ - A < (20 * κ - A) / 2 by linarith))]
      with X hX hr
    exact ((div_lt_iff₀ (sq_pos_of_pos hX)).mp hr).le
  apply Real.tendsto_exp_atBot.comp
  apply tendsto_atBot.2
  intro b
  filter_upwards [hupper, hlim.eventually_le_atBot b] with X hX hB
  exact hX.trans hB

/-- Actual uniform growing-order HL implies the existing large AHL budget. -/
theorem AHL_of_uniformError {κ A : ℝ} (hκ : 0 < κ)
    (hA : 40 * κ < A) (hHL : UniformError A) : AHL κ 20 := by
  obtain ⟨C, hC, henv⟩ := eventually_budget_envelope hκ hA hHL
  exact squeeze_zero' (Eventually.of_forall (ahlBudget_nonneg κ 20)) henv
    (by simpa using (exp_errorExponent_zero (A := A) hκ (by linarith)).const_mul C)

/-- Literal paper small-window AHL, with cutoff exactly twenty. -/
theorem ahlSmall_of_uniformError {κ A : ℝ} (hκ : 0 < κ)
    (hA : 40 * κ < A) (hHL : UniformError A) : ahlSmall_AHL κ 20 :=
  ahlSmall_AHL_of_AHL (AHL_of_uniformError hκ hA hHL)

/-- Reuses the existing D consumer; no alternative D interface is introduced. -/
theorem coreLinearD_of_uniformError {κ A : ℝ} (hκ : 0 < κ)
    (hA : 40 * κ < A) (hHL : UniformError A) : CoreLinearD κ 20 1 :=
  CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκ (ahlSmall_of_uniformError hκ hA hHL)

/-- Explicit paper exponent, with a proved vanishing coefficient correction. -/
theorem quantitative_envelope {κ A : ℝ} (hκ : 0 < κ)
    (hA : 40 * κ < A) (hHL : UniformError A) :
    ∃ C > 0, ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ahlSmall_budget κ 20 X ≤
        C * Real.exp (-(A - 20 * κ + η X) * ell X ^ 2) := by
  obtain ⟨C, hC, henv⟩ := eventually_budget_envelope hκ hA hHL
  refine ⟨C, hC, (fun X => (20 * κ - A) - errorExponent κ A X / ell X ^ 2),
    ?_, ?_⟩
  · simpa using (tendsto_const_nhds (x := 20 * κ - A)).sub (errorExponent_ratio hκ A)
  · filter_upwards [henv, ell_atTop.eventually_gt_atTop 0] with X hX hell
    have he : -(A - 20 * κ + ((20 * κ - A) - errorExponent κ A X / ell X ^ 2)) *
        ell X ^ 2 = errorExponent κ A X := by
      field_simp [hell.ne']
      <;> ring
    rw [he]
    exact (ahlSmall_budget_le_ahlBudget κ 20 X).trans hX

end
end PrimeGapNormality.Prime.CoreWeakHL
