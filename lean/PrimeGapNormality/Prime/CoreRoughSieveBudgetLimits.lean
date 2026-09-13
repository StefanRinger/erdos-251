import PrimeGapNormality.Prime.CoreRoughSieveBudget

/-!
# Relative beta decay and actual admissible levels

The explicit slope condition forces log X / Ψ(log X) to infinity.
The already proved negative exponent therefore gives vanishing relative
cost, including exp(10L). The same budget supplies every required finite
beta level uniformly through the full growing tuple rank.
-/

namespace PrimeGapNormality.Prime.CoreRoughSieveBudgetLimits

open Filter CoreRoughThreshold CoreRoughSieveBudget CoreRoughProfileError
open scoped Topology
noncomputable section

set_option maxHeartbeats 800000

theorem tendsto_ratio_atTop {Ψ : ℝ → ℝ} {A : ℝ} (h : HasSlopeBudget Ψ A) :
    Tendsto (fun t : ℝ => t / Ψ t) atTop atTop := by
  have hthree : Tendsto (fun t : ℝ => 3 * Ψ t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3) h.2.1
  have hlarge : Tendsto (fun t : ℝ => A * Real.log (3 * Ψ t)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop h.1 (Real.tendsto_log_atTop.comp hthree)
  exact tendsto_atTop_mono' atTop h.2.2 hlarge

theorem tendsto_logX_div_psi_atTop {Ψ : ℝ → ℝ} {A : ℝ} (h : HasSlopeBudget Ψ A) :
    Tendsto (fun X : ℕ => Real.log (X : ℝ) / Ψ (Real.log (X : ℝ))) atTop atTop := by
  have hh := (tendsto_ratio_atTop h).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  exact hh.congr' (Eventually.of_forall fun X => rfl)

theorem tendsto_exp_negative_ratio_zero {Ψ : ℝ → ℝ} {A : ℝ} (h : HasSlopeBudget Ψ A) :
    Tendsto (fun X : ℕ => Real.exp (-(Real.log (X : ℝ) / Ψ (Real.log (X : ℝ))) / 16))
      atTop (𝓝 0) := by
  have hscaled := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 16)
    (tendsto_logX_div_psi_atTop h)
  have hneg := tendsto_neg_atTop_atBot.comp hscaled
  have hh := Real.tendsto_exp_atBot.comp hneg
  apply hh.congr'
  exact Eventually.of_forall fun X => by
    dsimp only [Function.comp_apply]
    congr 1
    ring

def relativeCost (κ : ℝ) (Ψ : ℝ → ℝ) (Z : ℕ → ℝ) (X : ℕ) : ℝ :=
  Real.exp (299 * ((profileRank κ Ψ X + 1 : ℕ) : ℝ) +
    10 * (roughProfileL κ (zPsi Ψ X) : ℝ) -
      Real.log (cubeRootLevel X : ℝ) / Real.log (Z X))

/-- Actual relative beta cost times the fixed exp(10L) envelope tends to
zero, for every admissible upper cutoff sequence. -/
theorem tendsto_relativeCost_zero {Ψ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSlopeBudget Ψ (1000000 * κ)) (Z : ℕ → ℝ)
    (hZ : ∀ᶠ X : ℕ in atTop, 1 < Z X ∧
      Z X ≤ Real.exp (2 * Ψ (Real.log (X : ℝ))) + 1) :
    Tendsto (relativeCost κ Ψ Z) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun X => (Real.exp_pos _).le) _
    (tendsto_exp_negative_ratio_zero h)
  filter_upwards [eventually_relative_exponent_budget h.2.1 hκ Z hZ h.2.2] with X hX
  exact Real.exp_le_exp.mpr hX

theorem tendsto_relative_beta_times_moment_zero {Ψ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSlopeBudget Ψ (1000000 * κ)) (Z : ℕ → ℝ)
    (hZ : ∀ᶠ X : ℕ in atTop, 1 < Z X ∧
      Z X ≤ Real.exp (2 * Ψ (Real.log (X : ℝ))) + 1) :
    Tendsto (fun X : ℕ =>
      Real.exp (299 * ((profileRank κ Ψ X + 1 : ℕ) : ℝ) -
        Real.log (cubeRootLevel X : ℝ) / Real.log (Z X)) *
      Real.exp (10 * (roughProfileL κ (zPsi Ψ X) : ℝ))) atTop (𝓝 0) := by
  apply (tendsto_relativeCost_zero hκ h Z hZ).congr'
  exact Eventually.of_forall fun X => by
    dsimp only [relativeCost]
    rw [← Real.exp_add]
    congr 1
    ring

theorem tendsto_cubeRootLevel_atTop : Tendsto cubeRootLevel atTop atTop := by
  have hh := tendsto_nat_floor_atTop.comp
    ((_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  exact hh.congr' (Eventually.of_forall fun X => rfl)

/-- The real level is proved from the same slope budget, uniformly for
every k at most r+1. It is not a premise of the moving-count application. -/
theorem eventually_all_tuple_levels {Ψ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSlopeBudget Ψ (1000000 * κ)) (Z : ℕ → ℝ)
    (hZ : ∀ᶠ X : ℕ in atTop, 1 < Z X ∧
      Z X ≤ Real.exp (2 * Ψ (Real.log (X : ℝ))) + 1) :
    ∀ᶠ X : ℕ in atTop, ∀ k : ℕ, k ≤ profileRank κ Ψ X + 1 →
      Z X ^ (9 * k + 1) ≤ (cubeRootLevel X : ℝ) := by
  have hlogX : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_relative_exponent_budget h.2.1 hκ Z hZ h.2.2, hZ,
    hlogX.eventually_ge_atTop 0, (h.2.1.comp hlogX).eventually_ge_atTop 1,
    tendsto_cubeRootLevel_atTop.eventually_ge_atTop 1] with X hbudget hz hlog hP hR
  simp only [Function.comp_apply] at hP
  intro k hk
  have hq : 0 ≤ Real.log (X : ℝ) / Ψ (Real.log (X : ℝ)) :=
    div_nonneg hlog (zero_le_one.trans hP)
  have hkR : (k : ℝ) ≤ ((profileRank κ Ψ X + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hk
  have hrR : (1 : ℝ) ≤ ((profileRank κ Ψ X + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_pos (profileRank κ Ψ X))
  have hL : 0 ≤ (roughProfileL κ (zPsi Ψ X) : ℝ) := Nat.cast_nonneg _
  have hdegree : ((9 * k + 1 : ℕ) : ℝ) ≤
      Real.log (cubeRootLevel X : ℝ) / Real.log (Z X) := by
    push_cast
    nlinarith
  have hloglevel := (le_div_iff₀ (Real.log_pos hz.1)).mp hdegree
  have hposR : 0 < (cubeRootLevel X : ℝ) := Nat.cast_pos.mpr hR
  apply (Real.log_le_log_iff (pow_pos (zero_lt_one.trans hz.1) _) hposR).mp
  simpa only [Real.log_pow] using hloglevel

end
end PrimeGapNormality.Prime.CoreRoughSieveBudgetLimits
