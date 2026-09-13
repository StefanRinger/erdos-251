import PrimeGapNormality.Prime.CoreRoughThreshold
import PrimeGapNormality.Prime.CoreRoughScaleLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Subpower growth of the literal threshold follows from the slope
budget. The derived logarithmic upper bound on its mean-gap model scale
is unconditional; it is not a density assertion for the rough set. -/

namespace PrimeGapNormality.Prime.CoreRoughSubpower

open Filter CoreRoughThreshold CoreRoughSyntheticScale CoreRoughScaleLimits
open scoped Topology
noncomputable section

theorem eventually_psi_le_mul {Ψ : ℝ → ℝ} {A ε : ℝ}
    (h : HasSlopeBudget Ψ A) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, Ψ t ≤ ε * t := by
  have hlarge := h.2.1.eventually_ge_atTop (Real.exp (1 / (A * ε)))
  filter_upwards [hlarge, h.2.2] with t ht hbudget
  have hΨ : 0 < Ψ t := (Real.exp_pos _).trans_le ht
  have hlog : 1 / (A * ε) ≤ Real.log (3 * Ψ t) := by
    calc
      _ = Real.log (Real.exp (1 / (A * ε))) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hlog h.1.le
  have hcancel : A * (1 / (A * ε)) = 1 / ε := by
    field_simp [h.1.ne', hε.ne']
  rw [hcancel] at hmul
  have hstep := (le_div_iff₀ hΨ).mp (hmul.trans hbudget)
  have hfinal := mul_le_mul_of_nonneg_left hstep hε.le
  have hcancel2 : ε * ((1 / ε) * Ψ t) = Ψ t := by
    field_simp [hε.ne']
  rwa [hcancel2] at hfinal

theorem eventually_zPsi_le_rpow {Ψ : ℝ → ℝ} {A ε : ℝ}
    (h : HasSlopeBudget Ψ A) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (zPsi Ψ n : ℝ) ≤ (n : ℝ) ^ ε := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlog.eventually (eventually_psi_le_mul h hε),
    eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    (zPsi Ψ n : ℝ) ≤ Real.exp (Ψ (Real.log (n : ℝ))) :=
      Nat.floor_le (Real.exp_pos _).le
    _ ≤ Real.exp (ε * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hn
    _ = (n : ℝ) ^ ε := by rw [Real.rpow_def_of_pos hnpos]; ring_nf

theorem eventually_model_gap_le_log {Ψ : ℝ → ℝ} {A : ℝ}
    (h : HasSlopeBudget Ψ A) :
    ∀ᶠ n : ℕ in atTop,
      roughGapScale (zPsi Ψ n) ≤ Real.log (n : ℝ) / eulerProdLowerConst := by
  filter_upwards [h.tendsto_zPsi_atTop.eventually_ge_atTop 16,
    h.eventually_zPsi_lt] with n hz hn
  have hbound := roughGapScale_le_log_div_lowerConst hz
  have hzpos : (0 : ℝ) < zPsi Ψ n :=
    Nat.cast_pos.mpr (show 0 < zPsi Ψ n by omega)
  have hlogs : Real.log (zPsi Ψ n : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hzpos (Nat.cast_le.mpr hn.le)
  exact hbound.trans (div_le_div_of_nonneg_right hlogs eulerProdLowerConst_pos.le)

end
end PrimeGapNormality.Prime.CoreRoughSubpower
