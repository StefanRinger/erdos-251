import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Literal moving rough thresholds from a slope budget

For a real threshold profile `Ψ`, this file defines the paper's literal
natural cutoff

`zΨ(n) = floor(exp(Ψ(log n)))`.

An eventual lower bound on `t/Ψ(t)` by a positive multiple of
`log(3Ψ(t))`, together with `Ψ(t)→∞`, forces `Ψ(t)≤t/2`
eventually.  Consequently `zΨ(n)<n` eventually, while `zΨ(n)→∞`.
No derivative, density, or prime-distribution input is used.
-/

namespace PrimeGapNormality.Prime.CoreRoughThreshold

open Filter
open scoped Topology

noncomputable section

/-- Literal natural roughness cutoff attached to a real profile `Ψ`. -/
def zPsi (Ψ : ℝ → ℝ) (n : ℕ) : ℕ :=
  ⌊Real.exp (Ψ (Real.log (n : ℝ)))⌋₊

/-- The exact eventual slope budget needed by this threshold layer.  Bounds
on derivatives or local distortion belong to a later density module. -/
def HasSlopeBudget (Ψ : ℝ → ℝ) (A : ℝ) : Prop :=
  0 < A ∧
    Tendsto Ψ atTop atTop ∧
      ∀ᶠ t : ℝ in atTop,
        A * Real.log (3 * Ψ t) ≤ t / Ψ t

/-- A positive slope budget forces the threshold profile below half of its
argument eventually. -/
theorem eventually_psi_le_half_of_slope
    {Ψ : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hΨ : Tendsto Ψ atTop atTop)
    (hslope : ∀ᶠ t : ℝ in atTop,
      A * Real.log (3 * Ψ t) ≤ t / Ψ t) :
    ∀ᶠ t : ℝ in atTop, Ψ t ≤ t / 2 := by
  have hlarge : ∀ᶠ t : ℝ in atTop, Real.exp (2 / A) ≤ Ψ t :=
    hΨ.eventually (eventually_ge_atTop (Real.exp (2 / A)))
  filter_upwards [hlarge, hslope] with t hΨlarge hslopeT
  have hΨpos : 0 < Ψ t := (Real.exp_pos (2 / A)).trans_le hΨlarge
  have hthree : Real.exp (2 / A) ≤ 3 * Ψ t := by
    calc
      Real.exp (2 / A) ≤ Ψ t := hΨlarge
      _ ≤ 3 * Ψ t := by linarith
  have hlog : 2 / A ≤ Real.log (3 * Ψ t) := by
    calc
      2 / A = Real.log (Real.exp (2 / A)) := (Real.log_exp _).symm
      _ ≤ Real.log (3 * Ψ t) :=
        Real.log_le_log (Real.exp_pos _) hthree
  have hcost : (2 : ℝ) ≤ A * Real.log (3 * Ψ t) := by
    have hmul := mul_le_mul_of_nonneg_left hlog hA.le
    have hcancel : A * (2 / A) = 2 := by field_simp [hA.ne']
    rwa [hcancel] at hmul
  have hratio : (2 : ℝ) ≤ t / Ψ t := hcost.trans hslopeT
  have htwice : 2 * Ψ t ≤ t := (le_div_iff₀ hΨpos).mp hratio
  linarith

/-- The literal natural cutoff tends to infinity whenever `Ψ→∞`.
This part does not require the slope inequality. -/
theorem tendsto_zPsi_atTop {Ψ : ℝ → ℝ}
    (hΨ : Tendsto Ψ atTop atTop) :
    Tendsto (zPsi Ψ) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hexp : Tendsto
      (fun n : ℕ ↦ Real.exp (Ψ (Real.log (n : ℝ)))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hΨ.comp hlog)
  apply (tendsto_nat_floor_atTop.comp hexp).congr'
  exact Eventually.of_forall fun n ↦ rfl

/-- The slope budget makes the literal cutoff strictly smaller than its
natural argument eventually. -/
theorem eventually_zPsi_lt
    {Ψ : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hΨ : Tendsto Ψ atTop atTop)
    (hslope : ∀ᶠ t : ℝ in atTop,
      A * Real.log (3 * Ψ t) ≤ t / Ψ t) :
    ∀ᶠ n : ℕ in atTop, zPsi Ψ n < n := by
  have hhalf := eventually_psi_le_half_of_slope hA hΨ hslope
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hhalfNat : ∀ᶠ n : ℕ in atTop,
      Ψ (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 2 :=
    hlog.eventually hhalf
  filter_upwards [hhalfNat, eventually_ge_atTop 3] with n hnHalf hn3
  have hnpos : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 3) hn3)
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr
      (lt_of_lt_of_le (by norm_num : 1 < 3) hn3))
  have hpsiLt : Ψ (Real.log (n : ℝ)) < Real.log (n : ℝ) :=
    hnHalf.trans_lt (half_lt_self hlogpos)
  have hexpLt : Real.exp (Ψ (Real.log (n : ℝ))) < (n : ℝ) := by
    calc
      Real.exp (Ψ (Real.log (n : ℝ))) <
          Real.exp (Real.log (n : ℝ)) := Real.exp_lt_exp.mpr hpsiLt
      _ = (n : ℝ) := Real.exp_log hnpos
  unfold zPsi
  exact (Nat.floor_lt'
    (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 3) hn3))).2 hexpLt

/-- Packaged eventual half-bound. -/
theorem HasSlopeBudget.eventually_psi_le_half
    {Ψ : ℝ → ℝ} {A : ℝ} (h : HasSlopeBudget Ψ A) :
    ∀ᶠ t : ℝ in atTop, Ψ t ≤ t / 2 :=
  eventually_psi_le_half_of_slope h.1 h.2.1 h.2.2

/-- Packaged eventual strict natural cutoff. -/
theorem HasSlopeBudget.eventually_zPsi_lt
    {Ψ : ℝ → ℝ} {A : ℝ} (h : HasSlopeBudget Ψ A) :
    ∀ᶠ n : ℕ in atTop, zPsi Ψ n < n :=
  CoreRoughThreshold.eventually_zPsi_lt h.1 h.2.1 h.2.2

/-- Packaged divergence of the literal natural cutoff. -/
theorem HasSlopeBudget.tendsto_zPsi_atTop
    {Ψ : ℝ → ℝ} {A : ℝ} (h : HasSlopeBudget Ψ A) :
    Tendsto (zPsi Ψ) atTop atTop :=
  CoreRoughThreshold.tendsto_zPsi_atTop h.2.1

end

end PrimeGapNormality.Prime.CoreRoughThreshold
