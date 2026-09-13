import PrimeGapNormality.Prime.CoreRoughThresholdRegularity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite locality of a derivative-controlled rough cutoff

The real endpoints are retained throughout.  In particular, the natural
floor bounds below do not replace the real anchor `exp(Ψ(log a))` by its
floor inside a real power.
-/

namespace PrimeGapNormality.Prime.CoreRoughCutoffLocality

open Set

open CoreRoughThresholdRegularity

noncomputable section

/-- Literal natural cutoff evaluated at a positive real endpoint. -/
def realEndpointCutoff (Ψ : ℝ → ℝ) (x : ℝ) : ℕ :=
  ⌊Real.exp (Ψ (Real.log x))⌋₊

private theorem log_sub_le_relative_increment
    {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hδ : b - a ≤ δ * a) :
    Real.log b - Real.log a ≤ δ := by
  have hb : 0 < b := ha.trans_le hab
  have hquot : 0 < b / a := div_pos hb ha
  have hlog := Real.log_le_sub_one_of_pos hquot
  have hform : b / a - 1 = (b - a) / a := by
    field_simp [ha.ne'] <;> ring
  rw [Real.log_div hb.ne' ha.ne', hform] at hlog
  exact hlog.trans ((div_le_iff₀ ha).2 hδ)

/-- Logarithmic-endpoint form of the finite regularity comparison. -/
theorem psi_log_interval_comparison
    {Ψ dΨ : ℝ → ℝ} {a b δ C : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hδ0 : 0 ≤ δ)
    (hba : b - a ≤ δ * a) (hC : 0 ≤ C)
    (hpos : ∀ t ∈ Icc (Real.log a) (Real.log b), 0 < Ψ t)
    (hderiv : ∀ t ∈ Icc (Real.log a) (Real.log b),
      HasDerivAt Ψ (dΨ t) t)
    (hweighted : ∀ t ∈ Icc (Real.log a) (Real.log b),
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t) :
    Ψ (Real.log a) ≤ Ψ (Real.log b) ∧
      Ψ (Real.log b) ≤
        Ψ (Real.log a) * Real.exp (C * δ / Real.log a) := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hb : 0 < b := (zero_lt_one.trans ha).trans_le hab
  have hlogab : Real.log a ≤ Real.log b := Real.log_le_log (zero_lt_one.trans ha) hab
  have hbase := psi_interval_comparison hloga hlogab hC hpos hderiv hweighted
  have hdiff : Real.log b - Real.log a ≤ δ :=
    log_sub_le_relative_increment (zero_lt_one.trans ha) hab hba
  have hexponent : C * (Real.log b - Real.log a) / Real.log a ≤
      C * δ / Real.log a := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdiff hC) hloga.le
  have hexp := Real.exp_le_exp.mpr hexponent
  have hΨa : 0 ≤ Ψ (Real.log a) :=
    (hpos _ ⟨le_rfl, hlogab⟩).le
  exact ⟨hbase.1, hbase.2.trans
    (mul_le_mul_of_nonneg_left hexp hΨa)⟩

private theorem exp_le_one_add_two_mul {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4) :
    Real.exp u ≤ 1 + 2 * u := by
  have hrat := Real.exp_le_two_add_div_two_sub hu0 (by linarith : u < 2)
  have hden : 0 < 2 - u := by linarith
  have hfrac : (2 + u) / (2 - u) ≤ 1 + 2 * u := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg u]
  exact hrat.trans hfrac

/-- Under the paper's small local budget, the endpoint ratio is within the
explicit linearized exponential error. -/
theorem psi_log_interval_ratio_linear
    {Ψ dΨ : ℝ → ℝ} {a b δ C : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hδ0 : 0 ≤ δ)
    (hba : b - a ≤ δ * a) (hC : 0 ≤ C)
    (hsmall : C * δ / Real.log a ≤ 1 / 4)
    (hpos : ∀ t ∈ Icc (Real.log a) (Real.log b), 0 < Ψ t)
    (hderiv : ∀ t ∈ Icc (Real.log a) (Real.log b),
      HasDerivAt Ψ (dΨ t) t)
    (hweighted : ∀ t ∈ Icc (Real.log a) (Real.log b),
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t) :
    1 ≤ Ψ (Real.log b) / Ψ (Real.log a) ∧
      Ψ (Real.log b) / Ψ (Real.log a) ≤
        1 + 2 * (C * δ / Real.log a) := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogab : Real.log a ≤ Real.log b :=
    Real.log_le_log (zero_lt_one.trans ha) hab
  have hcmp := psi_log_interval_comparison ha hab hδ0 hba hC
    hpos hderiv hweighted
  have hΨa : 0 < Ψ (Real.log a) := hpos _ ⟨le_rfl, hlogab⟩
  have heta0 : 0 ≤ C * δ / Real.log a := by positivity
  have hexp := exp_le_one_add_two_mul heta0 hsmall
  constructor
  · exact (le_div_iff₀ hΨa).2 (by simpa only [one_mul] using hcmp.1)
  · have hratio : Ψ (Real.log b) / Ψ (Real.log a) ≤
        Real.exp (C * δ / Real.log a) :=
      (div_le_iff₀ hΨa).2 (by simpa only [mul_comm] using hcmp.2)
    exact hratio.trans hexp

/-- Real exponential cutoff comparison, still anchored at the actual real
quantity `exp(Ψ(log a))`. -/
theorem exp_psi_log_interval_bounds
    {Ψ dΨ : ℝ → ℝ} {a b δ C : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hδ0 : 0 ≤ δ)
    (hba : b - a ≤ δ * a) (hC : 0 ≤ C)
    (hsmall : C * δ / Real.log a ≤ 1 / 4)
    (hpos : ∀ t ∈ Icc (Real.log a) (Real.log b), 0 < Ψ t)
    (hderiv : ∀ t ∈ Icc (Real.log a) (Real.log b),
      HasDerivAt Ψ (dΨ t) t)
    (hweighted : ∀ t ∈ Icc (Real.log a) (Real.log b),
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t) :
    Real.exp (Ψ (Real.log a)) ≤ Real.exp (Ψ (Real.log b)) ∧
      Real.exp (Ψ (Real.log b)) ≤
        (Real.exp (Ψ (Real.log a))) ^
          (1 + 2 * (C * δ / Real.log a)) := by
  have hratio := psi_log_interval_ratio_linear ha hab hδ0 hba hC hsmall
    hpos hderiv hweighted
  have hlogab : Real.log a ≤ Real.log b :=
    Real.log_le_log (zero_lt_one.trans ha) hab
  have hΨa : 0 < Ψ (Real.log a) := hpos _ ⟨le_rfl, hlogab⟩
  have hΨupper : Ψ (Real.log b) ≤
      Ψ (Real.log a) * (1 + 2 * (C * δ / Real.log a)) := by
    simpa only [mul_comm] using (div_le_iff₀ hΨa).mp hratio.2
  constructor
  · exact Real.exp_le_exp.mpr
      (psi_log_interval_comparison ha hab hδ0 hba hC
        hpos hderiv hweighted).1
  · have h := Real.exp_le_exp.mpr hΨupper
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    exact h

/-- Literal natural-floor version of the same comparison.  The upper
endpoint is the floor of the real anchored power, not a power of the lower
natural floor. -/
theorem realEndpointCutoff_bounds
    {Ψ dΨ : ℝ → ℝ} {a b δ C : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hδ0 : 0 ≤ δ)
    (hba : b - a ≤ δ * a) (hC : 0 ≤ C)
    (hsmall : C * δ / Real.log a ≤ 1 / 4)
    (hpos : ∀ t ∈ Icc (Real.log a) (Real.log b), 0 < Ψ t)
    (hderiv : ∀ t ∈ Icc (Real.log a) (Real.log b),
      HasDerivAt Ψ (dΨ t) t)
    (hweighted : ∀ t ∈ Icc (Real.log a) (Real.log b),
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t) :
    realEndpointCutoff Ψ a ≤ realEndpointCutoff Ψ b ∧
      realEndpointCutoff Ψ b ≤
        ⌊(Real.exp (Ψ (Real.log a))) ^
          (1 + 2 * (C * δ / Real.log a))⌋₊ := by
  have hreal := exp_psi_log_interval_bounds ha hab hδ0 hba hC hsmall
    hpos hderiv hweighted
  unfold realEndpointCutoff
  exact ⟨Nat.floor_le_floor hreal.1, Nat.floor_le_floor hreal.2⟩

end

end PrimeGapNormality.Prime.CoreRoughCutoffLocality
