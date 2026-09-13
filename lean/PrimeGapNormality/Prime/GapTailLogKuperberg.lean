import PrimeGapNormality.Prime.PhysicalRemainderOfGapTail
import PrimeGapNormality.Prime.SingletonLi
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.OrderClosed

/-!
# Dyadic `GapTailT` at `windowG` from qualitative PNT

`PhysicalRemainderOfGapTail` closes the profile remainder from
`GapTailT`. At `G X = X` this is `gapTailT_nthPrime_linear`
(Chebyshev). At `windowG` the same file only has the implication
`..._windowG_of_GapTailT`, because dyadic Chebyshev yields `O_ρ(X)`
when `|I_X|` may be `1`.

`SingletonLi.primeCountingAsymp_of_kuperberg` supplies
`π(⌊x⌋) / (x / log x) → 1`. That density makes
`|I_X| = π(2X) - π(X) ∼ X / log X`. Combined with
`conditionT_seqWindow_nthPrime` and the Chebyshev-log `posMass`
bound, the first-gap-tail average is `O_ρ(log X) = O_ρ(windowG X)`.

Does **not** import `MixZeta` (that leaf inlines the same `Tendsto` as
`MixPrimeCountingAsymp` to avoid `Coupling.bernoulliThin` versus
`ActualRootLaw.actualBernoulliThin`). The window-count limit is
re-proved here from `IndexPassageFromPNT.PrimeCountingAsymp`.

Not compiled: Spark, joint spacing, rough backend, `UniformOrbitTail`,
`hU`/`hmatch`, `D` as a consumer input. Does not claim `GapTailT` from
Chebyshev alone, and does not replace `windowG` by `G X = X`.

Source: `SingletonLi`; `PrimeSTD.conditionT_seqWindow_nthPrime`;
`PhysicalRemainderOfGapTail`; `EndAPI.windowG`.
Contract: API
Audit: GREEN
-/

open Filter Polynomial
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### Elementary comparisons -/

private theorem one_lt_of_two_le {X : ℕ} (hX : 2 ≤ X) : (1 : ℝ) < X :=
  lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (Nat.cast_le.mpr hX)

private theorem X_pos {X : ℕ} (hX : 2 ≤ X) : (0 : ℝ) < X :=
  Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hX)

private theorem one_lt_two_mul_real {X : ℕ} (hX : 2 ≤ X) :
    (1 : ℝ) < 2 * (X : ℝ) :=
  lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 2)
      (one_lt_of_two_le hX).le)

private theorem log_X_pos {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log X :=
  Real.log_pos (one_lt_of_two_le hX)

private theorem log_two_mul_pos {X : ℕ} (hX : 2 ≤ X) :
    0 < Real.log (2 * (X : ℝ)) :=
  Real.log_pos (one_lt_two_mul_real hX)

private theorem one_le_log_of_three_le {X : ℕ} (hX : 3 ≤ X) :
    (1 : ℝ) ≤ Real.log X := by
  have h3 : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
    rwa [Real.log_exp] at h
  have hle : Real.log 3 ≤ Real.log X :=
    Real.log_le_log (by positivity : (0 : ℝ) < 3) (by exact_mod_cast hX)
  exact h3.trans hle

private theorem sqrt_le_add {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ x + 1 := by
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hnn : 0 ≤ (Real.sqrt x - 1) ^ 2 := sq_nonneg _
  have hexp : (Real.sqrt x - 1) ^ 2 =
      Real.sqrt x ^ 2 - 2 * Real.sqrt x + 1 := by
    ring
  have : 0 ≤ x - 2 * Real.sqrt x + 1 := by
    rwa [hexp, hsq] at hnn
  have h2 : 2 * Real.sqrt x ≤ x + 1 := by linarith
  have h0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  linarith

private theorem add_sqrt_le {x : ℝ} (hx : 0 ≤ x) :
    x + Real.sqrt x ≤ 2 * x + 1 := by
  linarith [sqrt_le_add hx]

private theorem stdProfileL_cast_le {ρ G : ℝ} (hG : 0 ≤ logρ ρ G) :
    (stdProfileL ρ G : ℝ) ≤ logρ ρ G + Real.sqrt (logρ ρ G) + 1 := by
  have ha : 0 ≤ logρ ρ G + Real.sqrt (logρ ρ G) :=
    add_nonneg hG (Real.sqrt_nonneg _)
  simpa [stdProfileL] using (Nat.ceil_lt_add_one (R := ℝ) ha).le

private theorem logρ_log_nonneg {ρ : ℝ} {X : ℕ} (hρ : 1 < ρ) (hX : 3 ≤ X) :
    0 ≤ logρ ρ (Real.log X) :=
  div_nonneg (Real.log_nonneg (one_le_log_of_three_le hX)) (Real.log_pos hρ).le

/-! ### `π(⌊x⌋) ∼ x / log x` on naturals and on `2X` -/

private theorem tendsto_two_mul_nat_atTop :
    Tendsto (fun X : ℕ => 2 * X) atTop atTop :=
  tendsto_atTop_atTop_of_monotone
    (fun _ _ h => Nat.mul_le_mul_left 2 h)
    fun n => ⟨n, Nat.le_mul_of_pos_left n (by norm_num : (0 : ℕ) < 2)⟩

/-- Natural argument: `π(X) / (X / log X) → 1`. -/
theorem tendsto_primeCounting_div_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    Tendsto (fun X : ℕ =>
      (Nat.primeCounting X : ℝ) / ((X : ℝ) / Real.log X)) atTop (𝓝 1) := by
  have h := hπ.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr fun X => ?_
  simp [Function.comp_apply, Nat.floor_natCast]

/-- Dilated argument: `π(2X) / (2X / log(2X)) → 1`. -/
theorem tendsto_primeCounting_two_mul_div_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    Tendsto (fun X : ℕ =>
      (Nat.primeCounting (2 * X) : ℝ) /
        ((2 * (X : ℝ)) / Real.log (2 * (X : ℝ)))) atTop (𝓝 1) := by
  have hx : Tendsto (fun X : ℕ => (2 : ℝ) * X) atTop atTop :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_two_mul_nat_atTop).congr
      fun X => two_mul_cast X
  have h := hπ.comp hx
  refine h.congr fun X => ?_
  have hfloor : ⌊(2 : ℝ) * X⌋₊ = 2 * X := by
    rw [← two_mul_cast, Nat.floor_natCast]
  simp [Function.comp_apply, hfloor]

private theorem tendsto_log_div_log_two_mul :
    Tendsto (fun X : ℕ => Real.log X / Real.log (2 * (X : ℝ)))
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    tendsto_log_nat_atTop
  have hinv : Tendsto (fun X : ℕ => Real.log 2 / Real.log X) atTop (𝓝 0) := by
    have h0 : Tendsto (fun X : ℕ => (Real.log X)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hlog
    simpa [div_eq_mul_inv] using h0.const_mul (Real.log 2)
  have hadd : Tendsto (fun X : ℕ => (1 : ℝ) + Real.log 2 / Real.log X)
      atTop (𝓝 1) := by
    simpa using Tendsto.add (tendsto_const_nhds (x := (1 : ℝ))) hinv
  have hinv1 : Tendsto (fun X : ℕ => ((1 : ℝ) + Real.log 2 / Real.log X)⁻¹)
      atTop (𝓝 1) := by
    simpa using hadd.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  refine hinv1.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hlogX := log_X_pos hX
  have hlog2X : Real.log (2 * (X : ℝ)) = Real.log 2 + Real.log X :=
    Real.log_mul (by norm_num) (X_pos hX).ne'
  have hden : (1 : ℝ) + Real.log 2 / Real.log X =
      (Real.log X + Real.log 2) / Real.log X := by
    have hone : (1 : ℝ) = Real.log X / Real.log X := (div_self hlogX.ne').symm
    rw [hone, add_div]
  rw [hlog2X, hden, inv_div, add_comm]

private theorem windowNX_div_eq {X : ℕ} (hX : 2 ≤ X) :
    (windowNX X : ℝ) / ((X : ℝ) / Real.log X) =
      (Nat.primeCounting (2 * X) : ℝ) /
          ((2 * (X : ℝ)) / Real.log (2 * (X : ℝ))) *
        (2 : ℝ) * (Real.log X / Real.log (2 * (X : ℝ))) -
      (Nat.primeCounting X : ℝ) / ((X : ℝ) / Real.log X) := by
  have hx := (X_pos hX).ne'
  have hL := (log_X_pos hX).ne'
  have hL2 := (log_two_mul_pos hX).ne'
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hx2 : (2 : ℝ) * (X : ℝ) ≠ 0 := mul_ne_zero h2 hx
  have hle : Nat.primeCounting X ≤ Nat.primeCounting (2 * X) :=
    Nat.monotone_primeCounting
      (Nat.le_mul_of_pos_left X (by norm_num : (0 : ℕ) < 2))
  have hcast : (windowNX X : ℝ) =
      (Nat.primeCounting (2 * X) : ℝ) - (Nat.primeCounting X : ℝ) := by
    rw [windowNX, Nat.cast_sub hle]
  rw [hcast]
  set π2 : ℝ := (Nat.primeCounting (2 * X) : ℝ)
  set π1 : ℝ := (Nat.primeCounting X : ℝ)
  set x : ℝ := (X : ℝ)
  set L : ℝ := Real.log (X : ℝ)
  set L2 : ℝ := Real.log (2 * (X : ℝ))
  have hsplit : (π2 - π1) / (x / L) = π2 * L / x - π1 * L / x := by
    have h : (π2 - π1) / (x / L) = (π2 - π1) * L / x := by
      field_simp [hx, hL]
    rw [h, sub_mul, sub_div]
  have hπ1 : π1 * L / x = π1 / (x / L) := by
    field_simp [hx, hL]
  have hπ2 : π2 * L / x = π2 / (2 * x / L2) * 2 * (L / L2) := by
    have hr : π2 / (2 * x / L2) * 2 * (L / L2) = π2 * L / x := by
      rw [div_div_eq_mul_div]
      field_simp [hx, hL, hL2, h2, hx2]
    exact hr.symm
  rw [hsplit, hπ1, hπ2]

/-- Public form of MixZeta’s private window-count limit, from
`IndexPassageFromPNT.PrimeCountingAsymp` rather than the MixZeta
inline. `|I_X| / (X / log X) → 1`. -/
theorem tendsto_windowNX_div_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    Tendsto (fun X : ℕ =>
      (windowNX X : ℝ) / ((X : ℝ) / Real.log X)) atTop (𝓝 1) := by
  have ha := tendsto_primeCounting_two_mul_div_of_primeCountingAsymp hπ
  have hb := tendsto_primeCounting_div_of_primeCountingAsymp hπ
  have hc := tendsto_log_div_log_two_mul
  have hmul : Tendsto (fun X : ℕ =>
      (Nat.primeCounting (2 * X) : ℝ) /
          ((2 * (X : ℝ)) / Real.log (2 * (X : ℝ))) *
        (2 : ℝ) * (Real.log X / Real.log (2 * (X : ℝ))))
      atTop (𝓝 2) := by
    have h := ((ha.mul (tendsto_const_nhds (x := (2 : ℝ)))).mul hc)
    simpa using h
  have hsub : Tendsto (fun X : ℕ =>
      (Nat.primeCounting (2 * X) : ℝ) /
          ((2 * (X : ℝ)) / Real.log (2 * (X : ℝ))) *
        (2 : ℝ) * (Real.log X / Real.log (2 * (X : ℝ))) -
      (Nat.primeCounting X : ℝ) / ((X : ℝ) / Real.log X))
      atTop (𝓝 1) := by
    have h := hmul.sub hb
    have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    rw [h21] at h
    exact h
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with X hX
  exact (windowNX_div_eq hX).symm

theorem tendsto_seqWindow_nthPrime_card_div_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    Tendsto (fun X : ℕ =>
      ((seqWindow nthPrime X).card : ℝ) / ((X : ℝ) / Real.log X))
      atTop (𝓝 1) := by
  simpa [seqWindow_nthPrime_card] using
    tendsto_windowNX_div_of_primeCountingAsymp hπ

/-! ### Eventual comparisons from the density -/

private theorem eventually_seqWindow_nthPrime_card_ge_half
    (hπ : PrimeCountingAsymp) :
    ∀ᶠ X : ℕ in atTop,
      (1 : ℝ) / 2 * ((X : ℝ) / Real.log X) ≤
        (seqWindow nthPrime X).card := by
  have hratio :=
    (tendsto_seqWindow_nthPrime_card_div_of_primeCountingAsymp hπ).eventually_const_le
      (by norm_num : (1 : ℝ) / 2 < 1)
  filter_upwards [hratio, eventually_ge_atTop 2] with X hle hX
  have hb : 0 < (X : ℝ) / Real.log X :=
    div_pos (X_pos hX) (log_X_pos hX)
  exact (le_div_iff₀ hb).mp hle

private theorem eventually_primeCounting_two_mul_le
    (hπ : PrimeCountingAsymp) :
    ∀ᶠ X : ℕ in atTop,
      (Nat.primeCounting (2 * X) : ℝ) ≤
        4 * (X : ℝ) / Real.log (2 * (X : ℝ)) := by
  have hratio :=
    (tendsto_primeCounting_two_mul_div_of_primeCountingAsymp hπ).eventually_le_const
      (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hratio, eventually_ge_atTop 2] with X hle hX
  have hx0 := X_pos hX
  have hL2 := log_two_mul_pos hX
  have hden : 0 < (2 * (X : ℝ)) / Real.log (2 * (X : ℝ)) :=
    div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hx0) hL2
  have hmul := (div_le_iff₀ hden).mp hle
  have hrew : (2 : ℝ) * ((2 * (X : ℝ)) / Real.log (2 * (X : ℝ))) =
      4 * (X : ℝ) / Real.log (2 * (X : ℝ)) := by
    ring
  exact hmul.trans_eq hrew

/-! ### Profile length `L_X = o(X / log X)` at `windowG` -/

private theorem tendsto_log_div_self :
    Tendsto (fun X : ℕ => Real.log X / X) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  exact (h0.comp tendsto_natCast_atTop_atTop).congr fun X => by
    rw [Function.comp_apply]

private theorem tendsto_log_sq_div_self :
    Tendsto (fun X : ℕ => Real.log X ^ 2 / X) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (𝓝 0) := by
    simpa [one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 2 (by norm_num)
  exact (h0.comp tendsto_natCast_atTop_atTop).congr fun X => by
    rw [Function.comp_apply]

private theorem tendsto_log_log_div_log :
    Tendsto (fun X : ℕ => Real.log (Real.log X) / Real.log X)
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  exact (h0.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).congr
    fun X => by
      rw [Function.comp_apply, Function.comp_apply]

private theorem tendsto_log_log_mul_log_div_self :
    Tendsto (fun X : ℕ => Real.log (Real.log X) * Real.log X / X)
      atTop (𝓝 0) := by
  have hfun :
      (fun X : ℕ => Real.log (Real.log X) * Real.log X / X) =ᶠ[atTop]
        fun X =>
          (Real.log (Real.log X) / Real.log X) * (Real.log X ^ 2 / X) := by
    filter_upwards [eventually_ge_atTop 3] with X hX
    have hlog : Real.log X ≠ 0 :=
      (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3)
        (by exact_mod_cast hX))).ne'
    have hx0 : (X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hlog, hx0]
  have hmul : Tendsto (fun X : ℕ =>
      (Real.log (Real.log X) / Real.log X) * (Real.log X ^ 2 / X))
      atTop (𝓝 (0 * 0)) :=
    tendsto_log_log_div_log.mul tendsto_log_sq_div_self
  have hmul0 : Tendsto (fun X : ℕ =>
      (Real.log (Real.log X) / Real.log X) * (Real.log X ^ 2 / X))
      atTop (𝓝 0) := by
    simpa using hmul
  exact hmul0.congr' hfun.symm

private theorem eventually_stdProfileL_windowG_le {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      (stdProfileL ρ (windowG X) : ℝ) + 1 ≤ (X : ℝ) / Real.log X := by
  have hnum : Tendsto (fun X : ℕ =>
      (2 * Real.log (Real.log X) / Real.log ρ + 3) * Real.log X / X)
      atTop (𝓝 0) := by
    have hfun :
        (fun X : ℕ =>
            (2 * Real.log (Real.log X) / Real.log ρ + 3) * Real.log X / X) =
          (fun X : ℕ =>
            (2 / Real.log ρ) * (Real.log (Real.log X) * Real.log X / X) +
              3 * (Real.log X / X)) := by
      funext X
      ring
    rw [hfun]
    have hsum :
        Tendsto (fun X : ℕ =>
            (2 / Real.log ρ) * (Real.log (Real.log X) * Real.log X / X) +
              3 * (Real.log X / X))
          atTop (𝓝 ((2 / Real.log ρ) * 0 + 3 * 0)) :=
      (tendsto_log_log_mul_log_div_self.const_mul (2 / Real.log ρ)).add
        (tendsto_log_div_self.const_mul (3 : ℝ))
    simpa using hsum
  have hsmall : ∀ᶠ X : ℕ in atTop,
      (2 * Real.log (Real.log X) / Real.log ρ + 3) * Real.log X / X < 1 :=
    hnum.eventually_lt_const (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop 3] with X hlt hX
  have hG : windowG X = Real.log X := windowG_eq_log hX
  rw [hG]
  have hx : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hX)
  have hx0 : (0 : ℝ) < X := lt_trans (by norm_num) hx
  have hlogX : 0 < Real.log X := Real.log_pos hx
  have hlogρ0 : 0 ≤ logρ ρ (Real.log X) := logρ_log_nonneg hρ hX
  have hL := stdProfileL_cast_le hlogρ0
  have hL2 : (stdProfileL ρ (Real.log X) : ℝ) ≤
      2 * logρ ρ (Real.log X) + 2 := by
    have h1 :
        logρ ρ (Real.log X) + Real.sqrt (logρ ρ (Real.log X)) + 1 ≤
          2 * logρ ρ (Real.log X) + 1 + 1 :=
      _root_.add_le_add (add_sqrt_le hlogρ0) (le_rfl : (1 : ℝ) ≤ 1)
    have heq : 2 * logρ ρ (Real.log X) + 1 + 1 =
        2 * logρ ρ (Real.log X) + 2 := by
      ring
    exact hL.trans (h1.trans_eq heq)
  have hbound : (stdProfileL ρ (Real.log X) : ℝ) + 1 ≤
      2 * Real.log (Real.log X) / Real.log ρ + 3 := by
    have h1 : (stdProfileL ρ (Real.log X) : ℝ) + 1 ≤
        2 * logρ ρ (Real.log X) + 2 + 1 :=
      _root_.add_le_add hL2 (le_rfl : (1 : ℝ) ≤ 1)
    have heq : 2 * logρ ρ (Real.log X) + 2 + 1 =
        2 * Real.log (Real.log X) / Real.log ρ + 3 := by
      simp only [logρ, mul_div_assoc]
      ring
    exact h1.trans_eq heq
  have hmul :
      ((stdProfileL ρ (Real.log X) : ℝ) + 1) * Real.log X / X ≤
        (2 * Real.log (Real.log X) / Real.log ρ + 3) * Real.log X / X :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbound hlogX.le) hx0.le
  have hprod :
      ((stdProfileL ρ (Real.log X) : ℝ) + 1) * Real.log X / X < 1 :=
    lt_of_le_of_lt hmul hlt
  have hmul' : ((stdProfileL ρ (Real.log X) : ℝ) + 1) * Real.log X < X :=
    (div_lt_one hx0).mp hprod
  exact le_of_lt ((lt_div_iff₀ hlogX).mpr hmul')

/-! ### Explicit `O_ρ(1)` factor at log scale -/

/-- `O_ρ(1)` factor: dyadic gap-tail average `≤ C_ρ · windowG X`. -/
noncomputable def gapTailLogKuperbergCoeff (ρ : ℝ) : ℝ :=
  40 * posMassChebyshevCoeff ρ

theorem gapTailLogKuperbergCoeff_nonneg {ρ : ℝ} (hρ : 1 < ρ) :
    0 ≤ gapTailLogKuperbergCoeff ρ :=
  mul_nonneg (by norm_num : (0 : ℝ) ≤ 40) (posMassChebyshevCoeff_nonneg hρ)

private theorem log_six_add_one_le :
    Real.log 6 + 1 ≤ 3 * Real.log 3 := by
  have h1 : (1 : ℝ) ≤ Real.log 3 :=
    one_le_log_of_three_le (le_rfl : (3 : ℕ) ≤ 3)
  have h18 : Real.log 6 + 1 ≤ Real.log 6 + Real.log 3 :=
    _root_.add_le_add le_rfl h1
  have hmul : Real.log 6 + Real.log 3 = Real.log (18 : ℝ) := by
    have h := Real.log_mul (by norm_num : (6 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0)
    have h18 : (6 : ℝ) * 3 = 18 := by norm_num
    rw [h18] at h
    exact h.symm
  have h18_27 : Real.log (18 : ℝ) ≤ Real.log (27 : ℝ) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 18) (by norm_num : (18 : ℝ) ≤ 27)
  have h27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    have hpow : (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [hpow, Real.log_pow]
    norm_cast
  exact (h18.trans_eq hmul).trans (h18_27.trans_eq h27)

/-- First-gap-tail window average is `O_ρ(windowG)` once
`π(⌊x⌋) ∼ x / log x`. Explicit nonnegative `C`. -/
theorem eventually_gapTail_avg_nthPrime_windowG_of_primeCountingAsymp
    {ρ : ℝ} (hρ : 1 < ρ) (hπ : PrimeCountingAsymp) :
    ∀ᶠ X : ℕ in atTop,
      0 < (seqWindow nthPrime X).card ∧
        windowAvgReal (seqWindow nthPrime X)
            (fun n => seqGapTail ρ nthPrime
              (n + stdProfileL ρ (windowG X))) ≤
          gapTailLogKuperbergCoeff ρ * windowG X := by
  have hπ2 := eventually_primeCounting_two_mul_le hπ
  have hL := eventually_stdProfileL_windowG_le hρ
  have hden := eventually_seqWindow_nthPrime_card_ge_half hπ
  filter_upwards [hπ2, hL, hden, eventually_ge_atTop 3] with
    X hπbd hLle hcardge hX
  have hm : 0 < (seqWindow nthPrime X).card :=
    card_seqWindow_nthPrime_pos (lt_of_lt_of_le (by omega : 0 < 3) hX)
  refine ⟨hm, ?_⟩
  have hx : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hX)
  have hx0 : (0 : ℝ) < X := lt_trans (by norm_num) hx
  have hlogX : 0 < Real.log X := Real.log_pos hx
  have hlogge1 : (1 : ℝ) ≤ Real.log X := one_le_log_of_three_le hX
  have hG : windowG X = Real.log X := windowG_eq_log hX
  have h2X : (1 : ℝ) < 2 * (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 2) hx.le)
  have hlog2X : 0 < Real.log (2 * (X : ℝ)) := Real.log_pos h2X
  have hlog_mono : Real.log X ≤ Real.log (2 * (X : ℝ)) :=
    Real.log_le_log hx0
      (le_mul_of_one_le_left hx0.le (by norm_num : (1 : ℝ) ≤ 2))
  set L := stdProfileL ρ (windowG X)
  set N : ℕ := Nat.primeCounting (2 * X) + L
  have hT : windowAvgReal (seqWindow nthPrime X)
        (fun n => seqGapTail ρ nthPrime (n + L)) ≤
      posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
          (Real.log ((N + 2 : ℕ) : ℝ) + 1) /
        ((seqWindow nthPrime X).card : ℝ) := by
    simpa [seqWindowMul_two, N] using
      (conditionT_seqWindowMul_nthPrime_chebyshev_log hρ 2 X L
        (by simpa [seqWindowMul_two] using hm))
  have hN1 : ((N + 1 : ℕ) : ℝ) =
      (Nat.primeCounting (2 * X) : ℝ) + (L : ℝ) + 1 := by
    dsimp only [N]
    rw [Nat.cast_add_one (Nat.primeCounting (2 * X) + L), Nat.cast_add]
  have hπ4 : (Nat.primeCounting (2 * X) : ℝ) ≤
      4 * (X : ℝ) / Real.log X :=
    hπbd.trans (div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hx0.le) hlogX hlog_mono)
  have hL1 : (L : ℝ) + 1 ≤ (X : ℝ) / Real.log X := hLle
  have hNbd : ((N + 1 : ℕ) : ℝ) ≤ 5 * (X : ℝ) / Real.log X := by
    have hadd := _root_.add_le_add hπ4 hL1
    have hsum :
        4 * (X : ℝ) / Real.log X + (X : ℝ) / Real.log X =
          5 * (X : ℝ) / Real.log X := by
      ring
    have hassoc : (Nat.primeCounting (2 * X) : ℝ) + (L : ℝ) + 1 =
        (Nat.primeCounting (2 * X) : ℝ) + ((L : ℝ) + 1) := by
      ring
    rw [hN1, hassoc]
    exact hadd.trans_eq hsum
  have hN2le : ((N + 2 : ℕ) : ℝ) ≤ 6 * (X : ℝ) := by
    have hN2 : ((N + 2 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) + 1 :=
      Nat.cast_add_one (N + 1)
    have h5 : ((N + 1 : ℕ) : ℝ) ≤ 5 * (X : ℝ) :=
      hNbd.trans (div_le_self
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hx0.le) hlogge1)
    have hmid : ((N + 1 : ℕ) : ℝ) + 1 ≤ 5 * (X : ℝ) + 1 :=
      _root_.add_le_add h5 (le_rfl : (1 : ℝ) ≤ 1)
    have h6 : 5 * (X : ℝ) + 1 ≤ 6 * (X : ℝ) := by
      linarith [hx]
    rw [hN2]
    exact hmid.trans h6
  have hlogN : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤ 4 * Real.log X := by
    have hpos : (0 : ℝ) < (N + 2 : ℕ) := by
      exact_mod_cast (Nat.succ_pos (N + 1))
    have h1 : Real.log ((N + 2 : ℕ) : ℝ) ≤ Real.log (6 * (X : ℝ)) :=
      Real.log_le_log hpos hN2le
    have hlog6X : Real.log (6 * (X : ℝ)) = Real.log 6 + Real.log X :=
      Real.log_mul (by norm_num) hx0.ne'
    have hcomb : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤
        Real.log 6 + Real.log X + 1 :=
      _root_.add_le_add (h1.trans_eq hlog6X) (le_rfl : (1 : ℝ) ≤ 1)
    have h61X : Real.log 6 + Real.log X + 1 ≤
        3 * Real.log 3 + Real.log X := by
      have heq : Real.log 6 + Real.log X + 1 =
          (Real.log 6 + 1) + Real.log X := by
        ring
      exact (le_of_eq heq).trans
        (_root_.add_le_add log_six_add_one_le (le_rfl : Real.log X ≤ Real.log X))
    have h3 : 3 * Real.log 3 ≤ 3 * Real.log X :=
      mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity : (0 : ℝ) < 3)
          (by exact_mod_cast hX)) (by norm_num : (0 : ℝ) ≤ 3)
    have h4 : 3 * Real.log 3 + Real.log X ≤ 4 * Real.log X := by
      have : 3 * Real.log X + Real.log X = 4 * Real.log X := by ring
      exact (_root_.add_le_add h3 (le_rfl : Real.log X ≤ Real.log X)).trans_eq
        this
    exact hcomb.trans (h61X.trans h4)
  have hprod :
      ((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤
        20 * (X : ℝ) := by
    have h1 := mul_le_mul hNbd hlogN
      (add_nonneg (Real.log_natCast_nonneg _) (by norm_num))
      (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hx0.le) hlogX.le)
    have h2 : (5 * (X : ℝ) / Real.log X) * (4 * Real.log X) =
        20 * (X : ℝ) := by
      have h0 : Real.log X ≠ 0 := hlogX.ne'
      field_simp [h0]
      norm_num
    exact h1.trans (le_of_eq h2)
  have hFnum :
      posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
          (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤
        posMassChebyshevCoeff ρ * 20 * (X : ℝ) := by
    have hassoc :
        posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
            (Real.log ((N + 2 : ℕ) : ℝ) + 1) =
          posMassChebyshevCoeff ρ *
            (((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1)) := by
      ring
    have hmul :=
      mul_le_mul_of_nonneg_left hprod (posMassChebyshevCoeff_nonneg hρ)
    have hRHS :
        posMassChebyshevCoeff ρ * (20 * (X : ℝ)) =
          posMassChebyshevCoeff ρ * 20 * (X : ℝ) := by
      ring
    exact hassoc.trans_le (hmul.trans_eq hRHS)
  have hmR : (0 : ℝ) < (seqWindow nthPrime X).card := by
    exact_mod_cast hm
  have hhalfpos : 0 < (1 : ℝ) / 2 * ((X : ℝ) / Real.log X) :=
    mul_pos (by norm_num : (0 : ℝ) < 1 / 2) (div_pos hx0 hlogX)
  have havg :
      windowAvgReal (seqWindow nthPrime X)
          (fun n => seqGapTail ρ nthPrime (n + L)) ≤
        posMassChebyshevCoeff ρ * 20 * (X : ℝ) /
          ((seqWindow nthPrime X).card : ℝ) := by
    have hden' : 0 ≤ ((seqWindow nthPrime X).card : ℝ) := Nat.cast_nonneg _
    exact hT.trans (div_le_div_of_nonneg_right hFnum hden')
  have hinv : 1 / ((seqWindow nthPrime X).card : ℝ) ≤
      1 / ((1 : ℝ) / 2 * ((X : ℝ) / Real.log X)) :=
    one_div_le_one_div_of_le hhalfpos hcardge
  have hquot :
      posMassChebyshevCoeff ρ * 20 * (X : ℝ) /
          ((seqWindow nthPrime X).card : ℝ) ≤
        posMassChebyshevCoeff ρ * 20 * (X : ℝ) *
          (1 / ((1 : ℝ) / 2 * ((X : ℝ) / Real.log X))) := by
    have hnn : 0 ≤ posMassChebyshevCoeff ρ * 20 * (X : ℝ) :=
      mul_nonneg (mul_nonneg (posMassChebyshevCoeff_nonneg hρ)
        (by norm_num : (0 : ℝ) ≤ 20)) hx0.le
    have : posMassChebyshevCoeff ρ * 20 * (X : ℝ) /
          ((seqWindow nthPrime X).card : ℝ) =
        (posMassChebyshevCoeff ρ * 20 * (X : ℝ)) *
          (1 / ((seqWindow nthPrime X).card : ℝ)) := by
      field_simp [hmR.ne']
    rw [this]
    exact mul_le_mul_of_nonneg_left hinv hnn
  have hsimp :
      posMassChebyshevCoeff ρ * 20 * (X : ℝ) *
          (1 / ((1 : ℝ) / 2 * ((X : ℝ) / Real.log X))) =
        gapTailLogKuperbergCoeff ρ * Real.log X := by
    have hx0' : (X : ℝ) ≠ 0 := hx0.ne'
    have hL' : Real.log X ≠ 0 := hlogX.ne'
    unfold gapTailLogKuperbergCoeff
    field_simp [hx0', hL']
    ring
  have hfinal :
      posMassChebyshevCoeff ρ * 20 * (X : ℝ) /
          ((seqWindow nthPrime X).card : ℝ) ≤
        gapTailLogKuperbergCoeff ρ * windowG X := by
    rw [hG]
    exact hquot.trans_eq hsimp
  exact havg.trans hfinal

/-! ### `GapTailT` at `windowG` -/

/-- AHL-reusable form: any source of `PrimeCountingAsymp` yields log-scale
`GapTailT` on dyadic `seqWindow nthPrime`. -/
theorem gapTailT_nthPrime_windowG_of_primeCountingAsymp {ρ : ℝ}
    (hρ : 1 < ρ) (hπ : PrimeCountingAsymp) :
    GapTailT nthPrime ρ windowG :=
  ⟨hρ, tendsto_windowG_atTop, nthPrime_div_pow_summable hρ,
    ⟨gapTailLogKuperbergCoeff ρ, gapTailLogKuperbergCoeff_nonneg hρ,
      eventually_gapTail_avg_nthPrime_windowG_of_primeCountingAsymp hρ hπ⟩⟩

/-- `GapTailT nthPrime ρ windowG` from the uniform Kuperberg singleton. -/
theorem gapTailT_nthPrime_windowG_of_kuperberg {ρ : ℝ}
    (hρ : 1 < ρ) (hK : KuperbergConj13) :
    GapTailT nthPrime ρ windowG :=
  gapTailT_nthPrime_windowG_of_primeCountingAsymp hρ
    (primeCountingAsymp_of_kuperberg hK)

/-! ### Profile remainder at `windowG` -/

theorem physicalPhaseRemainderVanishingProfile_nthPrime_polynomialX_windowG_of_primeCountingAsymp
    {B : ℕ} {ρ : ℝ} (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hπ : PrimeCountingAsymp) :
    PhysicalPhaseRemainderVanishingProfile nthPrime
      (fun _ => Polynomial.X) B ρ windowG :=
  physicalPhaseRemainderVanishingProfile_nthPrime_polynomialX_windowG_of_GapTailT
    hB hρB (gapTailT_nthPrime_windowG_of_primeCountingAsymp hρ hπ)

theorem physicalPhaseRemainderVanishingProfile_nthPrime_polynomialX_windowG_of_kuperberg
    {B : ℕ} {ρ : ℝ} (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hK : KuperbergConj13) :
    PhysicalPhaseRemainderVanishingProfile nthPrime
      (fun _ => Polynomial.X) B ρ windowG :=
  physicalPhaseRemainderVanishingProfile_nthPrime_polynomialX_windowG_of_GapTailT
    hB hρB (gapTailT_nthPrime_windowG_of_kuperberg hρ hK)

theorem physicalPhaseRemainderVanishingProfile_nthPrime_C_mul_windowG_of_primeCountingAsymp
    {B : ℕ} {ρ : ℝ} (c : ℝ)
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hπ : PrimeCountingAsymp) :
    PhysicalPhaseRemainderVanishingProfile nthPrime
      (fun _ => C c * Polynomial.X) B ρ windowG :=
  physicalPhaseRemainderVanishingProfile_C_mul_of_GapTailT c hB hρB
    (gapTailT_nthPrime_windowG_of_primeCountingAsymp hρ hπ)

theorem physicalPhaseRemainderVanishingProfile_nthPrime_C_mul_windowG_of_kuperberg
    {B : ℕ} {ρ : ℝ} (c : ℝ)
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hK : KuperbergConj13) :
    PhysicalPhaseRemainderVanishingProfile nthPrime
      (fun _ => C c * Polynomial.X) B ρ windowG :=
  physicalPhaseRemainderVanishingProfile_C_mul_of_GapTailT c hB hρB
    (gapTailT_nthPrime_windowG_of_kuperberg hρ hK)

end PrimeGapNormality.Prime
