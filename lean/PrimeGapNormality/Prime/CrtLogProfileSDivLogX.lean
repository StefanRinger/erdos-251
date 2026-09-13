import PrimeGapNormality.Prime.CrtFailureMassLimit
import PrimeGapNormality.Prime.CrtWindowGEqLog
import PrimeGapNormality.Prime.ProfileInequalities
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic

/-!
# `log (profileS κ X) / log X → 0`

Paper `profileS κ X = ⌊4 * profileL κ X * windowG X⌋` with
`windowG X = max(log X, 1)` and `profileL → ∞` slowly
(`CrtFailureMassLimit.tendsto_profileL_atTop`). Eventual
`windowG X = log X` is `CrtWindowGEqLog`. Floor comparison is
`profileS ≤ 4 L G`. Then `log (profileS) ≤ log(4 L G) =
log 4 + log L + log G` once `1 ≤ profileS` (hence `1 < 4 L G`
is not required beyond positivity). The ratios
`log L / log X` and `log(log X) / log X` vanish at `+∞`.

Does **not** claim `lateRetention → 0`. Does **not** claim `hden`
(`TruncatedPhaseSpanExceedsDensityVanishing`). No MixZeta.
`G(X) = X` is not the remainder scale (`windowG`, not linear
Chebyshev). Does not import MixZeta, TypicalOsc*,
ExactRootWindowClose, ExactLawTypicalSetMassLeOne, WeylOf*, or
SingletonLi. Unique names (`crtLogSLogX_*`). Kernel not closed.

**Compiled.**
1. `(profileS κ X : ℝ) ≤ 4 * profileL κ X * windowG X`.
2. `log(log X) / log X → 0` along `ℕ`.
3. Eventual `profileL κ X ≤ log X` for `0 < κ`.
4. `log (profileL κ X) / log X → 0` for `0 < κ`.
5. `log (profileS κ X) / log X → 0` for `0 < κ`.
6. Same at `κ = stdKappa ρ` with `1 < ρ`.

**Not compiled.** `lateRetention → 0`. Density `hden`. MixZeta.
Typical osc. Weyl. Kernel close. Linear `G(X) = X`.

**Remaining hyps.** Binder `0 < κ`. Binder `1 < ρ` for the
standard clock. Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `profileS ≤ 4 L G` | theorem (`crtLogSLogX_profileS_le_four`) |
| `log(log X) / log X → 0` | theorem (`crtLogSLogX_tendsto_log_log_div_log`) |
| eventual `L ≤ log X` | theorem (`crtLogSLogX_eventually_profileL_le_log`) |
| `log L / log X → 0` | theorem (`crtLogSLogX_tendsto_log_profileL_div_log`) |
| `log (profileS) / log X → 0` (`0 < κ`) | theorem (`crtLogSLogX_tendsto`) |
| same at `stdKappa ρ` (`1 < ρ`) | theorem (`crtLogSLogX_tendsto_stdKappa`) |
| `lateRetention → 0` | not claimed |
| `hden` / MixZeta / Weyl | not claimed |
| Chebyshev / `G(X) = X` remainder scale | not used |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `EndAPI.profileS`, `windowG`, `profileL`;
`CrtWindowGEqLog.crtWindowG_eq`, `crtWindowG_eventually_eq_log`;
`ProfileInequalities.eventually_one_le_profileL`,
`eventually_one_le_profileS`;
`CrtFailureMassLimit.tendsto_profileL_atTop`.
Contract: API
-/

open Filter Asymptotics
open scoped Topology

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Floor bound `profileS ≤ 4 L G` -/

/-- Definitional floor: `S = ⌊4 L G⌋ ≤ 4 L G`. -/
theorem crtLogSLogX_profileS_le_four (κ : ℝ) (X : ℕ) :
    (profileS κ X : ℝ) ≤ 4 * (profileL κ X : ℝ) * windowG X := by
  have hnn : 0 ≤ (4 : ℝ) * (profileL κ X : ℝ) * windowG X :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg _))
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) (crtWindowG_one_le X))
  exact Nat.floor_le hnn

/-! ### Elementary log ratios -/

/-- `(log x) / x → 0` at `+∞`. -/
private theorem crtLogSLogX_tendsto_log_div_id :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- `log(log X) / log X → 0` along `ℕ`. -/
theorem crtLogSLogX_tendsto_log_log_div_log :
    Tendsto (fun X : ℕ => Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ))
      atTop (nhds 0) :=
  crtLogSLogX_tendsto_log_div_id.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Constant over `log X` vanishes. -/
private theorem crtLogSLogX_tendsto_const_div_log (c : ℝ) :
    Tendsto (fun X : ℕ => c / Real.log (X : ℝ)) atTop (nhds 0) := by
  simpa [div_eq_mul_inv] using
    (tendsto_inv_atTop_zero.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul c

/-- `√x ≤ 1 + x` for `0 ≤ x`. -/
private theorem crtLogSLogX_sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ 1 + x := by
  rcases le_total (Real.sqrt x) 1 with h | h
  · exact h.trans (le_add_of_nonneg_right hx)
  · have hle : Real.sqrt x ≤ x := by
      have hmul : Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        le_mul_of_one_le_left (Real.sqrt_nonneg x) h
      rwa [Real.mul_self_sqrt hx] at hmul
    exact hle.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

/-- Ceil bound plus `√t ≤ 1 + t`: `L ≤ 2 κ log G + 2`. -/
private theorem crtLogSLogX_profileL_le {κ : ℝ} (hκ : 0 ≤ κ) (X : ℕ) :
    (profileL κ X : ℝ) ≤ 2 * (κ * Real.log (windowG X)) + 2 := by
  have hlogG : 0 ≤ Real.log (windowG X) := Real.log_nonneg (crtWindowG_one_le X)
  have harg : 0 ≤ κ * Real.log (windowG X) := mul_nonneg hκ hlogG
  set a := κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X))
  have ha : 0 ≤ a := add_nonneg harg (Real.sqrt_nonneg _)
  have hceil : (profileL κ X : ℝ) ≤ a + 1 :=
    (Nat.ceil_lt_add_one (R := ℝ) ha).le
  have hsqrt : Real.sqrt (κ * Real.log (windowG X)) ≤
      1 + κ * Real.log (windowG X) :=
    crtLogSLogX_sqrt_le_one_add harg
  have hsum : a + 1 ≤ 2 * (κ * Real.log (windowG X)) + 2 := by
    unfold a
    have hstep :
        κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X)) + 1 ≤
          κ * Real.log (windowG X) + (1 + κ * Real.log (windowG X)) + 1 := by
      have hin :
          κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X)) ≤
            κ * Real.log (windowG X) + (1 + κ * Real.log (windowG X)) :=
        add_le_add (le_refl _) hsqrt
      exact add_le_add hin (le_refl (1 : ℝ))
    refine hstep.trans_eq ?_
    ring
  exact hceil.trans hsum

/-- Real comparison `2 κ (log h / h) + 2 / h → 0`. -/
private theorem crtLogSLogX_tendsto_two_kappa_log_div (κ : ℝ) :
    Tendsto (fun h : ℝ => (2 * κ) * (Real.log h / h) + (2 : ℝ) / h)
      atTop (nhds 0) := by
  have h1 :
      Tendsto (fun h : ℝ => (2 * κ) * (Real.log h / h)) atTop (nhds 0) :=
    mul_zero (2 * κ) ▸
      (tendsto_const_nhds (x := 2 * κ)).mul crtLogSLogX_tendsto_log_div_id
  have h2 : Tendsto (fun h : ℝ => (2 : ℝ) / h) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
  simpa [add_zero] using h1.add h2

/-- Eventually `L ≤ log X`. Uses `G = log X` and `L = O(log log X)`. -/
theorem crtLogSLogX_eventually_profileL_le_log {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, (profileL κ X : ℝ) ≤ Real.log (X : ℝ) := by
  have hsum :=
    (crtLogSLogX_tendsto_two_kappa_log_div κ).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [crtWindowG_eventually_eq_log,
    hsum.eventually (Metric.ball_mem_nhds (0 : ℝ)
      (by norm_num : (0 : ℝ) < 1))] with X hGeq hball
  have hlog1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    have := crtWindowG_one_le X
    rwa [hGeq] at this
  have hpos : (0 : ℝ) < Real.log (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hlog1
  set hlog := Real.log (X : ℝ)
  have hdist : dist ((2 * κ) * (Real.log hlog / hlog) + (2 : ℝ) / hlog) 0 < 1 :=
    Metric.mem_ball.mp hball
  rw [Real.dist_eq, sub_zero] at hdist
  have hlt : (2 * κ) * (Real.log hlog / hlog) + (2 : ℝ) / hlog < 1 :=
    lt_of_le_of_lt (le_abs_self _) hdist
  have hne : hlog ≠ 0 := hpos.ne'
  have hcalc :
      ((2 * κ) * (Real.log hlog / hlog) + (2 : ℝ) / hlog) * hlog =
        2 * (κ * Real.log hlog) + 2 := by
    rw [add_mul, mul_assoc, div_mul_cancel₀ (Real.log hlog) hne,
      div_mul_cancel₀ (2 : ℝ) hne, mul_assoc]
  have hlt' : 2 * (κ * Real.log hlog) + 2 < hlog := by
    have := mul_lt_mul_of_pos_right hlt hpos
    rwa [hcalc, one_mul] at this
  have hbound : (profileL κ X : ℝ) ≤ 2 * (κ * Real.log hlog) + 2 := by
    simpa [hGeq, hlog] using crtLogSLogX_profileL_le hκ.le X
  exact hbound.trans hlt'.le

/-- `log L / log X → 0`. Remaining: `0 < κ`. Uses eventual `L ≤ log X`
and `log(log X) / log X → 0`. Does **not** claim `lateRetention → 0`. -/
theorem crtLogSLogX_tendsto_log_profileL_div_log {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ => Real.log (profileL κ X : ℝ) / Real.log (X : ℝ))
      atTop (nhds 0) := by
  refine squeeze_zero' ?h0 ?hle crtLogSLogX_tendsto_log_log_div_log
  · filter_upwards [(tendsto_profileL_atTop hκ).eventually (eventually_ge_atTop 1),
      tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with X hL hx
    exact div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hL))
      (Real.log_pos hx).le
  · filter_upwards [crtLogSLogX_eventually_profileL_le_log hκ,
      eventually_one_le_profileL hκ,
      crtWindowG_eventually_eq_log] with X hLle hL hGeq
    have hLpos : (0 : ℝ) < (profileL κ X : ℝ) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (Nat.one_le_cast.mpr hL)
    have hlog1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by
      have := crtWindowG_one_le X
      rwa [hGeq] at this
    have hlelog :
        Real.log (profileL κ X : ℝ) ≤ Real.log (Real.log (X : ℝ)) :=
      Real.log_le_log hLpos hLle
    exact div_le_div_of_nonneg_right hlelog
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog1)

/-! ### `log (profileS)` versus `log 4 + log L + log G` -/

/-- Once `1 ≤ L` and `1 ≤ S`, `log S ≤ log 4 + log L + log G`. -/
private theorem crtLogSLogX_log_profileS_le {κ : ℝ} {X : ℕ}
    (hL : 1 ≤ profileL κ X) (hS : 1 ≤ profileS κ X) :
    Real.log (profileS κ X : ℝ) ≤
      Real.log 4 + Real.log (profileL κ X : ℝ) + Real.log (windowG X) := by
  have hSpos : (0 : ℝ) < (profileS κ X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (Nat.one_le_cast.mpr hS)
  have hlog := Real.log_le_log hSpos (crtLogSLogX_profileS_le_four κ X)
  have hLne : (profileL κ X : ℝ) ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (Nat.one_le_cast.mpr hL)).ne'
  have hGne : windowG X ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (crtWindowG_one_le X)).ne'
  have h4ne : (4 : ℝ) ≠ 0 := by norm_num
  have hmul :
      Real.log (4 * (profileL κ X : ℝ) * windowG X) =
        Real.log 4 + Real.log (profileL κ X : ℝ) + Real.log (windowG X) := by
    rw [Real.log_mul (mul_ne_zero h4ne hLne) hGne, Real.log_mul h4ne hLne,
      add_assoc]
  exact hlog.trans_eq hmul

/-- `log (profileS κ X) / log X → 0` along `atTop`. Remaining hyp:
`0 < κ`. Does **not** claim `lateRetention → 0` or `hden`.
`G(X) = X` is not the remainder scale. -/
theorem crtLogSLogX_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
        Real.log (profileS κ X : ℝ) / Real.log (X : ℝ))
      atTop (nhds 0) := by
  have hupper :
      Tendsto (fun X : ℕ =>
          Real.log 4 / Real.log (X : ℝ) +
            Real.log (profileL κ X : ℝ) / Real.log (X : ℝ) +
            Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ))
        atTop (nhds 0) := by
    simpa [add_zero] using
      ((crtLogSLogX_tendsto_const_div_log (Real.log 4)).add
          (crtLogSLogX_tendsto_log_profileL_div_log hκ)).add
        crtLogSLogX_tendsto_log_log_div_log
  refine squeeze_zero' ?h0 ?hle hupper
  · filter_upwards [eventually_one_le_profileS hκ,
      crtWindowG_eventually_eq_log] with X hS hGeq
    have hlog1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by
      have := crtWindowG_one_le X
      rwa [hGeq] at this
    exact div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hS))
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog1)
  · filter_upwards [eventually_one_le_profileL hκ,
      eventually_one_le_profileS hκ,
      crtWindowG_eventually_eq_log] with X hL hS hGeq
    have hlog1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by
      have := crtWindowG_one_le X
      rwa [hGeq] at this
    have hle := crtLogSLogX_log_profileS_le hL hS
    have hle' :
        Real.log (profileS κ X : ℝ) ≤
          Real.log 4 + Real.log (profileL κ X : ℝ) +
            Real.log (Real.log (X : ℝ)) := by
      simpa [hGeq] using hle
    have hdiv :=
      div_le_div_of_nonneg_right hle'
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog1)
    have hsplit :
        (Real.log 4 + Real.log (profileL κ X : ℝ) +
            Real.log (Real.log (X : ℝ))) /
          Real.log (X : ℝ) =
          Real.log 4 / Real.log (X : ℝ) +
            Real.log (profileL κ X : ℝ) / Real.log (X : ℝ) +
            Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) := by
      rw [add_div, add_div]
    exact hdiv.trans_eq hsplit

/-- Same limit at the standard clock `κ = 1 / log ρ`. Remaining hyp:
`1 < ρ`. Does **not** claim `lateRetention → 0` or `hden`. -/
theorem crtLogSLogX_tendsto_stdKappa {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto (fun X : ℕ =>
        Real.log (profileS (stdKappa ρ) X : ℝ) / Real.log (X : ℝ))
      atTop (nhds 0) :=
  crtLogSLogX_tendsto (stdKappa_pos hρ)

end

end PrimeGapNormality.Prime
