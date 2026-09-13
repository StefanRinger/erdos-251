import PrimeGapNormality.Prime.EndAPI
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Eventual `windowG X = Real.log X`

`windowG X = max (log X, 1)`. Once `e ≤ X`, one has `1 ≤ log X`,
hence `windowG X = Real.log X`. The same identity holds eventually
along `ℕ`.

Does **not** claim `TruncatedPhaseSpanExceedsDensityVanishing` at
`windowG`. `G(X) = X` is not the remainder scale (`windowG`, not
linear Chebyshev). Does not import MixZeta, TypicalOsc*,
ExactRootWindowClose, ExactLawTypicalSetMassLeOne, WeylOf*,
SpanCutNthPrime, or SingletonLi. No Weyl file. Unique names
(`crtWindowG_*`). Kernel not closed.

**Compiled.**
1. `windowG X = max (log X, 1)`.
2. `1 ≤ windowG X`.
3. `1 ≤ log X` ⇒ `windowG X = log X`.
4. `e ≤ X` ⇒ `1 ≤ log X` and `windowG X = log X`.
5. Eventual `windowG X = Real.log X` along `ℕ`.

**Not compiled.** `TruncatedPhaseSpanExceedsDensityVanishing nthPrime
ρ windowG`. Density `→ 0` at `windowG`. Linear `G(X) = X` vanishing
as a statement about `windowG`. MixZeta. Weyl. Kernel close.

**Remaining hyps.** Pointwise `Real.exp 1 ≤ (X : ℝ)` for the
non-eventual identity. `TruncatedPhaseSpanExceedsDensityVanishing`
at `windowG` (named; not claimed). Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `windowG X = max(log X, 1)` | theorem (`crtWindowG_eq`) |
| `e ≤ X` ⇒ `1 ≤ log X` | theorem (`crtWindowG_one_le_log`) |
| `e ≤ X` ⇒ `windowG X = log X` | theorem (`crtWindowG_eq_log`) |
| eventual `windowG X = log X` | theorem (`crtWindowG_eventually_eq_log`) |
| `TruncatedPhaseSpanExceedsDensityVanishing` at `windowG` | remains (not claimed) |
| PNT / Chebyshev / `G(X) = X` ⇒ density `→ 0` | not claimed |
| MixZeta / Weyl | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `EndAPI.windowG`.
Contract: API
-/

open Filter

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Unfolding `windowG` -/

/-- Definitional identity: `windowG X = max (log X, 1)`. -/
theorem crtWindowG_eq (X : ℕ) :
    windowG X = max (Real.log (X : ℝ)) 1 :=
  rfl

/-- The floor at `1` in `windowG`. -/
theorem crtWindowG_one_le (X : ℕ) : (1 : ℝ) ≤ windowG X :=
  le_max_right _ _

/-! ### `windowG X = log X` once `e ≤ X` -/

/-- `max(log X, 1) = log X` as soon as `1 ≤ log X`. -/
theorem crtWindowG_eq_log_of_one_le_log {X : ℕ}
    (hlog : (1 : ℝ) ≤ Real.log (X : ℝ)) :
    windowG X = Real.log (X : ℝ) := by
  rw [crtWindowG_eq]
  exact max_eq_left hlog

/-- `e ≤ X` rearranges to `1 ≤ log X`. Remaining hyp:
`Real.exp 1 ≤ (X : ℝ)`. -/
theorem crtWindowG_one_le_log {X : ℕ}
    (hX : Real.exp 1 ≤ (X : ℝ)) :
    (1 : ℝ) ≤ Real.log (X : ℝ) := by
  have hx0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  exact (Real.le_log_iff_exp_le hx0).mpr hX

/-- `windowG X = max(log X, 1)` equals `log X` as soon as
`1 ≤ log X`, i.e. `e ≤ X`. Remaining hyp: `Real.exp 1 ≤ (X : ℝ)`.
Does **not** claim vanishing at `windowG`. -/
theorem crtWindowG_eq_log {X : ℕ}
    (hX : Real.exp 1 ≤ (X : ℝ)) :
    windowG X = Real.log (X : ℝ) :=
  crtWindowG_eq_log_of_one_le_log (crtWindowG_one_le_log hX)

/-- Eventual form of `crtWindowG_eq_log`. Does **not** claim
`TruncatedPhaseSpanExceedsDensityVanishing` at `windowG`. -/
theorem crtWindowG_eventually_eq_log :
    ∀ᶠ X : ℕ in atTop, windowG X = Real.log (X : ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 1))] with X hX
  exact crtWindowG_eq_log hX

end

end PrimeGapNormality.Prime
