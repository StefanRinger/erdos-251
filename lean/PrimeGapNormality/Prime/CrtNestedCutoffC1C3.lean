import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Nested cutoffs: scalar product of (C1) and (C3)

Paper `∑ |μ₁ − μ₂| ≤ 2 M₁ (1 − Θ)` and
`1 − Θ ≤ 1 − R + 1/(y₁ − 1)`, hence
`∑ |μ₁ − μ₂| ≤ 2 M₁ (1 − R + 1/(y₁ − 1))`
when `0 ≤ M₁` and `0 ≤ 1 − Θ` (or `0 ≤ 1 − R` and
`0 ≤ 1/(y₁ − 1)`).

This leaf is a **scalar inequality** on `ℝ`. Unique names
`crtNestC13_*`. The L1 bound and the product bound remain
separate theorems in other files; this leaf only multiplies
them. Binders stay honest: (C1) and (C3) are hypotheses here.

Does **not** import `CrtNestedCutoffL1`, `CrtNestedCutoffTheta`,
`CrtNestedCutoffVRatio`, MixZeta, SingletonLi, or WeylOf*.
Does **not** claim (C4) `O(L/G)`, `M₁ ≤ 12 L`, or that the
kernel is closed.

**Compiled.**
1. `0 ≤ M` and `0 ≤ a ≤ b` ⇒ `2 M a ≤ 2 M b`.
2. Instantiated: `0 ≤ M`, `0 ≤ 1 − θ`, and the (C3) binder
   `1 − θ ≤ 1 − R + 1/(y₁ − 1)` ⇒
   `2 M (1 − θ) ≤ 2 M (1 − R + 1/(y₁ − 1))`.
3. `0 ≤ 1 − R` and `0 ≤ 1/(y₁ − 1)` ⇒
   `0 ≤ 1 − R + 1/(y₁ − 1)`, hence `0 ≤ 2 M` times that sum.
4. Same scale without `0 ≤ 1 − θ`, from `0 ≤ 2 M` and the
   (C3) comparison alone.
5. A scalar (C1) binder `s ≤ 2 M (1 − θ)` times (C3), with
   `0 ≤ 1 − θ` or from `0 ≤ 2 M` alone.

**Not compiled.** (C1) L1. (C3) product/integral comparison.
(C4) `O(L/G)`. `M₁ ≤ 12 L`. Kernel close.

**Remaining hyps.** The L1 bound `s ≤ 2 M (1 − θ)` and the
product bound `1 − θ ≤ 1 − R + 1/(y₁ − 1)` as binders (proved
in other files, not imported). `0 ≤ M`. Either `0 ≤ 1 − θ`, or
the (C3) right-hand side nonnegative via `0 ≤ 1 − R` and
`0 ≤ 1/(y₁ − 1)`. Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `2 M a ≤ 2 M b` | theorem (`0 ≤ M`, `0 ≤ a ≤ b`) |
| `2 M (1−θ) ≤ 2 M (1−R+1/(y₁−1))` | theorem (`0 ≤ M`, `0 ≤ 1−θ`, (C3) binder) |
| `0 ≤ 1−R+1/(y₁−1)` and `0 ≤ 2 M` times it | theorem (`0 ≤ 1−R`, `0 ≤ 1/(y₁−1)`, `0 ≤ M`) |
| same scale from `0 ≤ 2 M` and (C3) | theorem (no `0 ≤ 1−θ`) |
| scalar (C1) times (C3) | theorem (both bounds as binders) |
| (C1) L1 / (C3) product | remaining (other files; not imported) |
| (C4) `O(L/G)` / `M₁ ≤ 12 L` | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round115/09_grok_mixture_gate_and_cutoff_bridge.md` §2
(C1) then (C3).
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Scale a nonnegative gap by `2 M` -/

private theorem crtNestC13_two_nonneg {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ (2 : ℝ) * M :=
  mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM

/-- If `0 ≤ M` and `0 ≤ a ≤ b` then `2 M a ≤ 2 M b`. Unique name. -/
theorem crtNestC13_two_mul_mono {M a b : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hab : a ≤ b) : (2 : ℝ) * M * a ≤ 2 * M * b :=
  mul_le_mul (le_rfl : (2 : ℝ) * M ≤ 2 * M) hab ha
    (crtNestC13_two_nonneg hM)

/-- Same comparison from `0 ≤ 2 M` and `a ≤ b` alone. Unique name. -/
theorem crtNestC13_two_mul_mono_left {M a b : ℝ} (hM : 0 ≤ M)
    (hab : a ≤ b) : (2 : ℝ) * M * a ≤ 2 * M * b :=
  mul_le_mul_of_nonneg_left hab (crtNestC13_two_nonneg hM)

/-! ### Instantiation on paper `(C3)` gaps -/

/-- Sum of nonnegative (C3) pieces. Remaining: `0 ≤ 1 − R` and
`0 ≤ 1/(y₁ − 1)`. -/
theorem crtNestC13_add_nonneg {R y1 : ℝ} (hR : 0 ≤ 1 - R)
    (hy : 0 ≤ 1 / (y1 - 1)) :
    0 ≤ 1 - R + 1 / (y1 - 1) :=
  add_nonneg hR hy

/-- The scaled (C3) right-hand side is nonnegative. Remaining:
`0 ≤ M`, `0 ≤ 1 − R`, and `0 ≤ 1/(y₁ − 1)`. -/
theorem crtNestC13_rhs_nonneg {M R y1 : ℝ} (hM : 0 ≤ M)
    (hR : 0 ≤ 1 - R) (hy : 0 ≤ 1 / (y1 - 1)) :
    0 ≤ (2 : ℝ) * M * (1 - R + 1 / (y1 - 1)) :=
  mul_nonneg (crtNestC13_two_nonneg hM) (crtNestC13_add_nonneg hR hy)

/-- Instantiated scale: `0 ≤ M` and `0 ≤ 1 − θ` and the (C3)
binder give `2 M (1 − θ) ≤ 2 M (1 − R + 1/(y₁ − 1))`. Does
**not** claim (C1), (C4), or `M ≤ 12 L`. -/
theorem crtNestC13_two_mul_one_sub {M θ R y1 : ℝ} (hM : 0 ≤ M)
    (hθ : 0 ≤ 1 - θ)
    (hC3 : 1 - θ ≤ 1 - R + 1 / (y1 - 1)) :
    (2 : ℝ) * M * (1 - θ) ≤ 2 * M * (1 - R + 1 / (y1 - 1)) :=
  crtNestC13_two_mul_mono hM hθ hC3

/-- Same scale from `0 ≤ M` and the (C3) binder, without
`0 ≤ 1 − θ`. The alternative positivity `0 ≤ 1 − R` and
`0 ≤ 1/(y₁ − 1)` is `crtNestC13_rhs_nonneg`, not this
comparison. Does **not** claim (C1) or (C4). -/
theorem crtNestC13_two_mul_one_sub_of {M θ R y1 : ℝ} (hM : 0 ≤ M)
    (hC3 : 1 - θ ≤ 1 - R + 1 / (y1 - 1)) :
    (2 : ℝ) * M * (1 - θ) ≤ 2 * M * (1 - R + 1 / (y1 - 1)) :=
  crtNestC13_two_mul_mono_left hM hC3

/-! ### Scalar `(C1)` binder times `(C3)` -/

/-- Paper combination on `ℝ`: a (C1) binder `s ≤ 2 M (1 − θ)`
and a (C3) binder multiply. Remaining: those two inequalities,
`0 ≤ M`, and `0 ≤ 1 − θ`. Does **not** claim (C4) or `M ≤ 12 L`. -/
theorem crtNestC13_le {s M θ R y1 : ℝ} (hM : 0 ≤ M) (hθ : 0 ≤ 1 - θ)
    (hC1 : s ≤ 2 * M * (1 - θ))
    (hC3 : 1 - θ ≤ 1 - R + 1 / (y1 - 1)) :
    s ≤ 2 * M * (1 - R + 1 / (y1 - 1)) :=
  hC1.trans (crtNestC13_two_mul_one_sub hM hθ hC3)

/-- Same chain from `0 ≤ M` and the two bound binders, without
`0 ≤ 1 − θ`. Remaining: the (C1) and (C3) binders. -/
theorem crtNestC13_le_of {s M θ R y1 : ℝ} (hM : 0 ≤ M)
    (hC1 : s ≤ 2 * M * (1 - θ))
    (hC3 : 1 - θ ≤ 1 - R + 1 / (y1 - 1)) :
    s ≤ 2 * M * (1 - R + 1 / (y1 - 1)) :=
  hC1.trans (crtNestC13_two_mul_one_sub_of hM hC3)

end

end PrimeGapNormality.Prime
