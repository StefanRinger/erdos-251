import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Isolated real algebra `ψ(t) = min(1, t)`

Paper v0.23: the bounded tail shift uses `ψ(t) = min(1, t)`
before a fixed-index move. This leaf isolates **only** that
real `min` algebra on `ℝ`. It does **not** compile an
unbounded tail shift, Weyl, MixZeta, SingletonLi, Kernel,
`¬ hs`, or (C4).

Does **not** import `CrtIncAbsErr` (`incErr_`) and does
**not** steal `|⌊x⌋ − x| < 1`. Clash-check: no `incErr_`
names. Does **not** import `CrtLiIncrement` (`liStep_`)
and does **not** steal the real increment sandwich.
Clash-check: no `liStep_` names. Does **not** import
`NatNotInUnit` (`natUnit_`), `VirtDoubleEnd`, or
`AbsErrDivN` (`divN_`). Clash-check: no `divN_`,
`mixCal_`, or `meanBad_` names.

Unique names `tailMin_` only. Mathlib `Real.Basic`
(`min_le_left`, `min_le_right`, `le_min_iff`,
`min_eq_left`, `min_eq_right`) and `Tactic.NormNum`
for `(0 : ℝ) ≤ 1`. No `open Nat`. Does **not** edit
`All.lean`.

**Compiled.**
1. `min (1 : ℝ) t ≤ 1` and `min (1 : ℝ) t ≤ t`.
2. `0 ≤ t` ⇒ `0 ≤ min (1 : ℝ) t`
   (`le_min_iff` and `(0 : ℝ) ≤ 1`).
3. `t ≤ 1` ⇒ `min (1 : ℝ) t = t` (`min_eq_right`).
4. `1 ≤ t` ⇒ `min (1 : ℝ) t = 1` (`min_eq_left`).
5. Optional: `|min (1 : ℝ) t| ≤ 1` under `0 ≤ t`.
   Optional: `min (1 : ℝ) t ≤ |t|` (unconditional:
   `min ≤ t` and `t ≤ |t|`).

**Not compiled.** Unbounded tail shift. Weyl. MixZeta.
SingletonLi. Kernel. `¬ hs`. (C4). The false claim
`0 ≤ min (1 : ℝ) t` with no sign of `t` (false at
`t = -1`). `|min (1 : ℝ) t| ≤ 1` with no sign of `t`
(false at `t = -2`). `CrtIncAbsErr` / `CrtLiIncrement` /
`NatNotInUnit` / `VirtDoubleEnd` / `AbsErrDivN`.

**Remaining hyps.** Binder `0 ≤ t` on (2) and on
`|min (1, t)| ≤ 1`. Binder `t ≤ 1` on (3). Binder
`1 ≤ t` on (4). The two comparisons in (1) and
`min ≤ |t|` are unconditional. Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `min 1 t ≤ 1` | theorem (`tailMin_le_one`) |
| `min 1 t ≤ t` | theorem (`tailMin_le_t`) |
| `(0 : ℝ) ≤ 1` | theorem (`tailMin_zero_le_one`) |
| `0 ≤ t` ⇒ `0 ≤ min 1 t` | theorem (`tailMin_nonneg`) |
| `t ≤ 1` ⇒ `min 1 t = t` | theorem (`tailMin_eq_t`) |
| `1 ≤ t` ⇒ `min 1 t = 1` | theorem (`tailMin_eq_one`) |
| `0 ≤ t` ⇒ `0 ≤ min 1 t ≤ 1` | theorem (`tailMin_mem_unit`) |
| `0 ≤ t` ⇒ `\|min 1 t\| ≤ 1` | theorem (`tailMin_abs_le_one`) |
| `min 1 t ≤ \|t\|` | theorem (`tailMin_le_abs`) |
| `0 ≤ min 1 t` with no sign of `t` | not claimed (false) |
| unbounded tail shift / Weyl | not claimed |
| MixZeta / SingletonLi / Kernel / `¬ hs` / (C4) | not claimed |
| `incErr_` / `liStep_` / `divN_` / `mixCal_` / `meanBad_` | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round126/22_paper_v0_23.tex` (`ψ(t)=min(1,t)`);
`rounds/round126/27_grok_v023_endpoints_handover.md`.
SHA-256 `2e5c8f8627b801af2a69c254733331cc43e11ce105f886725fcc455b9a9163b8`.
Mathlib `min_le_left`, `min_le_right`, `le_min_iff`,
`min_eq_left`, `min_eq_right`, `abs_of_nonneg`, `le_abs_self`.
Contract: API
-/

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Comparisons `min 1 t ≤ 1` and `min 1 t ≤ t` -/

/-- Mathlib `min_le_left`. Remaining: none. -/
theorem tailMin_le_one (t : ℝ) : min (1 : ℝ) t ≤ 1 :=
  min_le_left (1 : ℝ) t

/-- Mathlib `min_le_right`. Remaining: none. -/
theorem tailMin_le_t (t : ℝ) : min (1 : ℝ) t ≤ t :=
  min_le_right (1 : ℝ) t

/-! ### Nonnegativity needs `0 ≤ t`; `(0 : ℝ) ≤ 1` is `norm_num` -/

/-- `norm_num` for `(0 : ℝ) ≤ 1`. Remaining: none. -/
theorem tailMin_zero_le_one : (0 : ℝ) ≤ 1 := by
  norm_num

/-- Remaining: `0 ≤ t`. Does **not** claim `0 ≤ min 1 t`
without the sign of `t` (false at `t = -1`). -/
theorem tailMin_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ min (1 : ℝ) t :=
  le_min_iff.mpr ⟨tailMin_zero_le_one, ht⟩

/-! ### Identities on each side of the cut `t = 1` -/

/-- Remaining: `t ≤ 1`. Mathlib `min_eq_right`. -/
theorem tailMin_eq_t {t : ℝ} (ht : t ≤ 1) :
    min (1 : ℝ) t = t :=
  min_eq_right ht

/-- Remaining: `1 ≤ t`. Mathlib `min_eq_left`. -/
theorem tailMin_eq_one {t : ℝ} (ht : 1 ≤ t) :
    min (1 : ℝ) t = 1 :=
  min_eq_left ht

/-! ### Optional: unit interval under `0 ≤ t`, and `|min 1 t|` -/

/-- Remaining: `0 ≤ t`. Values of `ψ` lie in `[0, 1]`. -/
theorem tailMin_mem_unit {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ min (1 : ℝ) t ∧ min (1 : ℝ) t ≤ 1 :=
  ⟨tailMin_nonneg ht, tailMin_le_one t⟩

/-- Remaining: `0 ≤ t`. Does **not** claim `|min 1 t| ≤ 1`
without the sign of `t` (false at `t = -2`). -/
theorem tailMin_abs_le_one {t : ℝ} (ht : 0 ≤ t) :
    |min (1 : ℝ) t| ≤ 1 := by
  rw [abs_of_nonneg (tailMin_nonneg ht)]
  exact tailMin_le_one t

/-- Unconditional: `min 1 t ≤ t ≤ |t|`. Remaining: none. -/
theorem tailMin_le_abs (t : ℝ) : min (1 : ℝ) t ≤ |t| :=
  (tailMin_le_t t).trans (le_abs_self t)

end

end PrimeGapNormality.Prime
