import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Ring.Rat
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Isolated cyclic variable shift via `MvPolynomial.rename Nat.succ`

Paper v0.23 (package A: local algebra): the cyclic shift of
local polynomials is **variable rename along** `Nat.succ`
on `MvPolynomial ℕ ℚ`. This leaf isolates **only** that
`MvPolynomial.rename`. It is **not** the one-point
regression `HomogLeadTerm` / `onePt_` (mixed-degree
`X 0 ^ 3 + X 0 * X 5`). That test stays on `onePt_`.

It does **not** import `HomogLeadTerm` (`onePt_`) and does
**not** steal `onePt_regression_lead`. It does **not**
import `HomogDegNF` (`degNF_`). Unique names `cycSh_` only.
Clash-check: no `onePt_`, `degNF_`, `divN_`, `tailMin_`,
`mixCal_`, `meanBad_`.

Lean 4.33.1: `MvPolynomial.rename_X`, `rename_C`,
`IsHomogeneous.rename_isHomogeneous`. There is no
`totalDegree_rename`; Mathlib has `totalDegree_rename_le`
and, for injective rename, `weightedTotalDegree_rename_of_injective`
with `weightedTotalDegree_one`. No `omega`. No `open Nat`.

Unique names `cycSh_`. Imports Mathlib `MvPolynomial.Basic`,
`Rename`, `Degrees`, `RingTheory.MvPolynomial.Homogeneous`,
and `Algebra.Ring.Rat` (coefficient ring `ℚ`, held fixed).
Does **not** import MixZeta, SingletonLi, Kernel, EndAPI,
Weyl, HomogLeadTerm, or HomogDegNF. Does **not** edit
`All.lean`.

**Compiled.**
1. `rename Nat.succ (X i : MvPolynomial ℕ ℚ) = X (i + 1)`
   (`MvPolynomial.rename_X`).
2. `rename Nat.succ` preserves `IsHomogeneous d`
   (`IsHomogeneous.rename_isHomogeneous`). Not `omega`.
3. Optional: `totalDegree (rename Nat.succ f) = totalDegree f`
   (`totalDegree_rename_le` one way; converse via injective
   `weightedTotalDegree_rename_of_injective` and
   `Pi.one_comp`, since 4.33.1 has no `totalDegree_rename`).
4. Optional: `rename Nat.succ (C q) = C q` (`rename_C`).
5. Optional: `rename Nat.succ (X 0 ^ 3) = X 1 ^ 3`.
   Not the regression `X 0 ^ 3 + X 0 * X 5`.

**Not compiled.** Cyclic normal form `N_(B,k)`. S/T. Weyl.
MixZeta. SingletonLi. Kernel. `¬ hs`. (C4). HomogLeadTerm
one-point regression. HomogDegNF degree-of-normal-form.

**Remaining hyps.** Binder `IsHomogeneous d` on (2). None
on (1) and (3)–(5). Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `rename Nat.succ (X i) = X (i+1)` | theorem (`cycSh_rename_X`) |
| `IsHomogeneous d` is preserved | theorem (`cycSh_isHomogeneous`) |
| `totalDegree (rename Nat.succ f) ≤ totalDegree f` | theorem (`cycSh_totalDegree_le`) |
| `totalDegree f ≤ totalDegree (rename Nat.succ f)` | theorem (`cycSh_totalDegree_ge`) |
| `totalDegree` equality | theorem (`cycSh_totalDegree`) |
| `rename Nat.succ (C q) = C q` | theorem (`cycSh_rename_C`) |
| `rename Nat.succ (X 0 ^ 3) = X 1 ^ 3` | theorem (`cycSh_X_pow_three`) |
| cyclic NF `N_(B,k)` / S/T / Weyl | not claimed |
| MixZeta / SingletonLi / Kernel / `¬ hs` / (C4) | not claimed |
| `onePt_` regression `X 0 ^ 3 + X 0 * X 5` | not claimed (not imported) |
| `degNF_` degree of the normal form | not claimed (not imported) |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round126/22_paper_v0_23.tex`;
`rounds/round126/27_grok_v023_endpoints_handover.md`
(package A: cyclic shift of local polynomials).
SHA-256 `2e5c8f8627b801af2a69c254733331cc43e11ce105f886725fcc455b9a9163b8`.
Mathlib `rename_X`, `rename_C`,
`IsHomogeneous.rename_isHomogeneous`,
`totalDegree_rename_le`,
`weightedTotalDegree_rename_of_injective`,
`weightedTotalDegree_one`, `Pi.one_comp`, `map_pow`.
Contract: API
-/

namespace PrimeGapNormality.Prime

open MvPolynomial

noncomputable section

/-! ### `rename Nat.succ` on variables and constants -/

/-- Mathlib `rename_X`. Remaining: none. -/
theorem cycSh_rename_X (i : ℕ) :
    rename Nat.succ (X i : MvPolynomial ℕ ℚ) = X (i + 1) :=
  rename_X Nat.succ i

/-- Mathlib `rename_C`. Remaining: none. -/
theorem cycSh_rename_C (q : ℚ) :
    rename Nat.succ (C q : MvPolynomial ℕ ℚ) = C q :=
  rename_C Nat.succ q

/-- Optional monomial check. Not `onePt_regression_lead`. -/
theorem cycSh_X_pow_three :
    rename Nat.succ ((X 0 : MvPolynomial ℕ ℚ) ^ 3) = X 1 ^ 3 := by
  rw [map_pow, rename_X]

/-! ### Homogeneity is preserved -/

/-- Mathlib `IsHomogeneous.rename_isHomogeneous`. Remaining:
`f.IsHomogeneous d`. Not `omega`. -/
theorem cycSh_isHomogeneous {f : MvPolynomial ℕ ℚ} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (rename Nat.succ f).IsHomogeneous d :=
  hf.rename_isHomogeneous

/-! ### Total degree is preserved (`Nat.succ` is injective) -/

/-- Mathlib `totalDegree_rename_le`. Remaining: none. -/
theorem cycSh_totalDegree_le (f : MvPolynomial ℕ ℚ) :
    (rename Nat.succ f).totalDegree ≤ f.totalDegree :=
  totalDegree_rename_le Nat.succ f

/-- 4.33.1 has no `totalDegree_rename`. Injective `Nat.succ`
identifies weighted degree 1 after rename. Remaining: none. -/
theorem cycSh_totalDegree (f : MvPolynomial ℕ ℚ) :
    (rename Nat.succ f).totalDegree = f.totalDegree := by
  rw [← weightedTotalDegree_one,
    weightedTotalDegree_rename_of_injective (fun a b h => Nat.succ.inj h),
    Pi.one_comp, weightedTotalDegree_one]

/-- Converse inequality from `cycSh_totalDegree`. Remaining: none. -/
theorem cycSh_totalDegree_ge (f : MvPolynomial ℕ ℚ) :
    f.totalDegree ≤ (rename Nat.succ f).totalDegree :=
  (cycSh_totalDegree f).ge

end

end PrimeGapNormality.Prime
