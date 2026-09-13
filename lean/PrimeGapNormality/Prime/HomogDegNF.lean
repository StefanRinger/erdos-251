import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Ring.Rat
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Isolated degree bound on the homogeneous / normal-form part

Paper v0.23: the degree condition is on the **normal form** /
the homogeneous summand, not the visible degree of all of `F`.
This leaf isolates **only** Mathlib `totalDegree` versus
`IsHomogeneous` / `homogeneousComponent` on `MvPolynomial ℕ ℚ`.

It does **not** import `HomogLeadTerm` (`onePt_`) and does
**not** steal the mixed-degree regression
`X 0 ^ 3 + X 0 * X 5`. That `F^[3]` test stays on `onePt_`.
It does **not** import `CycShiftRename` (`cycSh_`). Unique
names `degNF_` only. Clash-check: no `onePt_`, no `cycSh_`.

Unique names `degNF_`. Imports Mathlib `MvPolynomial.Degrees`,
`MvPolynomial.Variables`, `RingTheory.MvPolynomial.Homogeneous`,
and `Algebra.Ring.Rat` (coefficient ring `ℚ`, held fixed).
No `open Nat`. Does **not** import MixZeta, SingletonLi, Kernel,
EndAPI, Weyl, HomogLeadTerm, or CycShiftRename. Does **not**
edit `All.lean`.

**Compiled.**
1. `{f : MvPolynomial ℕ ℚ} {d : ℕ}`: `IsHomogeneous d f` ⇒
   `totalDegree f ≤ d` (Mathlib `IsHomogeneous.totalDegree_le`).
2. `{f : MvPolynomial ℕ ℚ} {d : ℕ}`:
   `totalDegree (homogeneousComponent d f) ≤ d`.
3. Optional: `f ≠ 0` and `IsHomogeneous d f` ⇒
   `totalDegree f = d` (Mathlib `IsHomogeneous.totalDegree`).
4. Optional: `homogeneousComponent d f` is `IsHomogeneous d`.
5. Small example: `C (1 : ℚ)` has total degree `0` and is
   homogeneous of degree `0`. Not the `onePt_` regression.

**Not compiled.** Cyclic normal form. S/T. Weyl. MixZeta.
SingletonLi. Kernel. `¬ hs`. HomogLeadTerm `F^[3]` regression
`X 0 ^ 3 + X 0 * X 5`. CycShiftRename.

**Remaining hyps.** None on (1), (2), (4), (5). Binder `f ≠ 0`
on (3). Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `IsHomogeneous d f` ⇒ `totalDegree f ≤ d` | theorem (`degNF_isHomogeneous_totalDegree_le`) |
| `totalDegree (homogeneousComponent d f) ≤ d` | theorem (`degNF_homogeneousComponent_totalDegree_le`) |
| `f ≠ 0` and homogeneous ⇒ `totalDegree f = d` | theorem (`degNF_isHomogeneous_totalDegree`) |
| `homogeneousComponent d f` is homogeneous of degree `d` | theorem (`degNF_homogeneousComponent_isHomogeneous`) |
| `C 1` homogeneous of degree `0` | theorem (`degNF_C_one_isHomogeneous`) |
| `totalDegree (C 1) = 0` | theorem (`degNF_C_one_totalDegree`) |
| cyclic NF / S/T / Weyl / MixZeta / SingletonLi / Kernel / `¬ hs` | not claimed |
| `onePt_` regression `F^[3]` | not claimed (not imported) |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round126/22_paper_v0_23.tex`;
`rounds/round126/27_grok_v023_endpoints_handover.md`.
SHA-256 `2e5c8f8627b801af2a69c254733331cc43e11ce105f886725fcc455b9a9163b8`.
Mathlib `IsHomogeneous.totalDegree_le`, `IsHomogeneous.totalDegree`,
`homogeneousComponent_isHomogeneous`, `totalDegree_C`,
`isHomogeneous_C`.
Contract: API
-/

namespace PrimeGapNormality.Prime

open MvPolynomial

noncomputable section

/-! ### Homogeneous polynomials: `totalDegree ≤ d` -/

/-- Mathlib `IsHomogeneous.totalDegree_le`. Remaining: none.
Lean binder is `f.IsHomogeneous d`. -/
theorem degNF_isHomogeneous_totalDegree_le {f : MvPolynomial ℕ ℚ} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    f.totalDegree ≤ d :=
  hf.totalDegree_le

/-! ### Optional: each homogeneous component is homogeneous -/

/-- Mathlib `homogeneousComponent_isHomogeneous`. Remaining: none. -/
theorem degNF_homogeneousComponent_isHomogeneous {f : MvPolynomial ℕ ℚ}
    {d : ℕ} :
    (homogeneousComponent d f).IsHomogeneous d :=
  homogeneousComponent_isHomogeneous d f

/-! ### Degree of the degree-`d` component is at most `d` -/

/-- Follows from `degNF_homogeneousComponent_isHomogeneous` and
`degNF_isHomogeneous_totalDegree_le`. Remaining: none. -/
theorem degNF_homogeneousComponent_totalDegree_le {f : MvPolynomial ℕ ℚ}
    {d : ℕ} :
    (homogeneousComponent d f).totalDegree ≤ d :=
  degNF_isHomogeneous_totalDegree_le degNF_homogeneousComponent_isHomogeneous

/-! ### Optional: nonzero homogeneous polynomials have exact degree `d` -/

/-- Mathlib `IsHomogeneous.totalDegree`. Remaining: `f ≠ 0`. -/
theorem degNF_isHomogeneous_totalDegree {f : MvPolynomial ℕ ℚ} {d : ℕ}
    (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    f.totalDegree = d :=
  hf.totalDegree h0

/-! ### Small example: `C 1` has degree `0` (not the `onePt_` regression) -/

/-- Mathlib `isHomogeneous_C`. Remaining: none. Not `C 0`. -/
theorem degNF_C_one_isHomogeneous :
    (C (1 : ℚ) : MvPolynomial ℕ ℚ).IsHomogeneous 0 :=
  isHomogeneous_C ℕ (1 : ℚ)

/-- Mathlib `totalDegree_C`. Remaining: none. Not `omega`. -/
theorem degNF_C_one_totalDegree :
    (C (1 : ℚ) : MvPolynomial ℕ ℚ).totalDegree = 0 :=
  totalDegree_C (1 : ℚ)

end

end PrimeGapNormality.Prime
