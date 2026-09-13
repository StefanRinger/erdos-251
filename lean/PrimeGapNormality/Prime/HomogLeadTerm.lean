import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Ring.Rat
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Isolated top homogeneous part `P = F^[d]`

Paper v0.23 (Lemma `lem:onepoint`): the one-point test uses the
**top homogeneous part** `P = F^[d]`, not all of `F`. The greatest
variable index `h` is taken on `P`. Mixed-degree regression

    `F = u₀³ + u₀ u₅`

has top part `P = u₀³`, hence `h = 0` (not `h = 5` from `F`).

This leaf isolates **only** the Mathlib homogeneous component
`homogeneousComponent` / `IsHomogeneous` on `MvPolynomial ℕ ℚ`.
It does **not** compile cyclic normal form, the S/T criterion,
the converse one-point classification, MixZeta, SingletonLi,
Kernel, Weyl, or `4ϑ`. It does **not** import or edit
`rounds/round110/15_spark_local_polynomial_core.lean`.

Unique names `onePt_`. Imports Mathlib `MvPolynomial.Degrees`,
`MvPolynomial.Variables`, `RingTheory.MvPolynomial.Homogeneous`,
and `Algebra.Ring.Rat` (coefficient ring `ℚ`, held fixed).
No `open Nat`. Does **not** import MixZeta, SingletonLi, Kernel,
EndAPI, Weyl, OnePointMean, or the R110/15 core. Does **not**
edit `All.lean`.

**Compiled.**
1. `C 0` has total degree `0` and is homogeneous of degree `0`.
   For `0 < d`, `homogeneousComponent d (C 0) = 0`. Not `omega`.
2. `X 0 ^ 3` is homogeneous of degree `3` (`IsHomogeneous`).
3. Regression: `X 0 * X 5` has total degree `2`, and
   `homogeneousComponent 3 (X 0 ^ 3 + X 0 * X 5) = X 0 ^ 3`.
4. Optional: `homogeneousComponent 2 (X 0 ^ 3 + X 0 * X 5) =
   X 0 * X 5`. Optional: `(X 0 ^ 3).vars = {0}` (`h = 0`).

**Not compiled.** Cyclic normal form `N_(B,k)`. Local cohomological
equation `(B-A)H = F`. Converse classification
`N F = 0 ⇔ telescope ⇔ ∂_v π_s ≡ 0`. The action `π_s`.
MixZeta. SingletonLi. Kernel. Weyl. `4ϑ`. S/T.

**Remaining hyps.** None on (1)–(4). Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `C 0` homogeneous of degree `0` | theorem (`onePt_C_zero_isHomogeneous`) |
| `totalDegree (C 0) = 0` | theorem (`onePt_C_zero_totalDegree`) |
| `0 < d` ⇒ component `d` of `C 0` is `0` | theorem (`onePt_C_zero_component`) |
| `X 0 ^ 3` homogeneous of degree `3` | theorem (`onePt_X_pow_three_isHomogeneous`) |
| `X 0 * X 5` homogeneous of degree `2` | theorem (`onePt_X_mul_isHomogeneous`) |
| `totalDegree (X 0 * X 5) = 2` | theorem (`onePt_X_mul_totalDegree`) |
| component `3` of `u₀³+u₀u₅` is `u₀³` | theorem (`onePt_regression_lead`) |
| component `2` of `u₀³+u₀u₅` is `u₀u₅` | theorem (`onePt_regression_deg2`) |
| `vars (u₀³) = {0}` (`h = 0`) | theorem (`onePt_lead_vars`) |
| cyclic normal form / S/T / converse | not claimed |
| MixZeta / SingletonLi / Kernel / Weyl / `4ϑ` | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round126/22_paper_v0_23.tex` Lemma `lem:onepoint`;
`rounds/round126/27_grok_v023_endpoints_handover.md`.
SHA-256 `2e5c8f8627b801af2a69c254733331cc43e11ce105f886725fcc455b9a9163b8`.
Mathlib `IsHomogeneous`, `homogeneousComponent`, `totalDegree`, `vars`.
Contract: API
-/

namespace PrimeGapNormality.Prime

open MvPolynomial

noncomputable section

/-! ### `C 0`: degree `0`, higher components vanish -/

/-- Mathlib `isHomogeneous_C`. Remaining: none. -/
theorem onePt_C_zero_isHomogeneous :
    (C (0 : ℚ) : MvPolynomial ℕ ℚ).IsHomogeneous 0 :=
  isHomogeneous_C ℕ (0 : ℚ)

/-- Mathlib `totalDegree_C`. Remaining: none. -/
theorem onePt_C_zero_totalDegree :
    (C (0 : ℚ) : MvPolynomial ℕ ℚ).totalDegree = 0 :=
  totalDegree_C (0 : ℚ)

/-- Higher homogeneous components of `C 0` vanish. Remaining: `0 < d`.
Not `omega`. -/
theorem onePt_C_zero_component {d : ℕ} (hd : 0 < d) :
    homogeneousComponent d (C (0 : ℚ) : MvPolynomial ℕ ℚ) = 0 :=
  homogeneousComponent_eq_zero d _
    (lt_of_eq_of_lt onePt_C_zero_totalDegree hd)

/-! ### `X 0 ^ 3` is homogeneous of degree `3` -/

/-- Mathlib `isHomogeneous_X_pow`. Remaining: none. -/
theorem onePt_X_pow_three_isHomogeneous :
    ((X 0 : MvPolynomial ℕ ℚ) ^ 3).IsHomogeneous 3 :=
  isHomogeneous_X_pow (0 : ℕ) 3

/-! ### Mixed term `X 0 * X 5` has degree `2` -/

/-- Product of two distinct variables is homogeneous of degree `2`. -/
theorem onePt_X_mul_isHomogeneous :
    (X 0 * X 5 : MvPolynomial ℕ ℚ).IsHomogeneous 2 :=
  (isHomogeneous_X ℚ (0 : ℕ)).mul (isHomogeneous_X ℚ 5)

/-- Remaining: none. Not `omega`. -/
theorem onePt_X_mul_ne_zero :
    (X 0 * X 5 : MvPolynomial ℕ ℚ) ≠ 0 :=
  mul_ne_zero (X_ne_zero 0) (X_ne_zero 5)

/-- Mathlib `IsHomogeneous.totalDegree`. Remaining: none. -/
theorem onePt_X_mul_totalDegree :
    (X 0 * X 5 : MvPolynomial ℕ ℚ).totalDegree = 2 :=
  onePt_X_mul_isHomogeneous.totalDegree onePt_X_mul_ne_zero

/-! ### Regression: top part of `u₀³ + u₀ u₅` is `u₀³` -/

/-- `P = F^[3]`. The greatest index is taken on `P`, not on `F`.
Remaining: none. Not `omega`. -/
theorem onePt_regression_lead :
    homogeneousComponent 3
      (X 0 ^ 3 + X 0 * X 5 : MvPolynomial ℕ ℚ) =
      X 0 ^ 3 := by
  have hlt :
      (X 0 * X 5 : MvPolynomial ℕ ℚ).totalDegree < 3 := by
    rw [onePt_X_mul_totalDegree]
    exact Nat.lt_succ_self 2
  have hsum :=
    (homogeneousComponent (σ := ℕ) (R := ℚ) 3).map_add
      (X 0 ^ 3) (X 0 * X 5)
  rw [hsum, homogeneousComponent_eq_self onePt_X_pow_three_isHomogeneous,
    homogeneousComponent_eq_zero 3 (X 0 * X 5) hlt, add_zero]

/-- Optional degree-`2` summand of the same mixed polynomial. -/
theorem onePt_regression_deg2 :
    homogeneousComponent 2
      (X 0 ^ 3 + X 0 * X 5 : MvPolynomial ℕ ℚ) =
      X 0 * X 5 := by
  have hne : (2 : ℕ) ≠ 3 := Ne.symm (Nat.succ_ne_self 2)
  have hsum :=
    (homogeneousComponent (σ := ℕ) (R := ℚ) 2).map_add
      (X 0 ^ 3) (X 0 * X 5)
  rw [hsum, homogeneousComponent_of_mem (n := 3) onePt_X_pow_three_isHomogeneous,
    if_neg hne, zero_add,
    homogeneousComponent_eq_self onePt_X_mul_isHomogeneous]

/-- Optional: `h = 0` on the top part `P = u₀³`. -/
theorem onePt_lead_vars :
    ((X 0 : MvPolynomial ℕ ℚ) ^ 3).vars = {0} := by
  rw [X_pow_eq_monomial]
  exact vars_monomial_single (0 : ℕ) (Nat.succ_ne_zero 2) one_ne_zero

end

end PrimeGapNormality.Prime
