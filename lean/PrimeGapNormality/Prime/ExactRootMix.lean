import PrimeGapNormality.Prime.ActualRootLaw
import PrimeGapNormality.Prime.SieveCutoffCal
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# v0.4 finite root mix: weights `V(y_t)`, not `1/log t`

For integer `X` and `t ∈ Ioc X (2X)`:

  `y_t = sieveCutoff t`
  `w_t = eulerProdNat y_t`   -- paper `V(y_t)`
  `Z_X = ∑_t w_t`
  `ν_X(U) = ∑_t w_t * actualRootLaw(y_t,S,U) / Z_X`
  `ν̃_X(U) = ∑_t w_t * actualRootLaw(y_t,S,U) / N_X`

This **replaces** the R105 sketch with weights `1/log t`. Do not keep
both. `RootMix.hlRootWeight` is a different object and is not this
adapter.

Unnormalized `ν̃` is the Stopped input; divide by `Z_X` only after the
finite comparison. `|Z_X/N_X - 1|` is not multiplied by `exp(C L)`.

R106/09 Paket 2. Does not prove `Z_X/N_X → 1` or the Riemann bound.

Source: `rounds/round106/09_gpt_v04_lean_audit_and_grok_order.md` Paket 2;
`rounds/round106/05_grok_digestion_delta.md` §2;
`ActualRootLaw`; `SieveCutoffCal.sieveCutoff`; `EulerProd.eulerProdNat`.
Contract: API
Audit: GREEN
-/

open Finset

namespace PrimeGapNormality.Prime

/-- Mix support `{X+1,…,2X}`. -/
def mixScale (X : ℕ) : Finset ℕ :=
  Ioc X (2 * X)

/-- Exact root-density weight `V(y_t)`. Not `1 / log t`. -/
noncomputable def mixWeightV (t : ℕ) : ℝ :=
  eulerProdNat (sieveCutoff (t : ℝ))

/-- `Z_X = ∑_{X<t≤2X} V(y_t)`. -/
noncomputable def mixZ (X : ℕ) : ℝ :=
  ∑ t ∈ mixScale X, mixWeightV t

/-- Normalized finite mix `ν_X`. -/
noncomputable def finiteRootMix (X S : ℕ) (U : Finset ℕ) : ℝ :=
  (∑ t ∈ mixScale X, mixWeightV t *
      actualRootLaw (sieveCutoff (t : ℝ)) S U) / mixZ X

/-- Unnormalized mix `ν̃_X = (Z_X / N_X) ν_X`, used before Stopped. -/
noncomputable def finiteRootMixUnnorm (X S : ℕ) (U : Finset ℕ) : ℝ :=
  (∑ t ∈ mixScale X, mixWeightV t *
      actualRootLaw (sieveCutoff (t : ℝ)) S U) / (windowNX X : ℝ)

/-- Scalar `ζ_X = Z_X / N_X`. Paid additively after Stopped. -/
noncomputable def mixZeta (X : ℕ) : ℝ :=
  mixZ X / (windowNX X : ℝ)

theorem mixWeightV_nonneg (t : ℕ) : 0 ≤ mixWeightV t :=
  (eulerProdNat_pos (sieveCutoff (t : ℝ))).le

theorem mixZ_nonneg (X : ℕ) : 0 ≤ mixZ X :=
  sum_nonneg fun t _ => mixWeightV_nonneg t

end PrimeGapNormality.Prime
