import PrimeGapNormality.Prime.SieveCutoffCal
import PrimeGapNormality.Prime.EulerProd

/-!
# Canonical cutoff: `V(y) ≤ 1 / log X` and `(15/16)/log X < V(y)`

Lake-green `SieveCutoffCal.isSieveCutoff_eulerProd_asymp` says that if
`y` is a sieve cutoff of `t` with `e^{16} ≤ t`, then

  `(15 / 16) / log t < eulerProd y ∧ eulerProd y ≤ 1 / log t`.

`SieveCutoffCal.sieveCutoff_spec` supplies the least cutoff once
`1 < t`, and `1 < t` follows from `e^{16} ≤ t`. Instantiating at the
canonical cutoff `y = sieveCutoff t` (and at `t = (X : ℝ)`) gives

  `e^{16} ≤ X` ⇒ `eulerProd (sieveCutoff X) ≤ 1 / log X`

and the matching lower bound `(15 / 16) / log X < eulerProd y`.
The `ℕ` product is the same quantity, via
`EulerProd.eulerProd_eq_eulerProdNat` and `Nat.floor_natCast`.

Public names are `crtCutV_`-prefixed so this leaf can sit beside
`CrtCanonicalSieveCutoffRpow` (`crtCut_`) and
`CrtSieveCutoffRpowNat` (`crtRpow_`).

Does **not** claim Mertens / `e^{-γ}`. Does **not** claim
`lateRetention → 0`. Does **not** claim `hden` / Weyl. Does not
import MixZeta, TypicalOsc*, ExactRootWindowClose,
ExactLawTypicalSetMassLeOne, WeylOf*, or SingletonLi.
`G(X) = X` is not the remainder scale.

**Compiled.**
1. `e^{16} ≤ t` ⇒ `1 < t`, hence `sieveCutoff_spec` applies.
2. Two-sided jump at `y = sieveCutoff t`.
3. Upper `eulerProd (sieveCutoff t) ≤ 1 / log t`.
4. Lower `(15 / 16) / log t < eulerProd (sieveCutoff t)`.
5. Same at the integer argument `X : ℕ`.
6. `eulerProd y = eulerProdNat y` at the cutoff.
7. Matching `eulerProdNat` two-sided / upper / lower forms.

**Not compiled.** Mertens. `lateRetention → 0`. `hden` / Weyl.
Chebyshev / `G(X) = X`. Kernel close.

**Remaining hyps.** Pointwise `Real.exp 16 ≤ t` /
`Real.exp 16 ≤ (X : ℝ)` (binder). Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `V(y) ≍ 1/log t` at a sieve cutoff | theorem (`isSieveCutoff_eulerProd_asymp`) |
| canonical `sieveCutoff` is a sieve cutoff | theorem (`sieveCutoff_spec`) |
| `e^{16} ≤ t` ⇒ `1 < t` | theorem (this leaf) |
| `eulerProd (sieveCutoff t) ≤ 1 / log t` | theorem (`crtCutV_eulerProd_le_inv_log`) |
| `(15/16)/log t < eulerProd (sieveCutoff t)` | theorem (`crtCutV_fifteen_div_sixteen_div_log_lt`) |
| same at `X : ℕ` | theorem (`crtCutV_eulerProd_nat_*`) |
| `eulerProd y = eulerProdNat y` at the cutoff | theorem (`crtCutV_eulerProd_eq_eulerProdNat`) |
| `eulerProdNat` two-sided / upper / lower | theorem (`crtCutV_eulerProdNat_*`) |
| `Real.exp 16 ≤ t` / `Real.exp 16 ≤ (X : ℝ)` | remaining hyp (binder) |
| Mertens / `e^{-γ}` | not claimed |
| `lateRetention → 0` | not claimed |
| `hden` / Weyl | not claimed |
| Chebyshev / `G(X) = X` remainder scale | not used |

Does not claim the kernel is closed.

Source: `SieveCutoffCal.isSieveCutoff_eulerProd_asymp`,
`sieveCutoff_spec`; `EulerProd.eulerProd_eq_eulerProdNat`.
Contract: API
-/

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### `e^{16} ≤ t` forces `1 < t` for `sieveCutoff_spec` -/

/-- `e^{16} ≤ t` forces `1 < t` in `ℝ`, so `sieveCutoff_spec` applies. -/
private theorem one_lt_of_exp_sixteen_le {t : ℝ}
    (ht : Real.exp 16 ≤ t) : 1 < t :=
  lt_of_lt_of_le
    (lt_trans (by norm_num : (1 : ℝ) < 2)
      (lt_trans Real.exp_one_gt_two
        (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16))))
    ht

/-! ### Canonical cutoff is a sieve cutoff -/

/-- Least sieve cutoff of `t` once `e^{16} ≤ t`. Remaining hyp:
`Real.exp 16 ≤ t`. -/
theorem crtCutV_sieveCutoff_spec {t : ℝ} (ht : Real.exp 16 ≤ t) :
    IsSieveCutoff t (sieveCutoff t) :=
  sieveCutoff_spec (one_lt_of_exp_sixteen_le ht)

/-- Least sieve cutoff of a large natural `X`. Remaining hyp:
`Real.exp 16 ≤ (X : ℝ)`. -/
theorem crtCutV_sieveCutoff_spec_nat {X : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) :
    IsSieveCutoff (X : ℝ) (sieveCutoff (X : ℝ)) :=
  crtCutV_sieveCutoff_spec hX

/-! ### Two-sided jump `V(y) ≍ 1 / log t` at the canonical cutoff -/

/-- Instantiation of `isSieveCutoff_eulerProd_asymp` at
`y = sieveCutoff t`. Remaining hyp: `Real.exp 16 ≤ t`.
Does not claim Mertens. -/
theorem crtCutV_eulerProd_asymp {t : ℝ} (ht : Real.exp 16 ≤ t) :
    (15 / 16) / Real.log t < eulerProd (sieveCutoff t) ∧
      eulerProd (sieveCutoff t) ≤ 1 / Real.log t :=
  isSieveCutoff_eulerProd_asymp ht (crtCutV_sieveCutoff_spec ht)

/-- Upper jump at the canonical cutoff.
Remaining hyp: `Real.exp 16 ≤ t`. -/
theorem crtCutV_eulerProd_le_inv_log {t : ℝ} (ht : Real.exp 16 ≤ t) :
    eulerProd (sieveCutoff t) ≤ 1 / Real.log t :=
  (crtCutV_eulerProd_asymp ht).2

/-- Matching lower jump `(15/16) / log t < V(y)`.
Remaining hyp: `Real.exp 16 ≤ t`. -/
theorem crtCutV_fifteen_div_sixteen_div_log_lt {t : ℝ}
    (ht : Real.exp 16 ≤ t) :
    (15 / 16) / Real.log t < eulerProd (sieveCutoff t) :=
  (crtCutV_eulerProd_asymp ht).1

/-! ### Integer argument `X : ℕ` -/

/-- Two-sided jump at `y = sieveCutoff (X : ℝ)`. Remaining hyp:
`Real.exp 16 ≤ (X : ℝ)`. -/
theorem crtCutV_eulerProd_nat_asymp {X : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) :
    (15 / 16) / Real.log (X : ℝ) < eulerProd (sieveCutoff (X : ℝ)) ∧
      eulerProd (sieveCutoff (X : ℝ)) ≤ 1 / Real.log (X : ℝ) :=
  crtCutV_eulerProd_asymp hX

/-- `e^{16} ≤ X` ⇒ `eulerProd (sieveCutoff X) ≤ 1 / log X`.
Remaining hyp: `Real.exp 16 ≤ (X : ℝ)`. -/
theorem crtCutV_eulerProd_nat_le_inv_log {X : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) :
    eulerProd (sieveCutoff (X : ℝ)) ≤ 1 / Real.log (X : ℝ) :=
  crtCutV_eulerProd_le_inv_log hX

/-- Matching lower bound at the integer argument.
Remaining hyp: `Real.exp 16 ≤ (X : ℝ)`. -/
theorem crtCutV_fifteen_div_sixteen_div_log_lt_nat {X : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) :
    (15 / 16) / Real.log (X : ℝ) < eulerProd (sieveCutoff (X : ℝ)) :=
  crtCutV_fifteen_div_sixteen_div_log_lt hX

/-! ### `ℕ` product via `eulerProd_eq_eulerProdNat` -/

/-- `V` on the cutoff coincides with `eulerProdNat`, by
`eulerProd_eq_eulerProdNat` and `⌊n⌋ = n`. -/
theorem crtCutV_eulerProd_eq_eulerProdNat (t : ℝ) :
    eulerProd (sieveCutoff t) = eulerProdNat (sieveCutoff t) :=
  (eulerProd_eq_eulerProdNat (sieveCutoff t)).trans
    (congrArg eulerProdNat (Nat.floor_natCast (sieveCutoff t)))

/-- Two-sided jump for `eulerProdNat` at the canonical cutoff.
Remaining hyp: `Real.exp 16 ≤ t`. -/
theorem crtCutV_eulerProdNat_asymp {t : ℝ} (ht : Real.exp 16 ≤ t) :
    (15 / 16) / Real.log t < eulerProdNat (sieveCutoff t) ∧
      eulerProdNat (sieveCutoff t) ≤ 1 / Real.log t := by
  rw [← crtCutV_eulerProd_eq_eulerProdNat]
  exact crtCutV_eulerProd_asymp ht

/-- Upper jump for `eulerProdNat`. Remaining hyp: `Real.exp 16 ≤ t`. -/
theorem crtCutV_eulerProdNat_le_inv_log {t : ℝ}
    (ht : Real.exp 16 ≤ t) :
    eulerProdNat (sieveCutoff t) ≤ 1 / Real.log t :=
  (crtCutV_eulerProdNat_asymp ht).2

/-- Matching lower jump for `eulerProdNat`. Remaining hyp:
`Real.exp 16 ≤ t`. -/
theorem crtCutV_fifteen_div_sixteen_div_log_lt_eulerProdNat {t : ℝ}
    (ht : Real.exp 16 ≤ t) :
    (15 / 16) / Real.log t < eulerProdNat (sieveCutoff t) :=
  (crtCutV_eulerProdNat_asymp ht).1

/-- Integer-argument `eulerProdNat` form.
Remaining hyp: `Real.exp 16 ≤ (X : ℝ)`. -/
theorem crtCutV_eulerProdNat_nat_asymp {X : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) :
    (15 / 16) / Real.log (X : ℝ) <
        eulerProdNat (sieveCutoff (X : ℝ)) ∧
      eulerProdNat (sieveCutoff (X : ℝ)) ≤ 1 / Real.log (X : ℝ) :=
  crtCutV_eulerProdNat_asymp hX

/-- `e^{16} ≤ X` ⇒ `eulerProdNat (sieveCutoff X) ≤ 1 / log X`.
Remaining hyp: `Real.exp 16 ≤ (X : ℝ)`. -/
theorem crtCutV_eulerProdNat_nat_le_inv_log {X : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) :
    eulerProdNat (sieveCutoff (X : ℝ)) ≤ 1 / Real.log (X : ℝ) :=
  crtCutV_eulerProdNat_le_inv_log hX

/-- Matching lower `eulerProdNat` bound at the integer argument.
Remaining hyp: `Real.exp 16 ≤ (X : ℝ)`. -/
theorem crtCutV_fifteen_div_sixteen_div_log_lt_eulerProdNat_nat {X : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) :
    (15 / 16) / Real.log (X : ℝ) <
      eulerProdNat (sieveCutoff (X : ℝ)) :=
  crtCutV_fifteen_div_sixteen_div_log_lt_eulerProdNat hX

end

end PrimeGapNormality.Prime
