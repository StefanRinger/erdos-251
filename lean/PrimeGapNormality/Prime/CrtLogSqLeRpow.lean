import PrimeGapNormality.Prime.EulerProd
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Eventual `(log X)^2 ≤ X^{e^{-30}}`

Polynomial-in-log versus the Euler-product cutoff power
`c = eulerProdLowerConst > 0` (`eulerProdLowerConst_pos`). Mathlib
`isLittleO_log_rpow_rpow_atTop` (from `isLittleO_log_rpow_atTop`)
gives `(log x)^2 = o(x^c)` at `+∞`, hence the ratio tends to `0` and
the comparison holds eventually on `ℝ` and along `ℕ`.

This is the log-square half of the `profileS ≤ sieveCutoff` cutoff
comparison. This leaf does **not** import `ProfileSLeSieveCutoff`,
`CrtCanonicalSieveCutoffRpow`, MixZeta, TypicalOsc*, or Weyl, and
does **not** claim `profileS ≤ sieveCutoff`.

Does **not** claim Chebyshev / `G(X) = X`. Kernel not closed.

**Compiled.**
1. `(log x)^(2 : ℝ) = o(x^c)` at `atTop`.
2. `(log x)^(2 : ℝ) / x^c → 0`.
3. Eventual `(Real.log x)^2 ≤ x ^ eulerProdLowerConst` on `ℝ`.
4. Same along `X : ℕ`.

**Not compiled.** `profileS ≤ sieveCutoff`. Explicit finite `X₀`.
Off-band. MixZeta. Weyl. Kernel close.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `c = eulerProdLowerConst > 0` | theorem (`eulerProdLowerConst_pos`) |
| `(log x)^2 = o(x^c)` | theorem (`crtLogSq_isLittleO_log_sq_rpow`) |
| ratio `→ 0` | theorem (`crtLogSq_tendsto_log_sq_div_rpow`) |
| eventual `(log x)^2 ≤ x^c` (`ℝ`) | theorem (`crtLogSq_eventually_log_sq_le_rpow`) |
| same at `X : ℕ` | theorem (`crtLogSq_eventually_nat_log_sq_le_rpow`) |
| explicit finite threshold `X₀` | remaining (Filter-eventual only) |
| `profileS ≤ sieveCutoff` | not claimed |
| Chebyshev / `G(X) = X` remainder scale | not used |

Does not claim the kernel is closed.

Source: `EulerProd.eulerProdLowerConst`, `eulerProdLowerConst_pos`;
`isLittleO_log_rpow_rpow_atTop`.
Contract: API
-/

open Filter Asymptotics

namespace PrimeGapNormality.Prime

noncomputable section

/-- `(log x)^2 = o(x^c)` at `+∞`, `c = eulerProdLowerConst > 0`. -/
theorem crtLogSq_isLittleO_log_sq_rpow :
    (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop]
      fun x => x ^ eulerProdLowerConst :=
  isLittleO_log_rpow_rpow_atTop (2 : ℝ) eulerProdLowerConst_pos

/-- Ratio form of the little-o comparison. Remaining: none
(compiled `eulerProdLowerConst_pos`). -/
theorem crtLogSq_tendsto_log_sq_div_rpow :
    Tendsto (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ eulerProdLowerConst)
      atTop (nhds 0) :=
  crtLogSq_isLittleO_log_sq_rpow.tendsto_div_nhds_zero

/-- Pointwise comparison once `1 < x` and the little-o bound holds.
Remaining hyp: `1 < x`. -/
private theorem crtLogSq_log_sq_le_rpow_of_one_lt {x : ℝ} (hx : 1 < x)
    (hle : ‖Real.log x ^ (2 : ℝ)‖ ≤ ‖x ^ eulerProdLowerConst‖) :
    Real.log x ^ 2 ≤ x ^ eulerProdLowerConst := by
  have hlog0 : (0 : ℝ) ≤ Real.log x := (Real.log_pos hx).le
  have hnum : (0 : ℝ) ≤ Real.log x ^ (2 : ℝ) := Real.rpow_nonneg hlog0 _
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hden : (0 : ℝ) ≤ x ^ eulerProdLowerConst :=
    (Real.rpow_pos_of_pos hx0 _).le
  have hle' : Real.log x ^ (2 : ℝ) ≤ x ^ eulerProdLowerConst := by
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnum,
      abs_of_nonneg hden] at hle
  rwa [Real.rpow_two] at hle'

/-- Eventual real comparison `(log x)^2 ≤ x^c`. Remaining: Filter
`atTop` (no explicit `X₀`). Does not claim `profileS ≤ sieveCutoff`. -/
theorem crtLogSq_eventually_log_sq_le_rpow :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ x ^ eulerProdLowerConst := by
  filter_upwards [crtLogSq_isLittleO_log_sq_rpow.eventuallyLE,
    eventually_gt_atTop (1 : ℝ)] with x hnorm hx1
  exact crtLogSq_log_sq_le_rpow_of_one_lt hx1 hnorm

/-- Same comparison along `ℕ`. Remaining: Filter `atTop`. Does not
claim `profileS ≤ sieveCutoff`. -/
theorem crtLogSq_eventually_nat_log_sq_le_rpow :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ^ 2 ≤ (X : ℝ) ^ eulerProdLowerConst :=
  tendsto_natCast_atTop_atTop.eventually crtLogSq_eventually_log_sq_le_rpow

end

end PrimeGapNormality.Prime
