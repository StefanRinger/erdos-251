import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic

/-!
# Falling factorial monotonicity `(N-1)_r ≤ (N)_r`

Paper v0.16 (R119/19): physical multiple deletion of auxiliary
frames couples to the original coupon moments by the algebra

    `(N-1)_r ≤ (N)_r`.

Mathlib `N.descFactorial r` is the falling factorial `(N)_r`.
This leaf is that comparison, **not** a CRT law, **not** a Selberg
cap, and **not** the `8^r` density hull.

Does **not** compile `(N-1)_r ≤ N^r` (BinomPowBound already has
the stronger `C(n,j) * j! ≤ n^j`; not imported, not a `5L`
envelope). Does **not** import MixZeta, SingletonLi, Kernel,
EndAPI, UniformAuxFrame, SelbergHarmonicJ, or SelbergLambdaSq.
Does **not** touch the auxiliary-frame identity.

**Compiled.**
1. `M ≤ N` ⇒ `M.descFactorial r ≤ N.descFactorial r`
   (`Nat.descFactorial_le`).
2. `(N-1).descFactorial r ≤ N.descFactorial r`.
3. Same after `ℕ → ℝ`.

**Not compiled.** Selberg cap. `8^r` hull. Auxiliary-frame
identity. MixZeta. SingletonLi. Kernel. EndAPI. `5L`.
`(N-1)_r ≤ N^r`. CRT identification of the coupon product.

**Remaining hyps.** None: the inequalities are unconditional in
`N, r : ℕ` (`N = 0` is `(0)_r ≤ (0)_r`). Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `M ≤ N` ⇒ `(M)_r ≤ (N)_r` | theorem (`descFact_le`) |
| `(N-1)_r ≤ (N)_r` | theorem (`descFact_pred_le`) |
| same over `ℝ` | theorem (`descFact_pred_le_real`) |
| `(N-1)_r ≤ N^r` / `5L` | not claimed |
| Selberg cap / `8^r` / CRT coupon law | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round119/19_grok_v016_positive_frames_delta.md`;
`Mathlib.Data.Nat.Factorial.Basic` (`Nat.descFactorial_le`).
Contract: API
-/

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Natural numbers: `(M)_r ≤ (N)_r` if `M ≤ N` -/

/-- Mathlib `Nat.descFactorial_le`. Paper `(a)_r` is `a.descFactorial r`. -/
theorem descFact_le (M N r : ℕ) (hMN : M ≤ N) :
    M.descFactorial r ≤ N.descFactorial r :=
  Nat.descFactorial_le r hMN

/-- Physical multiple-deletion coupling: `(N-1)_r ≤ (N)_r`. -/
theorem descFact_pred_le (N r : ℕ) :
    (N - 1).descFactorial r ≤ N.descFactorial r :=
  descFact_le (N - 1) N r (Nat.sub_le N 1)

/-! ### Reals: the same inequality after `ℕ → ℝ` -/

/-- Cast of `descFact_pred_le`. Does **not** claim a `5L` moment. -/
theorem descFact_pred_le_real (N r : ℕ) :
    ((N - 1).descFactorial r : ℝ) ≤ (N.descFactorial r : ℝ) :=
  (Nat.cast_le (α := ℝ)).mpr (descFact_pred_le N r)

end

end PrimeGapNormality.Prime
