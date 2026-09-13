import PrimeGapNormality.Prime.UniformAuxFrame
import PrimeGapNormality.Prime.GoodCountFourTheta

/-!
# Auxiliary-frame coefficient `C(M, n−1)/C(M, n) = n/(M−n+1) ≤ 4 ϑ`

Paper v0.16, R119/19. The uniform auxiliary-frame identity of
lake-OK `UniformAuxFrame` has coefficient `n/(M−n+1)`. That
quotient equals the binomial ratio `C(M, n−1)/C(M, n)`
(`auxFrame_choose_ratio`). Under the binders of lake-OK
`GoodCountFourTheta`, the same coefficient is `≤ 4 ϑ`.

The binder `ϑ ≤ 1/4` is the finite substitute for the paper's
eventual `N ≤ M/2` from `ϑ → 0`. It remains a **hypothesis**, not a
theorem about the actual count `N`.

This leaf is **only** that identification and the good-count
comparison. It does **not** compile the uniform mean identity again,
does **not** apply `GenericFrameMassEqGeL` (in particular not to
`μ · f`), and does **not** import MixZeta, SingletonLi, Kernel, or
5L. It does **not** edit EulerVLogHalf or SubsetSpacingJoint.

Unique names `auxTheta_`.

**Compiled.**
1. `C(M, n−1)/C(M, n) = n/(M−n+1)` (`1 ≤ n ≤ M`).
2. Same from the good-count binder `0 < n` (`n ≤ M`).
3. Same with `M = |A|`.
4. `n/(M−n+1) ≤ 4 ϑ` under the `goodCount_` binders
   `0 < n`, `n ≤ M`, `n ≤ 2 M ϑ` (or `n ≤ 2 ϑ M`), `0 < ϑ`,
   and `ϑ ≤ 1/4`. Natural-number wrappers.
5. Same chain without `ϑ ≤ 1/4` on the remaining `n ≤ M/2`.
6. Combined: `C(M, n−1)/C(M, n) ≤ 4 ϑ` under those binders
   (and with `M = |A|`).

**Not compiled.** Uniform auxiliary-frame mean identity (already
`UniformAuxFrame`). `GenericFrameMassEqGeL` on `μ · f`. MixZeta.
SingletonLi. 5L. Kernel. (C4). Selberg. `8^r`. A theorem `ϑ ≤ 1/4`
for the actual `N`.

**Remaining hyps.** Binders in (4) and (6): `0 < n`, `n ≤ M`,
`n ≤ 2 M ϑ` (paper good count `N ≤ 2 M ϑ`, not discharged),
`0 < ϑ`, and `ϑ ≤ 1/4` (or else `n ≤ M/2`). Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `C(M, n−1)/C(M, n) = n/(M−n+1)` | theorem (`auxFrame_choose_ratio`) |
| `n/(M−n+1) ≤ 4 ϑ` | theorem (`goodCount_` binders) |
| `C(M, n−1)/C(M, n) ≤ 4 ϑ` | theorem (chain of the two) |
| `ϑ ≤ 1/4` for the actual `N` | remaining hyp |
| `GenericFrameMassEqGeL` on `μ · f` | not used |
| MixZeta / SingletonLi / 5L / kernel | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round119/19_grok_v016_positive_frames_delta.md`;
`UniformAuxFrame.auxFrame_choose_ratio`,
`GoodCountFourTheta.goodCount_ratio_le_four_theta`.
Contract: API
-/

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Binomial quotient `C(M, n−1)/C(M, n) = n/(M−n+1)` -/

/-- Paper coefficient of the auxiliary-frame identity, as a
binomial ratio. Remaining: `1 ≤ n ≤ M`. -/
theorem auxTheta_choose_ratio {M n : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    (M.choose (n - 1) : ℝ) / (M.choose n : ℝ) =
      (n : ℝ) / ((M : ℝ) - n + 1) :=
  auxFrame_choose_ratio hn hnM

/-- Same identity from the good-count binder `0 < n`. -/
theorem auxTheta_choose_ratio_pos {M n : ℕ} (hn : 0 < n) (hnM : n ≤ M) :
    (M.choose (n - 1) : ℝ) / (M.choose n : ℝ) =
      (n : ℝ) / ((M : ℝ) - n + 1) :=
  auxTheta_choose_ratio (Nat.succ_le_of_lt hn) hnM

/-- Carrier form `M = |A|`. Remaining: `1 ≤ n ≤ |A|`. -/
theorem auxTheta_choose_ratio_card {A : Finset ℕ} {n : ℕ}
    (hn : 1 ≤ n) (hnM : n ≤ A.card) :
    (A.card.choose (n - 1) : ℝ) / (A.card.choose n : ℝ) =
      (n : ℝ) / ((A.card : ℝ) - n + 1) :=
  auxTheta_choose_ratio hn hnM

/-! ### Good-count bound `n/(M−n+1) ≤ 4 ϑ` -/

/-- Remaining: `0 < n`, `n ≤ M`, `n ≤ 2 M ϑ`, `0 < ϑ`, and the
binder `ϑ ≤ 1/4` (not a theorem about `N`). -/
theorem auxTheta_ratio_le_four_theta {n M ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : n ≤ (2 : ℝ) * M * ϑ)
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    n / (M - n + 1) ≤ (4 : ℝ) * ϑ :=
  goodCount_ratio_le_four_theta hn hnM hbound hϑ hθ4

/-- Same with the commuted binder `n ≤ 2 ϑ M`. -/
theorem auxTheta_ratio_le_four_theta_comm {n M ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : n ≤ (2 : ℝ) * ϑ * M)
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    n / (M - n + 1) ≤ (4 : ℝ) * ϑ :=
  goodCount_ratio_le_four_theta_comm hn hnM hbound hϑ hθ4

/-- Natural counts. Remaining: `0 < n`, `n ≤ M`,
`(n : ℝ) ≤ 2 M ϑ`, `0 < ϑ`, and binder `ϑ ≤ 1/4`. -/
theorem auxTheta_ratio_le_four_theta_nat {n M : ℕ} {ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : (n : ℝ) ≤ (2 : ℝ) * (M : ℝ) * ϑ)
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    (n : ℝ) / ((M : ℝ) - n + 1) ≤ (4 : ℝ) * ϑ :=
  goodCount_ratio_le_four_theta_nat hn hnM hbound hϑ hθ4

theorem auxTheta_ratio_le_four_theta_nat_comm {n M : ℕ} {ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : (n : ℝ) ≤ (2 : ℝ) * ϑ * (M : ℝ))
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    (n : ℝ) / ((M : ℝ) - n + 1) ≤ (4 : ℝ) * ϑ :=
  goodCount_ratio_le_four_theta_nat_comm hn hnM hbound hϑ hθ4

/-- Paper chain on `n ≤ M/2`, without the binder `ϑ ≤ 1/4`.
Remaining: `0 ≤ n`, `0 < M`, `n ≤ M/2`, and `n ≤ 2 M ϑ`. -/
theorem auxTheta_ratio_le_four_theta_of_le_half {n M ϑ : ℝ}
    (hn : 0 ≤ n) (hM : 0 < M) (hhalf : n ≤ M / 2)
    (hbound : n ≤ (2 : ℝ) * M * ϑ) :
    n / (M - n + 1) ≤ (4 : ℝ) * ϑ :=
  goodCount_ratio_le_four_theta_of_le_half hn hM hhalf hbound

/-! ### Combined `C(M, n−1)/C(M, n) ≤ 4 ϑ` -/

/-- Auxiliary-frame coefficient under good counts. Remaining:
`0 < n`, `n ≤ M`, `(n : ℝ) ≤ 2 M ϑ`, `0 < ϑ`, and binder
`ϑ ≤ 1/4` (not a theorem about `N`). -/
theorem auxTheta_choose_le_four_theta {M n : ℕ} {ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : (n : ℝ) ≤ (2 : ℝ) * (M : ℝ) * ϑ)
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    (M.choose (n - 1) : ℝ) / (M.choose n : ℝ) ≤ (4 : ℝ) * ϑ :=
  (auxTheta_choose_ratio_pos hn hnM).trans_le
    (auxTheta_ratio_le_four_theta_nat hn hnM hbound hϑ hθ4)

/-- Same with the commuted binder `n ≤ 2 ϑ M`. -/
theorem auxTheta_choose_le_four_theta_comm {M n : ℕ} {ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : (n : ℝ) ≤ (2 : ℝ) * ϑ * (M : ℝ))
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    (M.choose (n - 1) : ℝ) / (M.choose n : ℝ) ≤ (4 : ℝ) * ϑ :=
  (auxTheta_choose_ratio_pos hn hnM).trans_le
    (auxTheta_ratio_le_four_theta_nat_comm hn hnM hbound hϑ hθ4)

/-- Combined chain on `n ≤ M/2`, without `ϑ ≤ 1/4`. Remaining:
`0 < n`, `n ≤ M`, `n ≤ M/2`, and `n ≤ 2 M ϑ`. -/
theorem auxTheta_choose_le_four_theta_of_le_half {M n : ℕ} {ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hhalf : (n : ℝ) ≤ (M : ℝ) / 2)
    (hbound : (n : ℝ) ≤ (2 : ℝ) * (M : ℝ) * ϑ) :
    (M.choose (n - 1) : ℝ) / (M.choose n : ℝ) ≤ (4 : ℝ) * ϑ :=
  (auxTheta_choose_ratio_pos hn hnM).trans_le
    (auxTheta_ratio_le_four_theta_of_le_half (Nat.cast_nonneg n)
      (lt_of_lt_of_le (Nat.cast_pos.mpr hn) (Nat.cast_le.mpr hnM))
      hhalf hbound)

/-- Carrier form `M = |A|`. Remaining: `0 < n`, `n ≤ |A|`,
`(n : ℝ) ≤ 2 |A| ϑ`, `0 < ϑ`, and binder `ϑ ≤ 1/4`. -/
theorem auxTheta_choose_le_four_theta_card {A : Finset ℕ} {n : ℕ}
    {ϑ : ℝ} (hn : 0 < n) (hnM : n ≤ A.card)
    (hbound : (n : ℝ) ≤ (2 : ℝ) * (A.card : ℝ) * ϑ)
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    (A.card.choose (n - 1) : ℝ) / (A.card.choose n : ℝ) ≤
      (4 : ℝ) * ϑ :=
  auxTheta_choose_le_four_theta hn hnM hbound hϑ hθ4

end

end PrimeGapNormality.Prime
