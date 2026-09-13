import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Good-count prefactor `n / (M - n + 1) ≤ 4 ϑ`

Paper v0.16: the exception `N > 2 M ϑ` is paid first under the
original measure for a test `0 ≤ f ≤ 1`. On good counts

    `n / (M - n + 1) ≤ 4 ϑ`,

then a nonnegative test extends to all auxiliary frames. `M = 0`
carries no mass.

This leaf is **only** that real algebra (paper chain
`n/(M-n+1) ≤ 2n/M ≤ 4ϑ` on `n ≤ M/2`). It does **not** compile the
counting identity, auxiliary-measure renormalisation, Selberg,
the hull `8^r`, the kernel, or (C4). The binder `ϑ ≤ 1/4` is the
finite substitute for the paper's eventual `N ≤ M/2` from `ϑ → 0`;
it is **not** a theorem about the actual count `N`.

Does **not** import MixZeta, SingletonLi, EndAPI,
UniformAuxFrame, AuxFrameDelete, or SubsetSpacingJoint.
Unique names `goodCount_`.

**Compiled.**
1. `0 < n` and `n ≤ M` force `0 < M` (`M = 0` has no mass).
2. `n ≤ M` ⇒ `0 < M - n + 1`.
3. `0 ≤ n / (M - n + 1)` (`0 ≤ n`, positive denominator).
4. `2 * M * ϑ = 2 * ϑ * M`.
5. Binder `ϑ ≤ 1/4` ⇒ `2 ϑ ≤ 1/2`; with `0 ≤ M` also
   `2 M ϑ ≤ M/2`, hence `n ≤ 2 M ϑ` ⇒ `n ≤ M/2`.
6. On `0 ≤ n`, `0 < M`, `n ≤ M/2`:
   `n / (M - n + 1) ≤ 2 n / M`.
7. On `0 < M` and `n ≤ 2 M ϑ`: `2 n / M ≤ 4 ϑ`.
8. Combined: `n / (M - n + 1) ≤ 4 ϑ` under
   `0 < n`, `n ≤ M`, `n ≤ 2 M ϑ` (or `n ≤ 2 ϑ M`),
   `0 < ϑ`, and `ϑ ≤ 1/4`. Same from `n ≤ M/2` without
   `ϑ ≤ 1/4`. Natural-number wrappers.

**Not compiled.** The counting law
`E[f(U) | A, N = n] = n/(M-n+1) · E_F Σ f`. Auxiliary-measure
renormalisation. Selberg. `8^r`. Kernel. (C4). MixZeta.
SingletonLi. A theorem `ϑ ≤ 1/4` for the actual `N`.

**Remaining hyps.** Binders in (8): `0 < n`, `n ≤ M`,
`n ≤ 2 M ϑ` (paper good count `N ≤ 2 M ϑ`, not discharged),
`0 < ϑ`, and `ϑ ≤ 1/4` (or else `n ≤ M/2`). Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `M = 0` has no mass (`0 < n`, `n ≤ M`) | theorem |
| `0 < M - n + 1` | theorem (`n ≤ M`) |
| `0 ≤ n/(M-n+1)` | theorem (`0 ≤ n`, positive denom) |
| `ϑ ≤ 1/4` ⇒ `2 M ϑ ≤ M/2` | theorem (`0 ≤ M`; binder `ϑ ≤ 1/4`) |
| `n/(M-n+1) ≤ 2n/M` | theorem (`0 ≤ n`, `0 < M`, `n ≤ M/2`) |
| `2n/M ≤ 4ϑ` | theorem (`0 < M`, `n ≤ 2 M ϑ`) |
| `n/(M-n+1) ≤ 4ϑ` | theorem (binders above) |
| actual counting law / aux-measure renormalisation | not claimed |
| Selberg / `8^r` / kernel / (C4) | not claimed |
| `ϑ ≤ 1/4` for the actual `N` | remaining hyp |

Does not claim the kernel is closed.

Source: `rounds/round119/19_grok_v016_positive_frames_delta.md`;
`rounds/round119/17_paper_v0_16.tex`.
Contract: API
-/

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### `M = 0` carries no mass -/

/-- A positive count cannot sit in a zero-cardinality ground set. -/
theorem goodCount_M_pos {n M : ℝ} (hn : 0 < n) (hnM : n ≤ M) :
    0 < M :=
  lt_of_lt_of_le hn hnM

/-- Same statement: `M = 0` excludes `0 < n ≤ M`. -/
theorem goodCount_not_le_of_M_eq_zero {n M : ℝ}
    (hM : M = 0) (hn : 0 < n) : ¬ n ≤ M :=
  fun hnM => (hnM.trans_eq hM).not_gt hn

theorem goodCount_M_pos_nat {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M) :
    0 < M :=
  lt_of_lt_of_le hn hnM

/-! ### Positive denominator and nonnegative ratio -/

/-- `n ≤ M` ⇒ `0 < M - n + 1`. -/
theorem goodCount_denom_pos {n M : ℝ} (hnM : n ≤ M) :
    0 < M - n + 1 := by
  have hsub : (0 : ℝ) ≤ M - n := sub_nonneg.mpr hnM
  have hone : (1 : ℝ) ≤ M - n + 1 := le_add_of_nonneg_left hsub
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hone

/-- Cast of the natural denominator, remaining `n ≤ M`. -/
theorem goodCount_denom_cast {n M : ℕ} (hnM : n ≤ M) :
    ((M - n + 1 : ℕ) : ℝ) = (M : ℝ) - n + 1 := by
  rw [Nat.cast_add, Nat.cast_sub hnM, Nat.cast_one]

theorem goodCount_denom_pos_nat {n M : ℕ} (hnM : n ≤ M) :
    (0 : ℝ) < (M : ℝ) - n + 1 :=
  goodCount_denom_pos (Nat.cast_le.mpr hnM)

/-- Remaining: `0 ≤ n` and a positive denominator. -/
theorem goodCount_ratio_nonneg {n M : ℝ}
    (hn : 0 ≤ n) (hden : 0 < M - n + 1) :
    0 ≤ n / (M - n + 1) :=
  div_nonneg hn hden.le

theorem goodCount_ratio_nonneg_of_le {n M : ℝ}
    (hn : 0 ≤ n) (hnM : n ≤ M) :
    0 ≤ n / (M - n + 1) :=
  goodCount_ratio_nonneg hn (goodCount_denom_pos hnM)

theorem goodCount_ratio_nonneg_nat {n M : ℕ} (hnM : n ≤ M) :
    (0 : ℝ) ≤ (n : ℝ) / ((M : ℝ) - n + 1) :=
  goodCount_ratio_nonneg_of_le (Nat.cast_nonneg n)
    (Nat.cast_le.mpr hnM)

/-! ### Commute `2 M ϑ` / `2 ϑ M` -/

theorem goodCount_two_mul_comm (M ϑ : ℝ) :
    (2 : ℝ) * M * ϑ = (2 : ℝ) * ϑ * M := by
  rw [mul_assoc, mul_assoc, mul_comm M ϑ]

theorem goodCount_four_mul_comm (M ϑ : ℝ) :
    (4 : ℝ) * M * ϑ = (4 : ℝ) * ϑ * M := by
  rw [mul_assoc, mul_assoc, mul_comm M ϑ]

/-! ### Binder `ϑ ≤ 1/4` (not a theorem about `N`) -/

/-- Finite half-count room from `ϑ ≤ 1/4`. Not a claim about `N`. -/
theorem goodCount_two_theta_le_half {ϑ : ℝ}
    (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    (2 : ℝ) * ϑ ≤ (1 : ℝ) / 2 := by
  have h :
      (2 : ℝ) * ϑ ≤ (2 : ℝ) * ((1 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left hθ4 (by norm_num : (0 : ℝ) ≤ 2)
  have h24 : (2 : ℝ) * ((1 : ℝ) / 4) = (1 : ℝ) / 2 := by
    norm_num
  exact h.trans_eq h24

theorem goodCount_two_M_theta_le_half {M ϑ : ℝ}
    (hM : 0 ≤ M) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    (2 : ℝ) * M * ϑ ≤ M / 2 := by
  have h2θ := goodCount_two_theta_le_half hθ4
  calc
    (2 : ℝ) * M * ϑ
        = M * ((2 : ℝ) * ϑ) := by
          rw [mul_comm (2 : ℝ) M, mul_assoc]
    _ ≤ M * ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left h2θ hM
    _ = M / 2 :=
          mul_one_div M 2

/-- Remaining: `0 ≤ M`, binder `ϑ ≤ 1/4`, and `n ≤ 2 M ϑ`. -/
theorem goodCount_le_half {n M ϑ : ℝ}
    (hM : 0 ≤ M) (hθ4 : ϑ ≤ (1 : ℝ) / 4)
    (hbound : n ≤ (2 : ℝ) * M * ϑ) :
    n ≤ M / 2 :=
  hbound.trans (goodCount_two_M_theta_le_half hM hθ4)

/-- Same with the commuted binder `n ≤ 2 ϑ M`. -/
theorem goodCount_le_half_comm {n M ϑ : ℝ}
    (hM : 0 ≤ M) (hθ4 : ϑ ≤ (1 : ℝ) / 4)
    (hbound : n ≤ (2 : ℝ) * ϑ * M) :
    n ≤ M / 2 :=
  goodCount_le_half hM hθ4
    (hbound.trans_eq (goodCount_two_mul_comm M ϑ).symm)

/-! ### Paper half: `n / (M - n + 1) ≤ 2 n / M` -/

theorem goodCount_sub_half (M : ℝ) : M - M / 2 = M / 2 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  calc
    M - M / 2
        = (2 : ℝ) * (M / 2) - M / 2 := by
          rw [mul_div_cancel₀ M h2]
    _ = (M / 2 + M / 2) - M / 2 := by
          rw [two_mul]
    _ = M / 2 :=
          add_sub_cancel_right _ _

theorem goodCount_half_le_self {M : ℝ} (hM : 0 ≤ M) : M / 2 ≤ M :=
  (goodCount_sub_half M).symm.le.trans
    (sub_le_self M (div_nonneg hM (by norm_num : (0 : ℝ) ≤ 2)))

theorem goodCount_half_le_sub {n M : ℝ} (hhalf : n ≤ M / 2) :
    M / 2 ≤ M - n := by
  have h : M - M / 2 ≤ M - n := sub_le_sub_left hhalf M
  exact (goodCount_sub_half M).symm.le.trans h

theorem goodCount_half_le_denom {n M : ℝ} (hhalf : n ≤ M / 2) :
    M / 2 ≤ M - n + 1 :=
  (goodCount_half_le_sub hhalf).trans
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))

theorem goodCount_denom_pos_of_le_half {n M : ℝ}
    (hM : 0 < M) (hhalf : n ≤ M / 2) :
    0 < M - n + 1 :=
  lt_of_lt_of_le (div_pos hM (by norm_num : (0 : ℝ) < 2))
    (goodCount_half_le_denom hhalf)

/-- Remaining: `0 ≤ n`, `0 < M`, and `n ≤ M/2`. -/
theorem goodCount_ratio_le_two_div {n M : ℝ}
    (hn : 0 ≤ n) (hM : 0 < M) (hhalf : n ≤ M / 2) :
    n / (M - n + 1) ≤ (2 : ℝ) * n / M := by
  have hhalfpos : (0 : ℝ) < M / 2 :=
    div_pos hM (by norm_num : (0 : ℝ) < 2)
  have hdenle : M / 2 ≤ M - n + 1 := goodCount_half_le_denom hhalf
  have hquot : n / (M - n + 1) ≤ n / (M / 2) :=
    div_le_div_of_nonneg_left hn hhalfpos hdenle
  have hrewrite : n / (M / 2) = (2 : ℝ) * n / M := by
    calc
      n / (M / 2)
          = n * (M / 2)⁻¹ :=
            div_eq_mul_inv _ _
      _ = n * (2 / M) := by
            rw [inv_div]
      _ = n * 2 / M := by
            rw [← mul_div_assoc]
      _ = (2 : ℝ) * n / M := by
            rw [mul_comm n 2]
  exact hquot.trans_eq hrewrite

/-! ### Count bound `n ≤ 2 M ϑ` ⇒ `2 n / M ≤ 4 ϑ` -/

/-- Remaining: `0 < M` and `n ≤ 2 M ϑ`. -/
theorem goodCount_two_div_le_four_theta {n M ϑ : ℝ}
    (hM : 0 < M) (hbound : n ≤ (2 : ℝ) * M * ϑ) :
    (2 : ℝ) * n / M ≤ (4 : ℝ) * ϑ := by
  have h2n :
      (2 : ℝ) * n ≤ (2 : ℝ) * ((2 : ℝ) * M * ϑ) :=
    mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)
  have h4 :
      (2 : ℝ) * ((2 : ℝ) * M * ϑ) = (4 : ℝ) * M * ϑ := by
    ring
  have h2n' : (2 : ℝ) * n ≤ (4 : ℝ) * M * ϑ := h2n.trans_eq h4
  have hdiv :
      (2 : ℝ) * n / M ≤ ((4 : ℝ) * M * ϑ) / M :=
    div_le_div_of_nonneg_right h2n' hM.le
  have hrhs : ((4 : ℝ) * M * ϑ) / M = (4 : ℝ) * ϑ := by
    have hM0 : M ≠ 0 := hM.ne'
    calc
      ((4 : ℝ) * M * ϑ) / M
          = ((4 : ℝ) * ϑ * M) / M := by
            rw [goodCount_four_mul_comm]
      _ = (4 : ℝ) * ϑ * (M / M) := by
            rw [mul_div_assoc]
      _ = (4 : ℝ) * ϑ * 1 := by
            rw [div_self hM0]
      _ = (4 : ℝ) * ϑ :=
            mul_one _
  exact hdiv.trans_eq hrhs

theorem goodCount_two_div_le_four_theta_comm {n M ϑ : ℝ}
    (hM : 0 < M) (hbound : n ≤ (2 : ℝ) * ϑ * M) :
    (2 : ℝ) * n / M ≤ (4 : ℝ) * ϑ :=
  goodCount_two_div_le_four_theta hM
    (hbound.trans_eq (goodCount_two_mul_comm M ϑ).symm)

/-- Positive density factor. Remaining: `0 < ϑ`. -/
theorem goodCount_four_theta_pos {ϑ : ℝ} (hϑ : 0 < ϑ) :
    0 < (4 : ℝ) * ϑ :=
  mul_pos (by norm_num : (0 : ℝ) < 4) hϑ

/-- From a positive count inside `n ≤ 2 M ϑ`. Remaining:
`0 < n`, `0 < M`, and `n ≤ 2 M ϑ`. -/
theorem goodCount_theta_pos {n M ϑ : ℝ}
    (hn : 0 < n) (hM : 0 < M)
    (hbound : n ≤ (2 : ℝ) * M * ϑ) :
    0 < ϑ :=
  pos_of_mul_pos_right (lt_of_lt_of_le hn hbound)
    (mul_pos (by norm_num : (0 : ℝ) < 2) hM).le

/-! ### Combined `n / (M - n + 1) ≤ 4 ϑ` -/

/-- Paper chain on `n ≤ M/2`, without the binder `ϑ ≤ 1/4`.
Remaining: `0 ≤ n`, `0 < M`, `n ≤ M/2`, and `n ≤ 2 M ϑ`. -/
theorem goodCount_ratio_le_four_theta_of_le_half {n M ϑ : ℝ}
    (hn : 0 ≤ n) (hM : 0 < M) (hhalf : n ≤ M / 2)
    (hbound : n ≤ (2 : ℝ) * M * ϑ) :
    n / (M - n + 1) ≤ (4 : ℝ) * ϑ :=
  (goodCount_ratio_le_two_div hn hM hhalf).trans
    (goodCount_two_div_le_four_theta hM hbound)

/-- Main algebra. Remaining: `0 < n`, `n ≤ M`, `n ≤ 2 M ϑ`,
`0 < ϑ`, and the binder `ϑ ≤ 1/4` (not a theorem about `N`).
Does **not** claim the counting law. -/
theorem goodCount_ratio_le_four_theta {n M ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : n ≤ (2 : ℝ) * M * ϑ)
    (_hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    n / (M - n + 1) ≤ (4 : ℝ) * ϑ :=
  goodCount_ratio_le_four_theta_of_le_half hn.le (goodCount_M_pos hn hnM)
    (goodCount_le_half (goodCount_M_pos hn hnM).le hθ4 hbound) hbound

/-- Same with the commuted binder `n ≤ 2 ϑ M`. -/
theorem goodCount_ratio_le_four_theta_comm {n M ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : n ≤ (2 : ℝ) * ϑ * M)
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    n / (M - n + 1) ≤ (4 : ℝ) * ϑ :=
  goodCount_ratio_le_four_theta hn hnM
    (hbound.trans_eq (goodCount_two_mul_comm M ϑ).symm) hϑ hθ4

/-! ### Natural counts -/

/-- Remaining: `0 < n`, `n ≤ M`, `(n : ℝ) ≤ 2 M ϑ`, `0 < ϑ`,
and binder `ϑ ≤ 1/4`. -/
theorem goodCount_ratio_le_four_theta_nat {n M : ℕ} {ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : (n : ℝ) ≤ (2 : ℝ) * (M : ℝ) * ϑ)
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    (n : ℝ) / ((M : ℝ) - n + 1) ≤ (4 : ℝ) * ϑ :=
  goodCount_ratio_le_four_theta (Nat.cast_pos.mpr hn)
    (Nat.cast_le.mpr hnM) hbound hϑ hθ4

theorem goodCount_ratio_le_four_theta_nat_comm {n M : ℕ} {ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : (n : ℝ) ≤ (2 : ℝ) * ϑ * (M : ℝ))
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    (n : ℝ) / ((M : ℝ) - n + 1) ≤ (4 : ℝ) * ϑ :=
  goodCount_ratio_le_four_theta_comm (Nat.cast_pos.mpr hn)
    (Nat.cast_le.mpr hnM) hbound hϑ hθ4

/-- Same inequality with the natural denominator `M - n + 1`. -/
theorem goodCount_ratio_le_four_theta_nat_denom {n M : ℕ} {ϑ : ℝ}
    (hn : 0 < n) (hnM : n ≤ M)
    (hbound : (n : ℝ) ≤ (2 : ℝ) * (M : ℝ) * ϑ)
    (hϑ : 0 < ϑ) (hθ4 : ϑ ≤ (1 : ℝ) / 4) :
    (n : ℝ) / (↑(M - n + 1) : ℝ) ≤ (4 : ℝ) * ϑ := by
  rw [goodCount_denom_cast hnM]
  exact goodCount_ratio_le_four_theta_nat hn hnM hbound hϑ hθ4

end

end PrimeGapNormality.Prime
