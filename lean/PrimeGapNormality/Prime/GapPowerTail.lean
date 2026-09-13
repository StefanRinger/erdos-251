import PrimeGapNormality.Prime.FractionalTail
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite gap-power tails (no position-difference remainder)

Compare `∑ g_j^d B^{-j}` with a linear gap tail. This is **not**
`fractionalTail`, which uses `x_k^d - x_(k-1)^d`.

For `B = b^D` and `1 ≤ d ≤ D`, the comparison
`∑ g_j^d B^{-j} ≤ (∑ g_j b^{-j})^d` holds for nonnegative `g` with no
mean hypothesis on `g^d`. Real exponents `1/d` are formed in `ℝ`.

Source: `rounds/round103/03_grok_gap_polynomial_implementation_update.md` P1.B;
`rounds/round103/01_gpt_gap_polynomial_normality.md` §4.
Contract: API
Audit: GREEN

Lean `Ioc L H` is paper `{j | L < j ≤ H}`.
-/

namespace PrimeGapNormality.Prime

open Finset

/-- Finite gap-power tail `∑_{L<j≤H} g_j^d / B^j`.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` §4.
Contract: API
Audit: GREEN -/
noncomputable def gapPowerTailTrunc (g : ℕ → ℝ) (B d L H : ℕ) : ℝ :=
  ∑ j ∈ Ioc L H, g j ^ d / (B : ℝ) ^ j

private theorem rpow_inv_pow {B j d : ℕ} (hB : 2 ≤ B) (hd : 0 < d) :
    ((B : ℝ) ^ (-((j : ℝ) / d))) ^ d = ((B : ℝ) ^ j)⁻¹ := by
  have hBpos : (0 : ℝ) < B :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (Nat.cast_le.mpr hB)
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
  have hmul : -((j : ℝ) / d) * d = -j := by
    field_simp [hd0]
  have hrpow := Real.rpow_mul_natCast hBpos.le (-((j : ℝ) / d)) d
  rw [hmul] at hrpow
  have hneg : (B : ℝ) ^ (-(j : ℝ)) = ((B : ℝ) ^ j)⁻¹ := by
    rw [Real.rpow_neg hBpos.le, Real.rpow_natCast]
  rw [← hrpow, hneg]

/-- Direct comparison: `∑ g_j^d B^{-j} ≤ (∑ g_j B^{-j/d})^d`.
No hypothesis on means of `g^d`.

Source: `rounds/round103/03_grok_gap_polynomial_implementation_update.md` P1.B.
Contract: API
Audit: GREEN -/
theorem gapPowerTailTrunc_le_rpow_sum (g : ℕ → ℝ) {B d L H : ℕ}
    (hB : 2 ≤ B) (hd : 1 ≤ d) (hg : ∀ j, 0 ≤ g j) :
    gapPowerTailTrunc g B d L H
      ≤ (∑ j ∈ Ioc L H, g j * (B : ℝ) ^ (-((j : ℝ) / d))) ^ d := by
  have hdpos : 0 < d := by omega
  have hterm :
      ∀ j ∈ Ioc L H,
        g j ^ d / (B : ℝ) ^ j
          ≤ (g j * (B : ℝ) ^ (-((j : ℝ) / d))) ^ d := by
    intro j _hj
    have hident :
        (g j * (B : ℝ) ^ (-((j : ℝ) / d))) ^ d
          = g j ^ d * ((B : ℝ) ^ j)⁻¹ := by
      rw [mul_pow, rpow_inv_pow hB hdpos]
    have hdiv : g j ^ d / (B : ℝ) ^ j = g j ^ d * ((B : ℝ) ^ j)⁻¹ :=
      div_eq_mul_inv _ _
    rw [hident, hdiv]
  have hsum := sum_le_sum hterm
  have hann :
      ∀ j ∈ Ioc L H, 0 ≤ g j * (B : ℝ) ^ (-((j : ℝ) / d)) := fun j _ =>
    mul_nonneg (hg j) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact hsum.trans (sum_pow_le_pow_sum (Ioc L H) _ hd hann)

/-- For `B = b^D` and `1 ≤ d ≤ D`, `B^{-j/d} ≤ b^{-j}`.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` §4.
Contract: API
Audit: GREEN -/
theorem base_pow_rpow_le_inv {b D d j : ℕ} (hb : 2 ≤ b) (hd : 1 ≤ d)
    (hdD : d ≤ D) :
    ((b ^ D : ℕ) : ℝ) ^ (-((j : ℝ) / d)) ≤ ((b : ℝ) ^ j)⁻¹ := by
  have hbpos : (0 : ℝ) < b :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (Nat.cast_le.mpr hb)
  have hdpos : 0 < d := by omega
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hdpos)
  have hcast : ((b ^ D : ℕ) : ℝ) = (b : ℝ) ^ D := Nat.cast_pow _ _
  have hleft :
      ((b ^ D : ℕ) : ℝ) ^ (-((j : ℝ) / d)) = (b : ℝ) ^ (-((D : ℝ) * j / d)) := by
    rw [hcast, ← Real.rpow_natCast, ← Real.rpow_mul hbpos.le]
    congr 1
    field_simp [hd0]
  have hright : ((b : ℝ) ^ j)⁻¹ = (b : ℝ) ^ (-(j : ℝ)) := by
    rw [Real.rpow_neg hbpos.le, Real.rpow_natCast]
  rw [hleft, hright]
  have hle : -((D : ℝ) * j / d) ≤ -(j : ℝ) := by
    have hfrac : (j : ℝ) ≤ (D : ℝ) * j / d := by
      have hdj : (d : ℝ) ≤ D := Nat.cast_le.mpr hdD
      have hnn : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
      have hden : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
      have : (d : ℝ) * j ≤ (D : ℝ) * j := mul_le_mul_of_nonneg_right hdj hnn
      rwa [le_div_iff₀ hden, mul_comm]
    linarith
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr
    (le_trans (by decide : 1 ≤ 2) hb)) hle

/-- For `b^D ≤ B` and `1 ≤ d ≤ D`, `B^{-j/d} ≤ b^{-j}`.
Does not claim b-normality of a B-normal number.

Source: `rounds/round103/07_grok_minimal_budget_small_addendum.md` §2;
`rounds/round103/04_paper_architecture_minimal_input_v2.md` (4.1).
Contract: API
Audit: GREEN -/
theorem base_pow_rpow_le_inv_of_le {b B D d j : ℕ} (hb : 2 ≤ b)
    (hB : b ^ D ≤ B) (hd : 1 ≤ d) (hdD : d ≤ D) :
    (B : ℝ) ^ (-((j : ℝ) / d)) ≤ ((b : ℝ) ^ j)⁻¹ := by
  have hdpos : 0 < d := by omega
  have hDpos : 0 < D := lt_of_lt_of_le hdpos hdD
  have hbD : 2 ≤ b ^ D :=
    le_trans hb (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hDpos) b)
  have hbDpos : (0 : ℝ) < (b ^ D : ℕ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (Nat.cast_le.mpr hbD)
  have hBle : ((b ^ D : ℕ) : ℝ) ≤ B := Nat.cast_le.mpr hB
  have hexp : -((j : ℝ) / d) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hmono :
      (B : ℝ) ^ (-((j : ℝ) / d))
        ≤ ((b ^ D : ℕ) : ℝ) ^ (-((j : ℝ) / d)) :=
    Real.rpow_le_rpow_of_nonpos hbDpos hBle hexp
  exact hmono.trans (base_pow_rpow_le_inv (b := b) (D := D) (d := d) (j := j)
    hb hd hdD)

/-- Comparison for any target base `B ≥ b^D`. Analytic continuation gives
B-normality, not automatically b-normality.

Source: `rounds/round103/07_grok_minimal_budget_small_addendum.md` §2.
Contract: API
Audit: GREEN -/
theorem gapPowerTailTrunc_le_linear_pow_of_le (g : ℕ → ℝ) {b B D d L H : ℕ}
    (hb : 2 ≤ b) (hB : b ^ D ≤ B) (hd : 1 ≤ d) (hdD : d ≤ D)
    (hg : ∀ j, 0 ≤ g j) :
    gapPowerTailTrunc g B d L H
      ≤ (∑ j ∈ Ioc L H, g j / (b : ℝ) ^ j) ^ d := by
  have hdpos : 0 < d := by omega
  have hDpos : 0 < D := lt_of_lt_of_le hdpos hdD
  have hbD : 2 ≤ b ^ D :=
    le_trans hb (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hDpos) b)
  have hB2 : 2 ≤ B := le_trans hbD hB
  have hcore := gapPowerTailTrunc_le_rpow_sum (L := L) (H := H) g hB2 hd hg
  have hterm :
      ∀ j ∈ Ioc L H,
        g j * (B : ℝ) ^ (-((j : ℝ) / d)) ≤ g j / (b : ℝ) ^ j := by
    intro j _hj
    have hscale := base_pow_rpow_le_inv_of_le (b := b) (B := B) (D := D)
      (d := d) (j := j) hb hB hd hdD
    have hdiv : g j / (b : ℝ) ^ j = g j * ((b : ℝ) ^ j)⁻¹ := div_eq_mul_inv _ _
    rw [hdiv]
    exact mul_le_mul_of_nonneg_left hscale (hg j)
  have hsum := sum_le_sum hterm
  have hmono := pow_le_pow_left₀
    (sum_nonneg fun j _ =>
      mul_nonneg (hg j) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    hsum d
  exact hcore.trans hmono

/-- Matched-base comparison: `∑ g_j^d (b^D)^{-j} ≤ (∑ g_j b^{-j})^d`.

Source: `rounds/round103/03_grok_gap_polynomial_implementation_update.md` P1.B.
Contract: API
Audit: GREEN -/
theorem gapPowerTailTrunc_le_linear_pow (g : ℕ → ℝ) {b D d L H : ℕ}
    (hb : 2 ≤ b) (hd : 1 ≤ d) (hdD : d ≤ D) (hg : ∀ j, 0 ≤ g j) :
    gapPowerTailTrunc g (b ^ D) d L H
      ≤ (∑ j ∈ Ioc L H, g j / (b : ℝ) ^ j) ^ d :=
  gapPowerTailTrunc_le_linear_pow_of_le (L := L) (H := H) g hb le_rfl hd hdD hg

/-- Root form of the matched-base bound. Exponent `1/d` in `ℝ`.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` §4.
Contract: API
Audit: GREEN -/
theorem gapPowerTailTrunc_rpow_le_linear_of_le (g : ℕ → ℝ) {b B D d L H : ℕ}
    (hb : 2 ≤ b) (hB : b ^ D ≤ B) (hd : 1 ≤ d) (hdD : d ≤ D)
    (hg : ∀ j, 0 ≤ g j) :
    gapPowerTailTrunc g B d L H ^ ((1 : ℝ) / d)
      ≤ ∑ j ∈ Ioc L H, g j / (b : ℝ) ^ j := by
  have hle := gapPowerTailTrunc_le_linear_pow_of_le (L := L) (H := H) g hb hB hd hdD hg
  have hnn : 0 ≤ gapPowerTailTrunc g B d L H :=
    sum_nonneg fun j _ => div_nonneg (pow_nonneg (hg j) _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hrhs : 0 ≤ ∑ j ∈ Ioc L H, g j / (b : ℝ) ^ j :=
    sum_nonneg fun j _ => div_nonneg (hg j) (pow_nonneg (Nat.cast_nonneg _) _)
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hpow : 0 ≤ (∑ j ∈ Ioc L H, g j / (b : ℝ) ^ j) ^ d := pow_nonneg hrhs d
  have hz : 0 < (1 : ℝ) / d := div_pos zero_lt_one hdpos
  have hroot :
      gapPowerTailTrunc g B d L H ^ ((1 : ℝ) / d)
        ≤ ((∑ j ∈ Ioc L H, g j / (b : ℝ) ^ j) ^ d) ^ ((1 : ℝ) / d) :=
    (Real.rpow_le_rpow_iff hnn hpow hz).mpr hle
  have hrhs_pow :
      ((∑ j ∈ Ioc L H, g j / (b : ℝ) ^ j) ^ d) ^ ((1 : ℝ) / d) =
        ∑ j ∈ Ioc L H, g j / (b : ℝ) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrhs]
    have : (d : ℝ) * (1 / d) = 1 := mul_one_div_cancel hdpos.ne'
    rw [this, Real.rpow_one]
  rwa [hrhs_pow] at hroot

theorem gapPowerTailTrunc_rpow_le_linear (g : ℕ → ℝ) {b D d L H : ℕ}
    (hb : 2 ≤ b) (hd : 1 ≤ d) (hdD : d ≤ D) (hg : ∀ j, 0 ≤ g j) :
    gapPowerTailTrunc g (b ^ D) d L H ^ ((1 : ℝ) / d)
      ≤ ∑ j ∈ Ioc L H, g j / (b : ℝ) ^ j :=
  gapPowerTailTrunc_rpow_le_linear_of_le (L := L) (H := H) g hb le_rfl hd hdD hg

end PrimeGapNormality.Prime
