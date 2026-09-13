import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite fractional tail remainder (no primes)

Finite weighted kernel from R99/05. For a nonnegative nondecreasing
sequence `x` with `x 0 = 0`,

  `R = ∑_{L<k≤J} (x k ^ d - x (k-1) ^ d) * b ^ (-k)`.

The comparison `(∑ y_k ^ d) ^ (1/d) ≤ ∑ y_k` on nonnegative terms
gives `R ^ (1/d) ≤ ∑_{L<k≤J} b ^ (-k/d) * x k`, and finite swapping
gives the weighted mean. Direct bounded Lipschitz test (4.1). No Kac,
Weyl, or prime-block applications. No higher-moment hypothesis `E[x^d]`.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md`;
`rounds/round99/03_gpt_tail_reuse_and_cross_base_independence.md` §§1–2;
`rounds/round101/02_grok_multibase_common_clock_update.md` §5.
Contract: API
Audit: GREEN

Lean `Ioc L J` is paper `{k | L < k ≤ J}` (0-based; equal to
`Icc (L+1) J`). The exponents `1/d` and `-k/d` are formed in `ℝ`,
never as `ℕ`/`ℤ` division.
-/

namespace PrimeGapNormality.Prime

open Finset

/-! ### Kernel comparison `∑ a_i ^ d ≤ (∑ a_i) ^ d` -/

/-- For `d ≥ 1` and nonnegative `a_i`, `∑ a_i ^ d ≤ (∑ a_i) ^ d`.
Equivalent after taking `d`-th roots to `(∑ a_i ^ d) ^ (1/d) ≤ ∑ a_i`.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md` §3;
`rounds/round99/03_gpt_tail_reuse_and_cross_base_independence.md` §1.
Contract: API
Audit: GREEN -/
theorem sum_pow_le_pow_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) {d : ℕ}
    (hd : 1 ≤ d) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, a i ^ d ≤ (∑ i ∈ s, a i) ^ d := by
  have hterm : ∀ i ∈ s, a i ^ d ≤ a i * (∑ j ∈ s, a j) ^ (d - 1) := by
    intro i hi
    have hai : 0 ≤ a i := ha i hi
    have hle : a i ≤ ∑ j ∈ s, a j := single_le_sum (fun j hj => ha j hj) hi
    have hpow : a i ^ (d - 1) ≤ (∑ j ∈ s, a j) ^ (d - 1) :=
      pow_le_pow_left₀ hai hle (d - 1)
    have hrewrite : a i ^ d = a i * a i ^ (d - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hd]
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_left hpow hai
  calc
    ∑ i ∈ s, a i ^ d
        ≤ ∑ i ∈ s, a i * (∑ j ∈ s, a j) ^ (d - 1) :=
      sum_le_sum hterm
    _ = (∑ i ∈ s, a i) * (∑ j ∈ s, a j) ^ (d - 1) :=
      (sum_mul _ _ _).symm
    _ = (∑ i ∈ s, a i) ^ (1 : ℕ) * (∑ i ∈ s, a i) ^ (d - 1) := by
      rw [pow_one]
    _ = (∑ i ∈ s, a i) ^ (1 + (d - 1)) :=
      (pow_add _ _ _).symm
    _ = (∑ i ∈ s, a i) ^ d := by
      rw [Nat.add_sub_of_le hd]

/-! ### Finite remainder `R` -/

/-- Finite fractional tail
`R = ∑_{k ∈ Ioc L J} (x k ^ d - x (k-1) ^ d) * ((b : ℝ) ^ k)⁻¹`.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md` §3.
Contract: API
Audit: GREEN -/
noncomputable def fractionalTail (x : ℕ → ℝ) (b d L J : ℕ) : ℝ :=
  ∑ k ∈ Ioc L J, (x k ^ d - x (k - 1) ^ d) * ((b : ℝ) ^ k)⁻¹

private theorem one_div_nat_nonneg (d : ℕ) : 0 ≤ (1 : ℝ) / (d : ℝ) :=
  div_nonneg zero_le_one (Nat.cast_nonneg _)

private theorem one_div_nat_le_one {d : ℕ} (hd : 1 ≤ d) :
    (1 : ℝ) / (d : ℝ) ≤ 1 := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have h1d : (1 : ℝ) ≤ (d : ℝ) := by
    simpa [Nat.cast_one] using (Nat.cast_le (α := ℝ)).mpr hd
  exact (div_le_one hdpos).mpr h1d

private theorem d_ne_zero {d : ℕ} (hd : 1 ≤ d) : d ≠ 0 := by
  omega

private theorem base_pos {b : ℕ} (hb : 2 ≤ b) : (0 : ℝ) < b :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (Nat.cast_le.mpr hb)

private theorem base_inv_nonneg {b k : ℕ} (hb : 2 ≤ b) : 0 ≤ ((b : ℝ) ^ k)⁻¹ :=
  (inv_pos.mpr (pow_pos (base_pos hb) k)).le

private theorem mono_of_succ {x : ℕ → ℝ} (h : ∀ k, x k ≤ x (k + 1)) : Monotone x :=
  monotone_nat_of_le_succ h

private theorem nonneg_of_zero_mono {x : ℕ → ℝ} (hx0 : x 0 = 0)
    (hmono : ∀ k, x k ≤ x (k + 1)) (n : ℕ) : 0 ≤ x n := by
  have hle : x 0 ≤ x n := (mono_of_succ hmono) (Nat.zero_le n)
  rwa [hx0] at hle

/-- Algebraic identity: `(x * b ^ (-k/d)) ^ d = x ^ d * b ^ (-k)`.
The quotients `-k/d` are formed in `ℝ`.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md` §3.
Contract: API
Audit: GREEN -/
private theorem mul_base_rpow_pow (b k d : ℕ) (x : ℝ) (hd : 0 < d) :
    ((b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x) ^ d
      = x ^ d * ((b : ℝ) ^ k)⁻¹ := by
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
  have hfactor :
      ((b : ℝ) ^ (-((k : ℝ) / (d : ℝ)))) ^ d = ((b : ℝ) ^ k)⁻¹ := by
    have h1 :
        ((b : ℝ) ^ (-((k : ℝ) / (d : ℝ)))) ^ d
          = (b : ℝ) ^ (-((k : ℝ) / (d : ℝ)) * (d : ℝ)) :=
      (Real.rpow_mul_natCast hb0 _ d).symm
    have h2 : -((k : ℝ) / (d : ℝ)) * (d : ℝ) = -(k : ℝ) := by
      rw [neg_mul, div_mul_cancel₀ _ hd0]
    have h3 : (b : ℝ) ^ (-(k : ℝ)) = ((b : ℝ) ^ (k : ℝ))⁻¹ :=
      Real.rpow_neg hb0 (k : ℝ)
    have h4 : (b : ℝ) ^ (k : ℝ) = (b : ℝ) ^ k :=
      Real.rpow_natCast _ _
    rw [h1, h2, h3, h4]
  rw [mul_pow, mul_comm (((b : ℝ) ^ (-((k : ℝ) / (d : ℝ)))) ^ d), hfactor]

/-- Nonnegativity of the finite remainder. Each increment of `x ^ d` is
nonnegative by monotonicity, and `b ^ (-k) ≥ 0`.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md` §3.
Contract: API
Audit: GREEN -/
theorem fractionalTail_nonneg (x : ℕ → ℝ) {b d L J : ℕ}
    (hb : 2 ≤ b) (_hd : 1 ≤ d) (_hLJ : L < J) (hx0 : x 0 = 0)
    (hmono : ∀ k, x k ≤ x (k + 1)) :
    0 ≤ fractionalTail x b d L J := by
  refine sum_nonneg fun k hk => ?_
  have hxk0 : 0 ≤ x (k - 1) := nonneg_of_zero_mono hx0 hmono (k - 1)
  have hle : x (k - 1) ≤ x k := (mono_of_succ hmono) (Nat.sub_le k 1)
  have hinc : 0 ≤ x k ^ d - x (k - 1) ^ d :=
    sub_nonneg.mpr (pow_le_pow_left₀ hxk0 hle d)
  exact mul_nonneg hinc (base_inv_nonneg hb)

/-- Intermediate power form: `R ≤ (∑_{L<k≤J} b ^ (-k/d) * x k) ^ d`.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md` §3.
Contract: API
Audit: GREEN -/
theorem fractionalTail_le_pow_sum (x : ℕ → ℝ) {b d L J : ℕ}
    (hb : 2 ≤ b) (hd : 1 ≤ d) (_hLJ : L < J) (hx0 : x 0 = 0)
    (hmono : ∀ k, x k ≤ x (k + 1)) :
    fractionalTail x b d L J
      ≤ (∑ k ∈ Ioc L J, (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x k) ^ d := by
  have hdpos : 0 < d := by omega
  have hxnn : ∀ n, 0 ≤ x n := nonneg_of_zero_mono hx0 hmono
  have hterm :
      ∀ k ∈ Ioc L J,
        (x k ^ d - x (k - 1) ^ d) * ((b : ℝ) ^ k)⁻¹
          ≤ ((b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x k) ^ d := by
    intro k _hk
    have hinc : x k ^ d - x (k - 1) ^ d ≤ x k ^ d :=
      sub_le_self _ (pow_nonneg (hxnn (k - 1)) d)
    have hmul :
        (x k ^ d - x (k - 1) ^ d) * ((b : ℝ) ^ k)⁻¹
          ≤ x k ^ d * ((b : ℝ) ^ k)⁻¹ :=
      mul_le_mul_of_nonneg_right hinc (base_inv_nonneg hb)
    have hident :
        ((b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x k) ^ d
          = x k ^ d * ((b : ℝ) ^ k)⁻¹ :=
      mul_base_rpow_pow b k d (x k) hdpos
    rwa [hident]
  have hsum :
      fractionalTail x b d L J
        ≤ ∑ k ∈ Ioc L J, ((b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x k) ^ d := by
    simpa [fractionalTail] using sum_le_sum hterm
  have hann :
      ∀ k ∈ Ioc L J, 0 ≤ (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x k :=
    fun k _hk =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg b) _) (hxnn k)
  exact hsum.trans (sum_pow_le_pow_sum (Ioc L J) _ hd hann)

/-- Root form: `R ^ (1/d) ≤ ∑_{L<k≤J} b ^ (-k/d) * x k`.
No hypothesis on higher moments of `x`.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md` §3.
Contract: API
Audit: GREEN -/
theorem fractionalTail_rpow_le (x : ℕ → ℝ) {b d L J : ℕ}
    (hb : 2 ≤ b) (hd : 1 ≤ d) (hLJ : L < J) (hx0 : x 0 = 0)
    (hmono : ∀ k, x k ≤ x (k + 1)) :
    fractionalTail x b d L J ^ ((1 : ℝ) / (d : ℝ))
      ≤ ∑ k ∈ Ioc L J, (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x k := by
  set S := ∑ k ∈ Ioc L J, (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x k
  have hR : 0 ≤ fractionalTail x b d L J :=
    fractionalTail_nonneg x hb hd hLJ hx0 hmono
  have hS0 : 0 ≤ S :=
    sum_nonneg fun k _hk =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg b) _)
        (nonneg_of_zero_mono hx0 hmono k)
  have hpow := fractionalTail_le_pow_sum x hb hd hLJ hx0 hmono
  have hroot :
      fractionalTail x b d L J ^ ((1 : ℝ) / (d : ℝ))
        ≤ (S ^ d) ^ ((1 : ℝ) / (d : ℝ)) :=
    Real.rpow_le_rpow hR hpow (one_div_nat_nonneg d)
  have hdiv : (1 : ℝ) / (d : ℝ) = (d : ℝ)⁻¹ := one_div _
  have heq : (S ^ d) ^ ((1 : ℝ) / (d : ℝ)) = S := by
    rw [hdiv, Real.pow_rpow_inv_natCast hS0 (d_ne_zero hd)]
  rwa [heq] at hroot

/-- Weighted finite mean: `∑_i w_i R_i ^ (1/d)` is at most the same
combination of first-order means `∑_i w_i x_{i,k}`. Weights are a
finite probability (`w_i ≥ 0`, `∑ w = 1`). No `E[x^d]` hypothesis.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md` §3.
Contract: API
Audit: GREEN -/
theorem weighted_fractionalTail_rpow_le {ι : Type*} (I : Finset ι)
    (w : ι → ℝ) (x : ι → ℕ → ℝ) {b d L J : ℕ}
    (hb : 2 ≤ b) (hd : 1 ≤ d) (hLJ : L < J)
    (hw0 : ∀ i ∈ I, 0 ≤ w i) (_hw1 : ∑ i ∈ I, w i = 1)
    (hx0 : ∀ i ∈ I, x i 0 = 0)
    (hmono : ∀ i ∈ I, ∀ k, x i k ≤ x i (k + 1)) :
    ∑ i ∈ I, w i * fractionalTail (x i) b d L J ^ ((1 : ℝ) / (d : ℝ))
      ≤ ∑ k ∈ Ioc L J,
          (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * ∑ i ∈ I, w i * x i k := by
  have hpt :
      ∀ i ∈ I,
        w i * fractionalTail (x i) b d L J ^ ((1 : ℝ) / (d : ℝ))
          ≤ w i * ∑ k ∈ Ioc L J, (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x i k :=
    fun i hi =>
      mul_le_mul_of_nonneg_left
        (fractionalTail_rpow_le (x i) hb hd hLJ (hx0 i hi) (hmono i hi))
        (hw0 i hi)
  have hswap :
      ∑ i ∈ I, w i * ∑ k ∈ Ioc L J, (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x i k
        = ∑ k ∈ Ioc L J,
            (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * ∑ i ∈ I, w i * x i k := by
    calc
      ∑ i ∈ I, w i * ∑ k ∈ Ioc L J, (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x i k
          = ∑ i ∈ I, ∑ k ∈ Ioc L J,
              w i * ((b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x i k) := by
            refine sum_congr rfl fun i _hi => ?_
            rw [mul_sum]
      _ = ∑ k ∈ Ioc L J, ∑ i ∈ I,
            w i * ((b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * x i k) :=
          sum_comm
      _ = ∑ k ∈ Ioc L J, ∑ i ∈ I,
            (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * (w i * x i k) := by
            refine sum_congr rfl fun k _hk => sum_congr rfl fun i _hi => ?_
            ring
      _ = ∑ k ∈ Ioc L J,
            (b : ℝ) ^ (-((k : ℝ) / (d : ℝ))) * ∑ i ∈ I, w i * x i k := by
            refine sum_congr rfl fun k _hk => ?_
            rw [← mul_sum]
  exact (sum_le_sum hpt).trans (le_of_eq hswap)

/-! ### Direct bounded Lipschitz test (4.1) -/

/-- Direct bounded test (4.1), generic seminormed codomain.
If `|R| ≤ 1` use Lipschitz and `|R| ≤ |R| ^ (1/d)`; if `|R| ≥ 1` use
boundedness and `1 ≤ |R| ^ (1/d)`. Coarser than the optional Hölder
form, and avoids a `0^0` convention.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md` §4 (4.1).
Contract: API
Audit: GREEN -/
theorem direct_bounded_test {E : Type*} [SeminormedAddCommGroup E]
    {f : ℝ → E} {M A : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hbound : ∀ t, ‖f t‖ ≤ M)
    (hlip : ∀ s t, ‖f s - f t‖ ≤ A * |s - t|)
    (t R : ℝ) :
    ‖f (t + R) - f t‖ ≤ max (2 * M) A * |R| ^ ((1 : ℝ) / (d : ℝ)) := by
  have hpow0 : 0 ≤ |R| ^ ((1 : ℝ) / (d : ℝ)) :=
    Real.rpow_nonneg (abs_nonneg _) _
  have h2M : 0 ≤ 2 * M := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM
  rcases le_total |R| 1 with hle | hge
  · have hlip' : ‖f (t + R) - f t‖ ≤ A * |R| := by
      have hdist : |(t + R) - t| = |R| := by
        have : (t + R) - t = R := by ring
        rw [this]
      simpa [hdist] using hlip (t + R) t
    have hRle :
        |R| ≤ |R| ^ ((1 : ℝ) / (d : ℝ)) := by
      have hexp :=
        Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg R) hle
          (one_div_nat_nonneg d) (one_div_nat_le_one hd)
      simpa [Real.rpow_one] using hexp
    have hA : A * |R| ≤ A * |R| ^ ((1 : ℝ) / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hRle hA
    have hmax :
        A * |R| ^ ((1 : ℝ) / (d : ℝ))
          ≤ max (2 * M) A * |R| ^ ((1 : ℝ) / (d : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hpow0
    exact hlip'.trans (hA.trans hmax)
  · have htri : ‖f (t + R) - f t‖ ≤ 2 * M := by
      calc
        ‖f (t + R) - f t‖ ≤ ‖f (t + R)‖ + ‖f t‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hbound (t + R)) (hbound t)
        _ = 2 * M := by ring
    have hone : (1 : ℝ) ≤ |R| ^ ((1 : ℝ) / (d : ℝ)) :=
      Real.one_le_rpow hge (one_div_nat_nonneg d)
    have hscale : 2 * M ≤ (2 * M) * |R| ^ ((1 : ℝ) / (d : ℝ)) :=
      le_mul_of_one_le_right h2M hone
    have hmax :
        (2 * M) * |R| ^ ((1 : ℝ) / (d : ℝ))
          ≤ max (2 * M) A * |R| ^ ((1 : ℝ) / (d : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0
    exact htri.trans (hscale.trans hmax)

/-- Real specialisation of (4.1): `|f(t+R) - f(t)|`.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md` §4 (4.1).
Contract: API
Audit: GREEN -/
theorem direct_bounded_test_real {f : ℝ → ℝ} {M A : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hbound : ∀ u, |f u| ≤ M)
    (hlip : ∀ s u, |f s - f u| ≤ A * |s - u|)
    (t R : ℝ) :
    |f (t + R) - f t| ≤ max (2 * M) A * |R| ^ ((1 : ℝ) / (d : ℝ)) := by
  have hbound' : ∀ u, ‖f u‖ ≤ M := by
    intro u
    rw [Real.norm_eq_abs]
    exact hbound u
  have hlip' : ∀ s u, ‖f s - f u‖ ≤ A * |s - u| := by
    intro s u
    rw [Real.norm_eq_abs]
    exact hlip s u
  have h := direct_bounded_test (E := ℝ) hd hM hA hbound' hlip' t R
  rwa [Real.norm_eq_abs] at h

/-- Complex specialisation of (4.1): left side is the complex norm.

Source: `rounds/round99/05_grok_fractional_tail_addendum.md` §4 (4.1).
Contract: API
Audit: GREEN -/
theorem direct_bounded_test_complex {f : ℝ → ℂ} {M A : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hbound : ∀ u, ‖f u‖ ≤ M)
    (hlip : ∀ s u, ‖f s - f u‖ ≤ A * |s - u|)
    (t R : ℝ) :
    ‖f (t + R) - f t‖ ≤ max (2 * M) A * |R| ^ ((1 : ℝ) / (d : ℝ)) :=
  direct_bounded_test hd hM hA hbound hlip t R

end PrimeGapNormality.Prime
