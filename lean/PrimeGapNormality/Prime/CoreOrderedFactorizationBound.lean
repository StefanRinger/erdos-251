import PrimeGapNormality.Prime.FiniteSelbergIntervalCap
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Ordered factorization summatory bound

The rough-pattern CRT remainder uses the elementary estimate

`sum_{d <= R} d_k(d) <= R * (1 + log R)^(k-1)`.

Here `d_k` is defined by the actual finite divisor convolution: it counts
ordered factorizations into `k` positive factors.  The proof is the finite
Dirichlet-hyperbola reindexing followed by the harmonic bound.  No sieve
weight or beta-sieve estimate appears.
-/

namespace PrimeGapNormality.Prime.CoreOrderedFactorizationBound

open Finset
open scoped BigOperators

noncomputable section

/-- Ordered `k`-factor divisor count.  The cases `k = 0` and `n = 0` are
irrelevant to the rough application and are fixed at zero. -/
def orderedFactorizationCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, n => if n = 0 then 0 else 1
  | k + 2, n =>
      ∑ a ∈ n.divisors, orderedFactorizationCount (k + 1) (n / a)

@[simp] theorem orderedFactorizationCount_zero (n : ℕ) :
    orderedFactorizationCount 0 n = 0 := rfl

theorem orderedFactorizationCount_one {n : ℕ} (hn : 1 ≤ n) :
    orderedFactorizationCount 1 n = 1 := by
  simp [orderedFactorizationCount, Nat.ne_of_gt (Nat.zero_lt_of_lt hn)]

/-- Genuine divisor-convolution recurrence for every positive number of
factors. -/
theorem orderedFactorizationCount_succ {k n : ℕ} (hk : 1 ≤ k) :
    orderedFactorizationCount (k + 1) n =
      ∑ a ∈ n.divisors, orderedFactorizationCount k (n / a) := by
  cases k with
  | zero => omega
  | succ k =>
      cases k <;> rfl

/-- The summatory ordered-factorization function. -/
def orderedFactorizationSum (k R : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 R, (orderedFactorizationCount k d : ℝ)

theorem orderedFactorizationSum_one {R : ℕ} (hR : 1 ≤ R) :
    orderedFactorizationSum 1 R = R := by
  unfold orderedFactorizationSum
  calc
    (∑ d ∈ Icc 1 R, (orderedFactorizationCount 1 d : ℝ)) =
        ∑ _d ∈ Icc 1 R, (1 : ℝ) := by
      apply sum_congr rfl
      intro d hd
      rw [orderedFactorizationCount_one (mem_Icc.mp hd).1, Nat.cast_one]
    _ = R := by
      rw [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
      norm_num [hR]

/-- Exact finite hyperbola recurrence for the summatory function. -/
theorem orderedFactorizationSum_succ {k R : ℕ} (hk : 1 ≤ k) :
    orderedFactorizationSum (k + 1) R =
      ∑ a ∈ Icc 1 R, orderedFactorizationSum k (R / a) := by
  unfold orderedFactorizationSum
  calc
    (∑ d ∈ Icc 1 R, (orderedFactorizationCount (k + 1) d : ℝ)) =
        ∑ d ∈ Icc 1 R, ∑ a ∈ d.divisors,
          (orderedFactorizationCount k (d / a) : ℝ) := by
      apply sum_congr rfl
      intro d _
      rw [orderedFactorizationCount_succ hk, Nat.cast_sum]
    _ = ∑ a ∈ Icc 1 R, ∑ m ∈ Icc 1 (R / a),
          (orderedFactorizationCount k m : ℝ) :=
      (finiteSelberg_sum_hyperbola R
        (fun _a m ↦ (orderedFactorizationCount k m : ℝ))).symm
    _ = ∑ a ∈ Icc 1 R,
          ∑ d ∈ Icc 1 (R / a), (orderedFactorizationCount k d : ℝ) := rfl

private theorem one_add_log_nonneg {R : ℕ} (hR : 1 ≤ R) :
    0 ≤ 1 + Real.log R := by
  exact add_nonneg zero_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hR))

private theorem orderedFactorization_quotient_term_le
    {j R a : ℕ} (hR : 1 ≤ R) (ha : a ∈ Icc 1 R)
    (hprev : ∀ Q : ℕ, 1 ≤ Q →
      orderedFactorizationSum (j + 1) Q ≤
        (Q : ℝ) * (1 + Real.log Q) ^ j) :
    orderedFactorizationSum (j + 1) (R / a) ≤
      ((R : ℝ) / a) * (1 + Real.log R) ^ j := by
  have ha0 : 0 < a := Nat.zero_lt_of_lt (mem_Icc.mp ha).1
  have hdiv : 1 ≤ R / a :=
    Nat.one_le_iff_ne_zero.mpr (Nat.div_pos (mem_Icc.mp ha).2 ha0).ne'
  have hlogq0 : 0 ≤ 1 + Real.log (R / a : ℕ) := one_add_log_nonneg hdiv
  have hlogR0 : 0 ≤ 1 + Real.log R := one_add_log_nonneg hR
  have hqR : R / a ≤ R := Nat.div_le_self R a
  have hlog : 1 + Real.log (R / a : ℕ) ≤ 1 + Real.log R := by
    exact _root_.add_le_add le_rfl
      (Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hdiv))
        (Nat.cast_le.mpr hqR))
  calc
    orderedFactorizationSum (j + 1) (R / a) ≤
        ((R / a : ℕ) : ℝ) * (1 + Real.log (R / a : ℕ)) ^ j :=
      hprev (R / a) hdiv
    _ ≤ ((R : ℝ) / a) * (1 + Real.log R) ^ j :=
      mul_le_mul Nat.cast_div_le
        (pow_le_pow_left₀ hlogq0 hlog j)
        (pow_nonneg hlogq0 j)
        (div_nonneg (Nat.cast_nonneg R) (Nat.cast_nonneg a))

/-- The cumulative number of ordered `k`-factor factorizations is bounded
by the classical harmonic envelope. -/
theorem orderedFactorizationSum_le
    (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R) :
    orderedFactorizationSum k R ≤
      (R : ℝ) * (1 + Real.log R) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  induction j generalizing R with
  | zero =>
      rw [orderedFactorizationSum_one hR]
      simp
  | succ j ih =>
      change orderedFactorizationSum (Nat.succ j + 1) R ≤
        (R : ℝ) * (1 + Real.log R) ^ Nat.succ j
      have hbase : 0 ≤ 1 + Real.log R := one_add_log_nonneg hR
      have hrec := orderedFactorizationSum_succ (R := R)
        (k := Nat.succ j) (Nat.succ_le_succ (Nat.zero_le j))
      rw [hrec]
      have hterm : ∀ a ∈ Icc 1 R,
          orderedFactorizationSum (Nat.succ j) (R / a) ≤
            ((R : ℝ) / a) * (1 + Real.log R) ^ j := by
        intro a ha
        exact orderedFactorization_quotient_term_le hR ha
          (fun Q hQ ↦ by
            simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right] using
              ih Q hQ (by omega))
      calc
        (∑ a ∈ Icc 1 R, orderedFactorizationSum (Nat.succ j) (R / a)) ≤
            ∑ a ∈ Icc 1 R,
              ((R : ℝ) / a) * (1 + Real.log R) ^ j :=
          sum_le_sum hterm
        _ = (R : ℝ) * (1 + Real.log R) ^ j *
            ∑ a ∈ Icc 1 R, (a : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro a ha
          have haR : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
            (Nat.ne_of_gt (Nat.zero_lt_of_lt (mem_Icc.mp ha).1))
          field_simp [haR]
          <;> ring
        _ ≤ (R : ℝ) * (1 + Real.log R) ^ j * (1 + Real.log R) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (Nat.cast_nonneg R) (pow_nonneg hbase j))
          rw [← selbergJR_harmonic_eq_sum_inv]
          exact harmonic_le_one_add_log R
        _ = (R : ℝ) * (1 + Real.log R) ^ (Nat.succ j) := by
          rw [pow_succ]
          ring

/-- The paper uses `d < R`; changing to that convention only shrinks the
already bounded nonnegative sum. -/
theorem orderedFactorizationSum_lt_le
    (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R) :
    (∑ d ∈ Ico 1 R, (orderedFactorizationCount k d : ℝ)) ≤
      (R : ℝ) * (1 + Real.log R) ^ (k - 1) := by
  calc
    (∑ d ∈ Ico 1 R, (orderedFactorizationCount k d : ℝ)) ≤
        ∑ d ∈ Icc 1 R, (orderedFactorizationCount k d : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact Ico_subset_Icc_self
      · intro d _ _
        exact Nat.cast_nonneg _
    _ = orderedFactorizationSum k R := rfl
    _ ≤ _ := orderedFactorizationSum_le k R hk hR

end

end PrimeGapNormality.Prime.CoreOrderedFactorizationBound
