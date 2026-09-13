import PrimeGapNormality.Digital.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite gap telescoping and Abel identity

Contracts 1 and 2. Inclusive `Icc 0 N` is used only for the position partial
`A_N`. Gap sums stay exclusive-end (`range` / `Ico`). No infinite Abel.
-/

open Finset

namespace PrimeGapNormality

/-! ### Position partial sum -/

/-- Position partial sum `A_N` (Contract 2). Inclusive `Icc 0 N`; this is `{0}`
at `N = 0`, which is the correct one-term sum.

Source: `rounds/round47/audit_fst_normality_certificate.py` `test_abel_identity`;
`lean/SOURCE_LEDGER.md` Contract 2; `lean/ARCHITECTURE.md` (Finite Abel).
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
def posPartial (a : ℕ → ℕ) (b : ℕ) (N : ℕ) : ℚ :=
  ∑ n ∈ Icc 0 N, (a n : ℚ) / (b : ℚ) ^ (n + 1)

/-- Inclusive `Icc 0 N` agrees with exclusive `range (N+1)`.

Source: same as `posPartial`.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem posPartial_eq_sum_range (a : ℕ → ℕ) (b : ℕ) (N : ℕ) :
    posPartial a b N = ∑ n ∈ range (N + 1), (a n : ℚ) / (b : ℚ) ^ (n + 1) := by
  simp [posPartial, Nat.range_succ_eq_Icc_zero]

/-- One-term position sum at `N = 0`.

Source: same as `posPartial`.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem posPartial_zero (a : ℕ → ℕ) (b : ℕ) :
    posPartial a b 0 = (a 0 : ℚ) / b := by
  simp [posPartial, Icc_self]

/-- Successor recurrence for `A_N`.

Source: same as `posPartial`.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem posPartial_succ (a : ℕ → ℕ) (b : ℕ) (N : ℕ) :
    posPartial a b (N + 1) =
      posPartial a b N + (a (N + 1) : ℚ) / (b : ℚ) ^ (N + 2) := by
  simp [posPartial_eq_sum_range, sum_range_succ]

/-- Successor recurrence for `B_N = gapPartial a b N`.

Source: same as `gapPartial`.
Contract: C2
Audit: GREEN

Index: paper `g_n` is Lean `gap a (n-1)`; paper `a_n` is Lean `a (n-1)`. -/
theorem gapPartial_succ (a : ℕ → ℕ) (b : ℕ) (N : ℕ) :
    gapPartial a b (N + 1) =
      gapPartial a b N + (gap a N : ℚ) / (b : ℚ) ^ (N + 1) := by
  simp [gapPartial, sum_range_succ]

/-- Cast of a gap to `ℚ` is the true difference.

Source: `lean/SOURCE_LEDGER.md` Contract 1; `gap_int` in `Basic.Sequence`.
Contract: C1
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem gap_rat {a : ℕ → ℕ} (ha : StrictMono a) (n : ℕ) :
    (gap a n : ℚ) = (a (n + 1) : ℚ) - a n := by
  have := congrArg (fun z : ℤ => (z : ℚ)) (gap_int ha n)
  simpa using this

private theorem b_cast_ne_zero {b : ℕ} (hb : 2 ≤ b) : (b : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

/-! ### Contract 1: gap telescoping -/

/-- Finite gap telescoping in `ℤ`. Empty at `k = 0`; one term at `k = 1`.

Source: `rounds/round47/05_manuscript_v3.tex` Lemma Mean tails (telescoping
step); ledger **ALG-H** (G); Round 51 Lemma 3 proof as identity only;
`lean/SOURCE_LEDGER.md` Contract 1.
Contract: C1
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. Exclusive
length `k` (`range k`). -/
theorem sum_gap_int {a : ℕ → ℕ} (ha : StrictMono a) (m k : ℕ) :
    ∑ i ∈ range k, (gap a (m + i) : ℤ) = (a (m + k) : ℤ) - a m := by
  have hterm (i : ℕ) :
      (gap a (m + i) : ℤ) = (a (m + (i + 1)) : ℤ) - a (m + i) := by
    simpa [Nat.add_assoc] using gap_int ha (m + i)
  simp_rw [hterm]
  simpa using sum_range_sub (fun i => (a (m + i) : ℤ)) k

/-- Empty telescoping (`k = 0`).

Source: same as `sum_gap_int`.
Contract: C1
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem sum_gap_int_zero {a : ℕ → ℕ} (ha : StrictMono a) (m : ℕ) :
    ∑ i ∈ range 0, (gap a (m + i) : ℤ) = (a (m + 0) : ℤ) - a m :=
  sum_gap_int ha m 0

/-- One-gap telescoping (`k = 1`), proved from `gap_int` directly.

Source: same as `sum_gap_int`.
Contract: C1
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem sum_gap_int_one {a : ℕ → ℕ} (ha : StrictMono a) (m : ℕ) :
    ∑ i ∈ range 1, (gap a (m + i) : ℤ) = (a (m + 1) : ℤ) - a m := by
  simp [gap_int ha]

/-- Equivalent `Ico` form of Contract 1.

Source: same as `sum_gap_int`.
Contract: C1
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. Exclusive
end `Ico m (m+k)`. -/
theorem sum_gap_Ico_int {a : ℕ → ℕ} (ha : StrictMono a) (m k : ℕ) :
    ∑ i ∈ Ico m (m + k), (gap a i : ℤ) = (a (m + k) : ℤ) - a m := by
  simp_rw [gap_int ha]
  exact sum_Ico_sub (fun i => (a i : ℤ)) (Nat.le_add_right m k)

/-- Finite gap telescoping in `ℚ`.

Source: same as `sum_gap_int`.
Contract: C1
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem sum_gap_rat {a : ℕ → ℕ} (ha : StrictMono a) (m k : ℕ) :
    ∑ i ∈ range k, (gap a (m + i) : ℚ) = (a (m + k) : ℚ) - a m := by
  have := congrArg (fun z : ℤ => (z : ℚ)) (sum_gap_int ha m k)
  simpa [Int.cast_sum] using this

/-- Empty telescoping in `ℚ` (`k = 0`).

Source: same as `sum_gap_int`.
Contract: C1
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem sum_gap_rat_zero {a : ℕ → ℕ} (ha : StrictMono a) (m : ℕ) :
    ∑ i ∈ range 0, (gap a (m + i) : ℚ) = (a (m + 0) : ℚ) - a m :=
  sum_gap_rat ha m 0

/-- One-gap telescoping in `ℚ` (`k = 1`).

Source: same as `sum_gap_int`.
Contract: C1
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem sum_gap_rat_one {a : ℕ → ℕ} (ha : StrictMono a) (m : ℕ) :
    ∑ i ∈ range 1, (gap a (m + i) : ℚ) = (a (m + 1) : ℚ) - a m :=
  sum_gap_rat ha m 1

/-! ### Contract 2: finite Abel identity -/

/-- Finite Abel identity at `N = 0` (empty gap sum). No `StrictMono` is
required: there are no gaps. `b ≥ 2` makes `b ≠ 0` in `ℚ`.

Source: `rounds/round47/audit_fst_normality_certificate.py` `test_abel_identity`;
`lean/SOURCE_LEDGER.md` Contract 2.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem gapPartial_abel_zero (a : ℕ → ℕ) {b : ℕ} (hb : 2 ≤ b) :
    gapPartial a b 0 =
      ((b : ℚ) - 1) * posPartial a b 0 - a 0 + (a 0 : ℚ) / (b : ℚ) ^ (0 + 1) := by
  have hb0 := b_cast_ne_zero hb
  simp [gapPartial, posPartial_zero, pow_one]
  refine Eq.symm ?_
  calc ((b : ℚ) - 1) * ((a 0 : ℚ) / b) - (a 0 : ℚ) + (a 0 : ℚ) / b
      = ((b : ℚ) - 1) * (a 0 : ℚ) / b + (a 0 : ℚ) / b - (a 0 : ℚ) := by
        rw [mul_div_assoc]
        ring
    _ = (((b : ℚ) - 1) * (a 0 : ℚ) + (a 0 : ℚ)) / b - (a 0 : ℚ) := by
        rw [← add_div]
    _ = ((b : ℚ) * (a 0 : ℚ)) / b - (a 0 : ℚ) := by ring
    _ = (a 0 : ℚ) - (a 0 : ℚ) := by
        rw [mul_comm (b : ℚ), mul_div_cancel_right₀ _ hb0]
    _ = 0 := by ring

/-- Coefficient identity `x / b^{N+1} = (b-1) (x / b^{N+2}) + x / b^{N+2}`. -/
private theorem abel_coeff_succ {b : ℕ} (hb0 : (b : ℚ) ≠ 0) (x : ℚ) (N : ℕ) :
    x / (b : ℚ) ^ (N + 1) =
      ((b : ℚ) - 1) * (x / (b : ℚ) ^ (N + 2)) + x / (b : ℚ) ^ (N + 2) := by
  have hpow : (b : ℚ) ^ (N + 2) = (b : ℚ) ^ (N + 1) * (b : ℚ) := pow_succ _ _
  refine Eq.symm ?_
  calc ((b : ℚ) - 1) * (x / (b : ℚ) ^ (N + 2)) + x / (b : ℚ) ^ (N + 2)
      = ((b : ℚ) - 1) * x / (b : ℚ) ^ (N + 2) + x / (b : ℚ) ^ (N + 2) := by
        rw [mul_div_assoc]
    _ = (((b : ℚ) - 1) * x + x) / (b : ℚ) ^ (N + 2) := by
        rw [← add_div]
    _ = ((b : ℚ) * x) / (b : ℚ) ^ (N + 2) := by ring
    _ = x / (b : ℚ) ^ (N + 1) := by
        rw [hpow, mul_comm ((b : ℚ) ^ (N + 1))]
        exact mul_div_mul_left x _ hb0

/-- Finite Abel identity with remainder: `B_N = (b-1) A_N - a_0 + a_N b^{-(N+1)}`,
including `N = 0`.

Source: `rounds/round47/audit_fst_normality_certificate.py` `test_abel_identity`;
`lean/SOURCE_LEDGER.md` Contract 2. Infinite form without remainder is **not**
an M1 theorem.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. `B_N` is
`gapPartial a b N`. -/
theorem gapPartial_abel {a : ℕ → ℕ} (ha : StrictMono a) {b : ℕ} (hb : 2 ≤ b)
    (N : ℕ) :
    gapPartial a b N =
      ((b : ℚ) - 1) * posPartial a b N - a 0 + (a N : ℚ) / (b : ℚ) ^ (N + 1) := by
  have hb0 := b_cast_ne_zero hb
  induction N with
  | zero =>
    exact gapPartial_abel_zero a hb
  | succ N ih =>
    rw [gapPartial_succ, posPartial_succ, ih, gap_rat ha]
    have hcollapse :
        ((b : ℚ) - 1) * posPartial a b N - a 0 + (a N : ℚ) / (b : ℚ) ^ (N + 1)
          + ((a (N + 1) : ℚ) - a N) / (b : ℚ) ^ (N + 1) =
          ((b : ℚ) - 1) * posPartial a b N - a 0
            + (a (N + 1) : ℚ) / (b : ℚ) ^ (N + 1) := by
      ring
    rw [hcollapse, abel_coeff_succ hb0 (a (N + 1) : ℚ) N]
    ring

/-! ### Affine rationality transfer (assumed equality, not infinite Abel) -/

private theorem b_sub_one_ne_zero {K : Type*} [Field K] [CharZero K] {b : ℕ}
    (hb : 2 ≤ b) : (b : K) - 1 ≠ 0 := by
  rw [sub_ne_zero, ne_eq, Nat.cast_eq_one]
  omega

/-- Affine rationality transfer from an **assumed** equality `B = (b-1)A - a_0`.
Does not prove infinite Abel. `A` is rational iff `B` is.

Source: `lean/SOURCE_LEDGER.md` Contract 2 (affine transfer, separate from the
finite identity); `lean/ARCHITECTURE.md` (Finite Abel).
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. The constant
`a0` is that paper `a_1`. -/
theorem affine_eq_rat_iff {K : Type*} [Field K] [CharZero K] {A B : K} {a0 b : ℕ}
    (hb : 2 ≤ b) (h : B = ((b : K) - 1) * A - a0) :
    (∃ q : ℚ, A = (q : K)) ↔ (∃ r : ℚ, B = (r : K)) := by
  have hb1 := b_sub_one_ne_zero (K := K) hb
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨((b : ℚ) - 1) * q - (a0 : ℚ), ?_⟩
    simp [h, hq]
  · rintro ⟨r, hr⟩
    refine ⟨(r + (a0 : ℚ)) / ((b : ℚ) - 1), ?_⟩
    have hA : A = (B + a0) / ((b : K) - 1) := by
      rw [eq_div_iff hb1, h]
      ring
    have hnum : (r : K) + a0 = Rat.cast (r + (a0 : ℚ)) := by
      rw [← Rat.cast_natCast a0, ← Rat.cast_add]
    have hden : (b : K) - 1 = Rat.cast ((b : ℚ) - 1) := by
      rw [Rat.cast_sub, Rat.cast_natCast, Rat.cast_one]
    rw [hA, hr, hnum, hden, ← Rat.cast_div]

/-- Real form of affine rationality transfer from an assumed real equality.

Source: same as `affine_eq_rat_iff`.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
theorem affine_eq_rat_iff_real {A B : ℝ} {a0 b : ℕ} (hb : 2 ≤ b)
    (h : B = ((b : ℝ) - 1) * A - a0) :
    (∃ q : ℚ, A = (q : ℝ)) ↔ (∃ r : ℚ, B = (r : ℝ)) :=
  affine_eq_rat_iff hb h

/-- Integer transfer from the same assumed equality: if `A` is an integer then
so is `B`. The converse is false for `b > 2` (e.g. `A = 1/2`, `b = 3`).

Source: `lean/SOURCE_LEDGER.md` Contract 2 (affine transfer, separate from the
finite identity); `lean/ARCHITECTURE.md` (Finite Abel).
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. The constant
`a0` is that paper `a_1`. -/
theorem affine_eq_int_of_int {K : Type*} [Field K] [CharZero K] {A B : K} {a0 b : ℕ}
    (_hb : 2 ≤ b) (h : B = ((b : K) - 1) * A - a0) :
    (∃ z : ℤ, A = (z : K)) → (∃ w : ℤ, B = (w : K)) := by
  rintro ⟨z, hz⟩
  refine ⟨((b : ℤ) - 1) * z - (a0 : ℤ), ?_⟩
  simp [h, hz]

/-- If `B` is an integer, then `A` is rational, under the assumed affine
equality. Does not claim that `A` is an integer.

Source: `lean/SOURCE_LEDGER.md` Contract 2 (affine transfer, separate from the
finite identity); `lean/ARCHITECTURE.md` (Finite Abel).
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. The constant
`a0` is that paper `a_1`. -/
theorem affine_eq_rat_of_int {K : Type*} [Field K] [CharZero K] {A B : K} {a0 b : ℕ}
    (hb : 2 ≤ b) (h : B = ((b : K) - 1) * A - a0)
    (hB : ∃ w : ℤ, B = (w : K)) : ∃ q : ℚ, A = (q : K) :=
  (affine_eq_rat_iff hb h).mpr <| by
    obtain ⟨w, hw⟩ := hB
    exact ⟨(w : ℚ), by simp [hw]⟩

/-! ### Regression examples -/

private theorem idSucc_strictMono : StrictMono (fun n : ℕ => n + 1) :=
  fun _ _ h => Nat.add_lt_add_right h 1

/-- `N = 0` Abel for `a n = n+1`, `b = 2`.

Source: Contract 2 regression.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
example : gapPartial (fun n => n + 1) 2 0 =
    ((2 : ℚ) - 1) * posPartial (fun n => n + 1) 2 0 - (1 : ℕ) +
      (1 : ℚ) / (2 : ℚ) ^ (0 + 1) :=
  gapPartial_abel_zero (fun n => n + 1) (le_rfl : 2 ≤ 2)

/-- Independent `N = 0` evaluation: empty `B_0` and `A_0 = a_0 / b`.

Source: Contract 2 regression.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
example : gapPartial (fun n => n + 1) 2 0 = 0 := by
  simp [gapPartial]

/-- One-term `A_0 = a_0 / b` at `N = 0`.

Source: Contract 2 regression.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
example : posPartial (fun n => n + 1) 2 0 = (1 : ℚ) / 2 := by
  simp [posPartial_zero]

/-- Telescoping `k = 0`.

Source: Contract 1 regression.
Contract: C1
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
example : ∑ i ∈ range 0, (gap (fun n => n + 1) (0 + i) : ℤ) =
    ((fun n : ℕ => n + 1) (0 + 0) : ℤ) - (fun n : ℕ => n + 1) 0 :=
  sum_gap_int_zero idSucc_strictMono 0

/-- Telescoping `k = 1`.

Source: Contract 1 regression.
Contract: C1
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
example : ∑ i ∈ range 1, (gap (fun n => n + 1) (0 + i) : ℤ) =
    ((fun n : ℕ => n + 1) (0 + 1) : ℤ) - (fun n : ℕ => n + 1) 0 :=
  sum_gap_int_one idSucc_strictMono 0

/-- Concrete Abel for `a n = n+1`, `b = 2`, `N = 2`, by the theorem.

Source: Contract 2 regression.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
example : gapPartial (fun n => n + 1) 2 2 =
    ((2 : ℚ) - 1) * posPartial (fun n => n + 1) 2 2 - (1 : ℕ) +
      (3 : ℚ) / (2 : ℚ) ^ 3 :=
  gapPartial_abel idSucc_strictMono (le_rfl : 2 ≤ 2) 2

/-- Independent numerical Abel for triangular `a n = n(n+1)/2`, `b = 2`, `N = 2`.

Source: Contract 2 regression (`test_abel_identity` style).
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
example :
    gapPartial (fun n => n * (n + 1) / 2) 2 2 =
      ((2 : ℚ) - 1) * posPartial (fun n => n * (n + 1) / 2) 2 2 - (0 : ℕ) +
        (3 : ℚ) / (2 : ℚ) ^ 3 := by
  simp [gapPartial, posPartial_eq_sum_range, gap, sum_range_succ]
  norm_num

/-- Affine transfer instance over `ℝ` from an assumed equality (not a proved
infinite Abel identity).

Source: Contract 2 affine transfer regression.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
example {A B : ℝ} (h : B = ((2 : ℝ) - 1) * A - (1 : ℕ)) :
    (∃ q : ℚ, A = (q : ℝ)) ↔ (∃ r : ℚ, B = (r : ℝ)) :=
  affine_eq_rat_iff_real (le_rfl : 2 ≤ 2) h

/-- Integer implication from an assumed affine equality: `A ∈ ℤ` implies `B ∈ ℤ`.

Source: Contract 2 affine transfer regression.
Contract: C2
Audit: GREEN

Index: paper `a_n` is Lean `a (n-1)`; Lean `a 0` is paper `a_1`. -/
example {A B : ℚ} (h : B = ((2 : ℚ) - 1) * A - (1 : ℕ)) :
    (∃ z : ℤ, A = (z : ℚ)) → (∃ w : ℤ, B = (w : ℚ)) :=
  affine_eq_int_of_int (K := ℚ) (le_rfl : 2 ≤ 2) h

end PrimeGapNormality
