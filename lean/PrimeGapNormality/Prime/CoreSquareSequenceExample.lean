import PrimeGapNormality.Prime.PosMassScale
import PrimeGapNormality.Prime.StatisticalCriterion

/-!
# The square-sequence counterexample

The paper indexes its sequence from one.  Thus its `a_n = n^2` is represented
here by `squareSequence n = (n+1)^2`.  The corresponding zero-based gap is
`2n+3`, and its base-`B` gap series has the rational value

`(3B-1)/(B-1)^2`.

This is a self-contained deterministic calculation.  It makes no assertion
about primes and uses no arithmetic or distributional hypothesis.
-/

namespace PrimeGapNormality.Prime.CoreSquareSequenceExample

open Filter Finset
open scoped Topology BigOperators

noncomputable section

/-- Lean's zero-based encoding of the paper sequence `a_n=n^2`, `n>=1`. -/
def squareSequence (n : ℕ) : ℕ := (n + 1) ^ 2

theorem squareSequence_strictMono : StrictMono squareSequence := by
  intro m n hmn
  unfold squareSequence
  exact Nat.pow_lt_pow_left (by omega : m + 1 < n + 1)
    (by norm_num : (2 : ℕ) ≠ 0)

/-- The actual consecutive gap is `a_(n+2)-a_(n+1)=2n+3`. -/
theorem squareSequence_gap (n : ℕ) :
    seqGap squareSequence n = 2 * n + 3 := by
  unfold seqGap squareSequence
  rw [Nat.sub_eq_iff_eq_add
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ n + 1 + 1) 2)]
  ring

theorem squareSequence_gap_paperIndex (n : ℕ) :
    seqGap squareSequence n = 2 * (n + 1) + 1 := by
  rw [squareSequence_gap]
  ring

/-- Literal zero-based form of the paper series
`sum_(n>=1) (2n+1)/B^n`. -/
def squareGapSeries (B : ℕ) : ℝ :=
  ∑' n : ℕ, (seqGap squareSequence n : ℝ) / (B : ℝ) ^ (n + 1)

/-- The literal square-gap series is genuinely summable for every `B>=2`. -/
theorem squareGapSeries_summable {B : ℕ} (hB : 2 ≤ B) :
    Summable (fun n : ℕ =>
      (seqGap squareSequence n : ℝ) / (B : ℝ) ^ (n + 1)) := by
  have hBr : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  have hn := (summable_nat_div_pow_succ hBr).mul_left (2 : ℝ)
  have h1 := (summable_one_div_pow_succ hBr).mul_left (3 : ℝ)
  apply (hn.add h1).congr
  intro n
  rw [squareSequence_gap]
  push_cast
  ring

/-- Closed form of the actual `tsum`, with the paper/Lean index shift made
explicit in `squareSequence_gap`. -/
theorem squareGapSeries_eq {B : ℕ} (hB : 2 ≤ B) :
    squareGapSeries B =
      (3 * (B : ℝ) - 1) / ((B : ℝ) - 1) ^ 2 := by
  have hBr : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  have hn := (summable_nat_div_pow_succ hBr).mul_left (2 : ℝ)
  have h1 := (summable_one_div_pow_succ hBr).mul_left (3 : ℝ)
  unfold squareGapSeries
  rw [show (fun n : ℕ =>
      (seqGap squareSequence n : ℝ) / (B : ℝ) ^ (n + 1)) =
        fun n : ℕ =>
          2 * ((n : ℝ) / (B : ℝ) ^ (n + 1)) +
            3 * ((1 : ℝ) / (B : ℝ) ^ (n + 1)) by
    funext n
    rw [squareSequence_gap]
    push_cast
    ring]
  rw [Summable.tsum_add hn h1, tsum_mul_left, tsum_mul_left,
    tsum_nat_div_pow_succ hBr, tsum_one_div_pow_succ hBr]
  have hden : (B : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hden] <;> ring

/-- The closed form is the cast of an explicit rational number. -/
theorem squareGapSeries_rational {B : ℕ} (hB : 2 ≤ B) :
    ∃ q : ℚ, squareGapSeries B = (q : ℝ) := by
  refine ⟨(3 * (B : ℚ) - 1) / ((B : ℚ) - 1) ^ 2, ?_⟩
  rw [squareGapSeries_eq hB]
  push_cast <;> rfl

end

end PrimeGapNormality.Prime.CoreSquareSequenceExample
