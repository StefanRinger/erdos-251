import PrimeGapNormality.Prime.CoreDigitalLipschitz
import Mathlib.Algebra.Field.GeomSum

/-!
# Finite comparison for a variable insertion clock

The block partition covers all ordinary digit positions. The comparison
pays for bad positions by their actual cardinality, without dividing by
the mass of a clock label. The final geometric identity sums the internal
amplifications instead of replacing them by their maximum.

These lemmas are finite bookkeeping, not a prime-distribution supplier.
-/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset
open scoped NNReal BoundedContinuousFunction

noncomputable section

/-- Exact partition into variable blocks, including the initial position. -/
theorem sum_variable_blocks {M : Type*} [AddCommMonoid M]
    (k P : ℕ → ℕ) (hzero : P 0 = 0)
    (hsucc : ∀ n, P (n + 1) = P n + k n) (F : ℕ → M) (N : ℕ) :
    (∑ n ∈ range N, ∑ r ∈ range (k n), F (P n + r)) =
      ∑ j ∈ range (P N), F j := by
  induction N with
  | zero => simp [hzero]
  | succ N ih =>
    rw [sum_range_succ, ih, hsucc, sum_range_add]

/-- A finite Lipschitz comparison with an explicit exceptional set.
No positivity assumption on the test is needed for this step. -/
theorem sum_test_le_with_bad {ι α : Type*} [DecidableEq ι] [PseudoMetricSpace α]
    (s : Finset ι) (good : ι → Prop) [DecidablePred good]
    (u v : ι → α) (f : α →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    (∑ i ∈ s, f (u i)) ≤ (∑ i ∈ s, f (v i)) +
      (K : ℝ) * (∑ i ∈ s.filter good, dist (u i) (v i)) +
      2 * ‖f‖ * ((s.filter fun i => ¬ good i).card : ℝ) := by
  have hpoint (i : ι) : f (u i) ≤ f (v i) +
      (if good i then (K : ℝ) * dist (u i) (v i) else 2 * ‖f‖) := by
    by_cases hi : good i
    · simp only [hi, if_true]
      have hd := hK.dist_le_mul (u i) (v i)
      rw [Real.dist_eq] at hd
      linarith [le_abs_self (f (u i) - f (v i))]
    · simp only [hi, if_false]
      have hd := f.dist_le_two_norm (u i) (v i)
      rw [Real.dist_eq] at hd
      linarith [le_abs_self (f (u i) - f (v i))]
  have hsum := sum_le_sum (fun i (_ : i ∈ s) => hpoint i)
  rw [sum_add_distrib] at hsum
  have hsplit :
      (∑ i ∈ s, if good i then (K : ℝ) * dist (u i) (v i) else 2 * ‖f‖) =
        (K : ℝ) * (∑ i ∈ s.filter good, dist (u i) (v i)) +
          2 * ‖f‖ * ((s.filter fun i => ¬ good i).card : ℝ) := by
    rw [sum_ite, ← mul_sum]
    simp [mul_comm]
  rw [hsplit] at hsum
  simpa only [add_assoc] using hsum

/-- Normalization is by the whole prefix, never by the good-set mass. -/
theorem average_test_le_with_bad {ι α : Type*} [DecidableEq ι]
    [PseudoMetricSpace α] (s : Finset ι) (good : ι → Prop)
    [DecidablePred good] (u v : ι → α) (f : α →ᵇ ℝ)
    {K : ℝ≥0} (hK : LipschitzWith K f) {W : ℝ} (hW : 0 ≤ W) :
    (∑ i ∈ s, f (u i)) / W ≤ (∑ i ∈ s, f (v i)) / W +
      (K : ℝ) * (∑ i ∈ s.filter good, dist (u i) (v i)) / W +
      2 * ‖f‖ * ((s.filter fun i => ¬ good i).card : ℝ) / W := by
  simpa only [add_div] using
    div_le_div_of_nonneg_right (sum_test_le_with_bad s good u v f hK) hW

/-- Summing the digit amplifications cancels the full local denominator.
This is the gain lost by bounding every `B^r` by `B^k` separately. -/
theorem sum_geometric_amplification {B : ℝ} (hB : 1 < B)
    {k : ℕ} (hk : 0 < k) (U : ℝ) :
    (∑ r ∈ range k, B ^ r * U / (B ^ k - 1)) = U / (B - 1) := by
  have hB1 : B - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hB)
  have hBk : B ^ k - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ hB (Nat.ne_of_gt hk)))
  rw [← sum_div, ← sum_mul, geom_sum_eq (ne_of_gt hB)]
  field_simp

end
end PrimeGapNormality.Prime.StretchedClock
