import PrimeGapNormality.Prime.CoreRoughMovingCount
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Exact interval slicing for the moving-rough arithmetic supplier

The discarded last interval costs its actual integer length.  The formulas
hold even for empty slices and locally impossible tuples.  No density or
model approximation is assumed in the partition identities.

Integration warning: the remainder estimate below is per predicate. For
the growing stopped inclusion sum, use only the complete-cell interval
of length q*H (as in CoreRoughSliceLaws). Restore discarded anchors once
after stopped comparison; do not sum the N%H cost over all inclusions.
-/

namespace PrimeGapNormality.Prime.CoreRoughIntervalSlices

open Finset CoreRoughMovingCount
open scoped Classical
noncomputable section

set_option maxHeartbeats 800000

def predicateCount (P : ℕ → Prop) (a H : ℕ) : ℝ :=
  ((Ico a (a + H)).filter P).card

theorem predicateCount_eq_sum (P : ℕ → Prop) (a H : ℕ) :
    predicateCount P a H = ∑ n ∈ Ico a (a + H), if P n then (1 : ℝ) else 0 := by
  simp only [predicateCount, Finset.sum_boole]

theorem predicateCount_nonneg (P : ℕ → Prop) (a H : ℕ) :
    0 ≤ predicateCount P a H := Nat.cast_nonneg _

theorem predicateCount_le_length (P : ℕ → Prop) (a H : ℕ) :
    predicateCount P a H ≤ (H : ℝ) := by
  have hh := Finset.card_filter_le (Ico a (a + H)) P
  simpa only [predicateCount, Nat.card_Ico, Nat.add_sub_cancel_left] using
    (Nat.cast_le.mpr hh : (((Ico a (a + H)).filter P).card : ℝ) ≤ (Ico a (a + H)).card)

theorem predicateCount_add (P : ℕ → Prop) (a H K : ℕ) :
    predicateCount P a (H + K) = predicateCount P a H + predicateCount P (a + H) K := by
  simp only [predicateCount_eq_sum, ← Nat.add_assoc]
  exact (Finset.sum_Ico_consecutive (fun n ↦ if P n then (1 : ℝ) else 0)
    (Nat.le_add_right a H) (Nat.le_add_right (a + H) K)).symm

theorem predicateCount_mul (P : ℕ → Prop) (a H q : ℕ) :
    predicateCount P a (q * H) =
      ∑ i ∈ range q, predicateCount P (a + i * H) H := by
  induction q with
  | zero => simp [predicateCount]
  | succ q ih =>
      rw [Nat.succ_mul, predicateCount_add, ih, Finset.sum_range_succ]

/-- Division with remainder gives an exact count partition, including H=0. -/
theorem predicateCount_division (P : ℕ → Prop) (a N H : ℕ) :
    predicateCount P a N =
      (∑ i ∈ range (N / H), predicateCount P (a + i * H) H) +
        predicateCount P (a + N / H * H) (N % H) := by
  have hN : N / H * H + N % H = N := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N H
  calc
    predicateCount P a N = predicateCount P a (N / H * H + N % H) := by rw [hN]
    _ = predicateCount P a (N / H * H) +
        predicateCount P (a + N / H * H) (N % H) := predicateCount_add _ _ _ _
    _ = _ := by rw [predicateCount_mul]

theorem discarded_count_bound (P : ℕ → Prop) (a N H : ℕ) :
    |predicateCount P a N -
      ∑ i ∈ range (N / H), predicateCount P (a + i * H) H| ≤ (N % H : ℕ) := by
  rw [predicateCount_division, add_sub_cancel_left,
    abs_of_nonneg (predicateCount_nonneg _ _ _)]
  exact predicateCount_le_length _ _ _

/-- Only the cell errors are summed. The last cell is paid once, without
any multiplication by the number of full cells. -/
theorem sliced_predicate_error (P : ℕ → Prop) (a N H : ℕ)
    (main error : ℕ → ℝ)
    (hcell : ∀ i ∈ range (N / H),
      |predicateCount P (a + i * H) H - main i| ≤ error i) :
    |predicateCount P a N - ∑ i ∈ range (N / H), main i| ≤
      (∑ i ∈ range (N / H), error i) + (N % H : ℕ) := by
  have hsum :
      |(∑ i ∈ range (N / H), predicateCount P (a + i * H) H) -
        ∑ i ∈ range (N / H), main i| ≤ ∑ i ∈ range (N / H), error i := by
    rw [← Finset.sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hcell)
  have hdiscard := discarded_count_bound P a N H
  have htri := abs_add_le
    (predicateCount P a N - ∑ i ∈ range (N / H), predicateCount P (a + i * H) H)
    ((∑ i ∈ range (N / H), predicateCount P (a + i * H) H) -
      ∑ i ∈ range (N / H), main i)
  rw [sub_add_sub_cancel] at htri
  linarith

theorem movingTupleInterval_count_eq (z : ℕ → ℕ) (E : Finset ℕ) (a H : ℕ) :
    ((movingTupleInterval z E a H).card : ℝ) =
      predicateCount (fun n ↦ ∀ h ∈ E, CoreMovingRoughSequence.RoughAt (z (n + h)) (n + h)) a H := by
  unfold movingTupleInterval predicateCount
  congr

/-- The partition estimate for the literal moving-rough tuple set. -/
theorem sliced_movingTuple_error (z : ℕ → ℕ) (E : Finset ℕ) (a N H : ℕ)
    (main error : ℕ → ℝ)
    (hcell : ∀ i ∈ range (N / H),
      |((movingTupleInterval z E (a + i * H) H).card : ℝ) - main i| ≤ error i) :
    |((movingTupleInterval z E a N).card : ℝ) - ∑ i ∈ range (N / H), main i| ≤
      (∑ i ∈ range (N / H), error i) + (N % H : ℕ) := by
  simp only [movingTupleInterval_count_eq] at hcell ⊢
  exact sliced_predicate_error _ a N H main error hcell

/-- The literal arithmetic supplier on all complete cells. All premises
are finite cutoff/level conditions; no pattern-count approximation is an
input. The locally forbidden case is included in the same estimate. -/
theorem sliced_movingTuple_sieve_error
    (z : ℕ → ℕ) (E : Finset ℕ) (hE : 1 ≤ E.card)
    (a N H : ℕ) (ha : 1 ≤ a) (yl yu : ℕ → ℕ) (δ : ℕ → ℝ) (R : ℝ)
    (hcutoffs : ∀ i ∈ range (N / H), 16 ≤ yl i ∧ yl i ≤ yu i)
    (hcut : ∀ i ∈ range (N / H), ∀ n ∈ Ico (a + i * H) (a + i * H + H),
      ∀ h ∈ E, yl i ≤ z (n + h) ∧ z (n + h) ≤ yu i)
    (hδ : ∀ i ∈ range (N / H), δ i ≤ 1 / 2)
    (hband : ∀ i ∈ range (N / H),
      ∑ p ∈ Nat.primesLE (yu i) \ Nat.primesLE (yl i),
        (residueCount E p : ℝ) / (p : ℝ) ≤ δ i)
    (hlevel : ∀ i ∈ range (N / H),
      ((yu i : ℝ) + 1 / 2) ^ (9 * E.card + 1) ≤ R) :
    |((movingTupleInterval z E a N).card : ℝ) -
      ∑ i ∈ range (N / H), (H : ℝ) * finiteTupleSieveProduct E (yl i)| ≤
      (∑ i ∈ range (N / H),
        ((H : ℝ) * finiteTupleSieveProduct E (yl i) *
          (δ i + Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log ((yu i : ℝ) + 1 / 2))) +
          Real.exp (10 * (E.card : ℝ)) * R * (1 + Real.log R) ^ (E.card - 1))) +
        (N % H : ℕ) := by
  apply sliced_movingTuple_error
  intro i hi
  exact movingTupleInterval_error z E hE (a + i * H) H
    (ha.trans (Nat.le_add_right _ _)) (hcutoffs i hi).1 (hcutoffs i hi).2
    (hcut i hi) (hδ i hi) (hband i hi) (hlevel i hi)

end
end PrimeGapNormality.Prime.CoreRoughIntervalSlices
