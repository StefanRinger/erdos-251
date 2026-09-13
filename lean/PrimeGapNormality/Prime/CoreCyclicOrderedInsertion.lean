import PrimeGapNormality.Prime.CoreCyclicPhysicalInsertion

/-!
# Ordered-subset specialization of cyclic insertion

The complete-frame exterior variables are filled by actual gaps of the
deleted ordered subset.  Inserting a point in its open slot produces
exactly the split real gap array used by `CoreCyclicPhysicalInsertion`.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Finset MvPolynomial
open scoped BigOperators

noncomputable section

/-- The actual nonnegative order-statistic gap, regarded as a real. -/
def orderedRealGap (E : Finset ℕ) (e : ℕ) : ℝ :=
  (subsetGap E e : ℝ)

/-- Exterior signed frame associated with deleting rank `j`.  Coordinate
zero is the whole insertion span. -/
def orderedExteriorGap (F : Finset ℕ) (j : ℕ) :
    OnePoint.ExteriorIndex → ℝ :=
  fun i ↦
    if hzero : (i : ℤ) = 0 then (subsetGap F (j - 1) : ℝ)
    else if hneg : (i : ℤ) < 0 then
      (subsetGap F (Int.toNat ((j : ℤ) + (i : ℤ))) : ℝ)
    else
      (subsetGap F (j + Int.toNat (i : ℤ) - 1) : ℝ)

@[simp] theorem orderedExteriorGap_zero (F : Finset ℕ) (j : ℕ) :
    orderedExteriorGap F j ⟨0, by norm_num⟩ =
      (subsetGap F (j - 1) : ℝ) := by
  simp [orderedExteriorGap]

theorem orderedExteriorGap_neg (F : Finset ℕ) (j : ℕ)
    (i : OnePoint.ExteriorIndex) (hi : (i : ℤ) < 0) :
    orderedExteriorGap F j i =
      (subsetGap F (Int.toNat ((j : ℤ) + (i : ℤ))) : ℝ) := by
  simp [orderedExteriorGap, hi, ne_of_lt hi]

theorem orderedExteriorGap_pos (F : Finset ℕ) (j : ℕ)
    (i : OnePoint.ExteriorIndex) (hi : 0 < (i : ℤ)) :
    orderedExteriorGap F j i =
      (subsetGap F (j + Int.toNat (i : ℤ) - 1) : ℝ) := by
  simp [orderedExteriorGap, hi, hi.ne', not_lt.mpr hi.le]

/-- The moving action coordinate is the new left gap, not the absolute
point position. -/
def orderedInsertionLeftGap (F : Finset ℕ) (j u : ℕ) : ℝ :=
  (u : ℝ) - (orderStat F (j - 1) : ℝ)

private theorem orderedRealGap_insert_left
    {F : Finset ℕ} {j u : ℕ} (hj : 1 ≤ j)
    (hu : (CoreLinearInsertion.insertionSlot F j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot F j).2) :
    orderedRealGap (insert u F) (j - 1) = orderedInsertionLeftGap F j u := by
  have hle : orderStat F (j - 1) ≤ u := by
    rw [← CoreLinearInsertion.insertionSlot_left]
    exact hu.1.le
  unfold orderedRealGap subsetGap orderedInsertionLeftGap
  rw [show j - 1 + 1 = j by omega,
    CoreLinearInsertion.orderStat_insert_at hj hu,
    CoreLinearInsertion.orderStat_insert_before hu (by omega : j - 1 < j),
    Nat.cast_sub hle]

private theorem orderedRealGap_insert_right
    {F : Finset ℕ} {j u : ℕ} (hj : 1 ≤ j)
    (hu : (CoreLinearInsertion.insertionSlot F j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot F j).2) :
    orderedRealGap (insert u F) j =
      (orderStat F j : ℝ) - u := by
  have hle : u ≤ orderStat F j := by
    rw [← CoreLinearInsertion.insertionSlot_right F hj]
    exact hu.2.le
  unfold orderedRealGap subsetGap
  rw [CoreLinearInsertion.orderStat_insert_at hj hu,
    CoreLinearInsertion.orderStat_insert_after hj hu (Nat.lt_succ_self j)]
  simp only [Nat.succ_sub_one, Nat.cast_sub hle]

private theorem orderedRealGap_insert_before
    {F : Finset ℕ} {j u e : ℕ}
    (hu : (CoreLinearInsertion.insertionSlot F j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot F j).2)
    (he : e + 1 < j) :
    orderedRealGap (insert u F) e = orderedRealGap F e := by
  unfold orderedRealGap subsetGap
  rw [CoreLinearInsertion.orderStat_insert_before hu he,
    CoreLinearInsertion.orderStat_insert_before hu (by omega : e < j)]

private theorem orderedRealGap_insert_after
    {F : Finset ℕ} {j u e : ℕ} (hj : 1 ≤ j)
    (hu : (CoreLinearInsertion.insertionSlot F j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot F j).2)
    (he : j < e) :
    orderedRealGap (insert u F) e = orderedRealGap F (e - 1) := by
  unfold orderedRealGap subsetGap
  rw [CoreLinearInsertion.orderStat_insert_after hj hu (by omega : j < e + 1),
    CoreLinearInsertion.orderStat_insert_after hj hu he]
  have hidx : e + 1 - 1 = (e - 1) + 1 := by omega
  rw [hidx]

/-- The abstract split array is exactly the gap array of the actual
ordered insertion. -/
theorem actionGapArray_orderedExterior
    {F : Finset ℕ} {j u e : ℕ} (hj : 1 ≤ j)
    (hu : (CoreLinearInsertion.insertionSlot F j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot F j).2) :
    actionGapArray (orderedExteriorGap F j)
        (orderedInsertionLeftGap F j u) j e =
      orderedRealGap (insert u F) e := by
  rcases lt_trichotomy e (j - 1) with hbefore | heq | hafter
  · have hej : e + 1 < j := by omega
    have hqj : e ≠ j := by omega
    have hqpred : e ≠ j - 1 := by omega
    rw [actionGapArray_eq_exterior _ _ hqpred hqj,
      orderedExteriorGap_neg, orderedRealGap_insert_before hu hej]
    · unfold orderedRealGap
      change (subsetGap F
          (Int.toNat ((j : ℤ) + ((e : ℤ) - (j : ℤ)))) : ℝ) =
        (subsetGap F e : ℝ)
      have htoNat : Int.toNat ((j : ℤ) + ((e : ℤ) - (j : ℤ))) = e := by
        rw [show (j : ℤ) + ((e : ℤ) - (j : ℤ)) = e by ring]
        simp
      rw [htoNat]
    · change (e : ℤ) - (j : ℤ) < 0
      omega
  · subst e
    rw [actionGapArray_left _ _ hj, orderedRealGap_insert_left hj hu]
  · rcases eq_or_lt_of_le (show j ≤ e from by omega) with heqj | hjlt
    · subst e
      rw [actionGapArray_right, orderedExteriorGap_zero,
        orderedRealGap_insert_right hj hu]
      have hjF : j - 1 < F.card := by
        have hlen := lt_length_of_mem_deletionSlot hu.2
        simpa [CoreLinearInsertion.insertionSlot] using hlen
      have hmono : orderStat F (j - 1) ≤ orderStat F j := by
        simpa [Nat.sub_add_cancel hj] using
          CoreLinearInsertion.orderStat_le_succ F hjF
      simp only [subsetGap, show j - 1 + 1 = j by omega]
      rw [Nat.cast_sub hmono]
      unfold orderedInsertionLeftGap
      ring
    · have hqpred : e ≠ j - 1 := by omega
      have hqj : e ≠ j := by omega
      rw [actionGapArray_eq_exterior _ _ hqpred hqj,
        orderedExteriorGap_pos, orderedRealGap_insert_after hj hu hjlt]
      · unfold orderedRealGap
        change (subsetGap F
            (j + Int.toNat ((e : ℤ) - (j : ℤ)) - 1) : ℝ) =
          (subsetGap F (e - 1) : ℝ)
        have htoNat : Int.toNat ((e : ℤ) - (j : ℤ)) = e - j := by
          have hcast : (e : ℤ) - (j : ℤ) = ((e - j : ℕ) : ℤ) := by
            rw [Nat.cast_sub hjlt.le]
          rw [hcast, Int.toNat_natCast]
        have hidx : j + (e - j) - 1 = e - 1 := by omega
        rw [htoNat, hidx]
      · change 0 < (e : ℤ) - (j : ℤ)
        exact sub_pos.mpr (by exact_mod_cast hjlt)

/-- Ordered-Finset version of the exact cyclic insertion identity. -/
theorem coreCyclicFinitePhase_ordered_insert_sub
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (K w j : ℕ)
    (hwj : w + 1 ≤ j) (hjK : j < K)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (F : Finset ℕ) {u v : ℕ}
    (hu : (CoreLinearInsertion.insertionSlot F j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot F j).2)
    (hv : (CoreLinearInsertion.insertionSlot F j).1 < v ∧
      v < (CoreLinearInsertion.insertionSlot F j).2) :
    coreCyclicFinitePhase B hk r P K (orderedRealGap (insert u F)) -
        coreCyclicFinitePhase B hk r P K (orderedRealGap (insert v F)) =
      (Polynomial.eval (orderedInsertionLeftGap F j u)
          (OnePoint.movingSpecialization
            (OnePoint.action B hk w (phaseAt hk r (j - 1)) P)
            (orderedExteriorGap F j)) -
        Polynomial.eval (orderedInsertionLeftGap F j v)
          (OnePoint.movingSpecialization
            (OnePoint.action B hk w (phaseAt hk r (j - 1)) P)
            (orderedExteriorGap F j))) /
        (B : ℝ) ^ (j + 1) := by
  have hj : 1 ≤ j := by omega
  have huGap : actionGapArray (orderedExteriorGap F j)
      (orderedInsertionLeftGap F j u) j = orderedRealGap (insert u F) := by
    funext (e : ℕ)
    exact actionGapArray_orderedExterior
      (F := F) (j := j) (u := u) (e := e) hj hu
  have hvGap : actionGapArray (orderedExteriorGap F j)
      (orderedInsertionLeftGap F j v) j = orderedRealGap (insert v F) := by
    funext (e : ℕ)
    exact actionGapArray_orderedExterior
      (F := F) (j := j) (u := v) (e := e) hj hv
  rw [← huGap, ← hvGap]
  exact coreCyclicFinitePhase_insert_sub hB hk r P K w j hwj hjK hw
    (orderedExteriorGap F j) _ _

end

end PrimeGapNormality.Prime.CoreCyclic
