import PrimeGapNormality.Prime.CoreIntegerGapObservable
import PrimeGapNormality.Prime.CoreActualCyclicSlot

/-!
# Actual finite insertion for arbitrary integer gap observables

Moving the point of rank `j` inside one ordered slot changes exactly the
gaps at ranks `j-1` and `j`.  For an arbitrary periodic integer observable
`F : Fin k → ℕ → ℤ`, their two weighted summands combine to

`B * F_s(leftGap) + F_(s+1)(rightGap)`

over the common denominator `B^(j+1)`.  All remaining finite-prefix terms
form an actual outer phase independent of the inserted point.  The selected
reference point comes from the genuine finite slot.

No polynomial, model, tail, or distribution hypothesis is used.
-/

namespace PrimeGapNormality.Prime.CoreIntegerGapInsertion

open Finset CoreCyclic
open CoreIntegerGapObservable
open scoped BigOperators Classical

noncomputable section

/-- Literal first-`L` phase on a finite natural gap array. -/
def finiteObservablePhase
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (L : ℕ) (g : ℕ → ℕ) : ℝ :=
  ∑ e ∈ range L, (F (phaseAt hk r e) (g e) : ℝ) / (B : ℝ) ^ (e + 1)

/-- The two adjacent integer observables with their exact common weight. -/
def pairActionInt
    (B : ℕ) {k : ℕ} (hk : 0 < k) (s : Fin k)
    (F : Fin k → ℕ → ℤ) (left right : ℕ) : ℤ :=
  (B : ℤ) * F s left + F (cyclicSucc hk s) right

private theorem sum_eq_erase_two_add
    {L j : ℕ} (hj : 1 ≤ j) (hjL : j < L) (f : ℕ → ℝ) :
    ∑ e ∈ range L, f e =
      (∑ e ∈ ((range L).erase (j - 1)).erase j, f e) +
        f (j - 1) + f j := by
  have hpred : j - 1 ∈ range L := mem_range.mpr (by omega)
  have hjmem : j ∈ (range L).erase (j - 1) := by
    exact mem_erase.mpr ⟨by omega, mem_range.mpr hjL⟩
  calc
    ∑ e ∈ range L, f e =
        (∑ e ∈ (range L).erase (j - 1), f e) + f (j - 1) :=
      (Finset.sum_erase_add (s := range L) (f := f) hpred).symm
    _ = ((∑ e ∈ ((range L).erase (j - 1)).erase j, f e) + f j) +
        f (j - 1) := by
      rw [(Finset.sum_erase_add (s := (range L).erase (j - 1))
        (f := f) hjmem).symm]
    _ = (∑ e ∈ ((range L).erase (j - 1)).erase j, f e) +
        f (j - 1) + f j := by ring

/-- Pure finite two-coordinate replacement identity. -/
theorem finiteObservablePhase_pair_sub
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {L j : ℕ} (hj : 1 ≤ j) (hjL : j < L)
    (gu gv : ℕ → ℕ)
    (hout : ∀ e, e ≠ j - 1 → e ≠ j → gu e = gv e) :
    finiteObservablePhase B hk r F L gu -
        finiteObservablePhase B hk r F L gv =
      ((pairActionInt B hk (phaseAt hk r (j - 1)) F
          (gu (j - 1)) (gu j) -
        pairActionInt B hk (phaseAt hk r (j - 1)) F
          (gv (j - 1)) (gv j) : ℤ) : ℝ) / (B : ℝ) ^ (j + 1) := by
  let tu : ℕ → ℝ := fun e ↦
    (F (phaseAt hk r e) (gu e) : ℝ) / (B : ℝ) ^ (e + 1)
  let tv : ℕ → ℝ := fun e ↦
    (F (phaseAt hk r e) (gv e) : ℝ) / (B : ℝ) ^ (e + 1)
  have houtSum :
      (∑ e ∈ ((range L).erase (j - 1)).erase j, tu e) =
        ∑ e ∈ ((range L).erase (j - 1)).erase j, tv e := by
    apply sum_congr rfl
    intro e he
    have hej : e ≠ j := (mem_erase.mp he).1
    have hepred : e ≠ j - 1 := (mem_erase.mp (mem_erase.mp he).2).1
    dsimp only [tu, tv]
    rw [hout e hepred hej]
  have hu := sum_eq_erase_two_add hj hjL tu
  have hv := sum_eq_erase_two_add hj hjL tv
  unfold finiteObservablePhase
  change (∑ e ∈ range L, tu e) - (∑ e ∈ range L, tv e) = _
  rw [hu, hv, houtSum]
  have hlabel := cyclicSucc_phaseAt_pred hk r hj
  have hpow : (B : ℝ) ^ (j + 1) = (B : ℝ) ^ j * B := by
    rw [pow_succ]
  dsimp only [tu, tv, pairActionInt]
  rw [show j - 1 + 1 = j by omega, hlabel, hpow]
  push_cast
  field_simp [show (B : ℝ) ≠ 0 by positivity,
    pow_ne_zero j (show (B : ℝ) ≠ 0 by positivity)] <;> ring

private theorem insertedGap_left
    {F : Finset ℕ} {j u : ℕ} (hj : 1 ≤ j)
    (hu : (CoreLinearInsertion.insertionSlot F j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot F j).2) :
    subsetGap (insert u F) (j - 1) =
      u - (CoreLinearInsertion.insertionSlot F j).1 := by
  unfold subsetGap
  rw [show j - 1 + 1 = j by omega,
    CoreLinearInsertion.orderStat_insert_at hj hu,
    CoreLinearInsertion.orderStat_insert_before hu (by omega : j - 1 < j),
    CoreLinearInsertion.insertionSlot_left]

private theorem insertedGap_right
    {F : Finset ℕ} {j u : ℕ} (hj : 1 ≤ j)
    (hu : (CoreLinearInsertion.insertionSlot F j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot F j).2) :
    subsetGap (insert u F) j =
      (CoreLinearInsertion.insertionSlot F j).2 - u := by
  unfold subsetGap
  rw [CoreLinearInsertion.orderStat_insert_at hj hu,
    CoreLinearInsertion.orderStat_insert_after hj hu (Nat.lt_succ_self j),
    Nat.succ_sub_one, CoreLinearInsertion.insertionSlot_right F hj]

private theorem insertedGap_eq_of_ne
    {F : Finset ℕ} {j u v e : ℕ} (hj : 1 ≤ j)
    (hu : (CoreLinearInsertion.insertionSlot F j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot F j).2)
    (hv : (CoreLinearInsertion.insertionSlot F j).1 < v ∧
      v < (CoreLinearInsertion.insertionSlot F j).2)
    (hepred : e ≠ j - 1) (hej : e ≠ j) :
    subsetGap (insert u F) e = subsetGap (insert v F) e := by
  unfold subsetGap
  rw [CoreLinearInsertion.orderStat_insert_eq_of_ne hj hu hv (by omega : e + 1 ≠ j),
    CoreLinearInsertion.orderStat_insert_eq_of_ne hj hu hv hej]

/-- Actual ordered-slot insertion identity for an arbitrary integer gap
observable. -/
theorem finiteObservablePhase_ordered_insert_sub
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (Fobs : Fin k → ℕ → ℤ) {L j : ℕ} (hj : 1 ≤ j) (hjL : j < L)
    (frame : Finset ℕ) {u v : ℕ}
    (hu : (CoreLinearInsertion.insertionSlot frame j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot frame j).2)
    (hv : (CoreLinearInsertion.insertionSlot frame j).1 < v ∧
      v < (CoreLinearInsertion.insertionSlot frame j).2) :
    finiteObservablePhase B hk r Fobs L (fun e ↦ subsetGap (insert u frame) e) -
        finiteObservablePhase B hk r Fobs L (fun e ↦ subsetGap (insert v frame) e) =
      ((pairActionInt B hk (phaseAt hk r (j - 1)) Fobs
          (u - (CoreLinearInsertion.insertionSlot frame j).1)
          ((CoreLinearInsertion.insertionSlot frame j).2 - u) -
        pairActionInt B hk (phaseAt hk r (j - 1)) Fobs
          (v - (CoreLinearInsertion.insertionSlot frame j).1)
          ((CoreLinearInsertion.insertionSlot frame j).2 - v) : ℤ) : ℝ) /
        (B : ℝ) ^ (j + 1) := by
  have hpair := finiteObservablePhase_pair_sub hB hk r Fobs hj hjL
    (fun e ↦ subsetGap (insert u frame) e)
    (fun e ↦ subsetGap (insert v frame) e)
    (fun e hepred hej ↦ insertedGap_eq_of_ne hj hu hv hepred hej)
  rw [insertedGap_left hj hu, insertedGap_right hj hu,
    insertedGap_left hj hv, insertedGap_right hj hv] at hpair
  exact hpair

/-- Actual finite phase on an inserted ordered subset. -/
def actualFiniteObservablePhase
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (Fobs : Fin k → ℕ → ℤ) (L : ℕ) (U : Finset ℕ) : ℝ :=
  finiteObservablePhase B hk r Fobs L (fun e ↦ subsetGap U e)

/-- Outer term fixed by one selected point of the genuine nonempty slot. -/
def selectedObservableOuter
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (Fobs : Fin k → ℕ → ℤ) (L j : ℕ)
    (A frame : Finset ℕ) (hE : (CoreActualCyclicSlot.slot A frame j).Nonempty) : ℝ :=
  let v := CoreActualCyclicSlot.selectedPoint A frame j hE
  actualFiniteObservablePhase B hk r Fobs L (insert v frame) -
    (pairActionInt B hk (phaseAt hk r (j - 1)) Fobs
      (v - (CoreLinearInsertion.insertionSlot frame j).1)
      ((CoreLinearInsertion.insertionSlot frame j).2 - v) : ℝ) /
        (B : ℝ) ^ (j + 1)

private theorem mem_slot_to_insertionSlot
    {A frame : Finset ℕ} {j u : ℕ} (hj : 1 ≤ j)
    (hu : u ∈ CoreActualCyclicSlot.slot A frame j) :
    (CoreLinearInsertion.insertionSlot frame j).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot frame j).2 := by
  have h := (mem_openSlot.mp hu).2
  simpa [CoreActualCyclicSlot.slot, CoreLinearInsertion.insertionSlot,
    Nat.sub_add_cancel hj] using h

/-- Every insertion in the genuine slot has the same outer term and the
displayed adjacent-gap action. -/
theorem actualFiniteObservablePhase_eq_outer_add
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (Fobs : Fin k → ℕ → ℤ) {L j : ℕ} (hj : 1 ≤ j) (hjL : j < L)
    (A frame : Finset ℕ) (hE : (CoreActualCyclicSlot.slot A frame j).Nonempty)
    {u : ℕ} (hu : u ∈ CoreActualCyclicSlot.slot A frame j) :
    actualFiniteObservablePhase B hk r Fobs L (insert u frame) =
      selectedObservableOuter B hk r Fobs L j A frame hE +
        (pairActionInt B hk (phaseAt hk r (j - 1)) Fobs
          (u - (CoreLinearInsertion.insertionSlot frame j).1)
          ((CoreLinearInsertion.insertionSlot frame j).2 - u) : ℝ) /
          (B : ℝ) ^ (j + 1) := by
  have huSlot := mem_slot_to_insertionSlot hj hu
  have hvSlot := mem_slot_to_insertionSlot hj
    (CoreActualCyclicSlot.selectedPoint_mem A frame j hE)
  have hdiff := finiteObservablePhase_ordered_insert_sub hB hk r Fobs hj hjL
    frame huSlot hvSlot
  rw [Int.cast_sub, sub_div] at hdiff
  unfold selectedObservableOuter
  dsimp only [actualFiniteObservablePhase]
  linarith

end
end PrimeGapNormality.Prime.CoreIntegerGapInsertion
