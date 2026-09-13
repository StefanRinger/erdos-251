import PrimeGapNormality.Prime.CoreLinearShapePhase
import Mathlib.Tactic.LinearCombination

/-!
The actual ordered-subset linear phase under insertion of an interior
point. Paper ranks are one-based: insertion at rank `j` changes precisely
the adjacent gaps of weights `B⁻ʲ` and `B⁻⁽ʲ⁺¹⁾`.
-/

namespace PrimeGapNormality.Prime.CoreLinearInsertion

open Finset

noncomputable section

theorem orderStat_eq_phasePoint (E : Finset ℕ) (i : ℕ) :
    orderStat E i = phasePoint (E.sort (· ≤ ·)) i := by
  by_cases hi : i = 0
  · simp [orderStat, phasePoint, hi]
  · by_cases hb : i - 1 < E.card
    · have hl : i - 1 < (E.sort (· ≤ ·)).length := by simpa using hb
      simp [orderStat, phasePoint, hi, hb, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hl]
    · have hl : (E.sort (· ≤ ·)).length ≤ i - 1 := by simpa using Nat.le_of_not_gt hb
      simp [orderStat, phasePoint, hi, hb, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none hl]

theorem orderStat_le_succ (E : Finset ℕ) {i : ℕ} (hi : i < E.card) :
    orderStat E i ≤ orderStat E (i + 1) := by
  cases i with
  | zero => simp [orderStat_zero]
  | succ i =>
    have hi0 : i < E.card := by omega
    rw [orderStat_succ_eq_sort hi0, orderStat_succ_eq_sort hi]
    exact ((Finset.sortedLT_sort E).getElem_le_getElem_iff).mpr (Nat.le_succ i)

/-- The natural gap differences really are the nonnegative consecutive
differences in the sorted list. -/
theorem shapePhase_eq_finiteGapPhase (B L : ℕ) (E : Finset ℕ) (hL : L ≤ E.card) :
    coreLinearShapePhase B L E = finiteGapPhase B L (E.sort (· ≤ ·)) := by
  unfold coreLinearShapePhase finiteGapPhase
  apply Finset.sum_congr rfl
  intro i hi
  have hicard : i < E.card := (Finset.mem_range.mp hi).trans_le hL
  simp only [subsetGap]
  rw [Nat.cast_sub (orderStat_le_succ E hicard)]
  simp only [orderStat_eq_phasePoint]

private theorem sort_firstL (L : ℕ) (E : Finset ℕ) :
    (Stopped.firstL L E).sort (· ≤ ·) = (E.sort (· ≤ ·)).take L := by
  have hnd := (E.sort_nodup (· ≤ ·)).sublist (List.take_sublist L _)
  have hpw : ((E.sort (· ≤ ·)).take L).Pairwise (· ≤ ·) :=
    (Finset.pairwise_sort E (· ≤ ·)).take
  exact (List.toFinset_sort (· ≤ ·) hnd).mpr hpw

/-- Prefix restriction preserves all the actual order statistics used by
the truncated phase, including the endpoint of its last gap. -/
theorem orderStat_firstL (L : ℕ) (E : Finset ℕ) {i : ℕ} (hi : i ≤ L) :
    orderStat (Stopped.firstL L E) i = orderStat E i := by
  rw [orderStat_eq_phasePoint, orderStat_eq_phasePoint, sort_firstL]
  by_cases hz : i = 0
  · simp [phasePoint, hz]
  · have hidx : i - 1 < L := by omega
    simp [phasePoint, hz, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hidx]

theorem shapePhase_firstL (B L : ℕ) (E : Finset ℕ) :
    coreLinearShapePhase B L (Stopped.firstL L E) = coreLinearShapePhase B L E := by
  unfold coreLinearShapePhase
  apply Finset.sum_congr rfl
  intro i hi
  have hiL := Finset.mem_range.mp hi
  simp only [subsetGap, orderStat_firstL L E (by omega : i + 1 ≤ L),
    orderStat_firstL L E (by omega : i ≤ L)]

def insertionSlot (F : Finset ℕ) (j : ℕ) : ℕ × ℕ :=
  deletionSlot (F.sort (· ≤ ·)) (j - 1)

theorem insertionSlot_left (F : Finset ℕ) (j : ℕ) :
    (insertionSlot F j).1 = orderStat F (j - 1) := by
  rw [orderStat_eq_phasePoint]
  rfl

theorem insertionSlot_right (F : Finset ℕ) {j : ℕ} (hj : 1 ≤ j) :
    (insertionSlot F j).2 = orderStat F j := by
  rw [orderStat_eq_phasePoint]
  simp [insertionSlot, deletionSlot, phasePoint, show j ≠ 0 by omega]

theorem notMem_of_mem_slot {F : Finset ℕ} {j u : ℕ}
    (hu : (insertionSlot F j).1 < u ∧ u < (insertionSlot F j).2) : u ∉ F := by
  have h := not_mem_toFinset_of_mem_deletionSlot (Finset.sortedLT_sort F).pairwise hu
  simpa only [Finset.sort_toFinset] using h

/-- Actual set insertion has exactly the sorted list obtained by insertion
at rank `j-1`; this is proved from the strict slot inequalities. -/
theorem sort_insert_of_mem_slot {F : Finset ℕ} {j u : ℕ}
    (hu : (insertionSlot F j).1 < u ∧ u < (insertionSlot F j).2) :
    (insert u F).sort (· ≤ ·) = insertAt (F.sort (· ≤ ·)) (j - 1) u := by
  have hlen : j - 1 < (F.sort (· ≤ ·)).length := lt_length_of_mem_deletionSlot hu.2
  have hpw := insertAt_pairwise_of_mem_slot (Finset.sortedLT_sort F).pairwise hu
  have hsort := (List.toFinset_sort (· ≤ ·) hpw.sortedLT.nodup).mpr
    (hpw.imp fun h ↦ Nat.le_of_lt h)
  rw [insertAt_toFinset hlen.le, Finset.sort_toFinset] at hsort
  exact hsort

theorem orderStat_insert_before {F : Finset ℕ} {j u q : ℕ}
    (hu : (insertionSlot F j).1 < u ∧ u < (insertionSlot F j).2) (hq : q < j) :
    orderStat (insert u F) q = orderStat F q := by
  rw [orderStat_eq_phasePoint, sort_insert_of_mem_slot hu,
    phasePoint_insertAt_of_le (by omega : q ≤ j - 1)]
  exact (orderStat_eq_phasePoint F q).symm

theorem orderStat_insert_at {F : Finset ℕ} {j u : ℕ} (hj : 1 ≤ j)
    (hu : (insertionSlot F j).1 < u ∧ u < (insertionSlot F j).2) :
    orderStat (insert u F) j = u := by
  have hlen : j - 1 ≤ (F.sort (· ≤ ·)).length :=
    (lt_length_of_mem_deletionSlot hu.2).le
  rw [orderStat_eq_phasePoint, sort_insert_of_mem_slot hu]
  have h := phasePoint_insertAt_succ (F := F.sort (· ≤ ·)) (u := u) hlen
  simpa [Nat.sub_add_cancel hj] using h

theorem orderStat_insert_after {F : Finset ℕ} {j u q : ℕ} (hj : 1 ≤ j)
    (hu : (insertionSlot F j).1 < u ∧ u < (insertionSlot F j).2) (hq : j < q) :
    orderStat (insert u F) q = orderStat F (q - 1) := by
  rw [orderStat_eq_phasePoint, sort_insert_of_mem_slot hu,
    phasePoint_insertAt_of_gt (by omega : j - 1 + 1 < q), orderStat_eq_phasePoint]
  simp [phasePoint, show q - 1 ≠ 0 by omega, Nat.sub_sub]

/-- Every other rank is unchanged when the point moves within its slot,
even for ranks beyond the truncation parameter `L`. -/
theorem orderStat_insert_eq_of_ne {F : Finset ℕ} {j u v q : ℕ} (hj : 1 ≤ j)
    (hu : (insertionSlot F j).1 < u ∧ u < (insertionSlot F j).2)
    (hv : (insertionSlot F j).1 < v ∧ v < (insertionSlot F j).2) (hq : q ≠ j) :
    orderStat (insert u F) q = orderStat (insert v F) q := by
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · rw [orderStat_insert_before hu hlt, orderStat_insert_before hv hlt]
  · rw [orderStat_insert_after hj hu hgt, orderStat_insert_after hj hv hgt]

def coefficient (B j : ℕ) : ℝ := ((B : ℝ) - 1) / (B : ℝ) ^ (j + 1)

/-- The proved list calculation transported to the actual ordered subsets. -/
theorem shapePhase_insert_sub {B L j : ℕ} (hB : 2 ≤ B) (hj : 1 ≤ j) (hjL : j < L)
    (F : Finset ℕ) (hFL : L ≤ F.card + 1) {u v : ℕ}
    (hu : (insertionSlot F j).1 < u ∧ u < (insertionSlot F j).2)
    (hv : (insertionSlot F j).1 < v ∧ v < (insertionSlot F j).2) :
    coreLinearShapePhase B L (insert u F) - coreLinearShapePhase B L (insert v F) =
      coefficient B j * ((u : ℝ) - v) := by
  have hLu : L ≤ (insert u F).card := by rwa [Finset.card_insert_of_notMem (notMem_of_mem_slot hu)]
  have hLv : L ≤ (insert v F).card := by rwa [Finset.card_insert_of_notMem (notMem_of_mem_slot hv)]
  rw [shapePhase_eq_finiteGapPhase B L _ hLu, shapePhase_eq_finiteGapPhase B L _ hLv,
    sort_insert_of_mem_slot hu, sort_insert_of_mem_slot hv]
  have hL : 2 ≤ L := by omega
  have hidx : j - 1 + 1 < L := by omega
  have hlen : L - 1 ≤ (F.sort (· ≤ ·)).length := by simp only [Finset.length_sort]; omega
  have h := phase_linear_in_deleted hB hL hidx (F.sort (· ≤ ·)) u v hlen
  have hpow : j - 1 + 2 = j + 1 := by omega
  simpa only [coefficient, hpow, div_mul_eq_mul_div] using h

/-- A reference determined solely by the frame. If the slot is empty the
value is harmless; every nonempty integer slot contains its point `a+1`. -/
def outerPhase (B L j : ℕ) (F : Finset ℕ) : ℝ :=
  coreLinearShapePhase B L (insert ((insertionSlot F j).1 + 1) F) - coefficient B j

theorem shapePhase_insert_affine {B L j : ℕ} (hB : 2 ≤ B) (hj : 1 ≤ j) (hjL : j < L)
    (F : Finset ℕ) (hFL : L ≤ F.card + 1) {u : ℕ}
    (hu : (insertionSlot F j).1 < u ∧ u < (insertionSlot F j).2) :
    coreLinearShapePhase B L (insert u F) = outerPhase B L j F +
      coefficient B j * ((u : ℝ) - (insertionSlot F j).1) := by
  have hv : (insertionSlot F j).1 < (insertionSlot F j).1 + 1 ∧
      (insertionSlot F j).1 + 1 < (insertionSlot F j).2 := by omega
  have hd := shapePhase_insert_sub hB hj hjL F hFL hu hv
  simp only [Nat.cast_add, Nat.cast_one] at hd
  unfold outerPhase
  linear_combination hd

theorem shapePhase_insert_scaled {B L j : ℕ} (hB : 2 ≤ B) (hj : 1 ≤ j) (hjL : j < L)
    (F : Finset ℕ) (hFL : L ≤ F.card + 1) {u : ℕ} {G : ℝ} (hG : 0 < G)
    (hu : (insertionSlot F j).1 < u ∧ u < (insertionSlot F j).2) :
    coreLinearShapePhase B L (insert u F) = outerPhase B L j F +
      (G * ((B : ℝ) - 1) / (B : ℝ) ^ (j + 1)) *
        (((u : ℝ) - (insertionSlot F j).1) / G) := by
  rw [shapePhase_insert_affine hB hj hjL F hFL hu]
  congr 1
  unfold coefficient
  have hB0 : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hG.ne', hB0] <;> ring

end

end PrimeGapNormality.Prime.CoreLinearInsertion
