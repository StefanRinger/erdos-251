import PrimeGapNormality.Prime.Coupling
import PrimeGapNormality.Prime.RankDelete
import PrimeGapNormality.Prime.SlotResample
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exceptional deletion slots: empty, short, or boundary

Paper (eq:slots): a remaining frame after deleting rank `j` is
exceptional when the open interval `W_F = (a,c)` is empty, occupancy
is at most `H`, the geometric length `c-a` is at most `H`, or the
deleted rank sits at the window boundary (left neighbour is the root
`0`, or the right neighbour is missing).

Finite Bernoulli identities only. The common preimage mass of
`insertAt F j u` is the RankDelete frame weight
`ρ^{|F|+1}(1-ρ)^{|A|-|F|-1}`. Summing the occupancy-capped weights
over `(L-1)`-frames yields the compiling bound
`O(L H / (|A|-L+1))`, and the first-window Markov bound `ρ H`
(calibrated to `L H / S` when `ρ S ≤ L`).

Lean ranks are 0-based. Root `0` is not an element of `A`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:slots),
subsection "Span, ranks and the two slot exceptions";
`RankDelete.deletionSlot`, `insertAt`, `frame_bernoulli_weight_const`;
`SlotResample.openSlot`, `frameBernoulliWeight`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ### Slot geometry -/

/-- Integer length `c - a` of `W_F = (a,c)`. Zero when `c ≤ a`. -/
def deletionSlotNatLength (F : List ℕ) (j : ℕ) : ℕ :=
  (deletionSlot F j).2 - (deletionSlot F j).1

/-- Occupancy of `A ∩ (a,c)` is at most `H` (includes the empty slot). -/
def IsShortOpenSlot (A : Finset ℕ) (F : List ℕ) (j H : ℕ) : Prop :=
  (openSlot A F j).card ≤ H

/-- Deleted rank at the window boundary: left neighbour is the root, or
the right neighbour is missing (`getD` default `0`). -/
def IsBoundaryDeletionRank (F : List ℕ) (j : ℕ) : Prop :=
  j = 0 ∨ F.length ≤ j

instance instDecidableIsBoundaryDeletionRank (F : List ℕ) (j : ℕ) :
    Decidable (IsBoundaryDeletionRank F j) := by
  dsimp [IsBoundaryDeletionRank]
  infer_instance

instance instDecidableIsShortOpenSlot (A : Finset ℕ) (F : List ℕ)
    (j H : ℕ) : Decidable (IsShortOpenSlot A F j H) := by
  dsimp [IsShortOpenSlot]
  infer_instance

/-- Remaining frame after deleting the rank-`j` order statistic. -/
def remainingFrame (B : Finset ℕ) (j : ℕ) : List ℕ :=
  (B.sort (· ≤ ·)).eraseIdx j

/-- Unnormalised Bernoulli mass of the open-slot preimages of `F`. -/
noncomputable def deletionPreimageMass (A : Finset ℕ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (F : List ℕ) (j : ℕ) : ℝ :=
  ∑ u ∈ openSlot A F j,
    bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset

/-- Bernoulli mass of configurations that hit `{1,…,H}`. Left-boundary
Markov input for (eq:slots). -/
noncomputable def firstWindowHitMass (A : Finset ℕ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (H : ℕ) : ℝ :=
  ∑ B ∈ A.powerset.filter (fun B => (B ∩ Icc 1 H).Nonempty),
    bernoulliThin A ρ hρ0 hρ1 B

/-- Occupancy-capped frame-weight sum over a family of remaining
`(L-1)`-sets, using the sorted list to read `deletionSlot`. -/
noncomputable def cappedOpenSlotFrameMass (A : Finset ℕ) (ρ : ℝ)
    (j H : ℕ) (frames : Finset (Finset ℕ)) : ℝ :=
  ∑ F ∈ frames,
    (min H (openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
      frameBernoulliWeight A ρ F

/-- Actual short-occupancy preimage mass of `(L-1)`-frames. -/
noncomputable def shortOpenSlotFrameMass (A : Finset ℕ) (ρ : ℝ)
    (j H : ℕ) (frames : Finset (Finset ℕ)) : ℝ :=
  ∑ F ∈ frames.filter (fun F =>
      (openSlot A (F.sort (· ≤ ·)) j).card ≤ H),
    ((openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
      frameBernoulliWeight A ρ F

/-! ### Empty and boundary geometry -/

theorem deletionSlot_right_eq_zero_of_not_lt {F : List ℕ} {j : ℕ}
    (hj : ¬ j < F.length) : (deletionSlot F j).2 = 0 := by
  have hnone : F[j]? = none := getElem?_neg F j hj
  unfold deletionSlot
  simp [List.getD_eq_getElem?_getD, hnone]

theorem openSlot_eq_empty_of_not_lt_length (A : Finset ℕ) {F : List ℕ}
    {j : ℕ} (hj : ¬ j < F.length) : openSlot A F j = ∅ := by
  ext u
  simp only [openSlot, mem_filter, notMem_empty, iff_false]
  intro h
  have hright : (deletionSlot F j).2 = 0 :=
    deletionSlot_right_eq_zero_of_not_lt hj
  exact Nat.not_lt_zero u (by simpa [hright] using h.2.2)

theorem IsBoundaryDeletionRank.left_zero (F : List ℕ) :
    (deletionSlot F 0).1 = 0 :=
  deletionSlot_left_zero F

theorem IsBoundaryDeletionRank.of_zero (F : List ℕ) :
    IsBoundaryDeletionRank F 0 :=
  Or.inl rfl

theorem IsBoundaryDeletionRank.of_length_le {F : List ℕ} {j : ℕ}
    (hj : F.length ≤ j) : IsBoundaryDeletionRank F j :=
  Or.inr hj

theorem openSlot_eq_empty_of_boundary_right (A : Finset ℕ) {F : List ℕ}
    {j : ℕ} (hj : F.length ≤ j) : openSlot A F j = ∅ :=
  openSlot_eq_empty_of_not_lt_length A (Nat.not_lt.mpr hj)

private theorem deletionIoo_eq_Ico (a c : ℕ) :
    Ioo a c = Ico (a + 1) c := by
  ext x
  simp only [mem_Ioo, mem_Ico]
  constructor
  · intro h
    exact ⟨Nat.succ_le_of_lt h.1, h.2⟩
  · intro h
    exact ⟨Nat.lt_of_succ_le h.1, h.2⟩

theorem openSlot_subset_deletionIoo (A : Finset ℕ) (F : List ℕ) (j : ℕ) :
    openSlot A F j ⊆ Ioo (deletionSlot F j).1 (deletionSlot F j).2 := by
  intro u hu
  exact mem_Ioo.mpr (mem_filter.mp hu).2

theorem openSlot_card_le_natLength (A : Finset ℕ) (F : List ℕ) (j : ℕ) :
    (openSlot A F j).card ≤ deletionSlotNatLength F j := by
  set a := (deletionSlot F j).1
  set c := (deletionSlot F j).2
  have hs : openSlot A F j ⊆ Ioo a c := openSlot_subset_deletionIoo A F j
  have hcard := card_le_card hs
  refine hcard.trans ?_
  unfold deletionSlotNatLength
  by_cases hlt : a < c
  · rw [deletionIoo_eq_Ico, Nat.card_Ico]
    omega
  · have hempty : Ioo a c = ∅ := by
      ext x
      simp only [mem_Ioo, notMem_empty, iff_false]
      intro h
      exact hlt (Nat.lt_trans h.1 h.2)
    simp [hempty]

theorem IsShortOpenSlot.of_natLength {A : Finset ℕ} {F : List ℕ}
    {j H : ℕ} (h : deletionSlotNatLength F j ≤ H) :
    IsShortOpenSlot A F j H :=
  (openSlot_card_le_natLength A F j).trans h

theorem IsShortOpenSlot.empty {A : Finset ℕ} {F : List ℕ} {j H : ℕ}
    (h : openSlot A F j = ∅) : IsShortOpenSlot A F j H := by
  simp [IsShortOpenSlot, h]

theorem openSlot_eq_empty_of_natLength_zero {A : Finset ℕ} {F : List ℕ}
    {j : ℕ} (h : deletionSlotNatLength F j = 0) :
    openSlot A F j = ∅ := by
  have hle := openSlot_card_le_natLength A F j
  have hz : (openSlot A F j).card = 0 := by omega
  exact card_eq_zero.mp hz

/-! ### Remaining frames of a configuration -/

theorem sort_pairwise_lt (B : Finset ℕ) :
    (B.sort (· ≤ ·)).Pairwise (· < ·) :=
  (sortedLT_sort B).pairwise

theorem remainingFrame_length {B : Finset ℕ} {j : ℕ} (hj : j < B.card) :
    (remainingFrame B j).length = B.card - 1 := by
  unfold remainingFrame
  have hlen : (B.sort (· ≤ ·)).length = B.card := length_sort _
  rw [List.length_eraseIdx_of_lt (by omega), hlen]

theorem remainingFrame_pairwise (B : Finset ℕ) (j : ℕ) :
    (remainingFrame B j).Pairwise (· < ·) :=
  List.Pairwise.sublist (List.eraseIdx_sublist _ _) (sort_pairwise_lt B)

theorem insertAt_remainingFrame {B : Finset ℕ} {j : ℕ} (hj : j < B.card) :
    insertAt (remainingFrame B j) j
        ((B.sort (· ≤ ·))[j]'(by simpa [length_sort] using hj)) =
      B.sort (· ≤ ·) := by
  unfold insertAt remainingFrame
  exact List.insertIdx_eraseIdx_getElem (by simpa [length_sort] using hj)

theorem mem_openSlot_of_remainingFrame {A B : Finset ℕ} {j : ℕ}
    (hBA : B ⊆ A) (hpos : ∀ x ∈ A, 0 < x) (hj : j + 1 < B.card) :
    (B.sort (· ≤ ·))[j]'(by simpa [length_sort] using Nat.lt_of_succ_lt hj) ∈
      openSlot A (remainingFrame B j) j := by
  have hjB : j < B.card := Nat.lt_of_succ_lt hj
  have hlenj : j < (B.sort (· ≤ ·)).length := by simpa [length_sort] using hjB
  have huB : (B.sort (· ≤ ·))[j]'hlenj ∈ B :=
    (mem_sort (· ≤ ·)).mp (List.getElem_mem hlenj)
  have huA : (B.sort (· ≤ ·))[j]'hlenj ∈ A := hBA huB
  have hP : (insertAt (remainingFrame B j) j
      ((B.sort (· ≤ ·))[j]'hlenj)).Pairwise (· < ·) := by
    rw [insertAt_remainingFrame hjB]
    exact sort_pairwise_lt B
  have hjF : j < (remainingFrame B j).length := by
    rw [remainingFrame_length hjB]
    omega
  have hslot := deletion_preimage hjF hP (Or.inl (hpos _ huA))
  exact mem_filter.mpr ⟨huA, hslot⟩

/-! ### Fixed-frame Bernoulli preimage masses -/

theorem frameBernoulliWeight_nonneg {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (F : Finset ℕ) :
    0 ≤ frameBernoulliWeight A ρ F :=
  mul_nonneg (pow_nonneg hρ0 _) (pow_nonneg (sub_nonneg.mpr hρ1) _)

private theorem insertAt_mem_iff {F : List ℕ} {j u x : ℕ}
    (hj : j ≤ F.length) : x ∈ insertAt F j u ↔ x = u ∨ x ∈ F :=
  mem_insertAt hj

private theorem insertAt_toFinset_eq {F : List ℕ} {j u : ℕ}
    (hj : j ≤ F.length) :
    (insertAt F j u).toFinset = insert u F.toFinset :=
  insertAt_toFinset hj

/-- Open-slot point is not a surviving frame site. After
`mem_iff_getElem` the deleted value is `F[i]`, never a free `u`. -/
private theorem mem_openSlot_not_mem_toFinset {F : List ℕ} {j u : ℕ}
    (hF : F.Pairwise (· < ·))
    (hu : (deletionSlot F j).1 < u ∧ u < (deletionSlot F j).2) :
    u ∉ F.toFinset :=
  not_mem_toFinset_of_mem_deletionSlot hF hu

/-- Direct RankDelete unfolding: one preimage has the paper frame
weight, independent of the slot point. -/
theorem insertAt_eq_frame_bernoulli_weight_const {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {F : List ℕ} {j u : ℕ}
    (hF : F.Pairwise (· < ·)) (hFA : F.toFinset ⊆ A)
    (hu : u ∈ openSlot A F j) :
    bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset =
      ρ ^ (F.toFinset.card + 1) *
        (1 - ρ) ^ (A.card - F.toFinset.card - 1) := by
  have huA : u ∈ A := (mem_filter.mp hu).1
  have hus : (deletionSlot F j).1 < u ∧ u < (deletionSlot F j).2 :=
    (mem_filter.mp hu).2
  have hj : j < F.length := lt_length_of_mem_deletionSlot hus.2
  have hjle : j ≤ F.length := Nat.le_of_lt hj
  have huF : u ∉ F.toFinset := mem_openSlot_not_mem_toFinset hF hus
  have hB : (insertAt F j u).toFinset ⊆ A := by
    rw [insertAt_toFinset_eq hjle]
    exact insert_subset huA hFA
  have huin : u ∈ (insertAt F j u).toFinset := by
    rw [insertAt_toFinset_eq hjle]
    exact mem_insert_self u _
  have herase : (insertAt F j u).toFinset.erase u = F.toFinset := by
    rw [insertAt_toFinset_eq hjle, erase_insert huF]
  exact frame_bernoulli_weight_const hρ0 hρ1 hB huin herase

theorem deletionPreimageMass_eq {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {F : List ℕ} {j : ℕ} (hF : F.Pairwise (· < ·))
    (hFA : F.toFinset ⊆ A) :
    deletionPreimageMass A ρ hρ0 hρ1 F j =
      (openSlot A F j).card * frameBernoulliWeight A ρ F.toFinset := by
  unfold deletionPreimageMass
  have hterm : ∀ u ∈ openSlot A F j,
      bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset =
        frameBernoulliWeight A ρ F.toFinset := fun u hu => by
    simpa [frameBernoulliWeight] using
      insertAt_eq_frame_bernoulli_weight_const hρ0 hρ1 hF hFA hu
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]

/-- Empty open slot: no rank-`j` preimage, mass `0`. -/
theorem deletionPreimageMass_empty (A : Finset ℕ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (F : List ℕ) (j : ℕ) (h : openSlot A F j = ∅) :
    deletionPreimageMass A ρ hρ0 hρ1 F j = 0 := by
  simp [deletionPreimageMass, h]

theorem deletionPreimageMass_empty_of_boundary_right (A : Finset ℕ)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {F : List ℕ} {j : ℕ}
    (hj : F.length ≤ j) :
    deletionPreimageMass A ρ hρ0 hρ1 F j = 0 :=
  deletionPreimageMass_empty A hρ0 hρ1 F j
    (openSlot_eq_empty_of_boundary_right A hj)

/-- Occupancy `≤ H`: preimage mass `≤ H` times the RankDelete frame
weight. Uses `insertAt` constancy (6.2). -/
theorem deletionPreimageMass_le_of_short {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {F : List ℕ} {j H : ℕ}
    (hF : F.Pairwise (· < ·)) (hFA : F.toFinset ⊆ A)
    (hH : IsShortOpenSlot A F j H) :
    deletionPreimageMass A ρ hρ0 hρ1 F j ≤
      (H : ℝ) * frameBernoulliWeight A ρ F.toFinset := by
  have heq := deletionPreimageMass_eq (j := j) hρ0 hρ1 hF hFA
  have hw : 0 ≤ frameBernoulliWeight A ρ F.toFinset :=
    frameBernoulliWeight_nonneg hρ0.le hρ1.le F.toFinset
  have hc : ((openSlot A F j).card : ℝ) ≤ (H : ℝ) := Nat.cast_le.mpr hH
  have hmul := mul_le_mul_of_nonneg_right hc hw
  rw [heq]
  exact hmul

theorem deletionPreimageMass_le_of_natLength {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {F : List ℕ} {j H : ℕ}
    (hF : F.Pairwise (· < ·)) (hFA : F.toFinset ⊆ A)
    (hH : deletionSlotNatLength F j ≤ H) :
    deletionPreimageMass A ρ hρ0 hρ1 F j ≤
      (H : ℝ) * frameBernoulliWeight A ρ F.toFinset :=
  deletionPreimageMass_le_of_short hρ0 hρ1 hF hFA
    (IsShortOpenSlot.of_natLength hH)

/-! ### First-window Markov (left boundary, paper `P(x_1 ≤ H)`) -/

theorem card_inter_Icc_one_le (A : Finset ℕ) (H : ℕ) :
    (A ∩ Icc 1 H).card ≤ H := by
  have hsub : A ∩ Icc 1 H ⊆ Icc 1 H := inter_subset_right
  refine (card_le_card hsub).trans ?_
  by_cases h : 1 ≤ H
  · rw [Nat.card_Icc]
    omega
  · have hempty : Icc 1 H = ∅ := by
      ext x
      simp only [mem_Icc, notMem_empty, iff_false]
      intro hx
      exact h (Nat.le_trans hx.1 hx.2)
    simp [hempty]

theorem bernoulliThin_avoid_window_mass (A W : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hWA : W ⊆ A) :
    ∑ B ∈ A.powerset.filter (fun B => Disjoint B W),
        bernoulliThin A ρ hρ0 hρ1 B =
      (1 - ρ) ^ W.card := by
  have hfilter :
      A.powerset.filter (fun B => Disjoint B W) = (A \ W).powerset := by
    ext B
    simp only [mem_filter, mem_powerset]
    constructor
    · intro h
      intro x hx
      exact mem_sdiff.mpr ⟨h.1 hx, disjoint_left.mp h.2 hx⟩
    · intro hB
      refine ⟨hB.trans sdiff_subset,
        Disjoint.mono_left hB (sdiff_disjoint (s := W) (t := A))⟩
  rw [hfilter]
  have hA : A.card = (A \ W).card + W.card :=
    (card_sdiff_add_card_eq_card hWA).symm
  have hpt : ∀ C ∈ (A \ W).powerset,
      bernoulliThin A ρ hρ0 hρ1 C =
        (1 - ρ) ^ W.card * bernoulliThin (A \ W) ρ hρ0 hρ1 C := by
    intro C hC
    have hCAW : C ⊆ A \ W := mem_powerset.mp hC
    have hCA : C ⊆ A := hCAW.trans sdiff_subset
    have hCle : C.card ≤ (A \ W).card := card_le_card hCAW
    have hcard : A.card - C.card = (A \ W).card - C.card + W.card := by
      omega
    rw [bernoulliThin_eq A hρ0 hρ1 hCA,
      bernoulliThin_eq (A \ W) hρ0 hρ1 hCAW, hcard, pow_add]
    ring
  rw [sum_congr rfl hpt, ← mul_sum, bernoulliThin_sum (A \ W) hρ0 hρ1,
    mul_one]

theorem bernoulliThin_hit_window_mass (A W : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hWA : W ⊆ A) :
    ∑ B ∈ A.powerset.filter (fun B => (B ∩ W).Nonempty),
        bernoulliThin A ρ hρ0 hρ1 B =
      1 - (1 - ρ) ^ W.card := by
  have htot := bernoulliThin_sum A hρ0 hρ1
  have havoid := bernoulliThin_avoid_window_mass A W hρ0 hρ1 hWA
  have hsplit :=
    sum_filter_add_sum_filter_not (s := A.powerset)
      (p := fun B => Disjoint B W)
      (f := fun B => bernoulliThin A ρ hρ0 hρ1 B)
  have hne :
      A.powerset.filter (fun B => ¬ Disjoint B W) =
        A.powerset.filter (fun B => (B ∩ W).Nonempty) := by
    ext B
    simp only [mem_filter, disjoint_iff_inter_eq_empty, and_congr_right_iff]
    intro _
    exact nonempty_iff_ne_empty.symm
  have hsum :
      ∑ B ∈ A.powerset.filter (fun B => Disjoint B W),
            bernoulliThin A ρ hρ0 hρ1 B +
          ∑ B ∈ A.powerset.filter (fun B => (B ∩ W).Nonempty),
            bernoulliThin A ρ hρ0 hρ1 B =
        1 := by
    rw [← hne, hsplit, htot]
  linarith [hsum, havoid]

theorem firstWindowHitMass_eq (A : Finset ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (H : ℕ) :
    firstWindowHitMass A ρ hρ0 hρ1 H =
      1 - (1 - ρ) ^ (A ∩ Icc 1 H).card := by
  unfold firstWindowHitMass
  set W := A ∩ Icc 1 H
  have hWA : W ⊆ A := inter_subset_left
  have hfilter :
      A.powerset.filter (fun B => (B ∩ Icc 1 H).Nonempty) =
        A.powerset.filter (fun B => (B ∩ W).Nonempty) := by
    ext B
    simp only [mem_filter, mem_powerset, and_congr_right_iff]
    intro hBA
    have hEQ : B ∩ Icc 1 H = B ∩ W := by
      ext x
      simp only [mem_inter, W]
      constructor
      · intro hx
        exact ⟨hx.1, hBA hx.1, hx.2⟩
      · intro hx
        exact ⟨hx.1, hx.2.2⟩
    rw [hEQ]
  rw [hfilter, bernoulliThin_hit_window_mass A W hρ0 hρ1 hWA]

theorem firstWindowHitMass_le (A : Finset ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (H : ℕ) :
    firstWindowHitMass A ρ hρ0 hρ1 H ≤
      ((A ∩ Icc 1 H).card : ℝ) * ρ := by
  rw [firstWindowHitMass_eq A hρ0 hρ1 H]
  simpa [mul_comm] using one_sub_pow_le hρ0 hρ1 (A ∩ Icc 1 H).card

/-- Compiling left-boundary bound: mass of frames whose first survivor
lies in `{1,…,H}` is at most `ρ H`. -/
theorem firstWindowHitMass_le_rho_H (A : Finset ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (H : ℕ) :
    firstWindowHitMass A ρ hρ0 hρ1 H ≤ (H : ℝ) * ρ := by
  have h := firstWindowHitMass_le A hρ0 hρ1 H
  have hc : ((A ∩ Icc 1 H).card : ℝ) ≤ (H : ℝ) :=
    Nat.cast_le.mpr (card_inter_Icc_one_le A H)
  have hρ : 0 ≤ ρ := hρ0
  have hmul : ((A ∩ Icc 1 H).card : ℝ) * ρ ≤ (H : ℝ) * ρ :=
    mul_le_mul_of_nonneg_right hc hρ
  exact h.trans hmul

/-- Calibrated form of the first-window bound: if `ρ S ≤ L` then the
mass is `≤ L H / S`. Paper `ξ` with `H ≍ ξ G` and `S ≍ L G`. -/
theorem firstWindowHitMass_le_LH_div_S {A : Finset ℕ} {ρ : ℝ}
    {L H S : ℕ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hS : 0 < S)
    (hρL : ρ * S ≤ L) :
    firstWindowHitMass A ρ hρ0 hρ1 H ≤ (L : ℝ) * H / S := by
  have h1 := firstWindowHitMass_le_rho_H A hρ0 hρ1 H
  have hS0 : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hSne : (S : ℝ) ≠ 0 := hS0.ne'
  have hρle : ρ ≤ (L : ℝ) / S := (le_div_iff₀ hS0).mpr hρL
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have h2 : (H : ℝ) * ρ ≤ (H : ℝ) * ((L : ℝ) / S) :=
    mul_le_mul_of_nonneg_left hρle hH
  have h3 : (H : ℝ) * ((L : ℝ) / S) = (L : ℝ) * H / S := by
    rw [← mul_div_assoc, mul_comm (H : ℝ)]
  have h12 : firstWindowHitMass A ρ hρ0 hρ1 H ≤ (H : ℝ) * ρ := by
    simpa [mul_comm] using h1
  exact h12.trans (h2.trans_eq h3)

theorem firstWindowHitMass_union_ranks_le {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (L H : ℕ) :
    (L : ℝ) * firstWindowHitMass A ρ hρ0 hρ1 H ≤
      (L : ℝ) * H * ρ := by
  have h := firstWindowHitMass_le_rho_H A hρ0 hρ1 H
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left h hL
  have hrw : (L : ℝ) * ((H : ℝ) * ρ) = (L : ℝ) * H * ρ := by ring
  exact hmul.trans_eq hrw

/-- A geometrically short left-boundary slot forces a hit in
`{1,…,H}`. -/
theorem remainingFrame_left_short_hit {A B : Finset ℕ} {H : ℕ}
    (hBA : B ⊆ A) (hpos : ∀ x ∈ A, 0 < x) (h2 : 2 ≤ B.card)
    (hshort : deletionSlotNatLength (remainingFrame B 0) 0 ≤ H) :
    (B ∩ Icc 1 H).Nonempty := by
  have hlen : (B.sort (· ≤ ·)).length = B.card := length_sort _
  have hx0 : 0 < (B.sort (· ≤ ·)).length := by omega
  have hx1 : 1 < (B.sort (· ≤ ·)).length := by omega
  have hjF : 0 < (remainingFrame B 0).length := by
    rw [remainingFrame_length (show 0 < B.card by omega)]
    omega
  have hget : (remainingFrame B 0)[0]'(by omega) =
      (B.sort (· ≤ ·))[1]' hx1 := by
    simp [remainingFrame, List.eraseIdx_zero, List.getElem_tail]
  have hright : (deletionSlot (remainingFrame B 0) 0).2 =
      (B.sort (· ≤ ·))[1]' hx1 := by
    rw [deletionSlot_right_eq hjF, hget]
  have hnat : deletionSlotNatLength (remainingFrame B 0) 0 =
      (B.sort (· ≤ ·))[1]' hx1 := by
    unfold deletionSlotNatLength
    rw [deletionSlot_left_zero, hright, Nat.sub_zero]
  have hsec : (B.sort (· ≤ ·))[1]' hx1 ≤ H := by omega
  have hfirst_lt :
      (B.sort (· ≤ ·))[0]' hx0 < (B.sort (· ≤ ·))[1]' hx1 :=
    (List.pairwise_iff_getElem.mp (sort_pairwise_lt B)) 0 1 hx0 hx1
      (by decide : (0 : ℕ) < 1)
  have hxB : (B.sort (· ≤ ·))[0]' hx0 ∈ B :=
    (mem_sort (· ≤ ·)).mp (List.getElem_mem hx0)
  have hxA : (B.sort (· ≤ ·))[0]' hx0 ∈ A := hBA hxB
  have hpos0 : 0 < (B.sort (· ≤ ·))[0]' hx0 := hpos _ hxA
  have hleH : (B.sort (· ≤ ·))[0]' hx0 ≤ H :=
    Nat.le_trans (Nat.le_of_lt hfirst_lt) hsec
  have hIcc : (B.sort (· ≤ ·))[0]' hx0 ∈ Icc 1 H :=
    mem_Icc.mpr ⟨Nat.succ_le_of_lt hpos0, hleH⟩
  exact ⟨_, mem_inter.mpr ⟨hxB, hIcc⟩⟩

/-! ### `(L-1)`-frame weight sums: `O(L H / S)` -/

theorem sum_frameBernoulliWeight_powersetCard (A : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {m : ℕ} (hm : m + 1 ≤ A.card) :
    ∑ F ∈ A.powersetCard m, frameBernoulliWeight A ρ F =
      (A.card.choose m : ℝ) * ρ ^ (m + 1) *
        (1 - ρ) ^ (A.card - m - 1) := by
  have hpt : ∀ F ∈ A.powersetCard m,
      frameBernoulliWeight A ρ F =
        ρ ^ (m + 1) * (1 - ρ) ^ (A.card - m - 1) := by
    intro F hF
    have hcard : F.card = m := (mem_powersetCard.mp hF).2
    simp [frameBernoulliWeight, hcard]
  rw [sum_congr rfl hpt, sum_const, nsmul_eq_mul, card_powersetCard]
  ring

theorem choose_pred_mul {S L : ℕ} (hL : 1 ≤ L) (hLS : L ≤ S) :
    (S.choose L : ℕ) * L = S.choose (L - 1) * (S - L + 1) := by
  have h := Nat.choose_succ_right_eq S (L - 1)
  have hk : L - 1 + 1 = L := Nat.sub_add_cancel hL
  have hn : S - (L - 1) = S - L + 1 := by omega
  rw [hk, hn] at h
  exact h

theorem choose_pred_cast {S L : ℕ} (hL : 1 ≤ L) (hLS : L ≤ S) :
    (S.choose (L - 1) : ℝ) =
      (L : ℝ) / ((S : ℝ) - L + 1) * S.choose L := by
  have hdenN : 0 < S - L + 1 := by omega
  have hcast : ((S - L + 1 : ℕ) : ℝ) = (S : ℝ) - (L : ℝ) + 1 := by
    rw [Nat.cast_add_one, Nat.cast_sub hLS]
  have hden : (S : ℝ) - (L : ℝ) + 1 ≠ 0 := by
    rw [← hcast]
    exact Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hdenN)
  have hnat := choose_pred_mul hL hLS
  have hR :
      (S.choose L : ℝ) * (L : ℝ) =
        (S.choose (L - 1) : ℝ) * ((S : ℝ) - (L : ℝ) + 1) := by
    have hnatR := congrArg (fun n : ℕ => (n : ℝ)) hnat
    simp only [Nat.cast_mul] at hnatR
    rw [hcast] at hnatR
    exact hnatR
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).mpr
  calc
    (S.choose (L - 1) : ℝ) * ((S : ℝ) - (L : ℝ) + 1) =
        (S.choose L : ℝ) * (L : ℝ) := hR.symm
    _ = (L : ℝ) * S.choose L := mul_comm _ _

theorem cappedOpenSlotFrameMass_le {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (j H : ℕ) (frames : Finset (Finset ℕ)) :
    cappedOpenSlotFrameMass A ρ j H frames ≤
      (H : ℝ) * ∑ F ∈ frames, frameBernoulliWeight A ρ F := by
  unfold cappedOpenSlotFrameMass
  have hpt : ∀ F ∈ frames,
      (min H (openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
          frameBernoulliWeight A ρ F ≤
        (H : ℝ) * frameBernoulliWeight A ρ F := by
    intro F _
    have hw : 0 ≤ frameBernoulliWeight A ρ F :=
      frameBernoulliWeight_nonneg hρ0 hρ1 F
    have hmin : min (H : ℝ) ((openSlot A (F.sort (· ≤ ·)) j).card : ℝ) ≤
        (H : ℝ) :=
      min_le_left _ _
    exact mul_le_mul_of_nonneg_right hmin hw
  have hsum := sum_le_sum hpt
  have hrw :
      ∑ F ∈ frames, (H : ℝ) * frameBernoulliWeight A ρ F =
        (H : ℝ) * ∑ F ∈ frames, frameBernoulliWeight A ρ F :=
    (mul_sum frames (fun F => frameBernoulliWeight A ρ F) (H : ℝ)).symm
  exact hsum.trans_eq hrw

theorem shortOpenSlotFrameMass_le_capped {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (j H : ℕ) (frames : Finset (Finset ℕ)) :
    shortOpenSlotFrameMass A ρ j H frames ≤
      cappedOpenSlotFrameMass A ρ j H frames := by
  unfold shortOpenSlotFrameMass cappedOpenSlotFrameMass
  have hpt :
      ∀ F ∈ frames.filter (fun F =>
          (openSlot A (F.sort (· ≤ ·)) j).card ≤ H),
        ((openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
            frameBernoulliWeight A ρ F ≤
          (min H (openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
            frameBernoulliWeight A ρ F := by
    intro F hF
    have hle : (openSlot A (F.sort (· ≤ ·)) j).card ≤ H :=
      (mem_filter.mp hF).2
    have hleR : ((openSlot A (F.sort (· ≤ ·)) j).card : ℝ) ≤ (H : ℝ) :=
      Nat.cast_le.mpr hle
    rw [min_eq_right hleR]
  have hsum := sum_le_sum hpt
  refine hsum.trans ?_
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ frames) fun F _ _ =>
    mul_nonneg
      (le_min (Nat.cast_nonneg H)
        (Nat.cast_nonneg (openSlot A (F.sort (· ≤ ·)) j).card))
      (frameBernoulliWeight_nonneg hρ0 hρ1 F)

/-- Empty open slots contribute `0` to the short-occupancy mass. -/
theorem shortOpenSlotFrameMass_empty_eq_zero (A : Finset ℕ) (ρ : ℝ)
    (j : ℕ) (frames : Finset (Finset ℕ)) :
    shortOpenSlotFrameMass A ρ j 0 frames = 0 := by
  unfold shortOpenSlotFrameMass
  have hpt :
      ∀ F ∈ frames.filter (fun F =>
          (openSlot A (F.sort (· ≤ ·)) j).card ≤ 0),
        ((openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
            frameBernoulliWeight A ρ F = 0 := by
    intro F hF
    have hle : (openSlot A (F.sort (· ≤ ·)) j).card ≤ 0 :=
      (mem_filter.mp hF).2
    have hz : (openSlot A (F.sort (· ≤ ·)) j).card = 0 := by omega
    simp [hz]
  rw [sum_congr rfl hpt, sum_const]
  simp

theorem shortOpenSlot_powersetCard_mass_le {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {L j H : ℕ} (hL : 2 ≤ L)
    (hLS : L ≤ A.card) :
    shortOpenSlotFrameMass A ρ j H (A.powersetCard (L - 1)) ≤
      (H : ℝ) * (A.card.choose (L - 1) : ℝ) * ρ ^ L *
        (1 - ρ) ^ (A.card - L) := by
  have h1 := shortOpenSlotFrameMass_le_capped (A := A) (ρ := ρ) hρ0 hρ1
    j H (A.powersetCard (L - 1))
  have h2 := cappedOpenSlotFrameMass_le (A := A) (ρ := ρ) hρ0 hρ1 j H
    (A.powersetCard (L - 1))
  have hm : (L - 1) + 1 ≤ A.card := by omega
  have hsum := sum_frameBernoulliWeight_powersetCard A hρ0 hρ1 hm
  have hpow : L - 1 + 1 = L := Nat.sub_add_cancel (Nat.le_of_succ_le hL)
  have hexp : A.card - (L - 1) - 1 = A.card - L := by omega
  have hrew :
      (H : ℝ) * ∑ F ∈ A.powersetCard (L - 1), frameBernoulliWeight A ρ F =
        (H : ℝ) * (A.card.choose (L - 1) : ℝ) * ρ ^ L *
          (1 - ρ) ^ (A.card - L) := by
    rw [hsum, hpow, hexp]
    ring
  exact (h1.trans h2).trans_eq hrew

/-- Weight-formula bound: short-occupancy `(L-1)`-frame mass is at most
`(L H / (|A|-L+1))` times the exact `L`-set Bernoulli mass. -/
theorem shortOpenSlot_powersetCard_mass_le_LH_div {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {L j H : ℕ} (hL : 2 ≤ L)
    (hLS : L ≤ A.card) :
    shortOpenSlotFrameMass A ρ j H (A.powersetCard (L - 1)) ≤
      ((L : ℝ) * H / ((A.card : ℝ) - L + 1)) *
        (A.card.choose L : ℝ) * ρ ^ L * (1 - ρ) ^ (A.card - L) := by
  have h0 := shortOpenSlot_powersetCard_mass_le (A := A) (ρ := ρ) (j := j)
    (H := H) hρ0 hρ1 hL hLS
  have hL1 : 1 ≤ L := Nat.le_of_succ_le hL
  have hch := choose_pred_cast (S := A.card) (L := L) hL1 hLS
  have hdenN : 0 < A.card - L + 1 := by omega
  have hcast : ((A.card - L + 1 : ℕ) : ℝ) = (A.card : ℝ) - (L : ℝ) + 1 := by
    rw [Nat.cast_add_one, Nat.cast_sub hLS]
  have hden : (A.card : ℝ) - (L : ℝ) + 1 ≠ 0 := by
    rw [← hcast]
    exact Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hdenN)
  have hrew :
      (H : ℝ) * (A.card.choose (L - 1) : ℝ) * ρ ^ L *
          (1 - ρ) ^ (A.card - L) =
        ((L : ℝ) * H / ((A.card : ℝ) - L + 1)) *
          (A.card.choose L : ℝ) * ρ ^ L * (1 - ρ) ^ (A.card - L) := by
    rw [hch]
    have hmul :
        (H : ℝ) * ((L : ℝ) / ((A.card : ℝ) - L + 1) *
          (A.card.choose L : ℝ)) =
          ((L : ℝ) * H / ((A.card : ℝ) - L + 1)) *
            (A.card.choose L : ℝ) := by
      rw [← mul_assoc, ← mul_div_assoc, mul_comm (H : ℝ)]
    rw [hmul]
  exact h0.trans_eq hrew

theorem bernoulliThin_powersetCard (A : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (k : ℕ) :
    ∑ B ∈ A.powersetCard k, bernoulliThin A ρ hρ0 hρ1 B =
      (A.card.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (A.card - k) := by
  have hpt : ∀ B ∈ A.powersetCard k,
      bernoulliThin A ρ hρ0 hρ1 B =
        ρ ^ k * (1 - ρ) ^ (A.card - k) := by
    intro B hB
    have hBA : B ⊆ A := (mem_powersetCard.mp hB).1
    have hcard : B.card = k := (mem_powersetCard.mp hB).2
    rw [bernoulliThin_eq A hρ0 hρ1 hBA, hcard]
  rw [sum_congr rfl hpt, sum_const, nsmul_eq_mul, card_powersetCard]
  ring

/-- Dropping the exact `L`-set mass (at most `1`) yields
`L H / (|A|-L+1)`. -/
theorem shortOpenSlot_powersetCard_mass_le_LH_div_card {A : Finset ℕ}
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {L j H : ℕ} (hL : 2 ≤ L)
    (hLS : L ≤ A.card) :
    shortOpenSlotFrameMass A ρ j H (A.powersetCard (L - 1)) ≤
      (L : ℝ) * H / ((A.card : ℝ) - L + 1) := by
  have h := shortOpenSlot_powersetCard_mass_le_LH_div (A := A) (ρ := ρ)
    (j := j) (H := H) hρ0 hρ1 hL hLS
  have hmass :
      (A.card.choose L : ℝ) * ρ ^ L * (1 - ρ) ^ (A.card - L) ≤ 1 := by
    have hsum := bernoulliThin_powersetCard A hρ0 hρ1 L
    have htot := bernoulliThin_sum A hρ0 hρ1
    have hle :
        ∑ B ∈ A.powersetCard L, bernoulliThin A ρ hρ0 hρ1 B ≤ 1 :=
      (sum_le_sum_of_subset_of_nonneg
        (s := A.powersetCard L) (t := A.powerset)
        (fun B hB => mem_powerset.mpr (mem_powersetCard.mp hB).1)
        (fun B _ _ => bernoulliThin_nonneg A hρ0 hρ1 B)).trans_eq htot
    rw [hsum] at hle
    simpa [mul_assoc] using hle
  have hfac : 0 ≤ (L : ℝ) * H / ((A.card : ℝ) - L + 1) := by
    have hdenN : 0 < A.card - L + 1 := by omega
    have hcast : ((A.card - L + 1 : ℕ) : ℝ) = (A.card : ℝ) - (L : ℝ) + 1 := by
      rw [Nat.cast_add_one, Nat.cast_sub hLS]
    have hden : 0 < (A.card : ℝ) - (L : ℝ) + 1 := by
      rw [← hcast]
      exact Nat.cast_pos.mpr hdenN
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      hden.le
  have hmul :
      ((L : ℝ) * H / ((A.card : ℝ) - L + 1)) *
          ((A.card.choose L : ℝ) * ρ ^ L * (1 - ρ) ^ (A.card - L)) ≤
        ((L : ℝ) * H / ((A.card : ℝ) - L + 1)) * 1 :=
    mul_le_mul_of_nonneg_left hmass hfac
  have hrw :
      ((L : ℝ) * H / ((A.card : ℝ) - L + 1)) *
          (A.card.choose L : ℝ) * ρ ^ L * (1 - ρ) ^ (A.card - L) =
        ((L : ℝ) * H / ((A.card : ℝ) - L + 1)) *
          ((A.card.choose L : ℝ) * ρ ^ L * (1 - ρ) ^ (A.card - L)) := by
    ring
  have h' := h.trans_eq hrw
  simpa using h'.trans hmul

/-- When `2 L ≤ |A|`, the weight bound is `≤ 2 L H / |A|`. -/
theorem shortOpenSlot_powersetCard_mass_le_two_LH_div_card {A : Finset ℕ}
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {L j H : ℕ} (hL : 2 ≤ L)
    (h2L : 2 * L ≤ A.card) :
    shortOpenSlotFrameMass A ρ j H (A.powersetCard (L - 1)) ≤
      (2 : ℝ) * L * H / A.card := by
  have hLS : L ≤ A.card := by omega
  have hS : 0 < A.card := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) <|
    le_trans hL hLS
  have h := shortOpenSlot_powersetCard_mass_le_LH_div_card (A := A)
    (ρ := ρ) (j := j) (H := H) hρ0 hρ1 hL hLS
  have h2R : (L : ℝ) * 2 ≤ (A.card : ℝ) := by
    simpa [mul_comm] using (by exact_mod_cast h2L : (2 : ℝ) * (L : ℝ) ≤ (A.card : ℝ))
  have hhalf : (L : ℝ) ≤ (A.card : ℝ) / 2 :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr h2R
  have hden1 : 0 < (A.card : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr hS) (by norm_num)
  have hden2 : (A.card : ℝ) / 2 ≤ (A.card : ℝ) - (L : ℝ) + 1 := by linarith
  have hdenpos : 0 < (A.card : ℝ) - (L : ℝ) + 1 := lt_of_lt_of_le hden1 hden2
  have hnum : 0 ≤ (L : ℝ) * H :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfrac :
      (L : ℝ) * H / ((A.card : ℝ) - L + 1) ≤
        (L : ℝ) * H / ((A.card : ℝ) / 2) :=
    div_le_div_of_nonneg_left hnum hden1 hden2
  have hrw : (L : ℝ) * H / ((A.card : ℝ) / 2) =
      (2 : ℝ) * L * H / A.card := by
    rw [div_div_eq_mul_div]
    ring
  exact h.trans (hfrac.trans_eq hrw)

end PrimeGapNormality.Prime
