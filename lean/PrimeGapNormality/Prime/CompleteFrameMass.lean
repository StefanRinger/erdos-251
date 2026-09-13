import PrimeGapNormality.Prime.Coupling
import PrimeGapNormality.Prime.ExceptionSlot
import PrimeGapNormality.Prime.GridCompare
import PrimeGapNormality.Prime.Merge
import PrimeGapNormality.Prime.RankDelete
import PrimeGapNormality.Prime.SlotResample
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Occupancy-weighted mass of complete frames of every cardinality `≥ L-1`

Paper v0.4, subsection "Complete frames and the deterministic grid
comparison": on configurations with `N ≥ L`, delete interior rank `j`
(`1 ≤ j < L` paper; Lean `j + 1 < L`), keep every other survivor
including those beyond rank `L`, and obtain a remaining frame `F`.
Neighbours determine `W_F = (a,c)`. Preimages are `F ∪ {u}` for
`u ∈ A ∩ W_F`, each with common Bernoulli weight
`ρ^{|F|+1}(1-ρ)^{|A|-|F|-1}`. Frame mass is that weight times
`|A ∩ W_F|`. Summing over **all** complete frames, not only those
with exactly `L-1` points, recovers `P(N ≥ L) ≤ 1`.

Unrooted count: `N = |B|` for `B ⊆ A`. Dummy root `0` is not in `A`.
The event `N ≥ L` is the frame condition `|F| ≥ L-1`. Empty preimage
has mass `0` and needs no division. Reinsertion is uniform on a nonempty
slot (`SlotResample.deleted_point_uniform_on_slot`).

`ExceptionSlot` sums only `(L-1)`-frames by design; this leaf is the
missing all-cardinalities identity. Do not import `StatisticalPack`.

Source: `rounds/round106/09_gpt_v04_lean_audit_and_grok_order.md`
Paket 5 complete frames; paper v0.4.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 800000

/-! ### Slot identification and named masses -/

/-- Grid-compare occupancy of a remaining frame is the open deletion
slot `A ∩ (a,c)`. -/
theorem completeFrameOccupancy_eq_openSlot (A : Finset ℕ) (F : List ℕ)
    (j : ℕ) : completeFrameOccupancy A F j = openSlot A F j :=
  rfl

/-- Remaining complete frames after deleting interior rank `j`:
every `F ⊆ A` with `|F| ≥ L-1`. Paper: `N ≥ L` is `|F| ≥ L-1`. -/
def completeFrames (A : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter (fun F => L - 1 ≤ F.card)

/-- Configurations with unrooted survivor count `N = |B| ≥ L`. -/
def geLConfigs (A : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter (fun B => L ≤ B.card)

/-- Occupancy-weighted frame mass, all cardinalities `≥ L-1`.
Uses `completeFrameOccupancy` (`= openSlot`). -/
noncomputable def completeFrameOccupancyMass (A : Finset ℕ) (ρ : ℝ)
    (L j : ℕ) : ℝ :=
  ∑ F ∈ completeFrames A L,
    ((completeFrameOccupancy A (F.sort (· ≤ ·)) j).card : ℝ) *
      frameBernoulliWeight A ρ F

/-- Bernoulli mass of `{B ⊆ A | L ≤ B.card}`. This is `P(N ≥ L)` for
independent Bernoulli-`ρ` thinning on `A`, with unrooted `N = |B|`.
The dummy root `0` is not an element of `A`. -/
noncomputable def geLBernoulliMass (A : Finset ℕ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (L : ℕ) : ℝ :=
  ∑ B ∈ geLConfigs A L, bernoulliThin A ρ hρ0 hρ1 B

/-! ### Empty preimage: mass `0`, no division -/

/-- Empty open slot: occupancy-weighted mass is `0`. No normalisation
is taken. -/
theorem openSlot_occupancy_weight_eq_zero_of_empty (A : Finset ℕ)
    (ρ : ℝ) (F : List ℕ) (j : ℕ) (h : openSlot A F j = ∅) :
    ((openSlot A F j).card : ℝ) * frameBernoulliWeight A ρ F.toFinset =
      0 := by
  simp [h]

theorem completeFrameOccupancy_weight_eq_zero_of_empty (A : Finset ℕ)
    (ρ : ℝ) (F : List ℕ) (j : ℕ)
    (h : completeFrameOccupancy A F j = ∅) :
    ((completeFrameOccupancy A F j).card : ℝ) *
        frameBernoulliWeight A ρ F.toFinset = 0 := by
  rw [completeFrameOccupancy_eq_openSlot] at h ⊢
  exact openSlot_occupancy_weight_eq_zero_of_empty A ρ F j h

/-! ### Occupancy × common weight is the preimage sum -/

theorem occupancy_weight_eq_openSlot_sum {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {F : Finset ℕ} {j : ℕ} (hFA : F ⊆ A) :
    ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j,
        bernoulliThin A ρ hρ0.le hρ1.le
          (insertAt (F.sort (· ≤ ·)) j u).toFinset =
      ((openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
        frameBernoulliWeight A ρ F := by
  have hpw : (F.sort (· ≤ ·)).Pairwise (· < ·) := sort_pairwise_lt F
  have hFA' : (F.sort (· ≤ ·)).toFinset ⊆ A := by
    simpa [sort_toFinset] using hFA
  have hsum :=
    openSlot_bernoulliThin_sum (A := A) (ρ := ρ) (F := F.sort (· ≤ ·))
      (j := j) hρ0 hρ1 hpw hFA'
  simpa [sort_toFinset] using hsum

/-! ### Remaining list versus the erased order statistic -/

/-- Rank-`j` order statistic, via `getD` so later identities do not
depend on a particular `getElem` proof. Equals `B.sort[j]` when
`j < B.card`. -/
def deletedOf (B : Finset ℕ) (j : ℕ) : ℕ :=
  (B.sort (· ≤ ·)).getD j 0

theorem deletedOf_eq_getElem {B : Finset ℕ} {j : ℕ} (hj : j < B.card) :
    deletedOf B j =
      (B.sort (· ≤ ·))[j]'(by simpa [length_sort] using hj) := by
  unfold deletedOf
  exact getD_eq_getElem_nat (by simpa [length_sort] using hj)

theorem deletedOf_mem {B : Finset ℕ} {j : ℕ} (hj : j < B.card) :
    deletedOf B j ∈ B := by
  rw [deletedOf_eq_getElem hj]
  exact (mem_sort (· ≤ ·)).mp (List.getElem_mem _)

theorem remainingFrame_toFinset {B : Finset ℕ} {j : ℕ}
    (hj : j < B.card) :
    (remainingFrame B j).toFinset = B.erase (deletedOf B j) := by
  have hjle : j ≤ (remainingFrame B j).length := by
    rw [remainingFrame_length hj]
    omega
  have hto := insertAt_toFinset (F := remainingFrame B j) (j := j)
    (u := deletedOf B j) hjle
  have hins :
      insertAt (remainingFrame B j) j (deletedOf B j) = B.sort (· ≤ ·) := by
    rw [deletedOf_eq_getElem hj, insertAt_remainingFrame hj]
  rw [hins, sort_toFinset] at hto
  -- `hto : B = insert u F.toFinset`. Abstract so `rw [hto]` does not
  -- re-apply `deletedOf`/`remainingFrame` to the substituted insert.
  set u : ℕ := deletedOf B j
  set F : List ℕ := remainingFrame B j
  have huF : u ∉ F.toFinset := by
    intro hmem
    have hcard : (insert u F.toFinset).card = B.card := by
      rw [← hto]
    have hcard' : (insert u F.toFinset).card = F.toFinset.card :=
      card_insert_of_mem hmem
    have hR : F.toFinset.card = F.length :=
      List.toFinset_card_of_nodup
        (pairwise_nodup_lt (remainingFrame_pairwise B j))
    have hlenR : F.length = B.card - 1 := remainingFrame_length hj
    have heq : B.card = B.card - 1 :=
      hcard.symm.trans (hcard'.trans (hR.trans hlenR))
    have hlt : B.card - 1 < B.card :=
      Nat.sub_lt (Nat.zero_lt_of_lt hj) Nat.zero_lt_one
    exact (ne_of_lt hlt) heq.symm
  rw [hto]
  exact (erase_insert huF).symm

theorem remainingFrame_eq_erase_sort {B : Finset ℕ} {j : ℕ}
    (hj : j < B.card) :
    remainingFrame B j = (B.erase (deletedOf B j)).sort (· ≤ ·) := by
  have hto : (remainingFrame B j).toFinset = B.erase (deletedOf B j) :=
    remainingFrame_toFinset hj
  have hpw : (remainingFrame B j).Pairwise (· < ·) :=
    remainingFrame_pairwise B j
  have hnd : (remainingFrame B j).Nodup := pairwise_nodup_lt hpw
  have hpw_le : (remainingFrame B j).Pairwise (· ≤ ·) :=
    hpw.imp (fun {_ _} h => le_of_lt h)
  have hsort := (List.toFinset_sort (· ≤ ·) hnd).mpr hpw_le
  rw [← hsort, hto]

/-! ### Reinsertion is the sorted insertion of a slot point -/

theorem not_mem_of_mem_openSlot_sort {A F : Finset ℕ} {j u : ℕ}
    (hu : u ∈ openSlot A (F.sort (· ≤ ·)) j) : u ∉ F := by
  have h := not_mem_toFinset_of_mem_deletionSlot (sort_pairwise_lt F)
    (mem_openSlot.mp hu).2
  simpa [sort_toFinset] using h

theorem insert_sort_eq_insertAt {A F : Finset ℕ} {j u : ℕ}
    (hu : u ∈ openSlot A (F.sort (· ≤ ·)) j) :
    (insert u F).sort (· ≤ ·) = insertAt (F.sort (· ≤ ·)) j u := by
  have hus := (mem_openSlot.mp hu).2
  have hpw := insertAt_pairwise_of_mem_slot (sort_pairwise_lt F) hus
  have hnd := pairwise_nodup_lt hpw
  have hpw_le : (insertAt (F.sort (· ≤ ·)) j u).Pairwise (· ≤ ·) :=
    hpw.imp (fun {_ _} h => le_of_lt h)
  have hj : j < (F.sort (· ≤ ·)).length :=
    lt_length_of_mem_deletionSlot hus.2
  have hjle : j ≤ (F.sort (· ≤ ·)).length := Nat.le_of_lt hj
  have hto : (insertAt (F.sort (· ≤ ·)) j u).toFinset = insert u F := by
    rw [insertAt_toFinset hjle, sort_toFinset]
  have hsort := (List.toFinset_sort (· ≤ ·) hnd).mpr hpw_le
  rw [← hsort, hto]

theorem j_lt_insert_card {A F : Finset ℕ} {j u : ℕ}
    (hu : u ∈ openSlot A (F.sort (· ≤ ·)) j) :
    j < (insert u F).card := by
  have hjF : j < F.card := by
    simpa [length_sort] using
      lt_length_of_mem_deletionSlot (mem_openSlot.mp hu).2.2
  have hcard : (insert u F).card = F.card + 1 :=
    card_insert_of_notMem (not_mem_of_mem_openSlot_sort hu)
  omega

theorem insert_sort_deletedOf_eq {A F : Finset ℕ} {j u : ℕ}
    (hu : u ∈ openSlot A (F.sort (· ≤ ·)) j) :
    deletedOf (insert u F) j = u := by
  unfold deletedOf
  rw [insert_sort_eq_insertAt hu]
  have hus := (mem_openSlot.mp hu).2
  have hj : j < (F.sort (· ≤ ·)).length :=
    lt_length_of_mem_deletionSlot hus.2
  have hjle : j ≤ (F.sort (· ≤ ·)).length := Nat.le_of_lt hj
  have hlen : j < (insertAt (F.sort (· ≤ ·)) j u).length := by
    rw [insertAt_length hjle]
    exact Nat.lt_succ_of_le hjle
  rw [getD_eq_getElem_nat hlen]
  simp [insertAt, List.getElem_insertIdx_self]

theorem insertAt_erase_deletedOf_toFinset {B : Finset ℕ} {j : ℕ}
    (hj : j < B.card) :
    (insertAt ((B.erase (deletedOf B j)).sort (· ≤ ·)) j
        (deletedOf B j)).toFinset = B := by
  rw [← remainingFrame_eq_erase_sort hj, deletedOf_eq_getElem hj,
    insertAt_remainingFrame hj, sort_toFinset]

/-! ### Uniform reinsertion on a nonempty complete-frame slot -/

/-- Conditional law of the deleted point given a remaining complete
frame: uniform on `A ∩ W_F`. Requires a nonempty slot (no `0/0`). -/
theorem deleted_point_uniform_on_completeFrame {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {F : List ℕ} {j u : ℕ}
    (hF : F.Pairwise (· < ·)) (hFA : F.toFinset ⊆ A)
    (hu : u ∈ completeFrameOccupancy A F j) :
    bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset /
        ∑ v ∈ completeFrameOccupancy A F j,
          bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j v).toFinset =
      (1 : ℝ) / (completeFrameOccupancy A F j).card := by
  rw [completeFrameOccupancy_eq_openSlot] at hu ⊢
  exact deleted_point_uniform_on_slot hρ0 hρ1 hF hFA hu

/-! ### Preimage bijection: complete frames ↔ `{N ≥ L}` -/

private theorem j_lt_of_geL {L j : ℕ} {B : Finset ℕ}
    (hj : j + 1 < L) (hB : L ≤ B.card) : j < B.card :=
  Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt hj) hB

private theorem mem_completeFrames_erase {A B : Finset ℕ} {L j : ℕ}
    (hBA : B ⊆ A) (hB : L ≤ B.card) (hj : j + 1 < L) :
    B.erase (deletedOf B j) ∈ completeFrames A L := by
  have hjB : j < B.card := j_lt_of_geL hj hB
  have huB : deletedOf B j ∈ B := deletedOf_mem hjB
  refine mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset _ B).trans hBA), ?_⟩
  rw [card_erase_of_mem huB]
  exact Nat.sub_le_sub_right hB 1

private theorem mem_openSlot_erase {A B : Finset ℕ} {j : ℕ}
    (hBA : B ⊆ A) (hpos : ∀ x ∈ A, 0 < x) (hj : j + 1 < B.card) :
    deletedOf B j ∈
      openSlot A ((B.erase (deletedOf B j)).sort (· ≤ ·)) j := by
  have hu := mem_openSlot_of_remainingFrame hBA hpos hj
  rw [← deletedOf_eq_getElem (Nat.lt_of_succ_lt hj)] at hu
  rwa [remainingFrame_eq_erase_sort (Nat.lt_of_succ_lt hj)] at hu

private theorem mem_geL_insert {A F : Finset ℕ} {L j u : ℕ}
    (hL : 2 ≤ L) (hFA : F ⊆ A) (hF : L - 1 ≤ F.card)
    (hu : u ∈ openSlot A (F.sort (· ≤ ·)) j) :
    insert u F ∈ geLConfigs A L := by
  have huA : u ∈ A := (mem_openSlot.mp hu).1
  have hBA : insert u F ⊆ A := insert_subset huA hFA
  have hcard : (insert u F).card = F.card + 1 :=
    card_insert_of_notMem (not_mem_of_mem_openSlot_sort hu)
  have hL1 : 1 ≤ L := Nat.le_of_succ_le hL
  have hge : L ≤ (insert u F).card := by
    rw [hcard]
    have := Nat.succ_le_succ hF
    simpa [Nat.sub_add_cancel hL1] using this
  exact mem_filter.mpr ⟨mem_powerset.mpr hBA, hge⟩

/-- Double sum of common preimage masses over remaining frames of every
cardinality `≥ L-1` equals the Bernoulli mass of `{N ≥ L}`. Unrooted:
`N = |B|`. -/
theorem completeFrame_preimage_sum_eq_geL {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L)
    (hpos : ∀ x ∈ A, 0 < x) :
    ∑ F ∈ A.powerset.filter (fun F => L - 1 ≤ F.card),
        ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j,
          bernoulliThin A ρ hρ0.le hρ1.le
            (insertAt (F.sort (· ≤ ·)) j u).toFinset =
      ∑ B ∈ A.powerset.filter (fun B => L ≤ B.card),
        bernoulliThin A ρ hρ0.le hρ1.le B := by
  set frames := A.powerset.filter (fun F => L - 1 ≤ F.card)
  rw [sum_sigma' (s := frames)
    (t := fun F => openSlot A (F.sort (· ≤ ·)) j)
    (f := fun F u =>
      bernoulliThin A ρ hρ0.le hρ1.le
        (insertAt (F.sort (· ≤ ·)) j u).toFinset)]
  -- Left index is the sigma `(F, u)`. Map that to `insert u F`; invert
  -- on a `Finset ℕ` configuration `B` via `B.erase`.
  refine sum_bij'
      (fun p _ => insert p.2 p.1)
      (fun B _ => ⟨B.erase (deletedOf B j), deletedOf B j⟩)
      ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hF := (mem_sigma.mp hp).1
    have hu := (mem_sigma.mp hp).2
    have hFcard : L - 1 ≤ p.1.card := (mem_filter.mp hF).2
    have hFA : p.1 ⊆ A := mem_powerset.mp (mem_filter.mp hF).1
    exact mem_geL_insert hL hFA hFcard hu
  · intro B hB
    have hBcard : L ≤ B.card := (mem_filter.mp hB).2
    have hBA : B ⊆ A := mem_powerset.mp (mem_filter.mp hB).1
    have hj1 : j + 1 < B.card := Nat.lt_of_lt_of_le hj hBcard
    refine mem_sigma.mpr ⟨?_, ?_⟩
    · exact mem_completeFrames_erase hBA hBcard hj
    · exact mem_openSlot_erase hBA hpos hj1
  · intro p hp
    have hu := (mem_sigma.mp hp).2
    have hdel : deletedOf (insert p.2 p.1) j = p.2 :=
      insert_sort_deletedOf_eq hu
    simp [hdel, erase_insert (not_mem_of_mem_openSlot_sort hu)]
  · intro B hB
    have hBcard : L ≤ B.card := (mem_filter.mp hB).2
    have hjB : j < B.card := j_lt_of_geL hj hBcard
    exact insert_erase (deletedOf_mem hjB)
  · intro p hp
    have hu := (mem_sigma.mp hp).2
    have hjF : j < (p.1.sort (· ≤ ·)).length :=
      lt_length_of_mem_deletionSlot (mem_openSlot.mp hu).2.2
    have hjle : j ≤ (p.1.sort (· ≤ ·)).length := Nat.le_of_lt hjF
    rw [insertAt_toFinset hjle, sort_toFinset]

/-- Occupancy-weighted masses of remaining frames of every cardinality
`≥ L-1` after deleting Lean rank `j` (`j + 1 < L`) equal the Bernoulli
mass of `{B ⊆ A | L ≤ B.card}`. This is `P(N ≥ L)` for unrooted
independent thinning (`N = |B|`); the dummy root is not in `A`. -/
theorem completeFrame_occupancy_mass_eq_geL {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L)
    (hpos : ∀ x ∈ A, 0 < x) :
    ∑ F ∈ A.powerset.filter (fun F => L - 1 ≤ F.card),
        ((openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
          frameBernoulliWeight A ρ F =
      ∑ B ∈ A.powerset.filter (fun B => L ≤ B.card),
        bernoulliThin A ρ hρ0.le hρ1.le B := by
  set frames := A.powerset.filter (fun F => L - 1 ≤ F.card)
  have hpt : ∀ F ∈ frames,
      ((openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
          frameBernoulliWeight A ρ F =
        ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j,
          bernoulliThin A ρ hρ0.le hρ1.le
            (insertAt (F.sort (· ≤ ·)) j u).toFinset := by
    intro F hF
    have hFA : F ⊆ A := mem_powerset.mp (mem_filter.mp hF).1
    exact (occupancy_weight_eq_openSlot_sum hρ0 hρ1 hFA).symm
  rw [sum_congr (s₁ := frames) (s₂ := frames) rfl hpt]
  exact completeFrame_preimage_sum_eq_geL hρ0 hρ1 hL hj hpos

/-- Same identity, written with `completeFrameOccupancy`
(`GridCompare`; definitionally `openSlot`). -/
theorem completeFrameOccupancy_mass_eq_geL {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L)
    (hpos : ∀ x ∈ A, 0 < x) :
    ∑ F ∈ A.powerset.filter (fun F => L - 1 ≤ F.card),
        ((completeFrameOccupancy A (F.sort (· ≤ ·)) j).card : ℝ) *
          frameBernoulliWeight A ρ F =
      ∑ B ∈ A.powerset.filter (fun B => L ≤ B.card),
        bernoulliThin A ρ hρ0.le hρ1.le B :=
  completeFrame_occupancy_mass_eq_geL hρ0 hρ1 hL hj hpos

theorem completeFrameOccupancyMass_eq_geLBernoulliMass {A : Finset ℕ}
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {L j : ℕ} (hL : 2 ≤ L)
    (hj : j + 1 < L) (hpos : ∀ x ∈ A, 0 < x) :
    completeFrameOccupancyMass A ρ L j =
      geLBernoulliMass A ρ hρ0.le hρ1.le L :=
  completeFrameOccupancy_mass_eq_geL hρ0 hρ1 hL hj hpos

/-! ### Bound `≤ 1` from the Bernoulli partition of the powerset -/

theorem geLBernoulliMass_le_one (A : Finset ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (L : ℕ) :
    geLBernoulliMass A ρ hρ0 hρ1 L ≤ 1 := by
  have htot := bernoulliThin_sum A hρ0 hρ1
  have hsub : geLConfigs A L ⊆ A.powerset := filter_subset _ _
  exact (sum_le_sum_of_subset_of_nonneg (s := geLConfigs A L)
      (t := A.powerset) hsub
      (fun B _ _ => bernoulliThin_nonneg A hρ0 hρ1 B)).trans_eq htot

/-- Occupancy-weighted complete-frame masses sum to `P(N ≥ L) ≤ 1`. -/
theorem completeFrame_occupancy_mass_le_one {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L)
    (hpos : ∀ x ∈ A, 0 < x) :
    ∑ F ∈ A.powerset.filter (fun F => L - 1 ≤ F.card),
        ((openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
          frameBernoulliWeight A ρ F ≤ 1 := by
  rw [completeFrame_occupancy_mass_eq_geL hρ0 hρ1 hL hj hpos]
  exact geLBernoulliMass_le_one A hρ0.le hρ1.le L

theorem completeFrameOccupancyMass_le_one {A : Finset ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L)
    (hpos : ∀ x ∈ A, 0 < x) :
    completeFrameOccupancyMass A ρ L j ≤ 1 :=
  completeFrame_occupancy_mass_le_one hρ0 hρ1 hL hj hpos

end PrimeGapNormality.Prime
