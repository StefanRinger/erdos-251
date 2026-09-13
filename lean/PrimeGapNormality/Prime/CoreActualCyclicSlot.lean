import PrimeGapNormality.Prime.CorePositiveRootFrameAssembly
import PrimeGapNormality.Prime.CoreCyclicOrderedInsertion
import PrimeGapNormality.Prime.CoreActualFrameJoint

/-!
# Actual cyclic phase on a finite insertion slot

This file supplies the finite bridge needed by the compact-polynomial
Selberg estimate.  The signed exterior assignment is identified with the
actual deleted-frame ranks, the original-law cutoff gives a compact
normalized frame (including the central slot width), and a chosen point of
every nonempty slot supplies an exact outer phase for all other insertions.

No analytic insertion estimate is proved here.
-/

namespace PrimeGapNormality.Prime.CoreActualCyclicSlot

open Finset MvPolynomial
open scoped BigOperators Classical Polynomial

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

/-! ## Signed exterior coordinates are actual deleted-frame gaps -/

/-- The piecewise signed-coordinate convention in the formal action is
exactly the contiguous rank convention of the finite exterior frame. -/
theorem orderedExteriorGap_eq_deletedRank
    (F : Finset ℕ) (J : ℕ) (hJ : 1 ≤ J)
    (i : CoreCyclic.OnePoint.ExteriorIndex) :
    CoreCyclic.orderedExteriorGap F J i =
      (subsetGap F (CoreCyclic.OnePoint.FiniteExterior.deletedRank J i) : ℝ) := by
  by_cases hi0 : (i : ℤ) = 0
  · have hi : i = ⟨0, by norm_num⟩ := Subtype.ext hi0
    subst i
    rw [CoreCyclic.orderedExteriorGap_zero,
      CoreCyclic.OnePoint.FiniteExterior.deletedRank_zero J hJ]
  · by_cases hineg : (i : ℤ) < 0
    · have hile : (i : ℤ) ≤ -2 := by
        have hine : (i : ℤ) ≠ -1 := i.property
        omega
      rw [CoreCyclic.orderedExteriorGap_neg F J i hineg]
      unfold CoreCyclic.OnePoint.FiniteExterior.deletedRank
      rw [if_pos hile]
    · have hipos : 0 < (i : ℤ) := lt_of_le_of_ne (not_lt.mp hineg) (Ne.symm hi0)
      have hinle : ¬(i : ℤ) ≤ -2 := by omega
      rw [CoreCyclic.orderedExteriorGap_pos F J i hipos]
      unfold CoreCyclic.OnePoint.FiniteExterior.deletedRank
      rw [if_neg hinle]
      have hiCast : ((Int.toNat (i : ℤ) : ℕ) : ℤ) = (i : ℤ) :=
        Int.toNat_of_nonneg hipos.le
      have hsum : 0 ≤ (J : ℤ) + (i : ℤ) - 1 := by
        have hJz : (1 : ℤ) ≤ J := by exact_mod_cast hJ
        omega
      have hsumCast :
          ((Int.toNat ((J : ℤ) + (i : ℤ) - 1) : ℕ) : ℤ) =
            (J : ℤ) + (i : ℤ) - 1 :=
        Int.toNat_of_nonneg hsum
      have hright : 1 ≤ J + Int.toNat (i : ℤ) := by omega
      have hidx : Int.toNat ((J : ℤ) + (i : ℤ) - 1) =
          J + Int.toNat (i : ℤ) - 1 := by omega
      rw [hidx]

/-- Finite-coordinate form of the same exact identification. -/
theorem orderedExteriorGap_embedding
    (w : ℕ) (F : Finset ℕ) (J : ℕ) (hJ : 1 ≤ J)
    (i : Fin (2 * w + 1)) :
    CoreCyclic.orderedExteriorGap F J
        (CoreCyclic.OnePoint.FiniteExterior.embedding w i) =
      (subsetGap F (CoreCyclic.OnePoint.FiniteExterior.frameRank w J i) : ℝ) := by
  exact orderedExteriorGap_eq_deletedRank F J hJ
    (CoreCyclic.OnePoint.FiniteExterior.embedding w i)

/-! ## The original cutoff gives a compact normalized frame -/

/-- The central deleted-frame gap rank belongs to the finite exterior
rank set. -/
theorem pred_mem_frameRanks (w J : ℕ) (hJ : 1 ≤ J) :
    J - 1 ∈ CoreCyclic.OnePoint.FiniteExterior.frameRanks w J := by
  let z : CoreCyclic.OnePoint.ExteriorIndex := ⟨0, by norm_num⟩
  obtain ⟨i, hi⟩ :=
      (CoreCyclic.OnePoint.FiniteExterior.mem_range_embedding_iff w z).2 (by
    dsimp only [z]
    constructor <;> omega)
  apply mem_image.mpr
  refine ⟨i, mem_univ i, ?_⟩
  unfold CoreCyclic.OnePoint.FiniteExterior.frameRank
  rw [hi, CoreCyclic.OnePoint.FiniteExterior.deletedRank_zero J hJ]

/-- Negating the original bad-frame event bounds every normalized exterior
coordinate by the cutoff radius. -/
theorem localFrame_le_of_not_bad
    (w J : ℕ) {G R : ℝ} (F : Finset ℕ)
    (hgood : ¬ ∃ q ∈ CoreCyclic.OnePoint.FiniteExterior.frameRanks w J,
      R < (subsetGap F q : ℝ) / G)
    (i : Fin (2 * w + 1)) :
    CoreActualFrameJoint.localFrame w J G F i ≤ R := by
  unfold CoreActualFrameJoint.localFrame
  apply le_of_not_gt
  intro hi
  apply hgood
  exact ⟨CoreCyclic.OnePoint.FiniteExterior.frameRank w J i,
    mem_image.mpr ⟨i, mem_univ i, rfl⟩, hi⟩

theorem localFrame_mem_Icc_of_not_bad
    (w J : ℕ) {G R : ℝ} (hG : 0 < G) (F : Finset ℕ)
    (hgood : ¬ ∃ q ∈ CoreCyclic.OnePoint.FiniteExterior.frameRanks w J,
      R < (subsetGap F q : ℝ) / G)
    (i : Fin (2 * w + 1)) :
    CoreActualFrameJoint.localFrame w J G F i ∈ Set.Icc 0 R :=
  ⟨CoreActualFrameJoint.localFrame_nonneg w J hG.le F i,
    localFrame_le_of_not_bad w J F hgood i⟩

/-- In particular, the normalized physical slot width is at most the same
cutoff radius. -/
theorem centralWidth_le_of_not_bad
    (w J : ℕ) (hJ : 1 ≤ J) {G R : ℝ} (F : Finset ℕ)
    (hgood : ¬ ∃ q ∈ CoreCyclic.OnePoint.FiniteExterior.frameRanks w J,
      R < (subsetGap F q : ℝ) / G) :
    (subsetGap F (J - 1) : ℝ) / G ≤ R := by
  exact le_of_not_gt fun h ↦ hgood
    ⟨J - 1, pred_mem_frameRanks w J hJ, h⟩

/-- The cutoff appearing in `corePositiveCutTest` specializes on an actual
insertion fibre to the preceding finite-frame condition. -/
theorem not_frameBad_insert_iff
    {A F : Finset ℕ} {J u : ℕ} (w : ℕ) (G R : ℝ)
    (hJ : 1 ≤ J)
    (hu : u ∈ openSlot A (F.sort (· ≤ ·)) (J - 1)) :
    ¬ corePositiveFrameBad (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
        (J - 1) G R (insert u F) ↔
      ¬ ∃ q ∈ CoreCyclic.OnePoint.FiniteExterior.frameRanks w J,
        R < (subsetGap F q : ℝ) / G := by
  exact not_congr
    (corePositiveFrameBad_insert_iff
      (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J) G R
      (j := J - 1) hu)

/-! ## Exact phase representation on a nonempty slot -/

def slot (A F : Finset ℕ) (J : ℕ) : Finset ℕ :=
  openSlot A (F.sort (· ≤ ·)) (J - 1)

def actualFinitePhase
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (K : ℕ) (U : Finset ℕ) : ℝ :=
  CoreCyclic.coreCyclicFinitePhase B hk r P K (CoreCyclic.orderedRealGap U)

def slotMovingPolynomial
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (w J : ℕ) (F : Finset ℕ) : ℝ[X] :=
  CoreCyclic.OnePoint.movingSpecialization
    (CoreCyclic.OnePoint.action B hk w (CoreCyclic.phaseAt hk r (J - 1)) P)
    (CoreCyclic.orderedExteriorGap F J)

/-- A selected actual point of every nonempty slot. -/
def selectedPoint (A F : Finset ℕ) (J : ℕ)
    (hE : (slot A F J).Nonempty) : ℕ := hE.choose

theorem selectedPoint_mem (A F : Finset ℕ) (J : ℕ)
    (hE : (slot A F J).Nonempty) : selectedPoint A F J hE ∈ slot A F J :=
  hE.choose_spec

/-- The outer phase determined by the selected reference insertion. -/
def selectedOuter
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (K w J : ℕ)
    (A F : Finset ℕ) (hE : (slot A F J).Nonempty) : ℝ :=
  actualFinitePhase B hk r P K (insert (selectedPoint A F J hE) F) -
    Polynomial.eval
      (CoreCyclic.orderedInsertionLeftGap F J (selectedPoint A F J hE))
      (slotMovingPolynomial B hk r P w J F) / (B : ℝ) ^ (J + 1)

private theorem mem_slot_to_insertionSlot
    {A F : Finset ℕ} {J u : ℕ} (hJ : 1 ≤ J)
    (hu : u ∈ slot A F J) :
    (CoreLinearInsertion.insertionSlot F J).1 < u ∧
      u < (CoreLinearInsertion.insertionSlot F J).2 := by
  have h := (mem_openSlot.mp hu).2
  simpa [slot, CoreLinearInsertion.insertionSlot, Nat.sub_add_cancel hJ] using h

/-- Every point of a nonempty physical slot has the same outer phase and
the exact moving polynomial supplied by the formal cyclic action. -/
theorem actualFinitePhase_eq_selectedOuter_add
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (K w J : ℕ)
    (hwJ : w + 1 ≤ J) (hJK : J < K)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (A F : Finset ℕ) (hE : (slot A F J).Nonempty)
    {u : ℕ} (hu : u ∈ slot A F J) :
    actualFinitePhase B hk r P K (insert u F) =
      selectedOuter B hk r P K w J A F hE +
        Polynomial.eval (CoreCyclic.orderedInsertionLeftGap F J u)
          (slotMovingPolynomial B hk r P w J F) / (B : ℝ) ^ (J + 1) := by
  have hJ : 1 ≤ J := by omega
  have huSlot := mem_slot_to_insertionSlot hJ hu
  have hvSlot := mem_slot_to_insertionSlot hJ (selectedPoint_mem A F J hE)
  have hdiff := CoreCyclic.coreCyclicFinitePhase_ordered_insert_sub
    hB hk r P K w J hwJ hJK hw F huSlot hvSlot
  unfold selectedOuter
  dsimp only [actualFinitePhase, slotMovingPolynomial] at hdiff ⊢
  rw [sub_div] at hdiff
  linarith

/-- Normalized insertion coordinate equals the moving left gap divided by
the physical scale. -/
theorem orderedInsertionLeftGap_eq_sub
    {F : Finset ℕ} {J u : ℕ} :
    CoreCyclic.orderedInsertionLeftGap F J u =
      (u : ℝ) - (CoreLinearInsertion.insertionSlot F J).1 := by
  unfold CoreCyclic.orderedInsertionLeftGap
  rw [CoreLinearInsertion.insertionSlot_left]

/-- The same representation in the normalized coordinate used by the
Selberg insertion theorem. -/
theorem actualFinitePhase_eq_selectedOuter_add_scaled
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (K w J : ℕ)
    (hwJ : w + 1 ≤ J) (hJK : J < K)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (A F : Finset ℕ) (hE : (slot A F J).Nonempty)
    {G : ℝ} (hG : G ≠ 0) {u : ℕ} (hu : u ∈ slot A F J) :
    actualFinitePhase B hk r P K (insert u F) =
      selectedOuter B hk r P K w J A F hE +
        Polynomial.eval
            (G * (((u : ℝ) - (CoreLinearInsertion.insertionSlot F J).1) / G))
            (slotMovingPolynomial B hk r P w J F) /
          (B : ℝ) ^ (J + 1) := by
  have hbase := actualFinitePhase_eq_selectedOuter_add
    hB hk r P K w J hwJ hJK hw A F hE hu
  have hx :
      G * (((u : ℝ) - (CoreLinearInsertion.insertionSlot F J).1) / G) =
        CoreCyclic.orderedInsertionLeftGap F J u := by
    rw [orderedInsertionLeftGap_eq_sub]
    field_simp [hG]
  exact hbase.trans (by rw [hx])

/-- Empty physical slots contribute exactly zero to the undivided slot
sum used by the auxiliary-frame identity. -/
theorem slotInsertSum_eq_zero_of_not_nonempty
    (A F : Finset ℕ) (J : ℕ) (test : Finset ℕ → ℝ)
    (hE : ¬(slot A F J).Nonempty) :
    auxFrame_slotInsertSum A (J - 1) test F = 0 := by
  have hempty : slot A F J = ∅ := not_nonempty_iff_eq_empty.mp hE
  unfold auxFrame_slotInsertSum
  change (∑ u ∈ slot A F J, test (insert u F)) = 0
  rw [hempty]
  simp

end

end PrimeGapNormality.Prime.CoreActualCyclicSlot
