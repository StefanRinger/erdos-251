import PrimeGapNormality.Prime.CoreRoughSiftedCount
import PrimeGapNormality.Prime.CoreRoughShiftResidues
import PrimeGapNormality.Prime.FiniteRootMixInclusionProduct
import Mathlib.Data.Finset.Sort

/-!
# The finite rough-tuple count with its literal tuple Euler product

The forbidden residues come from actual translates by the shift set.
Early and late prime sets partition all primes through y, including when
y ≤ 4|E|. The main-term identity does not divide by local Euler factors.
-/

namespace PrimeGapNormality.Prime.CoreRoughTupleCount

open Finset CoreRoughShiftResidues CoreRoughMixedCRT CoreRoughSiftedCount
open CoreRoughDimensionProduct
open scoped Classical
noncomputable section

set_option maxHeartbeats 1000000

/-- Negation of residue classes preserves the exact local rank. -/
theorem card_forbiddenResidues_eq_residueCount (E : Finset ℕ) {p : ℕ} (hp : Nat.Prime p) :
    (forbiddenResidues E p).card = residueCount E p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  unfold residueCount
  apply Finset.card_bij (s := forbiddenResidues E p)
    (t := E.image (fun h : ℕ => (h : ZMod p)))
    (fun (r : Fin p) _ => -((r : ℕ) : ZMod p))
  · intro r hr
    obtain ⟨h, hh, hmod⟩ := mem_forbiddenResidues.mp hr
    have hzero : ((r : ℕ) : ZMod p) + (h : ZMod p) = 0 := by
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_iff_mod_eq_zero.mpr hmod
    refine mem_image.mpr ⟨h, hh, ?_⟩
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hzero
  · intro r hr s hs heq
    have heq' := neg_injective heq
    have hv := congrArg (fun z : ZMod p => z.val) heq'
    rw [ZMod.val_natCast_of_lt r.isLt, ZMod.val_natCast_of_lt s.isLt] at hv
    exact Fin.ext hv
  · intro z hz
    obtain ⟨h, hh, rfl⟩ := mem_image.mp hz
    let r : Fin p := ⟨(-(h : ZMod p)).val, ZMod.val_lt _⟩
    have hr : ((r : ℕ) : ZMod p) = -(h : ZMod p) := ZMod.natCast_zmod_val _
    refine ⟨r, mem_forbiddenResidues.mpr ⟨h, hh, ?_⟩, ?_⟩
    · apply Nat.dvd_iff_mod_eq_zero.mp
      apply (ZMod.natCast_eq_zero_iff ((r : ℕ) + h) p).mp
      rw [Nat.cast_add, hr, neg_add_cancel]
    · rw [hr, neg_neg]

def earlyPrimes (y k : ℕ) : Finset ℕ := Nat.primesLE (min y (4 * k))

def latePrimes (y k : ℕ) : Finset ℕ := dimensionPrimeBand 0 y k

def lateList (y k : ℕ) : List ℕ := (latePrimes y k).sort (· ≥ ·)

theorem lateList_toFinset (y k : ℕ) : (lateList y k).toFinset = latePrimes y k :=
  Finset.sort_toFinset _ _

theorem lateList_decreasing (y k : ℕ) : (lateList y k).Pairwise (fun p q => q < p) :=
  (Finset.sortedGT_sort (latePrimes y k)).pairwise

theorem early_late_union (y k : ℕ) : earlyPrimes y k ∪ latePrimes y k = Nat.primesLE y := by
  ext p
  constructor
  · intro hp
    rcases mem_union.mp hp with hp | hp
    · have hh : p ≤ min y (4 * k) ∧ Nat.Prime p := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesLE.mpr ⟨hh.1.trans (min_le_left _ _), hh.2⟩
    · change p ∈ dimensionPrimeBand 0 y k at hp
      have hh := CoreRoughRealCutDimension.mem_dimensionPrimeBand_iff.mp hp
      exact Nat.mem_primesLE.mpr ⟨hh.2.2, hh.1⟩
  · intro hp
    obtain ⟨hpy, hprime⟩ := Nat.mem_primesLE.mp hp
    by_cases hsmall : p ≤ 4 * k
    · exact mem_union_left _ (Nat.mem_primesLE.mpr ⟨le_min hpy hsmall, hprime⟩)
    · apply mem_union_right
      change p ∈ dimensionPrimeBand 0 y k
      apply CoreRoughRealCutDimension.mem_dimensionPrimeBand_iff.mpr
      exact ⟨hprime, by simpa only [max_eq_right (Nat.zero_le _)] using Nat.lt_of_not_ge hsmall, hpy⟩

theorem early_late_disjoint (y k : ℕ) : Disjoint (earlyPrimes y k) (latePrimes y k) := by
  apply Finset.disjoint_left.mpr
  intro p hp hl
  have hsmall := (Nat.mem_primesLE.mp hp).1.trans (min_le_right y (4 * k))
  have hlarge := (CoreRoughRealCutDimension.mem_dimensionPrimeBand_iff.mp hl).2.1
  omega

theorem earlyPrimes_subset (y k : ℕ) : earlyPrimes y k ⊆ Nat.primesLE (4 * k) := by
  intro p hp
  have hh := Nat.mem_primesLE.mp hp
  exact Nat.mem_primesLE.mpr ⟨hh.1.trans (min_le_right _ _), hh.2⟩

/-- The early density is an exact Euler product, even when it vanishes. -/
theorem earlyDensity_eq_product (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    earlyDensity B P = ∏ p ∈ P, (1 - ((B p).card : ℝ) / (p : ℝ)) := by
  unfold earlyDensity earlyChoices CoreRoughResidueCount.residueModulus
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hcard : (B p).card ≤ p := by simpa only [Fintype.card_fin] using card_le_univ (B p)
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hP p hp).ne_zero
  rw [Nat.cast_sub hcard]
  field_simp [hp0]

theorem early_late_product_eq (E : Finset ℕ) (y : ℕ) :
    earlyDensity (forbiddenResidues E) (earlyPrimes y E.card) *
      CoreBetaBuchstab.euler (fun p : ℕ => ((forbiddenResidues E p).card : ℝ) / (p : ℝ))
        (lateList y E.card) = finiteTupleSieveProduct E y := by
  have hprime : ∀ p ∈ earlyPrimes y E.card, Nat.Prime p := by
    intro p hp
    change p ∈ Nat.primesLE (min y (4 * E.card)) at hp
    exact (Nat.mem_primesLE.mp hp).2
  rw [earlyDensity_eq_product (forbiddenResidues E) (earlyPrimes y E.card) hprime]
  unfold CoreBetaBuchstab.euler
  rw [← List.prod_toFinset _ ((lateList_decreasing y E.card).imp (fun h => Ne.symm h.ne)),
    lateList_toFinset, ← Finset.prod_union (early_late_disjoint y E.card), early_late_union]
  apply Finset.prod_congr rfl
  intro p hp
  rw [card_forbiddenResidues_eq_residueCount E (Nat.mem_primesLE.mp hp).2]

theorem siftedInterval_eq_avoidedInterval (E : Finset ℕ) (y a H : ℕ) :
    siftedInterval (forbiddenResidues E) (earlyPrimes y E.card) (lateList y E.card) a H =
      avoidedInterval E y a H := by
  rw [siftedInterval, lateList_toFinset, early_late_union]
  rfl

/-- Literal prime-divisibility pattern count, with all local zero factors
included. The parameter Z may be the paper's y+1/2. -/
theorem avoidedInterval_error (E : Finset ℕ) (hE : 1 ≤ E.card)
    {y : ℕ} (hy : 16 ≤ y) {Z R : ℝ}
    (hZlo : (y : ℝ) < Z) (hZhi : Z ≤ (y : ℝ) + 1)
    (hlevel : Z ^ (9 * E.card + 1) ≤ R) (a H : ℕ) :
    |((avoidedInterval E y a H).card : ℝ) - (H : ℝ) * finiteTupleSieveProduct E y| ≤
      (H : ℝ) * finiteTupleSieveProduct E y *
        Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log Z) +
      Real.exp (10 * (E.card : ℝ)) * R * (1 + Real.log R) ^ (E.card - 1) := by
  have hps : (lateList y E.card).toFinset = dimensionPrimeBand 0 y E.card :=
    lateList_toFinset y E.card
  have hdis : Disjoint (earlyPrimes y E.card) (lateList y E.card).toFinset := by
    rw [lateList_toFinset]
    exact early_late_disjoint y E.card
  have hprime : ∀ p ∈ earlyPrimes y E.card ∪ (lateList y E.card).toFinset, Nat.Prime p := by
    rw [lateList_toFinset, early_late_union]
    exact fun p hp => (Nat.mem_primesLE.mp hp).2
  have hν : ∀ p ∈ lateList y E.card, (forbiddenResidues E p).card ≤ E.card := by
    intro p hp
    exact card_forbiddenResidues_le E
      (hprime p (mem_union_right _ (List.mem_toFinset.mpr hp)))
  have hh := siftedInterval_error_absolute (Nat.zero_le y) hy hE (forbiddenResidues E)
    (earlyPrimes y E.card) (lateList y E.card) (lateList_decreasing y E.card)
    hps hdis (earlyPrimes_subset y E.card) hprime hν hZlo hZhi hlevel a H
  have hmain : (H : ℝ) * earlyDensity (forbiddenResidues E) (earlyPrimes y E.card) *
      CoreBetaBuchstab.euler (fun p : ℕ => ((forbiddenResidues E p).card : ℝ) / (p : ℝ))
        (lateList y E.card) = (H : ℝ) * finiteTupleSieveProduct E y := by
    rw [mul_assoc, early_late_product_eq]
  simp only [siftedInterval_eq_avoidedInterval, hmain] at hh
  exact hh

theorem translatedRoughInterval_error (E : Finset ℕ) (hE : 1 ≤ E.card)
    {y : ℕ} (hy : 16 ≤ y) {Z R : ℝ}
    (hZlo : (y : ℝ) < Z) (hZhi : Z ≤ (y : ℝ) + 1)
    (hlevel : Z ^ (9 * E.card + 1) ≤ R) (a H : ℕ) (ha : 1 ≤ a) :
    |((translatedRoughInterval E y a H).card : ℝ) - (H : ℝ) * finiteTupleSieveProduct E y| ≤
      (H : ℝ) * finiteTupleSieveProduct E y *
        Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log Z) +
      Real.exp (10 * (E.card : ℝ)) * R * (1 + Real.log R) ^ (E.card - 1) := by
  rw [← avoidedInterval_eq_translatedRoughInterval E y a H ha]
  exact avoidedInterval_error E hE hy hZlo hZhi hlevel a H

/-- The paper's half-integer cutoff avoids changing the set of sieving
primes while giving the strict upper endpoint required by the beta weights. -/
theorem translatedRoughInterval_error_half (E : Finset ℕ) (hE : 1 ≤ E.card)
    {y : ℕ} (hy : 16 ≤ y) {R : ℝ}
    (hlevel : ((y : ℝ) + 1 / 2) ^ (9 * E.card + 1) ≤ R) (a H : ℕ) (ha : 1 ≤ a) :
    |((translatedRoughInterval E y a H).card : ℝ) - (H : ℝ) * finiteTupleSieveProduct E y| ≤
      (H : ℝ) * finiteTupleSieveProduct E y *
        Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log ((y : ℝ) + 1 / 2)) +
      Real.exp (10 * (E.card : ℝ)) * R * (1 + Real.log R) ^ (E.card - 1) :=
  translatedRoughInterval_error E hE hy (by linarith) (by linarith) hlevel a H ha

/-- The covering-prime case gives exact zeros on both sides, not merely
an error estimate whose main term happens to vanish. -/
theorem count_and_product_zero_of_local_full (E : Finset ℕ) {y p a H : ℕ}
    (ha : 1 ≤ a) (hp : Nat.Prime p) (hpy : p ≤ y)
    (hfull : forbiddenResidues E p = Finset.univ) :
    (translatedRoughInterval E y a H).card = 0 ∧ finiteTupleSieveProduct E y = 0 := by
  refine ⟨translatedRoughInterval_card_eq_zero_of_local_full E ha hp hpy hfull, ?_⟩
  unfold finiteTupleSieveProduct
  apply Finset.prod_eq_zero (Nat.mem_primesLE.mpr ⟨hpy, hp⟩)
  rw [← card_forbiddenResidues_eq_residueCount E hp, hfull, card_univ, Fintype.card_fin,
    div_self (Nat.cast_ne_zero.mpr hp.ne_zero), sub_self]

end
end PrimeGapNormality.Prime.CoreRoughTupleCount
