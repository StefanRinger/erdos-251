import PrimeGapNormality.Prime.CoreSequencePattern
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Preorder.Finite

/-!
# The actual moving-threshold rough sequence

An integer `n` belongs when it is positive and every prime divisor of `n`
is strictly larger than the value of the moving threshold at `n`.  In
particular `1` belongs vacuously.

If the threshold is eventually smaller than its argument, every sufficiently
large prime belongs.  Euclid's theorem therefore proves that the predicate is
infinite and makes its `Nat.nth` enumeration genuinely strictly increasing.
This file records only exact enumeration, window, count, and finite-pattern
geometry.  It asserts no density or window-count growth.
-/

namespace PrimeGapNormality.Prime.CoreMovingRoughSequence

open Finset Filter
open scoped Classical

noncomputable section

/-- Literal membership in the moving-threshold rough set. -/
def IsMovingRough (z : ℕ → ℕ) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → z n < p

theorem one_isMovingRough (z : ℕ → ℕ) : IsMovingRough z 1 := by
  refine ⟨le_rfl, ?_⟩
  intro p hp hpdvd
  exact False.elim (hp.not_dvd_one hpdvd)

/-- Eventual `z(n)<n` already forces infinitely many actual members: all
sufficiently large primes work. -/
theorem isMovingRough_infinite
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) :
    (Set.ofPred (IsMovingRough z)).Infinite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hz
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨p, hpLower, hpPrime⟩ :=
    Nat.exists_infinite_primes (max (M + 1) N)
  have hNp : N ≤ p := (le_max_right (M + 1) N).trans hpLower
  have hzp : z p < p := hN p hNp
  refine ⟨p, ?_, ?_⟩
  · refine ⟨hpPrime.one_le, ?_⟩
    intro q hqPrime hqp
    have hqpEq : q = p :=
      (Nat.prime_dvd_prime_iff_eq hqPrime hpPrime).mp hqp
    rwa [hqpEq]
  · have hMp : M + 1 ≤ p := (le_max_left (M + 1) N).trans hpLower
    omega

/-- Increasing enumeration of the literal moving-rough predicate. -/
def movingRoughSequence (z : ℕ → ℕ) : ℕ → ℕ :=
  Nat.nth (IsMovingRough z)

theorem movingRoughSequence_strictMono
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) :
    StrictMono (movingRoughSequence z) :=
  Nat.nth_strictMono (isMovingRough_infinite hz)

theorem movingRoughSequence_mem
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) (i : ℕ) :
    IsMovingRough z (movingRoughSequence z i) :=
  Nat.nth_mem_of_infinite (isMovingRough_infinite hz) i

/-- Exact range of the enumeration. -/
theorem range_movingRoughSequence
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) :
    Set.range (movingRoughSequence z) = Set.ofPred (IsMovingRough z) :=
  Nat.range_nth_of_infinite (isMovingRough_infinite hz)

theorem exists_movingRoughSequence_eq_iff
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) (n : ℕ) :
    (∃ i, movingRoughSequence z i = n) ↔ IsMovingRough z n := by
  change n ∈ Set.range (movingRoughSequence z) ↔ n ∈ Set.ofPred (IsMovingRough z)
  rw [range_movingRoughSequence hz]

theorem movingRoughSequence_pos
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) (i : ℕ) :
    0 < movingRoughSequence z i :=
  Nat.zero_lt_of_lt (movingRoughSequence_mem hz i).1

theorem movingRoughGap_pos
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) (i : ℕ) :
    0 < seqGap (movingRoughSequence z) i := by
  unfold seqGap
  exact Nat.sub_pos_of_lt
    (movingRoughSequence_strictMono hz (Nat.lt_succ_self i))

/-! ## Exact initial counts -/

/-- Actual moving-rough values in `[1,X]`. -/
def initialMovingRoughs (z : ℕ → ℕ) (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (IsMovingRough z)

theorem initialMovingRoughs_eq_image_range
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) (X : ℕ) :
    initialMovingRoughs z X =
      (range (seqCount (movingRoughSequence z) X)).image
        (movingRoughSequence z) := by
  ext n
  constructor
  · intro hn
    have hn' := mem_filter.mp hn
    obtain ⟨i, hi⟩ := (exists_movingRoughSequence_eq_iff hz n).mpr hn'.2
    apply mem_image.mpr
    refine ⟨i, mem_range.mpr ?_, hi⟩
    apply (seqCount_lt_iff (movingRoughSequence_strictMono hz)).mpr
    rw [hi]
    exact (mem_Icc.mp hn'.1).2
  · intro hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    have hle : movingRoughSequence z i ≤ X :=
      (seqCount_lt_iff (movingRoughSequence_strictMono hz)).mp (mem_range.mp hi)
    exact mem_filter.mpr
      ⟨mem_Icc.mpr ⟨(movingRoughSequence_mem hz i).1, hle⟩,
        movingRoughSequence_mem hz i⟩

/-- The literal initial count is the generic sequence count. -/
theorem initialMovingRoughs_card_eq_seqCount
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) (X : ℕ) :
    (initialMovingRoughs z X).card = seqCount (movingRoughSequence z) X := by
  rw [initialMovingRoughs_eq_image_range hz,
    card_image_of_injective _ (movingRoughSequence_strictMono hz).injective,
    card_range]

/-! ## Exact physical windows -/

/-- Actual moving-rough roots in the physical dyadic interval `(X,2X]`. -/
def rawPhysicalRoots (z : ℕ → ℕ) (X : ℕ) : Finset ℕ :=
  (Ioc X (2 * X)).filter (IsMovingRough z)

/-- The raw physical roots are exactly the image of the generic sequence
window under the actual enumeration. -/
theorem rawPhysicalRoots_eq_image_seqWindow
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) (X : ℕ) :
    rawPhysicalRoots z X =
      (seqWindow (movingRoughSequence z) X).image (movingRoughSequence z) := by
  ext n
  constructor
  · intro hn
    have hn' := mem_filter.mp hn
    obtain ⟨i, hi⟩ := (exists_movingRoughSequence_eq_iff hz n).mpr hn'.2
    apply mem_image.mpr
    refine ⟨i, ?_, hi⟩
    apply mem_filter.mpr
    have hnI := mem_Ioc.mp hn'.1
    refine ⟨mem_range.mpr ?_, ?_⟩
    · exact Nat.lt_succ_of_le
        ((strictMono_le_id (movingRoughSequence_strictMono hz) i).trans
          (hi.trans_le hnI.2))
    · simpa only [hi] using hnI
  · intro hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    have hi' := mem_filter.mp hi
    exact mem_filter.mpr
      ⟨mem_Ioc.mpr hi'.2, movingRoughSequence_mem hz i⟩

theorem rawPhysicalRoots_card_eq_seqWindow
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) (X : ℕ) :
    (rawPhysicalRoots z X).card =
      (seqWindow (movingRoughSequence z) X).card := by
  rw [rawPhysicalRoots_eq_image_seqWindow hz,
    card_image_of_injective _ (movingRoughSequence_strictMono hz).injective]

/-! ## Exact finite patterns at a physical root -/

/-- Literal offsets which land on another moving-rough integer. -/
def rawPhysicalPattern (z : ℕ → ℕ) (Ω : Finset ℕ) (v : ℕ) : Finset ℕ :=
  Ω.filter (fun h => IsMovingRough z (v + h))

theorem rawPhysicalPattern_eq_sequencePattern
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n)
    (Ω : Finset ℕ) (n : ℕ) :
    rawPhysicalPattern z Ω (movingRoughSequence z n) =
      CoreSequencePattern.pattern (movingRoughSequence z) Ω
        (movingRoughSequence z n) := by
  ext h
  simp only [rawPhysicalPattern, CoreSequencePattern.pattern, mem_filter]
  exact and_congr_right fun _ =>
    (exists_movingRoughSequence_eq_iff hz (movingRoughSequence z n + h)).symm

theorem rawPhysicalPattern_card_ge_iff_span
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n)
    {n L S : ℕ} (hL : 1 ≤ L) :
    L ≤ (rawPhysicalPattern z (Icc 1 S) (movingRoughSequence z n)).card ↔
      movingRoughSequence z (n + L) - movingRoughSequence z n ≤ S := by
  rw [rawPhysicalPattern_eq_sequencePattern hz]
  exact CoreSequencePattern.pattern_card_ge_iff_span
    (movingRoughSequence_strictMono hz) hL

theorem rawPhysicalPattern_firstL_eq_prefixSet
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n)
    {n L S : ℕ} (hL : 1 ≤ L)
    (hspan : movingRoughSequence z (n + L) - movingRoughSequence z n ≤ S) :
    Stopped.firstL L
        (rawPhysicalPattern z (Icc 1 S) (movingRoughSequence z n)) =
      CoreSequencePattern.prefixSet (movingRoughSequence z) n L := by
  rw [rawPhysicalPattern_eq_sequencePattern hz]
  exact CoreSequencePattern.pattern_firstL_eq_prefixSet
    (movingRoughSequence_strictMono hz) hL hspan

end
end PrimeGapNormality.Prime.CoreMovingRoughSequence
