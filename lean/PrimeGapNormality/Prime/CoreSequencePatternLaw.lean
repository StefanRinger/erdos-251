import PrimeGapNormality.Prime.CoreSequencePattern
import PrimeGapNormality.Prime.CoreSequenceResiduePassage

/-!
# The finite rooted-pattern law of an arbitrary increasing sequence

This is the sequence-generic counterpart of the finite prime-pattern
pushforward.  Its sample space is the actual index window `seqWindow a X`;
membership of a translated point is expressed by `Set.range a`, never by a
prime predicate.  Every statement is an exact finite identity, including the
empty-window case.  No density, sieve, or limiting assertion occurs here.
-/

namespace PrimeGapNormality.Prime.CoreSequencePatternLaw

open Finset CoreSequencePattern
open scoped Classical

noncomputable section

/-- The rooted configuration seen from the sequence point `a n`. -/
def rootedPattern (a : ℕ → ℕ) (Ω : Finset ℕ) (n : ℕ) : Finset ℕ :=
  pattern a Ω (a n)

/-- The actual finite pushforward mass of rooted configurations.  Division
by an empty window is Lean's exact division by zero, hence gives zero. -/
def patternMass (a : ℕ → ℕ) (X : ℕ) (Ω U : Finset ℕ) : ℝ :=
  (∑ n ∈ seqWindow a X,
      if rootedPattern a Ω n = U then (1 : ℝ) else 0) /
    ((seqWindow a X).card : ℝ)

/-- Actual rooted tuple count, formulated solely through membership in the
range of the sequence. -/
def rootedTupleCount (a : ℕ → ℕ) (X : ℕ) (H : Finset ℕ) : ℕ :=
  ((seqWindow a X).filter
    (fun n ↦ ∀ h ∈ H, a n + h ∈ Set.range a)).card

theorem rootedPattern_mem (a : ℕ → ℕ) (Ω : Finset ℕ) (n : ℕ) :
    rootedPattern a Ω n ∈ Ω.powerset :=
  mem_powerset.mpr (filter_subset _ _)

theorem patternMass_nonneg (a : ℕ → ℕ) (X : ℕ) (Ω U : Finset ℕ) :
    0 ≤ patternMass a X Ω U := by
  unfold patternMass
  exact div_nonneg (sum_nonneg (fun _ _ ↦ by split_ifs <;> norm_num))
    (Nat.cast_nonneg _)

/-- Exact finite pushforward evaluation, including an empty denominator. -/
theorem patternMass_eval (a : ℕ → ℕ) (X : ℕ) (Ω : Finset ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ U ∈ Ω.powerset, patternMass a X Ω U * f U) =
      (∑ n ∈ seqWindow a X, f (rootedPattern a Ω n)) /
        ((seqWindow a X).card : ℝ) := by
  unfold patternMass
  simp_rw [div_mul_eq_mul_div, sum_mul]
  rw [← sum_div, sum_comm]
  congr 1
  apply sum_congr rfl
  intro n hn
  simp only [ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq, if_pos (rootedPattern_mem a Ω n)]

theorem patternMass_total {a : ℕ → ℕ} {X : ℕ} (Ω : Finset ℕ)
    (hN : 0 < (seqWindow a X).card) :
    ∑ U ∈ Ω.powerset, patternMass a X Ω U = 1 := by
  have h := patternMass_eval a X Ω (fun _ ↦ 1)
  have hden : (((seqWindow a X).card : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simpa only [mul_one, sum_const, nsmul_one, div_self hden] using h

theorem subset_rootedPattern_iff {a : ℕ → ℕ} {Ω H : Finset ℕ}
    (hH : H ⊆ Ω) (n : ℕ) :
    H ⊆ rootedPattern a Ω n ↔
      ∀ h ∈ H, a n + h ∈ Set.range a := by
  constructor
  · intro hsub h hh
    have hm := mem_filter.mp (hsub hh)
    obtain ⟨i, hi⟩ := hm.2
    exact ⟨i, hi⟩
  · intro hrange h hh
    obtain ⟨i, hi⟩ := hrange h hh
    exact mem_filter.mpr ⟨hH hh, ⟨i, hi⟩⟩

/-- Inclusion masses of the pushforward law are the literal rooted tuple
counts divided by the actual sequence-window cardinality. -/
theorem patternMass_inclusion
    (a : ℕ → ℕ) (X : ℕ) {Ω H : Finset ℕ} (hH : H ⊆ Ω) :
    Stopped.inclusionMass Ω (patternMass a X Ω) H =
      (rootedTupleCount a X H : ℝ) / ((seqWindow a X).card : ℝ) := by
  have h := patternMass_eval a X Ω (fun U ↦ if H ⊆ U then 1 else 0)
  have hleft :
      (∑ U ∈ Ω.powerset,
          patternMass a X Ω U * (if H ⊆ U then 1 else 0)) =
        Stopped.inclusionMass Ω (patternMass a X Ω) H := by
    simp [Stopped.inclusionMass, sum_filter]
  rw [hleft] at h
  rw [h]
  congr 1
  simp_rw [subset_rootedPattern_iff hH]
  rw [sum_boole]
  rfl

/-- Pure finite disintegration of a first-`L` shape test. -/
theorem firstL_test_eq_pushforward
    (Ω : Finset ℕ) (μ : Finset ℕ → ℝ) (L : ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ K ∈ Ω.powerset.filter (fun K ↦ K.card = L),
      f K * Stopped.shortShapeMass Ω μ L K) =
    ∑ U ∈ Ω.powerset, μ U *
      if L ≤ U.card then f (Stopped.firstL L U) else 0 := by
  unfold Stopped.shortShapeMass
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro U hU
  by_cases hcard : L ≤ U.card
  · have hmem :
        Stopped.firstL L U ∈ Ω.powerset.filter (fun K ↦ K.card = L) :=
      mem_filter.mpr ⟨mem_powerset.mpr
        (Stopped.firstL_subset.trans (mem_powerset.mp hU)),
          Stopped.firstL_card hcard⟩
    simp only [hcard, true_and, if_true, mul_ite, mul_zero]
    rw [sum_ite_eq, if_pos hmem, mul_comm]
  · simp [hcard]

/-- Failure is exactly the empirical indicator that the first `L`-point
physical span exceeds `S`. -/
theorem failureMass_eq_span
    {a : ℕ → ℕ} (ha : StrictMono a) (X S : ℕ) {L : ℕ}
    (hL : 1 ≤ L) :
    Stopped.failureMass (Icc 1 S) (patternMass a X (Icc 1 S)) L =
      (∑ n ∈ seqWindow a X,
        if a (n + L) - a n ≤ S then (0 : ℝ) else 1) /
          ((seqWindow a X).card : ℝ) := by
  have hleft :
      Stopped.failureMass (Icc 1 S) (patternMass a X (Icc 1 S)) L =
        ∑ U ∈ (Icc 1 S).powerset,
          patternMass a X (Icc 1 S) U * if U.card < L then 1 else 0 := by
    simp [Stopped.failureMass, sum_filter]
  rw [hleft, patternMass_eval]
  congr 1
  apply sum_congr rfl
  intro n hn
  by_cases hspan : a (n + L) - a n ≤ S
  · have hcard := (pattern_card_ge_iff_span ha hL).mpr hspan
    simp [rootedPattern, hspan, Nat.not_lt_of_ge hcard]
  · have hcard : (rootedPattern a (Icc 1 S) n).card < L :=
      Nat.lt_of_not_ge (fun hc ↦
        hspan ((pattern_card_ge_iff_span ha hL).mp hc))
    simp [hspan, hcard]

/-- The successful first-`L` pushforward is literally the consecutive
prefix-offset set of the original sequence. -/
theorem firstL_test_eq_prefix_average
    {a : ℕ → ℕ} (ha : StrictMono a) (X S : ℕ) {L : ℕ}
    (hL : 1 ≤ L) (f : Finset ℕ → ℝ) :
    (∑ K ∈ (Icc 1 S).powerset.filter (fun K ↦ K.card = L),
      f K * Stopped.shortShapeMass (Icc 1 S)
        (patternMass a X (Icc 1 S)) L K) =
      (∑ n ∈ seqWindow a X,
        if a (n + L) - a n ≤ S then f (prefixSet a n L) else 0) /
          ((seqWindow a X).card : ℝ) := by
  rw [firstL_test_eq_pushforward, patternMass_eval]
  congr 1
  apply sum_congr rfl
  intro n hn
  by_cases hspan : a (n + L) - a n ≤ S
  · have hcard : L ≤ (rootedPattern a (Icc 1 S) n).card :=
      (pattern_card_ge_iff_span ha hL).mpr hspan
    simp only [if_pos hcard, if_pos hspan]
    exact congrArg f (pattern_firstL_eq_prefixSet ha hL hspan)
  · have hcard : ¬ L ≤ (rootedPattern a (Icc 1 S) n).card :=
      fun hc ↦ hspan ((pattern_card_ge_iff_span ha hL).mp hc)
    rw [if_neg hcard, if_neg hspan]

/-- Generic finite positive test bound.  A failed physical span is charged
before the first-`L` law is used; no sequence distribution input appears. -/
theorem positive_firstL_window_le
    {a : ℕ → ℕ} (ha : StrictMono a) (X S : ℕ) {L : ℕ}
    (hL : 1 ≤ L) (f : Finset ℕ → ℝ) {C : ℝ}
    (hf : ∀ K, f K ≤ C) :
    windowAvgReal (seqWindow a X) (fun n ↦ f (prefixSet a n L)) ≤
      C * Stopped.failureMass (Icc 1 S)
          (patternMass a X (Icc 1 S)) L +
        ∑ K ∈ (Icc 1 S).powerset.filter (fun K ↦ K.card = L),
          f K * Stopped.shortShapeMass (Icc 1 S)
            (patternMass a X (Icc 1 S)) L K := by
  rw [failureMass_eq_span ha X S hL,
    firstL_test_eq_prefix_average ha X S hL]
  unfold windowAvgReal
  rw [← mul_div_assoc, ← add_div, mul_sum, ← sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro n hn
  by_cases hspan : a (n + L) - a n ≤ S
  · simp [hspan]
  · simp only [hspan, if_false, mul_one, add_zero]
    exact hf _

end
end PrimeGapNormality.Prime.CoreSequencePatternLaw
