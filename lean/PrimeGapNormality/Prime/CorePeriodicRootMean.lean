import PrimeGapNormality.Prime.CorePeriodicSurvivors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Rooting an actual periodic survivor enumeration

Translate the explicit periodic enumeration to a chosen survivor. The
translated list is identified with Nat.nth of the translated predicate.
Summing any fixed-rank gap over all possible roots telescopes over one full
period, so its mean is P/card(A), without an assumed stationarity statement.
-/

open Finset
open scoped BigOperators

namespace PrimeGapNormality.Prime

theorem corePeriodicPoint_at_rank (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (i : Fin (n + 1)) :
    corePeriodicPoint P A hcard i.val = A.orderEmbOfFin hcard i := by
  simp [corePeriodicPoint, Nat.div_eq_of_lt i.isLt, Nat.mod_eq_of_lt i.isLt]

theorem corePeriodicPoint_add_period (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (r : ℕ) :
    corePeriodicPoint P A hcard (r + (n + 1)) =
      corePeriodicPoint P A hcard r + P := by
  simp only [corePeriodicPoint, Nat.add_div_right _ (Nat.succ_pos _), Nat.add_mod_right]
  ring

noncomputable def corePeriodicRootPoint (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (i : Fin (n + 1)) (r : ℕ) : ℕ :=
  corePeriodicPoint P A hcard (i.val + r) - A.orderEmbOfFin hcard i

theorem corePeriodicRootPoint_base_le (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) (i : Fin (n + 1)) (r : ℕ) :
    A.orderEmbOfFin hcard i ≤ corePeriodicPoint P A hcard (i.val + r) := by
  rw [← corePeriodicPoint_at_rank P A hcard i]
  exact (corePeriodicPoint_strictMono P A hcard hA).monotone (Nat.le_add_right _ _)

theorem corePeriodicRootPoint_strictMono (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) (i : Fin (n + 1)) :
    StrictMono (corePeriodicRootPoint P A hcard i) := by
  intro r s hrs
  have h := (corePeriodicPoint_strictMono P A hcard hA) (Nat.add_lt_add_left hrs i.val)
  have hb := corePeriodicRootPoint_base_le P A hcard hA i r
  unfold corePeriodicRootPoint
  omega

theorem corePeriodicRootPoint_range (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) (i : Fin (n + 1)) :
    Set.range (corePeriodicRootPoint P A hcard i) =
      {m : ℕ | (A.orderEmbOfFin hcard i + m) % P ∈ A} := by
  have hmono := corePeriodicPoint_strictMono P A hcard hA
  have hrange := corePeriodicPoint_range P A hcard hA
  ext m
  constructor
  · rintro ⟨r, rfl⟩
    change (A.orderEmbOfFin hcard i +
      (corePeriodicPoint P A hcard (i.val + r) - A.orderEmbOfFin hcard i)) % P ∈ A
    rw [Nat.add_sub_of_le (corePeriodicRootPoint_base_le P A hcard hA i r)]
    rw [corePeriodicPoint_mod P A hcard hA]
    exact A.orderEmbOfFin_mem hcard _
  · intro hm
    have hm' : (A.orderEmbOfFin hcard i + m) ∈
        Set.range (corePeriodicPoint P A hcard) := by
      rw [hrange]
      exact hm
    obtain ⟨j, hj⟩ := hm'
    have hij : i.val ≤ j := by
      apply hmono.le_iff_le.mp
      rw [corePeriodicPoint_at_rank P A hcard i, hj]
      exact Nat.le_add_right _ _
    refine ⟨j - i.val, ?_⟩
    unfold corePeriodicRootPoint
    rw [Nat.add_sub_of_le hij, hj, Nat.add_sub_cancel_left]

/-- Nat.nth of the translated periodic set equals the translated actual
ordered enumeration, with subtraction justified by the base bound. -/
theorem corePeriodicRootPoint_eq_nth (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) (i : Fin (n + 1)) (r : ℕ) :
    corePeriodicRootPoint P A hcard i r =
      Nat.nth (fun m => (A.orderEmbOfFin hcard i + m) % P ∈ A) r := by
  have hmono := corePeriodicRootPoint_strictMono P A hcard hA i
  have hrange := corePeriodicRootPoint_range P A hcard hA i
  have hinf : Set.Infinite {m : ℕ | (A.orderEmbOfFin hcard i + m) % P ∈ A} := by
    rw [← hrange]
    exact Set.infinite_range_of_injective hmono.injective
  have heq := (hmono.range_inj (Nat.nth_strictMono hinf)).mp
    (hrange.trans (Nat.range_nth_of_infinite hinf).symm)
  exact congrFun heq r

/-- Sum of the physical rank-r gaps over every possible sorted root is P. -/
theorem corePeriodicRootPoint_gap_sum (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) (r : ℕ) :
    (∑ i : Fin (n + 1),
      ((corePeriodicRootPoint P A hcard i (r + 1) : ℝ) -
        (corePeriodicRootPoint P A hcard i r : ℝ))) = (P : ℝ) := by
  have hterm (i : Fin (n + 1)) :
      ((corePeriodicRootPoint P A hcard i (r + 1) : ℝ) -
        (corePeriodicRootPoint P A hcard i r : ℝ)) =
      (corePeriodicPoint P A hcard (r + (i.val + 1)) : ℝ) -
        (corePeriodicPoint P A hcard (r + i.val) : ℝ) := by
    unfold corePeriodicRootPoint
    rw [Nat.cast_sub (corePeriodicRootPoint_base_le P A hcard hA i (r + 1)),
      Nat.cast_sub (corePeriodicRootPoint_base_le P A hcard hA i r)]
    simp only [Nat.add_comm i.val, Nat.add_assoc]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_range (fun j =>
    (corePeriodicPoint P A hcard (r + (j + 1)) : ℝ) -
      (corePeriodicPoint P A hcard (r + j) : ℝ))]
  rw [sum_range_sub (fun j => (corePeriodicPoint P A hcard (r + j) : ℝ)),
    Nat.add_zero, corePeriodicPoint_add_period, Nat.cast_add]
  ring

/-- Exact physical first-moment identity at every rank for uniform roots. -/
theorem corePeriodicRootPoint_gap_mean (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) (r : ℕ) :
    (∑ i : Fin (n + 1),
      ((corePeriodicRootPoint P A hcard i (r + 1) : ℝ) -
        (corePeriodicRootPoint P A hcard i r : ℝ))) / (A.card : ℝ) =
      (P : ℝ) / (A.card : ℝ) := by
  rw [corePeriodicRootPoint_gap_sum P A hcard hA]

end PrimeGapNormality.Prime
