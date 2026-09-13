import PrimeGapNormality.Prime.CoreRoughResidueCount
import Mathlib.Tactic.Ring

/-!
# Exact mixed early-avoidance and late-hit CRT counts

Early primes are avoided; at each selected late prime the forbidden set
is hit. The interval error is the actual product of local choice counts.
In particular, a zero early factor is never divided out.
-/

namespace PrimeGapNormality.Prime.CoreRoughMixedCRT

open Finset CoreRoughResidueCount
open scoped Classical
noncomputable section

set_option maxHeartbeats 800000

def hit (B : ∀ p : ℕ, Finset (Fin p)) (p n : ℕ) : Prop :=
  ∃ r ∈ B p, n % p = (r : ℕ)

def avoids (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ P, ¬hit B p n

def hits (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ P, hit B p n

def mixedInterval (B : ∀ p : ℕ, Finset (Fin p)) (P D : Finset ℕ) (a S : ℕ) : Finset ℕ :=
  (Ico a (a + S)).filter (fun n => avoids B P n ∧ hits B D n)

def earlyChoices (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) : ℕ :=
  P.prod (fun p : ℕ => p - (B p).card)

def lateChoices (B : ∀ p : ℕ, Finset (Fin p)) (D : Finset ℕ) : ℕ :=
  ∏ p ∈ D, (B p).card

def mixedLocal (B : ∀ p : ℕ, Finset (Fin p)) (P D : Finset ℕ) : LocalResidues (P ∪ D) :=
  fun p => if p.1 ∈ P then univ \ B p.1 else B p.1

theorem residue_mem_iff_hit (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ)
    (hP : ∀ p : ↥P, Nat.Prime p.1) (n : ℕ) (p : ↥P) :
    residueAt P hP n p ∈ B p.1 ↔ hit B p.1 n := by
  constructor
  · intro h
    exact ⟨residueAt P hP n p, h, rfl⟩
  · rintro ⟨r, hr, hn⟩
    have he : residueAt P hP n p = r := Fin.ext hn
    rwa [he]

theorem mixed_accepts_iff (B : ∀ p : ℕ, Finset (Fin p)) (P D : Finset ℕ)
    (hPD : Disjoint P D) (hprime : ∀ p : ↥(P ∪ D), Nat.Prime p.1) (n : ℕ) :
    Accepts (P ∪ D) hprime (mixedLocal B P D) n ↔ avoids B P n ∧ hits B D n := by
  constructor
  · intro h
    constructor
    · intro p hp
      have hh := h ⟨p, mem_union_left D hp⟩
      have hnot : residueAt (P ∪ D) hprime n ⟨p, mem_union_left D hp⟩ ∉ B p := by
        simpa only [mixedLocal, hp, if_true, mem_sdiff, mem_univ, true_and] using hh
      exact fun hh => hnot ((residue_mem_iff_hit B (P ∪ D) hprime n
        ⟨p, mem_union_left D hp⟩).mpr hh)
    · intro p hp
      have hnP : p ∉ P := fun h => Finset.disjoint_left.mp hPD h hp
      have hh := h ⟨p, mem_union_right P hp⟩
      apply (residue_mem_iff_hit B (P ∪ D) hprime n ⟨p, mem_union_right P hp⟩).mp
      simpa only [mixedLocal, hnP, if_false] using hh
  · rintro ⟨hP, hD⟩ p
    by_cases hp : p.1 ∈ P
    · have hh := hP p.1 hp
      have hnot : residueAt (P ∪ D) hprime n p ∉ B p.1 :=
        fun hm => hh ((residue_mem_iff_hit B (P ∪ D) hprime n p).mp hm)
      simpa only [mixedLocal, hp, if_true, mem_sdiff, mem_univ, true_and] using hnot
    · have hpD : p.1 ∈ D := (mem_union.mp p.2).resolve_left hp
      have hh := hD p.1 hpD
      have hm := (residue_mem_iff_hit B (P ∪ D) hprime n p).mpr hh
      simpa only [mixedLocal, hp, if_false] using hm

theorem mixedInterval_eq_acceptedInterval
    (B : ∀ p : ℕ, Finset (Fin p)) (P D : Finset ℕ)
    (hPD : Disjoint P D) (hprime : ∀ p : ↥(P ∪ D), Nat.Prime p.1) (a S : ℕ) :
    mixedInterval B P D a S = acceptedInterval (P ∪ D) hprime (mixedLocal B P D) a S := by
  ext n
  simp only [mixedInterval, acceptedInterval, mem_filter, mixed_accepts_iff B P D hPD hprime]

theorem mixed_choice_product (B : ∀ p : ℕ, Finset (Fin p)) (P D : Finset ℕ)
    (hPD : Disjoint P D) :
    (∏ p : ↥(P ∪ D), (mixedLocal B P D p).card) =
      earlyChoices B P * lateChoices B D := by
  have hc (p : ↥(P ∪ D)) : (mixedLocal B P D p).card =
      if p.1 ∈ P then p.1 - (B p.1).card else (B p.1).card := by
    by_cases hp : p.1 ∈ P <;>
      simp [mixedLocal, hp, card_sdiff_of_subset (subset_univ (B p.1))]
  simp only [hc]
  have hearly : (∏ p ∈ P, if p ∈ P then p - (B p).card else (B p).card) = earlyChoices B P := by
    apply Finset.prod_congr rfl
    intro p hp
    simp [hp]
  have hlate : (∏ p ∈ D, if p ∈ P then p - (B p).card else (B p).card) = lateChoices B D := by
    apply Finset.prod_congr rfl
    intro p hp
    have hn : p ∉ P := fun h => Finset.disjoint_left.mp hPD h hp
    simp [hn]
  calc
    _ = ∏ p ∈ P ∪ D, (if p ∈ P then p - (B p).card else (B p).card) :=
      Finset.prod_coe_sort (s := P ∪ D)
        (f := fun p : ℕ => if p ∈ P then p - (B p).card else (B p).card)
    _ = _ := by rw [Finset.prod_union hPD, hearly, hlate]

theorem mixedInterval_count_error
    (B : ∀ p : ℕ, Finset (Fin p)) (P D : Finset ℕ)
    (hPD : Disjoint P D) (hprime : ∀ p : ↥(P ∪ D), Nat.Prime p.1) (a S : ℕ) :
    |((mixedInterval B P D a S).card : ℝ) -
      (S : ℝ) / ((∏ p ∈ P, p : ℕ) * (∏ p ∈ D, p : ℕ)) *
        ((earlyChoices B P : ℝ) * (lateChoices B D : ℝ))| ≤
      (earlyChoices B P : ℝ) * (lateChoices B D : ℝ) := by
  have hh := acceptedInterval_count_error (P ∪ D) hprime (mixedLocal B P D) a S
  rw [← mixedInterval_eq_acceptedInterval B P D hPD hprime a S,
    mixed_choice_product B P D hPD] at hh
  simpa only [residueModulus, Finset.prod_union hPD, Nat.cast_mul] using hh

/-- The mixed count vanishes exactly if the early allowed residue product
vanishes. No normalized early measure is introduced. -/
theorem mixedInterval_card_zero_of_earlyChoices_zero
    (B : ∀ p : ℕ, Finset (Fin p)) (P D : Finset ℕ)
    (hPD : Disjoint P D) (hprime : ∀ p : ↥(P ∪ D), Nat.Prime p.1) (a S : ℕ)
    (hzero : earlyChoices B P = 0) : (mixedInterval B P D a S).card = 0 := by
  have hh := mixedInterval_count_error B P D hPD hprime a S
  simp only [hzero, Nat.cast_zero, zero_mul, mul_zero, sub_zero,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (mixedInterval B P D a S).card)] at hh
  have hz : ((mixedInterval B P D a S).card : ℝ) = 0 :=
    le_antisymm hh (Nat.cast_nonneg _)
  exact_mod_cast hz

end
end PrimeGapNormality.Prime.CoreRoughMixedCRT
