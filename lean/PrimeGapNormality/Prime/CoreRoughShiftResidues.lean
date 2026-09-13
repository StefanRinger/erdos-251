import PrimeGapNormality.Prime.CoreRoughMixedCRT
import PrimeGapNormality.Prime.CoreMovingRoughSequence
import Mathlib.Data.Nat.ModEq

/-!
# Forbidden residues for translated rough tuples

For a finite shift set `E`, the forbidden residues at `p` are exactly the
classes `r` for which some translate `r+h` vanishes modulo `p`.  This file
identifies the generic mixed-CRT predicates with literal divisibility of the
translated integers.  It is deterministic finite arithmetic: no sieve
asymptotic or density statement is made.
-/

namespace PrimeGapNormality.Prime

namespace CoreMovingRoughSequence

/-- Fixed-cutoff roughness.  This is the constant-threshold specialization
of `IsMovingRough`. -/
def RoughAt (z n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → z < p

theorem isMovingRough_const_iff (z n : ℕ) :
    IsMovingRough (fun _ ↦ z) n ↔ RoughAt z n :=
  Iff.rfl

end CoreMovingRoughSequence

namespace CoreRoughShiftResidues

open Finset
open scoped Classical

noncomputable section

/-- Residues at which at least one translate by `E` is divisible by `p`. -/
def forbiddenResidues (E : Finset ℕ) (p : ℕ) : Finset (Fin p) :=
  Finset.univ.filter (fun r ↦ ∃ h ∈ E, (r.val + h) % p = 0)

theorem mem_forbiddenResidues {E : Finset ℕ} {p : ℕ} {r : Fin p} :
    r ∈ forbiddenResidues E p ↔ ∃ h ∈ E, (r.val + h) % p = 0 := by
  simp [forbiddenResidues]

/-- The generic mixed-CRT hit predicate is literal divisibility of one
translate. -/
theorem hit_forbiddenResidues_iff
    (E : Finset ℕ) {p n : ℕ} (hp : Nat.Prime p) :
    CoreRoughMixedCRT.hit (forbiddenResidues E) p n ↔
      ∃ h ∈ E, p ∣ n + h := by
  constructor
  · rintro ⟨r, hr, hn⟩
    obtain ⟨h, hE, hrh⟩ := mem_forbiddenResidues.mp hr
    refine ⟨h, hE, Nat.dvd_iff_mod_eq_zero.mpr ?_⟩
    have heq := Nat.add_mod r.val h p
    rw [Nat.mod_eq_of_lt r.isLt] at heq
    calc
      (n + h) % p = (n % p + h % p) % p := Nat.add_mod n h p
      _ = (r.val + h % p) % p := by rw [hn]
      _ = (r.val + h) % p := heq.symm
      _ = 0 := hrh
  · rintro ⟨h, hE, hdiv⟩
    let r : Fin p := ⟨n % p, Nat.mod_lt n hp.pos⟩
    refine ⟨r, mem_forbiddenResidues.mpr ⟨h, hE, ?_⟩, rfl⟩
    have hmod := Nat.dvd_iff_mod_eq_zero.mp hdiv
    simpa only [r, Nat.add_mod, Nat.mod_mod] using hmod

/-- There are at most `|E|` forbidden classes.  The proof chooses one shift
for each forbidden residue; a fixed shift cannot witness two different
residues. -/
theorem card_forbiddenResidues_le
    (E : Finset ℕ) {p : ℕ} (hp : Nat.Prime p) :
    (forbiddenResidues E p).card ≤ E.card := by
  let pick : ↥(forbiddenResidues E p) → ↥E := fun r ↦
    ⟨Classical.choose (mem_forbiddenResidues.mp r.2),
      (Classical.choose_spec (mem_forbiddenResidues.mp r.2)).1⟩
  have hpick (r : ↥(forbiddenResidues E p)) :
      (r.1.val + (pick r).1) % p = 0 :=
    (Classical.choose_spec (mem_forbiddenResidues.mp r.2)).2
  have hinj : Function.Injective pick := by
    intro r s hrs
    have hshift : (pick r).1 = (pick s).1 := congrArg Subtype.val hrs
    have hrmod : Nat.ModEq p (r.1.val + (pick r).1) 0 := by
      change (r.1.val + (pick r).1) % p = 0 % p
      simpa only [Nat.zero_mod] using hpick r
    have hsmod : Nat.ModEq p (s.1.val + (pick r).1) 0 := by
      change (s.1.val + (pick r).1) % p = 0 % p
      rw [hshift]
      simpa only [Nat.zero_mod] using hpick s
    have hrsmod : Nat.ModEq p r.1.val s.1.val :=
      Nat.ModEq.add_right_cancel' (pick r).1 (hrmod.trans hsmod.symm)
    apply Subtype.ext
    apply Fin.ext
    change r.1.val = s.1.val
    unfold Nat.ModEq at hrsmod
    simpa only [Nat.mod_eq_of_lt r.1.isLt, Nat.mod_eq_of_lt s.1.isLt] using hrsmod
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective pick hinj

/-- A covering local residue set can occur only at a prime no larger than
the number of shifts. -/
theorem le_card_of_forbiddenResidues_eq_univ
    (E : Finset ℕ) {p : ℕ} (hp : Nat.Prime p)
    (hfull : forbiddenResidues E p = Finset.univ) :
    p ≤ E.card := by
  have hcard := card_forbiddenResidues_le E hp
  rw [hfull, card_univ, Fintype.card_fin] at hcard
  exact hcard

/-- Avoiding all forbidden classes through `y` is exactly simultaneous
avoidance of every prime divisor through `y` by every translate. -/
theorem avoids_forbiddenResidues_iff
    (E : Finset ℕ) (y n : ℕ) :
    CoreRoughMixedCRT.avoids (forbiddenResidues E) (Nat.primesLE y) n ↔
      ∀ h ∈ E, ∀ p : ℕ, Nat.Prime p → p ≤ y → ¬ p ∣ n + h := by
  constructor
  · intro havoid h hE p hp hpy hdiv
    have hpMem : p ∈ Nat.primesLE y := Nat.mem_primesLE.mpr ⟨hpy, hp⟩
    exact havoid p hpMem ((hit_forbiddenResidues_iff E hp).mpr ⟨h, hE, hdiv⟩)
  · intro hrough p hpMem hhit
    have hp : Nat.Prime p := Nat.prime_of_mem_primesLE hpMem
    have hpy : p ≤ y := (Nat.mem_primesLE.mp hpMem).1
    obtain ⟨h, hE, hdiv⟩ := (hit_forbiddenResidues_iff E hp).mp hhit
    exact hrough h hE p hp hpy hdiv

/-- One covering prime below the cutoff makes the avoidance predicate
identically false. -/
theorem not_avoids_of_local_full
    (E : Finset ℕ) {y p n : ℕ} (hp : Nat.Prime p) (hpy : p ≤ y)
    (hfull : forbiddenResidues E p = Finset.univ) :
    ¬ CoreRoughMixedCRT.avoids
        (forbiddenResidues E) (Nat.primesLE y) n := by
  intro havoid
  have hpMem : p ∈ Nat.primesLE y := Nat.mem_primesLE.mpr ⟨hpy, hp⟩
  apply havoid p hpMem
  refine ⟨⟨n % p, Nat.mod_lt n hp.pos⟩, ?_, rfl⟩
  rw [hfull]
  exact mem_univ _

/-- The actual finite interval selected by simultaneous translated
fixed-cutoff roughness. -/
def translatedRoughInterval
    (E : Finset ℕ) (y a H : ℕ) : Finset ℕ :=
  (Ico a (a + H)).filter
    (fun n ↦ ∀ h ∈ E, CoreMovingRoughSequence.RoughAt y (n + h))

/-- The same interval written in the generic mixed-CRT avoidance language. -/
def avoidedInterval (E : Finset ℕ) (y a H : ℕ) : Finset ℕ :=
  (Ico a (a + H)).filter
    (CoreRoughMixedCRT.avoids (forbiddenResidues E) (Nat.primesLE y))

theorem avoidedInterval_eq_translatedRoughInterval
    (E : Finset ℕ) (y a H : ℕ) (ha : 1 ≤ a) :
    avoidedInterval E y a H = translatedRoughInterval E y a H := by
  ext n
  simp only [avoidedInterval, translatedRoughInterval, mem_filter]
  apply and_congr_right
  intro hn
  rw [avoids_forbiddenResidues_iff]
  constructor
  · intro havoid h hE
    have han : a ≤ n := (mem_Ico.mp hn).1
    refine ⟨by omega, ?_⟩
    intro p hp hdiv
    by_contra hnot
    exact havoid h hE p hp (Nat.not_lt.mp hnot) hdiv
  · intro hrough h hE p hp hpy hdiv
    exact (not_lt_of_ge hpy) ((hrough h hE).2 p hp hdiv)

/-- A local covering prime makes the literal translated rough interval, and
hence its count, vanish exactly. -/
theorem translatedRoughInterval_eq_empty_of_local_full
    (E : Finset ℕ) {y p a H : ℕ} (ha : 1 ≤ a)
    (hp : Nat.Prime p) (hpy : p ≤ y)
    (hfull : forbiddenResidues E p = Finset.univ) :
    translatedRoughInterval E y a H = ∅ := by
  rw [← avoidedInterval_eq_translatedRoughInterval E y a H ha]
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  exact not_avoids_of_local_full E hp hpy hfull (mem_filter.mp hn).2

theorem translatedRoughInterval_card_eq_zero_of_local_full
    (E : Finset ℕ) {y p a H : ℕ} (ha : 1 ≤ a)
    (hp : Nat.Prime p) (hpy : p ≤ y)
    (hfull : forbiddenResidues E p = Finset.univ) :
    (translatedRoughInterval E y a H).card = 0 := by
  rw [translatedRoughInterval_eq_empty_of_local_full E ha hp hpy hfull,
    card_empty]

end
end CoreRoughShiftResidues
end PrimeGapNormality.Prime
