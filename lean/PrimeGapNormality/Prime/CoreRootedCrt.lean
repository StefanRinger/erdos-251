import PrimeGapNormality.Prime.StatisticalCriterion
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Concrete CRT coordinates for the finite rooted sieve

The independent nonzero forbidden residues are in bijection with the
nonzero-residue sites of one primorial period. This identifies their uniform
finite averages, with no assumed pushforward law. The center convention here
is `n-c`: a point survives exactly when it avoids the center modulo every
sieving prime. Negating the center gives the paper's `a+n` convention.
-/

open Finset
open scoped BigOperators

namespace PrimeGapNormality.Prime

def coreRootedPeriod (y : ℕ) : ℕ := ∏ p ∈ Nat.primesLE y, p

def coreReducedResidues (y : ℕ) : Finset ℕ :=
  (range (coreRootedPeriod y)).filter fun a =>
    ∀ p ∈ Nat.primesLE y, a % p ≠ 0

private theorem prime_mod_congruence_period {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {a b : ℕ}
    (h : ∀ p ∈ P, a % p = b % p) :
    a % (∏ p ∈ P, p) = b % (∏ p ∈ P, p) := by
  induction P using Finset.induction with
  | empty => simp only [prod_empty, Nat.mod_one]
  | @insert p P hp ih =>
    have hP' : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (mem_insert_of_mem hq)
    have hprime := hP p (mem_insert_self p P)
    have hcop : Nat.Coprime (∏ q ∈ P, q) p := by
      rw [Nat.coprime_prod_left_iff]
      intro q hq
      exact (Nat.coprime_primes (hP' q hq) hprime).mpr fun hqp => hp (hqp ▸ hq)
    rw [prod_insert hp]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mp
      ⟨h p (mem_insert_self p P), ih hP' (fun q hq => h q (mem_insert_of_mem hq))⟩

private theorem coreRootedPrime_ne_zero (y : ℕ) :
    ∀ p ∈ Nat.primesLE y, p ≠ 0 :=
  fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero

private theorem coreRootedPrime_pairwise (y : ℕ) :
    Set.Pairwise (Nat.primesLE y) (Function.onFun Nat.Coprime (fun p : ℕ => p)) := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes (Nat.mem_primesLE.mp hp).2
    (Nat.mem_primesLE.mp hq).2).mpr hpq

/-- The unique representative in one period of the forbidden residue vector. -/
noncomputable def coreRootedCrtCenter (y : ℕ) (σ : ResidueChoice y) : ℕ :=
  (Nat.chineseRemainderOfFinset (residueOfChoice y σ) (fun p : ℕ => p)
    (Nat.primesLE y) (coreRootedPrime_ne_zero y) (coreRootedPrime_pairwise y)).val

theorem coreRootedCrtCenter_lt (y : ℕ) (σ : ResidueChoice y) :
    coreRootedCrtCenter y σ < coreRootedPeriod y :=
  Nat.chineseRemainderOfFinset_lt_prod (residueOfChoice y σ) (fun p : ℕ => p)
    (coreRootedPrime_ne_zero y) (coreRootedPrime_pairwise y)

theorem coreRootedCrtCenter_mod (y : ℕ) (σ : ResidueChoice y)
    {p : ℕ} (hp : p ∈ Nat.primesLE y) :
    coreRootedCrtCenter y σ % p = residueOfChoice y σ p := by
  have h := (Nat.chineseRemainderOfFinset (residueOfChoice y σ) (fun p : ℕ => p)
    (Nat.primesLE y) (coreRootedPrime_ne_zero y) (coreRootedPrime_pairwise y)).property p hp
  have hlt : residueOfChoice y σ p < p := by
    simp only [residueOfChoice, dif_pos hp]
    have hs : (σ ⟨p, hp⟩).val < p - 1 := (σ ⟨p, hp⟩).isLt
    omega
  change coreRootedCrtCenter y σ % p = residueOfChoice y σ p % p at h
  rw [Nat.mod_eq_of_lt hlt] at h
  exact h

theorem coreRootedCrtCenter_mem (y : ℕ) (σ : ResidueChoice y) :
    coreRootedCrtCenter y σ ∈ coreReducedResidues y := by
  apply mem_filter.mpr
  refine ⟨mem_range.mpr (coreRootedCrtCenter_lt y σ), ?_⟩
  intro p hp
  rw [coreRootedCrtCenter_mod y σ hp]
  simp [residueOfChoice, hp]

/-- Decode a reduced residue as the independent forbidden-coordinate vector. -/
def coreRootedChoiceOfResidue (y : ℕ) (a : {a // a ∈ coreReducedResidues y}) :
    ResidueChoice y := fun p =>
  ⟨a.val % p.val - 1, by
    have ha := (mem_filter.mp a.property).2 p.val p.property
    have hp := (Nat.mem_primesLE.mp p.property).2.pos
    have hlt := Nat.mod_lt a.val hp
    omega⟩

theorem coreRootedChoiceOfResidue_decode (y : ℕ)
    (a : {a // a ∈ coreReducedResidues y}) {p : ℕ} (hp : p ∈ Nat.primesLE y) :
    residueOfChoice y (coreRootedChoiceOfResidue y a) p = a.val % p := by
  simp only [residueOfChoice, dif_pos hp, coreRootedChoiceOfResidue]
  have ha := (mem_filter.mp a.property).2 p hp
  omega

theorem coreRootedCrtCenter_choice (y : ℕ)
    (a : {a // a ∈ coreReducedResidues y}) :
    coreRootedCrtCenter y (coreRootedChoiceOfResidue y a) = a.val := by
  have hmod := prime_mod_congruence_period
    (fun p hp => (Nat.mem_primesLE.mp hp).2)
    (fun p hp => (coreRootedCrtCenter_mod y (coreRootedChoiceOfResidue y a) hp).trans
      (coreRootedChoiceOfResidue_decode y a hp))
  have ha : a.val < coreRootedPeriod y := mem_range.mp (mem_filter.mp a.property).1
  change _ % coreRootedPeriod y = _ % coreRootedPeriod y at hmod
  simpa only [Nat.mod_eq_of_lt (coreRootedCrtCenter_lt y _), Nat.mod_eq_of_lt ha] using hmod

theorem coreRootedChoiceOfResidue_center (y : ℕ) (σ : ResidueChoice y) :
    coreRootedChoiceOfResidue y ⟨coreRootedCrtCenter y σ, coreRootedCrtCenter_mem y σ⟩ = σ := by
  funext p
  apply Fin.ext
  change coreRootedCrtCenter y σ % p.val - 1 = (σ p).val
  rw [coreRootedCrtCenter_mod y σ p.property]
  simp [residueOfChoice, p.property]

/-- The actual finite CRT bijection, including y<2 (one empty-coordinate choice). -/
noncomputable def coreRootedCrtEquiv (y : ℕ) :
    ResidueChoice y ≃ {a // a ∈ coreReducedResidues y} where
  toFun σ := ⟨coreRootedCrtCenter y σ, coreRootedCrtCenter_mem y σ⟩
  invFun := coreRootedChoiceOfResidue y
  left_inv := coreRootedChoiceOfResidue_center y
  right_inv a := Subtype.ext (coreRootedCrtCenter_choice y a)

theorem coreRootedCrt_card (y : ℕ) :
    Fintype.card (ResidueChoice y) = (coreReducedResidues y).card := by
  simpa using Fintype.card_congr (coreRootedCrtEquiv y)

/-- Uniform independent residue averages are exactly uniform physical-root
averages under the constructed center bijection. -/
theorem coreRootedCrt_uniform_average (y : ℕ) (f : ℕ → ℝ) :
    (∑ σ : ResidueChoice y, f (coreRootedCrtCenter y σ)) /
        (Fintype.card (ResidueChoice y) : ℝ) =
      (∑ a : {a // a ∈ coreReducedResidues y}, f a.val) /
        ((coreReducedResidues y).card : ℝ) := by
  rw [coreRootedCrt_card]
  congr 1
  exact Equiv.sum_comp (coreRootedCrtEquiv y) (fun a => f a.val)

/-- The center describes the existing rooted sieve predicate literally. -/
theorem coreRootedCrt_sieveSurvives_iff (y : ℕ) (σ : ResidueChoice y) (m : ℕ) :
    sieveSurvives y (residueOfChoice y σ) m ↔
      ∀ p ∈ Nat.primesLE y, m % p ≠ coreRootedCrtCenter y σ % p := by
  unfold sieveSurvives
  constructor <;> intro h p hp
  · simpa only [coreRootedCrtCenter_mod y σ hp] using h p hp
  · simpa only [coreRootedCrtCenter_mod y σ hp] using h p hp

end PrimeGapNormality.Prime
