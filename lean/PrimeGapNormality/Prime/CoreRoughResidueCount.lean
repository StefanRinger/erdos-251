import PrimeGapNormality.Prime.SelbergCrtInterval
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Exact finite counts with several forbidden residue sets

This is the elementary CRT layer of the rough-number sieve, before any
upper or lower beta weights.  For pairwise distinct prime moduli, a choice
of one allowed residue at every prime determines one residue modulo the
product.  Summing the honest one-class interval error gives a remainder at
most the product of the local numbers of choices.

No fundamental-lemma, beta-sieve, moving-cutoff, or asymptotic statement is
assumed or proved here.
-/

namespace PrimeGapNormality.Prime.CoreRoughResidueCount

open Finset
open scoped BigOperators Classical Function

noncomputable section

/-- Product of the distinct prime moduli. -/
def residueModulus (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

/-- One finite set of accepted residue classes at every prime in `P`. -/
abbrev LocalResidues (P : Finset ℕ) :=
  ∀ p : ↥P, Finset (Fin p.1)

/-- A simultaneous selection of one accepted local residue at every prime. -/
abbrev ResidueVector (P : Finset ℕ) (A : LocalResidues P) :=
  ∀ p : ↥P, ↥(A p)

private theorem primeModuli_ne_zero (P : Finset ℕ)
    (hP : ∀ p : ↥P, Nat.Prime p.1) :
    ∀ p ∈ (univ : Finset ↥P), p.1 ≠ 0 := by
  intro p _
  exact (hP p).ne_zero

private theorem primeModuli_pairwise (P : Finset ℕ)
    (hP : ∀ p : ↥P, Nat.Prime p.1) :
    Set.Pairwise (univ : Finset ↥P)
      (Function.onFun Nat.Coprime (fun p : ↥P ↦ p.1)) := by
  intro p _ q _ hpq
  apply (Nat.coprime_primes (hP p) (hP q)).mpr
  intro hpqv
  exact hpq (Subtype.ext hpqv)

/-- The CRT representative of a vector of accepted local residues. -/
def crtCenter (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (σ : ResidueVector P A) : ℕ :=
  (Nat.chineseRemainderOfFinset
    (fun p : ↥P ↦ ((σ p).1 : ℕ)) (fun p : ↥P ↦ p.1) univ
    (primeModuli_ne_zero P hP) (primeModuli_pairwise P hP)).1

theorem crtCenter_lt (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (σ : ResidueVector P A) :
    crtCenter P hP A σ < residueModulus P := by
  have h := Nat.chineseRemainderOfFinset_lt_prod
    (fun p : ↥P ↦ ((σ p).1 : ℕ)) (fun p : ↥P ↦ p.1)
    (primeModuli_ne_zero P hP) (primeModuli_pairwise P hP)
  have h' : crtCenter P hP A σ < ∏ p : ↥P, p.1 := by
    simpa only [crtCenter] using h
  rw [residueModulus, ← Finset.prod_coe_sort]
  exact h'

theorem crtCenter_mod (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (σ : ResidueVector P A) (p : ↥P) :
    crtCenter P hP A σ % p.1 = ((σ p).1 : ℕ) := by
  have h := (Nat.chineseRemainderOfFinset
    (fun q : ↥P ↦ ((σ q).1 : ℕ)) (fun q : ↥P ↦ q.1) univ
    (primeModuli_ne_zero P hP) (primeModuli_pairwise P hP)).property p (mem_univ p)
  have h' : crtCenter P hP A σ % p.1 = ((σ p).1 : ℕ) % p.1 := by
    simpa only [crtCenter, Nat.ModEq] using h
  rw [Nat.mod_eq_of_lt (σ p).1.isLt] at h'
  exact h'

theorem crtCenter_injective (P : Finset ℕ)
    (hP : ∀ p : ↥P, Nat.Prime p.1) (A : LocalResidues P) :
    Function.Injective (crtCenter P hP A) := by
  intro σ τ hστ
  funext p
  apply Subtype.ext
  apply Fin.ext
  have hσ := crtCenter_mod P hP A σ p
  have hτ := crtCenter_mod P hP A τ p
  exact hσ.symm.trans ((congrArg (fun z : ℕ ↦ z % p.1) hστ).trans hτ)

/-- All accepted residue vectors, represented in one product period. -/
def crtResidues (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) : Finset ℕ :=
  univ.image (crtCenter P hP A)

theorem crtResidues_card (P : Finset ℕ)
    (hP : ∀ p : ↥P, Nat.Prime p.1) (A : LocalResidues P) :
    (crtResidues P hP A).card = ∏ p : ↥P, (A p).card := by
  rw [crtResidues, card_image_of_injective _ (crtCenter_injective P hP A),
    card_univ, Fintype.card_pi]
  simp only [Fintype.card_coe]

theorem crtResidue_lt (P : Finset ℕ)
    (hP : ∀ p : ↥P, Nat.Prime p.1) (A : LocalResidues P)
    {c : ℕ} (hc : c ∈ crtResidues P hP A) :
    c < residueModulus P := by
  obtain ⟨σ, _, rfl⟩ := mem_image.mp hc
  exact crtCenter_lt P hP A σ

private theorem prime_mod_congruence_product {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {a b : ℕ}
    (h : ∀ p ∈ P, a % p = b % p) :
    a % (∏ p ∈ P, p) = b % (∏ p ∈ P, p) := by
  induction P using Finset.induction with
  | empty => simp only [prod_empty, Nat.mod_one]
  | @insert p P hp ih =>
    have hP' : ∀ q ∈ P, Nat.Prime q :=
      fun q hq ↦ hP q (mem_insert_of_mem hq)
    have hprime := hP p (mem_insert_self p P)
    have hcop : Nat.Coprime (∏ q ∈ P, q) p := by
      rw [Nat.coprime_prod_left_iff]
      intro q hq
      exact (Nat.coprime_primes (hP' q hq) hprime).mpr
        (fun hqp ↦ hp (hqp ▸ hq))
    rw [prod_insert hp]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mp
      ⟨h p (mem_insert_self p P),
        ih hP' (fun q hq ↦ h q (mem_insert_of_mem hq))⟩

/-- The canonical residue of `n` at one prime modulus. -/
def residueAt (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (n : ℕ) (p : ↥P) : Fin p.1 :=
  ⟨n % p.1, Nat.mod_lt n (hP p).pos⟩

/-- Simultaneous membership in all prescribed local residue sets. -/
def Accepts (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (n : ℕ) : Prop :=
  ∀ p : ↥P, residueAt P hP n p ∈ A p

theorem mod_residueModulus_eq_crtCenter_iff
    (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (n : ℕ) (σ : ResidueVector P A) :
    n % residueModulus P = crtCenter P hP A σ ↔
      ∀ p : ↥P, residueAt P hP n p = (σ p).1 := by
  constructor
  · intro hn p
    apply Fin.ext
    have hpdiv : p.1 ∣ residueModulus P := by
      unfold residueModulus
      exact dvd_prod_of_mem (fun q : ℕ ↦ q) p.2
    calc
      n % p.1 = (n % residueModulus P) % p.1 :=
        (Nat.mod_mod_of_dvd n hpdiv).symm
      _ = crtCenter P hP A σ % p.1 :=
        congrArg (fun z : ℕ ↦ z % p.1) hn
      _ = ((σ p).1 : ℕ) := crtCenter_mod P hP A σ p
  · intro hn
    have hmods : ∀ p ∈ P, n % p = crtCenter P hP A σ % p := by
      intro p hp
      let q : ↥P := ⟨p, hp⟩
      have hq := congrArg Fin.val (hn q)
      simpa only [residueAt, q] using hq.trans (crtCenter_mod P hP A σ q).symm
    have hglobal := prime_mod_congruence_product
      (fun p hp ↦ hP ⟨p, hp⟩) hmods
    change n % residueModulus P =
      crtCenter P hP A σ % residueModulus P at hglobal
    rw [Nat.mod_eq_of_lt (crtCenter_lt P hP A σ)] at hglobal
    exact hglobal

theorem accepts_iff_mod_mem_crtResidues
    (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (n : ℕ) :
    Accepts P hP A n ↔ n % residueModulus P ∈ crtResidues P hP A := by
  constructor
  · intro hn
    let σ : ResidueVector P A := fun p ↦ ⟨residueAt P hP n p, hn p⟩
    apply mem_image.mpr
    refine ⟨σ, mem_univ _, ?_⟩
    exact ((mod_residueModulus_eq_crtCenter_iff P hP A n σ).2
      (fun p ↦ rfl)).symm
  · intro hn p
    obtain ⟨σ, _, hσ⟩ := mem_image.mp hn
    have hlocal :=
      (mod_residueModulus_eq_crtCenter_iff P hP A n σ).1 hσ.symm
    rw [hlocal p]
    exact (σ p).2

/-- Actual accepted integers in a consecutive block. -/
def acceptedInterval (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (a S : ℕ) : Finset ℕ :=
  (Ico a (a + S)).filter (Accepts P hP A)

private def residueFiber (P : Finset ℕ) (a S c : ℕ) : Finset ℕ :=
  (Ico a (a + S)).filter (fun n ↦ n % residueModulus P = c)

private theorem acceptedInterval_eq_biUnion
    (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (a S : ℕ) :
    acceptedInterval P hP A a S =
      (crtResidues P hP A).biUnion (residueFiber P a S) := by
  ext n
  simp only [acceptedInterval, residueFiber, mem_filter, mem_biUnion]
  constructor
  · rintro ⟨hnI, hn⟩
    exact ⟨n % residueModulus P,
      (accepts_iff_mod_mem_crtResidues P hP A n).1 hn, hnI, rfl⟩
  · rintro ⟨c, hc, hnI, hnc⟩
    have hnmem : n % residueModulus P ∈ crtResidues P hP A := by
      rw [hnc]
      exact hc
    exact ⟨hnI, (accepts_iff_mod_mem_crtResidues P hP A n).2 hnmem⟩

private theorem residueFiber_pairwise
    (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (a S : ℕ) :
    Set.PairwiseDisjoint (crtResidues P hP A : Set ℕ)
      (residueFiber P a S) := by
  intro c _ d _ hcd
  apply Finset.disjoint_left.mpr
  intro n hnc hnd
  have hc := (mem_filter.mp hnc).2
  have hd := (mem_filter.mp hnd).2
  exact hcd (hc.symm.trans hd)

private theorem acceptedInterval_card_eq_sum
    (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (a S : ℕ) :
    (acceptedInterval P hP A a S).card =
      ∑ c ∈ crtResidues P hP A, (residueFiber P a S c).card := by
  rw [acceptedInterval_eq_biUnion,
    card_biUnion (residueFiber_pairwise P hP A a S)]

private theorem residueModulus_pos (P : Finset ℕ)
    (hP : ∀ p : ↥P, Nat.Prime p.1) :
    0 < residueModulus P := by
  unfold residueModulus
  exact prod_pos fun p hp ↦ (hP ⟨p, hp⟩).pos

private theorem residueFiber_error
    (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (a S : ℕ) {c : ℕ}
    (hc : c ∈ crtResidues P hP A) :
    |((residueFiber P a S c).card : ℝ) -
        (S : ℝ) / residueModulus P| ≤ 1 := by
  have h := selbergCrt_card_mod_abs_le a S (residueModulus P) c
    (residueModulus_pos P hP)
  simpa only [residueFiber, Nat.mod_eq_of_lt (crtResidue_lt P hP A hc)] using h

/-- Exact finite multi-residue count.  Its main term is the product of the
local numbers of accepted residues divided by the prime product; the entire
interval-rounding remainder is at most that same product of local counts. -/
theorem acceptedInterval_count_error
    (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (A : LocalResidues P) (a S : ℕ) :
    |((acceptedInterval P hP A a S).card : ℝ) -
        (S : ℝ) / residueModulus P *
          (∏ p : ↥P, (A p).card : ℕ)| ≤
      (∏ p : ↥P, (A p).card : ℕ) := by
  have hcard : ((acceptedInterval P hP A a S).card : ℝ) =
      ∑ c ∈ crtResidues P hP A, ((residueFiber P a S c).card : ℝ) := by
    exact_mod_cast acceptedInterval_card_eq_sum P hP A a S
  have hdecomp :
      ((acceptedInterval P hP A a S).card : ℝ) -
          (S : ℝ) / residueModulus P *
            (∏ p : ↥P, (A p).card : ℕ) =
        ∑ c ∈ crtResidues P hP A,
          (((residueFiber P a S c).card : ℝ) -
            (S : ℝ) / residueModulus P) := by
    rw [hcard, sum_sub_distrib, sum_const, nsmul_eq_mul,
      crtResidues_card]
    push_cast
    ring
  rw [hdecomp]
  calc
    |∑ c ∈ crtResidues P hP A,
        (((residueFiber P a S c).card : ℝ) -
          (S : ℝ) / residueModulus P)| ≤
      ∑ c ∈ crtResidues P hP A,
        |((residueFiber P a S c).card : ℝ) -
          (S : ℝ) / residueModulus P| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ crtResidues P hP A, (1 : ℝ) :=
      sum_le_sum fun c hc ↦ residueFiber_error P hP A a S hc
    _ = (∏ p : ↥P, (A p).card : ℕ) := by
      rw [sum_const, nsmul_eq_mul, mul_one, crtResidues_card]

/-! ## Forbidden-set formulation -/

/-- Accepted residues are the complement of the deterministic forbidden
set at each prime. -/
def allowedResidues (P : Finset ℕ)
    (F : ∀ p : ↥P, Finset (Fin p.1)) : LocalResidues P :=
  fun p ↦ univ \ F p

theorem allowedResidues_card (P : Finset ℕ)
    (F : ∀ p : ↥P, Finset (Fin p.1)) (p : ↥P) :
    (allowedResidues P F p).card = p.1 - (F p).card := by
  rw [allowedResidues, card_sdiff_of_subset (subset_univ _), card_univ,
    Fintype.card_fin]

def avoidsForbidden (P : Finset ℕ)
    (hP : ∀ p : ↥P, Nat.Prime p.1)
    (F : ∀ p : ↥P, Finset (Fin p.1)) (n : ℕ) : Prop :=
  ∀ p : ↥P, residueAt P hP n p ∉ F p

def forbiddenInterval (P : Finset ℕ)
    (hP : ∀ p : ↥P, Nat.Prime p.1)
    (F : ∀ p : ↥P, Finset (Fin p.1)) (a S : ℕ) : Finset ℕ :=
  (Ico a (a + S)).filter (avoidsForbidden P hP F)

theorem forbiddenInterval_eq_acceptedInterval
    (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (F : ∀ p : ↥P, Finset (Fin p.1)) (a S : ℕ) :
    forbiddenInterval P hP F a S =
      acceptedInterval P hP (allowedResidues P F) a S := by
  ext n
  simp only [forbiddenInterval, acceptedInterval, mem_filter, and_congr_right_iff]
  intro _
  simp only [avoidsForbidden, Accepts, allowedResidues, mem_sdiff, mem_univ,
    true_and]

/-- Deterministic multi-forbidden-residue interval count with its complete
finite CRT rounding error. -/
theorem forbiddenInterval_count_error
    (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (F : ∀ p : ↥P, Finset (Fin p.1)) (a S : ℕ) :
    |((forbiddenInterval P hP F a S).card : ℝ) -
        (S : ℝ) / residueModulus P *
          (∏ p : ↥P, (p.1 - (F p).card) : ℕ)| ≤
      (∏ p : ↥P, (p.1 - (F p).card) : ℕ) := by
  rw [forbiddenInterval_eq_acceptedInterval]
  simpa only [allowedResidues_card] using
    acceptedInterval_count_error P hP (allowedResidues P F) a S

/-- A full local forbidden residue set kills the count exactly. -/
theorem forbiddenInterval_eq_empty_of_local_full
    (P : Finset ℕ) (hP : ∀ p : ↥P, Nat.Prime p.1)
    (F : ∀ p : ↥P, Finset (Fin p.1)) (a S : ℕ) (p : ↥P)
    (hp : F p = univ) :
    forbiddenInterval P hP F a S = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  have havoid := (mem_filter.mp hn).2 p
  rw [hp] at havoid
  exact havoid (mem_univ _)

end

end PrimeGapNormality.Prime.CoreRoughResidueCount
