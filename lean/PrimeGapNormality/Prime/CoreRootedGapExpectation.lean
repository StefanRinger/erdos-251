import PrimeGapNormality.Prime.CoreRootedSieveEnumeration
import PrimeGapNormality.Prime.CorePeriodicRootMean
import PrimeGapNormality.Prime.EulerProd
import Mathlib.Tactic.FieldSimp

/-!
# Exact physical gap expectation in the actual rooted sieve

Negation of the CRT center gives a uniform survivor root. The actual
Nat.nth gap sequence is the translated periodic enumeration. Its mean is
computed by finite telescoping and the exact Euler-product cardinal ratio.
-/

open Finset
open scoped BigOperators

namespace PrimeGapNormality.Prime

private theorem coreReducedResidues_subset (y : ℕ) :
    coreReducedResidues y ⊆ range (coreRootedPeriod y) := filter_subset _ _

private theorem coreReducedResidues_nonempty (y : ℕ) : (coreReducedResidues y).Nonempty := by
  let σ : ResidueChoice y := fun p => ⟨0, by
    have hp := (Nat.mem_primesLE.mp p.property).2.two_le
    change 0 < p.val - 1
    omega⟩
  exact ⟨_, coreRootedCrtCenter_mem y σ⟩

private theorem coreReducedResidue_neg_mem (y : ℕ)
    (a : {a // a ∈ coreReducedResidues y}) :
    (coreRootedPeriod y - a.val) % coreRootedPeriod y ∈ coreReducedResidues y := by
  have ha : a.val < coreRootedPeriod y :=
    mem_range.mp (coreReducedResidues_subset y a.property)
  refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (coreRootedPeriod_pos y)), ?_⟩
  intro p hp hzero
  have hpP : p ∣ coreRootedPeriod y := dvd_prod_of_mem (fun q : ℕ => q) hp
  rw [Nat.mod_mod_of_dvd _ hpP] at hzero
  have hsum : (a.val + (coreRootedPeriod y - a.val)) % p = 0 := by
    rw [Nat.add_sub_of_le ha.le]
    exact Nat.mod_eq_zero_of_dvd hpP
  rw [Nat.add_mod, hzero, add_zero, Nat.mod_mod] at hsum
  exact (mem_filter.mp a.property).2 p hp hsum

private def coreReducedResidueNeg (y : ℕ)
    (a : {a // a ∈ coreReducedResidues y}) : {a // a ∈ coreReducedResidues y} :=
  ⟨(coreRootedPeriod y - a.val) % coreRootedPeriod y, coreReducedResidue_neg_mem y a⟩

private theorem coreReducedResidueNeg_involutive (y : ℕ) :
    Function.Involutive (coreReducedResidueNeg y) := by
  intro a
  apply Subtype.ext
  change (coreRootedPeriod y - ((coreRootedPeriod y - a.val) % coreRootedPeriod y)) %
    coreRootedPeriod y = a.val
  have ha : a.val < coreRootedPeriod y :=
    mem_range.mp (coreReducedResidues_subset y a.property)
  by_cases hz : a.val = 0
  · simp [hz]
  · have hsub : coreRootedPeriod y - a.val < coreRootedPeriod y :=
      Nat.sub_lt (coreRootedPeriod_pos y) (Nat.pos_of_ne_zero hz)
    rw [Nat.mod_eq_of_lt hsub, Nat.sub_sub_self ha.le, Nat.mod_eq_of_lt ha]

/-- The paper's root a, in the convention that a+m must be a reduced residue. -/
noncomputable def coreRootedPhysicalRootEquiv (y : ℕ) :
    ResidueChoice y ≃ {a // a ∈ coreReducedResidues y} :=
  (coreRootedCrtEquiv y).trans
    ((coreReducedResidueNeg_involutive y).toPerm (coreReducedResidueNeg y))

theorem coreRootedPhysicalRoot_survives (y : ℕ) (σ : ResidueChoice y) (m : ℕ) :
    sieveSurvives y (residueOfChoice y σ) m ↔
      ((coreRootedPhysicalRootEquiv y σ).val + m) % coreRootedPeriod y ∈
        coreReducedResidues y := by
  let a := (coreRootedPhysicalRootEquiv y σ).val
  let c := coreRootedCrtCenter y σ
  have hca : c ≤ coreRootedPeriod y := (coreRootedCrtCenter_lt y σ).le
  have hsum (p : ℕ) (hp : p ∈ Nat.primesLE y) : (a + c) % p = 0 := by
    have hpP : p ∣ coreRootedPeriod y := by
      unfold coreRootedPeriod
      exact dvd_prod_of_mem (fun q : ℕ => q) hp
    have hac : a = (coreRootedPeriod y - c) % coreRootedPeriod y := by
      rfl
    rw [hac]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ hpP, ← Nat.add_mod,
      Nat.sub_add_cancel hca]
    exact Nat.mod_eq_zero_of_dvd hpP
  have hpoint (p : ℕ) (hp : p ∈ Nat.primesLE y) :
      m % p ≠ c % p ↔ (a + m) % p ≠ 0 := by
    constructor
    · intro h hz
      apply h
      have heq : a + m ≡ a + c [MOD p] := hz.trans (hsum p hp).symm
      exact Nat.ModEq.add_left_cancel' a heq
    · intro h heq
      apply h
      have hadd := Nat.ModEq.add_left a (show m ≡ c [MOD p] from heq)
      change (a + m) % p = (a + c) % p at hadd
      exact hadd.trans (hsum p hp)
  rw [coreRootedCrt_sieveSurvives_iff]
  change (∀ p ∈ Nat.primesLE y, m % p ≠ c % p) ↔
    (a + m) % coreRootedPeriod y ∈ coreReducedResidues y
  simp only [coreReducedResidues, mem_filter, mem_range,
    Nat.mod_lt (a + m) (coreRootedPeriod_pos y), true_and]
  constructor <;> intro h p hp
  · have hpP : p ∣ coreRootedPeriod y := by
      unfold coreRootedPeriod
      exact dvd_prod_of_mem (fun q : ℕ => q) hp
    rw [Nat.mod_mod_of_dvd _ hpP]
    exact (hpoint p hp).mp (h p hp)
  · apply (hpoint p hp).mpr
    have hpP : p ∣ coreRootedPeriod y := by
      unfold coreRootedPeriod
      exact dvd_prod_of_mem (fun q : ℕ => q) hp
    simpa only [Nat.mod_mod_of_dvd _ hpP] using h p hp

theorem coreRootedPeriod_div_card_eq_euler_inv (y : ℕ) :
    (coreRootedPeriod y : ℝ) / ((coreReducedResidues y).card : ℝ) =
      (eulerProdNat y)⁻¹ := by
  have hcard : (Fintype.card (ResidueChoice y) : ℝ) =
      ∏ p ∈ Nat.primesLE y, ((p - 1 : ℕ) : ℝ) := by
    simp only [ResidueChoice, Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
    exact Finset.prod_coe_sort (Nat.primesLE y) (fun p => ((p - 1 : ℕ) : ℝ))
  rw [← coreRootedCrt_card, hcard]
  simp only [coreRootedPeriod, Nat.cast_prod, eulerProdNat, ← Finset.prod_div_distrib]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    linarith
  rw [Nat.cast_sub hprime.one_le, Nat.cast_one]
  field_simp

/-- Exact physical root-gap mean, at every finite sieve cutoff and every rank.
The expectation uses the existing independent uniform residue choice space
and the existing `sievePoint = Nat.nth` definition. -/
theorem core_rooted_sieve_gap_mean (y r : ℕ) :
    (∑ σ : ResidueChoice y,
      ((sievePoint y (residueOfChoice y σ) (r + 1) : ℝ) -
        (sievePoint y (residueOfChoice y σ) r : ℝ))) /
      (Fintype.card (ResidueChoice y) : ℝ) = (eulerProdNat y)⁻¹ := by
  let A := coreReducedResidues y
  let n := A.card - 1
  have hcard : A.card = n + 1 := by
    have := card_pos.mpr (coreReducedResidues_nonempty y)
    dsimp [n, A]
    omega
  let e : ResidueChoice y ≃ Fin (n + 1) :=
    (coreRootedPhysicalRootEquiv y).trans (A.orderIsoOfFin hcard).symm.toEquiv
  have hroot (σ : ResidueChoice y) :
      A.orderEmbOfFin hcard (e σ) = (coreRootedPhysicalRootEquiv y σ).val := by
    exact congrArg Subtype.val
      ((A.orderIsoOfFin hcard).apply_symm_apply (coreRootedPhysicalRootEquiv y σ))
  have hpoint (σ : ResidueChoice y) (j : ℕ) :
      sievePoint y (residueOfChoice y σ) j =
        corePeriodicRootPoint (coreRootedPeriod y) A hcard (e σ) j := by
    have hp : (fun m => (A.orderEmbOfFin hcard (e σ) + m) % coreRootedPeriod y ∈ A) =
        sieveSurvives y (residueOfChoice y σ) := by
      funext m
      rw [hroot]
      exact propext (coreRootedPhysicalRoot_survives y σ m).symm
    have h := corePeriodicRootPoint_eq_nth (coreRootedPeriod y) A hcard
      (coreReducedResidues_subset y) (e σ) j
    rw [hp] at h
    exact h.symm
  simp_rw [hpoint]
  have hsum := Equiv.sum_comp e (fun i : Fin (n + 1) =>
    ((corePeriodicRootPoint (coreRootedPeriod y) A hcard i (r + 1) : ℝ) -
      (corePeriodicRootPoint (coreRootedPeriod y) A hcard i r : ℝ)))
  rw [hsum]
  rw [coreRootedCrt_card]
  change _ / (A.card : ℝ) = _
  rw [corePeriodicRootPoint_gap_sum (coreRootedPeriod y) A hcard
    (coreReducedResidues_subset y)]
  exact coreRootedPeriod_div_card_eq_euler_inv y

end PrimeGapNormality.Prime
