import PrimeGapNormality.Prime.CoreRootedCrt
import PrimeGapNormality.Prime.CorePeriodicSurvivors

/-!
# Actual rooted-sieve enumeration through one physical period

The old `sievePoint` is `Nat.nth`. Here it is identified with the explicit
sorted periodic enumeration for the actual forbidden residues. In particular
the root is zero, not a candidate-index spacing or an abstract replacement.
-/

open Finset

namespace PrimeGapNormality.Prime

theorem coreRootedPeriod_pos (y : ℕ) : 0 < coreRootedPeriod y := by
  unfold coreRootedPeriod
  exact prod_pos (fun p hp => (Nat.mem_primesLE.mp hp).2.pos)

def coreSievePeriodSurvivors (y : ℕ) (σ : ResidueChoice y) : Finset ℕ :=
  (range (coreRootedPeriod y)).filter (sieveSurvives y (residueOfChoice y σ))

theorem coreSievePeriodSurvivors_subset (y : ℕ) (σ : ResidueChoice y) :
    coreSievePeriodSurvivors y σ ⊆ range (coreRootedPeriod y) :=
  filter_subset _ _

theorem coreSievePeriodSurvivors_zero_mem (y : ℕ) (σ : ResidueChoice y) :
    0 ∈ coreSievePeriodSurvivors y σ := by
  refine mem_filter.mpr ⟨mem_range.mpr (coreRootedPeriod_pos y), ?_⟩
  intro p hp
  simp [residueOfChoice, hp]

theorem coreSievePeriodSurvivors_card_pos (y : ℕ) (σ : ResidueChoice y) :
    0 < (coreSievePeriodSurvivors y σ).card :=
  card_pos.mpr ⟨0, coreSievePeriodSurvivors_zero_mem y σ⟩

theorem coreSievePeriodSurvivors_mod_iff (y : ℕ) (σ : ResidueChoice y) (m : ℕ) :
    m % coreRootedPeriod y ∈ coreSievePeriodSurvivors y σ ↔
      sieveSurvives y (residueOfChoice y σ) m := by
  have hmod (p : ℕ) (hp : p ∈ Nat.primesLE y) :
      (m % coreRootedPeriod y) % p = m % p :=
    Nat.mod_mod_of_dvd m (dvd_prod_of_mem (fun q : ℕ => q) hp)
  simp only [coreSievePeriodSurvivors, mem_filter, mem_range,
    Nat.mod_lt m (coreRootedPeriod_pos y), true_and, sieveSurvives]
  constructor <;> intro h p hp
  · simpa only [hmod p hp] using h p hp
  · simpa only [hmod p hp] using h p hp

def coreSievePeriodLastRank (y : ℕ) (σ : ResidueChoice y) : ℕ :=
  (coreSievePeriodSurvivors y σ).card - 1

theorem coreSievePeriod_card (y : ℕ) (σ : ResidueChoice y) :
    (coreSievePeriodSurvivors y σ).card = coreSievePeriodLastRank y σ + 1 := by
  have := coreSievePeriodSurvivors_card_pos y σ
  unfold coreSievePeriodLastRank
  omega

/-- Exact adapter to the live rooted model's Nat.nth definition. -/
theorem core_sievePoint_eq_periodicPoint (y : ℕ) (σ : ResidueChoice y) (r : ℕ) :
    sievePoint y (residueOfChoice y σ) r =
      corePeriodicPoint (coreRootedPeriod y) (coreSievePeriodSurvivors y σ)
        (coreSievePeriod_card y σ) r := by
  have hp : (fun m => m % coreRootedPeriod y ∈ coreSievePeriodSurvivors y σ) =
      sieveSurvives y (residueOfChoice y σ) := by
    funext m
    exact propext (coreSievePeriodSurvivors_mod_iff y σ m)
  have h := corePeriodicPoint_eq_nth (coreRootedPeriod y) (coreSievePeriodSurvivors y σ)
    (coreSievePeriod_card y σ) (coreSievePeriodSurvivors_subset y σ) r
  rw [hp] at h
  exact h.symm

end PrimeGapNormality.Prime
