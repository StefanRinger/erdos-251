import PrimeGapNormality.Prime.FiniteSelbergAsymptoticCap
import PrimeGapNormality.Prime.PresieveWindowS

/-!
# Uniform Selberg cap for concrete presieve survivors

The concrete survivor set already lies in `Icc 1 S`.  Every residue choice
also supplies the forbidden residue needed by the finite Selberg cap, after
restricting from primes through `S` to primes through `selbergRadius S`.
-/

open Filter Finset
open scoped Topology

namespace PrimeGapNormality.Prime

noncomputable section

theorem presieveSurvivors_subset_Icc_self (S : ℕ) (σ : ResidueChoice S) :
    presieveSurvivors S σ ⊆ Icc 1 S :=
  filter_subset _ _

theorem presieveSurvivors_avoids_radius_residues {S : ℕ}
    (hRS : selbergRadius S ≤ S) (σ : ResidueChoice S) :
    ∀ p ∈ Nat.primesLE (selbergRadius S), ∃ c : ℕ,
      ∀ n ∈ presieveSurvivors S σ, n % p ≠ c % p := by
  intro p hp
  have hpS : p ∈ Nat.primesLE S :=
    Nat.primesLE_mono hRS hp
  refine ⟨residueOfChoice S σ p, ?_⟩
  intro n hn
  have hsurv : sieveSurvives S (residueOfChoice S σ) n :=
    (mem_filter.mp hn).2
  have hc_lt : residueOfChoice S σ p < p := by
    unfold residueOfChoice
    rw [dif_pos hpS]
    have hval := (σ ⟨p, hpS⟩).isLt
    change (σ ⟨p, hpS⟩).val < p - 1 at hval
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE hpS
    omega
  rw [Nat.mod_eq_of_lt hc_lt]
  exact hsurv p hpS

theorem eventually_presieveSurvivors_card_le_two_add_eps
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℕ in atTop, ∀ σ : ResidueChoice S,
      ((presieveSurvivors S σ).card : ℝ) ≤
        (2 + ε) * (S : ℝ) / Real.log S := by
  filter_upwards [eventually_finiteSelberg_card_le_two_add_eps hε,
    eventually_selbergRadius_le_self] with S hcap hRS
  intro σ
  exact hcap (presieveSurvivors S σ)
    (presieveSurvivors_subset_Icc_self S σ)
    (presieveSurvivors_avoids_radius_residues hRS σ)

end

end PrimeGapNormality.Prime
