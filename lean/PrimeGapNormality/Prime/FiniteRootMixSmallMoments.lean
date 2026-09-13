import PrimeGapNormality.Prime.PresieveSelbergCap
import PrimeGapNormality.Prime.ExactRootMix
import PrimeGapNormality.Prime.CardinalitySymMass
import PrimeGapNormality.Prime.AhlSmallOfLarge
import PrimeGapNormality.Prime.ProfileSLeSieveCutoff

/-!
# Exact small-window root-mix moment inputs

This module identifies the concrete presieve fibres and exact late-root laws
used by the small finite root mix.  The remaining numerical input is the
uniform `M * theta < 5L` calibration over every mix parameter.
-/

open Filter Finset
open scoped Topology

namespace PrimeGapNormality.Prime

noncomputable section

theorem finiteRootMixSmall_presieve_eq_lateCandidateSet
    (S : ℕ) (σ : ResidueChoice S) :
    presieveSurvivors S σ = lateCandidateSet S S σ :=
  rfl

/-- Exact conditional count moments on a concrete small-window presieve
fibre. -/
theorem finiteRootMixSmall_exactCountMoments
    (κ : ℝ) (X y : ℕ) (σ : ResidueChoice (ahlSmall_window κ X))
    (hSy : ahlSmall_window κ X ≤ y) :
    ExactCountMoments (ahlSmall_window κ X) y
      (presieveSurvivors (ahlSmall_window κ X) σ)
      (lateRootLaw (ahlSmall_window κ X) y
        (presieveSurvivors (ahlSmall_window κ X) σ)) := by
  exact exactCountMoments_lateRootLaw (ahlSmall_window κ X) y
    (presieveSurvivors_subset_Icc_self (ahlSmall_window κ X) σ) le_rfl hSy

/-- The actual rooted law on the small window is the uniform average of the
exact conditional late-root laws over the same concrete presieve fibres. -/
theorem finiteRootMixSmall_actualRootLaw_eq_avg
    (κ : ℝ) (X y : ℕ) (hSy : ahlSmall_window κ X ≤ y)
    (U : Finset ℕ) :
    actualRootLaw y (ahlSmall_window κ X) U =
      (∑ σ : ResidueChoice (ahlSmall_window κ X),
          lateRootLaw (ahlSmall_window κ X) y
            (presieveSurvivors (ahlSmall_window κ X) σ) U) /
        (Fintype.card (ResidueChoice (ahlSmall_window κ X)) : ℝ) := by
  simp_rw [finiteRootMixSmall_presieve_eq_lateCandidateSet]
  exact actualRootLaw_eq_avg_lateRootLaw
    (ahlSmall_window κ X) y (ahlSmall_window κ X) le_rfl hSy U

/-- The concrete small search space is exactly the interval used by the
presieve survivor construction. -/
theorem finiteRootMixSmall_omega_eq_Icc (κ : ℝ) (X : ℕ) :
    ahlSmall_omega κ X = Icc 1 (ahlSmall_window κ X) :=
  rfl

end

end PrimeGapNormality.Prime
