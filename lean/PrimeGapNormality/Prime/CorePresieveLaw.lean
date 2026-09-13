import PrimeGapNormality.Prime.CardinalitySymMass
import PrimeGapNormality.Prime.PresieveWindowS

/-! Shared exact presieve laws without the legacy `PresieveToSFill`
packaging or its conflicting Nat/Real positivity helper names. These are
specializations of the proved finite laws, not additional hypotheses. -/

open Finset

namespace PrimeGapNormality.Prime

theorem corePresieveSurvivors_subset_Icc (S : ℕ) (σ : ResidueChoice S) :
    presieveSurvivors S σ ⊆ Icc 1 S :=
  lateCandidateSet_subset_Icc S S σ

theorem corePresieveLaw_cardinalitySymmetric
    (S y : ℕ) (σ : ResidueChoice S) (hSy : S ≤ y) :
    CardinalitySymmetricMass (presieveSurvivors S σ)
      (lateRootLaw S y (presieveSurvivors S σ)) :=
  lateRootLaw_cardinalitySymmetric S y
    (corePresieveSurvivors_subset_Icc S σ) le_rfl hSy

theorem corePresieveLaw_exactCountMoments
    (S y : ℕ) (σ : ResidueChoice S) (hSy : S ≤ y) :
    ExactCountMoments S y (presieveSurvivors S σ)
      (lateRootLaw S y (presieveSurvivors S σ)) :=
  exactCountMoments_lateRootLaw S y
    (corePresieveSurvivors_subset_Icc S σ) le_rfl hSy

theorem coreActualRootLaw_eq_avg_presieve
    (S y : ℕ) (hSy : S ≤ y) (U : Finset ℕ) :
    actualRootLaw y S U =
      (∑ σ : ResidueChoice S, lateRootLaw S y (presieveSurvivors S σ) U) /
        (Fintype.card (ResidueChoice S) : ℝ) :=
  actualRootLaw_eq_avg_lateRootLaw S y S le_rfl hSy U

end PrimeGapNormality.Prime
