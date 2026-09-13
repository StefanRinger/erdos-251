import PrimeGapNormality.Prime.CoreAuxiliaryGapMean
import PrimeGapNormality.Prime.ExactRootMix
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The genuine finite auxiliary-frame mass

For each exposed presieve `σ` and original late count `n ≥ L`, this law keeps
the original cardinality marginal and chooses uniformly among every
`(n-1)`-subset of the exposed carrier.  Low-count mass is discarded, not
renormalized.  The final root mixture uses exactly `mixWeightV / mixZ`.
-/

open Finset
open scoped BigOperators Classical

namespace PrimeGapNormality.Prime

noncomputable section

set_option maxHeartbeats 800000

/-- Point mass of the uniform `m`-subset law on a finite carrier. -/
def coreAuxUniformFrameMass (A : Finset ℕ) (m : ℕ) (F : Finset ℕ) : ℝ :=
  if F ∈ A.powersetCard m then 1 / (A.card.choose m : ℝ) else 0

theorem coreAuxUniformFrameMass_nonneg (A : Finset ℕ) (m : ℕ) (F : Finset ℕ) :
    0 ≤ coreAuxUniformFrameMass A m F := by
  unfold coreAuxUniformFrameMass
  split_ifs <;> positivity

/-- Summing the point mass over any ambient powerset containing `A` gives
one, provided the requested exact layer exists. -/
theorem coreAuxUniformFrameMass_sum (A Ω : Finset ℕ) (m : ℕ)
    (hAΩ : A ⊆ Ω) (hm : m ≤ A.card) :
    ∑ F ∈ Ω.powerset, coreAuxUniformFrameMass A m F = 1 := by
  have hlayer : A.powersetCard m ⊆ Ω.powerset := by
    intro F hF
    exact mem_powerset.mpr ((mem_powersetCard.mp hF).1.trans hAΩ)
  have hfilter : Ω.powerset.filter (fun F ↦ F ∈ A.powersetCard m) =
      A.powersetCard m := by
    ext F
    simp only [mem_filter]
    constructor
    · exact fun h ↦ h.2
    · intro hF
      exact ⟨hlayer hF, hF⟩
  unfold coreAuxUniformFrameMass
  rw [← sum_filter, hfilter, sum_const, nsmul_eq_mul,
    card_powersetCard]
  have hchoose : (A.card.choose m : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hm).ne'
  field_simp [hchoose]

/-- Integrating a test against the point mass is exactly the existing
uniform-layer mean. -/
theorem coreAuxUniformFrameMass_expectation (A Ω : Finset ℕ) (m : ℕ)
    (hAΩ : A ⊆ Ω) (f : Finset ℕ → ℝ) :
    (∑ F ∈ Ω.powerset, coreAuxUniformFrameMass A m F * f F) =
      auxFrame_uniformMean A m f := by
  have hlayer : A.powersetCard m ⊆ Ω.powerset := by
    intro F hF
    exact mem_powerset.mpr ((mem_powersetCard.mp hF).1.trans hAΩ)
  have hfilter : Ω.powerset.filter (fun F ↦ F ∈ A.powersetCard m) =
      A.powersetCard m := by
    ext F
    simp only [mem_filter]
    constructor
    · exact fun h ↦ h.2
    · intro hF
      exact ⟨hlayer hF, hF⟩
  unfold coreAuxUniformFrameMass auxFrame_uniformMean
  simp_rw [ite_mul, zero_mul]
  rw [← sum_filter, hfilter, ← mul_sum]
  ring

/-- The auxiliary frame mass at one sieve cutoff.  The original `(σ,n)`
marginals are retained literally; only `n < L` is omitted. -/
def coreAuxiliaryLayerFrameMass (S y L : ℕ) (F : Finset ℕ) : ℝ :=
  (∑ σ : ResidueChoice S,
      ∑ n ∈ Icc L (presieveSurvivors S σ).card,
        cardinalityLayer (presieveSurvivors S σ)
            (lateRootLaw S y (presieveSurvivors S σ)) n *
          coreAuxUniformFrameMass (presieveSurvivors S σ) (n - 1) F) /
    (Fintype.card (ResidueChoice S) : ℝ)

/-- The omitted part of the same original late law. -/
def coreAuxiliaryLayerLowCountMass (S y L : ℕ) : ℝ :=
  (∑ σ : ResidueChoice S,
      ∑ U ∈ (presieveSurvivors S σ).powerset.filter (fun U ↦ U.card < L),
        lateRootLaw S y (presieveSurvivors S σ) U) /
    (Fintype.card (ResidueChoice S) : ℝ)

private theorem coreAuxFrame_cardinalityLayer_nonneg
    {A : Finset ℕ} {μ : Finset ℕ → ℝ}
    (hμ : CardinalitySymmetricMass A μ) (n : ℕ) :
    0 ≤ cardinalityLayer A μ n := by
  unfold cardinalityLayer
  exact sum_nonneg fun U hU ↦ hμ.1 U (mem_filter.mp hU).1

theorem coreAuxiliaryLayerFrameMass_nonneg (S y L : ℕ) (hSy : S ≤ y)
    (F : Finset ℕ) : 0 ≤ coreAuxiliaryLayerFrameMass S y L F := by
  unfold coreAuxiliaryLayerFrameMass
  apply div_nonneg
  · exact sum_nonneg fun σ _ ↦ sum_nonneg fun n _ ↦
      mul_nonneg
        (coreAuxFrame_cardinalityLayer_nonneg
          (corePresieveLaw_cardinalitySymmetric S y σ hSy) n)
        (coreAuxUniformFrameMass_nonneg _ _ _)
  · exact Nat.cast_nonneg _

theorem coreAuxiliaryLayerLowCountMass_nonneg (S y L : ℕ) (hSy : S ≤ y) :
    0 ≤ coreAuxiliaryLayerLowCountMass S y L := by
  unfold coreAuxiliaryLayerLowCountMass
  apply div_nonneg
  · exact sum_nonneg fun σ _ ↦ sum_nonneg fun U hU ↦
      (corePresieveLaw_cardinalitySymmetric S y σ hSy).1 U
        (mem_filter.mp hU).1
  · exact Nat.cast_nonneg _

/-- Exact-cardinality layers aggregate to the corresponding high-count
event in the original finite law. -/
private theorem coreAuxFrame_sum_layers_eq_high
    (A : Finset ℕ) (μ : Finset ℕ → ℝ) (L : ℕ) :
    (∑ n ∈ Icc L A.card, cardinalityLayer A μ n) =
      ∑ U ∈ A.powerset.filter (fun U ↦ L ≤ U.card), μ U := by
  unfold cardinalityLayer
  rw [sum_sigma' (s := Icc L A.card)
    (t := fun n ↦ A.powerset.filter (fun U ↦ U.card = n))
    (f := fun _ U ↦ μ U)]
  refine sum_bij'
      (fun p _ ↦ p.2)
      (fun U _ ↦ ⟨U.card, U⟩)
      ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hn := mem_Icc.mp (mem_sigma.mp hp).1
    have hU := mem_filter.mp (mem_sigma.mp hp).2
    exact mem_filter.mpr ⟨hU.1, hU.2 ▸ hn.1⟩
  · intro U hU
    have hUm := mem_filter.mp hU
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hUm.2,
      card_le_card (mem_powerset.mp hUm.1)⟩,
      mem_filter.mpr ⟨hUm.1, rfl⟩⟩
  · intro p hp
    have hU := mem_filter.mp (mem_sigma.mp hp).2
    simp [hU.2]
  · intro U hU
    rfl
  · intro p hp
    rfl

/-- The total one-cutoff frame mass is exactly the retained original
high-count probability. -/
theorem coreAuxiliaryLayerFrameMass_sum (S y L : ℕ) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryLayerFrameMass S y L F) =
      (∑ σ : ResidueChoice S,
          ∑ n ∈ Icc L (presieveSurvivors S σ).card,
            cardinalityLayer (presieveSurvivors S σ)
              (lateRootLaw S y (presieveSurvivors S σ)) n) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  unfold coreAuxiliaryLayerFrameMass
  rw [← Finset.sum_div]
  apply congrArg (fun z : ℝ ↦ z / (Fintype.card (ResidueChoice S) : ℝ))
  rw [sum_comm]
  apply sum_congr rfl
  intro σ hσ
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [← mul_sum]
  have hsub : presieveSurvivors S σ ⊆ offsetWindow S := by
    simpa only [offsetWindow] using corePresieveSurvivors_subset_Icc S σ
  have hnm := mem_Icc.mp hn
  rw [coreAuxUniformFrameMass_sum _ _ _ hsub
    ((Nat.sub_le n 1).trans hnm.2), mul_one]

/-- Total retained mass plus the genuine original low-count probability is
exactly one. -/
theorem coreAuxiliaryLayerFrameMass_add_low_eq_one
    (S y L : ℕ) (hSy : S ≤ y) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryLayerFrameMass S y L F) +
      coreAuxiliaryLayerLowCountMass S y L = 1 := by
  rw [coreAuxiliaryLayerFrameMass_sum]
  unfold coreAuxiliaryLayerLowCountMass
  rw [← add_div]
  have hnum :
      (∑ σ : ResidueChoice S,
          ∑ n ∈ Icc L (presieveSurvivors S σ).card,
            cardinalityLayer (presieveSurvivors S σ)
              (lateRootLaw S y (presieveSurvivors S σ)) n) +
        (∑ σ : ResidueChoice S,
          ∑ U ∈ (presieveSurvivors S σ).powerset.filter (fun U ↦ U.card < L),
            lateRootLaw S y (presieveSurvivors S σ) U) =
        (Fintype.card (ResidueChoice S) : ℝ) := by
    rw [← sum_add_distrib]
    calc
      (∑ σ : ResidueChoice S,
          ((∑ n ∈ Icc L (presieveSurvivors S σ).card,
              cardinalityLayer (presieveSurvivors S σ)
                (lateRootLaw S y (presieveSurvivors S σ)) n) +
            ∑ U ∈ (presieveSurvivors S σ).powerset.filter (fun U ↦ U.card < L),
              lateRootLaw S y (presieveSurvivors S σ) U)) =
          ∑ σ : ResidueChoice S, 1 := by
        apply sum_congr rfl
        intro σ hσ
        let A := presieveSurvivors S σ
        let μ := lateRootLaw S y A
        have hμ := corePresieveLaw_cardinalitySymmetric S y σ hSy
        have hsplit := (sum_filter_add_sum_filter_not
          (s := A.powerset) (p := fun U ↦ L ≤ U.card) (f := μ)).symm
        change
          (∑ n ∈ Icc L A.card, cardinalityLayer A μ n) +
            (∑ U ∈ A.powerset.filter (fun U ↦ U.card < L), μ U) = 1
        rw [coreAuxFrame_sum_layers_eq_high]
        have hnot : A.powerset.filter (fun U ↦ ¬ L ≤ U.card) =
            A.powerset.filter (fun U ↦ U.card < L) := by
          ext U
          simp only [mem_filter, Nat.not_le]
        rw [← hnot]
        exact hsplit.symm.trans hμ.2.1
      _ = (Fintype.card (ResidueChoice S) : ℝ) := by
        rw [sum_const, card_univ, nsmul_eq_mul, mul_one]
  have hcard : (Fintype.card (ResidueChoice S) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [hnum]
  exact div_self hcard

theorem coreAuxiliaryLayerFrameMass_sum_le_one
    (S y L : ℕ) (hSy : S ≤ y) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryLayerFrameMass S y L F) ≤ 1 := by
  have h := coreAuxiliaryLayerFrameMass_add_low_eq_one S y L hSy
  have hlow := coreAuxiliaryLayerLowCountMass_nonneg S y L hSy
  linarith

/-- The subset-gap expectation of the genuine frame mass is the previously
proved physical auxiliary-layer mean. -/
theorem coreAuxiliaryLayerFrameMass_subsetGap_expectation
    (S y L j : ℕ) :
    (∑ F ∈ (offsetWindow S).powerset,
        coreAuxiliaryLayerFrameMass S y L F * (subsetGap F j : ℝ)) =
      coreAuxiliaryLayerPhysicalGapMean S y L j := by
  unfold coreAuxiliaryLayerFrameMass coreAuxiliaryLayerPhysicalGapMean
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun z : ℝ ↦ z / (Fintype.card (ResidueChoice S) : ℝ))
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ hσ
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  simp_rw [mul_assoc]
  rw [← mul_sum]
  have hsub : presieveSurvivors S σ ⊆ offsetWindow S := by
    simpa only [offsetWindow] using corePresieveSurvivors_subset_Icc S σ
  rw [coreAuxUniformFrameMass_expectation _ _ _ hsub
    (fun F ↦ (subsetGap F j : ℝ))]

/-! ## Exact normalized finite root mixture -/

/-- The final auxiliary frame mass with the literal finite-root-mixture
normalization `mixWeightV / mixZ`. -/
def coreAuxiliaryFrameMass (X S L : ℕ) (F : Finset ℕ) : ℝ :=
  (∑ t ∈ mixScale X, mixWeightV t *
      coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F) / mixZ X

def coreAuxiliaryFrameMissingMass (X S L : ℕ) : ℝ :=
  (∑ t ∈ mixScale X, mixWeightV t *
      coreAuxiliaryLayerLowCountMass S (sieveCutoff (t : ℝ)) L) / mixZ X

theorem coreAuxiliaryFrameMass_nonneg (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) (F : Finset ℕ) :
    0 ≤ coreAuxiliaryFrameMass X S L F := by
  unfold coreAuxiliaryFrameMass
  exact div_nonneg
    (sum_nonneg fun t ht ↦ mul_nonneg (mixWeightV_nonneg t)
      (coreAuxiliaryLayerFrameMass_nonneg S _ L (hSy t ht) F)) hZ.le

theorem coreAuxiliaryFrameMissingMass_nonneg (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) :
    0 ≤ coreAuxiliaryFrameMissingMass X S L := by
  unfold coreAuxiliaryFrameMissingMass
  exact div_nonneg
    (sum_nonneg fun t ht ↦ mul_nonneg (mixWeightV_nonneg t)
      (coreAuxiliaryLayerLowCountMass_nonneg S _ L (hSy t ht))) hZ.le

/-- The missing mass is exactly the mixture of the original low-count
probabilities; no frame law is renormalized. -/
theorem coreAuxiliaryFrameMass_add_missing_eq_one (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryFrameMass X S L F) +
      coreAuxiliaryFrameMissingMass X S L = 1 := by
  unfold coreAuxiliaryFrameMass coreAuxiliaryFrameMissingMass
  rw [← Finset.sum_div, ← add_div]
  have hnum :
      (∑ F ∈ (offsetWindow S).powerset,
          ∑ t ∈ mixScale X, mixWeightV t *
            coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F) +
        ∑ t ∈ mixScale X, mixWeightV t *
          coreAuxiliaryLayerLowCountMass S (sieveCutoff (t : ℝ)) L = mixZ X := by
    rw [sum_comm]
    rw [← sum_add_distrib]
    calc
      (∑ t ∈ mixScale X,
          ((∑ F ∈ (offsetWindow S).powerset,
              mixWeightV t *
                coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F) +
            mixWeightV t *
              coreAuxiliaryLayerLowCountMass S (sieveCutoff (t : ℝ)) L)) =
          ∑ t ∈ mixScale X, mixWeightV t := by
        apply sum_congr rfl
        intro t ht
        rw [← mul_sum, ← mul_add,
          coreAuxiliaryLayerFrameMass_add_low_eq_one S
            (sieveCutoff (t : ℝ)) L (hSy t ht), mul_one]
      _ = mixZ X := rfl
  rw [hnum]
  exact div_self hZ.ne'

theorem coreAuxiliaryFrameMass_sum_le_one (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryFrameMass X S L F) ≤ 1 := by
  have h := coreAuxiliaryFrameMass_add_missing_eq_one X S L hSy hZ
  have hmissing := coreAuxiliaryFrameMissingMass_nonneg X S L hSy hZ
  linarith

/-- Exact subset-gap expectation under the normalized finite auxiliary
mixture. -/
theorem coreAuxiliaryFrameMass_subsetGap_expectation (X S L j : ℕ) :
    (∑ F ∈ (offsetWindow S).powerset,
        coreAuxiliaryFrameMass X S L F * (subsetGap F j : ℝ)) =
      (∑ t ∈ mixScale X, mixWeightV t *
        coreAuxiliaryLayerPhysicalGapMean S (sieveCutoff (t : ℝ)) L j) /
        mixZ X := by
  unfold coreAuxiliaryFrameMass
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun z : ℝ ↦ z / mixZ X)
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  simp_rw [mul_assoc]
  rw [← mul_sum, coreAuxiliaryLayerFrameMass_subsetGap_expectation]

end

end PrimeGapNormality.Prime
