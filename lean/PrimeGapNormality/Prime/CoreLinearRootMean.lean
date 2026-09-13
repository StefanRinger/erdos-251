import PrimeGapNormality.Prime.CoreLinearModelMean
import PrimeGapNormality.Prime.CoreLinearMixtureScales
import PrimeGapNormality.Prime.CoreLinearCriticalRank
import PrimeGapNormality.Prime.CorePrimeWindowMean

/-!
# Actual rooted and finite-mixture linear model means

This file aggregates the finite good-cardinality layer estimate over the
proved late-root law, exposed presieve roots, and the normalized finite root
mixture.  The only discarded mass is the genuine self-normalized high-count
exception.
-/

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

noncomputable section

private theorem coreLinear_lateRetention_nonneg (S y : ℕ) :
    0 ≤ lateRetention S y := by
  unfold lateRetention rootedEulerProdNat
  refine prod_nonneg fun p hp => ?_
  have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp'.two_le
  have hden : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hden)

noncomputable def coreLinearFibreMean
    (B S y L : ℕ) (f : AddCircle (1 : ℝ) → ℝ) (σ : ResidueChoice S) : ℝ :=
  ∑ U ∈ (presieveSurvivors S σ).powerset,
    lateRootLaw S y (presieveSurvivors S σ) U *
      if L ≤ U.card then f (coreLinearShapePhase B L U : AddCircle (1 : ℝ)) else 0

noncomputable def coreLinearFibreAuxGap
    (S y L j : ℕ) (σ : ResidueChoice S) : ℝ :=
  ∑ n ∈ Icc L (presieveSurvivors S σ).card,
    cardinalityLayer (presieveSurvivors S σ)
        (lateRootLaw S y (presieveSurvivors S σ)) n *
      auxFrame_uniformMean (presieveSurvivors S σ) (n - 1)
        (fun F => (subsetGap F j : ℝ))

noncomputable def coreLinearActualRootMean
    (B y S L : ℕ) (f : AddCircle (1 : ℝ) → ℝ) : ℝ :=
  ∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U *
    if L ≤ U.card then f (coreLinearShapePhase B L U : AddCircle (1 : ℝ)) else 0

noncomputable def coreLinearFiniteRootMean
    (B X S L : ℕ) (f : AddCircle (1 : ℝ) → ℝ) : ℝ :=
  ∑ U ∈ (offsetWindow S).powerset.filter (fun U => U.card = L),
    f (coreLinearShapePhase B L U : AddCircle (1 : ℝ)) *
      Stopped.shortShapeMass (offsetWindow S) (finiteRootMix X S) L U

/-! ### Exact cardinality disintegration -/

private theorem coreLinear_cardinalityLayer_test_eq
    {A : Finset ℕ} {μ : Finset ℕ → ℝ}
    (hμ : CardinalitySymmetricMass A μ) (n : ℕ) (hnA : n ≤ A.card)
    (test : Finset ℕ → ℝ) :
    (∑ U ∈ A.powersetCard n, μ U * test U) =
      cardinalityLayer A μ n * auxFrame_uniformMean A n test := by
  let w := uniformLayerWeight A μ n
  have hterm : ∀ U ∈ A.powersetCard n, μ U = w := by
    intro U hU
    have hUm := mem_powersetCard.mp hU
    simpa [w, hUm.2] using mu_eq_uniformLayerWeight hμ hUm.1
  have hlayer : cardinalityLayer A μ n =
      (A.card.choose n : ℝ) * w := by
    unfold cardinalityLayer
    rw [show A.powerset.filter (fun U => U.card = n) = A.powersetCard n from
      powersetCard_eq_filter.symm]
    rw [sum_congr rfl hterm, sum_const, card_powersetCard, nsmul_eq_mul]
  have hchoose : (A.card.choose n : ℝ) ≠ 0 := auxFrame_choose_ne_zero hnA
  calc
    (∑ U ∈ A.powersetCard n, μ U * test U) =
        ∑ U ∈ A.powersetCard n, w * test U := by
      refine sum_congr rfl fun U hU => ?_
      rw [hterm U hU]
    _ = w * ∑ U ∈ A.powersetCard n, test U := by rw [Finset.mul_sum]
    _ = cardinalityLayer A μ n * auxFrame_uniformMean A n test := by
      rw [hlayer]
      unfold auxFrame_uniformMean
      field_simp [hchoose]

private theorem coreLinear_sum_powerset_card_layers
    (A : Finset ℕ) (L : ℕ) (g : Finset ℕ → ℝ) :
    (∑ n ∈ Icc L A.card, ∑ U ∈ A.powersetCard n, g U) =
      ∑ U ∈ A.powerset.filter (fun U => L ≤ U.card), g U := by
  rw [sum_sigma' (s := Icc L A.card) (t := fun n => A.powersetCard n)
    (f := fun _n U => g U)]
  refine sum_bij'
      (fun p _ => p.2)
      (fun U _ => ⟨U.card, U⟩)
      ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hn := (mem_sigma.mp hp).1
    have hU := mem_powersetCard.mp (mem_sigma.mp hp).2
    exact mem_filter.mpr ⟨mem_powerset.mpr hU.1,
      hU.2 ▸ (mem_Icc.mp hn).1⟩
  · intro U hU
    have hUm := mem_filter.mp hU
    have hsub := mem_powerset.mp hUm.1
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hUm.2, card_le_card hsub⟩,
      mem_powersetCard.mpr ⟨hsub, rfl⟩⟩
  · intro p hp
    have hU := mem_powersetCard.mp (mem_sigma.mp hp).2
    simp [hU.2]
  · intro U _hU
    rfl
  · intro p _hp
    rfl

private theorem coreLinear_sum_cardinalityLayers_filter
    (A : Finset ℕ) (μ : Finset ℕ → ℝ) (s : Finset ℕ) :
    (∑ n ∈ s, cardinalityLayer A μ n) =
      ∑ U ∈ A.powerset.filter (fun U => U.card ∈ s), μ U := by
  simp_rw [cardinalityLayer]
  rw [sum_sigma' (s := s)
    (t := fun n => A.powerset.filter (fun U => U.card = n))
    (f := fun _n U => μ U)]
  refine sum_bij'
      (fun p _ => p.2)
      (fun U _ => ⟨U.card, U⟩)
      ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hn := (mem_sigma.mp hp).1
    have hU := mem_filter.mp (mem_sigma.mp hp).2
    exact mem_filter.mpr ⟨hU.1, hU.2 ▸ hn⟩
  · intro U hU
    have hUm := mem_filter.mp hU
    exact mem_sigma.mpr ⟨hUm.2, mem_filter.mpr ⟨hUm.1, rfl⟩⟩
  · intro p hp
    have hU := (mem_filter.mp (mem_sigma.mp hp).2).2
    simp [hU]
  · intro U _hU
    rfl
  · intro p _hp
    rfl

private theorem coreLinear_auxFrame_uniformMean_le
    (A : Finset ℕ) (n : ℕ) (test : Finset ℕ → ℝ) {C : ℝ}
    (hnA : n ≤ A.card) (htest : ∀ U ∈ A.powersetCard n, test U ≤ C) :
    auxFrame_uniformMean A n test ≤ C := by
  have hchoose : 0 < (A.card.choose n : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hnA)
  unfold auxFrame_uniformMean
  apply (div_le_iff₀ hchoose).2
  calc
    (∑ U ∈ A.powersetCard n, test U) ≤
        ∑ _U ∈ A.powersetCard n, C := sum_le_sum htest
    _ = (A.card.choose n : ℝ) * C := by
      rw [sum_const, card_powersetCard, nsmul_eq_mul]
    _ = C * (A.card.choose n : ℝ) := mul_comm _ _

theorem coreLinearFibreMean_eq_cardinalityLayers
    (B S y L : ℕ) (f : AddCircle (1 : ℝ) → ℝ) (σ : ResidueChoice S)
    (hSy : S ≤ y) :
    coreLinearFibreMean B S y L f σ =
      ∑ n ∈ Icc L (presieveSurvivors S σ).card,
        cardinalityLayer (presieveSurvivors S σ)
            (lateRootLaw S y (presieveSurvivors S σ)) n *
          auxFrame_uniformMean (presieveSurvivors S σ) n
            (fun U => f (coreLinearShapePhase B L U : AddCircle (1 : ℝ))) := by
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  let test : Finset ℕ → ℝ := fun U =>
    f (coreLinearShapePhase B L U : AddCircle (1 : ℝ))
  have hμ : CardinalitySymmetricMass A μ := by
    simpa [A, μ] using corePresieveLaw_cardinalitySymmetric S y σ hSy
  have hfilter :
      (∑ U ∈ A.powerset, μ U * if L ≤ U.card then test U else 0) =
        ∑ U ∈ A.powerset.filter (fun U => L ≤ U.card), μ U * test U := by
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
  have hpartition := coreLinear_sum_powerset_card_layers A L
    (fun U => μ U * test U)
  unfold coreLinearFibreMean
  change (∑ U ∈ A.powerset, μ U * if L ≤ U.card then test U else 0) = _
  rw [hfilter, ← hpartition]
  refine sum_congr rfl fun n hn => ?_
  exact coreLinear_cardinalityLayer_test_eq hμ n (mem_Icc.mp hn).2 test

/-- Finite good/high split on one actual late fibre.  The high term is the
genuine event `N > 2Mϑ`; every good exact layer is handled by the proved
Selberg/insertion contraction. -/
theorem eventually_coreLinearFibreMean_le_good_add_high
    (B : ℕ) (hB : 2 ≤ B)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    {C δ : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ G : ℝ in atTop,
      ∀ (S y L J : ℕ) (σ : ResidueChoice S),
        1 < G → ⌊G⌋₊ ≤ S → S ≤ y → 1 ≤ J → J < L →
        lateRetention S y ≤ (1 / 4 : ℝ) →
        1 ≤ G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) →
        G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) ≤
          (B : ℝ) * ((B : ℝ) - 1) →
        coreLinearFibreMean B S y L f σ ≤
          ∑ n ∈ (Icc L (presieveSurvivors S σ).card).filter (fun n : ℕ =>
              (n : ℝ) ≤ 2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y),
            cardinalityLayer (presieveSurvivors S σ)
                (lateRootLaw S y (presieveSurvivors S σ)) n *
              (12 * lateRetention S y * G / Real.log G *
                (((auxFrame_uniformMean (presieveSurvivors S σ) (n - 1)
                    (fun F => (subsetGap F (J - 1) : ℝ)) / G) + 1) *
                  ((∫ x : AddCircle (1 : ℝ), f x) +
                    δ * ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)))) +
                  δ * C)) +
            C * coreFiniteRootMixUpperFibreMass S y σ := by
  filter_upwards [eventually_coreLinear_presieve_uniformLayer_le
    B hB f hK hf0 hfC hδ hδ1] with G hlayer
  intro S y L J σ hG hfloor hSy hJ hJL hthetaQuarter hslo hshi
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  let θ := lateRetention S y
  let idx := Icc L A.card
  let good := idx.filter (fun n : ℕ => (n : ℝ) ≤ 2 * (A.card : ℝ) * θ)
  let bad := idx.filter (fun n : ℕ => ¬(n : ℝ) ≤ 2 * (A.card : ℝ) * θ)
  let test : Finset ℕ → ℝ := fun U =>
    f (coreLinearShapePhase B L U : AddCircle (1 : ℝ))
  let layerTerm : ℕ → ℝ := fun n =>
    cardinalityLayer A μ n * auxFrame_uniformMean A n test
  let goodBound : ℕ → ℝ := fun n =>
    cardinalityLayer A μ n *
      (12 * θ * G / Real.log G *
        (((auxFrame_uniformMean A (n - 1)
            (fun F => (subsetGap F (J - 1) : ℝ)) / G) + 1) *
          ((∫ x : AddCircle (1 : ℝ), f x) +
            δ * ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)))) + δ * C))
  have hμ : CardinalitySymmetricMass A μ := by
    simpa [A, μ] using corePresieveLaw_cardinalitySymmetric S y σ hSy
  have hθ0 : 0 ≤ θ := by
    simpa [θ] using coreLinear_lateRetention_nonneg S y
  have hC0 : 0 ≤ C := (hf0 0).trans (hfC 0)
  have hlayer0 : ∀ n, 0 ≤ cardinalityLayer A μ n := by
    intro n
    unfold cardinalityLayer
    exact sum_nonneg fun U hU => hμ.1 U (mem_filter.mp hU).1
  have hsplit :
      (∑ n ∈ idx, layerTerm n) =
        (∑ n ∈ good, layerTerm n) + (∑ n ∈ bad, layerTerm n) := by
    have h := sum_filter_add_sum_filter_not idx
      (fun n => (n : ℝ) ≤ 2 * (A.card : ℝ) * θ) layerTerm
    simpa [good, bad] using h.symm
  have hgood : ∑ n ∈ good, layerTerm n ≤ ∑ n ∈ good, goodBound n := by
    apply sum_le_sum
    intro n hn
    have hng := mem_filter.mp hn
    have hnI := mem_Icc.mp hng.1
    have hhalf : (n : ℝ) ≤ (A.card : ℝ) / 2 := by
      have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
      nlinarith
    have hbound := hlayer S y L J n σ hG hfloor hSy hJ hJL hnI.1 hnI.2
      hng.2 hhalf hslo hshi
    exact mul_le_mul_of_nonneg_left hbound (hlayer0 n)
  have hbadMean : ∀ n ∈ bad, auxFrame_uniformMean A n test ≤ C := by
    intro n hn
    have hnA := (mem_Icc.mp (mem_filter.mp hn).1).2
    exact coreLinear_auxFrame_uniformMean_le A n test hnA (fun U _ => hfC _)
  have hbad₁ : ∑ n ∈ bad, layerTerm n ≤
      C * ∑ n ∈ bad, cardinalityLayer A μ n := by
    calc
      (∑ n ∈ bad, layerTerm n) ≤
          ∑ n ∈ bad, cardinalityLayer A μ n * C := by
        exact sum_le_sum fun n hn =>
          mul_le_mul_of_nonneg_left (hbadMean n hn) (hlayer0 n)
      _ = C * ∑ n ∈ bad, cardinalityLayer A μ n := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro n _
        ring
  have hbadSub :
      A.powerset.filter (fun U => U.card ∈ bad) ⊆
        A.powerset.filter (fun U => 2 * ((A.card : ℝ) * θ) < (U.card : ℝ)) := by
    intro U hU
    have hUm := mem_filter.mp hU
    have hnbad := mem_filter.mp hUm.2
    exact mem_filter.mpr ⟨hUm.1, by
      rw [not_le] at hnbad
      nlinarith⟩
  have hbadMass :
      (∑ n ∈ bad, cardinalityLayer A μ n) ≤
        coreFiniteRootMixUpperFibreMass S y σ := by
    rw [coreLinear_sum_cardinalityLayers_filter]
    unfold coreFiniteRootMixUpperFibreMass
    change (∑ U ∈ A.powerset.filter (fun U => U.card ∈ bad), μ U) ≤
      ∑ U ∈ A.powerset.filter
        (fun U => 2 * ((A.card : ℝ) * θ) < (U.card : ℝ)), μ U
    exact sum_le_sum_of_subset_of_nonneg hbadSub (fun U hU _ => hμ.1 U (mem_filter.mp hU).1)
  have hbadFinal : ∑ n ∈ bad, layerTerm n ≤
      C * coreFiniteRootMixUpperFibreMass S y σ :=
    hbad₁.trans (mul_le_mul_of_nonneg_left hbadMass hC0)
  rw [coreLinearFibreMean_eq_cardinalityLayers B S y L f σ hSy]
  change (∑ n ∈ idx, layerTerm n) ≤ _
  rw [hsplit]
  exact add_le_add hgood hbadFinal

/-! ### Exact early-root and finite-root-mixture identities -/

theorem coreLinearActualRootMean_eq_avg_fibres
    (B S y L : ℕ) (f : AddCircle (1 : ℝ) → ℝ) (hSy : S ≤ y) :
    coreLinearActualRootMean B y S L f =
      (∑ σ : ResidueChoice S, coreLinearFibreMean B S y L f σ) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  let g : Finset ℕ → ℝ := fun U =>
    if L ≤ U.card then f (coreLinearShapePhase B L U : AddCircle (1 : ℝ)) else 0
  have hU : ∀ U,
      actualRootLaw y S U =
        (∑ σ : ResidueChoice S,
          lateRootLaw S y (presieveSurvivors S σ) U) /
          (Fintype.card (ResidueChoice S) : ℝ) :=
    fun U => coreActualRootLaw_eq_avg_presieve S y hSy U
  have hswap :
      (∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U * g U) =
        (∑ σ : ResidueChoice S,
          ∑ U ∈ (offsetWindow S).powerset,
            lateRootLaw S y (presieveSurvivors S σ) U * g U) /
          (Fintype.card (ResidueChoice S) : ℝ) := by
    calc
      _ = ∑ U ∈ (offsetWindow S).powerset,
          (((∑ σ : ResidueChoice S,
            lateRootLaw S y (presieveSurvivors S σ) U) * g U) /
              (Fintype.card (ResidueChoice S) : ℝ)) := by
        refine sum_congr rfl fun U _ => ?_
        rw [hU U]
        ring
      _ = (∑ U ∈ (offsetWindow S).powerset,
          (∑ σ : ResidueChoice S,
            lateRootLaw S y (presieveSurvivors S σ) U) * g U) /
              (Fintype.card (ResidueChoice S) : ℝ) := by
        rw [Finset.sum_div]
      _ = _ := by
        congr 1
        simp_rw [sum_mul]
        rw [sum_comm]
  have hfibre : ∀ σ : ResidueChoice S,
      (∑ U ∈ (offsetWindow S).powerset,
          lateRootLaw S y (presieveSurvivors S σ) U * g U) =
        coreLinearFibreMean B S y L f σ := by
    intro σ
    let A := presieveSurvivors S σ
    have hA : A ⊆ offsetWindow S := by
      simpa [A, offsetWindow] using corePresieveSurvivors_subset_Icc S σ
    have hsub : A.powerset ⊆ (offsetWindow S).powerset := powerset_mono.mpr hA
    have hext := sum_subset
      (f := fun U => lateRootLaw S y A U * g U) hsub (fun U _hU hnot => by
      have hnotA : ¬ U ⊆ A := fun hUA => hnot (mem_powerset.mpr hUA)
      have hz : lateRootLaw S y A U = 0 := by
        have hempty :
            ((univ : Finset (LateResidueChoice S y)).filter
              fun τ => lateSurvivors S y A τ = U) = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro τ hτ
          apply hnotA
          have heq := (mem_filter.mp hτ).2
          rw [← heq]
          exact filter_subset _ _
        simp [lateRootLaw, lateProductMass, hempty]
      simpa [A, hz])
    unfold coreLinearFibreMean
    change (∑ U ∈ (offsetWindow S).powerset,
        lateRootLaw S y A U * g U) = ∑ U ∈ A.powerset,
          lateRootLaw S y A U * g U
    exact hext.symm
  unfold coreLinearActualRootMean
  change (∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U * g U) = _
  rw [hswap]
  congr 1
  exact sum_congr rfl fun σ _ => hfibre σ

theorem coreLinearFiniteRootMean_eq_weighted
    (B X S L : ℕ) (f : AddCircle (1 : ℝ) → ℝ) :
    coreLinearFiniteRootMean B X S L f =
      (∑ t ∈ mixScale X, mixWeightV t *
        coreLinearActualRootMean B (sieveCutoff (t : ℝ)) S L f) /
        mixZ X := by
  rw [coreLinearFiniteRootMean, coreStopped_positive_test_eq_pushforward]
  simp_rw [CoreLinearInsertion.shapePhase_firstL]
  let g : Finset ℕ → ℝ := fun U =>
    if L ≤ U.card then f (coreLinearShapePhase B L U : AddCircle (1 : ℝ)) else 0
  change (∑ U ∈ (offsetWindow S).powerset, finiteRootMix X S U * g U) = _
  unfold finiteRootMix coreLinearActualRootMean
  have hterm : ∀ U ∈ (offsetWindow S).powerset,
      ((∑ t ∈ mixScale X, mixWeightV t *
        actualRootLaw (sieveCutoff (t : ℝ)) S U) / mixZ X) * g U =
      ((∑ t ∈ mixScale X, mixWeightV t *
        actualRootLaw (sieveCutoff (t : ℝ)) S U) * g U) / mixZ X := by
    intro U _
    ring
  rw [sum_congr rfl hterm]
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [mul_sum]
  apply sum_congr rfl
  intro U _
  ring

end

end PrimeGapNormality.Prime
