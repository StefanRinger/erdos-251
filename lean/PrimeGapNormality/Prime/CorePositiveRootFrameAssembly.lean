import PrimeGapNormality.Prime.CorePositiveFrameAssembly
import PrimeGapNormality.Prime.CoreOriginalDeletedFrameTail
import PrimeGapNormality.Prime.CoreLinearInsertionAction

/-!
# Positive-test assembly through the actual rooted laws

The exact finite insertion estimate is aggregated here through the literal
late-root cardinality weights, the uniform exposed-presieve law, and the
normalized finite root mixture.  Two exceptional pieces remain visibly
measured in the original law:

* the genuine high-count event `N > 2 M θ`;
* a fixed-rank deleted-frame cutoff, removed before frame disintegration.

The only generic input is a finite slot-sum majorant on good layers.  It is
an intermediate interface for the Selberg estimate, not an assumed final
model bound.
-/

open Finset
open scoped BigOperators Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-- Original high-cardinality mean on one exposed presieve fibre. -/
def corePositiveFibreMean (S y L : ℕ) (test : Finset ℕ → ℝ)
    (σ : ResidueChoice S) : ℝ :=
  ∑ U ∈ (presieveSurvivors S σ).powerset,
    lateRootLaw S y (presieveSurvivors S σ) U *
      if L ≤ U.card then test U else 0

/-- Original high-cardinality mean under the normalized finite root mix. -/
def corePositiveFiniteRootMean (X S L : ℕ) (test : Finset ℕ → ℝ) : ℝ :=
  ∑ U ∈ (offsetWindow S).powerset, finiteRootMix X S U *
    if L ≤ U.card then test U else 0

private theorem corePositiveRoot_cardinalityLayer_nonneg
    {A : Finset ℕ} {μ : Finset ℕ → ℝ}
    (hμ : CardinalitySymmetricMass A μ) (n : ℕ) :
    0 ≤ cardinalityLayer A μ n := by
  unfold cardinalityLayer
  exact sum_nonneg fun U hU ↦ hμ.1 U (mem_filter.mp hU).1

private theorem corePositiveRoot_layer_test_eq
    {A : Finset ℕ} {μ : Finset ℕ → ℝ}
    (hμ : CardinalitySymmetricMass A μ) (n : ℕ) (hnA : n ≤ A.card)
    (test : Finset ℕ → ℝ) :
    (∑ U ∈ A.powersetCard n, μ U * test U) =
      cardinalityLayer A μ n * auxFrame_uniformMean A n test := by
  let c := uniformLayerWeight A μ n
  have hterm : ∀ U ∈ A.powersetCard n, μ U = c := by
    intro U hU
    have hUm := mem_powersetCard.mp hU
    simpa [c, hUm.2] using mu_eq_uniformLayerWeight hμ hUm.1
  have hlayer : cardinalityLayer A μ n = (A.card.choose n : ℝ) * c := by
    unfold cardinalityLayer
    rw [show A.powerset.filter (fun U ↦ U.card = n) = A.powersetCard n from
      powersetCard_eq_filter.symm]
    rw [sum_congr rfl hterm, sum_const, card_powersetCard, nsmul_eq_mul]
  have hchoose : (A.card.choose n : ℝ) ≠ 0 := auxFrame_choose_ne_zero hnA
  calc
    (∑ U ∈ A.powersetCard n, μ U * test U) =
        ∑ U ∈ A.powersetCard n, c * test U := by
      exact sum_congr rfl fun U hU ↦ by rw [hterm U hU]
    _ = c * ∑ U ∈ A.powersetCard n, test U := by rw [Finset.mul_sum]
    _ = cardinalityLayer A μ n * auxFrame_uniformMean A n test := by
      rw [hlayer]
      unfold auxFrame_uniformMean
      field_simp [hchoose]

private theorem corePositiveRoot_sum_powerset_layers
    (A : Finset ℕ) (L : ℕ) (g : Finset ℕ → ℝ) :
    (∑ n ∈ Icc L A.card, ∑ U ∈ A.powersetCard n, g U) =
      ∑ U ∈ A.powerset.filter (fun U ↦ L ≤ U.card), g U := by
  rw [sum_sigma' (s := Icc L A.card) (t := fun n ↦ A.powersetCard n)
    (f := fun _ U ↦ g U)]
  refine sum_bij'
      (fun p _ ↦ p.2) (fun U _ ↦ ⟨U.card, U⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hn := mem_Icc.mp (mem_sigma.mp hp).1
    have hU := mem_powersetCard.mp (mem_sigma.mp hp).2
    exact mem_filter.mpr ⟨mem_powerset.mpr hU.1, hU.2 ▸ hn.1⟩
  · intro U hU
    have hUm := mem_filter.mp hU
    have hsub := mem_powerset.mp hUm.1
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hUm.2, card_le_card hsub⟩,
      mem_powersetCard.mpr ⟨hsub, rfl⟩⟩
  · intro p hp
    have hU := mem_powersetCard.mp (mem_sigma.mp hp).2
    simp [hU.2]
  · intro U _
    rfl
  · intro p _
    rfl

private theorem corePositiveRoot_sum_layers_filter
    (A : Finset ℕ) (μ : Finset ℕ → ℝ) (s : Finset ℕ) :
    (∑ n ∈ s, cardinalityLayer A μ n) =
      ∑ U ∈ A.powerset.filter (fun U ↦ U.card ∈ s), μ U := by
  simp_rw [cardinalityLayer]
  rw [sum_sigma' (s := s)
    (t := fun n ↦ A.powerset.filter (fun U ↦ U.card = n))
    (f := fun _ U ↦ μ U)]
  refine sum_bij'
      (fun p _ ↦ p.2) (fun U _ ↦ ⟨U.card, U⟩) ?_ ?_ ?_ ?_ ?_
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
  · intro U _
    rfl
  · intro p _
    rfl

private theorem corePositiveRoot_uniformMean_le_const
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

/-- Exact cardinality disintegration on a genuine late-root fibre. -/
theorem corePositiveFibreMean_eq_cardinalityLayers
    (S y L : ℕ) (test : Finset ℕ → ℝ) (σ : ResidueChoice S)
    (hSy : S ≤ y) :
    corePositiveFibreMean S y L test σ =
      ∑ n ∈ Icc L (presieveSurvivors S σ).card,
        cardinalityLayer (presieveSurvivors S σ)
            (lateRootLaw S y (presieveSurvivors S σ)) n *
          auxFrame_uniformMean (presieveSurvivors S σ) n test := by
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  have hμ : CardinalitySymmetricMass A μ := by
    simpa [A, μ] using corePresieveLaw_cardinalitySymmetric S y σ hSy
  have hfilter :
      (∑ U ∈ A.powerset, μ U * if L ≤ U.card then test U else 0) =
        ∑ U ∈ A.powerset.filter (fun U ↦ L ≤ U.card), μ U * test U := by
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
  have hpartition := corePositiveRoot_sum_powerset_layers A L
    (fun U ↦ μ U * test U)
  unfold corePositiveFibreMean
  change (∑ U ∈ A.powerset, μ U * if L ≤ U.card then test U else 0) = _
  rw [hfilter, ← hpartition]
  exact sum_congr rfl fun n hn ↦
    corePositiveRoot_layer_test_eq hμ n (mem_Icc.mp hn).2 test

/-- Good layers use the finite slot majorant; bad layers are charged under
the original late-root law before any frame reweighting. -/
theorem corePositiveFibreMean_le_frame_add_high
    (S y L j : ℕ) (σ : ResidueChoice S)
    (test frameBound : Finset ℕ → ℝ) {C : ℝ}
    (hSy : S ≤ y) (hjL : j + 1 < L)
    (htest0 : ∀ U, 0 ≤ test U) (htestC : ∀ U, test U ≤ C)
    (hframe0 : ∀ F, 0 ≤ frameBound F)
    (hθ : 0 < lateRetention S y)
    (hθ4 : lateRetention S y ≤ (1 : ℝ) / 4)
    (hslot : ∀ n ∈ (Icc L (presieveSurvivors S σ).card).filter
        (fun n : ℕ ↦ (n : ℝ) ≤
          2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y),
      ∀ F ∈ (presieveSurvivors S σ).powersetCard (n - 1),
        auxFrame_slotInsertSum (presieveSurvivors S σ) j test F ≤ frameBound F) :
    corePositiveFibreMean S y L test σ ≤
      (4 : ℝ) * lateRetention S y *
        (∑ n ∈ Icc L (presieveSurvivors S σ).card,
          cardinalityLayer (presieveSurvivors S σ)
              (lateRootLaw S y (presieveSurvivors S σ)) n *
            auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) frameBound) +
      C * coreFiniteRootMixUpperFibreMass S y σ := by
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  let θ := lateRetention S y
  let idx := Icc L A.card
  let good := idx.filter (fun n : ℕ ↦ (n : ℝ) ≤ 2 * (A.card : ℝ) * θ)
  let bad := idx.filter (fun n : ℕ ↦ ¬(n : ℝ) ≤ 2 * (A.card : ℝ) * θ)
  let layerTerm : ℕ → ℝ := fun n ↦
    cardinalityLayer A μ n * auxFrame_uniformMean A n test
  let frameTerm : ℕ → ℝ := fun n ↦
    cardinalityLayer A μ n * auxFrame_uniformMean A (n - 1) frameBound
  have hμ : CardinalitySymmetricMass A μ := by
    simpa [A, μ] using corePresieveLaw_cardinalitySymmetric S y σ hSy
  have hlayer0 : ∀ n, 0 ≤ cardinalityLayer A μ n :=
    corePositiveRoot_cardinalityLayer_nonneg hμ
  have hframeTerm0 : ∀ n, 0 ≤ frameTerm n := by
    intro n
    exact mul_nonneg (hlayer0 n) (auxFrame_uniformMean_nonneg hframe0)
  have hsplit : (∑ n ∈ idx, layerTerm n) =
      (∑ n ∈ good, layerTerm n) + (∑ n ∈ bad, layerTerm n) := by
    have h := sum_filter_add_sum_filter_not idx
      (fun n : ℕ ↦ (n : ℝ) ≤ 2 * (A.card : ℝ) * θ) layerTerm
    simpa [good, bad] using h.symm
  have hgood₁ : (∑ n ∈ good, layerTerm n) ≤
      ∑ n ∈ good, (4 : ℝ) * θ * frameTerm n := by
    apply sum_le_sum
    intro n hn
    have hng := mem_filter.mp hn
    have hnI := mem_Icc.mp hng.1
    have hn1 : 1 ≤ n := by omega
    have hjn : j + 1 < n := hjL.trans_le hnI.1
    have hng' : n ∈
        (Icc L (presieveSurvivors S σ).card).filter
          (fun n : ℕ ↦ (n : ℝ) ≤
            2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y) := by
      apply mem_filter.mpr
      exact ⟨by simpa [idx, A] using hng.1,
        by simpa [A, θ] using hng.2⟩
    have hpoint := corePositive_goodLayer_le_frameBound A μ n j test frameBound
      hμ hn1 hnI.2 hjn
      (fun x hx ↦
        (mem_Icc.mp (corePresieveSurvivors_subset_Icc S σ hx)).1)
      htest0 hframe0
      (hslot n hng') hng.2 hθ hθ4
    simpa [layerTerm, frameTerm, A, μ, θ, mul_assoc, mul_left_comm, mul_comm]
      using hpoint
  have hgood₂ : (∑ n ∈ good, frameTerm n) ≤ ∑ n ∈ idx, frameTerm n :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun n hn _ ↦ hframeTerm0 n)
  have hfourθ0 : 0 ≤ (4 : ℝ) * θ := mul_nonneg (by norm_num) hθ.le
  have hgood : (∑ n ∈ good, layerTerm n) ≤
      (4 : ℝ) * θ * ∑ n ∈ idx, frameTerm n := by
    calc
      (∑ n ∈ good, layerTerm n) ≤
          ∑ n ∈ good, (4 : ℝ) * θ * frameTerm n := hgood₁
      _ = (4 : ℝ) * θ * ∑ n ∈ good, frameTerm n := by
        rw [Finset.mul_sum]
      _ ≤ (4 : ℝ) * θ * ∑ n ∈ idx, frameTerm n :=
        mul_le_mul_of_nonneg_left hgood₂ hfourθ0
  have hC0 : 0 ≤ C := (htest0 ∅).trans (htestC ∅)
  have hbadMean : ∀ n ∈ bad, auxFrame_uniformMean A n test ≤ C := by
    intro n hn
    exact corePositiveRoot_uniformMean_le_const A n test
      (mem_Icc.mp (mem_filter.mp hn).1).2 (fun U _ ↦ htestC U)
  have hbad₁ : (∑ n ∈ bad, layerTerm n) ≤
      C * ∑ n ∈ bad, cardinalityLayer A μ n := by
    calc
      (∑ n ∈ bad, layerTerm n) ≤
          ∑ n ∈ bad, cardinalityLayer A μ n * C :=
        sum_le_sum fun n hn ↦
          mul_le_mul_of_nonneg_left (hbadMean n hn) (hlayer0 n)
      _ = C * ∑ n ∈ bad, cardinalityLayer A μ n := by
        rw [Finset.mul_sum]
        exact sum_congr rfl fun n _ ↦ by ring
  have hbadSub : A.powerset.filter (fun U ↦ U.card ∈ bad) ⊆
      A.powerset.filter (fun U ↦ 2 * ((A.card : ℝ) * θ) < (U.card : ℝ)) := by
    intro U hU
    have hUm := mem_filter.mp hU
    have hnbad := (mem_filter.mp hUm.2).2
    rw [not_le] at hnbad
    exact mem_filter.mpr ⟨hUm.1, by nlinarith⟩
  have hbadMass : (∑ n ∈ bad, cardinalityLayer A μ n) ≤
      coreFiniteRootMixUpperFibreMass S y σ := by
    rw [corePositiveRoot_sum_layers_filter]
    unfold coreFiniteRootMixUpperFibreMass
    change (∑ U ∈ A.powerset.filter (fun U ↦ U.card ∈ bad), μ U) ≤
      ∑ U ∈ A.powerset.filter
        (fun U ↦ 2 * ((A.card : ℝ) * θ) < (U.card : ℝ)), μ U
    exact sum_le_sum_of_subset_of_nonneg hbadSub
      (fun U hU _ ↦ hμ.1 U (mem_filter.mp hU).1)
  have hbad : (∑ n ∈ bad, layerTerm n) ≤
      C * coreFiniteRootMixUpperFibreMass S y σ :=
    hbad₁.trans (mul_le_mul_of_nonneg_left hbadMass hC0)
  rw [corePositiveFibreMean_eq_cardinalityLayers S y L test σ hSy]
  change (∑ n ∈ idx, layerTerm n) ≤ _
  rw [hsplit]
  simpa [frameTerm, idx, A, μ, θ] using add_le_add hgood hbad

/-! ## Early-root, auxiliary-frame, and finite-mixture identities -/

/-- The actual rooted high mean is the uniform early-root average of the
genuine late fibres. -/
theorem corePositive_highMean_eq_avg_fibres
    (S y L : ℕ) (test : Finset ℕ → ℝ) (hSy : S ≤ y) :
    CoreOriginalDeletedFrame.highMean y S L test =
      (∑ σ : ResidueChoice S, corePositiveFibreMean S y L test σ) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  let g : Finset ℕ → ℝ := fun U ↦ if L ≤ U.card then test U else 0
  have hU : ∀ U,
      actualRootLaw y S U =
        (∑ σ : ResidueChoice S,
          lateRootLaw S y (presieveSurvivors S σ) U) /
          (Fintype.card (ResidueChoice S) : ℝ) :=
    fun U ↦ coreActualRootLaw_eq_avg_presieve S y hSy U
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
        exact sum_congr rfl fun U _ ↦ by rw [hU U]; ring
      _ = (∑ U ∈ (offsetWindow S).powerset,
          (∑ σ : ResidueChoice S,
            lateRootLaw S y (presieveSurvivors S σ) U) * g U) /
              (Fintype.card (ResidueChoice S) : ℝ) := by
        rw [Finset.sum_div]
      _ = _ := by
        congr 1
        simp_rw [Finset.sum_mul]
        rw [sum_comm]
  have hfibre : ∀ σ : ResidueChoice S,
      (∑ U ∈ (offsetWindow S).powerset,
          lateRootLaw S y (presieveSurvivors S σ) U * g U) =
        corePositiveFibreMean S y L test σ := by
    intro σ
    let A := presieveSurvivors S σ
    have hA : A ⊆ offsetWindow S := by
      simpa [A, offsetWindow] using corePresieveSurvivors_subset_Icc S σ
    have hsub : A.powerset ⊆ (offsetWindow S).powerset := powerset_mono.mpr hA
    have hext := sum_subset
      (f := fun U ↦ lateRootLaw S y A U * g U) hsub (fun U _ hnot ↦ by
      have hnotA : ¬ U ⊆ A := fun hUA ↦ hnot (mem_powerset.mpr hUA)
      have hz : lateRootLaw S y A U = 0 := by
        have hempty :
            ((univ : Finset (LateResidueChoice S y)).filter
              fun τ ↦ lateSurvivors S y A τ = U) = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro τ hτ
          apply hnotA
          have heq := (mem_filter.mp hτ).2
          rw [← heq]
          exact filter_subset _ _
        simp [lateRootLaw, lateProductMass, hempty]
      simp [hz])
    unfold corePositiveFibreMean
    change (∑ U ∈ (offsetWindow S).powerset,
        lateRootLaw S y A U * g U) =
      ∑ U ∈ A.powerset, lateRootLaw S y A U * g U
    exact hext.symm
  unfold CoreOriginalDeletedFrame.highMean
  change (∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U * g U) = _
  rw [hswap]
  exact congrArg (fun z : ℝ ↦ z / (Fintype.card (ResidueChoice S) : ℝ))
    (sum_congr rfl fun σ _ ↦ hfibre σ)

/-- Integrating any frame test against the genuine one-cutoff auxiliary
mass equals the early-root/cardinality average of its uniform layer means. -/
theorem corePositive_auxiliaryLayerFrame_expectation
    (S y L : ℕ) (frameBound : Finset ℕ → ℝ) :
    (∑ F ∈ (offsetWindow S).powerset,
        coreAuxiliaryLayerFrameMass S y L F * frameBound F) =
      (∑ σ : ResidueChoice S,
        ∑ n ∈ Icc L (presieveSurvivors S σ).card,
          cardinalityLayer (presieveSurvivors S σ)
              (lateRootLaw S y (presieveSurvivors S σ)) n *
            auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) frameBound) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  unfold coreAuxiliaryLayerFrameMass
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun z : ℝ ↦ z / (Fintype.card (ResidueChoice S) : ℝ))
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  simp_rw [mul_assoc]
  rw [← mul_sum]
  have hsub : presieveSurvivors S σ ⊆ offsetWindow S := by
    simpa only [offsetWindow] using corePresieveSurvivors_subset_Icc S σ
  rw [coreAuxUniformFrameMass_expectation _ _ _ hsub frameBound]

/-- Aggregated good/high inequality at one actual sieve cutoff. -/
theorem corePositive_highMean_le_frame_add_high
    (S y L j : ℕ) (test frameBound : Finset ℕ → ℝ) {C : ℝ}
    (hSy : S ≤ y) (hjL : j + 1 < L)
    (htest0 : ∀ U, 0 ≤ test U) (htestC : ∀ U, test U ≤ C)
    (hframe0 : ∀ F, 0 ≤ frameBound F)
    (hθ : 0 < lateRetention S y)
    (hθ4 : lateRetention S y ≤ (1 : ℝ) / 4)
    (hslot : ∀ σ : ResidueChoice S,
      ∀ n ∈ (Icc L (presieveSurvivors S σ).card).filter
        (fun n : ℕ ↦ (n : ℝ) ≤
          2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y),
      ∀ F ∈ (presieveSurvivors S σ).powersetCard (n - 1),
        auxFrame_slotInsertSum (presieveSurvivors S σ) j test F ≤ frameBound F) :
    CoreOriginalDeletedFrame.highMean y S L test ≤
      (4 : ℝ) * lateRetention S y *
        (∑ F ∈ (offsetWindow S).powerset,
          coreAuxiliaryLayerFrameMass S y L F * frameBound F) +
      C * coreFiniteRootMixUpperRootMass S y := by
  let frameFibre : ResidueChoice S → ℝ := fun σ ↦
    ∑ n ∈ Icc L (presieveSurvivors S σ).card,
      cardinalityLayer (presieveSurvivors S σ)
          (lateRootLaw S y (presieveSurvivors S σ)) n *
        auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) frameBound
  have hfibre : ∀ σ : ResidueChoice S,
      corePositiveFibreMean S y L test σ ≤
        (4 : ℝ) * lateRetention S y * frameFibre σ +
          C * coreFiniteRootMixUpperFibreMass S y σ := by
    intro σ
    simpa [frameFibre] using corePositiveFibreMean_le_frame_add_high
      S y L j σ test frameBound hSy hjL htest0 htestC hframe0 hθ hθ4 (hslot σ)
  have hsum := sum_le_sum fun σ (_hσ : σ ∈ (univ : Finset (ResidueChoice S))) ↦
    hfibre σ
  have hcard0 : 0 ≤ (Fintype.card (ResidueChoice S) : ℝ) := Nat.cast_nonneg _
  rw [corePositive_highMean_eq_avg_fibres S y L test hSy]
  refine (div_le_div_of_nonneg_right hsum hcard0).trans_eq ?_
  rw [sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hframe := corePositive_auxiliaryLayerFrame_expectation S y L frameBound
  have hframe' :
      ((∑ σ : ResidueChoice S, frameFibre σ) /
          (Fintype.card (ResidueChoice S) : ℝ)) =
        ∑ F ∈ (offsetWindow S).powerset,
          coreAuxiliaryLayerFrameMass S y L F * frameBound F := by
    simpa only [frameFibre] using hframe.symm
  unfold coreFiniteRootMixUpperRootMass
  calc
    (((4 : ℝ) * lateRetention S y * ∑ σ, frameFibre σ) +
          C * ∑ σ, coreFiniteRootMixUpperFibreMass S y σ) /
        (Fintype.card (ResidueChoice S) : ℝ) =
      (4 : ℝ) * lateRetention S y *
          ((∑ σ, frameFibre σ) /
            (Fintype.card (ResidueChoice S) : ℝ)) +
        C * ((∑ σ, coreFiniteRootMixUpperFibreMass S y σ) /
          (Fintype.card (ResidueChoice S) : ℝ)) := by ring
    _ = _ := by rw [hframe']

/-- Exact normalized finite-root-mixture disintegration of an arbitrary
configuration test. -/
theorem corePositiveFiniteRootMean_eq_weighted
    (X S L : ℕ) (test : Finset ℕ → ℝ) :
    corePositiveFiniteRootMean X S L test =
      (∑ t ∈ mixScale X, mixWeightV t *
        CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L test) /
        mixZ X := by
  let g : Finset ℕ → ℝ := fun U ↦ if L ≤ U.card then test U else 0
  unfold corePositiveFiniteRootMean finiteRootMix
  change (∑ U ∈ (offsetWindow S).powerset,
    ((∑ t ∈ mixScale X, mixWeightV t *
      actualRootLaw (sieveCutoff (t : ℝ)) S U) / mixZ X) * g U) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun z : ℝ ↦ z / mixZ X)
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  unfold CoreOriginalDeletedFrame.highMean
  rw [mul_sum]
  exact sum_congr rfl fun U _ ↦ by ring

/-- Any one-cutoff bound transports through the literal normalized root
mixture, without changing its weights. -/
theorem corePositiveFiniteRootMean_le_of_root
    (X S L : ℕ) (test : Finset ℕ → ℝ) (rootBound : ℕ → ℝ)
    (hZ : 0 < mixZ X)
    (hroot : ∀ t ∈ mixScale X,
      CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L test ≤
        rootBound t) :
    corePositiveFiniteRootMean X S L test ≤
      (∑ t ∈ mixScale X, mixWeightV t * rootBound t) / mixZ X := by
  rw [corePositiveFiniteRootMean_eq_weighted]
  apply div_le_div_of_nonneg_right _ hZ.le
  exact sum_le_sum fun t ht ↦
    mul_le_mul_of_nonneg_left (hroot t ht) (mixWeightV_nonneg t)

/-! ## Fixed original deleted-frame cutoff -/

def corePositiveFrameBad (I : Finset ℕ) (j : ℕ) (G R : ℝ)
    (U : Finset ℕ) : Prop :=
  ∃ i ∈ I, R <
    (subsetGap (CoreOriginalDeletedFrame.deleted (j + 1) U) i : ℝ) / G

def corePositiveCutTest (I : Finset ℕ) (j : ℕ) (G R : ℝ)
    (test : Finset ℕ → ℝ) (U : Finset ℕ) : ℝ :=
  if corePositiveFrameBad I j G R U then 0 else test U

/-- In an insertion fibre, deleting the fixed inserted rank recovers the
literal frame. -/
theorem corePositive_deleted_insert_eq
    {A F : Finset ℕ} {j u : ℕ}
    (hu : u ∈ openSlot A (F.sort (· ≤ ·)) j) :
    CoreOriginalDeletedFrame.deleted (j + 1) (insert u F) = F := by
  have huSlot :
      (CoreLinearInsertion.insertionSlot F (j + 1)).1 < u ∧
        u < (CoreLinearInsertion.insertionSlot F (j + 1)).2 := by
    simpa [CoreLinearInsertion.insertionSlot] using (mem_openSlot.mp hu).2
  have horder : orderStat (insert u F) (j + 1) = u :=
    CoreLinearInsertion.orderStat_insert_at (by omega) huSlot
  unfold CoreOriginalDeletedFrame.deleted
  rw [horder, erase_insert (not_mem_of_mem_openSlot_sort hu)]

/-- Consequently the cutoff is constant throughout each insertion fibre. -/
theorem corePositiveFrameBad_insert_iff
    {A F : Finset ℕ} {j u : ℕ} (I : Finset ℕ) (G R : ℝ)
    (hu : u ∈ openSlot A (F.sort (· ≤ ·)) j) :
    corePositiveFrameBad I j G R (insert u F) ↔
      ∃ i ∈ I, R < (subsetGap F i : ℝ) / G := by
  simp only [corePositiveFrameBad, corePositive_deleted_insert_eq hu]

private theorem corePositive_highMean_const_mul
    (y S L : ℕ) (C : ℝ) (f : Finset ℕ → ℝ) :
    CoreOriginalDeletedFrame.highMean y S L (fun U ↦ C * f U) =
      C * CoreOriginalDeletedFrame.highMean y S L f := by
  unfold CoreOriginalDeletedFrame.highMean
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro U _
  by_cases hU : L ≤ U.card <;> simp [hU] <;> ring

/-- The deleted-frame cutoff is charged under the original rooted law,
before the good part is disintegrated into auxiliary frames. -/
theorem corePositive_highMean_le_cut_add_originalBad
    (y S L : ℕ) (I : Finset ℕ) (j : ℕ) (G R : ℝ)
    (test : Finset ℕ → ℝ) {C : ℝ}
    (htest0 : ∀ U, 0 ≤ test U) (htestC : ∀ U, test U ≤ C) :
    CoreOriginalDeletedFrame.highMean y S L test ≤
      CoreOriginalDeletedFrame.highMean y S L
        (corePositiveCutTest I j G R test) +
      C * CoreOriginalDeletedFrame.highMean y S L
        (fun U ↦ if corePositiveFrameBad I j G R U then 1 else 0) := by
  have hpoint : ∀ U, L ≤ U.card →
      test U ≤ corePositiveCutTest I j G R test U +
        C * (if corePositiveFrameBad I j G R U then 1 else 0) := by
    intro U _
    by_cases hbad : corePositiveFrameBad I j G R U
    · simp [corePositiveCutTest, hbad, htestC U]
    · simp [corePositiveCutTest, hbad]
  have hmono := CoreOriginalDeletedFrame.highMean_mono y S L hpoint
  rw [CoreOriginalDeletedFrame.highMean_add,
    corePositive_highMean_const_mul] at hmono
  exact hmono

/-- Quantitative version of the same original-law cutoff, using only the
proved first moments of the fixed-rank deleted gaps. -/
theorem corePositive_highMean_le_cut_add_originalTail
    (y S L : ℕ) (I : Finset ℕ) (j : ℕ) (G R : ℝ)
    (test : Finset ℕ → ℝ) {C : ℝ}
    (hjL : j + 1 ≤ L) (hI : ∀ i ∈ I, i + 1 < L)
    (hG : 0 < G) (hR : 0 < R)
    (htest0 : ∀ U, 0 ≤ test U) (htestC : ∀ U, test U ≤ C) :
    CoreOriginalDeletedFrame.highMean y S L test ≤
      CoreOriginalDeletedFrame.highMean y S L
        (corePositiveCutTest I j G R test) +
      C * ((2 * (I.card : ℝ)) / (R * G * eulerProdNat y)) := by
  have hC0 : 0 ≤ C := (htest0 ∅).trans (htestC ∅)
  have hsplit := corePositive_highMean_le_cut_add_originalBad
    y S L I j G R test htest0 htestC
  refine hsplit.trans (_root_.add_le_add le_rfl
    (mul_le_mul_of_nonneg_left ?_ hC0))
  let bad : Finset ℕ → ℝ := fun U ↦
    if corePositiveFrameBad I j G R U then 1 else 0
  let originalBad : Finset ℕ → ℝ := fun U ↦
    if ∃ i ∈ I,
        R < (subsetGap (CoreOriginalDeletedFrame.deleted (j + 1) U) i : ℝ) / G
      then 1 else 0
  have hfun : bad = originalBad := by
    funext U
    by_cases hU : ∃ i ∈ I,
        R < (subsetGap (CoreOriginalDeletedFrame.deleted (j + 1) U) i : ℝ) / G
    · simp [bad, originalBad, corePositiveFrameBad, hU]
    · simp [bad, originalBad, corePositiveFrameBad, hU]
  change CoreOriginalDeletedFrame.highMean y S L bad ≤ _
  rw [hfun]
  exact CoreOriginalDeletedFrame.original_bad_frame_mass_le
    y S L (j + 1) I (by omega) hjL hI hG hR

/-! ## Full normalized finite-root-mixture assembly -/

/-- Finite positive-test assembly with both exceptional pieces measured
under the original configuration law.  The slot estimate remains the
visible intermediate input to be discharged by the finite Selberg theorem. -/
theorem corePositiveFiniteRootMean_le_frame_high_originalBad
    (X S L j : ℕ) (I : Finset ℕ) (G R : ℝ)
    (test : Finset ℕ → ℝ) (frameBound : ℕ → Finset ℕ → ℝ)
    {C : ℝ} (hZ : 0 < mixZ X) (hjL : j + 1 < L)
    (htest0 : ∀ U, 0 ≤ test U) (htestC : ∀ U, test U ≤ C)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hθ : ∀ t ∈ mixScale X, 0 < lateRetention S (sieveCutoff (t : ℝ)))
    (hθ4 : ∀ t ∈ mixScale X,
      lateRetention S (sieveCutoff (t : ℝ)) ≤ (1 : ℝ) / 4)
    (hframe0 : ∀ t ∈ mixScale X, ∀ F, 0 ≤ frameBound t F)
    (hslot : ∀ t ∈ mixScale X, ∀ σ : ResidueChoice S,
      ∀ n ∈ (Icc L (presieveSurvivors S σ).card).filter
        (fun n : ℕ ↦ (n : ℝ) ≤
          2 * ((presieveSurvivors S σ).card : ℝ) *
            lateRetention S (sieveCutoff (t : ℝ))),
      ∀ F ∈ (presieveSurvivors S σ).powersetCard (n - 1),
        auxFrame_slotInsertSum (presieveSurvivors S σ) j
            (corePositiveCutTest I j G R test) F ≤ frameBound t F) :
    corePositiveFiniteRootMean X S L test ≤
      (∑ t ∈ mixScale X, mixWeightV t *
        (((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
            (∑ F ∈ (offsetWindow S).powerset,
              coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F *
                frameBound t F) +
          C * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) +
          C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
            (fun U ↦ if corePositiveFrameBad I j G R U then 1 else 0))) /
        mixZ X := by
  apply corePositiveFiniteRootMean_le_of_root X S L test
    (fun t ↦
      (((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
          (∑ F ∈ (offsetWindow S).powerset,
            coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F *
              frameBound t F) +
        C * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) +
        C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
          (fun U ↦ if corePositiveFrameBad I j G R U then 1 else 0))) hZ
  intro t ht
  have hcut0 : ∀ U, 0 ≤ corePositiveCutTest I j G R test U := by
    intro U
    unfold corePositiveCutTest
    split_ifs
    · exact le_rfl
    · exact htest0 U
  have hcutC : ∀ U, corePositiveCutTest I j G R test U ≤ C := by
    intro U
    unfold corePositiveCutTest
    split_ifs
    · exact (htest0 ∅).trans (htestC ∅)
    · exact htestC U
  have hgood := corePositive_highMean_le_frame_add_high
    S (sieveCutoff (t : ℝ)) L j (corePositiveCutTest I j G R test)
      (frameBound t) (hSy t ht) hjL hcut0 hcutC (hframe0 t ht)
      (hθ t ht) (hθ4 t ht) (hslot t ht)
  have hcut := corePositive_highMean_le_cut_add_originalBad
    (sieveCutoff (t : ℝ)) S L I j G R test htest0 htestC
  calc
    CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L test ≤
        CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
            (corePositiveCutTest I j G R test) +
          C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
            (fun U ↦ if corePositiveFrameBad I j G R U then 1 else 0) := hcut
    _ ≤ (((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
            (∑ F ∈ (offsetWindow S).powerset,
              coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F *
                frameBound t F) +
          C * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) +
        C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
          (fun U ↦ if corePositiveFrameBad I j G R U then 1 else 0)) :=
      _root_.add_le_add hgood le_rfl

end

end PrimeGapNormality.Prime
