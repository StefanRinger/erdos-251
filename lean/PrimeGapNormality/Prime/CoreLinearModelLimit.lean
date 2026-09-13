import PrimeGapNormality.Prime.CoreLinearRootMean

/-!
# Uniform positive bound for the normalized linear root model

The finite good-layer estimate is averaged over the exact late fibres and the
literal normalized finite root mixture.  Scale calibration is supplied by
`CoreLinearMixtureScales`; the only discarded mass is the proved high-count
exception.  Finally the fixed mesh parameter is chosen from the requested
test error, while the volume-domination constant remains independent of the
test.
-/

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

noncomputable section

private theorem coreLinearLimit_lateRetention_nonneg (S y : ℕ) :
    0 ≤ lateRetention S y := by
  unfold lateRetention rootedEulerProdNat
  refine prod_nonneg fun p hp => ?_
  have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp'.two_le
  have hden : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hden)

private theorem coreLinearLimit_sum_cardinalityLayers_filter
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

/-- Collapse the good-layer sum on one fibre to its auxiliary physical gap
mean and total mass. -/
theorem eventually_coreLinearFibreMean_le_auxiliary
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
          12 * lateRetention S y * G / Real.log G *
            (((coreLinearFibreAuxGap S y L (J - 1) σ / G) + 1) *
              ((∫ x : AddCircle (1 : ℝ), f x) +
                δ * ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)))) +
              δ * C) +
            C * coreFiniteRootMixUpperFibreMass S y σ := by
  filter_upwards [eventually_coreLinearFibreMean_le_good_add_high
    B hB f hK hf0 hfC hδ hδ1] with G hraw
  intro S y L J σ hG hfloor hSy hJ hJL hquarter hslo hshi
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  let θ := lateRetention S y
  let idx := Icc L A.card
  let good := idx.filter (fun n : ℕ => (n : ℝ) ≤ 2 * (A.card : ℝ) * θ)
  let p : ℕ → ℝ := fun n => cardinalityLayer A μ n
  let gap : ℕ → ℝ := fun n =>
    auxFrame_uniformMean A (n - 1) (fun F => (subsetGap F (J - 1) : ℝ))
  let a : ℝ := 12 * θ * G / Real.log G
  let q : ℝ := (∫ x : AddCircle (1 : ℝ), f x) +
    δ * ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)))
  let r : ℝ := δ * C
  let term : ℕ → ℝ := fun n => p n * (a * (((gap n / G) + 1) * q + r))
  have hμ : CardinalitySymmetricMass A μ := by
    simpa [A, μ] using corePresieveLaw_cardinalitySymmetric S y σ hSy
  have hp0 : ∀ n, 0 ≤ p n := by
    intro n
    unfold p cardinalityLayer
    exact sum_nonneg fun U hU => hμ.1 U (mem_filter.mp hU).1
  have hgap0 : ∀ n, 0 ≤ gap n := fun n =>
    auxFrame_uniformMean_nonneg (fun F => Nat.cast_nonneg _)
  have hθ0 : 0 ≤ θ := by simpa [θ] using coreLinearLimit_lateRetention_nonneg S y
  have hG0 : 0 < G := zero_lt_one.trans hG
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθ0) hG0.le)
      (Real.log_pos hG).le
  have hC0 : 0 ≤ C := (hf0 0).trans (hfC 0)
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hD0 : 0 ≤ (B : ℝ) * ((B : ℝ) - 1) := by nlinarith
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    exact add_nonneg (integral_nonneg hf0)
      (mul_nonneg hδ.le (mul_nonneg K.coe_nonneg hD0))
  have hr0 : 0 ≤ r := by dsimp only [r]; exact mul_nonneg hδ.le hC0
  have hterm0 : ∀ n ∈ idx, 0 ≤ term n := by
    intro n _
    unfold term
    exact mul_nonneg (hp0 n) (mul_nonneg ha0
      (add_nonneg (mul_nonneg
        (add_nonneg (div_nonneg (hgap0 n) hG0.le) zero_le_one) hq0) hr0))
  have hgoodle : (∑ n ∈ good, term n) ≤ ∑ n ∈ idx, term n :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun n hn _ ↦ hterm0 n hn)
  have hmass : (∑ n ∈ idx, p n) ≤ 1 := by
    rw [coreLinearLimit_sum_cardinalityLayers_filter]
    calc
      (∑ U ∈ A.powerset.filter (fun U => U.card ∈ idx), μ U) ≤
          ∑ U ∈ A.powerset, μ U := by
        refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_
        intro U hU _
        exact hμ.1 U hU
      _ = 1 := hμ.2.1
  have haux : (∑ n ∈ idx, p n * gap n) =
      coreLinearFibreAuxGap S y L (J - 1) σ := by
    rfl
  have hsumform :
      (∑ n ∈ idx, term n) =
        a * (((coreLinearFibreAuxGap S y L (J - 1) σ / G +
          ∑ n ∈ idx, p n) * q) + (∑ n ∈ idx, p n) * r) := by
    have hpoint : ∀ n ∈ idx,
        term n = (a * q / G) * (p n * gap n) + (a * (q + r)) * p n := by
      intro n _
      dsimp only [term]
      field_simp [hG0.ne']
      ring
    rw [sum_congr rfl hpoint, sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, haux]
    ring
  have hinner :
      (((coreLinearFibreAuxGap S y L (J - 1) σ / G +
          ∑ n ∈ idx, p n) * q) + (∑ n ∈ idx, p n) * r) ≤
        ((coreLinearFibreAuxGap S y L (J - 1) σ / G + 1) * q + r) := by
    have hqr : 0 ≤ q + r := add_nonneg hq0 hr0
    have hm := mul_le_mul_of_nonneg_right hmass hqr
    nlinarith
  have hcollapsed : (∑ n ∈ good, term n) ≤
      a * ((coreLinearFibreAuxGap S y L (J - 1) σ / G + 1) * q + r) := by
    exact hgoodle.trans (hsumform ▸ mul_le_mul_of_nonneg_left hinner ha0)
  have hbase := hraw S y L J σ hG hfloor hSy hJ hJL hquarter hslo hshi
  exact hbase.trans (add_le_add (by simpa [A, μ, θ, idx, good, p, gap, a, q, r, term]
    using hcollapsed) le_rfl)

/-- Average the collapsed fibre estimate over the actual uniform exposed
presieve root. -/
theorem eventually_coreLinearActualRootMean_le_auxiliary
    (B : ℕ) (hB : 2 ≤ B)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    {C δ : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ G : ℝ in atTop,
      ∀ (S y L J : ℕ),
        1 < G → ⌊G⌋₊ ≤ S → S ≤ y → 1 ≤ J → J < L →
        lateRetention S y ≤ (1 / 4 : ℝ) →
        1 ≤ G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) →
        G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) ≤
          (B : ℝ) * ((B : ℝ) - 1) →
        coreLinearActualRootMean B y S L f ≤
          12 * lateRetention S y * G / Real.log G *
            (((coreAuxiliaryLayerPhysicalGapMean S y L (J - 1) / G) + 1) *
              ((∫ x : AddCircle (1 : ℝ), f x) +
                δ * ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)))) +
              δ * C) +
            C * coreFiniteRootMixUpperRootMass S y := by
  filter_upwards [eventually_coreLinearFibreMean_le_auxiliary
    B hB f hK hf0 hfC hδ hδ1] with G hfibre
  intro S y L J hG hfloor hSy hJ hJL hquarter hslo hshi
  let a : ℝ := 12 * lateRetention S y * G / Real.log G
  let q : ℝ := (∫ x : AddCircle (1 : ℝ), f x) +
    δ * ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)))
  let r : ℝ := δ * C
  let gap (σ : ResidueChoice S) := coreLinearFibreAuxGap S y L (J - 1) σ
  let upper (σ : ResidueChoice S) := coreFiniteRootMixUpperFibreMass S y σ
  have hden : 0 < (Fintype.card (ResidueChoice S) : ℝ) :=
    Nat.cast_pos.mpr (residueChoice_card_pos S)
  have hpoint : ∀ σ : ResidueChoice S,
      coreLinearFibreMean B S y L f σ ≤
        a * (((gap σ / G) + 1) * q + r) + C * upper σ := by
    intro σ
    simpa [a, q, r, gap, upper] using
      hfibre S y L J σ hG hfloor hSy hJ hJL hquarter hslo hshi
  have hsum := sum_le_sum fun σ (_ : σ ∈ (univ : Finset (ResidueChoice S))) => hpoint σ
  rw [coreLinearActualRootMean_eq_avg_fibres B S y L f hSy]
  have hdiv := div_le_div_of_nonneg_right hsum hden.le
  refine hdiv.trans_eq ?_
  have hgap :
      (∑ σ : ResidueChoice S, gap σ) /
          (Fintype.card (ResidueChoice S) : ℝ) =
        coreAuxiliaryLayerPhysicalGapMean S y L (J - 1) := by
    rfl
  have hupper :
      (∑ σ : ResidueChoice S, upper σ) /
          (Fintype.card (ResidueChoice S) : ℝ) =
        coreFiniteRootMixUpperRootMass S y := by
    rfl
  rw [sum_add_distrib, add_div]
  have hfirst :
      (∑ σ : ResidueChoice S, a * (((gap σ / G) + 1) * q + r)) /
          (Fintype.card (ResidueChoice S) : ℝ) =
        a * (((coreAuxiliaryLayerPhysicalGapMean S y L (J - 1) / G) + 1) * q + r) := by
    have hpoint' : ∀ σ : ResidueChoice S,
        a * (((gap σ / G) + 1) * q + r) =
          (a * q / G) * gap σ + a * (q + r) := by
      intro σ
      field_simp [(zero_lt_one.trans hG).ne']
      ring
    rw [sum_congr rfl (fun σ _ => hpoint' σ), sum_add_distrib,
      ← Finset.mul_sum, sum_const, card_univ, nsmul_eq_mul]
    rw [show (∑ σ : ResidueChoice S, gap σ) =
        coreAuxiliaryLayerPhysicalGapMean S y L (J - 1) *
          (Fintype.card (ResidueChoice S) : ℝ) by
      apply (div_eq_iff hden.ne').mp
      simpa [mul_comm] using hgap]
    field_simp [hden.ne', (zero_lt_one.trans hG).ne']
    ring
  rw [hfirst]
  have hsecond :
      (∑ σ : ResidueChoice S, C * upper σ) /
          (Fintype.card (ResidueChoice S) : ℝ) =
        C * coreFiniteRootMixUpperRootMass S y := by
    rw [← Finset.mul_sum]
    calc
      C * (∑ σ : ResidueChoice S, upper σ) /
          (Fintype.card (ResidueChoice S) : ℝ) =
        C * ((∑ σ : ResidueChoice S, upper σ) /
          (Fintype.card (ResidueChoice S) : ℝ)) := by ring
      _ = C * coreFiniteRootMixUpperRootMass S y := by rw [hupper]
  rw [hsecond]

/-! ### Normalized finite-mixture bound -/

private theorem coreLinearLimit_mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos'
  · intro t _
    exact mixWeightV_nonneg t
  · refine ⟨2 * X, ?_, ?_⟩
    · simp only [mixScale, mem_Ioc]
      omega
    · exact eulerProdNat_pos (sieveCutoff ((2 * X : ℕ) : ℝ))

/-- Explicit finite normalized model estimate.  Its volume coefficient is
test-independent; the mesh error and genuine high-count exception are kept
visible for the final epsilon choice. -/
theorem eventually_coreLinearFiniteRootMean_le_explicit
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    {C δ : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ X : ℕ in atTop,
      coreLinearFiniteRootMean B X (ahlSmall_window κ X) (profileL κ X) f ≤
        (324 / eulerProdLowerConst : ℝ) *
            (∫ x : AddCircle (1 : ℝ), f x) +
          δ * ((324 / eulerProdLowerConst : ℝ) *
              ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1))) +
            (36 / eulerProdLowerConst : ℝ) * C) +
          C * coreFiniteRootMixUpperException κ X := by
  have hlogB : 0 < Real.log (B : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (by omega))
  have hκpos : 0 < κ :=
    (div_pos zero_lt_one hlogB).trans_le hκ
  have hraw := eventually_coreLinearActualRootMean_le_auxiliary
    B hB f hK hf0 hfC hδ hδ1
  have hactual := tendsto_windowG_atTop.eventually hraw
  filter_upwards [hactual, eventually_coreLinearMixtureScales hκpos,
    coreFRMUpper_eventually_lateRetention_le_quarter hκpos,
    CoreLinearInsertion.eventually_critical_rank_profileL hB hκ,
    eventually_ge_atTop 1] with X hactualX hscale hquarter hcritical hX
  let G := windowG X
  let S := ahlSmall_window κ X
  let L := profileL κ X
  obtain ⟨J, hJ, hJL, hratioLo, hratioHi⟩ := hcritical
  have hslope := CoreLinearInsertion.scaled_slope_bounds hB hratioLo hratioHi
  have hslo : 1 ≤ G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) := by
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    have hB1 : (1 : ℝ) ≤ (B : ℝ) - 1 := by linarith
    exact hB1.trans hslope.1
  have hshi : G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) ≤
      (B : ℝ) * ((B : ℝ) - 1) := hslope.2.le
  have hZ : 0 < mixZ X := coreLinearLimit_mixZ_pos hX
  let m : ℝ := ∫ x : AddCircle (1 : ℝ), f x
  let D : ℝ := (K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1))
  let T : ℝ := (3 : ℝ) / eulerProdLowerConst
  let Aconst : ℝ := (324 : ℝ) / eulerProdLowerConst
  have hT : 0 ≤ T := coreLinearScales_retentionConst_pos.le
  have hm : 0 ≤ m := by dsimp only [m]; exact integral_nonneg hf0
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg K.coe_nonneg (mul_nonneg (by linarith) (by linarith))
  have hC : 0 ≤ C := (hf0 0).trans (hfC 0)
  have hcommon0 : 0 ≤ (m + δ * D) := add_nonneg hm (mul_nonneg hδ.le hD)
  have hroot : ∀ t ∈ mixScale X,
      coreLinearActualRootMean B (sieveCutoff (t : ℝ)) S L f ≤
        Aconst * m + δ * (Aconst * D + (36 / eulerProdLowerConst : ℝ) * C) +
          C * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ)) := by
    intro t ht
    have hs := hscale.2.2.2.2 t ht
    have hbase := hactualX S (sieveCutoff (t : ℝ)) L J
      hscale.1 hscale.2.2.2.1 hs.1 hJ hJL (hquarter t ht) hslo hshi
    have hgapBound := coreAuxiliaryLayerPhysicalGapMean_le S
      (sieveCutoff (t : ℝ)) L (J - 1) hs.1 (by omega)
    have hgapDiv : coreAuxiliaryLayerPhysicalGapMean S
        (sieveCutoff (t : ℝ)) L (J - 1) / G ≤ 8 := by
      have hdiv := div_le_div_of_nonneg_right hgapBound
        (zero_lt_one.trans hscale.1).le
      calc
        _ ≤ ((2 : ℝ) * (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹) / G := hdiv
        _ = 2 * ((eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / G) := by ring
        _ ≤ 2 * 4 := mul_le_mul_of_nonneg_left hs.2.2.2.2 (by norm_num)
        _ = 8 := by norm_num
    have hgapPlus : coreAuxiliaryLayerPhysicalGapMean S
        (sieveCutoff (t : ℝ)) L (J - 1) / G + 1 ≤ 9 := by linarith
    have hbracket :
        ((coreAuxiliaryLayerPhysicalGapMean S (sieveCutoff (t : ℝ)) L (J - 1) / G + 1) *
            (m + δ * D) + δ * C) ≤ 9 * (m + δ * D) + δ * C :=
      add_le_add (mul_le_mul_of_nonneg_right hgapPlus hcommon0) le_rfl
    have hcoef := hs.2.2.2.1
    have hcoef0 : 0 ≤ 12 * lateRetention S (sieveCutoff (t : ℝ)) * G /
        Real.log G := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hs.2.2.1)
          (zero_lt_one.trans hscale.1).le)
        hscale.2.1.le
    have hcoefBound : 12 * lateRetention S (sieveCutoff (t : ℝ)) * G /
        Real.log G ≤ 12 * T := by
      have hmul := mul_le_mul_of_nonneg_left hs.2.2.2.1
        (by norm_num : (0 : ℝ) ≤ 12)
      dsimp only [T]
      calc
        12 * lateRetention S (sieveCutoff (t : ℝ)) * G / Real.log G =
            12 * (lateRetention S (sieveCutoff (t : ℝ)) * G / Real.log G) := by ring
        _ ≤ 12 * ((3 : ℝ) / eulerProdLowerConst) := hmul
    have hbracket0 : 0 ≤ 9 * (m + δ * D) + δ * C :=
      add_nonneg (mul_nonneg (by norm_num) hcommon0) (mul_nonneg hδ.le hC)
    have hmain := (mul_le_mul_of_nonneg_left hbracket hcoef0).trans
      (mul_le_mul_of_nonneg_right hcoefBound hbracket0)
    exact hbase.trans (add_le_add (hmain.trans_eq (by
      dsimp only [T, Aconst, m, D]
      field_simp [eulerProdLowerConst_pos.ne']
      ring)) le_rfl)
  rw [coreLinearFiniteRootMean_eq_weighted]
  have hsum :
      ∑ t ∈ mixScale X, mixWeightV t *
          coreLinearActualRootMean B (sieveCutoff (t : ℝ)) S L f ≤
        ∑ t ∈ mixScale X, mixWeightV t *
          (Aconst * m + δ * (Aconst * D + (36 / eulerProdLowerConst : ℝ) * C) +
            C * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) :=
    sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hroot t ht) (mixWeightV_nonneg t)
  have hdiv := div_le_div_of_nonneg_right hsum hZ.le
  refine hdiv.trans_eq ?_
  unfold coreFiniteRootMixUpperException
  dsimp only [S, L, G, Aconst, m, D]
  let z : ℝ :=
    (324 / eulerProdLowerConst : ℝ) *
        (∫ x : AddCircle (1 : ℝ), f x) +
      δ * ((324 / eulerProdLowerConst : ℝ) *
          ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1))) +
        (36 / eulerProdLowerConst : ℝ) * C)
  change
    (∑ t ∈ mixScale X, mixWeightV t *
      (z + C * coreFiniteRootMixUpperRootMass
        (ahlSmall_window κ X) (sieveCutoff (t : ℝ)))) / mixZ X =
      z + C * ((∑ t ∈ mixScale X, mixWeightV t *
        coreFiniteRootMixUpperRootMass
          (ahlSmall_window κ X) (sieveCutoff (t : ℝ))) / mixZ X)
  have hconst (z : ℝ) : (∑ t ∈ mixScale X, mixWeightV t * z) = mixZ X * z := by
    rw [← Finset.sum_mul]
    rfl
  have hnum :
      (∑ t ∈ mixScale X, mixWeightV t *
        (z + C * coreFiniteRootMixUpperRootMass
          (ahlSmall_window κ X) (sieveCutoff (t : ℝ)))) =
        mixZ X * z + C * (∑ t ∈ mixScale X, mixWeightV t *
          coreFiniteRootMixUpperRootMass
            (ahlSmall_window κ X) (sieveCutoff (t : ℝ))) := by
    calc
      _ = (∑ t ∈ mixScale X, mixWeightV t * z) +
          ∑ t ∈ mixScale X, mixWeightV t *
            (C * coreFiniteRootMixUpperRootMass
              (ahlSmall_window κ X) (sieveCutoff (t : ℝ))) := by
        simp_rw [mul_add]
        rw [sum_add_distrib]
      _ = mixZ X * z + C * (∑ t ∈ mixScale X, mixWeightV t *
          coreFiniteRootMixUpperRootMass
            (ahlSmall_window κ X) (sieveCutoff (t : ℝ))) := by
        rw [hconst]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
  rw [hnum]
  field_simp [hZ.ne']

/-! ### Test-independent domination constant and epsilon choice -/

/-- The normalized stopped linear model obeys a positive Lipschitz bound with
a constant independent of the test. -/
theorem coreLinearFiniteRootMean_eventually_le_volume
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0),
        LipschitzWith K f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ X : ℕ in atTop,
            coreLinearFiniteRootMean B X (ahlSmall_window κ X) (profileL κ X) f ≤
              A * (∫ x : AddCircle (1 : ℝ), f x) + ε := by
  refine ⟨(324 : ℝ) / eulerProdLowerConst,
    div_nonneg (by norm_num) eulerProdLowerConst_pos.le, ?_⟩
  intro f K hK hf0 ε hε
  let C : ℝ := ‖f‖
  let D : ℝ := (324 / eulerProdLowerConst : ℝ) *
      ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1))) +
    (36 / eulerProdLowerConst : ℝ) * C
  let δ : ℝ := min 1 (ε / (2 * (D + 1)))
  have hC : 0 ≤ C := norm_nonneg _
  have hfC : ∀ x, f x ≤ C := fun x =>
    (le_abs_self (f x)).trans (by
      simpa only [Real.norm_eq_abs, C] using f.norm_coe_le_norm x)
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hD : 0 ≤ D := by
    dsimp only [D, C]
    have hc : 0 ≤ eulerProdLowerConst := eulerProdLowerConst_pos.le
    have hB0 : (0 : ℝ) ≤ B := by linarith
    have hB1 : (0 : ℝ) ≤ (B : ℝ) - 1 := by linarith
    exact add_nonneg
      (mul_nonneg (div_nonneg (by norm_num) hc)
        (mul_nonneg K.coe_nonneg (mul_nonneg hB0 hB1)))
      (mul_nonneg (div_nonneg (by norm_num) hc) (norm_nonneg _))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min zero_lt_one (div_pos hε (mul_pos (by norm_num) (by linarith)))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδD : δ * D ≤ ε / 2 := by
    have hle : δ ≤ ε / (2 * (D + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (mul_pos (by norm_num) (by linarith : 0 < D + 1))).mp hle
    nlinarith [mul_nonneg hδ.le hD]
  have hexplicit := eventually_coreLinearFiniteRootMean_le_explicit
    B hB hκ f hK hf0 hfC hδ hδ1
  have hupper := (tendsto_coreFiniteRootMixUpperException
    ((div_pos zero_lt_one (Real.log_pos (Nat.one_lt_cast.mpr (by omega)))).trans_le hκ)).const_mul C
  have hupper0 : Tendsto
      (fun X : ℕ => C * coreFiniteRootMixUpperException κ X)
      atTop (nhds 0) := by
    simpa only [mul_zero] using hupper
  have hupperSmall : ∀ᶠ X : ℕ in atTop,
      C * coreFiniteRootMixUpperException κ X ≤ ε / 2 := by
    have ht := hupper0.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by linarith : 0 < ε / 2))
    filter_upwards [ht] with X hball
    have habs : |C * coreFiniteRootMixUpperException κ X| < ε / 2 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, mul_zero] using hball
    exact (le_abs_self _).trans habs.le
  filter_upwards [hexplicit, hupperSmall] with X hmain hhigh
  dsimp only [D] at hδD
  exact hmain.trans (by linarith)

end

end PrimeGapNormality.Prime
