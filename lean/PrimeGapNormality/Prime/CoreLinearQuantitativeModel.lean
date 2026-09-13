import PrimeGapNormality.Prime.CoreSelbergDiagonalInsertion
import PrimeGapNormality.Prime.CorePositiveRootFrameAssembly
import PrimeGapNormality.Prime.CoreLinearModelLimit
import PrimeGapNormality.Prime.CorePresieveCountRate

/-!
# Quantitative positive linear bound for the canonical finite root model

The shrinking-mesh Selberg estimate is assembled through the literal
one-cutoff auxiliary frame mass and the normalized `mixWeightV / mixZ`
mixture.  Its scale threshold is chosen before the bounded continuous test
and its Lipschitz constant.  Thus this file does not specialize an eventual
fixed-mesh theorem to a mesh depending on the test.

The only count loss is the genuine original-law high-count exception.  Its
`O(1 / profileL)` estimate is obtained from the finite presieve variance;
no quantitative calibration rate is assumed.
-/

namespace PrimeGapNormality.Prime.CoreLinearQuantitativeModel

open Filter Finset MeasureTheory
open CorePresieveCountRate
open scoped Topology NNReal Classical BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1000000

private theorem mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos'
  · intro t _
    exact mixWeightV_nonneg t
  · refine ⟨2 * X, ?_, ?_⟩
    · simp only [mixScale, mem_Ioc]
      omega
    · exact eulerProdNat_pos (sieveCutoff ((2 * X : ℕ) : ℝ))

private theorem linearMean_eq_positiveMean
    (B X S L : ℕ) (f : AddCircle (1 : ℝ) → ℝ) :
    coreLinearFiniteRootMean B X S L f =
      corePositiveFiniteRootMean X S L
        (fun U ↦ f (coreLinearShapePhase B L U : AddCircle (1 : ℝ))) := by
  rw [coreLinearFiniteRootMean_eq_weighted,
    corePositiveFiniteRootMean_eq_weighted]
  apply congrArg (fun z : ℝ ↦ z / mixZ X)
  exact sum_congr rfl fun t _ ↦ by rfl

/-! ## The diagonal insertion estimate on an actual presieve slot -/

/-- The shrinking-mesh insertion estimate in the exact slot and phase used
by the linear model.  The eventual threshold is independent of `f` and `K`.
-/
theorem eventually_coreLinear_diagonal_slot_sum_le
    (B : ℕ) (hB : 2 ≤ B) :
    ∀ᶠ G : ℝ in atTop,
      ∀ (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0),
        LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ (S L J n : ℕ) (σ : ResidueChoice S) (F : Finset ℕ),
        1 < G → ⌊G⌋₊ ≤ S → 1 ≤ J → J < L → L ≤ n →
        F ∈ (presieveSurvivors S σ).powersetCard (n - 1) →
        1 ≤ G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) →
        G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) ≤
          (B : ℝ) * ((B : ℝ) - 1) →
        (∑ u ∈ openSlot (presieveSurvivors S σ)
            (F.sort (· ≤ ·)) (J - 1),
          f (coreLinearShapePhase B L (insert u F) : AddCircle (1 : ℝ))) ≤
          (6 * G / Real.log G) *
            ((((subsetGap F (J - 1) : ℝ) / G) + 1) *
                (∫ x : AddCircle (1 : ℝ), f x) +
              G ^ (-(1 / 2 : ℝ)) *
                ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)) *
                    ((subsetGap F (J - 1) : ℝ) / G) + ‖f‖)) := by
  filter_upwards
      [CoreSelbergDiagonalInsertion.eventually_circle_linear_insertion]
      with G hdiag
  intro f K hK hf0 S L J n σ F hG1 hfloor hJ hJL hLn hF hslo hshi
  let A := presieveSurvivors S σ
  let E := openSlot A (F.sort (· ≤ ·)) (J - 1)
  let a := (CoreLinearInsertion.insertionSlot F J).1
  let W := (subsetGap F (J - 1) : ℝ) / G
  let s := G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1)
  let O := CoreLinearInsertion.outerPhase B L J F
  let D := (B : ℝ) * ((B : ℝ) - 1)
  have hG : 0 < G := zero_lt_one.trans hG1
  have hFm := mem_powersetCard.mp hF
  have hn : 1 ≤ n := by omega
  have hFcard : F.card + 1 = n := by
    rw [hFm.2, Nat.sub_add_cancel hn]
  have hFL : L ≤ F.card + 1 := hFcard ▸ hLn
  have hJcard : J - 1 < F.card := by omega
  have horder : orderStat F (J - 1) ≤ orderStat F J := by
    simpa only [Nat.sub_add_cancel hJ] using
      CoreLinearInsertion.orderStat_le_succ F hJcard
  have hgap : (subsetGap F (J - 1) : ℝ) =
      ((CoreLinearInsertion.insertionSlot F J).2 : ℝ) -
        (CoreLinearInsertion.insertionSlot F J).1 := by
    unfold subsetGap
    rw [Nat.sub_add_cancel hJ, Nat.cast_sub horder,
      CoreLinearInsertion.insertionSlot_left,
      CoreLinearInsertion.insertionSlot_right F hJ]
  have hW : 0 ≤ W := div_nonneg (Nat.cast_nonneg _) hG.le
  have hEin : ∀ u ∈ E, a < u ∧ (u : ℝ) - a < W * G := by
    intro u hu
    have hus := (mem_openSlot.mp hu).2
    have huSlot :
        (CoreLinearInsertion.insertionSlot F J).1 < u ∧
          u < (CoreLinearInsertion.insertionSlot F J).2 := by
      simpa only [CoreLinearInsertion.insertionSlot] using hus
    refine ⟨by simpa only [a] using huSlot.1, ?_⟩
    have hwidth : W * G =
        ((CoreLinearInsertion.insertionSlot F J).2 : ℝ) -
          (CoreLinearInsertion.insertionSlot F J).1 := by
      dsimp only [W]
      rw [hgap, div_mul_cancel₀ _ hG.ne']
    rw [hwidth]
    have hur : (u : ℝ) < (CoreLinearInsertion.insertionSlot F J).2 := by
      exact_mod_cast huSlot.2
    linarith
  have hEA : E ⊆ A := fun u hu ↦ (mem_openSlot.mp hu).1
  have havoid : CoreSelberg.AvoidsResidues E ⌊G⌋₊ :=
    coreLinear_presieveSubset_avoids σ hEA hfloor
  have hs0 : 0 ≤ s := zero_le_one.trans hslo
  have hsabs : 1 ≤ |s| := by
    rw [abs_of_nonneg hs0]
    exact hslo
  have hsD : |s| ≤ D := by
    rw [abs_of_nonneg hs0]
    exact hshi
  have hphase : ∀ u ∈ E,
      coreLinearShapePhase B L (insert u F) =
        O + s * (((u : ℝ) - a) / G) := by
    intro u hu
    have hus := (mem_openSlot.mp hu).2
    have huSlot :
        (CoreLinearInsertion.insertionSlot F J).1 < u ∧
          u < (CoreLinearInsertion.insertionSlot F J).2 := by
      simpa only [CoreLinearInsertion.insertionSlot] using hus
    simpa only [O, s, a] using
      CoreLinearInsertion.shapePhase_insert_scaled
        hB hJ hJL F hFL hG huSlot
  have hsumphase :
      (∑ u ∈ E,
          f (coreLinearShapePhase B L (insert u F) : AddCircle (1 : ℝ))) =
        ∑ u ∈ E,
          f ((O + s * (((u : ℝ) - a) / G) : ℝ) : AddCircle (1 : ℝ)) := by
    exact sum_congr rfl fun u hu ↦ by rw [hphase u hu]
  have hbase := hdiag a E W O s f K hW hsabs hEin havoid hK hf0
  have he : 0 ≤ G ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hG.le _
  have hinner :
      (K : ℝ) * |s| * W + ‖f‖ ≤ (K : ℝ) * D * W + ‖f‖ := by
    exact _root_.add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsD K.coe_nonneg) hW) le_rfl
  have hcoef : 0 ≤ 6 * G / Real.log G :=
    div_nonneg (mul_nonneg (by norm_num) hG.le) (Real.log_pos hG1).le
  rw [hsumphase]
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hinner he)) hcoef)

/-! ## One-cutoff assembly -/

/-- Quantitative one-cutoff estimate under the literal original root law.
The test and its Lipschitz constant occur only after the finite-scale
hypotheses. -/
theorem coreLinearActualRootMean_le_quantitative
    (B : ℕ) (hB : 2 ≤ B) {G : ℝ} {S y L J : ℕ}
    (hdiag : ∀ (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0),
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ (n : ℕ) (σ : ResidueChoice S) (F : Finset ℕ),
        1 < G → ⌊G⌋₊ ≤ S → 1 ≤ J → J < L → L ≤ n →
        F ∈ (presieveSurvivors S σ).powersetCard (n - 1) →
        1 ≤ G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) →
        G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) ≤
          (B : ℝ) * ((B : ℝ) - 1) →
        (∑ u ∈ openSlot (presieveSurvivors S σ)
            (F.sort (· ≤ ·)) (J - 1),
          f (coreLinearShapePhase B L (insert u F) : AddCircle (1 : ℝ))) ≤
          (6 * G / Real.log G) *
            ((((subsetGap F (J - 1) : ℝ) / G) + 1) *
                (∫ x : AddCircle (1 : ℝ), f x) +
              G ^ (-(1 / 2 : ℝ)) *
                ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)) *
                    ((subsetGap F (J - 1) : ℝ) / G) + ‖f‖)))
    (hG : 1 < G) (hfloor : ⌊G⌋₊ ≤ S) (hSy : S ≤ y)
    (hS2 : 2 ≤ S) (hJ : 1 ≤ J) (hJL : J < L)
    (hquarter : lateRetention S y ≤ (1 / 4 : ℝ))
    (hslo : 1 ≤ G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1))
    (hshi : G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) ≤
      (B : ℝ) * ((B : ℝ) - 1))
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0)
    (hK : LipschitzWith K f) (hf0 : ∀ x, 0 ≤ f x) :
    coreLinearActualRootMean B y S L f ≤
      24 * lateRetention S y * G / Real.log G *
        (((coreAuxiliaryLayerPhysicalGapMean S y L (J - 1) / G) + 1) *
            (∫ x : AddCircle (1 : ℝ), f x) +
          G ^ (-(1 / 2 : ℝ)) *
            ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)) *
                (coreAuxiliaryLayerPhysicalGapMean S y L (J - 1) / G) + ‖f‖)) +
        ‖f‖ * coreFiniteRootMixUpperRootMass S y := by
  let test : Finset ℕ → ℝ := fun U ↦
    f (coreLinearShapePhase B L U : AddCircle (1 : ℝ))
  let gap : Finset ℕ → ℝ := fun F ↦ (subsetGap F (J - 1) : ℝ)
  let m : ℝ := ∫ x : AddCircle (1 : ℝ), f x
  let C : ℝ := ‖f‖
  let D : ℝ := (K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1))
  let e : ℝ := G ^ (-(1 / 2 : ℝ))
  let d : ℝ := 6 * G / Real.log G
  let frameBound : Finset ℕ → ℝ := fun F ↦
    d * (((gap F / G) + 1) * m + e * (D * (gap F / G) + C))
  have hG0 : 0 < G := zero_lt_one.trans hG
  have hm0 : 0 ≤ m := by
    dsimp only [m]
    exact integral_nonneg hf0
  have hC0 : 0 ≤ C := by dsimp only [C]; exact norm_nonneg _
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    exact mul_nonneg K.coe_nonneg (mul_nonneg (by linarith) (by linarith))
  have he0 : 0 ≤ e := by dsimp only [e]; exact Real.rpow_nonneg hG0.le _
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    exact div_nonneg (mul_nonneg (by norm_num) hG0.le) (Real.log_pos hG).le
  have hframe0 : ∀ F, 0 ≤ frameBound F := by
    intro F
    unfold frameBound
    exact mul_nonneg hd0 (_root_.add_nonneg
      (mul_nonneg (_root_.add_nonneg
        (div_nonneg (Nat.cast_nonneg _) hG0.le) zero_le_one) hm0)
      (mul_nonneg he0 (_root_.add_nonneg
        (mul_nonneg hD0 (div_nonneg (Nat.cast_nonneg _) hG0.le)) hC0)))
  have hslot : ∀ σ : ResidueChoice S,
      ∀ n ∈ (Icc L (presieveSurvivors S σ).card).filter
        (fun n : ℕ ↦ (n : ℝ) ≤
          2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y),
      ∀ F ∈ (presieveSurvivors S σ).powersetCard (n - 1),
        auxFrame_slotInsertSum (presieveSurvivors S σ) (J - 1) test F ≤
          frameBound F := by
    intro σ n hn F hF
    have hnI := mem_Icc.mp (mem_filter.mp hn).1
    unfold auxFrame_slotInsertSum
    simpa only [test, frameBound, gap, m, C, D, e, d] using
      hdiag f K hK hf0 n σ F hG hfloor hJ hJL hnI.1 hF hslo hshi
  have hθ : 0 < lateRetention S y := rootedEulerProdNat_pos hS2
  have hbase := corePositive_highMean_le_frame_add_high
    S y L (J - 1) test frameBound hSy
    (by simpa only [Nat.sub_add_cancel hJ] using hJL)
    (fun U ↦ hf0 _) (fun U ↦ f.apply_le_norm _) hframe0 hθ hquarter hslot
  have hmass0 : ∀ F ∈ (offsetWindow S).powerset,
      0 ≤ coreAuxiliaryLayerFrameMass S y L F := fun F _ ↦
    coreAuxiliaryLayerFrameMass_nonneg S y L hSy F
  let mass : ℝ := ∑ F ∈ (offsetWindow S).powerset,
    coreAuxiliaryLayerFrameMass S y L F
  let gapMean : ℝ := coreAuxiliaryLayerPhysicalGapMean S y L (J - 1)
  have hmassLe : mass ≤ 1 := by
    simpa only [mass] using coreAuxiliaryLayerFrameMass_sum_le_one S y L hSy
  have hmass0' : 0 ≤ mass := by
    dsimp only [mass]
    exact sum_nonneg fun F hF ↦ hmass0 F hF
  have hgap0 : 0 ≤ gapMean := by
    dsimp only [gapMean]
    rw [← coreAuxiliaryLayerFrameMass_subsetGap_expectation]
    exact sum_nonneg fun F hF ↦ mul_nonneg (hmass0 F hF) (Nat.cast_nonneg _)
  have hsumform :
      (∑ F ∈ (offsetWindow S).powerset,
          coreAuxiliaryLayerFrameMass S y L F * frameBound F) =
        (d * m / G + d * e * D / G) * gapMean + d * (m + e * C) * mass := by
    have hpoint : ∀ F ∈ (offsetWindow S).powerset,
        coreAuxiliaryLayerFrameMass S y L F * frameBound F =
          (d * m / G + d * e * D / G) *
              (coreAuxiliaryLayerFrameMass S y L F * gap F) +
            d * (m + e * C) * coreAuxiliaryLayerFrameMass S y L F := by
      intro F _
      dsimp only [frameBound]
      field_simp [hG0.ne'] <;> ring
    rw [sum_congr rfl hpoint, sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    rw [show (∑ F ∈ (offsetWindow S).powerset,
        coreAuxiliaryLayerFrameMass S y L F * gap F) = gapMean by
      simpa only [gap, gapMean] using
        coreAuxiliaryLayerFrameMass_subsetGap_expectation S y L (J - 1)]
  have hmassCoef0 : 0 ≤ d * (m + e * C) :=
    mul_nonneg hd0 (_root_.add_nonneg hm0 (mul_nonneg he0 hC0))
  have hframeLe :
      (∑ F ∈ (offsetWindow S).powerset,
          coreAuxiliaryLayerFrameMass S y L F * frameBound F) ≤
        d * (((gapMean / G) + 1) * m + e * (D * (gapMean / G) + C)) := by
    rw [hsumform]
    have hmassBound := mul_le_mul_of_nonneg_left hmassLe hmassCoef0
    calc
      (d * m / G + d * e * D / G) * gapMean + d * (m + e * C) * mass ≤
          (d * m / G + d * e * D / G) * gapMean + d * (m + e * C) * 1 :=
        _root_.add_le_add le_rfl hmassBound
      _ = d * (((gapMean / G) + 1) * m +
          e * (D * (gapMean / G) + C)) := by ring
  have hfourθ0 : 0 ≤ (4 : ℝ) * lateRetention S y :=
    mul_nonneg (by norm_num) hθ.le
  have hmain := mul_le_mul_of_nonneg_left hframeLe hfourθ0
  change coreLinearActualRootMean B y S L f ≤ _
  change CoreOriginalDeletedFrame.highMean y S L test ≤ _
  exact hbase.trans (_root_.add_le_add (hmain.trans_eq (by
    dsimp only [d, gapMean, m, C, D, e]
    ring)) le_rfl)

/-! ## Quantitative count exception -/

def linearCountRateConstant : ℝ :=
  1 + presieveLowerRateConstant (1 / 100)

theorem linearCountRateConstant_pos : 0 < linearCountRateConstant := by
  unfold linearCountRateConstant
  have h := presieveLowerRateConstant_pos
    (by norm_num : (0 : ℝ) < 1 / 100)
  linarith

private theorem eventually_profileL_le_log_small_sq {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      (profileL κ X : ℝ) ≤ Real.log (ahlSmall_window κ X : ℝ) ^ 2 := by
  filter_upwards [eventually_one_le_profileL hκ,
    eventually_coreLinearScales_sixteen_le_small hκ,
    eventually_windowG_le_ahlSmall_window hκ,
    tendsto_windowG_atTop.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp tendsto_windowG_atTop).eventually_ge_atTop
      (2 * κ + 2)] with X hL hS hGS hG hlogLarge
  let G := windowG X
  let S := ahlSmall_window κ X
  have hG2 : (2 : ℝ) ≤ G := hG
  have hGpos : 0 < G := zero_lt_two.trans_le hG2
  have hlogG0 : 0 ≤ Real.log G := Real.log_nonneg (by linarith)
  have hLbound : (profileL κ X : ℝ) ≤ 2 * κ * Real.log G + 2 := by
    have hlog : 0 ≤ κ * Real.log G := mul_nonneg hκ.le hlogG0
    have hs0 := Real.sqrt_nonneg (κ * Real.log G)
    have hs2 := Real.sq_sqrt hlog
    have hs : Real.sqrt (κ * Real.log G) ≤ κ * Real.log G + 1 := by
      nlinarith [sq_nonneg (Real.sqrt (κ * Real.log G) - 1)]
    have hp : (profileL κ X : ℝ) ≤
        κ * Real.log (windowG X) +
          Real.sqrt (κ * Real.log (windowG X)) + 1 := by
      set a := κ * Real.log (windowG X) +
        Real.sqrt (κ * Real.log (windowG X))
      have ha : 0 ≤ a := _root_.add_nonneg
        (mul_nonneg hκ.le
          (Real.log_nonneg (crtWindowG_one_le X))) (Real.sqrt_nonneg _)
      exact (Nat.ceil_lt_add_one (R := ℝ) ha).le
    dsimp only [G] at hs
    linarith
  have hlogGS : Real.log G ≤ Real.log (S : ℝ) :=
    Real.log_le_log hGpos (by simpa only [G, S] using hGS)
  have hlogSquare : 2 * κ * Real.log G + 2 ≤ Real.log G ^ 2 := by
    have hlogGlarge : 2 * κ + 2 ≤ Real.log G := by
      simpa only [G, Function.comp_apply] using hlogLarge
    nlinarith
  exact hLbound.trans (hlogSquare.trans
    (pow_le_pow_left₀ hlogG0 hlogGS 2))

/-- The normalized mixture of the genuine low-mean fibres inherits the
finite-variance `1 / log(S)^2` rate. -/
theorem eventually_finiteRootMixSmallLowerException_le_log_sq
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      finiteRootMixSmallLowerException κ X ≤
        presieveLowerRateConstant (1 / 100) /
          Real.log (ahlSmall_window κ X : ℝ) ^ 2 := by
  have hrate := eventually_presieve_lower_mass_le_log_sq_of_tendsto
    (tendsto_ahlSmall_window_atTop hκ)
    (by norm_num : (0 : ℝ) < 1 / 100)
    (by norm_num : (1 / 100 : ℝ) ≤ 1)
  filter_upwards [eventually_finiteRootMixSmallLowerFibreMass_le_global hκ,
    hrate, eventually_ge_atTop 1] with X hfibre hrateX hX
  have hZ : 0 < mixZ X := mixZ_pos hX
  let q : ℝ := presieveSmallGlobalLowerMass (ahlSmall_window κ X)
    ((1 - (1 / 100 : ℝ)) * ((ahlSmall_window κ X : ℝ) *
      eulerProdNat (ahlSmall_window κ X)))
  have havg : finiteRootMixSmallLowerException κ X ≤ q := by
    unfold finiteRootMixSmallLowerException
    apply (div_le_iff₀ hZ).2
    calc
      (∑ t ∈ mixScale X, mixWeightV t *
          finiteRootMixSmallLowerFibreMass (ahlSmall_window κ X)
            (sieveCutoff (t : ℝ)) (profileL κ X)) ≤
        ∑ t ∈ mixScale X, mixWeightV t * q :=
          sum_le_sum fun t ht ↦
            mul_le_mul_of_nonneg_left (hfibre t ht) (mixWeightV_nonneg t)
      _ = q * mixZ X := by
        rw [← Finset.sum_mul]
        unfold mixZ
        ring
  exact havg.trans (by simpa only [q] using hrateX)

/-- The actual original-law high-count loss is `O(1 / profileL)` with an
explicit constant. -/
theorem eventually_coreFiniteRootMixUpperException_le_inv_rank
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      coreFiniteRootMixUpperException κ X ≤
        linearCountRateConstant / (profileL κ X : ℝ) := by
  filter_upwards [eventually_coreFiniteRootMixUpperException_le hκ,
    eventually_finiteRootMixSmallLowerException_le_log_sq hκ,
    eventually_profileL_le_log_small_sq hκ,
    eventually_one_le_profileL hκ,
    eventually_coreLinearScales_sixteen_le_small hκ] with
      X hupper hlower hrank hL hS
  let Lr : ℝ := profileL κ X
  let logS : ℝ := Real.log (ahlSmall_window κ X : ℝ)
  let c : ℝ := presieveLowerRateConstant (1 / 100)
  have hLpos : 0 < Lr := by
    dsimp only [Lr]
    exact Nat.cast_pos.mpr (by omega)
  have hlogSpos : 0 < logS := by
    dsimp only [logS]
    exact Real.log_pos (Nat.one_lt_cast.mpr (by omega))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    exact (presieveLowerRateConstant_pos
      (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hinv : 1 / logS ^ 2 ≤ 1 / Lr := by
    apply one_div_le_one_div_of_le hLpos
    simpa only [Lr, logS] using hrank
  have hlower' : finiteRootMixSmallLowerException κ X ≤ c / Lr := by
    calc
      finiteRootMixSmallLowerException κ X ≤ c / logS ^ 2 := by
        simpa only [c, logS] using hlower
      _ ≤ c / Lr := by
        have hh := mul_le_mul_of_nonneg_left hinv hc0
        simpa only [div_eq_mul_inv, one_mul] using hh
  calc
    coreFiniteRootMixUpperException κ X ≤
        (profileL κ X : ℝ)⁻¹ + finiteRootMixSmallLowerException κ X := hupper
    _ ≤ 1 / Lr + c / Lr := by
      simpa only [Lr, one_div] using _root_.add_le_add le_rfl hlower'
    _ = linearCountRateConstant / (profileL κ X : ℝ) := by
      unfold linearCountRateConstant
      dsimp only [Lr, c]
      ring

/-! ## The canonical finite mixture -/

/-- Explicit quantitative estimate for the actual canonical normalized
finite-root linear mean.  The eventual threshold is before `f` and `K`.
-/
theorem eventually_coreLinearFiniteRootMean_le_quantitative_explicit
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∀ᶠ X : ℕ in atTop,
      ∀ (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0),
        LipschitzWith K f → (∀ x, 0 ≤ f x) →
        coreLinearFiniteRootMean B X (ahlSmall_window κ X)
            (profileL κ X) f ≤
          (648 / eulerProdLowerConst : ℝ) *
              (∫ x : AddCircle (1 : ℝ), f x) +
            (576 / eulerProdLowerConst : ℝ) *
                ((B : ℝ) * ((B : ℝ) - 1)) *
                windowG X ^ (-(1 / 2 : ℝ)) * (K : ℝ) +
            ((72 / eulerProdLowerConst : ℝ) *
                windowG X ^ (-(1 / 2 : ℝ)) +
              linearCountRateConstant / (profileL κ X : ℝ)) * ‖f‖ := by
  have hlogB : 0 < Real.log (B : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (by omega))
  have hκpos : 0 < κ := (div_pos zero_lt_one hlogB).trans_le hκ
  filter_upwards [
      tendsto_windowG_atTop.eventually
        (eventually_coreLinear_diagonal_slot_sum_le B hB),
      eventually_coreLinearMixtureScales hκpos,
      coreFRMUpper_eventually_lateRetention_le_quarter hκpos,
      CoreLinearInsertion.eventually_critical_rank_profileL hB hκ,
      eventually_coreFiniteRootMixUpperException_le_inv_rank hκpos,
      eventually_ge_atTop 1] with
      X hdiag hscale hquarter hcritical hupper hX
  intro f K hK hf0
  let G := windowG X
  let S := ahlSmall_window κ X
  let L := profileL κ X
  let m : ℝ := ∫ x : AddCircle (1 : ℝ), f x
  let C : ℝ := ‖f‖
  let D : ℝ := (K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1))
  let e : ℝ := G ^ (-(1 / 2 : ℝ))
  obtain ⟨J, hJ, hJL, hratioLo, hratioHi⟩ := hcritical
  have hslope := CoreLinearInsertion.scaled_slope_bounds hB hratioLo hratioHi
  have hslo : 1 ≤ G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) := by
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    have hB1 : (1 : ℝ) ≤ (B : ℝ) - 1 := by linarith
    exact hB1.trans hslope.1
  have hshi : G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) ≤
      (B : ℝ) * ((B : ℝ) - 1) := hslope.2.le
  have hZ : 0 < mixZ X := mixZ_pos hX
  have hm0 : 0 ≤ m := by dsimp only [m]; exact integral_nonneg hf0
  have hC0 : 0 ≤ C := by dsimp only [C]; exact norm_nonneg _
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg K.coe_nonneg (mul_nonneg (by linarith) (by linarith))
  have he0 : 0 ≤ e := by
    dsimp only [e]
    exact Real.rpow_nonneg (zero_lt_one.trans hscale.1).le _
  have hroot : ∀ t ∈ mixScale X,
      coreLinearActualRootMean B (sieveCutoff (t : ℝ)) S L f ≤
        (648 / eulerProdLowerConst : ℝ) * m +
          (576 / eulerProdLowerConst : ℝ) * e * D +
          (72 / eulerProdLowerConst : ℝ) * e * C +
          C * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ)) := by
    intro t ht
    have hs := hscale.2.2.2.2 t ht
    have hbase := coreLinearActualRootMean_le_quantitative B hB
      (fun f K hK hf0 n σ F hG hfloor hJ hJL hLn hF hlo hhi ↦
        hdiag f K hK hf0 S L J n σ F hG hfloor hJ hJL hLn hF hlo hhi)
      hscale.1 hscale.2.2.2.1 hs.1
      (by omega) hJ hJL (hquarter t ht) hslo hshi f K hK hf0
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
    have hgap0 : 0 ≤ coreAuxiliaryLayerPhysicalGapMean S
        (sieveCutoff (t : ℝ)) L (J - 1) := by
      rw [← coreAuxiliaryLayerFrameMass_subsetGap_expectation]
      exact sum_nonneg fun F _ ↦ mul_nonneg
        (coreAuxiliaryLayerFrameMass_nonneg S (sieveCutoff (t : ℝ)) L hs.1 F)
        (Nat.cast_nonneg _)
    have hgapDiv0 : 0 ≤ coreAuxiliaryLayerPhysicalGapMean S
        (sieveCutoff (t : ℝ)) L (J - 1) / G :=
      div_nonneg hgap0 (zero_lt_one.trans hscale.1).le
    have hgapPlus : coreAuxiliaryLayerPhysicalGapMean S
        (sieveCutoff (t : ℝ)) L (J - 1) / G + 1 ≤ 9 := by linarith
    let q := coreAuxiliaryLayerPhysicalGapMean S
      (sieveCutoff (t : ℝ)) L (J - 1) / G
    have hDgap : D * q ≤ 8 * D := by
      simpa only [q, mul_comm] using mul_le_mul_of_nonneg_left hgapDiv hD0
    have hbracket :
        ((q + 1) * m + e * (D * q + C)) ≤ 9 * m + e * (8 * D + C) := by
      exact _root_.add_le_add
        (mul_le_mul_of_nonneg_right hgapPlus hm0)
        (mul_le_mul_of_nonneg_left
          (_root_.add_le_add hDgap le_rfl) he0)
    have hcoef0 : 0 ≤ 24 * lateRetention S (sieveCutoff (t : ℝ)) * G /
        Real.log G := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hs.2.2.1)
          (zero_lt_one.trans hscale.1).le) hscale.2.1.le
    have hcoefBound : 24 * lateRetention S (sieveCutoff (t : ℝ)) * G /
        Real.log G ≤ 24 * ((3 : ℝ) / eulerProdLowerConst) := by
      have hh := mul_le_mul_of_nonneg_left hs.2.2.2.1
        (by norm_num : (0 : ℝ) ≤ 24)
      calc
        24 * lateRetention S (sieveCutoff (t : ℝ)) * G / Real.log G =
            24 * (lateRetention S (sieveCutoff (t : ℝ)) * G /
              Real.log G) := by ring
        _ ≤ 24 * ((3 : ℝ) / eulerProdLowerConst) := hh
    have hbracket0 : 0 ≤ 9 * m + e * (8 * D + C) :=
      _root_.add_nonneg (mul_nonneg (by norm_num) hm0)
        (mul_nonneg he0 (_root_.add_nonneg
          (mul_nonneg (by norm_num) hD0) hC0))
    have hmain :=
      (mul_le_mul_of_nonneg_left hbracket hcoef0).trans
        (mul_le_mul_of_nonneg_right hcoefBound hbracket0)
    exact hbase.trans (_root_.add_le_add (hmain.trans_eq (by
      dsimp only [q, m, C, D, e]
      field_simp [eulerProdLowerConst_pos.ne'] <;> ring)) le_rfl)
  have hsum :
      (∑ t ∈ mixScale X, mixWeightV t *
          CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
            (fun U ↦ f (coreLinearShapePhase B L U : AddCircle (1 : ℝ)))) ≤
        ∑ t ∈ mixScale X, mixWeightV t *
          ((648 / eulerProdLowerConst : ℝ) * m +
            (576 / eulerProdLowerConst : ℝ) * e * D +
            (72 / eulerProdLowerConst : ℝ) * e * C +
            C * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) := by
    apply sum_le_sum
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (mixWeightV_nonneg t)
    change coreLinearActualRootMean B (sieveCutoff (t : ℝ)) S L f ≤ _
    exact hroot t ht
  have hdiv := div_le_div_of_nonneg_right hsum hZ.le
  let z : ℝ := (648 / eulerProdLowerConst : ℝ) * m +
    (576 / eulerProdLowerConst : ℝ) * e * D +
    (72 / eulerProdLowerConst : ℝ) * e * C
  have hnormalize :
      (∑ t ∈ mixScale X, mixWeightV t *
          (z + C * coreFiniteRootMixUpperRootMass S
            (sieveCutoff (t : ℝ)))) / mixZ X =
        z + C * coreFiniteRootMixUpperException κ X := by
    unfold coreFiniteRootMixUpperException
    have hnum :
        (∑ t ∈ mixScale X, mixWeightV t *
          (z + C * coreFiniteRootMixUpperRootMass S
            (sieveCutoff (t : ℝ)))) =
          mixZ X * z + C * (∑ t ∈ mixScale X, mixWeightV t *
            coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) := by
      simp_rw [mul_add]
      rw [sum_add_distrib, ← Finset.sum_mul]
      change mixZ X * z +
        (∑ t ∈ mixScale X, mixWeightV t *
          (C * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ)))) = _
      congr 1
      rw [Finset.mul_sum]
      exact sum_congr rfl fun t _ ↦ by ring
    rw [hnum]
    dsimp only [S]
    field_simp [hZ.ne']
  have hraw : coreLinearFiniteRootMean B X S L f ≤
      z + C * coreFiniteRootMixUpperException κ X := by
    rw [linearMean_eq_positiveMean, corePositiveFiniteRootMean_eq_weighted]
    exact hdiv.trans_eq hnormalize
  have hhigh := mul_le_mul_of_nonneg_left hupper hC0
  have hfinal := hraw.trans (_root_.add_le_add le_rfl hhigh)
  dsimp only [z, G, S, L, m, C, D, e] at hfinal ⊢
  exact hfinal.trans_eq (by ring)

/-- Packaged paper-form estimate with constants independent of the test.
Only the second constant depends on the base (the threshold may also depend
on `κ`). -/
theorem coreLinearFiniteRootMean_quantitative_bound
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∃ Cvol Cerr : ℝ, 0 ≤ Cvol ∧ 0 ≤ Cerr ∧
      ∀ᶠ X : ℕ in atTop,
        ∀ (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0),
          LipschitzWith K f → (∀ x, 0 ≤ f x) →
          coreLinearFiniteRootMean B X (ahlSmall_window κ X)
              (profileL κ X) f ≤
            Cvol * (∫ x : AddCircle (1 : ℝ), f x) +
              Cerr * (((profileL κ X : ℝ)⁻¹ +
                  windowG X ^ (-(1 / 2 : ℝ))) * ‖f‖ +
                windowG X ^ (-(1 / 2 : ℝ)) * (K : ℝ)) := by
  have hEuler := eulerProdLowerConst_pos
  have hCount := linearCountRateConstant_pos
  let Cvol : ℝ := 648 / eulerProdLowerConst
  let Cerr : ℝ :=
    576 / eulerProdLowerConst * ((B : ℝ) * ((B : ℝ) - 1)) +
      72 / eulerProdLowerConst + linearCountRateConstant
  refine ⟨Cvol, Cerr, ?_, ?_, ?_⟩
  · dsimp only [Cvol]
    exact div_nonneg (by norm_num) eulerProdLowerConst_pos.le
  · dsimp only [Cerr]
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    have hB1 : 0 ≤ (B : ℝ) - 1 := by linarith
    positivity
  filter_upwards [eventually_coreLinearFiniteRootMean_le_quantitative_explicit
    B hB hκ, eventually_one_le_profileL
      ((div_pos zero_lt_one
        (Real.log_pos (Nat.one_lt_cast.mpr (by omega)))).trans_le hκ)] with X hX hL
  intro f K hK hf0
  have hbase := hX f K hK hf0
  let e : ℝ := windowG X ^ (-(1 / 2 : ℝ))
  let q : ℝ := (profileL κ X : ℝ)⁻¹
  let a : ℝ := 576 / eulerProdLowerConst *
    ((B : ℝ) * ((B : ℝ) - 1))
  let b : ℝ := 72 / eulerProdLowerConst
  let c : ℝ := linearCountRateConstant
  have he0 : 0 ≤ e := by
    dsimp only [e]
    exact Real.rpow_nonneg (zero_le_one.trans (crtWindowG_one_le X)) _
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    have hB1 : 0 ≤ (B : ℝ) - 1 := by linarith
    positivity
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    exact linearCountRateConstant_pos.le
  have hnorm0 : 0 ≤ ‖f‖ := norm_nonneg _
  have hK0 : 0 ≤ (K : ℝ) := K.coe_nonneg
  have hcollect :
      a * e * (K : ℝ) + (b * e + c * q) * ‖f‖ ≤
        (a + b + c) * ((q + e) * ‖f‖ + e * (K : ℝ)) := by
    rw [← sub_nonneg]
    have hid :
        (a + b + c) * ((q + e) * ‖f‖ + e * (K : ℝ)) -
            (a * e * (K : ℝ) + (b * e + c * q) * ‖f‖) =
          a * q * ‖f‖ + a * e * ‖f‖ + b * q * ‖f‖ +
            b * e * (K : ℝ) + c * e * ‖f‖ + c * e * (K : ℝ) := by
      ring
    rw [hid]
    positivity
  have hbase' :
      coreLinearFiniteRootMean B X (ahlSmall_window κ X) (profileL κ X) f ≤
        Cvol * (∫ x : AddCircle (1 : ℝ), f x) +
          (a * e * (K : ℝ) + (b * e + c * q) * ‖f‖) := by
    refine hbase.trans_eq ?_
    dsimp only [Cvol, a, b, c, e, q]
    ring
  change coreLinearFiniteRootMean B X (ahlSmall_window κ X) (profileL κ X) f ≤
    Cvol * (∫ x : AddCircle (1 : ℝ), f x) +
      (a + b + c) * ((q + e) * ‖f‖ + e * (K : ℝ))
  exact hbase'.trans (_root_.add_le_add le_rfl hcollect)

end

end PrimeGapNormality.Prime.CoreLinearQuantitativeModel
