import PrimeGapNormality.Prime.CoreSelbergGlobalInsertion
import PrimeGapNormality.Prime.CoreLinearInsertionAction
import PrimeGapNormality.Prime.CoreDigitalLinearDomination
import PrimeGapNormality.Prime.CorePositiveTail
import PrimeGapNormality.Prime.CoreAuxiliaryMixtureMean
import PrimeGapNormality.Prime.CoreFiniteRootMixUpperException

/-!
# Finite positive linear model mean

This is the finite contraction used by the P1a consumer.  The exact ordered
linear insertion action is combined with the global Selberg insertion bound
on a literal presieve slot.  No spacing, grid, or asymptotic insertion bound
is assumed as an input.
-/

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

noncomputable section

/-- Every subset of the literal `S`-presieve avoids one residue class for
each prime up to any smaller radius. -/
theorem coreLinear_presieveSubset_avoids
    {S R : ℕ} (σ : ResidueChoice S) {E : Finset ℕ}
    (hE : E ⊆ presieveSurvivors S σ) (hRS : R ≤ S) :
    CoreSelberg.AvoidsResidues E R := by
  intro p hp
  have hpS : p ∈ Nat.primesLE S := Nat.primesLE_mono hRS hp
  refine ⟨residueOfChoice S σ p, ?_⟩
  intro n hn
  have hsurv : n % p ≠ residueOfChoice S σ p :=
    (mem_filter.mp (hE hn)).2 p hpS
  have hlt : residueOfChoice S σ p < p := by
    simp only [residueOfChoice, dif_pos hpS]
    have hs := (σ ⟨p, hpS⟩).isLt
    change (σ ⟨p, hpS⟩).val < p - 1 at hs
    change (σ ⟨p, hpS⟩).val + 1 < p
    omega
  rwa [Nat.mod_eq_of_lt hlt]

/-- Uniform-in-the-frame positive slot estimate.  The slope assumptions are
exactly what the later profile choice supplies: `1 ≤ s ≤ B(B-1)`.
The mesh error remains the explicit fixed `δ` term, linear in `W+1`. -/
theorem eventually_coreLinear_presieve_slot_sum_le
    (B : ℕ) (hB : 2 ≤ B)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    {C δ : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ G : ℝ in atTop,
      ∀ (S L J n : ℕ) (σ : ResidueChoice S) (F : Finset ℕ),
        1 < G → ⌊G⌋₊ ≤ S → 1 ≤ J → J < L → L ≤ n →
        F ∈ (presieveSurvivors S σ).powersetCard (n - 1) →
        1 ≤ G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) →
        G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) ≤
          (B : ℝ) * ((B : ℝ) - 1) →
        (∑ u ∈ openSlot (presieveSurvivors S σ) (F.sort (· ≤ ·)) (J - 1),
          f (coreLinearShapePhase B L (insert u F) : AddCircle (1 : ℝ))) ≤
          3 * G / Real.log G *
            ((((subsetGap F (J - 1) : ℝ) / G) + 1) *
                ((∫ x : AddCircle (1 : ℝ), f x) +
                  δ * ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)))) +
              δ * C) := by
  let D : ℝ := (B : ℝ) * ((B : ℝ) - 1)
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    nlinarith
  let Dnn : ℝ≥0 := ⟨D, hD⟩
  let K' : ℝ≥0 := K * Dnn
  have hKreal : (K' : ℝ) = (K : ℝ) * D := rfl
  have hC : 0 ≤ C := (hf0 0).trans (hfC 0)
  filter_upwards [CoreSelberg.eventually_global_positive_insertion
    (K := K') hC hδ hδ1] with G hglobal
  intro S L J n σ F hG1 hfloor hJ hJL hLn hF hslo hshi
  let A := presieveSurvivors S σ
  let E := openSlot A (F.sort (· ≤ ·)) (J - 1)
  let a := (CoreLinearInsertion.insertionSlot F J).1
  let W := (subsetGap F (J - 1) : ℝ) / G
  let s := G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1)
  let O := CoreLinearInsertion.outerPhase B L J F
  let f' : ℝ → ℝ := fun z => f ((O + s * z : ℝ) : AddCircle (1 : ℝ))
  have hG : 0 < G := zero_lt_one.trans hG1
  have hFm := mem_powersetCard.mp hF
  have hn : 1 ≤ n := by omega
  have hFcard : F.card + 1 = n := by
    rw [hFm.2, Nat.sub_add_cancel hn]
  have hFL : L ≤ F.card + 1 := hFcard ▸ hLn
  have hJcard : J - 1 < F.card := by omega
  have horder : orderStat F (J - 1) ≤ orderStat F J := by
    simpa [Nat.sub_add_cancel hJ] using
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
      simpa [CoreLinearInsertion.insertionSlot] using hus
    refine ⟨by simpa [a] using huSlot.1, ?_⟩
    have hwidth : W * G =
        ((CoreLinearInsertion.insertionSlot F J).2 : ℝ) -
          (CoreLinearInsertion.insertionSlot F J).1 := by
      dsimp only [W]
      rw [hgap, div_mul_cancel₀ _ hG.ne']
    rw [hwidth]
    have hur : (u : ℝ) < (CoreLinearInsertion.insertionSlot F J).2 := by
      exact_mod_cast huSlot.2
    linarith
  have hEA : E ⊆ A := fun u hu => (mem_openSlot.mp hu).1
  have havoid : CoreSelberg.AvoidsResidues E ⌊G⌋₊ :=
    coreLinear_presieveSubset_avoids σ hEA hfloor
  have hs0 : 0 ≤ s := zero_le_one.trans hslo
  have hsabs : 1 ≤ |s| := by
    rw [abs_of_nonneg hs0]
    exact hslo
  have hsD : |s| ≤ D := by
    rw [abs_of_nonneg hs0]
    exact hshi
  have hLip' : LipschitzWith K' f' := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hfxy := hK.dist_le_mul
      ((O + s * x : ℝ) : AddCircle (1 : ℝ))
      ((O + s * y : ℝ) : AddCircle (1 : ℝ))
    calc
      dist (f' x) (f' y) ≤ (K : ℝ) *
          dist ((O + s * x : ℝ) : AddCircle (1 : ℝ))
            ((O + s * y : ℝ) : AddCircle (1 : ℝ)) := hfxy
      _ ≤ (K : ℝ) * |(O + s * x) - (O + s * y)| :=
        mul_le_mul_of_nonneg_left (coreCircle_dist_coe_le _ _) K.coe_nonneg
      _ = (K : ℝ) * |s| * dist x y := by
        rw [show O + s * x - (O + s * y) = s * (x - y) by ring,
          abs_mul, Real.dist_eq]
        ring
      _ ≤ (K : ℝ) * D * dist x y := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsD K.coe_nonneg) (dist_nonneg : 0 ≤ dist x y)
      _ = (K' : ℝ) * dist x y := by
        rw [hKreal]
  have hf' : ∀ z : ℝ, 0 ≤ f' z ∧ f' z ≤ C := fun z => ⟨hf0 _, hfC _⟩
  have hphase : ∀ u ∈ E,
      coreLinearShapePhase B L (insert u F) = O + s * (((u : ℝ) - a) / G) := by
    intro u hu
    have hus := (mem_openSlot.mp hu).2
    have huSlot :
        (CoreLinearInsertion.insertionSlot F J).1 < u ∧
          u < (CoreLinearInsertion.insertionSlot F J).2 := by
      simpa [CoreLinearInsertion.insertionSlot] using hus
    simpa [O, s, a] using
      CoreLinearInsertion.shapePhase_insert_scaled hB hJ hJL F hFL hG huSlot
  have hsumphase :
      (∑ u ∈ E, f (coreLinearShapePhase B L (insert u F) : AddCircle (1 : ℝ))) =
        ∑ u ∈ E, f' (((u : ℝ) - a) / G) := by
    refine sum_congr rfl fun u hu => ?_
    unfold f'
    rw [hphase u hu]
  have hins := hglobal a W E f' hW hEin havoid hLip' hf'
  have hint := coreDigital_circle_linear_insertion_integral_le
    (fun x => f x) f.continuous hf0 O s W hsabs hW
  rw [hsumphase]
  calc
    (∑ u ∈ E, f' (((u : ℝ) - a) / G)) ≤
        3 * G / Real.log G *
          ((∫ z in (0 : ℝ)..W, f' z) +
            δ * (C + (K' : ℝ) * (W + 1))) := hins
    _ ≤ 3 * G / Real.log G *
        ((W + 1) * (∫ x : AddCircle (1 : ℝ), f x) +
          δ * (C + (K' : ℝ) * (W + 1))) := by
      apply mul_le_mul_of_nonneg_left (add_le_add hint le_rfl)
      exact div_nonneg (mul_nonneg (by norm_num) hG.le) (Real.log_pos hG1).le
    _ = 3 * G / Real.log G *
        ((W + 1) * ((∫ x : AddCircle (1 : ℝ), f x) +
            δ * ((K : ℝ) * D)) + δ * C) := by
      rw [hKreal]
      ring

/-! ### Exact uniform-layer contraction -/

/-- On a good exact-cardinality layer, the insertion prefactor is at most
`4ϑ`.  Averaging the global slot estimate over the uniform auxiliary frames
uses exactly their physical first gap mean; the error is linear in the same
mean and hence needs no span cutoff. -/
theorem eventually_coreLinear_presieve_uniformLayer_le
    (B : ℕ) (hB : 2 ≤ B)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    {C δ : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ G : ℝ in atTop,
      ∀ (S y L J n : ℕ) (σ : ResidueChoice S),
        1 < G → ⌊G⌋₊ ≤ S → S ≤ y → 1 ≤ J → J < L → L ≤ n →
        n ≤ (presieveSurvivors S σ).card →
        (n : ℝ) ≤
          2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y →
        (n : ℝ) ≤ ((presieveSurvivors S σ).card : ℝ) / 2 →
        1 ≤ G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) →
        G * ((B : ℝ) - 1) / (B : ℝ) ^ (J + 1) ≤
          (B : ℝ) * ((B : ℝ) - 1) →
        auxFrame_uniformMean (presieveSurvivors S σ) n
            (fun U => f (coreLinearShapePhase B L U : AddCircle (1 : ℝ))) ≤
          12 * lateRetention S y * G / Real.log G *
            (((auxFrame_uniformMean (presieveSurvivors S σ) (n - 1)
                (fun F => (subsetGap F (J - 1) : ℝ)) / G) + 1) *
              ((∫ x : AddCircle (1 : ℝ), f x) +
                δ * ((K : ℝ) * ((B : ℝ) * ((B : ℝ) - 1)))) +
              δ * C) := by
  filter_upwards [eventually_coreLinear_presieve_slot_sum_le
    B hB f hK hf0 hfC hδ hδ1] with G hslot
  intro S y L J n σ hG1 hfloor hSy hJ hJL hLn hnA hnmean hnhalf hslo hshi
  let A := presieveSurvivors S σ
  let test : Finset ℕ → ℝ := fun U =>
    f (coreLinearShapePhase B L U : AddCircle (1 : ℝ))
  let gap : Finset ℕ → ℝ := fun F => (subsetGap F (J - 1) : ℝ)
  let D : ℝ := (B : ℝ) * ((B : ℝ) - 1)
  let q : ℝ := (∫ x : AddCircle (1 : ℝ), f x) + δ * ((K : ℝ) * D)
  let r : ℝ := δ * C
  let d : ℝ := 3 * G / Real.log G
  have hn : 1 ≤ n := by omega
  have hJn : J < n := lt_of_lt_of_le hJL hLn
  have hjn : J - 1 + 1 < n := by simpa [Nat.sub_add_cancel hJ] using hJn
  have hpos : ∀ x ∈ A, 0 < x := by
    intro x hx
    exact (mem_Icc.mp (corePresieveSurvivors_subset_Icc S σ hx)).1
  have htest0 : ∀ U, 0 ≤ test U := fun U => hf0 _
  have heq := auxFrame_uniformMean_eq (A := A) (n := n) (j := J - 1)
    test hn hnA hjn hpos htest0
  have hslot' : ∀ F ∈ A.powersetCard (n - 1),
      auxFrame_slotInsertSum A (J - 1) test F ≤
        d * (((gap F / G) + 1) * q + r) := by
    intro F hF
    simpa [A, test, gap, D, q, r, d, auxFrame_slotInsertSum] using
      hslot S L J n σ F hG1 hfloor hJ hJL hLn hF hslo hshi
  have hsum :
      (∑ F ∈ A.powersetCard (n - 1), auxFrame_slotInsertSum A (J - 1) test F) ≤
        ∑ F ∈ A.powersetCard (n - 1), d * (((gap F / G) + 1) * q + r) :=
    sum_le_sum hslot'
  have hchoose : (A.card.choose (n - 1) : ℝ) ≠ 0 :=
    auxFrame_choose_pred_ne_zero hnA
  have havg := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (A.card.choose (n - 1)))
  have hGne : G ≠ 0 := (zero_lt_one.trans hG1).ne'
  have hsumfactor :
      (∑ F ∈ A.powersetCard (n - 1), d * (((gap F / G) + 1) * q + r)) =
        d * ((((∑ F ∈ A.powersetCard (n - 1), gap F) / G +
          (A.card.choose (n - 1) : ℝ)) * q) +
          (A.card.choose (n - 1) : ℝ) * r) := by
    have hpoint : ∀ F ∈ A.powersetCard (n - 1),
        d * (((gap F / G) + 1) * q + r) =
          (d * q / G) * gap F + d * (q + r) := by
      intro F _
      field_simp [hGne]
      ring
    rw [sum_congr rfl hpoint, sum_add_distrib, ← Finset.mul_sum,
      sum_const, auxFrame_powersetCard_card, nsmul_eq_mul]
    ring
  have hnormalize :
      (∑ F ∈ A.powersetCard (n - 1), d * (((gap F / G) + 1) * q + r)) /
          (A.card.choose (n - 1) : ℝ) =
        d * (((auxFrame_uniformMean A (n - 1) gap / G) + 1) * q + r) := by
    unfold auxFrame_uniformMean
    rw [hsumfactor]
    field_simp [hchoose, hGne]
    <;> ring
  have havg' :
      (∑ F ∈ A.powersetCard (n - 1), auxFrame_slotInsertSum A (J - 1) test F) /
          (A.card.choose (n - 1) : ℝ) ≤
        d * (((auxFrame_uniformMean A (n - 1) gap / G) + 1) * q + r) :=
    havg.trans_eq hnormalize
  have hdenpos : 0 < (A.card : ℝ) - n + 1 := by
    rw [← auxFrame_cast_sub hnA]
    positivity
  have hAcardS : A.card ≤ S := by
    have hsub : A ⊆ Icc 1 S := by
      simpa [A] using corePresieveSurvivors_subset_Icc S σ
    have hc := card_le_card hsub
    simpa [Nat.card_Icc] using hc
  have hS2 : 2 ≤ S := (le_trans (by omega : 2 ≤ n) hnA).trans hAcardS
  have htheta : 0 ≤ lateRetention S y :=
    (rootedEulerProdNat_pos hS2).le
  have hdenhalf : (A.card : ℝ) / 2 ≤ (A.card : ℝ) - n + 1 := by
    nlinarith
  have hcoef : (n : ℝ) / ((A.card : ℝ) - n + 1) ≤
      4 * lateRetention S y := by
    apply (div_le_iff₀ hdenpos).2
    have hfourtheta : 0 ≤ 4 * lateRetention S y := mul_nonneg (by norm_num) htheta
    have hmul := mul_le_mul_of_nonneg_left hdenhalf hfourtheta
    nlinarith
  have hq : 0 ≤ q := by
    dsimp only [q, D]
    have hI : 0 ≤ ∫ x : AddCircle (1 : ℝ), f x := integral_nonneg hf0
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    have hD0 : 0 ≤ (B : ℝ) * ((B : ℝ) - 1) := by nlinarith
    exact add_nonneg hI (mul_nonneg hδ.le (mul_nonneg K.coe_nonneg hD0))
  have hr : 0 ≤ r := by
    dsimp only [r]
    have hC : 0 ≤ C := (hf0 0).trans (hfC 0)
    exact mul_nonneg hδ.le hC
  have hd : 0 ≤ d := by
    dsimp only [d]
    exact div_nonneg (mul_nonneg (by norm_num) (zero_lt_one.trans hG1).le)
      (Real.log_pos hG1).le
  have hgapMean : 0 ≤ auxFrame_uniformMean A (n - 1) gap :=
    auxFrame_uniformMean_nonneg (fun F => Nat.cast_nonneg _)
  have hbracket :
      0 ≤ d * (((auxFrame_uniformMean A (n - 1) gap / G) + 1) * q + r) := by
    have hG : 0 ≤ G := (zero_lt_one.trans hG1).le
    exact mul_nonneg hd (add_nonneg
      (mul_nonneg (add_nonneg (div_nonneg hgapMean hG) zero_le_one) hq) hr)
  have hform :
      auxFrame_uniformMean A n test =
        ((n : ℝ) / ((A.card : ℝ) - n + 1)) *
          ((∑ F ∈ A.powersetCard (n - 1),
              auxFrame_slotInsertSum A (J - 1) test F) /
            (A.card.choose (n - 1) : ℝ)) := by
    rw [heq]
    ring
  change auxFrame_uniformMean A n test ≤ _
  rw [hform]
  calc
    ((n : ℝ) / ((A.card : ℝ) - n + 1)) *
        ((∑ F ∈ A.powersetCard (n - 1),
            auxFrame_slotInsertSum A (J - 1) test F) /
          (A.card.choose (n - 1) : ℝ)) ≤
      ((n : ℝ) / ((A.card : ℝ) - n + 1)) *
        (d * (((auxFrame_uniformMean A (n - 1) gap / G) + 1) * q + r)) :=
      mul_le_mul_of_nonneg_left havg' (div_nonneg (Nat.cast_nonneg _) hdenpos.le)
    _ ≤ (4 * lateRetention S y) *
        (d * (((auxFrame_uniformMean A (n - 1) gap / G) + 1) * q + r)) :=
      mul_le_mul_of_nonneg_right hcoef hbracket
    _ = 12 * lateRetention S y * G / Real.log G *
        (((auxFrame_uniformMean A (n - 1) gap / G) + 1) * q + r) := by
      dsimp only [d]
      ring

end

end PrimeGapNormality.Prime
