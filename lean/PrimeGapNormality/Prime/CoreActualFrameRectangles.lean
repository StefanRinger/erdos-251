import PrimeGapNormality.Prime.CoreAuxiliaryRectangleBound
import PrimeGapNormality.Prime.CoreAuxiliaryFrameMass
import PrimeGapNormality.Prime.CoreActualFrameJoint
import PrimeGapNormality.Prime.CoreSelbergPositiveInsertion
import PrimeGapNormality.Prime.CoreFiniteRootMixUpperException

/-!
# Concrete finite rectangle bounds for actual auxiliary frames

This first checkpoint proves actual translated Selberg candidate caps,
the good-count presieve layer bound, and exact aggregation under the
genuine auxiliary/frame joint laws. It does not yet assert the asymptotic
rectangle domination of the full mixture: high-count aggregation and the
fixed-dimensional padded-cap asymptotics remain separate steps.
-/

namespace PrimeGapNormality.Prime.CoreActualFrameRectangles

open Finset Set MeasureTheory
open scoped Classical BigOperators Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Integer padding for a real interval of physical length `h`. -/
def intervalLength (h : ℝ) : ℕ := ⌈h⌉₊ + 1

/-- Selberg's actual finite cap on a real translated interval. The carrier
consists of positive integers; the left endpoint may be any real number. -/
theorem real_interval_card_le (E : Finset ℕ) {l h : ℝ} {R : ℕ}
    (hpos : ∀ n ∈ E, 0 < n)
    (hinterval : ∀ n ∈ E, l < (n : ℝ) ∧ (n : ℝ) < l + h)
    (hR : 1 ≤ R) (hRH : R ≤ intervalLength h)
    (havoid : CoreSelberg.AvoidsResidues E R) :
    (E.card : ℝ) ≤ CoreSelberg.cellCap (intervalLength h) R := by
  let a : ℕ := ⌊max l 0⌋₊
  have hl : l < (a : ℝ) + 1 :=
    (le_max_left l 0).trans_lt (Nat.lt_floor_add_one (max l 0))
  have hsub : E ⊆ Ioc a (a + intervalLength h) := by
    intro n hn
    apply Finset.mem_Ioc.2
    constructor
    · by_cases hl0 : 0 ≤ l
      · have ha : (a : ℝ) ≤ l := by
          dsimp only [a]
          rw [max_eq_left hl0]
          exact Nat.floor_le hl0
        exact_mod_cast ha.trans_lt (hinterval n hn).1
      · have ha : a = 0 := by simp only [a, max_eq_right (le_of_not_ge hl0), Nat.floor_zero]
        rw [ha]
        exact hpos n hn
    · have hceil := Nat.le_ceil h
      have hnR : (n : ℝ) ≤ ((a + intervalLength h : ℕ) : ℝ) := by
        simp only [intervalLength, Nat.cast_add, Nat.cast_one]
        linarith [(hinterval n hn).2]
      exact_mod_cast hnR
  exact CoreSelberg.translated_card_le hR hRH hsub havoid

def candidateCap (G l u : ℝ) (R : ℕ) : ℕ :=
  ⌈CoreSelberg.cellCap (intervalLength (G * (u - l))) R⌉₊

theorem translated_candidate_cap (A : Finset ℕ) {G l u : ℝ} {R : ℕ}
    (hpos : ∀ n ∈ A, 0 < n) (hR : 1 ≤ R)
    (hRH : R ≤ intervalLength (G * (u - l)))
    (havoid : CoreSelberg.AvoidsResidues A R) (a : ℝ) :
    (CoreUniformGapRectangles.translatedCandidates A (Set.Ioo (G * l) (G * u)) a).card ≤
      candidateCap G l u R := by
  let E := CoreUniformGapRectangles.translatedCandidates A (Set.Ioo (G * l) (G * u)) a
  have hEA : E ⊆ A := fun n hn => (CoreUniformGapRectangles.mem_translatedCandidates.1 hn).1
  have hinterval : ∀ n ∈ E,
      a + G * l < (n : ℝ) ∧ (n : ℝ) < (a + G * l) + G * (u - l) := by
    intro n hn
    have hmem := (CoreUniformGapRectangles.mem_translatedCandidates.1 hn).2
    constructor <;> nlinarith [hmem.1, hmem.2]
  have h := real_interval_card_le E (fun n hn => hpos n (hEA hn)) hinterval
    hR hRH (havoid.mono hEA)
  have hceil := h.trans (Nat.le_ceil (CoreSelberg.cellCap (intervalLength (G * (u - l))) R))
  exact_mod_cast hceil

/-- The actual presieve supplies literal forbidden residue classes. -/
theorem presieve_avoids {S R : ℕ} (σ : ResidueChoice S) (hRS : R ≤ S) :
    CoreSelberg.AvoidsResidues (presieveSurvivors S σ) R := by
  intro p hp
  have hpS : p ∈ Nat.primesLE S := Nat.primesLE_mono hRS hp
  refine ⟨residueOfChoice S σ p, ?_⟩
  intro n hn
  have hsurv : n % p ≠ residueOfChoice S σ p := (mem_filter.mp hn).2 p hpS
  have hlt : residueOfChoice S σ p < p := by
    simp only [residueOfChoice, dif_pos hpS]
    have hs := (σ ⟨p, hpS⟩).isLt
    change (σ ⟨p, hpS⟩).val < p - 1 at hs
    change (σ ⟨p, hpS⟩).val + 1 < p
    omega
  rwa [Nat.mod_eq_of_lt hlt]

def rectangleIndicator (J : Finset ℕ) (G : ℝ) (l u : ℕ → ℝ) (F : Finset ℕ) : ℝ :=
  if ∀ i ∈ J, (subsetGap F i : ℝ) / G ∈ Set.Ioo (l i) (u i) then 1 else 0

/-- Concrete finite good-count layer estimate. The original cardinality is
`n`; the auxiliary frame is a uniform `(n-1)`-subset of the actual presieve.
Every candidate cap on the right was proved from Selberg above. -/
theorem presieve_good_layer_rectangle_le
    (S y L n : ℕ) (σ : ResidueChoice S) (J : Finset ℕ)
    (l u : ℕ → ℝ) (R : ℕ → ℕ) {G : ℝ} (hG : 0 < G)
    (hL : 1 ≤ L) (hLn : L ≤ n) (hn : n ≤ (presieveSurvivors S σ).card)
    (hJ : ∀ i ∈ J, i + 1 < L)
    (hcount : (n : ℝ) ≤ 2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y)
    (hθ : 0 < lateRetention S y) (hθ4 : lateRetention S y ≤ (1 : ℝ) / 4)
    (hR : ∀ i ∈ J, 1 ≤ R i ∧ R i ≤ intervalLength (G * (u i - l i)) ∧ R i ≤ S) :
    auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) (rectangleIndicator J G l u) ≤
      ((4 : ℝ) * lateRetention S y) ^ J.card *
        ∏ i ∈ J, (candidateCap G (l i) (u i) (R i) : ℝ) := by
  have hJm : ∀ i ∈ J, i < n - 1 := by
    intro i hi
    have := hJ i hi
    omega
  have hJsub : J ⊆ range (n - 1) := fun i hi => mem_range.2 (hJm i hi)
  have hcard : J.card ≤ n - 1 := by simpa only [card_range] using Finset.card_le_card hJsub
  have hcap : ∀ i ∈ J, ∀ a : ℝ,
      (CoreUniformGapRectangles.translatedCandidates (presieveSurvivors S σ)
        (Set.Ioo (G * l i) (G * u i)) a).card ≤ candidateCap G (l i) (u i) (R i) := by
    intro i hi a
    apply translated_candidate_cap _ _ (hR i hi).1 (hR i hi).2.1
      (presieve_avoids σ (hR i hi).2.2) a
    intro t ht
    exact (Finset.mem_Icc.1 (corePresieveSurvivors_subset_Icc S σ ht)).1
  have hcount' : ((n - 1 : ℕ) : ℝ) ≤
      2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y :=
    (Nat.cast_le.2 (Nat.sub_le n 1)).trans hcount
  have h := CoreAuxiliaryRectangleBound.uniformMean_rectangle_indicator_le_fourTheta
    (presieveSurvivors S σ) (n - 1) J
    (fun i => Set.Ioo (G * l i) (G * u i))
    (fun i => candidateCap G (l i) (u i) (R i))
    ((Nat.sub_le n 1).trans hn) hcard hJm hcap hcount' hθ hθ4
  have htest : rectangleIndicator J G l u =
      (fun F : Finset ℕ => if ∀ i ∈ J,
        (subsetGap F i : ℝ) ∈ Set.Ioo (G * l i) (G * u i) then 1 else 0) := by
    funext F
    simp only [rectangleIndicator, Set.mem_Ioo, lt_div_iff₀ hG, div_lt_iff₀ hG, mul_comm]
  rw [htest]
  apply le_trans ?_ h
  unfold auxFrame_uniformMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro F _
  split_ifs <;> exact le_rfl

/-! ### The actual finite exterior-coordinate indexing -/

open CoreCyclic.OnePoint.FiniteExterior

def rankEndpoints (w j : ℕ) (a : Fin (2 * w + 1) → ℝ) : ℕ → ℝ :=
  Function.extend (frameRank w j) a (fun _ => 0)

theorem rankEndpoints_apply {w j : ℕ} (hj : w + 1 ≤ j)
    (a : Fin (2 * w + 1) → ℝ) (i : Fin (2 * w + 1)) :
    rankEndpoints w j a (frameRank w j i) = a i :=
  (frameRank_injective w j hj).extend_apply a (fun _ => 0) i

theorem rectangleIndicator_eq_localFrame {w j : ℕ} (hj : w + 1 ≤ j)
    (G : ℝ) (a b : Fin (2 * w + 1) → ℝ) (F : Finset ℕ) :
    rectangleIndicator (frameRanks w j) G (rankEndpoints w j a) (rankEndpoints w j b) F =
      if ∀ i, CoreActualFrameJoint.localFrame w j G F i ∈ Set.Ioo (a i) (b i) then 1 else 0 := by
  unfold rectangleIndicator
  congr 1
  apply propext
  constructor
  · intro h i
    have hi : frameRank w j i ∈ frameRanks w j := mem_image.2 ⟨i, mem_univ _, rfl⟩
    simpa only [rankEndpoints_apply hj, CoreActualFrameJoint.localFrame] using h _ hi
  · intro h n hn
    obtain ⟨i, _, rfl⟩ := mem_image.1 hn
    simpa only [rankEndpoints_apply hj, CoreActualFrameJoint.localFrame] using h i

/-- The preceding finite Selberg bound for the actual `localFrame` vector,
with the exact dimension and physical rank map used by the joint law. -/
theorem actual_presieve_good_layer_rectangle_le
    (S y L n w j : ℕ) (σ : ResidueChoice S)
    (a b : Fin (2 * w + 1) → ℝ) (R : ℕ → ℕ) {G : ℝ} (hG : 0 < G)
    (hj : w + 1 ≤ j) (hjL : j + w < L)
    (hLn : L ≤ n) (hn : n ≤ (presieveSurvivors S σ).card)
    (hcount : (n : ℝ) ≤ 2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y)
    (hθ : 0 < lateRetention S y) (hθ4 : lateRetention S y ≤ (1 : ℝ) / 4)
    (hR : ∀ i : Fin (2 * w + 1),
      1 ≤ R (frameRank w j i) ∧
        R (frameRank w j i) ≤ intervalLength (G * (b i - a i)) ∧ R (frameRank w j i) ≤ S) :
    auxFrame_uniformMean (presieveSurvivors S σ) (n - 1)
        (fun F => if ∀ i, CoreActualFrameJoint.localFrame w j G F i ∈ Set.Ioo (a i) (b i)
          then 1 else 0) ≤
      ((4 : ℝ) * lateRetention S y) ^ (2 * w + 1) *
        ∏ i : Fin (2 * w + 1), (candidateCap G (a i) (b i) (R (frameRank w j i)) : ℝ) := by
  have hRp : ∀ i ∈ frameRanks w j, 1 ≤ R i ∧
      R i ≤ intervalLength (G * (rankEndpoints w j b i - rankEndpoints w j a i)) ∧ R i ≤ S := by
    intro i hi
    obtain ⟨t, _, rfl⟩ := mem_image.1 hi
    simpa only [rankEndpoints_apply hj] using hR t
  have h := presieve_good_layer_rectangle_le S y L n σ (frameRanks w j)
    (rankEndpoints w j a) (rankEndpoints w j b) R hG (by omega) hLn hn
    (fun i hi => frameRanks_valid hj hjL hi) hcount hθ hθ4 hRp
  have htest : rectangleIndicator (frameRanks w j) G (rankEndpoints w j a) (rankEndpoints w j b) =
      (fun F => if ∀ i, CoreActualFrameJoint.localFrame w j G F i ∈ Set.Ioo (a i) (b i)
        then 1 else 0) := by
    funext F
    exact rectangleIndicator_eq_localFrame hj G a b F
  rw [htest] at h
  rw [frameRanks_card w j hj] at h
  have hprod : (∏ i ∈ frameRanks w j,
      (candidateCap G (rankEndpoints w j a i) (rankEndpoints w j b i) (R i) : ℝ)) =
      ∏ i : Fin (2 * w + 1), (candidateCap G (a i) (b i) (R (frameRank w j i)) : ℝ) := by
    unfold frameRanks
    rw [Finset.prod_image]
    · simp only [rankEndpoints_apply hj]
    · intro i _ t _ hit
      exact frameRank_injective w j hj hit
  rwa [hprod] at h

/-- Exact one-cutoff aggregation for every finite test, preserving the
original early residue choice and cardinality weights. -/
theorem layer_expectation (S y L : ℕ) (f : Finset ℕ → ℝ) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryLayerFrameMass S y L F * f F) =
      (∑ σ : ResidueChoice S,
        ∑ n ∈ Icc L (presieveSurvivors S σ).card,
          cardinalityLayer (presieveSurvivors S σ)
            (lateRootLaw S y (presieveSurvivors S σ)) n *
              auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) f) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  unfold coreAuxiliaryLayerFrameMass
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun x : ℝ => x / (Fintype.card (ResidueChoice S) : ℝ))
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
  rw [coreAuxUniformFrameMass_expectation _ _ _ hsub f]

/-- Exact full-mixture aggregation. No model is substituted for the
literal `mixWeightV / mixZ` law. -/
theorem mixture_expectation (X S L : ℕ) (f : Finset ℕ → ℝ) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryFrameMass X S L F * f F) =
      (∑ t ∈ mixScale X, mixWeightV t *
        ((∑ σ : ResidueChoice S,
          ∑ n ∈ Icc L (presieveSurvivors S σ).card,
            cardinalityLayer (presieveSurvivors S σ)
              (lateRootLaw S (sieveCutoff (t : ℝ)) (presieveSurvivors S σ)) n *
                auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) f) /
          (Fintype.card (ResidueChoice S) : ℝ))) / mixZ X := by
  unfold coreAuxiliaryFrameMass
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun x : ℝ => x / mixZ X)
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  simp_rw [mul_assoc]
  rw [← mul_sum, layer_expectation]

/-- The rectangle test of the actual completed joint law has exactly the
retained auxiliary contribution and its explicit missing atom at frame 0.
The outer phase is arbitrary and may depend on the complete frame. -/
theorem joint_rectangle_integral (X S L w j : ℕ) (G θ : ℝ)
    (O : Finset ℕ → CoreActualFrameJoint.Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    (a b : Fin (2 * w + 1) → ℝ) :
    (∫ z, if ∀ i, CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i) then (1 : ℝ) else 0
      ∂(CoreActualFrameJoint.jointLaw X S L w j G θ O hSy hZ :
        Measure (CoreJointFrameLimit.Joint (2 * w + 1)))) =
      (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryFrameMass X S L F *
        if ∀ i, CoreActualFrameJoint.localFrame w j G F i ∈ Set.Ioo (a i) (b i) then 1 else 0) +
      coreAuxiliaryFrameMissingMass X S L *
        if ∀ i, (0 : ℝ) ∈ Set.Ioo (a i) (b i) then 1 else 0 := by
  have hm : Measurable (fun z : CoreJointFrameLimit.Joint (2 * w + 1) =>
      if ∀ i, CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i) then (1 : ℝ) else 0) := by
    have hs : MeasurableSet {z : CoreJointFrameLimit.Joint (2 * w + 1) |
        ∀ i, CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i)} := by
      have h : MeasurableSet (⋂ i : Fin (2 * w + 1),
          {z : CoreJointFrameLimit.Joint (2 * w + 1) |
            CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i)}) :=
        MeasurableSet.iInter fun i => measurableSet_Ioo.preimage
          (((continuous_apply i).comp CoreJointFrameLimit.continuous_frame).measurable)
      convert h using 1
      ext z
      simp only [mem_setOf_eq, mem_iInter]
    exact Measurable.ite hs measurable_const measurable_const
  simpa only [CoreActualFrameJoint.jointPoint, CoreJointFrameLimit.frame,
    Pi.zero_apply] using
    CoreActualFrameJoint.integral_jointLaw X S L w j G θ O hSy hZ _ hm

end

end PrimeGapNormality.Prime.CoreActualFrameRectangles
