import PrimeGapNormality.Prime.CoreAuxiliaryFactorialRectangle
import PrimeGapNormality.Prime.CoreActualFrameRectangles
import PrimeGapNormality.Prime.CoreCalibratedMixtureMoments
import PrimeGapNormality.Prime.DescFactMono

/-!
# Actual auxiliary rectangles with factorial averaging

The uniform-frame rectangle estimate is averaged under the original
late-root cardinality law before its falling factorial is discarded.  The
layers `N > M/8` are charged by the genuine first moment, while on the
remaining layers the denominator is at least `7M/8`.  Exact factorial
moments then give the finite one-cutoff bound

`(8 θ / 7)^r ∏ K_i + 8 θ`.

No pointwise replacement of `(N)_r` by `N^r`, and no rectangle or moment
estimate, is assumed.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedFactorialRectangle

open Finset
open scoped Classical BigOperators

noncomputable section

set_option maxHeartbeats 1000000

private theorem cardinalityLayer_nonneg
    {A : Finset ℕ} {μ : Finset ℕ → ℝ}
    (hμ : CardinalitySymmetricMass A μ) (n : ℕ) :
    0 ≤ cardinalityLayer A μ n := by
  unfold cardinalityLayer
  exact sum_nonneg fun U hU ↦ hμ.1 U (mem_filter.mp hU).1

/-- Summing a scalar function of the cardinality layers is the same as
summing it under the original subset law. -/
private theorem sum_cardinalityLayers_apply
    (A : Finset ℕ) (μ : Finset ℕ → ℝ) (f : ℕ → ℝ) :
    (∑ n ∈ range (A.card + 1), cardinalityLayer A μ n * f n) =
      ∑ U ∈ A.powerset, μ U * f U.card := by
  unfold cardinalityLayer
  simp_rw [sum_mul]
  have hfilter (n : ℕ) :
      (∑ U ∈ A.powerset.filter (fun U ↦ U.card = n), μ U * f n) =
        ∑ U ∈ A.powerset,
          if U.card = n then μ U * f n else 0 := by
    rw [← Finset.sum_filter]
  simp_rw [hfilter]
  rw [sum_comm]
  apply sum_congr rfl
  intro U hU
  have hcard : U.card ∈ range (A.card + 1) := by
    apply mem_range.mpr
    have hsub := mem_powerset.mp hU
    have hc := Finset.card_le_card hsub
    omega
  rw [sum_eq_single U.card]
  · rw [if_pos rfl]
  · intro n hn hne
    rw [if_neg (Ne.symm hne)]
  · exact fun hnot ↦ (hnot hcard).elim

private theorem auxFrame_rectangleIndicator_nonneg
    (A : Finset ℕ) (m : ℕ) (J : Finset ℕ)
    (I : ℕ → Set ℝ) :
    0 ≤ auxFrame_uniformMean A m
      (fun U ↦ if ∀ j ∈ J, (subsetGap U j : ℝ) ∈ I j then 1 else 0) :=
  auxFrame_uniformMean_nonneg fun U ↦ by split_ifs <;> norm_num

private theorem auxFrame_rectangleIndicator_le_one
    (A : Finset ℕ) (m : ℕ) (J : Finset ℕ)
    (I : ℕ → Set ℝ) (hm : m ≤ A.card) :
    auxFrame_uniformMean A m
      (fun U ↦ if ∀ j ∈ J, (subsetGap U j : ℝ) ∈ I j then 1 else 0) ≤ 1 := by
  have hchoose : (0 : ℝ) < A.card.choose m :=
    Nat.cast_pos.mpr (Nat.choose_pos hm)
  unfold auxFrame_uniformMean
  apply (div_le_one hchoose).2
  calc
    (∑ U ∈ A.powersetCard m,
        if ∀ j ∈ J, (subsetGap U j : ℝ) ∈ I j then (1 : ℝ) else 0) ≤
        ∑ _U ∈ A.powersetCard m, (1 : ℝ) := by
      apply sum_le_sum
      intro U hU
      split_ifs <;> norm_num
    _ = (A.card.choose m : ℝ) := by
      rw [sum_const, card_powersetCard, nsmul_eq_mul, mul_one]

/-! ## Exact factorial moment of the original cardinality layers -/

/-- The original late-root falling-factorial moment is bounded by
`(M θ)^r`. -/
theorem lateRootLayer_descFactorial_moment_le
    (S y : ℕ) (σ : ResidueChoice S) (hS : 2 ≤ S) (hSy : S ≤ y)
    (r : ℕ) (hr : r ≤ (presieveSurvivors S σ).card) :
    (∑ n ∈ range ((presieveSurvivors S σ).card + 1),
        cardinalityLayer (presieveSurvivors S σ)
            (lateRootLaw S y (presieveSurvivors S σ)) n *
          (n.descFactorial r : ℝ)) ≤
      (((presieveSurvivors S σ).card : ℝ) * lateRetention S y) ^ r := by
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  let M := A.card
  let θ := lateRetention S y
  have hA : A ⊆ offsetWindow S := by
    simpa only [A, offsetWindow] using corePresieveSurvivors_subset_Icc S σ
  have hMS : M ≤ S := by
    have hh := card_le_card hA
    simpa only [M, offsetWindow, Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hMom : ExactCountMoments S y A μ := by
    simpa only [A, μ] using corePresieveLaw_exactCountMoments S y σ hSy
  have hθ0 : 0 ≤ θ := by
    dsimp only [θ]
    exact (rootedEulerProdNat_pos hS).le
  have hchoose := hMom.2.2.1 r (by simpa only [M, A] using hr)
  have hfactor := CoreCalibratedMixtureMoments.lateInclusionFactor_le_retention_pow
    (y := y) hS (hr.trans hMS)
  rw [sum_cardinalityLayers_apply]
  have hdesc :
      (∑ U ∈ A.powerset, μ U * (U.card.descFactorial r : ℝ)) =
        (r.factorial : ℝ) *
          ∑ U ∈ A.powerset, (Nat.choose U.card r : ℝ) * μ U := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro U hU
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    ring
  rw [hdesc, hchoose]
  have hfac0 : 0 ≤ (r.factorial : ℝ) * (Nat.choose M r : ℝ) := by positivity
  calc
    (r.factorial : ℝ) *
        ((Nat.choose M r : ℝ) * lateInclusionFactor S y r) =
        ((r.factorial : ℝ) * (Nat.choose M r : ℝ)) *
          lateInclusionFactor S y r := by ring
    _ ≤ ((r.factorial : ℝ) * (Nat.choose M r : ℝ)) * θ ^ r :=
      mul_le_mul_of_nonneg_left hfactor hfac0
    _ = (M.descFactorial r : ℝ) * θ ^ r := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    _ ≤ (M : ℝ) ^ r * θ ^ r := by
      have hdescPow : (M.descFactorial r : ℝ) ≤ ((M ^ r : ℕ) : ℝ) :=
        Nat.cast_le.mpr (Nat.descFactorial_le_pow M r)
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Nat.cast_pow] using hdescPow) (pow_nonneg hθ0 r)
    _ = (((M : ℝ) * θ) ^ r) := by rw [mul_pow]

/-! ## One exposed-presieve fibre -/

/-- Actual original-cardinality rectangle bound on one exposed presieve
fibre.  The high-count term is charged by the exact first moment. -/
theorem presieve_factorial_rectangle_le
    (S y L : ℕ) (σ : ResidueChoice S) (J : Finset ℕ)
    (I : ℕ → Set ℝ) (K : ℕ → ℕ)
    (hS : 2 ≤ S) (hSy : S ≤ y) (hL : 1 ≤ L)
    (hJ : ∀ j ∈ J, j + 1 < L)
    (hcap : ∀ j ∈ J, ∀ a : ℝ,
      (CoreUniformGapRectangles.translatedCandidates
        (presieveSurvivors S σ) (I j) a).card ≤ K j) :
    (∑ n ∈ Icc L (presieveSurvivors S σ).card,
      cardinalityLayer (presieveSurvivors S σ)
          (lateRootLaw S y (presieveSurvivors S σ)) n *
        auxFrame_uniformMean (presieveSurvivors S σ) (n - 1)
          (fun U ↦ if ∀ j ∈ J, (subsetGap U j : ℝ) ∈ I j then 1 else 0)) ≤
      ((8 * lateRetention S y / 7) ^ J.card) *
          ∏ j ∈ J, (K j : ℝ) +
        8 * lateRetention S y := by
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  let M := A.card
  let θ := lateRetention S y
  let test : Finset ℕ → ℝ := fun U ↦
    if ∀ j ∈ J, (subsetGap U j : ℝ) ∈ I j then 1 else 0
  let idx : Finset ℕ := Finset.Icc L M
  let low : Finset ℕ := idx.filter (fun n : ℕ ↦ (n : ℝ) ≤ (M : ℝ) / 8)
  let high : Finset ℕ := idx.filter (fun n : ℕ ↦ (M : ℝ) / 8 < (n : ℝ))
  have hμ : CardinalitySymmetricMass A μ := by
    simpa only [A, μ] using corePresieveLaw_cardinalitySymmetric S y σ hSy
  have hp0 : ∀ n, 0 ≤ cardinalityLayer A μ n :=
    cardinalityLayer_nonneg hμ
  have hθ : 0 < θ := by
    dsimp only [θ]
    exact rootedEulerProdNat_pos hS
  have hprod0 : 0 ≤ ∏ j ∈ J, (K j : ℝ) :=
    prod_nonneg fun j hj ↦ Nat.cast_nonneg _
  by_cases hM : M = 0
  · have hidx : idx = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hnI := mem_Icc.mp hn
      dsimp only [M] at hM
      omega
    rw [show Icc L (presieveSurvivors S σ).card = idx by rfl, hidx, sum_empty]
    exact _root_.add_nonneg
      (mul_nonneg (pow_nonneg (by positivity) _) hprod0)
      (mul_nonneg (by norm_num) hθ.le)
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
  have hsplit :
      (∑ n ∈ idx, cardinalityLayer A μ n *
          auxFrame_uniformMean A (n - 1) test) =
        (∑ n ∈ low, cardinalityLayer A μ n *
          auxFrame_uniformMean A (n - 1) test) +
        (∑ n ∈ high, cardinalityLayer A μ n *
          auxFrame_uniformMean A (n - 1) test) := by
    have hh := sum_filter_add_sum_filter_not idx
      (fun n : ℕ ↦ (n : ℝ) ≤ (M : ℝ) / 8)
      (fun n ↦ cardinalityLayer A μ n *
        auxFrame_uniformMean A (n - 1) test)
    have hnot : idx.filter (fun n : ℕ ↦ ¬(n : ℝ) ≤ (M : ℝ) / 8) = high := by
      ext n
      simp only [high, mem_filter, not_le]
    rw [hnot] at hh
    simpa only [low] using hh.symm
  have hlowPoint : ∀ n ∈ low,
      auxFrame_uniformMean A (n - 1) test ≤
        (((n - 1).descFactorial J.card : ℝ) /
          (((7 : ℝ) / 8) * (M : ℝ)) ^ J.card) *
            ∏ j ∈ J, (K j : ℝ) := by
    intro n hn
    have hnI := mem_Icc.mp (mem_filter.mp hn).1
    have hnlow := (mem_filter.mp hn).2
    have hJm : ∀ j ∈ J, j < n - 1 := by
      intro j hj
      have := hJ j hj
      omega
    have hden := CoreAuxiliaryFactorialRectangle.denominator_floor_of_sparse_layer
      (M := M) (m := n - 1) (ε := (1 / 8 : ℝ))
      (by norm_num) (Nat.pos_of_ne_zero hM) (by
        have hpred : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) :=
          Nat.cast_le.mpr (Nat.sub_le n 1)
        nlinarith)
    have hseven : (1 : ℝ) - 1 / 8 = 7 / 8 := by norm_num
    simpa only [A, M, test, hseven] using
      CoreAuxiliaryFactorialRectangle.uniformMean_rectangle_le_descFactorial
        A (n - 1) J I K ((Nat.sub_le n 1).trans hnI.2) hJm hcap
        hden.1 hden.2
  have hlowBound :
      (∑ n ∈ low, cardinalityLayer A μ n *
          auxFrame_uniformMean A (n - 1) test) ≤
        ((8 * θ / 7) ^ J.card) * ∏ j ∈ J, (K j : ℝ) := by
    have hpoint := sum_le_sum fun n hn ↦
      mul_le_mul_of_nonneg_left (hlowPoint n hn) (hp0 n)
    let R : ℝ := ((7 : ℝ) / 8) * (M : ℝ)
    let Q : ℝ := ∏ j ∈ J, (K j : ℝ)
    have hR : 0 < R := by dsimp only [R]; positivity
    have hsumDesc :
        (∑ n ∈ low, cardinalityLayer A μ n *
          ((n - 1).descFactorial J.card : ℝ)) ≤
          ((M : ℝ) * θ) ^ J.card := by
      by_cases hLM : L ≤ M
      · have hcardJ : J.card ≤ M := by
          have hsubJ : J ⊆ range M := by
            intro j hj
            exact mem_range.mpr (by
              have hjL := hJ j hj
              omega)
          simpa only [card_range] using card_le_card hsubJ
        have hsub : low ⊆ range (M + 1) := by
          intro n hn
          have hnM := (mem_Icc.mp (mem_filter.mp hn).1).2
          exact mem_range.mpr (by omega)
        have hmono :
            (∑ n ∈ low, cardinalityLayer A μ n *
                ((n - 1).descFactorial J.card : ℝ)) ≤
              ∑ n ∈ range (M + 1), cardinalityLayer A μ n *
                (n.descFactorial J.card : ℝ) := by
          calc
            _ ≤ ∑ n ∈ low, cardinalityLayer A μ n *
                (n.descFactorial J.card : ℝ) := by
              exact sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_left
                (descFact_pred_le_real n J.card) (hp0 n)
            _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
              (fun n hn _ ↦ mul_nonneg (hp0 n) (Nat.cast_nonneg _))
        exact hmono.trans (lateRootLayer_descFactorial_moment_le
          S y σ hS hSy J.card (by simpa only [M, A] using hcardJ))
      · have hidxEmpty : idx = ∅ := by
          simp only [idx, Icc_eq_empty_iff]
          omega
        have hlowEmpty : low = ∅ := by
          simp only [low, hidxEmpty, filter_empty]
        rw [hlowEmpty, sum_empty]
        exact pow_nonneg (mul_nonneg hMr.le hθ.le) J.card
    have hsumScaled := mul_le_mul_of_nonneg_left hsumDesc
      (div_nonneg hprod0 (pow_nonneg hR.le J.card))
    have hsumScaled' :
        (Q / R ^ J.card) *
            (∑ n ∈ low, cardinalityLayer A μ n *
              ((n - 1).descFactorial J.card : ℝ)) ≤
          (Q / R ^ J.card) * (((M : ℝ) * θ) ^ J.card) := by
      simpa only [Q] using hsumScaled
    have hfactor :
        (∑ n ∈ low, cardinalityLayer A μ n *
            ((((n - 1).descFactorial J.card : ℝ) / R ^ J.card) * Q)) =
          (Q / R ^ J.card) *
            ∑ n ∈ low, cardinalityLayer A μ n *
              ((n - 1).descFactorial J.card : ℝ) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
    exact hpoint.trans (by
      rw [show ((7 : ℝ) / 8) * (M : ℝ) = R by rfl]
      change (∑ n ∈ low, cardinalityLayer A μ n *
          ((((n - 1).descFactorial J.card : ℝ) / R ^ J.card) * Q)) ≤ _
      rw [hfactor]
      have hratio : ((M : ℝ) * θ) / R = 8 * θ / 7 := by
        dsimp only [R]
        field_simp [hMr.ne'] <;> ring
      exact hsumScaled'.trans_eq (by
        calc
          (Q / R ^ J.card) * (((M : ℝ) * θ) ^ J.card) =
              ((((M : ℝ) * θ) ^ J.card) / R ^ J.card) * Q := by ring
          _ = ((((M : ℝ) * θ) / R) ^ J.card) * Q := by rw [div_pow]
          _ = ((8 * θ / 7) ^ J.card) * Q := by rw [hratio]))
  have hhighBound :
      (∑ n ∈ high, cardinalityLayer A μ n *
          auxFrame_uniformMean A (n - 1) test) ≤ 8 * θ := by
    have hpoint : ∀ n ∈ high,
        cardinalityLayer A μ n * auxFrame_uniformMean A (n - 1) test ≤
          (8 / (M : ℝ)) *
            ((n : ℝ) * cardinalityLayer A μ n) := by
      intro n hn
      have hnI := mem_Icc.mp (mem_filter.mp hn).1
      have hmean := auxFrame_rectangleIndicator_le_one A (n - 1) J I
        ((Nat.sub_le n 1).trans hnI.2)
      have hfirst := mul_le_mul_of_nonneg_left hmean (hp0 n)
      have hnhi := (mem_filter.mp hn).2
      have hscale : 1 ≤ (8 / (M : ℝ)) * (n : ℝ) := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hMr).2
        nlinarith
      have hscaled := mul_le_mul_of_nonneg_right hscale (hp0 n)
      nlinarith
    have hsum := sum_le_sum hpoint
    rw [← Finset.mul_sum] at hsum
    have hsub : high ⊆ range (M + 1) := by
      intro n hn
      have hnM := (mem_Icc.mp (mem_filter.mp hn).1).2
      exact mem_range.mpr (by omega)
    have hfull :
        (∑ n ∈ high, (n : ℝ) * cardinalityLayer A μ n) ≤
          ∑ n ∈ range (M + 1),
            cardinalityLayer A μ n * (n : ℝ) := by
      calc
        _ = ∑ n ∈ high, cardinalityLayer A μ n * (n : ℝ) := by
          apply sum_congr rfl
          intro n hn
          ring
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
          (fun n hn _ ↦ mul_nonneg (hp0 n) (Nat.cast_nonneg _))
    have hmoment :
        (∑ n ∈ range (M + 1), cardinalityLayer A μ n * (n : ℝ)) =
          (M : ℝ) * θ := by
      rw [sum_cardinalityLayers_apply]
      simpa only [A, μ, M, θ, mul_comm] using
        (corePresieveLaw_exactCountMoments S y σ hSy).1
    have hscale := mul_le_mul_of_nonneg_left (hfull.trans_eq hmoment)
      (show (0 : ℝ) ≤ 8 / (M : ℝ) from div_nonneg (by norm_num) hMr.le)
    exact hsum.trans (hscale.trans_eq (by field_simp [hMr.ne'] <;> ring))
  change (∑ n ∈ idx, cardinalityLayer A μ n *
    auxFrame_uniformMean A (n - 1) test) ≤ _
  rw [hsplit]
  exact _root_.add_le_add hlowBound hhighBound

/-! ## The actual one-cutoff auxiliary-frame mass -/

/-- Averaging over the original uniform early residue choice preserves the
same one-cutoff rectangle bound. -/
theorem auxiliaryLayer_factorial_rectangle_le
    (S y L : ℕ) (J : Finset ℕ) (I : ℕ → Set ℝ) (K : ℕ → ℕ)
    (hS : 2 ≤ S) (hSy : S ≤ y) (hL : 1 ≤ L)
    (hJ : ∀ j ∈ J, j + 1 < L)
    (hcap : ∀ σ : ResidueChoice S, ∀ j ∈ J, ∀ a : ℝ,
      (CoreUniformGapRectangles.translatedCandidates
        (presieveSurvivors S σ) (I j) a).card ≤ K j) :
    (∑ F ∈ (offsetWindow S).powerset,
      coreAuxiliaryLayerFrameMass S y L F *
        (if ∀ j ∈ J, (subsetGap F j : ℝ) ∈ I j then 1 else 0)) ≤
      ((8 * lateRetention S y / 7) ^ J.card) *
          ∏ j ∈ J, (K j : ℝ) +
        8 * lateRetention S y := by
  rw [CoreActualFrameRectangles.layer_expectation]
  have hcard : (0 : ℝ) < Fintype.card (ResidueChoice S) := by
    exact_mod_cast (residueChoice_card_pos S)
  apply (div_le_iff₀ hcard).2
  calc
    (∑ σ : ResidueChoice S,
      ∑ n ∈ Icc L (presieveSurvivors S σ).card,
        cardinalityLayer (presieveSurvivors S σ)
          (lateRootLaw S y (presieveSurvivors S σ)) n *
            auxFrame_uniformMean (presieveSurvivors S σ) (n - 1)
              (fun F ↦ if ∀ j ∈ J, (subsetGap F j : ℝ) ∈ I j then 1 else 0)) ≤
      ∑ _σ : ResidueChoice S,
        (((8 * lateRetention S y / 7) ^ J.card) *
            ∏ j ∈ J, (K j : ℝ) + 8 * lateRetention S y) := by
      exact sum_le_sum fun σ _ ↦
        presieve_factorial_rectangle_le S y L σ J I K
          hS hSy hL hJ (hcap σ)
    _ = ((((8 * lateRetention S y / 7) ^ J.card) *
          ∏ j ∈ J, (K j : ℝ) + 8 * lateRetention S y) *
        (Fintype.card (ResidueChoice S) : ℝ)) := by
      rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

end

end PrimeGapNormality.Prime.CoreCalibratedFactorialRectangle
