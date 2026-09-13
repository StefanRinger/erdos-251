import PrimeGapNormality.Prime.CoreScaledGapSTNormality
import PrimeGapNormality.Prime.CoreRoughLocalNormality
import PrimeGapNormality.Prime.CoreRoundedPolynomialNormality

/-!
# Rounded observables on the actual moving-rough sequence

The actual rough Shape S and mean-tail suppliers discharge the concrete
sequence hypotheses of `CoreScaledGapSTNormality`.  Public statements retain
only the paper's explicit slope and weighted-derivative regularity inputs.
Floors and ceilings are again separate through one fixed `RoundKind`.
-/

namespace PrimeGapNormality.Prime.CoreRoundedRoughNormality

open Finset Filter Polynomial CoreCyclic
open CoreRoundedPowerScaling CoreRoundedPolynomialScaling
open CoreIntegerGapObservable CoreRoughThreshold CoreRoughSyntheticScale
open CoreMovingRoughSequence CoreSequenceSTConsumer
open scoped Topology Classical

noncomputable section

private def roughSequence (Ψ : ℝ → ℝ) : ℕ → ℕ :=
  movingRoughSequence (zPsi Ψ)

private def roughModelScale (Ψ : ℝ → ℝ) : ℕ → ℕ :=
  fun X => roughSyntheticScale (zPsi Ψ X)

private theorem roundedCombination_compactScaling
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a)) :
    CoreScaledGapModelReference.CompactScaling
      (roundedCombination kind alpha b) a
      (CoreRoundedModelSubsequence.integerLeadingColumn alpha b a) := by
  intro A hA eps heps
  have hh := eventually_roundedCombination_compact_expansion
    kind alpha b ha ha1 hA halpha eps heps
  filter_upwards [hh] with G hG
  intro s q hq
  rw [CoreRoundedModelSubsequence.integerLeadingColumn_cast]
  simpa only [roundedCombination_cast] using hG s q hq

private theorem roundedCombination_linearBound
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1) :
    ∀ s q, 1 ≤ q → |(roundedCombination kind alpha b s q : ℝ)| ≤
      CoreRoundedPrimeNormality.roundedLinearConstant b * (q : ℝ) :=
  CoreRoundedPrimeNormality.roundedCombination_linear_bound kind alpha b halpha

/-- Actual moving-rough normality for every nonzero maximal-exponent
integer column. -/
theorem movingRough_roundedCombination_isNormal
    {I : Type*} [Fintype I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {exponent : ℝ} (hexp : 0 < exponent) (hexp1 : exponent ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = exponent ∨ alpha i < exponent))
    (hlead : CoreRoundedModelSubsequence.integerLeadingColumn alpha b exponent ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    PrimeGapNormality.BFree.IsNormal B
      (observableFullSeries B hk r (roundedCombination kind alpha b)
        (seqGap (roughSequence Ψ))) := by
  let aSeq := roughSequence Ψ
  let T := roughModelScale Ψ
  have ha : StrictMono aSeq := movingRoughSequence_strictMono
    hSlope.eventually_zPsi_lt
  have hT : Tendsto T atTop atTop := by
    change Tendsto (fun X : ℕ => roughSyntheticScale (zPsi Ψ X)) atTop atTop
    exact CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope
  have hTail : GapTailT aSeq (localTailBase κ) (windowG ∘ T) := by
    change GapTailT (movingRoughSequence (zPsi Ψ)) (localTailBase κ)
      (windowG ∘ fun X : ℕ => roughSyntheticScale (zPsi Ψ X))
    exact CoreRoughLocalNormality.movingRough_gapTailT hκpos hSlope hC hreg
  have hS : SequencePositiveShapeS aSeq T κ 1 := by
    change SequencePositiveShapeS (movingRoughSequence (zPsi Ψ))
      (fun X : ℕ => roughSyntheticScale (zPsi Ψ X)) κ 1
    exact CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
  have halphaLinear : ∀ i, 0 < alpha i ∧ alpha i ≤ 1 := by
    intro i
    exact ⟨(halpha i).1, (halpha i).2.elim (fun h => h ▸ hexp1)
      (fun h => h.le.trans hexp1)⟩
  exact CoreScaledGapSTNormality.observableFullSeries_isNormal_of_shapeS
    ha hB hk r (roundedCombination kind alpha b)
    (CoreRoundedPrimeNormality.roundedLinearConstant_nonneg b)
    (roundedCombination_linearBound kind alpha b halphaLinear)
    hexp hexp1 (CoreRoundedModelSubsequence.integerLeadingColumn alpha b exponent)
    hlead (roundedCombination_compactScaling kind alpha b hexp hexp1 halpha)
    hκ (by norm_num : (0 : ℝ) < 1) hT hTail hS

/-- Literal integer-polynomial rounded series for the moving-rough gaps. -/
def movingRoughRoundedPolynomialSeries
    (Ψ : ℝ → ℝ) (B : ℕ) (P : ℤ[X]) (kind : RoundKind) (alpha : ℝ) : ℝ :=
  ∑' n : ℕ,
    (roundedPolynomialIncrement P kind alpha (seqGap (roughSequence Ψ) n) : ℝ) /
      (B : ℝ) ^ (n + 1)

private theorem observablePolynomial_eq
    (Ψ : ℝ → ℝ) (B : ℕ) (P : ℤ[X]) (kind : RoundKind) (alpha : ℝ) :
    observableFullSeries B (by omega : 0 < (1 : ℕ)) ⟨0, by omega⟩
      (fun _ q => roundedPolynomialIncrement P kind alpha q)
      (seqGap (roughSequence Ψ)) =
        movingRoughRoundedPolynomialSeries Ψ B P kind alpha := by
  unfold observableFullSeries observableSeries observableValue
    movingRoughRoundedPolynomialSeries
  apply tsum_congr
  intro n
  congr 2
  simp only [Nat.zero_add]

/-- Polynomial compositions require only `alpha * degree P ≤ 1`; no false
identification with a single rounded power is used. -/
theorem movingRough_roundedPolynomial_isNormal
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B) (P : ℤ[X]) (kind : RoundKind)
    {alpha : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    PrimeGapNormality.BFree.IsNormal B
      (movingRoughRoundedPolynomialSeries Ψ B P kind alpha) := by
  let aSeq := roughSequence Ψ
  let T := roughModelScale Ψ
  let F : Fin 1 → ℕ → ℤ := fun _ q => roundedPolynomialIncrement P kind alpha q
  let exponent := alpha * (P.natDegree : ℝ)
  let lead : Fin 1 → ℤ := fun _ => P.leadingCoeff
  have ha : StrictMono aSeq := movingRoughSequence_strictMono
    hSlope.eventually_zPsi_lt
  have hT : Tendsto T atTop atTop := by
    change Tendsto (fun X : ℕ => roughSyntheticScale (zPsi Ψ X)) atTop atTop
    exact CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope
  have hTail : GapTailT aSeq (localTailBase κ) (windowG ∘ T) := by
    change GapTailT (movingRoughSequence (zPsi Ψ)) (localTailBase κ)
      (windowG ∘ fun X : ℕ => roughSyntheticScale (zPsi Ψ X))
    exact CoreRoughLocalNormality.movingRough_gapTailT hκpos hSlope hC hreg
  have hS : SequencePositiveShapeS aSeq T κ 1 := by
    change SequencePositiveShapeS (movingRoughSequence (zPsi Ψ))
      (fun X : ℕ => roughSyntheticScale (zPsi Ψ X)) κ 1
    exact CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
  have hexp : 0 < exponent := mul_pos halpha
    (Nat.cast_pos.mpr (zero_lt_one.trans_le hdeg))
  have hlead : lead ≠ 0 := by
    have hP : P ≠ 0 := ne_zero_of_natDegree_gt (zero_lt_one.trans_le hdeg)
    have hleadP := Polynomial.leadingCoeff_ne_zero.mpr hP
    intro hz
    exact hleadP (congrFun hz ⟨0, by omega⟩)
  have hscale : CoreScaledGapModelReference.CompactScaling F exponent lead := by
    simpa only [F, exponent, lead] using
      CoreRoundedPolynomialNormality.roundedPolynomial_compactScaling
        P kind halpha hdeg
  have hlin : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤
      roundedPolynomialLinearConstant P alpha * (q : ℝ) := by
    intro s q hq
    exact roundedPolynomialIncrement_abs_le_linear P kind halpha hdeg
      halphaDeg hq
  have hn := CoreScaledGapSTNormality.observableFullSeries_isNormal_of_shapeS
    ha hB (by omega : 0 < (1 : ℕ)) ⟨0, by omega⟩ F
    (roundedPolynomialLinearConstant_nonneg P) hlin hexp halphaDeg lead hlead
    hscale hκ (by norm_num : (0 : ℝ) < 1) hT hTail hS
  rw [observablePolynomial_eq Ψ B P kind alpha] at hn
  exact hn

end

end PrimeGapNormality.Prime.CoreRoundedRoughNormality
