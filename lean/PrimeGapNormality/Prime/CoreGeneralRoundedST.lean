import PrimeGapNormality.Prime.CoreGeneralScaledGapST
import PrimeGapNormality.Prime.CoreGeneralRealCutoff
import PrimeGapNormality.Prime.CoreRoundedPrimeNormality

/-!
# Rounded powers under literal arbitrary-mixture S/T

The deterministic scaling and linear growth are discharged for actual
floor/ceiling combinations. The real-cutoff adapter preserves the actual
complex pattern expectation through the proved floor-pushforward identity.
No model/reference, marked-index, or additional tail assumption is made.
-/

namespace PrimeGapNormality.Prime.CoreGeneralRoundedST
open Filter MeasureTheory Finset CoreCyclic CoreIntegerGapObservable
open CoreRoundedPowerScaling CoreGeneralSequenceST CoreSequenceSTMeanTail
open CoreCalibratedMixtureFiniteSupport CoreGeneralModelReference
open scoped Classical Topology
noncomputable section

theorem rounded_compactScaling {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {exponent : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = exponent ∨ alpha i < exponent)) :
    CoreScaledGapModelReference.CompactScaling (roundedCombination kind alpha b) exponent
      (CoreRoundedModelSubsequence.integerLeadingColumn alpha b exponent) := by
  intro A hA ε hε
  filter_upwards [eventually_roundedCombination_compact_expansion kind alpha b he he1 hA halpha ε hε]
    with G hG
  intro s q hq
  rw [CoreRoundedModelSubsequence.integerLeadingColumn_cast, roundedCombination_cast]
  exact hG s q hq

theorem roundedCombination_weyl
    {I : Type*} [Fintype I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = exponent ∨ alpha i < exponent))
    (hb : leadingColumn alpha b exponent ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion (B ^ k)
      (observableFullSeries B hk r (roundedCombination kind alpha b) (seqGap a)) := by
  have hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1 := fun i =>
    ⟨(halpha i).1, (halpha i).2.elim (fun h => h ▸ he1) (fun h => h.le.trans he1)⟩
  exact CoreGeneralScaledGapST.observableFullSeries_weyl ha hB hk r _
    (CoreRoundedPrimeNormality.roundedLinearConstant_nonneg b)
    (CoreRoundedPrimeNormality.roundedCombination_linear_bound kind alpha b hα)
    he he1 (CoreRoundedModelSubsequence.integerLeadingColumn alpha b exponent)
    (CoreRoundedModelSubsequence.integerLeadingColumn_ne_zero alpha b exponent hb)
    (rounded_compactScaling kind alpha b he he1 halpha) hκ hG hω hsum hcal hS hT

theorem roundedCombination_normal
    {I : Type*} [Fintype I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = exponent ∨ alpha i < exponent))
    (hb : leadingColumn alpha b exponent ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
        (observableFullSeries B hk r (roundedCombination kind alpha b) (seqGap a)) ∧
      PrimeGapNormality.BFree.IsNormal B
        (observableFullSeries B hk r (roundedCombination kind alpha b) (seqGap a)) := by
  have hW := roundedCombination_weyl ha hB hk r kind alpha b he he1 halpha hb
    hκ hG hω hsum hcal hS hT
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  exact ⟨CoreWeylNormality.isNormal_of_weyl hclock hW,
    CoreWeylNormality.isNormal_of_weyl hB (weylCriterion_of_pow hB hk hW)⟩

/-- The scalar model/sequence consumer also accepts an arbitrary probability
on real cutoffs. Its actual floor pushforward supplies all natural weights. -/
theorem scaled_observable_weyl_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1) (b : Fin k → ℤ) (hb : b ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent b)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : CoreGeneralRealCutoff.PatternS a κ G μ)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion (B ^ k) (observableFullSeries B hk r F (seqGap a)) :=
  CoreGeneralScaledGapST.observableFullSeries_weyl ha hB hk r F hC hF he he1 b hb hscale hκ hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRealCutoff.patternS_nat hG hcal hS) hT

theorem roundedCombination_normal_realCutoff
    {I : Type*} [Fintype I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = exponent ∨ alpha i < exponent))
    (hb : leadingColumn alpha b exponent ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : CoreGeneralRealCutoff.PatternS a κ G μ)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
        (observableFullSeries B hk r (roundedCombination kind alpha b) (seqGap a)) ∧
      PrimeGapNormality.BFree.IsNormal B
        (observableFullSeries B hk r (roundedCombination kind alpha b) (seqGap a)) :=
  roundedCombination_normal ha hB hk r kind alpha b he he1 halpha hb hκ hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRealCutoff.patternS_nat hG hcal hS) hT

end
end PrimeGapNormality.Prime.CoreGeneralRoundedST
