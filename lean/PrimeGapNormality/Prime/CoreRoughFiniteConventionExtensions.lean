import PrimeGapNormality.Prime.CoreRoughAnyRhoTail
import PrimeGapNormality.Prime.CoreRoughFiniteConvention
import PrimeGapNormality.Prime.CoreSequenceSTRelations

/-!
# Every-base tails and finite families for arbitrary finite rough conventions

All conclusions concern the supplied increasing sequence itself. Eventual
range agreement is the literal finite-convention hypothesis, not a model or
distribution assumption. Physical windows retain their exact denominator.
The every-rho result uses the original Euler scale and the original slope
budget; no rho-dependent strengthening of that budget is required.

Source candidate: compilation and the companion axiom audit are scheduled
centrally, not asserted here.
-/

namespace PrimeGapNormality.Prime.CoreRoughFiniteConventionExtensions

open Filter Finset MvPolynomial CoreCyclic
open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSyntheticScale
  CoreSequenceSTConsumer CoreSequenceSTMeanTail CoreSequenceSubexponentialGrowth
open scoped Topology Classical

noncomputable section

/-- Exact physical-root alignment transfers the actual mean tail at every
fixed rho, with the unchanged original slope budget. -/
theorem meanGapTailT_any_rho
    {a : ℕ → ℕ} (ha : StrictMono a)
    {Ψ dΨ : ℝ → ℝ} {A C rho : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v))
    (hrho : 1 < rho) :
    MeanGapTailT a rho (fun X => roughGapScale (zPsi Ψ X)) := by
  have hb := movingRoughSequence_strictMono hSlope.eventually_zPsi_lt
  have hsame := CoreRoughFiniteConvention.eventually_movingRough_range_iff hSlope hrange
  exact (CoreSequenceTailAgreement.meanGapTailT_iff_of_range_agreement
    hb ha hsame rho (fun X => roughGapScale (zPsi Ψ X))).mp
      (CoreRoughAnyRhoTail.movingRough_meanGapTailT_roughScale hSlope hC hreg hrho)

section Profile

variable {a : ℕ → ℕ} (ha : StrictMono a)
variable {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
variable (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
variable (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
variable (hrange : ∀ᶠ v : ℕ in atTop,
  (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v))

include ha hκpos hSlope hC hreg hrange

private theorem windowCount : WindowCountToInfinity a := by
  exact CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
    ha hκpos (by norm_num : (0 : ℝ) < 1)
    (CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope)
    (CoreRoughFiniteConvention.sequencePositiveShapeS ha hκpos hSlope hC hreg hrange)
    (CoreRoughFiniteConvention.gapTailT ha hκpos hSlope hC hreg hrange)

/-- Geometric summability of the actual changed enumeration is a conclusion,
not a premise of the family wrappers. -/
theorem position_summable {rho : ℝ} (hrho : 1 < rho) :
    Summable (fun n : ℕ => (a n : ℝ) / rho ^ n) :=
  sequence_div_pow_summable ha (windowCount ha hκpos hSlope hC hreg hrange) hrho

/-- Every fixed local polynomial series converges absolutely, without a
degree-budget restriction on this convergence statement. -/
theorem localSeries_summable
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) :
    Summable (fun n : ℕ =>
      localValue hk phase (fun j => (seqGap a j : ℝ)) F n /
        (B : ℝ) ^ (n + 1)) := by
  have hg := sequenceGap_hasSubexponentialGrowth ha
    (windowCount ha hκpos hSlope hC hreg hrange)
  simpa only [Nat.zero_add] using
    localSeries_summable_of_subexponential hB hk phase
      (fun j => (seqGap a j : ℝ)) hg F 0

/-- Literal finite rational linearity of the actual convergent series. -/
theorem fullSeries_sum_smul
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k) (q : I → ℚ) :
    coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ))
        (∑ i, q i • F i) =
      ∑ i, (q i : ℝ) * coreCyclicFullSeries B hk phase
        (fun n => (seqGap a n : ℝ)) (F i) := by
  exact CoreSequenceSTRelations.fullSeries_sum_smul_of_shapeS
    ha hB hk phase F q (by norm_num : (0 : ℝ) < 1)
    (CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope)
    (CoreRoughFiniteConvention.gapTailT ha hκpos hSlope hC hreg hrange)
    (CoreRoughFiniteConvention.sequencePositiveShapeS ha hκpos hSlope hC hreg hrange)

/-- All rational relations, including the rational constant, are detected by
the actual normal forms at one common effective-degree budget. -/
theorem rational_relation_iff
    {I : Type*} [Fintype I] {B k d : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) (q : I → ℚ) :
    (∃ t : ℚ, (∑ i, (q i : ℝ) * coreCyclicFullSeries B hk phase
      (fun n => (seqGap a n : ℝ)) (F i)) = (t : ℝ)) ↔
      (∑ i, q i • normalForm hB hk (F i)) = 0 := by
  exact CoreSequenceSTRelations.rational_relation_iff_of_shapeS
    ha hB hk phase F hdeg hκ (by norm_num : (0 : ℝ) < 1)
    (CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope)
    (CoreRoughFiniteConvention.gapTailT ha hκpos hSlope hC hreg hrange)
    (CoreRoughFiniteConvention.sequencePositiveShapeS ha hκpos hSlope hC hreg hrange) q

/-- Every nonzero rational normal-form combination has the literal common
clock Weyl property for the supplied finite convention. -/
theorem combination_weyl
    {I : Type*} [Fintype I] {B k d : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (q : I → ℚ) (hq : (∑ i, q i • normalForm hB hk (F i)) ≠ 0) :
    weylCriterion (B ^ k)
      (∑ i, (q i : ℝ) * coreCyclicFullSeries B hk phase
        (fun n => (seqGap a n : ℝ)) (F i)) := by
  exact CoreSequenceSTRelations.combination_weyl_clock_of_shapeS
    ha hB hk phase F hdeg hκ (by norm_num : (0 : ℝ) < 1)
    (CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope)
    (CoreRoughFiniteConvention.gapTailT ha hκpos hSlope hC hreg hrange)
    (CoreRoughFiniteConvention.sequencePositiveShapeS ha hκpos hSlope hC hreg hrange) q hq

/-- Genuine joint Weyl cancellation, not an inference from separate scalar
normality. The empty finite family is allowed. -/
theorem jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I] {B k d : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    JointWeyl (fun _ : I => B ^ k)
      (fun i => coreCyclicFullSeries B hk phase
        (fun n => (seqGap a n : ℝ)) (F i)) := by
  exact CoreSequenceSTRelations.jointWeyl_of_independent_normalForms_of_shapeS
    ha hB hk phase F hdeg hlin hκ (by norm_num : (0 : ℝ) < 1)
    (CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope)
    (CoreRoughFiniteConvention.gapTailT ha hκpos hSlope hC hreg hrange)
    (CoreRoughFiniteConvention.sequencePositiveShapeS ha hκpos hSlope hC hreg hrange)

/-- Rational linear independence of one and the actual family series. -/
theorem linearIndependent_one
    {I : Type*} [Fintype I] [DecidableEq I] {B k d : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    LinearIndependent ℚ (fun i : Option I => match i with
      | none => (1 : ℝ)
      | some i => coreCyclicFullSeries B hk phase
          (fun n => (seqGap a n : ℝ)) (F i)) := by
  exact CoreSequenceSTRelations.linearIndependent_one_of_independent_normalForms_of_shapeS
    ha hB hk phase F hdeg hlin hκ (by norm_num : (0 : ℝ) < 1)
    (CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope)
    (CoreRoughFiniteConvention.gapTailT ha hκpos hSlope hC hreg hrange)
    (CoreRoughFiniteConvention.sequencePositiveShapeS ha hκpos hSlope hC hreg hrange)

end Profile

/-- Complete summable TailT at the original Euler scale for every fixed
rho. Reparametrizing A as 1000000*(A/1000000) derives the convergence
supplier without strengthening the supplied slope hypothesis. -/
theorem gapTailT_any_rho
    {a : ℕ → ℕ} (ha : StrictMono a)
    {Ψ dΨ : ℝ → ℝ} {A C rho : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v))
    (hrho : 1 < rho) :
    GapTailT a rho (fun X => roughGapScale (zPsi Ψ X)) := by
  have hκ : 0 < A / 1000000 := div_pos hSlope.1 (by norm_num)
  have hbudget : HasSlopeBudget Ψ (1000000 * (A / 1000000)) := by
    rw [show (1000000 : ℝ) * (A / 1000000) = A by ring]
    exact hSlope
  have hsum := position_summable ha hκ hbudget hC hreg hrange hrho
  have hG := CoreRoughScaleLimits.tendsto_roughGapScale_atTop.comp
    hSlope.tendsto_zPsi_atTop
  obtain ⟨K, hK, hmean⟩ := meanGapTailT_any_rho ha hSlope hC hreg hrange hrho
  exact ⟨hrho, hG, hsum, K, hK, hmean⟩

end

end PrimeGapNormality.Prime.CoreRoughFiniteConventionExtensions
