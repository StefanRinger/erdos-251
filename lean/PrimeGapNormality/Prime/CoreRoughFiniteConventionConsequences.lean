import PrimeGapNormality.Prime.CoreRoughFiniteConventionExtensions
import PrimeGapNormality.Prime.CoreJointEquidistribution
import PrimeGapNormality.Prime.CoreSequenceSTDimension

/-!
# Product-Haar and dimension consequences for finite rough conventions

These are direct consumers of the already-proved finite-convention S/T and
joint-Weyl statements.  Eventual range agreement is still the only premise
describing the changed initial convention.  No density, count, growth,
summability, or model hypothesis is added.
-/

namespace PrimeGapNormality.Prime.CoreRoughFiniteConventionConsequences

open Filter Finset MeasureTheory MvPolynomial CoreCyclic
open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSyntheticScale
  CoreSequenceSTConsumer CoreSequenceSTMeanTail
open scoped Topology Classical BoundedContinuousFunction

noncomputable section

section Profile

variable {a : ℕ → ℕ} (ha : StrictMono a)
variable {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
variable (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
variable (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
variable (hrange : ∀ᶠ v : ℕ in atTop,
  (v ∈ Set.range a ↔ IsMovingRough (zPsi Ψ) v))

include ha hκpos hSlope hC hreg hrange

/-- Integer-frequency joint Weyl gives the literal empirical law converging
to product Haar measure for the supplied finite initial convention. -/
theorem joint_empirical_tendsto
    {I : Type*} [Fintype I] [DecidableEq I] {B k d : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    Tendsto
      (CoreJointEquidistribution.empirical (fun _ : I => B ^ k)
        (fun i => coreCyclicFullSeries B hk phase
          (fun n => (seqGap a n : ℝ)) (F i)))
      atTop (𝓝 (CoreJointEquidistribution.torusVolume I)) :=
  CoreJointEquidistribution.empirical_tendsto_of_jointWeyl
    (CoreRoughFiniteConventionExtensions.jointWeyl
      ha hκpos hSlope hC hreg hrange hB hk phase F hdeg hlin hκ)

/-- Explicit continuous-test form of the same product-Haar convergence. -/
theorem joint_continuous_integral_tendsto
    {I : Type*} [Fintype I] [DecidableEq I] {B k d : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (f : CoreJointEquidistribution.Torus I →ᵇ ℝ) :
    Tendsto (fun N => ∫ x, f x ∂(CoreJointEquidistribution.empirical
        (fun _ : I => B ^ k)
        (fun i => coreCyclicFullSeries B hk phase
          (fun n => (seqGap a n : ℝ)) (F i)) N :
          Measure (CoreJointEquidistribution.Torus I)))
      atTop (𝓝 (∫ x, f x ∂(CoreJointEquidistribution.torusVolume I :
        Measure (CoreJointEquidistribution.Torus I)))) := by
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (joint_empirical_tendsto ha hκpos hSlope hC hreg hrange
      hB hk phase F hdeg hlin hκ) f

/-- Exact rational dimension of the literal series span for the supplied
finite initial convention. The effective degree and variable conditions are
unchanged. -/
theorem finrank_seriesSpan
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hH : 0 < H) (hD : 0 < D)
    (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ) :
    Module.finrank ℚ (CoreSequenceSTDimension.seriesSpan a B H D hk phase) =
      1 + k * (H + D - 1).choose (D - 1) := by
  exact CoreSequenceSTDimension.finrank_seriesSpan_of_shapeS
    ha hB hk phase hH hD hκ (by norm_num : (0 : ℝ) < 1)
    (CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope)
    (CoreRoughFiniteConvention.gapTailT ha hκpos hSlope hC hreg hrange)
    (CoreRoughFiniteConvention.sequencePositiveShapeS
      ha hκpos hSlope hC hreg hrange)

end Profile

end
end PrimeGapNormality.Prime.CoreRoughFiniteConventionConsequences
