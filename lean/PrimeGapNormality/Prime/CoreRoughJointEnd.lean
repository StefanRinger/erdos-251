import PrimeGapNormality.Prime.CoreRoughLocalNormality
import PrimeGapNormality.Prime.CorePrimeLocalJointEnd

/-!
# Actual joint orbit laws of moving-rough local series

This module specializes the general finite-torus consequences of JointWeyl.
The imported prime-named file contains those general measure-theoretic
lemmas; no prime-distribution theorem is used here. The arithmetic supplier
is the literal moving-rough backend. This source remains pending its own
central compilation and end-type/axiom acceptance.
-/

namespace PrimeGapNormality.Prime.CoreRoughJointEnd

open Filter MeasureTheory CoreCyclic CoreJointEquidistribution
open CoreRoughThreshold CoreMovingRoughSequence CoreSequenceSTConsumer
open scoped Topology Classical
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
  (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
  (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
  {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
  (F : I → PeriodicLocal k)
  (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
  (hlin : LinearIndependent ℚ (fun i ↦ normalForm hB hk (F i)))
  (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)

include hκpos hSlope hC hreg hdeg hlin hκ in
/-- Weak convergence of the actual joint orbit to product Haar. -/
theorem empirical_tendsto :
    Tendsto (empirical (fun _ : I ↦ B ^ k)
      (fun i ↦ coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) (F i)))
      atTop (𝓝 (torusVolume I)) :=
  empirical_tendsto_of_jointWeyl
    (CoreRoughLocalNormality.movingRough_jointWeyl
      hκpos hSlope hC hreg hB hk phase F hdeg hlin hκ)

include hκpos hSlope hC hreg hdeg hlin hκ in
/-- Actual averages of every continuous test on the finite torus. -/
theorem continuous_test_tendsto (f : C(Torus I, ℝ)) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, f (fun i ↦
      ((((B ^ k : ℕ) : ℝ) ^ n * coreCyclicFullSeries B hk phase
        (fun q ↦ (seqGap (movingRoughSequence (zPsi Ψ)) q : ℝ)) (F i) : ℝ) :
          AddCircle (1 : ℝ)))) / N) atTop (𝓝 (∫ x : Torus I, f x)) :=
  continuous_test_tendsto_of_jointWeyl
    (CoreRoughLocalNormality.movingRough_jointWeyl
      hκpos hSlope hC hreg hB hk phase F hdeg hlin hκ) f

include hκpos hSlope hC hreg hdeg hlin hκ in
/-- Literal simultaneous fractional-part box frequencies. No independence
of the arithmetic sequence, or of its gaps, is assumed. -/
theorem box_frequency (a b : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hb : ∀ i, b i ≤ 1) (hw : ∀ i, b i < a i + 1) :
    Tendsto (fun N : ℕ ↦ (((Finset.range N).filter (fun n ↦ ∀ i,
      Int.fract (((B ^ k : ℕ) : ℝ) ^ n * coreCyclicFullSeries B hk phase
        (fun q ↦ (seqGap (movingRoughSequence (zPsi Ψ)) q : ℝ)) (F i)) ∈
          Set.Ico (a i) (b i))).card : ℝ) / N)
      atTop (𝓝 (∏ i, (b i - a i))) :=
  box_frequency_of_jointWeyl
    (CoreRoughLocalNormality.movingRough_jointWeyl
      hκpos hSlope hC hreg hB hk phase F hdeg hlin hκ) a b ha hab hb hw

end
end PrimeGapNormality.Prime.CoreRoughJointEnd
