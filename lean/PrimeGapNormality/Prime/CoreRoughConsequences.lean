import PrimeGapNormality.Prime.CoreRoughConstants
import PrimeGapNormality.Prime.CoreRoughDimensionEnd
import PrimeGapNormality.Prime.CoreRoundedRoughInfiniteFamily
import PrimeGapNormality.Prime.CoreRoundedRoughPolynomial
import PrimeGapNormality.Prime.CoreCommonPeriodEnd

/-! Literal composition of the remaining V1 rough conclusions with the
single displayed universal constant.  This leaf has no arithmetic model,
shape, tail, or moment conclusion among its hypotheses. -/
namespace PrimeGapNormality.Prime.CoreRoughConsequences
open Finset Filter Polynomial CoreCyclic CoreMovingRoughSequence
  CoreRoughThreshold CoreRoughConstants CoreRoundedPowerScaling
  CoreRoundedRoughFamily CoreRoundedRoughInfiniteFamily CoreRoundedRoughPolynomial
open scoped Topology Classical
noncomputable section

theorem movingRough_rational_relation_iff
    {I : Type*} [Fintype I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) (q : I → ℚ) :
    (∃ r : ℚ, (∑ i, (q i : ℝ) *
      coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) (F i)) =
          (r : ℝ)) ↔
      (∑ i, q i • normalForm hB hk (F i)) = 0 := by
  exact CoreRoughLocalNormality.movingRough_rational_relation_iff hκpos (paperSlope_to_verified hκpos hSlope).1 hC hreg hB hk phase F hdeg hκ q

theorem movingRough_jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i ↦ normalForm hB hk (F i)))
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    JointWeyl (fun _ : I ↦ B ^ k)
      (fun i ↦ coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) (F i)) := by
  exact CoreRoughLocalNormality.movingRough_jointWeyl hκpos (paperSlope_to_verified hκpos hSlope).1 hC hreg hB hk phase F hdeg hlin hκ

theorem movingRough_linearIndependent_one
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i ↦ normalForm hB hk (F i)))
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    LinearIndependent ℚ (fun i : Option I ↦ match i with
      | none => (1 : ℝ)
      | some i => coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) (F i)) := by
  exact CoreRoughLocalNormality.movingRough_linearIndependent_one hκpos (paperSlope_to_verified hκpos hSlope).1 hC hreg hB hk phase F hdeg hlin hκ

theorem finrank_seriesSpan
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hH : 0 < H) (hD : 0 < D)
    (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ) :
    Module.finrank ℚ (CoreSequenceSTDimension.seriesSpan
      (movingRoughSequence (zPsi Ψ)) B H D hk phase) =
        1 + k * (H + D - 1).choose (D - 1) := by
  exact CoreRoughDimensionEnd.finrank_seriesSpan hκpos (paperSlope_to_verified hκpos hSlope).1 hC hreg hB hk phase hH hD hκ

theorem movingRoughRoundedResidue_jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    JointWeyl (fun _ : Fin k × I ↦ B ^ k)
      (movingRoughRoundedResidueSeries Ψ B hk r kind alpha) := by
  have hκpos : 0 < κ := (mul_pos_iff_of_pos_left paperConstant_pos).mp hSlope.1
  exact CoreRoundedRoughFamily.movingRoughRoundedResidue_jointWeyl (paperSlope_to_verified hκpos hSlope).1 hC hreg hB hk r kind alpha halpha halphaInj hκ

theorem movingRoughRoundedResidue_rationalCombination_isNormal_clock
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (q : Fin k × I → ℚ) (hq : ∃ i, q i ≠ 0) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (∑ i, (q i : ℝ) *
        movingRoughRoundedResidueSeries Ψ B hk r kind alpha i) := by
  have hκpos : 0 < κ := (mul_pos_iff_of_pos_left paperConstant_pos).mp hSlope.1
  exact CoreRoundedRoughFamily.movingRoughRoundedResidue_rationalCombination_isNormal_clock (paperSlope_to_verified hκpos hSlope).1 hC hreg hB hk r kind alpha halpha halphaInj hκ q hq

theorem one_movingRoughRoundedInfiniteSeries_linearIndependent
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    LinearIndependent ℚ
      (fun x : Option (Fin k × Exponent) ↦ match x with
        | none => (1 : ℝ)
        | some p => movingRoughRoundedInfiniteSeries Ψ B hk r kind p) := by
  have hκpos : 0 < κ := (mul_pos_iff_of_pos_left paperConstant_pos).mp hSlope.1
  exact CoreRoundedRoughInfiniteFamily.one_movingRoughRoundedInfiniteSeries_linearIndependent (paperSlope_to_verified hκpos hSlope).1 hC hreg hB hk r kind hκ

theorem movingRough_roundedRatPolynomial_isNormal
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B) (P : ℚ[X]) (kind : RoundKind)
    {alpha : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    PrimeGapNormality.BFree.IsNormal B
      (movingRoughRoundedRatPolynomialSeries Ψ B P kind alpha) := by
  exact CoreRoundedRoughPolynomial.movingRough_roundedRatPolynomial_isNormal hκpos (paperSlope_to_verified hκpos hSlope).1 hC hreg hB P kind halpha hdeg halphaDeg hκ

theorem rational_relation_iff_common_period
    {I : Type*} [Fintype I] {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B l d : ℕ} (hB : 2 ≤ B) {k : I → ℕ} (hk : ∀ i, 0 < k i)
    (hl : 0 < l) (hkl : ∀ i, k i ∣ l) (F : ∀ i, PeriodicLocal (k i))
    (hdeg : ∀ i, topDegree (normalForm hB (hk i) (F i)) ≤ d)
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) (q : I → ℚ) :
    (∃ z : ℚ, (∑ i, (q i : ℝ) * coreCyclicFullSeries B (hk i) ⟨0, hk i⟩
      (fun n => (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) (F i)) = (z : ℝ)) ↔
      (∑ i, q i • CorePeriodRefinement.repeatTuple (l := l) (hk i)
        (normalForm hB (hk i) (F i))) = 0 := by
  have hgdeg : ∀ i, topDegree (normalForm hB hl (CoreCommonPeriodEnd.family hk l F i)) ≤ d := by
    intro i
    rw [CoreCommonPeriodEnd.family_effective_degree hB hk hl hkl F i]
    exact hdeg i
  have hnf (i : I) : normalForm hB hl (CoreCommonPeriodEnd.family hk l F i) =
      CorePeriodRefinement.repeatTuple (l := l) (hk i) (normalForm hB (hk i) (F i)) :=
    CorePeriodRefinement.repeat_normalForm hB (hk i) hl (hkl i) (F i)
  have hh := movingRough_rational_relation_iff hκpos hSlope hC hreg hB hl ⟨0, hl⟩
    (CoreCommonPeriodEnd.family hk l F) hgdeg hκ q
  simpa only [CoreCommonPeriodEnd.family_series B hk hl hkl F, hnf] using hh

theorem jointWeyl_common_period
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B l d : ℕ} (hB : 2 ≤ B) {k : I → ℕ} (hk : ∀ i, 0 < k i)
    (hl : 0 < l) (hkl : ∀ i, k i ∣ l) (F : ∀ i, PeriodicLocal (k i))
    (hdeg : ∀ i, topDegree (normalForm hB (hk i) (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i =>
      CorePeriodRefinement.repeatTuple (l := l) (hk i) (normalForm hB (hk i) (F i))))
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    JointWeyl (fun _ : I => B ^ l)
      (fun i => coreCyclicFullSeries B (hk i) ⟨0, hk i⟩
        (fun n => (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) (F i)) := by
  have hgdeg : ∀ i, topDegree (normalForm hB hl (CoreCommonPeriodEnd.family hk l F i)) ≤ d := by
    intro i
    rw [CoreCommonPeriodEnd.family_effective_degree hB hk hl hkl F i]
    exact hdeg i
  have hnf (i : I) : normalForm hB hl (CoreCommonPeriodEnd.family hk l F i) =
      CorePeriodRefinement.repeatTuple (l := l) (hk i) (normalForm hB (hk i) (F i)) :=
    CorePeriodRefinement.repeat_normalForm hB (hk i) hl (hkl i) (F i)
  have hlin' : LinearIndependent ℚ (fun i => normalForm hB hl (CoreCommonPeriodEnd.family hk l F i)) := by
    simpa only [hnf] using hlin
  have hh := movingRough_jointWeyl hκpos hSlope hC hreg hB hl ⟨0, hl⟩
    (CoreCommonPeriodEnd.family hk l F) hgdeg hlin' hκ
  simpa only [CoreCommonPeriodEnd.family_series B hk hl hkl F] using hh

end
end PrimeGapNormality.Prime.CoreRoughConsequences
