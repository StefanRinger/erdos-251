import PrimeGapNormality.Prime.CoreGeneralSequenceClassification
import PrimeGapNormality.Prime.CoreSequenceSTRelations
import PrimeGapNormality.Prime.CoreCommonPeriodEnd
import PrimeGapNormality.Prime.CoreJointEquidistribution

/-!
# Actual relations under arbitrary calibrated-mixture S/T

The existing sequence-generic linear map supplies exact finite/tsum
linearity. Its convergence is derived from literal complex S and bare T.
All combinations use one fixed effective-degree budget and original G.
Common-period repetition changes neither degree nor series value.
-/
namespace PrimeGapNormality.Prime.CoreGeneralSequenceRelations
open Finset Filter MeasureTheory MvPolynomial CoreCyclic
open CoreGeneralSequenceST CoreGeneralSequenceClassification CoreSequenceSTMeanTail
open CoreCalibratedMixtureFiniteSupport
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 800000

theorem fullSeries_sum_smul
    {I : Type*} [Fintype I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k) (q : I → ℚ) {κ : ℝ} (hκp : 0 < κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (∑ i, q i • F i) =
      ∑ i, (q i : ℝ) * coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (F i) := by
  let ev := CoreSequenceSTRelations.sequenceSeriesLinear hB hk phase
    (gap_growth ha hκp hG hω hsum hcal hS hT)
  change ev (∑ i, q i • F i) = ∑ i, (q i : ℝ) * ev (F i)
  simp only [map_sum, map_smul, Rat.smul_def]

theorem combination_weyl
    {I : Type*} [Fintype I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k) (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    {κ : ℝ} (hκp : 0 < κ) (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G)
    (q : I → ℚ) (hq : (∑ i, q i • normalForm hB hk (F i)) ≠ 0) :
    weylCriterion (B ^ k)
      (∑ i, (q i : ℝ) * coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (F i)) := by
  have hκq : (topDegree (normalForm hB hk (∑ i, q i • F i)) : ℝ) / Real.log (B : ℝ) ≤ κ :=
    (div_le_div_of_nonneg_right (Nat.cast_le.2
      (CoreLocalRelations.topDegree_normalForm_sum_le hB hk F q hdeg))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega)))).trans hκ
  have hW := local_weyl ha hB hk phase (∑ i, q i • F i)
    (by rwa [CoreLocalRelations.normalForm_sum_smul]) hκp hκq hG hω hsum hcal hS hT
  rwa [fullSeries_sum_smul ha hB hk phase F q hκp hG hω hsum hcal hS hT] at hW

theorem rational_relation_iff
    {I : Type*} [Fintype I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k) (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    {κ : ℝ} (hκp : 0 < κ) (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) (q : I → ℚ) :
    (∃ z : ℚ, (∑ i, (q i : ℝ) *
      coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (F i)) = (z : ℝ)) ↔
      (∑ i, q i • normalForm hB hk (F i)) = 0 := by
  have hκq : (topDegree (normalForm hB hk (∑ i, q i • F i)) : ℝ) / Real.log (B : ℝ) ≤ κ :=
    (div_le_div_of_nonneg_right (Nat.cast_le.2
      (CoreLocalRelations.topDegree_normalForm_sum_le hB hk F q hdeg))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega)))).trans hκ
  have hh := local_rational_iff_normalForm_zero ha hB hk phase (∑ i, q i • F i)
    hκp hκq hG hω hsum hcal hS hT
  rwa [fullSeries_sum_smul ha hB hk phase F q hκp hG hω hsum hcal hS hT,
    CoreLocalRelations.normalForm_sum_smul] at hh

theorem jointWeyl_of_independent_normalForms
    {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k) (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    {κ : ℝ} (hκp : 0 < κ) (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    JointWeyl (fun _ : I => B ^ k)
      (fun i => coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (F i)) := by
  intro t ht
  have hq : (∑ i, (t i : ℚ) • normalForm hB hk (F i)) ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := ht
    exact hi (Int.cast_eq_zero.1 ((Fintype.linearIndependent_iff.1 hlin) (fun i => (t i : ℚ)) hz i))
  have hW := combination_weyl ha hB hk phase F hdeg hκp hκ hG hω hsum hcal hS hT
    (fun i => (t i : ℚ)) hq
  have hchar := hW 1 (by norm_num)
  have heq (n : ℕ) :
      (∑ i, (t i : ℝ) * ((B ^ k : ℕ) : ℝ) ^ n *
        coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (F i)) =
      ((1 : ℤ) : ℝ) * ((B ^ k : ℕ) : ℝ) ^ n *
        (∑ i, ((t i : ℚ) : ℝ) * coreCyclicFullSeries B hk phase
          (fun n => (seqGap a n : ℝ)) (F i)) := by
    simp only [Int.cast_one, one_mul, Rat.cast_intCast, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by ring
  simpa only [heq] using hchar

theorem one_linearIndependent
    {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k) (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    {κ : ℝ} (hκp : 0 < κ) (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    LinearIndependent ℚ (fun i : Option I => match i with
      | none => (1 : ℝ)
      | some i => coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (F i)) := by
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  exact linearIndependent_one_jointWeyl hclock
    (jointWeyl_of_independent_normalForms ha hB hk phase F hdeg hlin hκp hκ hG hω hsum hcal hS hT)

theorem joint_empirical_tendsto
    {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k) (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    {κ : ℝ} (hκp : 0 < κ) (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    Tendsto (CoreJointEquidistribution.empirical (fun _ : I => B ^ k)
      (fun i => coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (F i))) atTop
      (𝓝 (CoreJointEquidistribution.torusVolume I)) :=
  CoreJointEquidistribution.empirical_tendsto_of_jointWeyl
    (jointWeyl_of_independent_normalForms ha hB hk phase F hdeg hlin hκp hκ hG hω hsum hcal hS hT)

/-- Every positive common multiple is allowed, in particular the LCM of
the finitely many original positive periods. Only the embedded normal
classes enter the independence criterion; the original series stay literal. -/
theorem jointWeyl_common_period
    {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B l d : ℕ} (hB : 2 ≤ B) {k : I → ℕ} (hk : ∀ i, 0 < k i)
    (hl : 0 < l) (hkl : ∀ i, k i ∣ l) (F : ∀ i, PeriodicLocal (k i))
    (hdeg : ∀ i, topDegree (normalForm hB (hk i) (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i =>
      CorePeriodRefinement.repeatTuple (l := l) (hk i) (normalForm hB (hk i) (F i))))
    {κ : ℝ} (hκp : 0 < κ) (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    JointWeyl (fun _ : I => B ^ l)
      (fun i => coreCyclicFullSeries B (hk i) ⟨0, hk i⟩ (fun n => (seqGap a n : ℝ)) (F i)) := by
  have hgdeg : ∀ i, topDegree (normalForm hB hl (CoreCommonPeriodEnd.family hk l F i)) ≤ d := by
    intro i
    rw [CoreCommonPeriodEnd.family_effective_degree hB hk hl hkl F i]
    exact hdeg i
  have hnf (i : I) : normalForm hB hl (CoreCommonPeriodEnd.family hk l F i) =
      CorePeriodRefinement.repeatTuple (l := l) (hk i) (normalForm hB (hk i) (F i)) :=
    CorePeriodRefinement.repeat_normalForm hB (hk i) hl (hkl i) (F i)
  have hlin' : LinearIndependent ℚ (fun i => normalForm hB hl (CoreCommonPeriodEnd.family hk l F i)) := by
    simpa only [hnf] using hlin
  have hh := jointWeyl_of_independent_normalForms ha hB hl ⟨0, hl⟩
    (CoreCommonPeriodEnd.family hk l F) hgdeg hlin' hκp hκ hG hω hsum hcal hS hT
  simpa only [CoreCommonPeriodEnd.family_series B hk hl hkl F] using hh

theorem rational_relation_iff_common_period
    {I : Type*} [Fintype I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B l d : ℕ} (hB : 2 ≤ B) {k : I → ℕ} (hk : ∀ i, 0 < k i)
    (hl : 0 < l) (hkl : ∀ i, k i ∣ l) (F : ∀ i, PeriodicLocal (k i))
    (hdeg : ∀ i, topDegree (normalForm hB (hk i) (F i)) ≤ d)
    {κ : ℝ} (hκp : 0 < κ) (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) (q : I → ℚ) :
    (∃ z : ℚ, (∑ i, (q i : ℝ) * coreCyclicFullSeries B (hk i) ⟨0, hk i⟩
      (fun n => (seqGap a n : ℝ)) (F i)) = (z : ℝ)) ↔
      (∑ i, q i • CorePeriodRefinement.repeatTuple (l := l) (hk i)
        (normalForm hB (hk i) (F i))) = 0 := by
  have hgdeg : ∀ i, topDegree (normalForm hB hl (CoreCommonPeriodEnd.family hk l F i)) ≤ d := by
    intro i
    rw [CoreCommonPeriodEnd.family_effective_degree hB hk hl hkl F i]
    exact hdeg i
  have hnf (i : I) : normalForm hB hl (CoreCommonPeriodEnd.family hk l F i) =
      CorePeriodRefinement.repeatTuple (l := l) (hk i) (normalForm hB (hk i) (F i)) :=
    CorePeriodRefinement.repeat_normalForm hB (hk i) hl (hkl i) (F i)
  have hh := rational_relation_iff ha hB hl ⟨0, hl⟩ (CoreCommonPeriodEnd.family hk l F)
    hgdeg hκp hκ hG hω hsum hcal hS hT q
  simpa only [CoreCommonPeriodEnd.family_series B hk hl hkl F, hnf] using hh

end
end PrimeGapNormality.Prime.CoreGeneralSequenceRelations
