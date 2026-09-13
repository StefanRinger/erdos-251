import PrimeGapNormality.Prime.CoreGeneralSequenceClassification
import PrimeGapNormality.Prime.CoreGeneralRoundedPositive

/-!
# Rational local classification under positive arbitrary-mixture S/T

This leaf uses the existing integer-rooted positive consumer with its
original factor c. Denominator clearing, normal form and the actual
rational boundary are unchanged. Complex S is not inferred. Counts,
growth and summability are derived from the stated ShapeS and mean T.
-/

namespace PrimeGapNormality.Prime.CoreGeneralPositiveClassification
open Finset Filter MvPolynomial CoreCyclic CoreGeneralSequenceST
open CoreCalibratedMixtureFiniteSupport CoreSequenceSTMeanTail
  CoreSequenceSubexponentialGrowth
open scoped Classical Topology
noncomputable section

private theorem clock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) : 2 ≤ B ^ k := by
  rw [show k = k - 1 + 1 by omega, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

private theorem exists_width {k : ℕ} (F : PeriodicLocal k) :
    ∃ w : ℕ, ∀ s i, i ∈ (F s).vars → i ≤ w := by
  refine ⟨univ.sup (fun s : Fin k => (F s).vars.sup id), ?_⟩
  intro s i hi
  exact (Finset.le_sup (f := id) hi).trans
    (Finset.le_sup (f := fun s : Fin k => (F s).vars.sup id) (mem_univ s))

theorem gap_growth {a : ℕ → ℕ} (ha : StrictMono a) {κ : ℝ} (hκ : 0 < κ)
    {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    HasSubexponentialGrowth (fun n => (seqGap a n : ℝ)) := by
  exact sequenceGap_hasSubexponentialGrowth ha
    (windowCountToInfinity ha hκ hc hG hω hsum hcal hS
      (meanGapTail_eventually_nonempty hT))

/-- Exact rational boundary with convergence supplied internally by S. -/
theorem fullSeries_eq_normalForm_add_boundary
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) {κ : ℝ} (hκ : 0 < κ)
    {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F =
      coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (normalForm hB hk F) +
        (CoreSequenceSTClassification.sequenceLocalBoundaryRat hB hk phase a F : ℝ) :=
  CoreSequenceSTClassification.coreCyclicFullSeries_eq_normalForm_add_boundary_of_subexponential
    hB hk phase F (gap_growth ha hκ hc hG hω hsum hcal hS hT)

theorem rooted_rational_weyl
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    {κ : ℝ} (hκp : 0 < κ) (hκ : (topDegree N : ℝ) / Real.log (B : ℝ) ≤ κ)
    {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion (B ^ k) (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) N) := by
  obtain ⟨w, hw⟩ := exists_width N
  have hκI : (topDegree (liftedIntegerTuple N) : ℝ) / Real.log (B : ℝ) ≤ κ := by
    rwa [topDegree_liftedIntegerTuple N]
  have hI := fullSeries_weyl_clock ha hB hk phase (integerTupleLift N).tuple w
    (liftedIntegerTuple_rooted hk N hroot) (liftedIntegerTuple_ne_zero N hN)
    ((liftedIntegerTuple_width_iff N).2 hw) hκI hc
    hG hω hsum hcal hS hT
  change weylCriterion (B ^ k)
    (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (liftedIntegerTuple N)) at hI
  rw [coreCyclicFullSeries_liftedIntegerTuple] at hI
  exact weylCriterion_of_mul (Nat.succ_le_iff.mpr (liftedIntegerScale_pos N)) (clock_ge hB hk) hI

theorem local_weyl
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) (hNF : normalForm hB hk F ≠ 0)
    {κ : ℝ} (hκp : 0 < κ)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion (B ^ k) (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F) := by
  have hn := rooted_rational_weyl ha hB hk phase (normalForm hB hk F)
    (drop_normalForm hB hk F) hNF hκp hκ hc hG hω hsum hcal hS hT
  have heq := fullSeries_eq_normalForm_add_boundary ha hB hk phase F hκp hc hG hω hsum hcal hS hT
  have hh := CoreRationalAffine.weylCriterion_add_rat (clock_ge hB hk)
    (CoreSequenceSTClassification.sequenceLocalBoundaryRat hB hk phase a F) hn
  rwa [← heq] at hh

theorem local_rational_iff_normalForm_zero
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) {κ : ℝ} (hκp : 0 < κ)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    (∃ q : ℚ, coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F = (q : ℝ)) ↔
      normalForm hB hk F = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    by_contra hn
    exact (weylCriterion_irrational
      (local_weyl ha hB hk phase F hn hκp hκ hc hG hω hsum hcal hS hT)) ⟨q, hq.symm⟩
  · intro hz
    exact CoreSequenceSTClassification.coreCyclicFullSeries_rational_of_normalForm_zero
      hB hk phase F (gap_growth ha hκp hc hG hω hsum hcal hS hT) hz

/-- Full rational-or-normal dichotomy at unchanged effective NF degree. -/
theorem local_classification
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) {κ : ℝ} (hκp : 0 < κ)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    (normalForm hB hk F = 0 ∧
      ∃ q : ℚ, coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F = (q : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k) (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F)) := by
  by_cases hz : normalForm hB hk F = 0
  · exact Or.inl ⟨hz, (local_rational_iff_normalForm_zero ha hB hk phase F hκp hκ hc hG
      hω hsum hcal hS hT).2 hz⟩
  · have hW := local_weyl ha hB hk phase F hz hκp hκ hc hG hω hsum hcal hS hT
    exact Or.inr ⟨hz, hW, CoreWeylNormality.isNormal_of_weyl (clock_ge hB hk) hW,
      CoreWeylNormality.isNormal_of_weyl hB (weylCriterion_of_pow hB hk hW)⟩

/-- Literal positive comparison with an arbitrary real-cutoff probability,
including nonatomic laws, is transferred by the exact floor expectation. -/
theorem local_classification_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) {κ : ℝ} (hκp : 0 < κ)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → MeasureTheory.ProbabilityMeasure ℝ)
    (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : CoreGeneralRoundedPositive.RealShapeS a κ G μ c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    (normalForm hB hk F = 0 ∧
      ∃ q : ℚ, coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F = (q : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k) (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F)) :=
  local_classification ha hB hk phase F hκp hκ hc hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRoundedPositive.shapeS_of_real hG hcal hS) hT

end
end PrimeGapNormality.Prime.CoreGeneralPositiveClassification
