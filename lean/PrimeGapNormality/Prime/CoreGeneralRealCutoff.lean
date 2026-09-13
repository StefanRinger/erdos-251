import PrimeGapNormality.Prime.CoreGeneralSequenceClassification
import PrimeGapNormality.Prime.CoreCalibratedRealCutoff
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Actual real-cutoff mixtures in general S/T

The real probability may be nonatomic. Only its natural-floor pushforward
is eventually finitely supported. The same finite support handles every
complex pattern expectation exactly, not through a truncation error or a
new integrability assumption. Calibration and S are preserved literally.
-/

namespace PrimeGapNormality.Prime.CoreGeneralRealCutoff
open Filter MeasureTheory Finset CoreCyclic CoreGeneralSequenceST
open CoreCalibratedRealCutoff CoreCalibratedMixtureFiniteSupport CoreSequenceSTMeanTail
open scoped Classical Topology ENNReal
noncomputable section
set_option maxHeartbeats 1000000

def weights (μ : ℕ → ProbabilityMeasure ℝ) (X y : ℕ) : ℝ := (cutoffPMF (μ X) y).toReal

theorem integrable_of_pmf_tail_zero (p : PMF ℕ) {N : ℕ}
    (hz : ∀ y, N ≤ y → p y = 0) (f : ℕ → ℂ) : Integrable f p.toMeasure := by
  have hae : ∀ᵐ y ∂p.toMeasure, y < N := by
    apply ae_iff_of_countable.2
    intro y hy
    by_contra hn
    apply hy
    rw [PMF.toMeasure_apply_singleton p y (measurableSet_singleton y)]
    exact hz y (Nat.not_lt.mp hn)
  let C : ℝ := ∑ y ∈ range N, ‖f y‖
  apply (integrable_const C : Integrable (fun _ : ℕ => C) p.toMeasure).mono'
    (measurable_of_countable f).aestronglyMeasurable
  filter_upwards [hae] with y hy
  dsimp only [C]
  exact Finset.single_le_sum (f := fun z : ℕ ↦ ‖f z‖)
    (fun z _ ↦ norm_nonneg (f z)) (Finset.mem_range.2 hy)

/-- Every complex cutoff observable has an exact finite expectation once
the actual cutoff PMF has finite support. No global bound on f is needed. -/
theorem integral_floor_eq_sum (μ : ProbabilityMeasure ℝ) {N : ℕ}
    (hz : ∀ y, N ≤ y → cutoffPMF μ y = 0) (f : ℕ → ℂ) :
    (∫ x : ℝ, f (Nat.floor x) ∂(μ : Measure ℝ)) =
      ∑ y ∈ range N, ((cutoffPMF μ y).toReal : ℂ) * f y := by
  have hf : Measurable f := measurable_of_countable _
  calc
    _ = ∫ y, f y ∂(cutoffPMF μ).toMeasure := by
      rw [cutoffPMF_toMeasure,
        integral_map Nat.measurable_floor.aemeasurable hf.aestronglyMeasurable]
    _ = ∑' y, (cutoffPMF μ y).toReal • f y :=
      PMF.integral_eq_tsum _ _ (integrable_of_pmf_tail_zero _ hz f)
    _ = _ := by
      simp only [Complex.real_smul]
      apply tsum_eq_sum
      intro y hy
      rw [hz y (by simpa only [Finset.mem_range, not_lt] using hy), ENNReal.toReal_zero,
        Complex.ofReal_zero, zero_mul]

theorem complexShapeMean_mixture (ω : ℕ → ℝ) (S L : ℕ) {N : ℕ}
    (hz : ∀ y, N ≤ y → ω y = 0) (f : Finset ℕ → ℂ) :
    complexShapeMean (offsetWindow S) (CoreCalibratedMixtureMoments.law ω S) L f =
      ∑ y ∈ range N, (ω y : ℂ) * complexShapeMean (offsetWindow S) (actualRootLaw y S) L f := by
  have hshort (K : Finset ℕ) :
      Stopped.shortShapeMass (offsetWindow S) (CoreCalibratedMixtureMoments.law ω S) L K =
        ∑ y ∈ range N, ω y * Stopped.shortShapeMass (offsetWindow S) (actualRootLaw y S) L K := by
    unfold Stopped.shortShapeMass CoreCalibratedMixtureMoments.law
    simp_rw [weighted_tsum_eq_sum_of_tail_zero ω _ hz]
    have hi (U : Finset ℕ) :
        (if L ≤ U.card ∧ Stopped.firstL L U = K then ∑ y ∈ range N, ω y * actualRootLaw y S U else 0) =
        ∑ y ∈ range N, ω y * (if L ≤ U.card ∧ Stopped.firstL L U = K then actualRootLaw y S U else 0) := by
      split_ifs <;> simp
    simp_rw [hi]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  unfold complexShapeMean
  simp_rw [hshort, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro K hK
  ring

/-- Exact equality of the REAL-cutoff integral and natural-mixture model
for every complex first-L test, all using the same finite support. -/
theorem modelExpectation_eq (μ : ProbabilityMeasure ℝ) {N : ℕ}
    (hz : ∀ y, N ≤ y → cutoffPMF μ y = 0) (S L : ℕ) (f : Finset ℕ → ℂ) :
    (∫ x : ℝ, complexShapeMean (offsetWindow S) (actualRootLaw (Nat.floor x) S) L f
      ∂(μ : Measure ℝ)) =
    complexShapeMean (offsetWindow S)
      (CoreCalibratedMixtureMoments.law (fun y => (cutoffPMF μ y).toReal) S) L f := by
  rw [integral_floor_eq_sum μ hz
    (fun y => complexShapeMean (offsetWindow S) (actualRootLaw y S) L f)]
  exact (complexShapeMean_mixture _ S L (fun y hy => by rw [hz y hy, ENNReal.toReal_zero]) f).symm

def Calibration (μ : ℕ → ProbabilityMeasure ℝ) (G : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ X in atTop, ∀ᵐ x : ℝ ∂(μ X : Measure ℝ),
    |CoreRoughSyntheticScale.roughGapScale (Nat.floor x) / G X - 1| ≤ ε

/-- Literal complex S with an actual integral over real cutoffs. -/
def PatternS (a : ℕ → ℕ) (κ : ℝ) (G : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ X in atTop, ∀ f : Finset ℕ → ℂ,
    (∀ U ∈ (offsetWindow (span κ G X)).powerset.filter
      (fun U => U.card = CoreGeneralModelReference.rank κ G X), ‖f U‖ ≤ 1) →
    ‖complexShapeMean (offsetWindow (span κ G X))
        (CoreSequencePatternLaw.patternMass a X (offsetWindow (span κ G X)))
        (CoreGeneralModelReference.rank κ G X) f -
      ∫ x : ℝ, complexShapeMean (offsetWindow (span κ G X))
        (actualRootLaw (Nat.floor x) (span κ G X)) (CoreGeneralModelReference.rank κ G X) f
          ∂(μ X : Measure ℝ)‖ ≤ ε

theorem patternS_nat {a : ℕ → ℕ} {κ : ℝ} {G : ℕ → ℝ}
    (hG : Tendsto G atTop atTop) {μ : ℕ → ProbabilityMeasure ℝ}
    (hcal : Calibration μ G) (hS : PatternS a κ G μ) :
    CoreGeneralSequenceST.ComplexPatternS a κ G (weights μ) := by
  intro ε hε
  filter_upwards [hS ε hε, hG.eventually_gt_atTop 0, hcal 1 (by norm_num)] with X hx hg hc
  obtain ⟨N, hz, hs, he⟩ := exists_finite_floor_representation (μ X) hg hc
  intro f hf
  have hh := hx f hf
  rw [modelExpectation_eq (μ X) hz] at hh
  exact hh

/-- Full effective-degree classification for arbitrary real-cutoff
probabilities and the literal complex S/T input. -/
theorem local_classification
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) {κ : ℝ} (hκp : 0 < κ)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) (μ : ℕ → ProbabilityMeasure ℝ)
    (hcal : Calibration μ G) (hS : PatternS a κ G μ)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    (normalForm hB hk F = 0 ∧
      ∃ q : ℚ, coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F = (q : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k) (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) F)) :=
  CoreGeneralSequenceClassification.local_classification ha hB hk phase F hκp hκ hG
    (fun X y => real_weights_nonneg (μ X) y) (fun X => real_weights_sum (μ X))
    (uniformCalibration_of_ae μ G hcal) (patternS_nat hG hcal hS) hT

end
end PrimeGapNormality.Prime.CoreGeneralRealCutoff
