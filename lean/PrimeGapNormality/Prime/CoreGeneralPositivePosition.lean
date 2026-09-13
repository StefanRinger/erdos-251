import PrimeGapNormality.Prime.CoreGeneralPositiveClassification
import PrimeGapNormality.Prime.CoreGeneralPeriodicPosition
import PrimeGapNormality.Prime.CoreGeneralPositionComponents

/-!
# Positive arbitrary-mixture S/T for periodic position weights

All position series, periodic inverses, Abel boundaries and residue
components are the existing literal objects. Only the scalar consumer is
changed to the genuine positive ShapeS with factor cS. Both sequence and
gap growth are derived; no separate position-tail premise is introduced.
-/
namespace PrimeGapNormality.Prime.CoreGeneralPositivePosition
open Finset Filter Function MeasureTheory CoreCyclic
open CoreGeneralSequenceST CoreGeneralPositiveClassification CoreSequenceSTMeanTail
open CoreCalibratedMixtureFiniteSupport CoreSequenceSubexponentialGrowth CorePeriodicPositionEnd
open CoreGeneralPeriodicPosition CoreGeneralPositionComponents CorePositionComponents
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem positionSeries_weyl
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {cS : ℝ} (hcS : 0 < cS) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω cS)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion (B ^ k) (positionSeries a B c) := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hcount := windowCountToInfinity ha hκp hcS
    hG hω hsum hcal hS (meanGapTail_eventually_nonempty hT)
  let c' := oneBasedWeight k c
  have hc' : Periodic c' k := oneBasedWeight_periodic hc
  have hc0' : c' ≠ 0 := oneBasedWeight_ne_zero hk hc hc0
  have hnf := periodicGapTuple_normalForm_ne_zero hB hk c' hc' hc0'
  have hdeg := periodicGapTuple_normalForm_degree hB hk c' hc' hc0'
  have hκ' : (topDegree (normalForm hB hk (CoreOneGapWeights.tuple (periodicGapFinWeight c' B))) : ℝ) /
      Real.log (B : ℝ) ≤ κ := by
    rw [hdeg]
    simpa only [Nat.cast_one] using hκ
  have hlocal := local_weyl ha hB hk (phaseZero hk)
    (CoreOneGapWeights.tuple (periodicGapFinWeight c' B)) hnf hκp hκ' hcS hG hω hsum hcal hS hT
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  have hshift := CoreRationalAffine.weylCriterion_add_rat hclock
    ((a 0 : ℚ) * periodicGapWeightQ c' B k 0) hlocal
  rw [positionSeries_eq_boundary_add_core ha hB hk c hc
    (sequence_hasSubexponentialGrowth ha hcount) (sequenceGap_hasSubexponentialGrowth ha hcount)]
  simpa only [c', add_comm] using hshift

theorem positionSeries_normal
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {cS : ℝ} (hcS : 0 < cS) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω cS)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal (B ^ k) (positionSeries a B c) ∧
      PrimeGapNormality.BFree.IsNormal B (positionSeries a B c) := by
  have hW := positionSeries_weyl ha hB hk c hc hc0 hκ hcS hG hω hsum hcal hS hT
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  exact ⟨CoreWeylNormality.isNormal_of_weyl hclock hW,
    CoreWeylNormality.isNormal_of_weyl hB (weylCriterion_of_pow hB hk hW)⟩

theorem positionSeries_normal_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {cS : ℝ} (hcS : 0 < cS) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : CoreGeneralRoundedPositive.RealShapeS a κ G μ cS)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal (B ^ k) (positionSeries a B c) ∧
      PrimeGapNormality.BFree.IsNormal B (positionSeries a B c) :=
  positionSeries_normal ha hB hk c hc hc0 hκ hcS hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRoundedPositive.shapeS_of_real hG hcal hS) hT


theorem components_jointWeyl
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {cS : ℝ} (hcS : 0 < cS) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω cS)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    JointWeyl (fun _ : Fin k => B ^ k) (component a B) := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hcount := windowCountToInfinity ha hκp hcS
    hG hω hsum hcal hS (meanGapTail_eventually_nonempty hT)
  have hg := sequence_hasSubexponentialGrowth ha hcount
  intro t ht
  have hW := positionSeries_weyl ha hB hk
    (positionResidueCombination t) (positionResidueCombination_periodic t)
    (positionResidueCombination_ne_zero hk ht) hκ hcS hG hω hsum hcal hS hT
  rw [positionSeries_combination hB hg t] at hW
  have hchar := hW 1 (by norm_num)
  have heq (n : ℕ) :
      (∑ s : Fin k, (t s : ℝ) * ((B ^ k : ℕ) : ℝ) ^ n * component a B s) =
      ((1 : ℤ) : ℝ) * ((B ^ k : ℕ) : ℝ) ^ n *
        (∑ s : Fin k, (t s : ℝ) * component a B s) := by
    simp only [Int.cast_one, one_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  simpa only [heq] using hchar

theorem components_one_linearIndependent
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {cS : ℝ} (hcS : 0 < cS) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω cS)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    LinearIndependent ℚ (fun i : Option (Fin k) => match i with
      | none => (1 : ℝ)
      | some s => component a B s) := by
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  convert linearIndependent_one_jointWeyl hclock
    (components_jointWeyl ha hB hk hκ hcS hG hω hsum hcal hS hT) using 1
  funext i
  cases i <;> rfl

theorem components_empirical_tendsto
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {cS : ℝ} (hcS : 0 < cS) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω cS)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    Tendsto (CoreJointEquidistribution.empirical (fun _ : Fin k => B ^ k) (component a B)) atTop
      (𝓝 (CoreJointEquidistribution.torusVolume (Fin k))) :=
  CoreJointEquidistribution.empirical_tendsto_of_jointWeyl
    (components_jointWeyl ha hB hk hκ hcS hG hω hsum hcal hS hT)

theorem components_jointWeyl_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {cS : ℝ} (hcS : 0 < cS) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : CoreGeneralRoundedPositive.RealShapeS a κ G μ cS)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    JointWeyl (fun _ : Fin k => B ^ k) (component a B) :=
  components_jointWeyl ha hB hk hκ hcS hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRoundedPositive.shapeS_of_real hG hcal hS) hT


end
end PrimeGapNormality.Prime.CoreGeneralPositivePosition
