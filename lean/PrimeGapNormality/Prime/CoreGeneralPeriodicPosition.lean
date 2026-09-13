import PrimeGapNormality.Prime.CoreGeneralSequenceClassification
import PrimeGapNormality.Prime.CoreGeneralRealCutoff
import PrimeGapNormality.Prime.CorePeriodicPositionEnd

/-!
# Actual periodic positions under general calibrated-mixture S/T

The literal series is zero-based: sum c(n)*a(n)/B^(n+1). A one-step
periodic rotation reconciles it with the already proved one-based Abel
recurrence. Finite Abel, the rational matrix inverse, its noncancellation,
and the degree-one gap tuple are reused. S supplies position/gap growth;
no new position-tail estimate or sequence-growth premise is required.
-/
namespace PrimeGapNormality.Prime.CoreGeneralPeriodicPosition
open Finset Filter Function MeasureTheory CoreCyclic
open CoreGeneralSequenceST CoreGeneralSequenceClassification CoreSequenceSTMeanTail
open CoreCalibratedMixtureFiniteSupport CoreSequenceSubexponentialGrowth CorePeriodicPositionEnd
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 800000

def positionSeries (a : ℕ → ℕ) (B : ℕ) (c : ℕ → ℚ) : ℝ :=
  ∑' n : ℕ, (c n : ℝ) * (a n : ℝ) / (B : ℝ) ^ (n + 1)

def oneBasedWeight (k : ℕ) (c : ℕ → ℚ) (n : ℕ) : ℚ := c (n + (k - 1))

theorem oneBasedWeight_periodic {k : ℕ} {c : ℕ → ℚ} (hc : Periodic c k) :
    Periodic (oneBasedWeight k c) k := by
  intro n
  simpa only [oneBasedWeight, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc (n + (k - 1))

theorem oneBasedWeight_succ {k : ℕ} (hk : 0 < k) {c : ℕ → ℚ}
    (hc : Periodic c k) (n : ℕ) : oneBasedWeight k c (n + 1) = c n := by
  unfold oneBasedWeight
  rw [show n + 1 + (k - 1) = n + k by omega]
  exact hc n

theorem oneBasedWeight_ne_zero {k : ℕ} (hk : 0 < k) {c : ℕ → ℚ}
    (hc : Periodic c k) (hc0 : c ≠ 0) : oneBasedWeight k c ≠ 0 := by
  intro hz
  apply hc0
  funext n
  rw [← oneBasedWeight_succ hk hc n, hz]
  rfl

private theorem periodic_growth {k : ℕ} (hk : 0 < k) {c : ℕ → ℝ}
    (hc : Periodic c k) : HasSubexponentialGrowth c := by
  intro ρ hρ
  let C := ∑ j ∈ range k, |c j|
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨C, hC, fun n => ?_⟩
  exact (abs_le_sum_of_periodic (by omega) hc n).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hρ.le : 1 ≤ ρ ^ n) hC)

/-- Infinite Abel from the existing finite identity. Both summabilities
and the terminal decay are proved from the displayed subexponential data. -/
theorem positionSeries_eq_boundary_add_core
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k)
    (hpos : HasSubexponentialGrowth (fun n => (a n : ℝ)))
    (hgap : HasSubexponentialGrowth (fun n => (seqGap a n : ℝ))) :
    positionSeries a B c =
      (((a 0 : ℚ) * periodicGapWeightQ (oneBasedWeight k c) B k 0 : ℚ) : ℝ) +
        coreCyclicFullSeries B hk (phaseZero hk) (fun n => (seqGap a n : ℝ))
          (CoreOneGapWeights.tuple (periodicGapFinWeight (oneBasedWeight k c) B)) := by
  let c' := oneBasedWeight k c
  have hc' : Periodic c' k := oneBasedWeight_periodic hc
  let d : ℕ → ℝ := fun n => (periodicGapWeightQ c' B k n : ℝ)
  have hd : Periodic d k := periodic_cast_rat (periodicGapWeightQ_periodic hB (by omega) c' hc')
  have hrec (n : ℕ) : recGapWeight B d n = (c n : ℝ) := by
    have hh := periodicGapWeight_rec (j := n) hB (by omega : 1 ≤ k)
      (fun j => (c' j : ℝ)) (periodic_cast_rat hc')
    unfold recGapWeight at hh ⊢
    rw [periodicGapWeight_eq_rat (j := n) hB (by omega) c',
      periodicGapWeight_eq_rat (j := n + 1) hB (by omega) c'] at hh
    simpa only [c', oneBasedWeight_succ hk hc, d] using hh
  let f : ℕ → ℝ := fun n => (c n : ℝ) * (a n : ℝ) / (B : ℝ) ^ (n + 1)
  let g : ℕ → ℝ := fun n => d (n + 1) * (seqGap a n : ℝ) / (B : ℝ) ^ (n + 1)
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hf : Summable f := ((periodic_growth hk (periodic_cast_rat hc)).mul hpos).summable_div_pow_succ hBr
  have hg : Summable g := (((periodic_growth hk hd).shift 1).mul hgap).summable_div_pow_succ hBr
  have hrem : Tendsto (fun n => (a n : ℝ) * d (n + 1) / (B : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
    ((hpos.mul ((periodic_growth hk hd).shift 1)).summable_div_pow_succ hBr).tendsto_atTop_zero
  have hfin (n : ℕ) : (∑ i ∈ range (n + 1), f i) =
      (a 0 : ℝ) * d 0 + ∑ i ∈ range n, g i - (a n : ℝ) * d (n + 1) / (B : ℝ) ^ (n + 1) := by
    have hh := finite_gap_abel hB (fun j => (a (j - 1) : ℝ)) d (N := n + 1) (by omega)
    have hcast (i : ℕ) : (a (i + 1) : ℝ) - (a i : ℝ) = (seqGap a i : ℝ) := by
      unfold seqGap
      rw [Nat.cast_sub (ha.monotone (Nat.le_succ i))]
    simpa only [hrec, Nat.add_sub_cancel, show (1 : ℕ) - 1 = 0 by rfl,
      show ∀ i : ℕ, i + 2 - 1 = i + 1 by intro i; omega, hcast, f, g] using hh
  have hleft : Tendsto (fun n => ∑ i ∈ range (n + 1), f i) atTop (𝓝 (∑' n, f n)) := by
    simpa only [Function.comp_def] using
      hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hright : Tendsto (fun n => (a 0 : ℝ) * d 0 + ∑ i ∈ range n, g i -
      (a n : ℝ) * d (n + 1) / (B : ℝ) ^ (n + 1)) atTop
      (𝓝 ((a 0 : ℝ) * d 0 + ∑' n, g n)) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (a 0 : ℝ) * d 0)).add hg.hasSum.tendsto_sum_nat).sub hrem
  have heq := tendsto_nhds_unique hleft (hright.congr fun n => (hfin n).symm)
  rw [CoreOneGapWeights.series_tuple]
  have hphase (n : ℕ) :
      periodicGapFinWeight c' B (phaseAt hk (phaseZero hk) n) =
        periodicGapWeightQ c' B k (n + 1) :=
    periodicGapFinWeight_phase hB hk c' hc' n
  simpa only [hphase, positionSeries, f, g, d, c', Rat.cast_mul,
    Rat.cast_natCast] using heq

theorem positionSeries_weyl
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion (B ^ k) (positionSeries a B c) := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hs := shapeS_of_patternS hκp hG hω hsum hcal (patternS_of_complex hS)
    (meanGapTail_eventually_nonempty hT)
  have hcount := windowCountToInfinity ha hκp (by norm_num : (0 : ℝ) < 1)
    hG hω hsum hcal hs (meanGapTail_eventually_nonempty hT)
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
    (CoreOneGapWeights.tuple (periodicGapFinWeight c' B)) hnf hκp hκ' hG hω hsum hcal hS hT
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
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal (B ^ k) (positionSeries a B c) ∧
      PrimeGapNormality.BFree.IsNormal B (positionSeries a B c) := by
  have hW := positionSeries_weyl ha hB hk c hc hc0 hκ hG hω hsum hcal hS hT
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  exact ⟨CoreWeylNormality.isNormal_of_weyl hclock hW,
    CoreWeylNormality.isNormal_of_weyl hB (weylCriterion_of_pow hB hk hW)⟩

theorem positionSeries_normal_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : CoreGeneralRealCutoff.PatternS a κ G μ)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal (B ^ k) (positionSeries a B c) ∧
      PrimeGapNormality.BFree.IsNormal B (positionSeries a B c) :=
  positionSeries_normal ha hB hk c hc hc0 hκ hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRealCutoff.patternS_nat hG hcal hS) hT

end
end PrimeGapNormality.Prime.CoreGeneralPeriodicPosition
