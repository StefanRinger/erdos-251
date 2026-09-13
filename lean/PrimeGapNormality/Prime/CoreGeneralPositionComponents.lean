import PrimeGapNormality.Prime.CoreGeneralPeriodicPosition
import PrimeGapNormality.Prime.CorePositionComponents
import PrimeGapNormality.Prime.CoreJointEquidistribution

/-!
# The k position residue components under general calibrated S/T

The components are literally sum over n mod k=s of a(n)/B^(n+1).
Pure periodic residue weights are reused. Every integer character becomes
one actual nonzero periodic position weight; the scalar general S/T
consumer therefore gives joint Weyl and independence of 1 and the k
components, without any family-independence assumption.
-/
namespace PrimeGapNormality.Prime.CoreGeneralPositionComponents
open Finset Filter MeasureTheory Function CoreCyclic
open CoreGeneralSequenceST CoreGeneralSequenceClassification CoreSequenceSTMeanTail
open CoreCalibratedMixtureFiniteSupport CoreSequenceSubexponentialGrowth CorePositionComponents
open scoped Classical Topology
noncomputable section

def component (a : ℕ → ℕ) (B : ℕ) {k : ℕ} (s : Fin k) : ℝ :=
  ∑' n : ℕ, if n % k = s.val then (a n : ℝ) / (B : ℝ) ^ (n + 1) else 0

theorem component_summable {a : ℕ → ℕ} {B k : ℕ} (hB : 2 ≤ B)
    (hg : HasSubexponentialGrowth (fun n => (a n : ℝ))) (s : Fin k) :
    Summable (fun n : ℕ => if n % k = s.val then (a n : ℝ) / (B : ℝ) ^ (n + 1) else 0) := by
  have hBr : (1 : ℝ) < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hs := hg.summable_div_pow_succ hBr
  apply Summable.of_norm_bounded hs
  intro n
  have hnon : 0 ≤ (a n : ℝ) / (B : ℝ) ^ (n + 1) := by positivity
  split_ifs <;> simp only [Real.norm_eq_abs, abs_of_nonneg hnon, abs_zero, le_refl] <;> exact hnon

/-- Exact finite/tsum identity at the same original sequence origin.
Only summability is needed here and is derived from S in the consumer. -/
theorem positionSeries_combination {a : ℕ → ℕ} {B k : ℕ} (hB : 2 ≤ B)
    (hg : HasSubexponentialGrowth (fun n => (a n : ℝ))) (t : Fin k → ℤ) :
    CoreGeneralPeriodicPosition.positionSeries a B (positionResidueCombination t) =
      ∑ s : Fin k, (t s : ℝ) * component a B s := by
  have hs : ∀ s : Fin k, Summable (fun n : ℕ => (t s : ℝ) *
      (if n % k = s.val then (a n : ℝ) / (B : ℝ) ^ (n + 1) else 0)) :=
    fun s => (component_summable hB hg s).mul_left _
  have hterm (n : ℕ) : (positionResidueCombination t n : ℝ) *
      (a n : ℝ) / (B : ℝ) ^ (n + 1) =
      ∑ s : Fin k, (t s : ℝ) *
        (if n % k = s.val then (a n : ℝ) / (B : ℝ) ^ (n + 1) else 0) := by
    unfold positionResidueCombination
    rw [Rat.cast_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    unfold positionResidueWeight
    rw [Rat.cast_mul, Rat.cast_intCast]
    split_ifs <;> simp [mul_div_assoc]
  unfold CoreGeneralPeriodicPosition.positionSeries component
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun s _ => hs s)]
  exact Finset.sum_congr rfl fun s _ => tsum_mul_left

theorem components_jointWeyl
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    JointWeyl (fun _ : Fin k => B ^ k) (component a B) := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hs := shapeS_of_patternS hκp hG hω hsum hcal (patternS_of_complex hS)
    (meanGapTail_eventually_nonempty hT)
  have hcount := windowCountToInfinity ha hκp (by norm_num : (0 : ℝ) < 1)
    hG hω hsum hcal hs (meanGapTail_eventually_nonempty hT)
  have hg := sequence_hasSubexponentialGrowth ha hcount
  intro t ht
  have hW := CoreGeneralPeriodicPosition.positionSeries_weyl ha hB hk
    (positionResidueCombination t) (positionResidueCombination_periodic t)
    (positionResidueCombination_ne_zero hk ht) hκ hG hω hsum hcal hS hT
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
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    LinearIndependent ℚ (fun i : Option (Fin k) => match i with
      | none => (1 : ℝ)
      | some s => component a B s) := by
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  convert linearIndependent_one_jointWeyl hclock
    (components_jointWeyl ha hB hk hκ hG hω hsum hcal hS hT) using 1
  funext i
  cases i <;> rfl

theorem components_empirical_tendsto
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    Tendsto (CoreJointEquidistribution.empirical (fun _ : Fin k => B ^ k) (component a B)) atTop
      (𝓝 (CoreJointEquidistribution.torusVolume (Fin k))) :=
  CoreJointEquidistribution.empirical_tendsto_of_jointWeyl
    (components_jointWeyl ha hB hk hκ hG hω hsum hcal hS hT)

theorem components_jointWeyl_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : CoreGeneralRealCutoff.PatternS a κ G μ)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    JointWeyl (fun _ : Fin k => B ^ k) (component a B) :=
  components_jointWeyl ha hB hk hκ hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRealCutoff.patternS_nat hG hcal hS) hT

end
end PrimeGapNormality.Prime.CoreGeneralPositionComponents
