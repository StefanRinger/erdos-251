import PrimeGapNormality.Prime.CoreGeneralRoundedST
import PrimeGapNormality.Prime.CoreRoundedPolynomialNormality

/-!
# Rational polynomials of rounded powers under general calibrated S/T

The summands are literally P(round(gap^alpha)), not round(gap^(alpha*degree)).
Denominator clearing preserves degree. Subexponential gap growth and all
summability are derived from the same complex S and bare first-gap T.
-/
namespace PrimeGapNormality.Prime.CoreGeneralRoundedPolynomial
open Finset Filter MeasureTheory Polynomial CoreCyclic CoreIntegerGapObservable
open CoreRoundedPowerScaling CoreRoundedPolynomialScaling CoreRoundedPolynomialNormality
open CoreGeneralSequenceST CoreSequenceSTMeanTail CoreCalibratedMixtureFiniteSupport
open CoreSequenceSubexponentialGrowth
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

def integerSeries (a : ℕ → ℕ) (B : ℕ) (P : ℤ[X]) (kind : RoundKind) (alpha : ℝ) : ℝ :=
  ∑' n : ℕ, (roundedPolynomialIncrement P kind alpha (seqGap a n) : ℝ) / (B : ℝ) ^ (n + 1)

def rationalSeries (a : ℕ → ℕ) (B : ℕ) (P : ℚ[X]) (kind : RoundKind) (alpha : ℝ) : ℝ :=
  ∑' n : ℕ, ((P.eval ((roundedPower kind alpha (seqGap a n)).toNat : ℚ) : ℚ) : ℝ) /
    (B : ℝ) ^ (n + 1)

private theorem denominator_pos (P : ℚ[X]) : 0 < ratPolyDenProd P := by
  unfold ratPolyDenProd
  exact Finset.prod_pos fun i hi => (P.coeff i).den_pos

private theorem integerSeries_eq (a : ℕ → ℕ) (B : ℕ) (P : ℤ[X]) (kind : RoundKind) (alpha : ℝ) :
    observableFullSeries B (by norm_num : 0 < (1 : ℕ)) (0 : Fin 1)
      (fun _ q => roundedPolynomialIncrement P kind alpha q) (seqGap a) =
      integerSeries a B P kind alpha := by
  unfold observableFullSeries observableSeries observableValue integerSeries
  simp only [Nat.zero_add]

theorem integerSeries_weyl
    {a : ℕ → ℕ} (ha : StrictMono a) {B : ℕ} (hB : 2 ≤ B)
    (P : ℤ[X]) (kind : RoundKind) {alpha κ : ℝ} (hα : 0 < alpha)
    (hdeg : 1 ≤ P.natDegree) (hαdeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion B (integerSeries a B P kind alpha) := by
  have hlead : (fun _ : Fin 1 => P.leadingCoeff) ≠ 0 := by
    intro hz
    exact (Polynomial.leadingCoeff_ne_zero.2
      (ne_zero_of_natDegree_gt (zero_lt_one.trans_le hdeg))) (congrFun hz (0 : Fin 1))
  have he : 0 < alpha * (P.natDegree : ℝ) :=
    mul_pos hα (Nat.cast_pos.2 (zero_lt_one.trans_le hdeg))
  have hW := CoreGeneralScaledGapST.observableFullSeries_weyl ha hB
    (by norm_num : 0 < (1 : ℕ)) (0 : Fin 1)
    (fun _ q => roundedPolynomialIncrement P kind alpha q)
    (roundedPolynomialLinearConstant_nonneg P (alpha := alpha))
    (fun _ q hq => roundedPolynomialIncrement_abs_le_linear P kind hα hdeg hαdeg hq)
    he hαdeg (fun _ : Fin 1 => P.leadingCoeff) hlead
    (roundedPolynomial_compactScaling P kind hα hdeg) hκ hG hω hsum hcal hS hT
  simpa only [pow_one, integerSeries_eq] using hW

private theorem cleared_increment_eq (P : ℚ[X]) (kind : RoundKind)
    {alpha : ℝ} (hα : 0 < alpha) (q : ℕ) :
    (roundedPolynomialIncrement (clearedRatPolynomial P) kind alpha q : ℝ) =
      (ratPolyDenProd P : ℝ) * ((P.eval ((roundedPower kind alpha q).toNat : ℚ) - P.eval 0 : ℚ) : ℝ) := by
  let x : ℕ := (roundedPower kind alpha q).toNat
  have hx : (x : ℤ) = roundedPower kind alpha q := by
    dsimp only [x]
    exact Int.toNat_of_nonneg (roundedPower_nonneg kind hα q)
  have hevalRounded :
      ((Polynomial.eval (roundedPower kind alpha q) (clearedRatPolynomial P) : ℤ) : ℝ) =
        (ratPolyDenProd P : ℝ) * ((Polynomial.eval (x : ℚ) P : ℚ) : ℝ) := by
    rw [← hx]
    exact clearedRatPolynomial_eval_cast P x
  have hevalZero :
      ((Polynomial.eval (0 : ℤ) (clearedRatPolynomial P) : ℤ) : ℝ) =
        (ratPolyDenProd P : ℝ) * ((Polynomial.eval (0 : ℚ) P : ℚ) : ℝ) := by
    simpa only [Nat.cast_zero] using clearedRatPolynomial_eval_cast P 0
  unfold roundedPolynomialIncrement
  rw [Int.cast_sub, hevalRounded, hevalZero, Rat.cast_sub]
  dsimp only [x]
  ring

/-- Exact full-series denominator/constant identity with explicitly proved
convergence. Growth here is a finite analytic intermediate, discharged below. -/
theorem rationalSeries_eq_cleared_add {a : ℕ → ℕ} (ha : StrictMono a)
    {B : ℕ} (hB : 2 ≤ B) (P : ℚ[X]) (kind : RoundKind)
    {alpha : ℝ} (hα : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (hαdeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hg : HasSubexponentialGrowth (fun n => (seqGap a n : ℝ))) :
    rationalSeries a B P kind alpha =
      integerSeries a B (clearedRatPolynomial P) kind alpha / (ratPolyDenProd P : ℝ) +
        ((P.eval 0 : ℚ) : ℝ) / ((B : ℝ) - 1) := by
  let Q := clearedRatPolynomial P
  have hdegQ : 1 ≤ Q.natDegree := by simpa only [Q, clearedRatPolynomial_natDegree] using hdeg
  have hαQ : alpha * (Q.natDegree : ℝ) ≤ 1 := by
    simpa only [Q, clearedRatPolynomial_natDegree] using hαdeg
  have hgap : ∀ n, 1 ≤ seqGap a n := by
    intro n
    unfold seqGap
    exact Nat.one_le_iff_ne_zero.2 (Nat.sub_ne_zero_of_lt (ha (Nat.lt_succ_self n)))
  have hsumQ : Summable (fun n : ℕ =>
      (roundedPolynomialIncrement Q kind alpha (seqGap a n) : ℝ) / (B : ℝ) ^ (n + 1)) := by
    simpa only [observableValue, Nat.zero_add] using
      observableSeries_summable hB (by norm_num : 0 < (1 : ℕ)) (0 : Fin 1)
        (fun _ q => roundedPolynomialIncrement Q kind alpha q) hgap hg
        (roundedPolynomialLinearConstant_nonneg Q (alpha := alpha))
        (fun _ q hq => roundedPolynomialIncrement_abs_le_linear Q kind hα hdegQ hαQ hq) 0
  have hD : (ratPolyDenProd P : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos P).ne'
  have hsumC : Summable (fun n : ℕ => ((P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1)) := by
    simpa only [div_eq_mul_inv, one_mul] using (summable_one_div_pow_succ
      (by exact_mod_cast (show 1 < B by omega))).mul_left ((P.eval 0 : ℚ) : ℝ)
  have hconst : (∑' n : ℕ, ((P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1)) =
      ((P.eval 0 : ℚ) : ℝ) / ((B : ℝ) - 1) := by
    simp_rw [div_eq_mul_inv]
    rw [tsum_mul_left]
    have ht := tsum_inv_pow_succ hB
    simp only [one_div] at ht
    rw [ht]
  calc
    rationalSeries a B P kind alpha = ∑' n : ℕ,
        (((roundedPolynomialIncrement Q kind alpha (seqGap a n) : ℝ) / (B : ℝ) ^ (n + 1)) /
          (ratPolyDenProd P : ℝ) + ((P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1)) := by
      apply tsum_congr
      intro n
      rw [show Q = clearedRatPolynomial P from rfl, cleared_increment_eq P kind hα]
      push_cast
      field_simp [hD] <;> ring
    _ = _ := by
      rw [(hsumQ.div_const (ratPolyDenProd P : ℝ)).tsum_add hsumC, tsum_div_const, hconst] <;> rfl

theorem rationalSeries_normal
    {a : ℕ → ℕ} (ha : StrictMono a) {B : ℕ} (hB : 2 ≤ B)
    (P : ℚ[X]) (kind : RoundKind) {alpha κ : ℝ} (hα : 0 < alpha)
    (hdeg : 1 ≤ P.natDegree) (hαdeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal B (rationalSeries a B P kind alpha) := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hg := CoreGeneralSequenceClassification.gap_growth ha hκp hG hω hsum hcal hS hT
  have hW := integerSeries_weyl ha hB (clearedRatPolynomial P) kind hα
    (by simpa only [clearedRatPolynomial_natDegree] using hdeg)
    (by simpa only [clearedRatPolynomial_natDegree] using hαdeg) hκ hG hω hsum hcal hS hT
  have hD : (ratPolyDenProd P : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos P).ne'
  have hscaled : weylCriterion B ((ratPolyDenProd P : ℝ) *
      (integerSeries a B (clearedRatPolynomial P) kind alpha / (ratPolyDenProd P : ℝ))) := by
    have heq : (ratPolyDenProd P : ℝ) *
        (integerSeries a B (clearedRatPolynomial P) kind alpha / (ratPolyDenProd P : ℝ)) =
        integerSeries a B (clearedRatPolynomial P) kind alpha := by field_simp [hD]
    rwa [heq]
  have hroot := weylCriterion_of_mul (Nat.one_le_iff_ne_zero.2 (denominator_pos P).ne') hB hscaled
  let q : ℚ := P.eval 0 / (B - 1 : ℕ)
  have hfull := CoreRationalAffine.weylCriterion_add_rat hB q hroot
  have hq : (q : ℝ) = ((P.eval 0 : ℚ) : ℝ) / ((B : ℝ) - 1) := by
    dsimp only [q]
    rw [Rat.cast_div, Rat.cast_natCast, Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_one]
  apply CoreWeylNormality.isNormal_of_weyl hB
  rw [rationalSeries_eq_cleared_add ha hB P kind hα hdeg hαdeg hg]
  rwa [hq] at hfull

theorem rationalSeries_normal_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B : ℕ} (hB : 2 ≤ B)
    (P : ℚ[X]) (kind : RoundKind) {alpha κ : ℝ} (hα : 0 < alpha)
    (hdeg : 1 ≤ P.natDegree) (hαdeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : CoreGeneralRealCutoff.PatternS a κ G μ)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal B (rationalSeries a B P kind alpha) :=
  rationalSeries_normal ha hB P kind hα hdeg hαdeg hκ hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRealCutoff.patternS_nat hG hcal hS) hT

end
end PrimeGapNormality.Prime.CoreGeneralRoundedPolynomial
