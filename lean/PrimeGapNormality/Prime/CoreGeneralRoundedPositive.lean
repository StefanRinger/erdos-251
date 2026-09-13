import PrimeGapNormality.Prime.CoreGeneralScaledGapPositiveST
import PrimeGapNormality.Prime.CoreGeneralRoundedST
import PrimeGapNormality.Prime.CoreGeneralRoundedFamily
import PrimeGapNormality.Prime.CoreGeneralRoundedInfinite
import PrimeGapNormality.Prime.CoreGeneralRoundedPolynomial
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Rounded powers and compositions under positive arbitrary-mixture S/T

The input is the literal one-sided ShapeS with the same c, G, canonical
rank and actual cutoff weights. We never infer complex equality from it.
All series and deterministic finite-family algebra are the existing actual
objects. One kind fixes all floors or all ceilings. The common kappa is
chosen before every finite frequency and before every finite restriction.
-/
namespace PrimeGapNormality.Prime.CoreGeneralRoundedPositive
open Finset Filter MeasureTheory Polynomial CoreCyclic CoreIntegerGapObservable
open CoreRoundedPowerScaling CoreRoundedPolynomialScaling CoreRoundedPolynomialNormality
open CoreGeneralSequenceST CoreSequenceSTMeanTail CoreCalibratedMixtureFiniteSupport
open CoreGeneralModelReference CoreSequenceSubexponentialGrowth
open CoreSequenceWindowGrowthFromS
open CoreGeneralRoundedST CoreGeneralRoundedFamily CoreGeneralRoundedInfinite
open CoreGeneralRoundedPolynomial
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem roundedCombination_weyl
    {I : Type*} [Fintype I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = exponent ∨ alpha i < exponent))
    (hb : leadingColumn alpha b exponent ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion (B ^ k)
      (observableFullSeries B hk r (roundedCombination kind alpha b) (seqGap a)) := by
  have hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1 := fun i =>
    ⟨(halpha i).1, (halpha i).2.elim (fun h => h ▸ he1) (fun h => h.le.trans he1)⟩
  exact CoreGeneralScaledGapPositiveST.observableFullSeries_weyl ha hB hk r _
    (CoreRoundedPrimeNormality.roundedLinearConstant_nonneg b)
    (CoreRoundedPrimeNormality.roundedCombination_linear_bound kind alpha b hα)
    he he1 (CoreRoundedModelSubsequence.integerLeadingColumn alpha b exponent)
    (CoreRoundedModelSubsequence.integerLeadingColumn_ne_zero alpha b exponent hb)
    (rounded_compactScaling kind alpha b he he1 halpha) hκ hc hG hω hsum hcal hS hT

theorem roundedCombination_normal
    {I : Type*} [Fintype I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = exponent ∨ alpha i < exponent))
    (hb : leadingColumn alpha b exponent ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
        (observableFullSeries B hk r (roundedCombination kind alpha b) (seqGap a)) ∧
      PrimeGapNormality.BFree.IsNormal B
        (observableFullSeries B hk r (roundedCombination kind alpha b) (seqGap a)) := by
  have hW := roundedCombination_weyl ha hB hk r kind alpha b he he1 halpha hb
    hκ hc hG hω hsum hcal hS hT
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  exact ⟨CoreWeylNormality.isNormal_of_weyl hclock hW,
    CoreWeylNormality.isNormal_of_weyl hB (weylCriterion_of_pow hB hk hW)⟩

theorem residue_jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (hinj : Function.Injective alpha) {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    JointWeyl (fun _ : Fin k × I => B ^ k) (residueSeries a B hk r kind alpha) := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hcount := windowCountToInfinity ha hκp hc
    hG hω hsum hcal hS (meanGapTail_eventually_nonempty hT)
  have hg := sequenceGap_hasSubexponentialGrowth ha hcount
  have hgap : ∀ n, 1 ≤ seqGap a n := by
    intro n
    unfold seqGap
    exact Nat.one_le_iff_ne_zero.2 (Nat.sub_ne_zero_of_lt (ha (Nat.lt_succ_self n)))
  intro t ht
  obtain ⟨exponent, he, he1, alpha', b', hα', hb', hobs⟩ := exists_active_leading kind alpha hα hinj t ht
  have hW := roundedCombination_weyl ha hB hk r kind alpha' b' he he1 hα' hb'
    hκ hc hG hω hsum hcal hS hT
  have hseries : observableFullSeries B hk r (roundedCombination kind alpha' b') (seqGap a) =
      ∑ p : Fin k × I, (t p : ℝ) * residueSeries a B hk r kind alpha p := by
    rw [← hobs]
    simpa only [residueSeries] using
      CoreIntegerGapLinearAlgebra.observableFullSeries_integerCombination hB hk r (seqGap a) hgap hg
        t (basisObservable kind alpha) (fun _ => (2 : ℝ)) (fun _ => by norm_num)
        (basis_linear kind alpha hα)
  have hone := hW 1 (by norm_num)
  apply hone.congr'
  exact Eventually.of_forall fun N => by
    apply congrArg (fun z : ℂ => z / (N : ℂ))
    apply sum_congr rfl
    intro n hn
    apply congrArg e
    rw [hseries]
    simp only [Int.cast_one, one_mul, Finset.mul_sum]
    apply sum_congr rfl
    intro q hq
    ring

section Consequences
variable {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (hinj : Function.Injective alpha) {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G)

include ha hB hk r kind alpha hα hinj hκ hc hG hω hsum hcal hS hT

theorem residue_rationalCombination_normal (q : Fin k × I → ℚ) (hq : ∃ p, q p ≠ 0) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (∑ p, (q p : ℝ) * residueSeries a B hk r kind alpha p) := by
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  exact CoreWeylNormality.isNormal_of_weyl hclock (weylCriterion_linearCombination hclock
    (residue_jointWeyl ha hB hk r kind alpha hα hinj hκ hc hG hω hsum hcal hS hT) hq)

theorem residue_one_linearIndependent :
    LinearIndependent ℚ (fun p : Option (Fin k × I) => match p with
      | none => (1 : ℝ)
      | some p => residueSeries a B hk r kind alpha p) := by
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  convert (linearIndependent_one_jointWeyl (I := Fin k × I)
    (θ := residueSeries a B hk r kind alpha) hclock
    (residue_jointWeyl ha hB hk r kind alpha hα hinj hκ hc hG hω hsum hcal hS hT)) using 1 <;>
    first | (funext p; cases p <;> rfl) | rfl

theorem residue_empirical_tendsto :
    Tendsto (CoreJointEquidistribution.empirical (fun _ : Fin k × I => B ^ k)
      (residueSeries a B hk r kind alpha)) atTop
      (𝓝 (CoreJointEquidistribution.torusVolume (Fin k × I))) :=
  CoreJointEquidistribution.empirical_tendsto_of_jointWeyl
    (residue_jointWeyl ha hB hk r kind alpha hα hinj hκ hc hG hω hsum hcal hS hT)

end Consequences

private def exponentOf {k : ℕ} (x : Option (Fin k × Exponent)) : Exponent :=
  match x with
  | none => ⟨1, by simp⟩
  | some p => p.2
private def supportExponents {k : ℕ} (s : Finset (Option (Fin k × Exponent))) : Finset Exponent :=
  s.image exponentOf
private abbrev FiniteExponent {k : ℕ} (s : Finset (Option (Fin k × Exponent))) :=
  {x : Exponent // x ∈ supportExponents s}
private def restrictIndex {k : ℕ} (s : Finset (Option (Fin k × Exponent)))
    (x : {x // x ∈ s}) : Option (Fin k × FiniteExponent s) :=
  match h : x.1 with
  | none => none
  | some p => some (p.1, ⟨p.2, by
      exact mem_image.2 ⟨x.1, x.2, by simp only [exponentOf, h]⟩⟩)

private def forgetIndex {k : ℕ}
    (s : Finset (Option (Fin k × Exponent))) :
    Option (Fin k × FiniteExponent s) → Option (Fin k × Exponent) :=
  Option.map (fun p => (p.1, p.2.1))

private theorem forgetIndex_restrictIndex {k : ℕ}
    (s : Finset (Option (Fin k × Exponent))) (x : {x // x ∈ s}) :
    forgetIndex s (restrictIndex s x) = x.1 := by
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

private theorem restrictIndex_injective {k : ℕ} (s : Finset (Option (Fin k × Exponent))) :
    Function.Injective (restrictIndex s) := by
  intro x y hxy
  apply Subtype.ext
  calc
    x.1 = forgetIndex s (restrictIndex s x) := (forgetIndex_restrictIndex s x).symm
    _ = forgetIndex s (restrictIndex s y) := congrArg (forgetIndex s) hxy
    _ = y.1 := forgetIndex_restrictIndex s y

theorem one_entireSeries_linearIndependent
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    LinearIndependent ℚ (fun x : Option (Fin k × Exponent) => match x with
      | none => (1 : ℝ)
      | some p => entireSeries a B hk r kind p) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let alpha : FiniteExponent s → ℝ := fun x => (x.1 : ℝ)
  have hα : ∀ x, 0 < alpha x ∧ alpha x ≤ 1 := fun x => x.1.2
  have hinj : Function.Injective alpha := fun x y h => Subtype.ext (Subtype.ext h)
  have hfinite := residue_one_linearIndependent ha hB hk r kind alpha hα hinj hκ hc hG hω hsum hcal hS hT
  have hcomp := hfinite.comp (restrictIndex s) (restrictIndex_injective s)
  convert hcomp using 1
  funext x
  rcases x with ⟨x, hx⟩
  cases x <;> rfl


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
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion B (integerSeries a B P kind alpha) := by
  have hlead : (fun _ : Fin 1 => P.leadingCoeff) ≠ 0 := by
    intro hz
    exact (Polynomial.leadingCoeff_ne_zero.2
      (ne_zero_of_natDegree_gt (zero_lt_one.trans_le hdeg))) (congrFun hz (0 : Fin 1))
  have he : 0 < alpha * (P.natDegree : ℝ) :=
    mul_pos hα (Nat.cast_pos.2 (zero_lt_one.trans_le hdeg))
  have hW := CoreGeneralScaledGapPositiveST.observableFullSeries_weyl ha hB
    (by norm_num : 0 < (1 : ℕ)) (0 : Fin 1)
    (fun _ q => roundedPolynomialIncrement P kind alpha q)
    (roundedPolynomialLinearConstant_nonneg P (alpha := alpha))
    (fun _ q hq => roundedPolynomialIncrement_abs_le_linear P kind hα hdeg hαdeg hq)
    he hαdeg (fun _ : Fin 1 => P.leadingCoeff) hlead
    (roundedPolynomial_compactScaling P kind hα hdeg) hκ hc hG hω hsum hcal hS hT
  simpa only [pow_one, integerSeries_eq] using hW

theorem rationalSeries_normal
    {a : ℕ → ℕ} (ha : StrictMono a) {B : ℕ} (hB : 2 ≤ B)
    (P : ℚ[X]) (kind : RoundKind) {alpha κ : ℝ} (hα : 0 < alpha)
    (hdeg : 1 ≤ P.natDegree) (hαdeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal B (rationalSeries a B P kind alpha) := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hg := CoreGeneralScaledGapPositiveST.gap_growth ha hκp hc hG hω hsum hcal hS hT
  have hW := integerSeries_weyl ha hB (clearedRatPolynomial P) kind hα
    (by simpa only [clearedRatPolynomial_natDegree] using hdeg)
    (by simpa only [clearedRatPolynomial_natDegree] using hαdeg) hκ hc hG hω hsum hcal hS hT
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


/-- The positive real-cutoff comparison is an actual integral inequality,
not a claim of complex S and not a model-reference assumption. -/
def RealShapeS (a : ℕ → ℕ) (κ : ℝ) (G : ℕ → ℝ)
    (cutoffs : ℕ → ProbabilityMeasure ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ X in atTop, ∀ f : Finset ℕ → ℝ,
    (∀ U ∈ (offsetWindow (span κ G X)).powerset.filter
      (fun U => U.card = rank κ G X), 0 ≤ f U) →
    (∀ U ∈ (offsetWindow (span κ G X)).powerset.filter
      (fun U => U.card = rank κ G X), f U ≤ 1) →
    Stopped.failureMass (offsetWindow (span κ G X))
      (CoreSequencePatternLaw.patternMass a X (offsetWindow (span κ G X))) (rank κ G X) +
      shapeMean (offsetWindow (span κ G X))
        (CoreSequencePatternLaw.patternMass a X (offsetWindow (span κ G X))) (rank κ G X) f ≤
      c * (∫ y : ℝ, shapeMean (offsetWindow (span κ G X))
        (actualRootLaw (Nat.floor y) (span κ G X)) (rank κ G X) f
          ∂(cutoffs X : Measure ℝ)) + ε

theorem real_modelExpectation_eq (μ : ProbabilityMeasure ℝ) {N : ℕ}
    (hz : ∀ y, N ≤ y → CoreCalibratedRealCutoff.cutoffPMF μ y = 0)
    (S L : ℕ) (f : Finset ℕ → ℝ) :
    (∫ y : ℝ, shapeMean (offsetWindow S) (actualRootLaw (Nat.floor y) S) L f
      ∂(μ : Measure ℝ)) =
      shapeMean (offsetWindow S) (CoreCalibratedMixtureMoments.law
        (fun y => (CoreCalibratedRealCutoff.cutoffPMF μ y).toReal) S) L f := by
  have hshape (Ω : Finset ℕ) (ν : Finset ℕ → ℝ) :
      complexShapeMean Ω ν L (fun U => (f U : ℂ)) = (shapeMean Ω ν L f : ℂ) := by
    simp only [complexShapeMean, shapeMean, Complex.ofReal_sum, Complex.ofReal_mul]
  have hh := CoreGeneralRealCutoff.modelExpectation_eq μ hz S L (fun U => (f U : ℂ))
  simp_rw [hshape, integral_complex_ofReal] at hh
  exact Complex.ofReal_injective hh

theorem shapeS_of_real {a : ℕ → ℕ} {κ c : ℝ} {G : ℕ → ℝ}
    (hG : Tendsto G atTop atTop) {cutoffs : ℕ → ProbabilityMeasure ℝ}
    (hcal : CoreGeneralRealCutoff.Calibration cutoffs G)
    (hS : RealShapeS a κ G cutoffs c) :
    ShapeS a κ G (CoreGeneralRealCutoff.weights cutoffs) c := by
  intro ε hε
  filter_upwards [hS ε hε, hG.eventually_gt_atTop 0, hcal 1 (by norm_num)]
    with X hx hg hcalX
  obtain ⟨N, hz, _, _⟩ :=
    CoreCalibratedRealCutoff.exists_finite_floor_representation (cutoffs X) hg hcalX
  intro f hf0 hf1
  have hh := hx f hf0 hf1
  rw [real_modelExpectation_eq (cutoffs X) hz] at hh
  exact hh

theorem scaled_observable_normal_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1) (b : Fin k → ℤ) (hb : b ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent b)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : RealShapeS a κ G μ c) (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal (B ^ k) (observableFullSeries B hk r F (seqGap a)) ∧
      PrimeGapNormality.BFree.IsNormal B (observableFullSeries B hk r F (seqGap a)) :=
  CoreGeneralScaledGapPositiveST.observableFullSeries_normal ha hB hk r F hC hF
    he he1 b hb hscale hκ hc hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (shapeS_of_real hG hcal hS) hT

theorem residue_jointWeyl_realCutoff
    {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (hinj : Function.Injective alpha) {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : RealShapeS a κ G μ c) (hT : MeanGapTailT a (localTailBase κ) G) :
    JointWeyl (fun _ : Fin k × I => B ^ k) (residueSeries a B hk r kind alpha) :=
  residue_jointWeyl ha hB hk r kind alpha hα hinj hκ hc hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (shapeS_of_real hG hcal hS) hT

theorem one_entireSeries_linearIndependent_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : RealShapeS a κ G μ c) (hT : MeanGapTailT a (localTailBase κ) G) :
    LinearIndependent ℚ (fun x : Option (Fin k × Exponent) => match x with
      | none => (1 : ℝ)
      | some p => entireSeries a B hk r kind p) :=
  one_entireSeries_linearIndependent ha hB hk r kind hκ hc hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (shapeS_of_real hG hcal hS) hT

theorem rationalSeries_normal_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B : ℕ} (hB : 2 ≤ B)
    (P : ℚ[X]) (kind : RoundKind) {alpha κ : ℝ} (hα : 0 < alpha)
    (hdeg : 1 ≤ P.natDegree) (hαdeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration μ G)
    (hS : RealShapeS a κ G μ c) (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal B (rationalSeries a B P kind alpha) :=
  rationalSeries_normal ha hB P kind hα hdeg hαdeg hκ hc hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (shapeS_of_real hG hcal hS) hT

end
end PrimeGapNormality.Prime.CoreGeneralRoundedPositive
