import PrimeGapNormality.Prime.CoreRoundedRoughNormality

/-! Rational polynomial compositions for the actual moving-rough gaps. -/

namespace PrimeGapNormality.Prime.CoreRoundedRoughPolynomial

open Finset Filter Polynomial CoreCyclic
open CoreRoundedPowerScaling CoreRoundedPolynomialScaling
open CoreIntegerGapObservable CoreRoughThreshold CoreRoughSyntheticScale
open CoreMovingRoughSequence CoreSequenceSTConsumer
open scoped Topology Classical

noncomputable section

private def roughSeq (Ψ : ℝ → ℝ) := movingRoughSequence (zPsi Ψ)
private def roughT (Ψ : ℝ → ℝ) (X : ℕ) := roughSyntheticScale (zPsi Ψ X)

private theorem observablePolynomial_eq
    (Ψ : ℝ → ℝ) (B : ℕ) (P : ℤ[X]) (kind : RoundKind) (alpha : ℝ) :
    observableFullSeries B (by omega : 0 < (1 : ℕ)) ⟨0, by omega⟩
      (fun _ q => roundedPolynomialIncrement P kind alpha q) (seqGap (roughSeq Ψ)) =
      CoreRoundedRoughNormality.movingRoughRoundedPolynomialSeries Ψ B P kind alpha := by
  unfold observableFullSeries observableSeries observableValue
    CoreRoundedRoughNormality.movingRoughRoundedPolynomialSeries
  apply tsum_congr
  intro n
  change (roundedPolynomialIncrement P kind alpha
      (seqGap (movingRoughSequence (zPsi Ψ)) (0 + n)) : ℝ) / (B : ℝ) ^ (n + 1) =
    (roundedPolynomialIncrement P kind alpha
      (seqGap (movingRoughSequence (zPsi Ψ)) n) : ℝ) / (B : ℝ) ^ (n + 1)
  simp only [Nat.zero_add]

/-- Weyl form of the integer-polynomial rough endpoint. -/
theorem movingRough_roundedPolynomial_weyl
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B) (P : ℤ[X]) (kind : RoundKind)
    {alpha : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    weylCriterion B
      (CoreRoundedRoughNormality.movingRoughRoundedPolynomialSeries
        Ψ B P kind alpha) := by
  let a := roughSeq Ψ
  let T := roughT Ψ
  let F : Fin 1 → ℕ → ℤ := fun _ q => roundedPolynomialIncrement P kind alpha q
  let exponent := alpha * (P.natDegree : ℝ)
  let lead : Fin 1 → ℤ := fun _ => P.leadingCoeff
  have ha : StrictMono a := movingRoughSequence_strictMono hSlope.eventually_zPsi_lt
  have hT : Tendsto T atTop atTop := by
    change Tendsto (fun X : ℕ => roughSyntheticScale (zPsi Ψ X)) atTop atTop
    exact CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope
  have hTail : GapTailT a (localTailBase κ) (windowG ∘ T) := by
    change GapTailT (movingRoughSequence (zPsi Ψ)) (localTailBase κ)
      (windowG ∘ fun X : ℕ => roughSyntheticScale (zPsi Ψ X))
    exact CoreRoughLocalNormality.movingRough_gapTailT hκpos hSlope hC hreg
  have hS : SequencePositiveShapeS a T κ 1 := by
    change SequencePositiveShapeS (movingRoughSequence (zPsi Ψ))
      (fun X : ℕ => roughSyntheticScale (zPsi Ψ X)) κ 1
    exact CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
  have hexp : 0 < exponent := mul_pos halpha
    (Nat.cast_pos.mpr (zero_lt_one.trans_le hdeg))
  have hlead : lead ≠ 0 := by
    have hp := Polynomial.leadingCoeff_ne_zero.mpr
      (ne_zero_of_natDegree_gt (zero_lt_one.trans_le hdeg))
    intro hz
    exact hp (congrFun hz ⟨0, by omega⟩)
  have hscale : CoreScaledGapModelReference.CompactScaling F exponent lead := by
    simpa only [F, exponent, lead] using
      CoreRoundedPolynomialNormality.roundedPolynomial_compactScaling P kind halpha hdeg
  have hlin : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤
      roundedPolynomialLinearConstant P alpha * (q : ℝ) := by
    intro s q hq
    exact roundedPolynomialIncrement_abs_le_linear P kind halpha hdeg halphaDeg hq
  have hw := CoreScaledGapSTNormality.observableFullSeries_weyl_clock_of_shapeS
    ha hB (by omega : 0 < (1 : ℕ)) ⟨0, by omega⟩ F
    (roundedPolynomialLinearConstant_nonneg P) hlin hexp halphaDeg lead hlead
    hscale hκ (by norm_num : (0 : ℝ) < 1) hT hTail hS
  have hwB := weylCriterion_of_pow hB (by omega : 1 ≤ (1 : ℕ)) hw
  simpa only [pow_one, F, a, observablePolynomial_eq Ψ B P kind alpha] using hwB

def movingRoughRoundedRatPolynomialRootedSeries
    (Ψ : ℝ → ℝ) (B : ℕ) (P : ℚ[X]) (kind : RoundKind) (alpha : ℝ) : ℝ :=
  ∑' n : ℕ,
    ((P.eval ((roundedPower kind alpha (seqGap (roughSeq Ψ) n)).toNat : ℚ) -
      P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1)

def movingRoughRoundedRatPolynomialSeries
    (Ψ : ℝ → ℝ) (B : ℕ) (P : ℚ[X]) (kind : RoundKind) (alpha : ℝ) : ℝ :=
  ∑' n : ℕ,
    ((P.eval ((roundedPower kind alpha (seqGap (roughSeq Ψ) n)).toNat : ℚ) : ℚ) : ℝ) /
      (B : ℝ) ^ (n + 1)

private theorem clear_increment
    (P : ℚ[X]) (kind : RoundKind) {alpha : ℝ} (halpha : 0 < alpha) (q : ℕ) :
    (roundedPolynomialIncrement (CoreRoundedPolynomialNormality.clearedRatPolynomial P)
      kind alpha q : ℝ) =
      (ratPolyDenProd P : ℝ) *
        ((P.eval ((roundedPower kind alpha q).toNat : ℚ) - P.eval 0 : ℚ) : ℝ) := by
  let x : ℕ := (roundedPower kind alpha q).toNat
  have hnon := roundedPower_nonneg kind halpha q
  have hx : (x : ℤ) = roundedPower kind alpha q := by
    dsimp only [x]
    exact Int.toNat_of_nonneg hnon
  have hevalRounded :
      ((Polynomial.eval (roundedPower kind alpha q)
          (CoreRoundedPolynomialNormality.clearedRatPolynomial P) : ℤ) : ℝ) =
        (ratPolyDenProd P : ℝ) * ((Polynomial.eval (x : ℚ) P : ℚ) : ℝ) := by
    rw [← hx]
    exact CoreRoundedPolynomialNormality.clearedRatPolynomial_eval_cast P x
  have hevalZero :
      ((Polynomial.eval (0 : ℤ)
          (CoreRoundedPolynomialNormality.clearedRatPolynomial P) : ℤ) : ℝ) =
        (ratPolyDenProd P : ℝ) * ((Polynomial.eval (0 : ℚ) P : ℚ) : ℝ) := by
    simpa only [Nat.cast_zero] using
      CoreRoundedPolynomialNormality.clearedRatPolynomial_eval_cast P 0
  unfold roundedPolynomialIncrement
  rw [Int.cast_sub, hevalRounded, hevalZero, Rat.cast_sub]
  dsimp only [x]
  ring

private theorem clearedSeries_eq
    (Ψ : ℝ → ℝ) {B : ℕ} (P : ℚ[X]) (kind : RoundKind)
    {alpha : ℝ} (halpha : 0 < alpha) :
    CoreRoundedRoughNormality.movingRoughRoundedPolynomialSeries Ψ B
        (CoreRoundedPolynomialNormality.clearedRatPolynomial P) kind alpha =
      (ratPolyDenProd P : ℝ) *
        movingRoughRoundedRatPolynomialRootedSeries Ψ B P kind alpha := by
  unfold CoreRoundedRoughNormality.movingRoughRoundedPolynomialSeries
    movingRoughRoundedRatPolynomialRootedSeries
  change (∑' n : ℕ,
      (roundedPolynomialIncrement (CoreRoundedPolynomialNormality.clearedRatPolynomial P)
        kind alpha (seqGap (movingRoughSequence (zPsi Ψ)) n) : ℝ) / (B : ℝ) ^ (n + 1)) =
    (ratPolyDenProd P : ℝ) * (∑' n : ℕ,
      ((P.eval ((roundedPower kind alpha (seqGap (movingRoughSequence (zPsi Ψ)) n)).toNat : ℚ) -
        P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1))
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [clear_increment P kind halpha]
  simp only [Rat.cast_sub]
  ring

private theorem full_eq_rooted_add
    (Ψ : ℝ → ℝ) {B : ℕ} (hB : 2 ≤ B) (P : ℚ[X])
    (kind : RoundKind) (alpha : ℝ)
    (hsRoot : Summable (fun n : ℕ =>
      ((P.eval ((roundedPower kind alpha (seqGap (roughSeq Ψ) n)).toNat : ℚ) -
        P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1))) :
    movingRoughRoundedRatPolynomialSeries Ψ B P kind alpha =
      movingRoughRoundedRatPolynomialRootedSeries Ψ B P kind alpha +
        ((P.eval 0 : ℚ) : ℝ) / ((B : ℝ) - 1) := by
  have hsConst : Summable (fun n : ℕ =>
      ((P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1)) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (summable_one_div_pow_succ
        (by exact_mod_cast (show 1 < B by omega))).mul_left ((P.eval 0 : ℚ) : ℝ)
  have hconst : (∑' n : ℕ, ((P.eval 0 : ℚ) : ℝ) /
      (B : ℝ) ^ (n + 1)) = ((P.eval 0 : ℚ) : ℝ) / ((B : ℝ) - 1) := by
    rw [show (fun n : ℕ => ((P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1)) =
      fun n => ((P.eval 0 : ℚ) : ℝ) * ((1 : ℝ) / (B : ℝ) ^ (n + 1)) by
        funext n; ring, tsum_mul_left, tsum_inv_pow_succ hB]
    ring
  unfold movingRoughRoundedRatPolynomialSeries
    movingRoughRoundedRatPolynomialRootedSeries
  rw [← hconst, ← hsRoot.tsum_add hsConst]
  apply tsum_congr
  intro n
  push_cast
  ring

theorem movingRough_roundedRatPolynomial_isNormal
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B) (P : ℚ[X]) (kind : RoundKind)
    {alpha : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    PrimeGapNormality.BFree.IsNormal B
      (movingRoughRoundedRatPolynomialSeries Ψ B P kind alpha) := by
  let Q := CoreRoundedPolynomialNormality.clearedRatPolynomial P
  have hdegQ : 1 ≤ Q.natDegree := by
    simpa only [Q, CoreRoundedPolynomialNormality.clearedRatPolynomial_natDegree] using hdeg
  have hboundQ : alpha * (Q.natDegree : ℝ) ≤ 1 := by
    simpa only [Q, CoreRoundedPolynomialNormality.clearedRatPolynomial_natDegree] using halphaDeg
  have hW := movingRough_roundedPolynomial_weyl hκpos hSlope hC hreg hB Q kind
    halpha hdegQ hboundQ hκ
  rw [clearedSeries_eq Ψ P kind halpha] at hW
  have hD : 1 ≤ ratPolyDenProd P := by
    unfold ratPolyDenProd
    exact prod_pos fun i hi => (P.coeff i).den_pos
  have hroot := weylCriterion_of_mul hD hB hW
  have hDpos : (0 : ℝ) < ratPolyDenProd P :=
    Nat.cast_pos.mpr (by omega : 0 < ratPolyDenProd P)
  have hsQ : Summable (fun n : ℕ =>
      (roundedPolynomialIncrement Q kind alpha (seqGap (roughSeq Ψ) n) : ℝ) /
        (B : ℝ) ^ (n + 1)) := by
    -- The actual rough gaps are subexponential, derived from S/T above.
    let a := roughSeq Ψ
    let T := roughT Ψ
    have ha : StrictMono a := movingRoughSequence_strictMono hSlope.eventually_zPsi_lt
    have hTail : GapTailT a (localTailBase κ) (windowG ∘ T) := by
      change GapTailT (movingRoughSequence (zPsi Ψ)) (localTailBase κ)
        (windowG ∘ fun X : ℕ => roughSyntheticScale (zPsi Ψ X))
      exact CoreRoughLocalNormality.movingRough_gapTailT hκpos hSlope hC hreg
    have hS : SequencePositiveShapeS a T κ 1 := by
      change SequencePositiveShapeS (movingRoughSequence (zPsi Ψ))
        (fun X : ℕ => roughSyntheticScale (zPsi Ψ X)) κ 1
      exact CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
    have hT : Tendsto T atTop atTop := by
      change Tendsto (fun X : ℕ => roughSyntheticScale (zPsi Ψ X)) atTop atTop
      exact CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope
    have hcount := CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
      ha hκpos (by norm_num : (0 : ℝ) < 1) hT hS hTail
    have hg := CoreSequenceSubexponentialGrowth.sequenceGap_hasSubexponentialGrowth ha hcount
    have hGapPos : ∀ n : ℕ, 1 ≤ seqGap a n := by
      intro n
      unfold seqGap
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.sub_ne_zero_of_lt (ha (Nat.lt_succ_self n)))
    have hv : CoreSequenceSubexponentialGrowth.HasSubexponentialGrowth
        (fun n => (roundedPolynomialIncrement Q kind alpha (seqGap a n) : ℝ)) := by
      intro rho hrho
      obtain ⟨D, hD0, hh⟩ := hg rho hrho
      let M := roundedPolynomialLinearConstant Q alpha
      refine ⟨M * D, mul_nonneg (roundedPolynomialLinearConstant_nonneg Q (alpha := alpha)) hD0, ?_⟩
      intro n
      have hp := roundedPolynomialIncrement_abs_le_linear Q kind halpha hdegQ hboundQ
        (hGapPos n)
      simpa only [M, mul_assoc] using hp.trans (mul_le_mul_of_nonneg_left
        (by simpa only [abs_of_nonneg (show (0 : ℝ) ≤ (seqGap a n : ℝ) from
          Nat.cast_nonneg _)] using hh n)
        (roundedPolynomialLinearConstant_nonneg Q (alpha := alpha)))
    exact hv.summable_div_pow_succ (by exact_mod_cast (show 1 < B by omega))
  have hsRoot : Summable (fun n : ℕ =>
      ((P.eval ((roundedPower kind alpha (seqGap (roughSeq Ψ) n)).toNat : ℚ) -
        P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1)) := by
    apply (hsQ.mul_left (ratPolyDenProd P : ℝ)⁻¹).congr
    intro n
    dsimp only [Q]
    rw [clear_increment P kind halpha]
    field_simp [hDpos.ne']
  have hfull := CoreRationalAffine.weylCriterion_add_rat hB
    (P.eval 0 / (B - 1 : ℕ)) hroot
  have heq := full_eq_rooted_add Ψ hB P kind alpha hsRoot
  apply CoreWeylNormality.isNormal_of_weyl hB
  rw [heq]
  have hcast : (((P.eval 0 / (B - 1 : ℕ) : ℚ) : ℝ)) =
      ((P.eval 0 : ℚ) : ℝ) / ((B : ℝ) - 1) := by
    rw [Rat.cast_div, Rat.cast_natCast, Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_one]
  rwa [hcast] at hfull

end

end PrimeGapNormality.Prime.CoreRoundedRoughPolynomial
