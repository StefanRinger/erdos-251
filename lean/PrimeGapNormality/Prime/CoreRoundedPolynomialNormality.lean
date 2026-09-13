import PrimeGapNormality.Prime.CoreScaledGapModelReference
import PrimeGapNormality.Prime.CoreRoundedPolynomialScaling
import PrimeGapNormality.Prime.CoreRoundedPrimeNormality

/-!
# Polynomial compositions of rounded prime-gap powers

For an integer polynomial `P` of positive degree this file treats the
literal rooted observable

`P(round(q^alpha)) - P(0)`.

It is not identified with `round(q^(alpha*degree P))`.  Instead the actual
compact expansion and linear bound from `CoreRoundedPolynomialScaling`
instantiate the deterministic scaled-observable model.  Both floor and
ceiling are covered by one fixed `RoundKind`; no mixed assertion is made.
-/

namespace PrimeGapNormality.Prime.CoreRoundedPolynomialNormality

open Finset Filter Polynomial CoreCyclic
open CoreRoundedPowerScaling CoreRoundedPolynomialScaling
open CoreIntegerGapObservable
open CoreSequenceSubexponentialGrowth
open scoped Topology Classical NNReal BoundedContinuousFunction

noncomputable section

/-- Literal rooted integer-polynomial series. -/
def roundedPolynomialSeries
    (B : ℕ) (P : ℤ[X]) (kind : RoundKind) (alpha : ℝ) : ℝ :=
  ∑' n : ℕ, (roundedPolynomialIncrement P kind alpha (primeGap n) : ℝ) /
    (B : ℝ) ^ (n + 1)

private theorem finOne_pos : 0 < (1 : ℕ) := by omega
private def finOneZero : Fin 1 := ⟨0, by omega⟩

private theorem primeGap_one_le (n : ℕ) : 1 ≤ primeGap n := by
  unfold primeGap
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.sub_ne_zero_of_lt (nthPrime_strictMono (Nat.lt_succ_self n)))

private theorem primeGap_subexponential :
    HasSubexponentialGrowth (fun n => (primeGap n : ℝ)) := by
  have hcount : WindowCountToInfinity nthPrime := by
    have hreal := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      CorePrimeDensity.tendsto_windowNX_atTop
    simpa only [WindowCountToInfinity, seqWindow_nthPrime_card,
      Function.comp_def] using hreal
  simpa only [seqGap_nthPrime] using
    (sequenceGap_hasSubexponentialGrowth nthPrime_strictMono hcount)

theorem observableFullSeries_finOne_eq
    (B : ℕ) (P : ℤ[X]) (kind : RoundKind) (alpha : ℝ) :
    observableFullSeries B finOne_pos finOneZero
      (fun _ q => roundedPolynomialIncrement P kind alpha q) primeGap =
      roundedPolynomialSeries B P kind alpha := by
  unfold observableFullSeries observableSeries observableValue
    roundedPolynomialSeries
  apply tsum_congr
  intro n
  congr 2
  simp only [Nat.zero_add]

theorem roundedPolynomial_compactScaling
    (P : ℤ[X]) (kind : RoundKind) {alpha : ℝ}
    (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree) :
    CoreScaledGapModelReference.CompactScaling
      (fun _ q => roundedPolynomialIncrement P kind alpha q)
      (alpha * (P.natDegree : ℝ)) (fun _ : Fin 1 => P.leadingCoeff) := by
  intro A hA eps heps
  have hh := eventually_roundedPolynomial_compact_expansion
    P kind halpha hdeg hA eps heps
  filter_upwards [hh] with G hG
  intro s q hq
  simpa only using hG q hq

private theorem leadingColumn_ne_zero
    (P : ℤ[X]) (hdeg : 1 ≤ P.natDegree) :
    (fun _ : Fin 1 => P.leadingCoeff) ≠ 0 := by
  have hP : P ≠ 0 := ne_zero_of_natDegree_gt (zero_lt_one.trans_le hdeg)
  have hlead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  intro hz
  exact hlead (congrFun hz finOneZero)

/-- Actual D gives Weyl for the rooted literal integer-polynomial series. -/
theorem roundedPolynomial_weyl_of_D
    {B : ℕ} (hB : 2 ≤ B) (P : ℤ[X]) (kind : RoundKind)
    {alpha κ : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {d0 c : ℝ} (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    weylCriterion B (roundedPolynomialSeries B P kind alpha) := by
  let Fobs : Fin 1 → ℕ → ℤ :=
    fun _ q => roundedPolynomialIncrement P kind alpha q
  let a : ℝ := alpha * (P.natDegree : ℝ)
  let b : Fin 1 → ℤ := fun _ => P.leadingCoeff
  have ha : 0 < a := mul_pos halpha (Nat.cast_pos.mpr
    (zero_lt_one.trans_le hdeg))
  have hb : b ≠ 0 := leadingColumn_ne_zero P hdeg
  have hscale : CoreScaledGapModelReference.CompactScaling Fobs a b := by
    simpa only [Fobs, a, b] using roundedPolynomial_compactScaling P kind halpha hdeg
  let C := roundedPolynomialLinearConstant P alpha
  have hC : 0 ≤ C := roundedPolynomialLinearConstant_nonneg P
  have hlin : ∀ s q, 1 ≤ q → |(Fobs s q : ℝ)| ≤ C * (q : ℝ) := by
    intro s q hq
    exact roundedPolynomialIncrement_abs_le_linear P kind halpha hdeg
      halphaDeg hq
  have href := CoreScaledGapModelReference.subsequenceReference_of_D
    hB finOne_pos finOneZero Fobs ha halphaDeg b hb hscale hC hlin
    hκ hd0 hc hD
  have hW := CoreRoundedPrimeNormality.observableFullSeries_weyl_clock_of_subsequence_reference
    hB finOne_pos finOneZero Fobs hC hlin href
  simpa only [pow_one, observableFullSeries_finOne_eq B P kind alpha,
    Fobs] using hW

theorem roundedPolynomial_isNormal_of_D
    {B : ℕ} (hB : 2 ≤ B) (P : ℤ[X]) (kind : RoundKind)
    {alpha κ : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {d0 c : ℝ} (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    PrimeGapNormality.BFree.IsNormal B (roundedPolynomialSeries B P kind alpha) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (roundedPolynomial_weyl_of_D hB P kind halpha hdeg halphaDeg
      hκ hd0 hc hD)

theorem roundedPolynomial_isNormal_of_AHL
    {B : ℕ} (hB : 2 ≤ B) (P : ℤ[X]) (kind : RoundKind)
    {alpha κ : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκpos : 0 < κ) (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hAHL : ahlSmall_AHL κ 20) :
    PrimeGapNormality.BFree.IsNormal B (roundedPolynomialSeries B P kind alpha) :=
  roundedPolynomial_isNormal_of_D hB P kind halpha hdeg halphaDeg hκ
    (by norm_num) (by norm_num)
    (CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκpos hAHL)

theorem roundedPolynomial_isNormal_of_kuperberg
    {B : ℕ} (hB : 2 ≤ B) (P : ℤ[X]) (kind : RoundKind)
    {alpha κ : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hK : KuperbergConj13) :
    PrimeGapNormality.BFree.IsNormal B (roundedPolynomialSeries B P kind alpha) := by
  have hκpos : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  exact roundedPolynomial_isNormal_of_D hB P kind halpha hdeg halphaDeg hκ
    (by norm_num) (by norm_num) (coreLinearD_of_kuperberg hK hκpos)

/-! ## Rational polynomials by an actual common denominator -/

/-- An integer coefficient whose real cast is the common denominator times
the corresponding rational coefficient. -/
noncomputable def clearedRatCoeff (P : ℚ[X]) (i : ℕ) : ℤ :=
  Classical.choose (exists_int_mul_coeff_ratPolyDenProd P i)

theorem clearedRatCoeff_cast (P : ℚ[X]) (i : ℕ) :
    (clearedRatCoeff P i : ℝ) =
      (ratPolyDenProd P : ℝ) * (P.coeff i : ℝ) := by
  exact (Classical.choose_spec (exists_int_mul_coeff_ratPolyDenProd P i)).symm

/-- Literal denominator-cleared integer polynomial. -/
noncomputable def clearedRatPolynomial (P : ℚ[X]) : ℤ[X] :=
  ∑ i ∈ range (P.natDegree + 1), monomial i (clearedRatCoeff P i)

private theorem ratPolyDenProd_pos (P : ℚ[X]) : 0 < ratPolyDenProd P := by
  unfold ratPolyDenProd
  exact prod_pos fun i hi => (P.coeff i).den_pos

theorem clearedRatPolynomial_coeff (P : ℚ[X]) (i : ℕ) :
    (clearedRatPolynomial P).coeff i = clearedRatCoeff P i := by
  classical
  by_cases hi : i ∈ range (P.natDegree + 1)
  · unfold clearedRatPolynomial
    rw [Polynomial.finsetSum_coeff]
    rw [sum_eq_single i]
    · simp
    · intro j hj hji
      simp [coeff_monomial, hji]
    · exact fun h => (h hi).elim
  · have hPi : P.coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (by
        have hle : P.natDegree + 1 ≤ i := Nat.not_lt.mp (mt mem_range.mpr hi)
        omega)
    have hci : clearedRatCoeff P i = 0 := by
      apply (Int.cast_injective (α := ℝ))
      rw [clearedRatCoeff_cast, hPi]
      simp
    unfold clearedRatPolynomial
    rw [Polynomial.finsetSum_coeff]
    rw [sum_eq_zero]
    · exact hci.symm
    · intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hi hj
      simp [coeff_monomial, hji]

/-- Coefficientwise clearing identity over the reals. -/
theorem map_clearedRatPolynomial (P : ℚ[X]) :
    mapIntPoly (clearedRatPolynomial P) =
      C (ratPolyDenProd P : ℝ) * mapRatPoly P := by
  ext i
  rw [mapIntPoly_coeff, coeff_C_mul, mapRatPoly_coeff,
    clearedRatPolynomial_coeff, clearedRatCoeff_cast]

theorem clearedRatPolynomial_natDegree (P : ℚ[X]) :
    (clearedRatPolynomial P).natDegree = P.natDegree := by
  have hD : (ratPolyDenProd P : ℝ) ≠ 0 := by
    exact_mod_cast (ratPolyDenProd_pos P).ne'
  calc
    (clearedRatPolynomial P).natDegree =
        (mapIntPoly (clearedRatPolynomial P)).natDegree := by
      unfold mapIntPoly
      exact (natDegree_map_eq_of_injective Int.cast_injective _).symm
    _ = (C (ratPolyDenProd P : ℝ) * mapRatPoly P).natDegree := by
      rw [map_clearedRatPolynomial]
    _ = (mapRatPoly P).natDegree := natDegree_C_mul hD
    _ = P.natDegree := by
      unfold mapRatPoly
      exact natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective _

/-- Evaluation form of common-denominator clearing at natural integers. -/
theorem clearedRatPolynomial_eval_cast (P : ℚ[X]) (x : ℕ) :
    ((Polynomial.eval (x : ℤ) (clearedRatPolynomial P) : ℤ) : ℝ) =
      (ratPolyDenProd P : ℝ) *
        ((Polynomial.eval (x : ℚ) P : ℚ) : ℝ) := by
  have hh := congrArg (Polynomial.eval (x : ℝ)) (map_clearedRatPolynomial P)
  rw [eval_mapIntPoly, eval_mul, eval_C, eval_mapRatPoly_nat] at hh
  exact hh

/-- Literal rooted rational-polynomial series.  The `toNat` is exactly the
nonnegative floor or ceiling integer. -/
def roundedRatPolynomialRootedSeries
    (B : ℕ) (P : ℚ[X]) (kind : RoundKind) (alpha : ℝ) : ℝ :=
  ∑' n : ℕ,
    ((((Polynomial.eval
      ((roundedPower kind alpha (primeGap n)).toNat : ℚ) P) - P.eval 0 : ℚ) : ℝ) /
      (B : ℝ) ^ (n + 1))

def roundedRatPolynomialSeries
    (B : ℕ) (P : ℚ[X]) (kind : RoundKind) (alpha : ℝ) : ℝ :=
  ∑' n : ℕ,
    (((Polynomial.eval
      ((roundedPower kind alpha (primeGap n)).toNat : ℚ) P : ℚ) : ℝ) /
      (B : ℝ) ^ (n + 1))

private theorem cleared_increment_eq
    (P : ℚ[X]) (kind : RoundKind) {alpha : ℝ} (halpha : 0 < alpha) (q : ℕ) :
    (roundedPolynomialIncrement (clearedRatPolynomial P) kind alpha q : ℝ) =
      (ratPolyDenProd P : ℝ) *
        ((Polynomial.eval ((roundedPower kind alpha q).toNat : ℚ) P -
          P.eval 0 : ℚ) : ℝ) := by
  let x : ℕ := (roundedPower kind alpha q).toNat
  have hnon := roundedPower_nonneg kind halpha q
  have hx : (x : ℤ) = roundedPower kind alpha q := by
    dsimp only [x]
    exact Int.toNat_of_nonneg hnon
  have hevalRounded :
      ((Polynomial.eval (roundedPower kind alpha q)
          (clearedRatPolynomial P) : ℤ) : ℝ) =
        (ratPolyDenProd P : ℝ) *
          ((Polynomial.eval (x : ℚ) P : ℚ) : ℝ) := by
    rw [← hx]
    exact clearedRatPolynomial_eval_cast P x
  have hevalZero :
      ((Polynomial.eval (0 : ℤ) (clearedRatPolynomial P) : ℤ) : ℝ) =
        (ratPolyDenProd P : ℝ) *
          ((Polynomial.eval (0 : ℚ) P : ℚ) : ℝ) := by
    simpa only [Nat.cast_zero] using clearedRatPolynomial_eval_cast P 0
  unfold roundedPolynomialIncrement
  rw [Int.cast_sub, hevalRounded, hevalZero, Rat.cast_sub]
  dsimp only [x]
  ring

private theorem roundedPolynomialSeries_cleared_eq
    {B : ℕ} (hB : 2 ≤ B) (P : ℚ[X]) (kind : RoundKind)
    {alpha : ℝ} (halpha : 0 < alpha) :
    roundedPolynomialSeries B (clearedRatPolynomial P) kind alpha =
      (ratPolyDenProd P : ℝ) *
        roundedRatPolynomialRootedSeries B P kind alpha := by
  unfold roundedPolynomialSeries roundedRatPolynomialRootedSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [cleared_increment_eq P kind halpha]
  ring

/-- The literal unrooted rational series differs by the expected rational
geometric constant. -/
theorem roundedRatPolynomialSeries_eq_rooted_add
    {B : ℕ} (hB : 2 ≤ B) (P : ℚ[X]) (kind : RoundKind)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hdeg : 1 ≤ P.natDegree) (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1) :
    roundedRatPolynomialSeries B P kind alpha =
      roundedRatPolynomialRootedSeries B P kind alpha +
        ((P.eval 0 : ℚ) : ℝ) / ((B : ℝ) - 1) := by
  let Q := clearedRatPolynomial P
  have hdegQ : 1 ≤ Q.natDegree := by
    simpa only [Q, clearedRatPolynomial_natDegree] using hdeg
  have hdegBoundQ : alpha * (Q.natDegree : ℝ) ≤ 1 := by
    simpa only [Q, clearedRatPolynomial_natDegree] using halphaDeg
  have hsQ : Summable (fun n : ℕ =>
      (roundedPolynomialIncrement Q kind alpha (primeGap n) : ℝ) /
        (B : ℝ) ^ (n + 1)) := by
    let C := roundedPolynomialLinearConstant Q alpha
    have hg := primeGap_subexponential
    have hv : CoreSequenceSubexponentialGrowth.HasSubexponentialGrowth
        (fun n => (roundedPolynomialIncrement Q kind alpha (primeGap n) : ℝ)) := by
      intro rho hrho
      obtain ⟨D, hD, hgD⟩ := hg rho hrho
      refine ⟨C * D, mul_nonneg (roundedPolynomialLinearConstant_nonneg Q) hD, ?_⟩
      intro n
      have hlin := roundedPolynomialIncrement_abs_le_linear Q kind halpha
        hdegQ hdegBoundQ (primeGap_one_le n)
      simpa only [C, mul_assoc] using hlin.trans (mul_le_mul_of_nonneg_left
        (by simpa only [abs_of_nonneg (show (0 : ℝ) ≤ (primeGap n : ℝ) from
          Nat.cast_nonneg _)] using hgD n)
        (roundedPolynomialLinearConstant_nonneg Q))
    exact hv.summable_div_pow_succ
      (by exact_mod_cast (show 1 < B by omega))
  have hDpos : (0 : ℝ) < ratPolyDenProd P := by exact_mod_cast ratPolyDenProd_pos P
  have hsRoot : Summable (fun n : ℕ =>
      ((Polynomial.eval ((roundedPower kind alpha (primeGap n)).toNat : ℚ) P -
        P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1)) := by
    apply (hsQ.mul_left (ratPolyDenProd P : ℝ)⁻¹).congr
    intro n
    rw [cleared_increment_eq P kind halpha]
    field_simp [hDpos.ne']
  have hsConst : Summable (fun n : ℕ =>
      (((P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1))) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (summable_one_div_pow_succ
        (by exact_mod_cast (show 1 < B by omega))).mul_left ((P.eval 0 : ℚ) : ℝ)
  have hconstSum : (∑' n : ℕ,
      (((P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1))) =
      ((P.eval 0 : ℚ) : ℝ) / ((B : ℝ) - 1) := by
    calc
      (∑' n : ℕ, ((P.eval 0 : ℚ) : ℝ) / (B : ℝ) ^ (n + 1)) =
          ∑' n : ℕ, ((P.eval 0 : ℚ) : ℝ) *
            ((1 : ℝ) / (B : ℝ) ^ (n + 1)) := by
        apply tsum_congr
        intro n
        ring
      _ = ((P.eval 0 : ℚ) : ℝ) *
          (∑' n : ℕ, (1 : ℝ) / (B : ℝ) ^ (n + 1)) := tsum_mul_left
      _ = ((P.eval 0 : ℚ) : ℝ) / ((B : ℝ) - 1) := by
        rw [tsum_inv_pow_succ hB]
        ring
  unfold roundedRatPolynomialSeries roundedRatPolynomialRootedSeries
  have hadd := hsRoot.tsum_add hsConst
  rw [← hconstSum, ← hadd]
  apply tsum_congr
  intro n
  push_cast
  ring

/-- Actual rational-polynomial rounded series, including its constant
boundary, is normal. -/
theorem roundedRatPolynomial_isNormal_of_D
    {B : ℕ} (hB : 2 ≤ B) (P : ℚ[X]) (kind : RoundKind)
    {alpha κ : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {d0 c : ℝ} (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    PrimeGapNormality.BFree.IsNormal B
      (roundedRatPolynomialSeries B P kind alpha) := by
  let Q := clearedRatPolynomial P
  have hdegQ : 1 ≤ Q.natDegree := by
    simpa only [Q, clearedRatPolynomial_natDegree] using hdeg
  have hdegBoundQ : alpha * (Q.natDegree : ℝ) ≤ 1 := by
    simpa only [Q, clearedRatPolynomial_natDegree] using halphaDeg
  have hWQ := roundedPolynomial_weyl_of_D hB Q kind halpha hdegQ
    hdegBoundQ hκ hd0 hc hD
  rw [roundedPolynomialSeries_cleared_eq hB P kind halpha] at hWQ
  have hDnat : 1 ≤ ratPolyDenProd P := by
    have := ratPolyDenProd_pos P
    omega
  have hroot := weylCriterion_of_mul hDnat hB hWQ
  let q : ℚ := P.eval 0 / (B - 1 : ℕ)
  have hfull := CoreRationalAffine.weylCriterion_add_rat hB q hroot
  have heq := roundedRatPolynomialSeries_eq_rooted_add hB P kind halpha
    hdeg halphaDeg
  apply CoreWeylNormality.isNormal_of_weyl hB
  rw [heq]
  have hq : (q : ℝ) = ((P.eval 0 : ℚ) : ℝ) / ((B : ℝ) - 1) := by
    dsimp only [q]
    rw [Rat.cast_div, Rat.cast_natCast, Nat.cast_sub (by omega : 1 ≤ B),
      Nat.cast_one]
  rwa [hq] at hfull

theorem roundedRatPolynomial_isNormal_of_AHL
    {B : ℕ} (hB : 2 ≤ B) (P : ℚ[X]) (kind : RoundKind)
    {alpha κ : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκpos : 0 < κ) (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hAHL : ahlSmall_AHL κ 20) :
    PrimeGapNormality.BFree.IsNormal B
      (roundedRatPolynomialSeries B P kind alpha) :=
  roundedRatPolynomial_isNormal_of_D hB P kind halpha hdeg halphaDeg hκ
    (by norm_num) (by norm_num)
    (CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκpos hAHL)

theorem roundedRatPolynomial_isNormal_of_kuperberg
    {B : ℕ} (hB : 2 ≤ B) (P : ℚ[X]) (kind : RoundKind)
    {alpha κ : ℝ} (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hK : KuperbergConj13) :
    PrimeGapNormality.BFree.IsNormal B
      (roundedRatPolynomialSeries B P kind alpha) := by
  have hκpos : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  exact roundedRatPolynomial_isNormal_of_D hB P kind halpha hdeg halphaDeg hκ
    (by norm_num) (by norm_num) (coreLinearD_of_kuperberg hK hκpos)

end

end PrimeGapNormality.Prime.CoreRoundedPolynomialNormality
