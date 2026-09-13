import PrimeGapNormality.Prime.CorePrimeQuantitativeComparison
import PrimeGapNormality.Prime.CoreKuperbergQuantitativeBudget
import PrimeGapNormality.Prime.CoreFiniteOrbitDiscrepancy
import PrimeGapNormality.Prime.CoreLinearMeanNormalization

/-!
# Quantitative positive comparison for the prime-position orbit

The linear gap orbit is `(B-1)` times the prime-position orbit, up to the
integer Abel boundary.  A nonnegative test on the position circle is
therefore covered by the sum of that test over all `(B-1)` preimages.  The
cover has exactly `(B-1)` times the Haar integral, supremum at most
`(B-1)‖f‖`, and the same Lipschitz constant.

Combining this finite rational cover with the actual quantitative gap
comparison and the genuine Kuperberg `D(X,1)=O(1/L)` theorem produces the
literal finite positive-domination input used by the orbit-discrepancy
lemma.  No residue-class equidistribution is used.
-/

namespace PrimeGapNormality.Prime.CorePrimePositionQuantitativeComparison

open Filter Finset MeasureTheory Set
open CorePrimeQuantitativeComparison CoreFiniteOrbitDiscrepancy
open scoped Topology NNReal Classical BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1000000

abbrev Circle := AddCircle (1 : ℝ)

/-! ## The rational preimage cover -/

def rationalCoverReal (q : ℕ) (f : Circle → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ range q, f ((((j : ℝ) + x) / (q : ℝ) : ℝ) : Circle)

private theorem circle_natCast_eq_zero (j : ℕ) :
    ((j : ℝ) : Circle) = 0 := by
  have hh := AddCircle.coe_nsmul (p := (1 : ℝ)) (n := j) (x := (1 : ℝ))
  simpa only [nsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using hh

theorem rationalCoverReal_continuous (q : ℕ) (f : Circle →ᵇ ℝ) :
    Continuous (rationalCoverReal q f) := by
  unfold rationalCoverReal
  fun_prop

theorem rationalCoverReal_endpoints
    {q : ℕ} (hq : 0 < q) (f : Circle → ℝ) :
    rationalCoverReal q f 0 = rationalCoverReal q f 1 := by
  let g : ℕ → ℝ := fun j ↦ f (((j : ℝ) / (q : ℝ) : ℝ) : Circle)
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hlast : g q = g 0 := by
    dsimp only [g]
    rw [div_self hqR, Nat.cast_zero, zero_div,
      AddCircle.coe_period, AddCircle.coe_zero]
  have hleft : rationalCoverReal q f 0 = ∑ j ∈ range q, g j := by
    unfold rationalCoverReal
    apply sum_congr rfl
    intro j _
    dsimp only [g]
    congr 2
    ring
  have hright : rationalCoverReal q f 1 = ∑ j ∈ range q, g (j + 1) := by
    unfold rationalCoverReal
    apply sum_congr rfl
    intro j _
    dsimp only [g]
    congr 2
    push_cast
    ring
  rw [hleft, hright]
  have hs := Finset.sum_range_succ g q
  have hs' := Finset.sum_range_succ' g q
  rw [hlast] at hs
  linarith

/-- Sum of a test over all rational preimages of the circle multiplication
map. -/
def rationalCover (q : ℕ) (hq : 0 < q)
    (f : Circle →ᵇ ℝ) : Circle →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨AddCircle.liftIoc (1 : ℝ) 0 (rationalCoverReal q f),
      AddCircle.liftIoc_zero_continuous
        (rationalCoverReal_endpoints hq f)
        (rationalCoverReal_continuous q f).continuousOn⟩

theorem rationalCover_coe
    {q : ℕ} (hq : 0 < q) (f : Circle →ᵇ ℝ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    rationalCover q hq f (x : Circle) = rationalCoverReal q f x := by
  unfold rationalCover
  simp only [BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk]
  by_cases hx0 : x = 0
  · subst x
    have hcoe : ((0 : ℝ) : Circle) = ((1 : ℝ) : Circle) :=
      (AddCircle.coe_period (p := (1 : ℝ))).symm
    rw [hcoe, AddCircle.liftIoc_zero_coe_apply
      (by simp : (1 : ℝ) ∈ Set.Ioc 0 1)]
    exact (rationalCoverReal_endpoints hq f).symm
  · exact AddCircle.liftIoc_zero_coe_apply
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩

theorem rationalCover_nonneg
    {q : ℕ} (hq : 0 < q) (f : Circle →ᵇ ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (x : Circle) :
    0 ≤ rationalCover q hq f x := by
  unfold rationalCover
  change 0 ≤ rationalCoverReal q f _
  unfold rationalCoverReal
  exact sum_nonneg fun j _ ↦ hf0 _

theorem rationalCover_norm_le
    {q : ℕ} (hq : 0 < q) (f : Circle →ᵇ ℝ) :
    ‖rationalCover q hq f‖ ≤ (q : ℝ) * ‖f‖ := by
  rw [BoundedContinuousFunction.norm_le
    (mul_nonneg (Nat.cast_nonneg q) (norm_nonneg f))]
  intro x
  unfold rationalCover
  change ‖rationalCoverReal q f _‖ ≤ (q : ℝ) * ‖f‖
  rw [Real.norm_eq_abs]
  unfold rationalCoverReal
  calc
    |∑ j ∈ range q,
        f (((((j : ℝ) + _) / (q : ℝ) : ℝ) : Circle))| ≤
        ∑ j ∈ range q,
          |f (((((j : ℝ) + _) / (q : ℝ) : ℝ) : Circle))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range q, ‖f‖ := by
      exact sum_le_sum fun j _ ↦ by
        rw [← Real.norm_eq_abs]
        exact f.norm_coe_le_norm _
    _ = (q : ℝ) * ‖f‖ := by
      rw [sum_const, card_range, nsmul_eq_mul]

theorem rationalCoverReal_lipschitz
    {q : ℕ} (hq : 0 < q) (f : Circle →ᵇ ℝ) {K : ℝ≥0}
    (hK : LipschitzWith K f) :
    LipschitzWith K (rationalCoverReal q f) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq]
  unfold rationalCoverReal
  rw [← sum_sub_distrib]
  calc
    |∑ j ∈ range q,
        (f (((((j : ℝ) + x) / (q : ℝ) : ℝ) : Circle)) -
          f (((((j : ℝ) + y) / (q : ℝ) : ℝ) : Circle)))| ≤
        ∑ j ∈ range q,
          |f (((((j : ℝ) + x) / (q : ℝ) : ℝ) : Circle)) -
            f (((((j : ℝ) + y) / (q : ℝ) : ℝ) : Circle))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range q, (K : ℝ) * (|x - y| / (q : ℝ)) := by
      apply sum_le_sum
      intro j _
      have hh := corePositiveTest_real_dist_le f hK
        (((j : ℝ) + x) / (q : ℝ)) (((j : ℝ) + y) / (q : ℝ))
      have heq : ((j : ℝ) + x) / (q : ℝ) -
          ((j : ℝ) + y) / (q : ℝ) = (x - y) / (q : ℝ) := by ring
      rw [heq, abs_div, abs_of_pos hqR] at hh
      exact hh
    _ = (K : ℝ) * |x - y| := by
      rw [sum_const, card_range, nsmul_eq_mul]
      field_simp [hqR.ne']

theorem rationalCover_lipschitz
    {q : ℕ} (hq : 0 < q) (f : Circle →ᵇ ℝ) {K : ℝ≥0}
    (hK : LipschitzWith K f) :
    LipschitzWith K (rationalCover q hq f) := by
  unfold rationalCover
  exact CoreCircleIntervalRamps.liftIoc_zero_lipschitz
    (rationalCoverReal_lipschitz hq f hK)
    (rationalCoverReal_endpoints hq f)

private theorem rationalCoverReal_eq_q_mul_gridMean
    {q : ℕ} (hq : 0 < q) (f : Circle →ᵇ ℝ) (x : ℝ) :
    rationalCoverReal q f x =
      (q : ℝ) * CoreBVOrbitMixing.gridMean q
        (CoreBVOrbitMixing.circleLift f) x := by
  unfold rationalCoverReal CoreBVOrbitMixing.gridMean
    CoreBVOrbitMixing.circleLift
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  field_simp [hqR]

theorem rationalCover_integral
    {q : ℕ} (hq : 0 < q) (f : Circle →ᵇ ℝ) :
    (∫ x : Circle, rationalCover q hq f x) =
      (q : ℝ) * ∫ x : Circle, f x := by
  let one : Circle →ᵇ ℝ := BoundedContinuousFunction.const Circle 1
  have hdual := CoreBVOrbitMixing.interval_clock_transfer_duality f one hq
  have hleft : (∫ x in (0 : ℝ)..1,
      f (x : Circle) * one (q • (x : Circle))) =
      ∫ x : Circle, f x := by
    simp only [one, BoundedContinuousFunction.const_apply, mul_one]
    simpa only [zero_add] using
      AddCircle.intervalIntegral_preimage (1 : ℝ) 0 f
  have hright : (∫ u in (0 : ℝ)..1,
      CoreBVOrbitMixing.gridMean q (CoreBVOrbitMixing.circleLift f) u *
        one (u : Circle)) =
      ∫ u in (0 : ℝ)..1,
        CoreBVOrbitMixing.gridMean q (CoreBVOrbitMixing.circleLift f) u := by
    simp only [one, BoundedContinuousFunction.const_apply, mul_one]
  rw [hleft, hright] at hdual
  have hcoverInterval : (∫ u in (0 : ℝ)..1, rationalCoverReal q f u) =
      (q : ℝ) * ∫ x : Circle, f x := by
    calc
      (∫ u in (0 : ℝ)..1, rationalCoverReal q f u) =
          ∫ u in (0 : ℝ)..1,
            (q : ℝ) * CoreBVOrbitMixing.gridMean q
              (CoreBVOrbitMixing.circleLift f) u := by
        apply intervalIntegral.integral_congr
        intro u _
        exact rationalCoverReal_eq_q_mul_gridMean hq f u
      _ = (q : ℝ) * ∫ u in (0 : ℝ)..1,
          CoreBVOrbitMixing.gridMean q (CoreBVOrbitMixing.circleLift f) u := by
        rw [intervalIntegral.integral_const_mul]
      _ = (q : ℝ) * ∫ x : Circle, f x := by rw [← hdual]
  have hpre := AddCircle.intervalIntegral_preimage (1 : ℝ) 0
    (rationalCover q hq f)
  calc
    (∫ x : Circle, rationalCover q hq f x) =
        ∫ u in (0 : ℝ)..1, rationalCover q hq f (u : Circle) := by
      simpa only [zero_add] using hpre.symm
    _ = ∫ u in (0 : ℝ)..1, rationalCoverReal q f u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact rationalCover_coe hq f hu
    _ = (q : ℝ) * ∫ x : Circle, f x := hcoverInterval

/-- Every nonnegative test value at a preimage is contained in the
rational cover evaluated at its image. -/
theorem le_rationalCover_mul
    {q : ℕ} (hq : 0 < q) (f : Circle →ᵇ ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (x : Circle) :
    f x ≤ rationalCover q hq f (q • x) := by
  let u := (AddCircle.equivIco (1 : ℝ) 0 x : Ico (0 : ℝ) (0 + 1))
  let z : ℝ := (q : ℝ) * (u : ℝ)
  let j : ℕ := ⌊z⌋₊
  let τ : ℝ := z - j
  have hu : (u : ℝ) ∈ Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using u.property
  have hux : ((u : ℝ) : Circle) = x := AddCircle.coe_equivIco
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hz0 : 0 ≤ z := mul_nonneg hqR.le hu.1
  have hjle : (j : ℝ) ≤ z := by
    dsimp only [j]
    exact Nat.floor_le hz0
  have hzj : z < (j : ℝ) + 1 := by
    dsimp only [j]
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one z
  have hτ0 : 0 ≤ τ := by dsimp only [τ]; linarith
  have hτ1 : τ < 1 := by dsimp only [τ]; linarith
  have hjq : j < q := by
    have hzq : z < (q : ℝ) := by
      dsimp only [z]
      nlinarith [hu.2]
    exact_mod_cast hjle.trans_lt hzq
  have himage : q • x = (τ : Circle) := by
    rw [← hux, ← AddCircle.coe_nsmul]
    simp only [nsmul_eq_mul]
    have hz : (q : ℝ) * (u : ℝ) = (j : ℝ) + τ := by
      dsimp only [z, τ]
      ring
    rw [hz, AddCircle.coe_add, circle_natCast_eq_zero, zero_add]
  have hterm : f x =
      f (((((j : ℝ) + τ) / (q : ℝ) : ℝ) : Circle)) := by
    rw [← hux]
    congr 2
    dsimp only [z, τ]
    field_simp [hqR.ne'] <;> ring
  rw [himage, rationalCover_coe hq f ⟨hτ0, hτ1.le⟩]
  rw [hterm]
  unfold rationalCoverReal
  exact single_le_sum
    (f := fun i : ℕ ↦
      f (((((i : ℝ) + τ) / (q : ℝ) : ℝ) : Circle)))
    (fun i hi ↦ hf0 _) (mem_range.mpr hjq)

/-! ## The actual position and gap orbits -/

def primePositionCircleOrbit (B n : ℕ) : Circle :=
  B ^ n • (primePosSeries B : Circle)

theorem primePositionCircleOrbit_succ (B n : ℕ) :
    primePositionCircleOrbit B (n + 1) =
      B • primePositionCircleOrbit B n := by
  simp only [primePositionCircleOrbit, smul_smul, ← pow_succ']

theorem gapOrbit_eq_mul_positionOrbit
    {B : ℕ} (hB : 2 ≤ B) (n : ℕ) :
    corePrimeGapCircleOrbit B n =
      (B - 1) • primePositionCircleOrbit B n := by
  induction n with
  | zero =>
      unfold corePrimeGapCircleOrbit primePositionCircleOrbit
      simp only [pow_zero, one_nsmul]
      have hgap : seqGapPolyTail nthPrime (fun _ ↦ Polynomial.X) B 0 =
          primeGapPowerSeries B 1 := by
        simp only [seqGapPolyTail, primeGapPowerSeries, Polynomial.eval_X,
          zero_add, seqGap_nthPrime, pow_one]
      rw [hgap, primeGapPowerSeries_one_eq hB,
        AddCircle.coe_sub, coreCircle_natCast_eq_zero, sub_zero,
        ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one]
  | succ n ih =>
      rw [corePrimeGapCircleOrbit_recurrence hB,
        primePositionCircleOrbit_succ, ih, smul_smul, smul_smul]
      exact congrArg (fun m : ℕ ↦ m • primePositionCircleOrbit B n)
        (Nat.mul_comm B (B - 1))

theorem position_orbitBlockMean_eq_windowAvg
    (B X : ℕ) (f : Circle → ℝ) :
    orbitBlockMean B (primePosSeries B : Circle) f
        (Nat.primeCounting X) (windowNX X) =
      windowAvgReal (seqWindow nthPrime X)
        (fun n ↦ f (primePositionCircleOrbit B n)) := by
  unfold orbitBlockMean CoreFiniteOrbitBoundary.blockMean windowAvgReal
    primePositionCircleOrbit
  rw [seqWindow_nthPrime_card, corePrime_seqWindow_eq_Ico,
    sum_Ico_eq_sum_range]
  simp only [windowNX, add_comm]

/-! ## Uniform finite positive domination -/

/-- Under Kuperberg, the actual prime-position block satisfies the precise
positive-domination interface needed by the finite orbit lemma. -/
theorem primePosition_finitePositiveDomination_of_kuperberg
    (B : ℕ) (hB : 2 ≤ B) (hK : KuperbergConj13) :
    ∃ A E H : ℝ, 0 ≤ A ∧ 0 ≤ E ∧ 0 ≤ H ∧
      ∀ᶠ X : ℕ in atTop,
        FinitePositiveDomination B (primePosSeries B : Circle)
          (Nat.primeCounting X) (windowNX X) A
          (E / (profileL (4 / Real.log (B : ℝ)) X : ℝ))
          (H * (windowG X ^ (-(1 / 2 : ℝ)) +
            windowG X * ((B : ℝ) ^ profileL
              (4 / Real.log (B : ℝ)) X)⁻¹)) := by
  let κ : ℝ := 4 / Real.log (B : ℝ)
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos hBr
  have hκ : 1 / Real.log (B : ℝ) ≤ κ := by
    dsimp only [κ]
    exact div_le_div_of_nonneg_right (by norm_num) hlogB.le
  have hκpos : 0 < κ := div_pos (by norm_num) hlogB
  obtain ⟨Avol, Aerr, hAvol, hAerr, hprime⟩ :=
    corePrimeGap_positive_window_quantitative B hB hκ (c := 1) le_rfl
  let q : ℕ := B - 1
  let A : ℝ := Avol * q
  let E : ℝ := Aerr * ((q : ℝ) *
      (CoreKuperbergQuantitativeBudget.comparisonConstant + 1))
  let H : ℝ := Aerr
  have hq : 0 < q := by dsimp only [q]; omega
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    have hc := CoreKuperbergQuantitativeBudget.comparisonConstant_pos
    positivity
  have hH : 0 ≤ H := by simpa only [H] using hAerr
  refine ⟨A, E, H, hA, hE, hH, ?_⟩
  filter_upwards [hprime,
    CoreKuperbergQuantitativeBudget.eventually_comparison_le_inv_rank
      hK hκpos,
    eventually_one_le_profileL hκpos] with X hprimeX hD hL
  intro f K hf0 hLip
  let cover := rationalCover q hq f
  have hcover0 : ∀ x, 0 ≤ cover x := rationalCover_nonneg hq f hf0
  have hcoverLip : LipschitzWith K cover :=
    rationalCover_lipschitz hq f hLip
  have hbase := hprimeX cover K hcoverLip hcover0
  simp only [mul_one] at hbase
  have hpoint : ∀ n ∈ seqWindow nthPrime X,
      f (primePositionCircleOrbit B n) ≤ cover (corePrimeGapCircleOrbit B n) := by
    intro n _
    rw [gapOrbit_eq_mul_positionOrbit hB]
    exact le_rationalCover_mul hq f hf0 _
  have havg : windowAvgReal (seqWindow nthPrime X)
      (fun n ↦ f (primePositionCircleOrbit B n)) ≤
      windowAvgReal (seqWindow nthPrime X)
        (fun n ↦ cover (corePrimeGapCircleOrbit B n)) := by
    unfold windowAvgReal
    exact div_le_div_of_nonneg_right (sum_le_sum hpoint) (Nat.cast_nonneg _)
  have hnorm := rationalCover_norm_le hq f
  have hint := rationalCover_integral hq f
  let L := profileL κ X
  let e : ℝ := windowG X ^ (-(1 / 2 : ℝ))
  let t : ℝ := windowG X * ((B : ℝ) ^ L)⁻¹
  let D : ℝ := corePrimeComparisonQuantity X (ahlSmall_omega κ X) L
    (profileR L 20) 1
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (by omega)
  have hD' : D ≤ CoreKuperbergQuantitativeBudget.comparisonConstant / (L : ℝ) := by
    simpa only [D, L, ahlSmall_omega, offsetWindow] using hD
  have hDq : D + (L : ℝ)⁻¹ ≤
      (CoreKuperbergQuantitativeBudget.comparisonConstant + 1) / (L : ℝ) := by
    calc
      D + (L : ℝ)⁻¹ ≤
          CoreKuperbergQuantitativeBudget.comparisonConstant / (L : ℝ) +
            1 / (L : ℝ) := _root_.add_le_add hD'
              (by simp only [one_div, le_refl])
      _ = _ := by ring
  have hnormTerm : (D + (L : ℝ)⁻¹) * ‖cover‖ ≤
      ((q : ℝ) * (CoreKuperbergQuantitativeBudget.comparisonConstant + 1) /
        (L : ℝ)) * ‖f‖ := by
    have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
    have hscale := mul_le_mul hDq hnorm (norm_nonneg cover)
      (div_nonneg
        (_root_.add_nonneg
          CoreKuperbergQuantitativeBudget.comparisonConstant_pos.le zero_le_one)
        hLpos.le)
    exact hscale.trans_eq (by ring)
  have hcombined := havg.trans (hbase.trans
    (_root_.add_le_add
      (mul_le_mul_of_nonneg_left hint.le hAvol)
      (mul_le_mul_of_nonneg_left
        (_root_.add_le_add hnormTerm le_rfl) hAerr)))
  rw [position_orbitBlockMean_eq_windowAvg]
  dsimp only [A, E, H, κ, q, L, e, t, D, cover] at hcombined ⊢
  exact hcombined.trans_eq (by ring)

end

end PrimeGapNormality.Prime.CorePrimePositionQuantitativeComparison
