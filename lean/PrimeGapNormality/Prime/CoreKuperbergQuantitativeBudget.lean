import PrimeGapNormality.Prime.CoreAHLToD
import PrimeGapNormality.Prime.CoreLinearQuantitativeModel
import PrimeGapNormality.Prime.CoreRoughRemainderScalar

/-!
# Actual one-sided D has an inverse-rank rate under Kuperberg

Normalization is controlled by the EMPTY rooted pattern: its actual
normalized inclusion is one and its unnormalized model inclusion is ζ.
The same genuine arithmetic/calibration errors therefore control ζ-1 and
the finite Janossy transform. No quantitative PNT is assumed or imported
as an input. The actual count and factorial-moment rates are used below.
-/

namespace PrimeGapNormality.Prime.CoreKuperbergQuantitativeBudget
open Filter Finset
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1200000

def transformCost (S r : ℕ) : ℝ := (((r + 1) * ((offsetWindow S).card + 1) ^ r : ℕ) : ℝ)

/-- The empty-pattern instance supplies normalization quantitatively. -/
theorem normalization_le_pair_errors {X S r : ℕ} (hN : 0 < windowNX X)
    {A C : ℝ}
    (hA : ∀ H ⊆ offsetWindow S, H.card ≤ r →
      |(rootedTupleCount X H : ℝ) / windowNX X - rootedMainTerm X H / windowNX X| ≤ A)
    (hC : ∀ H ⊆ offsetWindow S, H.card ≤ r →
      |rootedMainTerm X H / windowNX X -
        Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H| ≤ C) :
    |1 - mixZeta X| ≤ A + C := by
  have ha := hA ∅ (empty_subset _) (by simp)
  have hc := hC ∅ (empty_subset _) (by simp)
  have he : (rootedTupleCount X ∅ : ℝ) / windowNX X = 1 := by
    have hh := coreActualPatternMass_inclusion X (empty_subset (offsetWindow S))
    simpa only [Stopped.inclusionMass, empty_subset, filter_true,
      coreActualPatternMass_total _ hN] using hh.symm
  have hz : Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) ∅ = mixZeta X := by
    simpa only [Stopped.inclusionMass, empty_subset, filter_true] using crtMixUnnorm_sum X S hN
  rw [he] at ha
  rw [hz] at hc
  exact (abs_sub_le 1 (rootedMainTerm X ∅ / windowNX X) (mixZeta X)).trans (_root_.add_le_add ha hc)

/-- Unified finite comparison: singleton calibration is charged once,
while the two genuine pointwise errors pay the literal transform cost. -/
theorem comparison_le_pair_errors {X S L r : ℕ} (hN : 0 < windowNX X)
    (hZ : 0 < mixZ X) (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    {A C : ℝ} (hA0 : 0 ≤ A) (hC0 : 0 ≤ C)
    (hA : ∀ H ⊆ offsetWindow S, H.card ≤ r →
      |(rootedTupleCount X H : ℝ) / windowNX X - rootedMainTerm X H / windowNX X| ≤ A)
    (hC : ∀ H ⊆ offsetWindow S, H.card ≤ r →
      |rootedMainTerm X H / windowNX X -
        Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H| ≤ C) :
    corePrimeComparisonQuantity X (offsetWindow S) L r 1 ≤
      (1 + transformCost S r ^ 2) * (A + C) + mixZeta X *
        (Stopped.failureMass (offsetWindow S) (finiteRootMix X S) L +
          Stopped.modelRemainder (offsetWindow S) (finiteRootMix X S) L r) := by
  have hbase := corePrimeComparisonQuantity_le_absolute_errors
    (Ω := offsetWindow S) (ν := finiteRootMixUnnorm X S) hN hL hr hpar
  rw [crtMixUnnorm_sum X S hN,
    finiteRootMixUnnorm_failureMass_eq_mixZeta_mul hN hZ,
    finiteRootMixUnnorm_modelRemainder_eq_mixZeta_mul hN hZ] at hbase
  have ha := coreJanossyTransform_sum_sub_le (offsetWindow S) hr hA0 hA
  have hc := coreJanossyTransform_sum_sub_le (offsetWindow S) hr hC0 hC
  simp only [coreJanossyTransform_div] at ha hc
  simp only [coreJanossyTransform_inclusionMass_eq_janossyTrunc] at hc
  have hz := normalization_le_pair_errors hN hA hC
  dsimp only [transformCost]
  linarith

private theorem mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos
  · intro t ht
    exact eulerProdNat_pos (sieveCutoff (t : ℝ))
  · exact ⟨2 * X, by simp only [mixScale, mem_Ioc]; omega⟩

private theorem finiteRootMix_nonneg (X S : ℕ) (U : Finset ℕ) :
    0 ≤ finiteRootMix X S U := by
  unfold finiteRootMix
  exact div_nonneg
    (sum_nonneg fun t _ ↦
      mul_nonneg (mixWeightV_nonneg t) (actualRootLaw_nonneg _ _ _))
    (mixZ_nonneg X)

/-- A finite exponentially small model remainder; the old qualitative
remainder limit is not used to infer this rate. -/
theorem eventually_remainder_le_half_pow {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X in atTop,
      Stopped.modelRemainder (ahlSmall_omega κ X) (finiteRootMix X (ahlSmall_window κ X))
        (profileL κ X) (profileR (profileL κ X) 20) ≤ (1 / 2 : ℝ) ^ profileL κ X := by
  filter_upwards [finiteRootMix_small_countMoment_le_five hκ,
    (tendsto_profileL_atTop hκ).eventually_ge_atTop 2] with X hm hL
  have hr := Stopped.modelRemainder_le (Ω := ahlSmall_omega κ X)
    (ν := finiteRootMix X (ahlSmall_window κ X)) (by omega : 1 ≤ profileL κ X)
    (profileR_ge (profileL κ X) 20) (fun U _ => finiteRootMix_nonneg _ _ U)
  have hh := hr.trans (mul_le_mul_of_nonneg_left (hm (profileR (profileL κ X) 20 + 1))
    (Nat.cast_nonneg ((profileR (profileL κ X) 20).choose (profileL κ X - 1))))
  rw [← mul_div_assoc] at hh
  exact hh.trans (CoreRoughRemainderScalar.small_remainder_scalar_le_half_pow _ hL)

theorem half_pow_le_inv (L : ℕ) (hL : 1 ≤ L) : (1 / 2 : ℝ) ^ L ≤ 1 / (L : ℝ) := by
  have hp : (L : ℝ) ≤ (2 : ℝ) ^ L := by
    exact_mod_cast (show L < 2 ^ L from Nat.lt_two_pow_self).le
  have hh := one_div_le_one_div_of_le (Nat.cast_pos.2 (show 0 < L by omega)) hp
  simpa only [div_pow, one_pow] using hh

def failureConstant : ℝ := 500 + CorePresieveCountRate.presieveLowerRateConstant (1 / 100)

private theorem eventually_rank_le_log_span_sq {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X in atTop, (profileL κ X : ℝ) ≤ Real.log (ahlSmall_window κ X : ℝ) ^ 2 := by
  filter_upwards [eventually_windowG_le_ahlSmall_window hκ,
    (Real.tendsto_log_atTop.comp tendsto_windowG_atTop).eventually_ge_atTop (2 * κ + 2)] with X hGS hl
  simp only [Function.comp_apply] at hl
  have hG := crtWindowG_one_le X
  have ht : 0 ≤ κ * Real.log (windowG X) := mul_nonneg hκ.le (Real.log_nonneg hG)
  have hs := Real.sq_sqrt ht
  have hs0 := Real.sqrt_nonneg (κ * Real.log (windowG X))
  have hceil : (profileL κ X : ℝ) ≤ κ * Real.log (windowG X) +
      Real.sqrt (κ * Real.log (windowG X)) + 1 := (Nat.ceil_lt_add_one (add_nonneg ht hs0)).le
  have hbound : (profileL κ X : ℝ) ≤ Real.log (windowG X) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (κ * Real.log (windowG X)) - 1)]
  exact hbound.trans (pow_le_pow_left₀ (Real.log_nonneg hG)
    (Real.log_le_log (zero_lt_one.trans_le hG) hGS) 2)

theorem eventually_failure_le_inv_rank {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X in atTop,
      Stopped.failureMass (ahlSmall_omega κ X) (finiteRootMix X (ahlSmall_window κ X))
        (profileL κ X) ≤ failureConstant / (profileL κ X : ℝ) := by
  filter_upwards [finiteRootMix_small_failureMass_le_lowerException hκ,
    CoreLinearQuantitativeModel.eventually_finiteRootMixSmallLowerException_le_log_sq hκ,
    eventually_rank_le_log_span_sq hκ, eventually_one_le_profileL hκ] with X hf hl hsq hL
  have hp : (0 : ℝ) < profileL κ X := Nat.cast_pos.2 (by omega)
  have hi := one_div_le_one_div_of_le hp hsq
  have hc : 0 ≤ CorePresieveCountRate.presieveLowerRateConstant (1 / 100) :=
    (CorePresieveCountRate.presieveLowerRateConstant_pos (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hh := mul_le_mul_of_nonneg_left hi hc
  have hlow : finiteRootMixSmallLowerException κ X ≤
      CorePresieveCountRate.presieveLowerRateConstant (1 / 100) / (profileL κ X : ℝ) :=
    hl.trans (by simpa only [div_eq_mul_inv, one_mul] using hh)
  exact (hf.trans (_root_.add_le_add le_rfl hlow)).trans_eq (by unfold failureConstant; ring)

def exponentialCost (X : ℕ) : ℝ := Real.exp (Real.log (Real.log (X : ℝ)) ^ 4)

theorem exponentialCost_pow (X m : ℕ) :
    exponentialCost X ^ m = Real.exp ((m : ℝ) * Real.log (Real.log (X : ℝ)) ^ 4) := by
  rw [exponentialCost, ← Real.exp_nat_mul]

theorem exponentialCost_one_le (X : ℕ) : 1 ≤ exponentialCost X := by
  unfold exponentialCost
  exact Real.one_le_exp_iff.2 (by positivity)

theorem profile_cost_bounds {κ : ℝ} {X : ℕ} (hfit : ProfileFits κ 20 X)
    (hG : 2 ≤ Real.log (X : ℝ)) :
    (profileL κ X : ℝ) ≤ exponentialCost X ∧
      (profileR (profileL κ X) 20 + 1 : ℝ) ≤ exponentialCost X ∧
      Real.log (X : ℝ) ≤ exponentialCost X ∧
      transformCost (ahlSmall_window κ X) (profileR (profileL κ X) 20) ^ 2 ≤ exponentialCost X ^ 10 := by
  let ell := Real.log (Real.log (X : ℝ))
  have he1 : 1 < ell := one_lt_log_log_of_sixteen_le hfit.1
  have he4 : ell ≤ ell ^ 4 := le_self_pow₀ he1.le (by omega)
  have he34 : ell ^ 3 ≤ ell ^ 4 := pow_le_pow_right₀ he1.le (by omega)
  have heexp : ell ^ 4 ≤ Real.exp (ell ^ 4) := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hr : (profileR (profileL κ X) 20 + 1 : ℝ) ≤ exponentialCost X :=
    hfit.2.2.1.trans (he34.trans heexp)
  have hL : (profileL κ X : ℝ) ≤ (profileR (profileL κ X) 20 + 1 : ℝ) := by
    exact_mod_cast (Nat.le_succ_of_le (profileR_ge (profileL κ X) 20))
  refine ⟨hL.trans hr, hr, ?_, ?_⟩
  · have hp : 0 < Real.log (X : ℝ) := by linarith
    calc
      Real.log (X : ℝ) = Real.exp ell := (Real.exp_log hp).symm
      _ ≤ Real.exp (ell ^ 4) := Real.exp_le_exp.2 he4
      _ = exponentialCost X := rfl
  · rw [exponentialCost_pow]
    simpa only [transformCost, ahlSmall_omega, offsetWindow, Nat.cast_ofNat] using
      small_combination_cost_le_exp hfit hG

def arithmeticCoefficient (ε K : ℝ) : ℝ := 16 * K * ((2 : ℝ) ^ (1 - ε) + 1)
def arithmeticError (ε K : ℝ) (X : ℕ) : ℝ :=
  arithmeticCoefficient ε K * exponentialCost X * (X : ℝ) ^ (-ε)
def calibrationError (X : ℕ) : ℝ :=
  96 * exponentialCost X ^ 3 * (X : ℝ) ^ (-eulerProdLowerConst) +
    64 * exponentialCost X * (X : ℝ) ^ (-(1 : ℝ))

theorem arithmeticError_nonneg {ε K : ℝ} (hK : 0 ≤ K) (X : ℕ) : 0 ≤ arithmeticError ε K X := by
  unfold arithmeticError arithmeticCoefficient exponentialCost
  positivity
theorem calibrationError_nonneg (X : ℕ) : 0 ≤ calibrationError X := by
  unfold calibrationError exponentialCost
  positivity

theorem tendsto_exponentialCost_pow_mul_neg (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun X : ℕ => exponentialCost X ^ m * (X : ℝ) ^ (-ε)) atTop (𝓝 0) := by
  have hh := (tendsto_exp_loglog_pow_four_mul_rpow_neg (A := (m : ℝ)) (ε := ε)
    (Nat.cast_nonneg _) hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, exponentialCost_pow] using hh

/-- The explicit error envelope survives multiplication by the ACTUAL
rank and full finite Janossy cost. -/
theorem tendsto_weighted_pair_errors {κ ε K : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hK : 0 ≤ K) :
    Tendsto (fun X : ℕ => (profileL κ X : ℝ) *
      ((1 + transformCost (ahlSmall_window κ X) (profileR (profileL κ X) 20) ^ 2) *
        (arithmeticError ε K X + calibrationError X))) atTop (𝓝 0) := by
  have hlim := (((tendsto_exponentialCost_pow_mul_neg 12 hε).const_mul
      (2 * arithmeticCoefficient ε K)).add
    ((tendsto_exponentialCost_pow_mul_neg 14 eulerProdLowerConst_pos).const_mul 192)).add
    ((tendsto_exponentialCost_pow_mul_neg 12 (by norm_num : (0 : ℝ) < 1)).const_mul 128)
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun X =>
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity)
      (add_nonneg (arithmeticError_nonneg hK X) (calibrationError_nonneg X)))) _ hlim
  filter_upwards [eventually_profileFits hκ (by norm_num : (0 : ℝ) < 20),
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2]
    with X hfit hg
  simp only [Function.comp_apply] at hg
  have hb := profile_cost_bounds hfit hg
  let E := exponentialCost X
  have hE : 1 ≤ E := exponentialCost_one_le X
  have hfactor : (profileL κ X : ℝ) *
      (1 + transformCost (ahlSmall_window κ X) (profileR (profileL κ X) 20) ^ 2) ≤ 2 * E ^ 11 := by
    have h1 : (1 : ℝ) ≤ E ^ 10 := one_le_pow₀ hE
    have hh := mul_le_mul hb.1 (_root_.add_le_add h1 hb.2.2.2)
      (by positivity) (zero_le_one.trans hE)
    exact hh.trans_eq (by dsimp only [E]; ring)
  have hm := mul_le_mul_of_nonneg_right hfactor
    (add_nonneg (arithmeticError_nonneg (ε := ε) hK X) (calibrationError_nonneg X))
  calc
    _ = ((profileL κ X : ℝ) *
        (1 + transformCost (ahlSmall_window κ X) (profileR (profileL κ X) 20) ^ 2)) *
          (arithmeticError ε K X + calibrationError X) := by ring
    _ ≤ 2 * E ^ 11 * (arithmeticError ε K X + calibrationError X) := hm
    _ = _ := by unfold arithmeticError calibrationError; dsimp only [E]; ring

/-- Genuine Kuperberg tuple errors and actual minimal-cutoff calibration
give these two explicit uniform envelopes, including the empty pattern. -/
theorem exists_pair_error_bounds (hK : KuperbergConj13) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ᶠ X in atTop,
      ∀ H ⊆ offsetWindow (ahlSmall_window κ X), H.card ≤ profileR (profileL κ X) 20 →
        |(rootedTupleCount X H : ℝ) / windowNX X - rootedMainTerm X H / windowNX X| ≤
          arithmeticError ε K X ∧
        |rootedMainTerm X H / windowNX X -
          Stopped.inclusionMass (offsetWindow (ahlSmall_window κ X))
            (finiteRootMixUnnorm X (ahlSmall_window κ X)) H| ≤ calibrationError X := by
  obtain ⟨ε, K, hε, hKp, hbound⟩ := hK
  refine ⟨ε, K, hε, hKp, ?_⟩
  filter_upwards [eventually_profileFits hκ (by norm_num : (0 : ℝ) < 20),
    CorePrimeDensity.eventually_X_div_windowNX_le,
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2,
    eventually_finiteRootMixUnnorm_small_inclusionMass_relative_error_le hκ (by norm_num : (0 : ℝ) < 20),
    (tendsto_coreMixtureRelativeError hκ (by norm_num : (0 : ℝ) < 20)).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 2)] with X hfit hXN hg hrel hδhalf
  simp only [Function.comp_apply] at hg
  let E := exponentialCost X
  let δ := coreMixtureRelativeError κ 20 X
  have hX : 0 < X := by have := hfit.1; omega
  have hXr : (0 : ℝ) < X := Nat.cast_pos.2 hX
  have hN : 0 < windowNX X := windowNX_pos hX
  have hNr : (0 : ℝ) < windowNX X := Nat.cast_pos.2 hN
  have hb := profile_cost_bounds hfit hg
  have hE : 0 ≤ E := zero_le_one.trans (exponentialCost_one_le X)
  have hXE : (X : ℝ) / windowNX X ≤ 16 * E := hXN.trans
    (mul_le_mul_of_nonneg_left hb.2.2.1 (by norm_num))
  have hδ0 : 0 ≤ δ := by unfold δ coreMixtureRelativeError; positivity
  have hδ : δ ≤ 3 * E ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst) + 2 / X := by
    have hs := pow_le_pow_left₀ (show 0 ≤ (profileR (profileL κ X) 20 + 1 : ℝ) by positivity) hb.2.1 2
    exact _root_.add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num))
        (Real.rpow_nonneg hXr.le _)) le_rfl
  intro H hH hcard
  constructor
  · have hlarge : H ⊆ windowOmega κ X := hH.trans (ahlSmall_omega_subset_windowOmega κ X)
    have hh := rooted_error_abs_le_kuperberg hKp.le hbound hfit hlarge hcard
    have h1 : (X : ℝ) ^ (1 - ε) = (X : ℝ) * (X : ℝ) ^ (-ε) := by
      rw [show 1 - ε = 1 + (-ε) by ring, Real.rpow_add hXr, Real.rpow_one]
    have h2 : (2 * X : ℝ) ^ (1 - ε) = (2 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε) :=
      Real.mul_rpow (by norm_num) hXr.le
    rw [← sub_div, abs_div, abs_of_pos hNr]
    refine (div_le_div_of_nonneg_right hh hNr.le).trans ?_
    have heq : K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)) / windowNX X =
        (K * ((2 : ℝ) ^ (1 - ε) + 1)) * ((X : ℝ) / windowNX X) * (X : ℝ) ^ (-ε) := by
      rw [h2, h1]
      ring
    rw [heq]
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hXE (by positivity : 0 ≤ K * ((2 : ℝ) ^ (1 - ε) + 1)))
      (Real.rpow_nonneg hXr.le (-ε))
    exact hm.trans_eq (by unfold arithmeticError arithmeticCoefficient; dsimp only [E]; ring)
  · have hh := finiteRootMixUnnorm_inclusionMass_absolute_error_le hX hH hδ0 hδhalf
      (hrel H hH hcard)
    have hh' : |rootedMainTerm X H / windowNX X -
        Stopped.inclusionMass (offsetWindow (ahlSmall_window κ X))
          (finiteRootMixUnnorm X (ahlSmall_window κ X)) H| ≤ 2 * δ * (X : ℝ) / windowNX X := by
      simpa only [abs_sub_comm] using hh
    refine hh'.trans ?_
    have hfirst := mul_le_mul_of_nonneg_left hXE (show 0 ≤ 2 * δ by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hδ (show 0 ≤ 32 * E by positivity)
    calc
      2 * δ * (X : ℝ) / windowNX X = 2 * δ * ((X : ℝ) / windowNX X) := by ring
      _ ≤ 2 * δ * (16 * E) := hfirst
      _ = 32 * E * δ := by ring
      _ ≤ 32 * E * (3 * E ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst) + 2 / X) := hsecond
      _ = calibrationError X := by unfold calibrationError; rw [Real.rpow_neg_one]; dsimp only [E]; ring

def comparisonConstant : ℝ := 1 + 16 * (failureConstant + 1)

theorem comparisonConstant_pos : 0 < comparisonConstant := by
  have hc := CorePresieveCountRate.presieveLowerRateConstant_pos (by norm_num : (0 : ℝ) < 1 / 100)
  unfold comparisonConstant failureConstant
  linarith

/-- The actual one-sided arithmetic comparison quantity has the announced
Oκ(1/L) rate. Every rate input is proved from genuine Kuperberg or from
the unconditional finite model. Constants in the eventual threshold may
depend on the Kuperberg witnesses; no quantitative PNT is added. -/
theorem eventually_comparison_le_inv_rank (hK : KuperbergConj13) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X in atTop,
      corePrimeComparisonQuantity X (offsetWindow (ahlSmall_window κ X)) (profileL κ X)
        (profileR (profileL κ X) 20) 1 ≤ comparisonConstant / (profileL κ X : ℝ) := by
  obtain ⟨ε, K, hε, hKp, hpairs⟩ := exists_pair_error_bounds hK hκ
  have hrate := tendsto_weighted_pair_errors hκ hε hKp.le
  filter_upwards [hpairs, hrate.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_failure_le_inv_rank hκ, eventually_remainder_le_half_pow hκ,
    CorePrimeDensity.eventually_mixZeta_le_sixteen, eventually_one_le_profileL hκ,
    eventually_ge_atTop 1] with X hp he hf hr hζ hL hX
  have hN := windowNX_pos (by omega : 0 < X)
  have hZ := mixZ_pos hX
  have hLp : (0 : ℝ) < profileL κ X := Nat.cast_pos.2 (by omega)
  have hpair : (1 + transformCost (ahlSmall_window κ X) (profileR (profileL κ X) 20) ^ 2) *
      (arithmeticError ε K X + calibrationError X) ≤ 1 / (profileL κ X : ℝ) := by
    apply (le_div_iff₀ hLp).2
    simpa only [mul_comm] using he
  have hrem := hr.trans (half_pow_le_inv _ hL)
  have hsum : Stopped.failureMass (ahlSmall_omega κ X)
        (finiteRootMix X (ahlSmall_window κ X)) (profileL κ X) +
      Stopped.modelRemainder (ahlSmall_omega κ X)
        (finiteRootMix X (ahlSmall_window κ X)) (profileL κ X) (profileR (profileL κ X) 20) ≤
      (failureConstant + 1) / (profileL κ X : ℝ) :=
    (_root_.add_le_add hf hrem).trans_eq (by ring)
  have hζ0 : 0 ≤ mixZeta X := by unfold mixZeta; exact div_nonneg (mixZ_nonneg X) (Nat.cast_nonneg _)
  have hcost0 : 0 ≤ (failureConstant + 1) / (profileL κ X : ℝ) := by
    have hc := CorePresieveCountRate.presieveLowerRateConstant_pos (by norm_num : (0 : ℝ) < 1 / 100)
    unfold failureConstant
    positivity
  have hmodel := (mul_le_mul_of_nonneg_left hsum hζ0).trans
    (mul_le_mul_of_nonneg_right hζ hcost0)
  have hD := comparison_le_pair_errors hN hZ hL (profileR_ge (profileL κ X) 20)
    (crtMixProf_odd_at κ 20 X) (arithmeticError_nonneg hKp.le X) (calibrationError_nonneg X)
    (fun H hH hc => (hp H hH hc).1) (fun H hH hc => (hp H hH hc).2)
  exact (hD.trans (_root_.add_le_add hpair hmodel)).trans_eq (by unfold comparisonConstant; ring)

theorem comparison_rate (hK : KuperbergConj13) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X in atTop,
      corePrimeComparisonQuantity X (offsetWindow (ahlSmall_window κ X)) (profileL κ X)
        (profileR (profileL κ X) 20) 1 ≤ C / (profileL κ X : ℝ) :=
  ⟨comparisonConstant, comparisonConstant_pos, eventually_comparison_le_inv_rank hK hκ⟩

end
end PrimeGapNormality.Prime.CoreKuperbergQuantitativeBudget
