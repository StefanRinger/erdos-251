import PrimeGapNormality.Prime.CoreComparisonRemainder
import PrimeGapNormality.Prime.CoreMixtureCalibrationLimit
import PrimeGapNormality.Prime.CrtMixUnnormStopped
import PrimeGapNormality.Prime.CrtProfileRParity
import PrimeGapNormality.Prime.FiniteRootMixSmallCosts
import PrimeGapNormality.Prime.FiniteRootMixSmallLowerException
import PrimeGapNormality.Prime.PrimeCountingNormalization

/-!
# Concrete Kuperberg-to-D comparison at the small prime profile

The first consumer fixes the paper cutoff `d0 = 20`.  The reference law is
the unnormalized finite root mixture `ν̃ = ζ ν`: its total-mass error is
paid once, while failure and Bonferroni remainder are transferred from the
normalized mixture by exact scalar identities.
-/

open Filter Finset
open scoped Classical Topology

namespace PrimeGapNormality.Prime

noncomputable section

private theorem core_mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos
  · intro t _
    exact eulerProdNat_pos (sieveCutoff (t : ℝ))
  · exact ⟨2 * X, by simp only [mixScale, mem_Ioc]; omega⟩

/-- Exact pointwise normalization `ν̃ = ζ ν`. -/
theorem finiteRootMixUnnorm_eq_mixZeta_mul_finiteRootMix
    {X : ℕ} (hN : 0 < windowNX X) (hZ : 0 < mixZ X)
    (S : ℕ) (U : Finset ℕ) :
    finiteRootMixUnnorm X S U = mixZeta X * finiteRootMix X S U := by
  unfold finiteRootMixUnnorm finiteRootMix mixZeta
  have hN' : (windowNX X : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hZ' : mixZ X ≠ 0 := hZ.ne'
  field_simp [hN', hZ']

theorem finiteRootMixUnnorm_failureMass_eq_mixZeta_mul
    {X : ℕ} (hN : 0 < windowNX X) (hZ : 0 < mixZ X)
    (S L : ℕ) :
    Stopped.failureMass (offsetWindow S) (finiteRootMixUnnorm X S) L =
      mixZeta X *
        Stopped.failureMass (offsetWindow S) (finiteRootMix X S) L := by
  unfold Stopped.failureMass
  simp_rw [finiteRootMixUnnorm_eq_mixZeta_mul_finiteRootMix hN hZ]
  exact (mul_sum _ _ _).symm

theorem finiteRootMixUnnorm_modelRemainder_eq_mixZeta_mul
    {X : ℕ} (hN : 0 < windowNX X) (hZ : 0 < mixZ X)
    (S L r : ℕ) :
    Stopped.modelRemainder (offsetWindow S) (finiteRootMixUnnorm X S) L r =
      mixZeta X *
        Stopped.modelRemainder (offsetWindow S) (finiteRootMix X S) L r := by
  unfold Stopped.modelRemainder
  simp_rw [finiteRootMixUnnorm_eq_mixZeta_mul_finiteRootMix hN hZ, mul_assoc]
  exact (mul_sum _ _ _).symm

theorem tendsto_finiteRootMixUnnorm_small_failureMass_of_kuperberg
    (hK : KuperbergConj13) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      Stopped.failureMass (ahlSmall_omega κ X)
        (finiteRootMixUnnorm X (ahlSmall_window κ X)) (profileL κ X))
      atTop (nhds 0) := by
  have hmul := (PrimeCountingNormalization.mixZeta_one_of_kuperberg hK).mul
    (tendsto_finiteRootMix_small_failureMass hκ)
  have htarget : Tendsto (fun X : ℕ =>
      mixZeta X * Stopped.failureMass (ahlSmall_omega κ X)
        (finiteRootMix X (ahlSmall_window κ X)) (profileL κ X))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hmul
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hN := windowNX_pos (by omega : 0 < X)
  have hZ := core_mixZ_pos hX
  simpa only [ahlSmall_omega, offsetWindow] using
    (finiteRootMixUnnorm_failureMass_eq_mixZeta_mul hN hZ
      (ahlSmall_window κ X) (profileL κ X)).symm

theorem tendsto_finiteRootMixUnnorm_small_modelRemainder_of_kuperberg
    (hK : KuperbergConj13) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      Stopped.modelRemainder (ahlSmall_omega κ X)
        (finiteRootMixUnnorm X (ahlSmall_window κ X))
        (profileL κ X) (profileR (profileL κ X) 20))
      atTop (nhds 0) := by
  have hmul := (PrimeCountingNormalization.mixZeta_one_of_kuperberg hK).mul
    (tendsto_finiteRootMix_small_modelRemainder hκ)
  have htarget : Tendsto (fun X : ℕ =>
      mixZeta X * Stopped.modelRemainder (ahlSmall_omega κ X)
        (finiteRootMix X (ahlSmall_window κ X))
        (profileL κ X) (profileR (profileL κ X) 20))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hmul
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hN := windowNX_pos (by omega : 0 < X)
  have hZ := core_mixZ_pos hX
  simpa only [ahlSmall_omega, offsetWindow] using
    (finiteRootMixUnnorm_modelRemainder_eq_mixZeta_mul hN hZ
      (ahlSmall_window κ X) (profileL κ X) (profileR (profileL κ X) 20)).symm

/-- The actual-count/main-term Janossy error in the finite D bound. -/
noncomputable def coreActualMainJanossyError (κ d0 : ℝ) (X : ℕ) : ℝ :=
  ∑ K ∈ (ahlSmall_omega κ X).powerset.filter
      (fun K => K.card = profileL κ X),
    |coreJanossyTransform (ahlSmall_omega κ X)
          (fun H => (rootedTupleCount X H : ℝ))
          (profileL κ X) (profileR (profileL κ X) d0) K /
          (windowNX X : ℝ) -
      coreJanossyTransform (ahlSmall_omega κ X) (rootedMainTerm X)
          (profileL κ X) (profileR (profileL κ X) d0) K /
          (windowNX X : ℝ)|

private theorem log_two_mul_le_two_log_core {X : ℕ} (hX : 3 ≤ X) :
    Real.log (2 * (X : ℝ)) ≤ 2 * Real.log (X : ℝ) := by
  have hx : 0 < (X : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [Real.log_mul (by norm_num) hx.ne']
  have hlog : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) (Nat.cast_le.mpr (by omega : 2 ≤ X))
  linarith

/-- The actual tuple-count contribution to D tends to zero directly from
Kuperberg, with the coarse transform cost absorbed by its power saving. -/
theorem tendsto_coreActualMainJanossyError_of_kuperberg
    (hK : KuperbergConj13) {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    Tendsto (coreActualMainJanossyError κ d0) atTop (nhds 0) := by
  obtain ⟨ε, K, hε, hKpos, hbound⟩ := hK
  let C0 : ℝ := 4 * K * ((2 : ℝ) ^ (1 - ε) + 1)
  have hupper : Tendsto (fun X : ℕ =>
      C0 * (Real.exp (11 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-ε))) atTop (nhds 0) := by
    have h :=
      (tendsto_exp_loglog_pow_four_mul_rpow_neg
        (A := (11 : ℝ)) (ε := ε) (by norm_num) hε).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
    have hc := h.const_mul C0
    simpa only [Function.comp_apply, mul_zero] using hc
  have hle : ∀ᶠ X : ℕ in atTop,
      coreActualMainJanossyError κ d0 X ≤
        C0 * (Real.exp (11 * Real.log (Real.log (X : ℝ)) ^ 4) *
          (X : ℝ) ^ (-ε)) := by
    filter_upwards [eventually_profileFits hκ hd0,
      eventually_windowNX_ge_half hε hKpos hbound,
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
          (eventually_ge_atTop 2)] with X hfit hN hG2
    let Ω := ahlSmall_omega κ X
    let L := profileL κ X
    let r := profileR L d0
    let err := K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)) /
      (windowNX X : ℝ)
    let ell := Real.log (Real.log (X : ℝ))
    have hX3 : 3 ≤ X := le_trans (by norm_num) hfit.1
    have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
    have hlog2 : 0 < Real.log (2 * (X : ℝ)) :=
      Real.log_pos (by
        have hX3r : (3 : ℝ) ≤ X := by exact_mod_cast hX3
        nlinarith)
    have hNpos : 0 < (windowNX X : ℝ) :=
      (div_pos hXpos (mul_pos (by norm_num) hlog2)).trans_le hN
    have herr0 : 0 ≤ err := by
      dsimp only [err]
      exact div_nonneg
        (mul_nonneg hKpos.le
          (add_nonneg
            (Real.rpow_nonneg
              (mul_nonneg (by norm_num) (Nat.cast_nonneg X)) _)
            (Real.rpow_nonneg (Nat.cast_nonneg X) _))) hNpos.le
    have hpoint : ∀ H ⊆ Ω, H.card ≤ r →
        |(rootedTupleCount X H : ℝ) / (windowNX X : ℝ) -
            rootedMainTerm X H / (windowNX X : ℝ)| ≤ err := by
      intro H hH hHr
      have hHsmall : H ⊆ ahlSmall_omega κ X := by
        simpa only [Ω] using hH
      have hHlarge : H ⊆ windowOmega κ X :=
        hHsmall.trans (ahlSmall_omega_subset_windowOmega κ X)
      have herrH := rooted_error_abs_le_kuperberg hKpos.le hbound hfit hHlarge
        (by simpa only [r, L] using hHr)
      rw [← sub_div, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right herrH hNpos.le
    have hsum := coreJanossyTransform_sum_sub_le Ω (profileR_ge L d0)
      herr0
      (a := fun H => (rootedTupleCount X H : ℝ) / (windowNX X : ℝ))
      (b := fun H => rootedMainTerm X H / (windowNX X : ℝ)) hpoint
    have hfinite : coreActualMainJanossyError κ d0 X ≤
        ((((r + 1) * (Ω.card + 1) ^ r : ℕ) : ℝ)) ^ 2 * err := by
      simpa only [coreActualMainJanossyError, Ω, L, r,
        coreJanossyTransform_div] using hsum
    have hcost : ((((r + 1) * (Ω.card + 1) ^ r : ℕ) : ℝ)) ^ 2 ≤
        Real.exp (10 * ell ^ 4) := by
      simpa only [Ω, L, r, ell] using small_combination_cost_le_exp hfit hG2
    have hInv : (1 : ℝ) / (windowNX X : ℝ) ≤
        (2 * Real.log (2 * (X : ℝ))) / (X : ℝ) := by
      have hden : 0 < (X : ℝ) / (2 * Real.log (2 * (X : ℝ))) :=
        div_pos hXpos (mul_pos (by norm_num) hlog2)
      have hi := one_div_le_one_div_of_le hden hN
      have hre : (1 : ℝ) /
          ((X : ℝ) / (2 * Real.log (2 * (X : ℝ)))) =
          (2 * Real.log (2 * (X : ℝ))) / (X : ℝ) := by
        field_simp [hXpos.ne', hlog2.ne']
      rwa [hre] at hi
    have h2pow : (2 * X : ℝ) ^ (1 - ε) =
        (2 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε) := by
      rw [Real.mul_rpow (by norm_num) hXpos.le]
    have herrForm : err =
        (K * ((2 : ℝ) ^ (1 - ε) + 1) * (X : ℝ) ^ (1 - ε)) *
          ((windowNX X : ℝ)⁻¹) := by
      dsimp only [err]
      rw [h2pow, div_eq_mul_inv]
      ring
    have herrLe : err ≤
        C0 * (Real.exp (ell ^ 4) * (X : ℝ) ^ (-ε)) := by
      have hnum0 : 0 ≤ K * ((2 : ℝ) ^ (1 - ε) + 1) *
          (X : ℝ) ^ (1 - ε) := by positivity
      have hInv' : ((windowNX X : ℝ)⁻¹) ≤
          (2 * Real.log (2 * (X : ℝ))) / (X : ℝ) := by
        simpa only [one_div] using hInv
      have hxratio : (X : ℝ) ^ (1 - ε) * ((X : ℝ)⁻¹) =
          (X : ℝ) ^ (-ε) := by
        rw [← div_eq_mul_inv, ← Real.rpow_sub_one hXpos.ne']
        congr 1
        ring
      have hscaleEq :
          (K * ((2 : ℝ) ^ (1 - ε) + 1) * (X : ℝ) ^ (1 - ε)) *
              ((2 * Real.log (2 * (X : ℝ))) / (X : ℝ)) =
            2 * K * ((2 : ℝ) ^ (1 - ε) + 1) *
              Real.log (2 * (X : ℝ)) *
                ((X : ℝ) ^ (1 - ε) * ((X : ℝ)⁻¹)) := by
        rw [div_eq_mul_inv]
        ring
      rw [herrForm]
      calc
        (K * ((2 : ℝ) ^ (1 - ε) + 1) * (X : ℝ) ^ (1 - ε)) *
            ((windowNX X : ℝ)⁻¹) ≤
          (K * ((2 : ℝ) ^ (1 - ε) + 1) * (X : ℝ) ^ (1 - ε)) *
            ((2 * Real.log (2 * (X : ℝ))) / (X : ℝ)) :=
          mul_le_mul_of_nonneg_left hInv' hnum0
        _ = 2 * K * ((2 : ℝ) ^ (1 - ε) + 1) *
            Real.log (2 * (X : ℝ)) * (X : ℝ) ^ (-ε) := by
          rw [hscaleEq, hxratio]
        _ ≤ 4 * K * ((2 : ℝ) ^ (1 - ε) + 1) *
            Real.log (X : ℝ) * (X : ℝ) ^ (-ε) := by
          have hlog := log_two_mul_le_two_log_core hX3
          have hc0 : 0 ≤ 2 * K * ((2 : ℝ) ^ (1 - ε) + 1) :=
            mul_nonneg
              (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hKpos.le)
              (add_nonneg
                (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (1 - ε))
                (show (0 : ℝ) ≤ 1 by norm_num))
          calc
            2 * K * ((2 : ℝ) ^ (1 - ε) + 1) *
                Real.log (2 * (X : ℝ)) * (X : ℝ) ^ (-ε) =
              (2 * K * ((2 : ℝ) ^ (1 - ε) + 1)) *
                Real.log (2 * (X : ℝ)) * (X : ℝ) ^ (-ε) := by ring
            _ ≤ (2 * K * ((2 : ℝ) ^ (1 - ε) + 1)) *
                (2 * Real.log (X : ℝ)) * (X : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hlog hc0)
                (Real.rpow_nonneg hXpos.le (-ε))
            _ = 4 * K * ((2 : ℝ) ^ (1 - ε) + 1) *
                Real.log (X : ℝ) * (X : ℝ) ^ (-ε) := by ring
        _ ≤ C0 * (Real.exp (ell ^ 4) * (X : ℝ) ^ (-ε)) := by
          have hell1 : 1 < ell := by
            dsimp only [ell]
            exact one_lt_log_log_of_sixteen_le hfit.1
          have hlogexp : Real.log (X : ℝ) ≤ Real.exp (ell ^ 4) := by
            have hlogpos : 0 < Real.log (X : ℝ) := zero_lt_two.trans_le hG2
            have heq : Real.log (X : ℝ) = Real.exp ell := by
              dsimp only [ell]
              exact (Real.exp_log hlogpos).symm
            rw [heq]
            exact Real.exp_le_exp.mpr
              (le_self_pow₀ hell1.le (by omega : 4 ≠ 0))
          dsimp only [C0]
          have hc0 : 0 ≤ 4 * K * ((2 : ℝ) ^ (1 - ε) + 1) :=
            mul_nonneg
              (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hKpos.le)
              (add_nonneg
                (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (1 - ε))
                (show (0 : ℝ) ≤ 1 by norm_num))
          simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlogexp hc0)
              (Real.rpow_nonneg hXpos.le (-ε)))
    have htotal :
        ((((r + 1) * (Ω.card + 1) ^ r : ℕ) : ℝ)) ^ 2 * err ≤
          C0 * (Real.exp (11 * ell ^ 4) * (X : ℝ) ^ (-ε)) := by
      have hexp : Real.exp (10 * ell ^ 4) * Real.exp (ell ^ 4) =
          Real.exp (11 * ell ^ 4) := by
        rw [← Real.exp_add]
        ring_nf
      calc
        ((((r + 1) * (Ω.card + 1) ^ r : ℕ) : ℝ)) ^ 2 * err ≤
            Real.exp (10 * ell ^ 4) *
              (C0 * (Real.exp (ell ^ 4) * (X : ℝ) ^ (-ε))) :=
          mul_le_mul hcost herrLe herr0 (Real.exp_nonneg _)
        _ = C0 * ((Real.exp (10 * ell ^ 4) * Real.exp (ell ^ 4)) *
            (X : ℝ) ^ (-ε)) := by ring
        _ = C0 * (Real.exp (11 * ell ^ 4) * (X : ℝ) ^ (-ε)) := by rw [hexp]
    exact hfinite.trans (htotal.trans_eq (by simp only [C0, ell]))
  refine squeeze_zero' ?_ hle hupper
  exact Eventually.of_forall fun X => by
    unfold coreActualMainJanossyError
    exact sum_nonneg fun K _ => abs_nonneg _

theorem corePrimeComparisonQuantity_nonneg
    {X L r : ℕ} {Ω : Finset ℕ} (hN : 0 < windowNX X)
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L)) :
    0 ≤ corePrimeComparisonQuantity X Ω L r 1 := by
  let μ := coreActualPatternMass X Ω
  have hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U := fun U _ =>
    coreActualPatternMass_nonneg X Ω U
  have hJ :
      (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        Stopped.janossyTrunc Ω μ L r K) ≤
      ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        Stopped.shortShapeMass Ω μ L K := by
    apply sum_le_sum
    intro K hK
    exact Stopped.janossyTrunc_le_shortShapeMass hL hr hpar
      (mem_filter.mp hK).2 hμ
  have hfail : 0 ≤ Stopped.failureMass Ω μ L := by
    unfold Stopped.failureMass
    exact sum_nonneg fun U hU => hμ U (mem_filter.mp hU).1
  have hmass := Stopped.shortShapeMass_add_failureMass
    (Ω := Ω) (μ := μ) (L := L)
  have hfirst : 0 ≤
      (∑ U ∈ Ω.powerset, μ U) -
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          Stopped.janossyTrunc Ω μ L r K := by
    linarith
  have hmax : 0 ≤
      ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        max (Stopped.janossyTrunc Ω μ L r K -
          coreJanossyTransform Ω (rootedMainTerm X) L r K /
            (windowNX X : ℝ)) 0 :=
    sum_nonneg fun K _ => le_max_right _ _
  rw [← corePrimeComparisonQuantity_eq_budget hN Ω L r 1]
  unfold Stopped.stoppedPositiveBudgetAgainst
  simpa only [one_mul] using add_nonneg hfirst hmax

/-- Priority-A arithmetic endpoint: Kuperberg implies the concrete frozen
`D(X,1)` quantity tends to zero on the `(6/5)LG` small window, with
`r = profileR L 20`. -/
theorem tendsto_corePrimeComparisonQuantity_small_of_kuperberg
    (hK : KuperbergConj13) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      corePrimeComparisonQuantity X (ahlSmall_omega κ X)
        (profileL κ X) (profileR (profileL κ X) 20) 1)
      atTop (nhds 0) := by
  have hmass := PrimeCountingNormalization.mixZeta_abs_zero_of_kuperberg hK
  have hfail := tendsto_finiteRootMixUnnorm_small_failureMass_of_kuperberg hK hκ
  have hrem := tendsto_finiteRootMixUnnorm_small_modelRemainder_of_kuperberg hK hκ
  have hactual := tendsto_coreActualMainJanossyError_of_kuperberg hK hκ
    (by norm_num : (0 : ℝ) < 20)
  have hcal := tendsto_coreMixtureJanossyCalibration_of_kuperberg hK hκ
    (by norm_num : (0 : ℝ) < 20)
  have hupper : Tendsto (fun X : ℕ =>
      |1 - mixZeta X| +
        Stopped.failureMass (ahlSmall_omega κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X)) (profileL κ X) +
        Stopped.modelRemainder (ahlSmall_omega κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X))
          (profileL κ X) (profileR (profileL κ X) 20) +
        coreActualMainJanossyError κ 20 X +
        coreMixtureJanossyCalibration κ 20 X) atTop (nhds 0) := by
    simpa only [add_zero] using (((hmass.add hfail).add hrem).add hactual).add hcal
  have hle : ∀ᶠ X : ℕ in atTop,
      corePrimeComparisonQuantity X (ahlSmall_omega κ X)
          (profileL κ X) (profileR (profileL κ X) 20) 1 ≤
        |1 - mixZeta X| +
          Stopped.failureMass (ahlSmall_omega κ X)
            (finiteRootMixUnnorm X (ahlSmall_window κ X)) (profileL κ X) +
          Stopped.modelRemainder (ahlSmall_omega κ X)
            (finiteRootMixUnnorm X (ahlSmall_window κ X))
            (profileL κ X) (profileR (profileL κ X) 20) +
          coreActualMainJanossyError κ 20 X +
          coreMixtureJanossyCalibration κ 20 X := by
    filter_upwards [eventually_one_le_profileL hκ, eventually_ge_atTop 1]
      with X hL hX
    have hN := windowNX_pos (by omega : 0 < X)
    have h := corePrimeComparisonQuantity_le_absolute_errors
      (Ω := ahlSmall_omega κ X)
      (ν := finiteRootMixUnnorm X (ahlSmall_window κ X)) hN hL
      (crtMixProf_le_at κ 20 X) (crtMixProf_odd_at κ 20 X)
    have hsum :
        (∑ U ∈ (ahlSmall_omega κ X).powerset,
          finiteRootMixUnnorm X (ahlSmall_window κ X) U) = mixZeta X := by
      simpa only [ahlSmall_omega, offsetWindow] using
        crtMixUnnorm_sum X (ahlSmall_window κ X) hN
    rw [hsum] at h
    change corePrimeComparisonQuantity X (ahlSmall_omega κ X)
          (profileL κ X) (profileR (profileL κ X) 20) 1 ≤
        |1 - mixZeta X| +
          Stopped.failureMass (ahlSmall_omega κ X)
            (finiteRootMixUnnorm X (ahlSmall_window κ X)) (profileL κ X) +
          Stopped.modelRemainder (ahlSmall_omega κ X)
            (finiteRootMixUnnorm X (ahlSmall_window κ X))
            (profileL κ X) (profileR (profileL κ X) 20) +
          coreActualMainJanossyError κ 20 X +
          coreMixtureJanossyCalibration κ 20 X at h
    exact h
  refine squeeze_zero' ?_ hle hupper
  filter_upwards [eventually_one_le_profileL hκ, eventually_ge_atTop 1]
      with X hL hX
  exact corePrimeComparisonQuantity_nonneg (windowNX_pos (by omega : 0 < X))
    hL (crtMixProf_le_at κ 20 X) (crtMixProf_odd_at κ 20 X)

end

end PrimeGapNormality.Prime
