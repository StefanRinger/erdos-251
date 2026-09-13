import PrimeGapNormality.Prime.CoreCutoffCalibration
import PrimeGapNormality.Prime.CoreJanossyCalibration
import PrimeGapNormality.Prime.AhlSmallOfLarge
import PrimeGapNormality.Prime.CrtLogSqLeRpow
import PrimeGapNormality.Prime.CrtNestedCutoffVRatio
import PrimeGapNormality.Prime.ProfileSLeSieveCutoff
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Calibration of the literal unnormalized finite root mixture

This file keeps the normalization required by the positive-comparison
argument: `finiteRootMixUnnorm` has inclusion masses `Σ P_t / N_X`.
The cutoff error is summed before division by `N_X`, and the Riemann error
then identifies the result with the Hardy--Littlewood window main term.
No `mixZeta` error is distributed over individual Janossy cells.
-/

open Filter Finset
open scoped Classical Topology

namespace PrimeGapNormality.Prime

noncomputable section

/-- The paper window main term is exactly the singular series times the
dyadic comparison integral used by `MixRiemann`. -/
theorem rootedMainTerm_eq_singularSeries_mul_mixLogPowIntegral
    {X : ℕ} (hX : 2 ≤ X) (H : Finset ℕ) :
    rootedMainTerm X H =
      singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1) := by
  have hXR : (2 : ℝ) ≤ X := Nat.cast_le.mpr hX
  have hab : (X : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by exact_mod_cast (by omega : X ≤ 2 * X)
  unfold rootedMainTerm mixLogPowIntegral mixLogPow
  rw [← hlIntegral_sub (H.card + 1) hXR hab]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Finite, uniform numerator calibration.  The two hypotheses involving
the cutoff are stated for every integer scale in the literal mixture
support; later profile lemmas discharge them without a free calibration
assumption. -/
theorem finiteRootMixUnnorm_inclusionNumerator_relative_error_le
    {X S r : ℕ} {H : Finset ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ))
    (hH : H ⊆ offsetWindow S) (hHr : H.card ≤ r)
    (hcut : ∀ t ∈ mixScale X, S < sieveCutoff (t : ℝ))
    (hvcut : ∀ t ∈ mixScale X,
      2 * (r + 1) ^ 2 ≤ sieveCutoff (t : ℝ))
    (hrlog : (r + 1 : ℝ) ≤ Real.log X) :
    |(∑ t ∈ mixScale X,
          finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) -
        rootedMainTerm X H| ≤
      (3 * (r + 1 : ℝ) ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst) +
          (2 : ℝ) / X) * rootedMainTerm X H := by
  have hXgt2 : (2 : ℝ) < X :=
    (Real.exp_one_gt_two.trans
      (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16))).trans_le hX
  have hXnat : 2 < X := by exact_mod_cast hXgt2
  have hX2 : 2 ≤ X := hXnat.le
  have hX3 : 3 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have h0 : 0 ∉ H := by
    intro hz
    have := hH hz
    simp [offsetWindow] at this
  have hcard : (insert 0 H).card = H.card + 1 := card_insert_of_notMem h0
  have hcardle : (insert 0 H).card ≤ r + 1 := by rw [hcard]; omega
  have hcardsq : (insert 0 H).card ^ 2 ≤ (r + 1) ^ 2 :=
    pow_le_pow_left' hcardle 2
  have hE : ∀ n ∈ insert 0 H, n ≤ S := by
    intro n hn
    rcases mem_insert.mp hn with rfl | hn
    · omega
    · exact (mem_Icc.mp (hH hn)).2
  have ht0mem : 2 * X ∈ mixScale X := by
    simp only [mixScale, mem_Ioc]
    omega
  have ht0exp : Real.exp 16 ≤ ((2 * X : ℕ) : ℝ) := by
    exact hX.trans (Nat.cast_le.mpr (by omega : X ≤ 2 * X))
  have ht0one : (1 : ℝ) < (2 * X : ℕ) :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le ht0exp
  have ht0spec := sieveCutoff_spec ht0one
  have ht0cut := hcut (2 * X) ht0mem
  have ht0v : 2 * (insert 0 H).card ^ 2 ≤ sieveCutoff ((2 * X : ℕ) : ℝ) :=
    (Nat.mul_le_mul_left 2 hcardsq).trans (hvcut (2 * X) ht0mem)
  have hSS : 0 ≤ singularSeries (insert 0 H) :=
    singularSeries_nonneg_of_completion hE ht0cut
      (by have := isSieveCutoff_ge_sixteen ht0exp ht0spec; omega) ht0v
  let a : ℝ :=
    3 * (r + 1 : ℝ) ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst)
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    positivity
  have hpoint : ∀ t ∈ mixScale X,
      |finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ)) -
          singularSeries (insert 0 H) * mixLogPow (H.card + 1) t| ≤
        a * (singularSeries (insert 0 H) * mixLogPow (H.card + 1) t) := by
    intro t ht
    have htI : t ∈ Ioc X (2 * X) := by simpa only [mixScale] using ht
    have hXt : (X : ℝ) ≤ t := Nat.cast_le.mpr (mem_Ioc.mp htI).1.le
    have htexp : Real.exp 16 ≤ (t : ℝ) := hX.trans hXt
    have hv : 2 * (insert 0 H).card ^ 2 ≤ sieveCutoff (t : ℝ) :=
      (Nat.mul_le_mul_left 2 hcardsq).trans (hvcut t ht)
    have hraw := finiteTupleSieveProduct_sieveCutoff_rpow_error_le
      (E := insert 0 H) (S := S) htexp hE (hcut t ht) hv
    rw [hcard] at hraw
    have hrpow : (t : ℝ) ^ (-eulerProdLowerConst) ≤
        (X : ℝ) ^ (-eulerProdLowerConst) :=
      Real.rpow_le_rpow_of_nonpos hXpos hXt
        (neg_nonpos.mpr eulerProdLowerConst_pos.le)
    have hcardsqR : ((insert 0 H).card : ℝ) ^ 2 ≤ (r + 1 : ℝ) ^ 2 := by
      exact_mod_cast hcardsq
    have hcoef :
        3 * ((insert 0 H).card : ℝ) ^ 2 *
            (t : ℝ) ^ (-eulerProdLowerConst) ≤ a := by
      dsimp only [a]
      calc
        3 * ((insert 0 H).card : ℝ) ^ 2 *
            (t : ℝ) ^ (-eulerProdLowerConst) ≤
            3 * (r + 1 : ℝ) ^ 2 *
              (t : ℝ) ^ (-eulerProdLowerConst) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcardsqR (by norm_num))
            (Real.rpow_nonneg (Nat.cast_nonneg t) _)
        _ ≤ 3 * (r + 1 : ℝ) ^ 2 *
              (X : ℝ) ^ (-eulerProdLowerConst) :=
          mul_le_mul_of_nonneg_left hrpow
            (mul_nonneg (by norm_num) (sq_nonneg _))
    rw [hcard] at hcoef
    have hmain0 :
        0 ≤ singularSeries (insert 0 H) * mixLogPow (H.card + 1) t :=
      mul_nonneg hSS
        (mixLogPow_nonneg (H.card + 1)
          ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le htexp))
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoef hmain0)
  have hsumdiff :
      (∑ t ∈ mixScale X,
          finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) -
          singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1) =
        ∑ t ∈ mixScale X,
          (finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ)) -
            singularSeries (insert 0 H) * mixLogPow (H.card + 1) t) := by
    rw [mixLogPowSum, mul_sum, sum_sub_distrib]
  have hsumcal :
      |(∑ t ∈ mixScale X,
          finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) -
          singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1)| ≤
        a * (singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1)) := by
    rw [hsumdiff]
    calc
      |∑ t ∈ mixScale X,
          (finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ)) -
            singularSeries (insert 0 H) * mixLogPow (H.card + 1) t)| ≤
          ∑ t ∈ mixScale X,
            |finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ)) -
              singularSeries (insert 0 H) * mixLogPow (H.card + 1) t| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ mixScale X,
          a * (singularSeries (insert 0 H) * mixLogPow (H.card + 1) t) :=
        sum_le_sum hpoint
      _ = ∑ t ∈ mixScale X,
          (a * singularSeries (insert 0 H)) * mixLogPow (H.card + 1) t := by
        apply sum_congr rfl
        intro t _
        ring
      _ = (a * singularSeries (insert 0 H)) *
          (∑ t ∈ mixScale X, mixLogPow (H.card + 1) t) :=
        (mul_sum _ _ _).symm
      _ = a * (singularSeries (insert 0 H) *
          mixLogPowSum X (H.card + 1)) := by
        rw [mixLogPowSum]
        ring
  have hv1 : 1 ≤ H.card + 1 := by omega
  have hvlog : (H.card + 1 : ℝ) ≤ Real.log X := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hrlog ⊢
    exact (add_le_add (Nat.cast_le.mpr hHr) le_rfl).trans hrlog
  have hsumle := mixLogPow_sum_le_integral (H.card + 1) hX2
  have hcalInt :
      |(∑ t ∈ mixScale X,
          finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) -
          singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1)| ≤
        a * (singularSeries (insert 0 H) *
          mixLogPowIntegral X (H.card + 1)) := by
    refine hsumcal.trans ?_
    calc
      a * (singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1)) =
          (a * singularSeries (insert 0 H)) * mixLogPowSum X (H.card + 1) := by ring
      _ ≤ (a * singularSeries (insert 0 H)) *
          mixLogPowIntegral X (H.card + 1) :=
        mul_le_mul_of_nonneg_left hsumle (mul_nonneg ha0 hSS)
      _ = a * (singularSeries (insert 0 H) *
          mixLogPowIntegral X (H.card + 1)) := by ring
  have hriem0 :
      0 ≤ mixLogPowIntegral X (H.card + 1) -
        mixLogPowSum X (H.card + 1) :=
    (mixLogPow_riemann (H.card + 1) hX2 hv1).1
  have hvlog' : ((H.card + 1 : ℕ) : ℝ) ≤ Real.log X := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact hvlog
  have hriem := mixLogPow_rel_err (H.card + 1) hX3 hv1 hvlog'
  have hriemAbs :
      |singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1) -
          singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1)| ≤
        ((2 : ℝ) / X) *
          (singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1)) := by
    rw [abs_sub_comm]
    have hnonneg : 0 ≤ singularSeries (insert 0 H) *
        (mixLogPowIntegral X (H.card + 1) - mixLogPowSum X (H.card + 1)) :=
      mul_nonneg hSS hriem0
    rw [show singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1) -
        singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1) =
          singularSeries (insert 0 H) *
            (mixLogPowIntegral X (H.card + 1) -
              mixLogPowSum X (H.card + 1)) by ring,
      abs_of_nonneg hnonneg]
    calc
      singularSeries (insert 0 H) *
          (mixLogPowIntegral X (H.card + 1) -
            mixLogPowSum X (H.card + 1)) ≤
          singularSeries (insert 0 H) *
            (((2 : ℝ) / X) * mixLogPowIntegral X (H.card + 1)) :=
        mul_le_mul_of_nonneg_left hriem hSS
      _ = ((2 : ℝ) / X) *
          (singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1)) := by ring
  rw [rootedMainTerm_eq_singularSeries_mul_mixLogPowIntegral hX2]
  have hsplit :
      (∑ t ∈ mixScale X,
          finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) -
          singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1) =
        ((∑ t ∈ mixScale X,
            finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) -
            singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1)) +
        (singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1) -
            singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1)) := by ring
  rw [hsplit]
  calc
    |((∑ t ∈ mixScale X,
          finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) -
          singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1)) +
        (singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1) -
          singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1))| ≤
        |(∑ t ∈ mixScale X,
          finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) -
          singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1)| +
        |singularSeries (insert 0 H) * mixLogPowSum X (H.card + 1) -
          singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1)| :=
      abs_add_le _ _
    _ ≤ a * (singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1)) +
        ((2 : ℝ) / X) *
          (singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1)) :=
      add_le_add hcalInt hriemAbs
    _ = (3 * (r + 1 : ℝ) ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst) +
          (2 : ℝ) / X) *
        (singularSeries (insert 0 H) * mixLogPowIntegral X (H.card + 1)) := by
      dsimp only [a]
      ring

/-- Inclusion-mass form of the finite calibration.  It uses the exact
unnormalized mixture identity, so no `mixZeta` term appears. -/
theorem finiteRootMixUnnorm_inclusionMass_relative_error_le
    {X S r : ℕ} {H : Finset ℕ}
    (hN : 0 < windowNX X)
    (hX : Real.exp 16 ≤ (X : ℝ))
    (hH : H ⊆ offsetWindow S) (hHr : H.card ≤ r)
    (hcut : ∀ t ∈ mixScale X, S < sieveCutoff (t : ℝ))
    (hvcut : ∀ t ∈ mixScale X,
      2 * (r + 1) ^ 2 ≤ sieveCutoff (t : ℝ))
    (hrlog : (r + 1 : ℝ) ≤ Real.log X) :
    |Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H -
        rootedMainTerm X H / (windowNX X : ℝ)| ≤
      (3 * (r + 1 : ℝ) ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst) +
          (2 : ℝ) / X) * (rootedMainTerm X H / (windowNX X : ℝ)) := by
  rw [finiteRootMixUnnorm_inclusionMass_eq_product_sum X S hH, ← sub_div]
  have hden : |(windowNX X : ℝ)| = (windowNX X : ℝ) :=
    abs_of_pos (Nat.cast_pos.mpr hN)
  rw [abs_div, hden]
  have hnum := finiteRootMixUnnorm_inclusionNumerator_relative_error_le
    hX hH hHr hcut hvcut hrlog
  have hdiv := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg (windowNX X))
  exact hdiv.trans_eq (by ring)

/-! ### Actual small profiles -/

/-- The calibration coefficient at the paper's small profile and its
Bonferroni depth. -/
noncomputable def coreMixtureRelativeError (κ d0 : ℝ) (X : ℕ) : ℝ :=
  3 * (profileR (profileL κ X) d0 + 1 : ℝ) ^ 2 *
      (X : ℝ) ^ (-eulerProdLowerConst) + (2 : ℝ) / X

private theorem ahlSmall_window_lt_profileS_of_one_le_profileL
    {κ : ℝ} {X : ℕ} (hL : 1 ≤ profileL κ X) :
    ahlSmall_window κ X < profileS κ X := by
  have hLR : (1 : ℝ) ≤ profileL κ X := by exact_mod_cast hL
  have hG : (1 : ℝ) ≤ windowG X := ahlSmall_windowG_one_le X
  have hLG : (1 : ℝ) ≤ (profileL κ X : ℝ) * windowG X :=
    one_le_mul_of_one_le_of_one_le hLR hG
  have ha0 : 0 ≤ (6 / 5 : ℝ) * (profileL κ X : ℝ) * windowG X := by
    positivity
  have hgap :
      (6 / 5 : ℝ) * (profileL κ X : ℝ) * windowG X + 1 ≤
        4 * (profileL κ X : ℝ) * windowG X := by
    nlinarith
  unfold ahlSmall_window profileS
  apply Nat.succ_le_iff.mp
  apply Nat.le_floor
  have hfloor := Nat.floor_le ha0
  norm_num only [Nat.cast_add, Nat.cast_one]
  simpa only [Nat.cast_succ] using (add_le_add hfloor le_rfl).trans hgap

private theorem tendsto_loglog_pow_six_div_log_nat :
    Tendsto (fun X : ℕ =>
      Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ))
      atTop (nhds 0) := by
  have h :=
    (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 6 (by norm_num)).comp
      Real.tendsto_log_atTop
  have hn := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [one_mul, add_zero, Function.comp_apply] at hn
  change Tendsto (fun X : ℕ =>
    Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ)) atTop (nhds 0) at hn
  exact hn

private theorem eventually_two_loglog_pow_six_le_log :
    ∀ᶠ X : ℕ in atTop,
      2 * Real.log (Real.log (X : ℝ)) ^ 6 ≤ Real.log (X : ℝ) := by
  filter_upwards [eventually_ge_atTop 16,
    tendsto_loglog_pow_six_div_log_nat.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))]
      with X hX hball
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) (Nat.cast_le.mpr hX))
  have hll : 0 < Real.log (Real.log (X : ℝ)) :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (one_lt_log_log_of_sixteen_le hX)
  have hratio0 : 0 ≤
      Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ) :=
    div_nonneg (pow_nonneg hll.le 6) hlog.le
  have hratio :
      Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ) < 1 / 2 := by
    have habs :
        |Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ) - 0| < 1 / 2 := by
      exact hball
    rw [sub_zero, abs_of_nonneg hratio0] at habs
    exact habs
  have hmul := (div_lt_iff₀ hlog).mp hratio
  linarith

private theorem eventual_small_profile_calibration_hypotheses
    {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    ∀ᶠ X : ℕ in atTop,
      Real.exp 16 ≤ (X : ℝ) ∧
      (∀ t ∈ mixScale X,
        ahlSmall_window κ X < sieveCutoff (t : ℝ)) ∧
      (∀ t ∈ mixScale X,
        2 * (profileR (profileL κ X) d0 + 1) ^ 2 ≤
          sieveCutoff (t : ℝ)) ∧
      (profileR (profileL κ X) d0 + 1 : ℝ) ≤ Real.log X := by
  filter_upwards [
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 16)),
    eventually_one_le_profileL hκ,
    eventually_profileS_le_sieveCutoff hκ,
    eventually_profileFits hκ hd0,
    eventually_two_loglog_pow_six_le_log,
    crtLogSq_eventually_nat_log_sq_le_rpow]
      with X hX hL hScut hfit hloglog hlogsq
  have hX1 : (1 : ℝ) < X :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hX
  have hsmall : ahlSmall_window κ X < profileS κ X :=
    ahlSmall_window_lt_profileS_of_one_le_profileL hL
  have hScutNat : profileS κ X ≤ sieveCutoff (X : ℝ) := Nat.cast_le.mp hScut
  have hcut : ∀ t ∈ mixScale X,
      ahlSmall_window κ X < sieveCutoff (t : ℝ) := by
    intro t ht
    have hXt : (X : ℝ) < t := Nat.cast_lt.mpr (mem_Ioc.mp ht).1
    exact lt_of_lt_of_le hsmall
      (hScutNat.trans (crtNestVR_sieveCutoff_mono hX1 hXt))
  let R : ℝ := (profileR (profileL κ X) d0 + 1 : ℕ)
  let ell : ℝ := Real.log (Real.log (X : ℝ))
  let G : ℝ := Real.log (X : ℝ)
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hell0 : 0 ≤ ell := by
    dsimp only [ell]
    exact (lt_trans (by norm_num : (0 : ℝ) < 1)
      (one_lt_log_log_of_sixteen_le hfit.1)).le
  have hG1 : 1 ≤ G := by
    dsimp only [G]
    exact (one_lt_log_of_three_le (le_trans (by norm_num) hfit.1)).le
  have hRell : R ≤ ell ^ 3 := by
    simpa only [R, ell, Nat.cast_add, Nat.cast_one] using hfit.2.2.1
  have hRsq : R ^ 2 ≤ ell ^ 6 := by
    calc
      R ^ 2 ≤ (ell ^ 3) ^ 2 := pow_le_pow_left₀ hR0 hRell 2
      _ = ell ^ 6 := by ring
  have htwoRsq : 2 * R ^ 2 ≤ G := by
    exact (mul_le_mul_of_nonneg_left hRsq (by norm_num)).trans
      (by simpa only [ell, G] using hloglog)
  have hRlog : R ≤ G := by
    nlinarith [sq_nonneg (R - 1 / 2)]
  have htwoRsqRpow : 2 * R ^ 2 ≤ (X : ℝ) ^ eulerProdLowerConst := by
    calc
      2 * R ^ 2 ≤ G := htwoRsq
      _ ≤ G ^ 2 := le_self_pow₀ hG1 (by omega : 2 ≠ 0)
      _ ≤ (X : ℝ) ^ eulerProdLowerConst := by
        simpa only [G] using hlogsq
  have hcutX : (X : ℝ) ^ eulerProdLowerConst ≤ sieveCutoff (X : ℝ) :=
    isSieveCutoff_rpow hX (sieveCutoff_spec hX1)
  dsimp only [R] at htwoRsqRpow
  have hvX :
      2 * (profileR (profileL κ X) d0 + 1) ^ 2 ≤ sieveCutoff (X : ℝ) := by
    exact_mod_cast htwoRsqRpow.trans hcutX
  have hvcut : ∀ t ∈ mixScale X,
      2 * (profileR (profileL κ X) d0 + 1) ^ 2 ≤
        sieveCutoff (t : ℝ) := by
    intro t ht
    have hXt : (X : ℝ) < t := Nat.cast_lt.mpr (mem_Ioc.mp ht).1
    exact hvX.trans (crtNestVR_sieveCutoff_mono hX1 hXt)
  exact ⟨hX, hcut, hvcut, by
    simpa only [R, G, Nat.cast_add, Nat.cast_one] using hRlog⟩

/-- The actual calibration coefficient tends to zero at the paper's small
profiles.  In particular, it is not a free `hcal` assumption. -/
theorem tendsto_coreMixtureRelativeError {κ d0 : ℝ}
    (hκ : 0 < κ) (hd0 : 0 < d0) :
    Tendsto (coreMixtureRelativeError κ d0) atTop (nhds 0) := by
  have hmain0 : Tendsto (fun X : ℕ =>
      3 * (Real.log (X : ℝ) ^ (2 : ℝ) /
        (X : ℝ) ^ eulerProdLowerConst)) atTop (nhds 0) := by
    simpa using
      (crtLogSq_tendsto_log_sq_div_rpow.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (3 : ℝ)
  have hmain : Tendsto (fun X : ℕ =>
      3 * Real.log (X : ℝ) ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst))
      atTop (nhds 0) := by
    apply hmain0.congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    have hX0 : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
    rw [Real.rpow_neg hX0.le, Real.rpow_two, div_eq_mul_inv]
    ring
  have htwo : Tendsto (fun X : ℕ => (2 : ℝ) / X) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  have henv : Tendsto (fun X : ℕ =>
      3 * Real.log (X : ℝ) ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst) +
        (2 : ℝ) / X) atTop (nhds 0) := by
    simpa using hmain.add htwo
  refine squeeze_zero' (Eventually.of_forall fun X => ?_) ?_ henv
  · unfold coreMixtureRelativeError
    positivity
  · filter_upwards [eventual_small_profile_calibration_hypotheses hκ hd0,
      eventually_profileFits hκ hd0,
      eventually_two_loglog_pow_six_le_log] with X hh hfit hloglog
    let R : ℝ := (profileR (profileL κ X) d0 + 1 : ℕ)
    let ell : ℝ := Real.log (Real.log (X : ℝ))
    let G : ℝ := Real.log (X : ℝ)
    have hR0 : 0 ≤ R := by dsimp only [R]; positivity
    have hRell : R ≤ ell ^ 3 := by
      simpa only [R, ell, Nat.cast_add, Nat.cast_one] using hfit.2.2.1
    have hRsq : R ^ 2 ≤ ell ^ 6 := by
      calc
        R ^ 2 ≤ (ell ^ 3) ^ 2 := pow_le_pow_left₀ hR0 hRell 2
        _ = ell ^ 6 := by ring
    have hRsqlog : R ^ 2 ≤ G ^ 2 := by
      have htwo : 2 * R ^ 2 ≤ G :=
        (mul_le_mul_of_nonneg_left hRsq (by norm_num)).trans
          (by simpa only [ell, G] using hloglog)
      have hG1 : 1 ≤ G := by
        dsimp only [G]
        exact (one_lt_log_of_three_le (le_trans (by norm_num) hfit.1)).le
      exact (le_trans (by linarith) (le_self_pow₀ hG1 (by omega : 2 ≠ 0)))
    have hRsqlog' :
        (profileR (profileL κ X) d0 + 1 : ℝ) ^ 2 ≤
          Real.log (X : ℝ) ^ 2 := by
      simpa only [R, G, Nat.cast_add, Nat.cast_one] using hRsqlog
    unfold coreMixtureRelativeError
    exact add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRsqlog' (by norm_num))
        (Real.rpow_nonneg (Nat.cast_nonneg X) _)) le_rfl

/-- Uniform inclusion-mass calibration on the actual small window, with
the explicit coefficient above and no free calibration hypothesis. -/
theorem eventually_finiteRootMixUnnorm_small_inclusionMass_relative_error_le
    {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    ∀ᶠ X : ℕ in atTop,
      ∀ H ⊆ ahlSmall_omega κ X,
        H.card ≤ profileR (profileL κ X) d0 →
        |Stopped.inclusionMass (ahlSmall_omega κ X)
              (finiteRootMixUnnorm X (ahlSmall_window κ X)) H -
            rootedMainTerm X H / (windowNX X : ℝ)| ≤
          coreMixtureRelativeError κ d0 X *
            (rootedMainTerm X H / (windowNX X : ℝ)) := by
  filter_upwards [eventual_small_profile_calibration_hypotheses hκ hd0]
      with X hh
  intro H hH hHr
  have hH' : H ⊆ offsetWindow (ahlSmall_window κ X) := by
    simpa only [ahlSmall_omega, offsetWindow] using hH
  have hXpos : 0 < X := by
    have : (0 : ℝ) < X := (Real.exp_pos 16).trans_le hh.1
    exact Nat.cast_pos.mp this
  change |Stopped.inclusionMass (offsetWindow (ahlSmall_window κ X))
        (finiteRootMixUnnorm X (ahlSmall_window κ X)) H -
      rootedMainTerm X H / (windowNX X : ℝ)| ≤
    coreMixtureRelativeError κ d0 X *
      (rootedMainTerm X H / (windowNX X : ℝ))
  simpa only [coreMixtureRelativeError] using
    finiteRootMixUnnorm_inclusionMass_relative_error_le
      (windowNX_pos hXpos) hh.1 hH' hHr hh.2.1 hh.2.2.1 hh.2.2.2

end

end PrimeGapNormality.Prime
