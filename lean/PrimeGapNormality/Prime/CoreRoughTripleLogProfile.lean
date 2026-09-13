import PrimeGapNormality.Prime.CoreRoughLittleOProfile
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The explicit triple-log rough profile

The globally total function used here is

`Psi(t) = t / (log t * log (log t))`.

Only eventual positivity and differentiability are required by the rough
backend.  We prove its literal derivative formula, the weighted derivative
bound with constant one, divergence, and the paper's little-o condition.
Thus the corresponding actual cutoff supports every separately fixed base,
period and local polynomial through `CoreRoughLittleOProfile`.
-/

namespace PrimeGapNormality.Prime.CoreRoughTripleLogProfile

open Asymptotics Filter MvPolynomial CoreCyclic
open CoreRoughThreshold CoreRoughSyntheticScale CoreMovingRoughSequence
open scoped Topology Classical

noncomputable section

def tripleLogDen (t : ℝ) : ℝ :=
  Real.log t * Real.log (Real.log t)

def profile (t : ℝ) : ℝ :=
  t / tripleLogDen t

def profileDerivative (t : ℝ) : ℝ :=
  (tripleLogDen t - Real.log (Real.log t) - 1) / tripleLogDen t ^ 2

private theorem eventually_log_sq_le_sqrt :
    ∀ᶠ t : ℝ in atTop,
      Real.log t ^ 2 ≤ t ^ (1 / 2 : ℝ) := by
  have hnorm :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).eventuallyLE
  filter_upwards [hnorm, eventually_gt_atTop (1 : ℝ)] with t ht hlarge
  have ht0 : 0 < t := zero_lt_one.trans hlarge
  have hlog0 : 0 ≤ Real.log t := (Real.log_pos hlarge).le
  have hnum : 0 ≤ Real.log t ^ (2 : ℝ) := Real.rpow_nonneg hlog0 _
  have hden : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
  have hh : Real.log t ^ (2 : ℝ) ≤ t ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnum,
      abs_of_nonneg hden] using ht
  simpa only [Real.rpow_ofNat] using hh

/-- The totalized profile has the displayed derivative once both logarithmic
denominators are positive. -/
theorem profile_hasDerivAt {t : ℝ} (ht : 1 < t)
    (hlogOne : 1 < Real.log t) :
    HasDerivAt profile (profileDerivative t) t := by
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have hlogPos : 0 < Real.log t := Real.log_pos ht
  have hlog0 : Real.log t ≠ 0 := hlogPos.ne'
  have hloglog :=
    (Real.hasDerivAt_log hlog0).comp t (Real.hasDerivAt_log ht0)
  have hden : HasDerivAt tripleLogDen
      ((Real.log (Real.log t) + 1) / t) t := by
    have hraw := (Real.hasDerivAt_log ht0).mul hloglog
    change HasDerivAt (fun x : ℝ =>
      Real.log x * Real.log (Real.log x))
        (t⁻¹ * Real.log (Real.log t) +
          Real.log t * ((Real.log t)⁻¹ * t⁻¹)) t at hraw
    have hcoefficient :
        t⁻¹ * Real.log (Real.log t) +
            Real.log t * ((Real.log t)⁻¹ * t⁻¹) =
          (Real.log (Real.log t) + 1) / t := by
      field_simp [ht0, hlog0] <;> ring
    rw [hcoefficient] at hraw
    change HasDerivAt (fun x : ℝ => Real.log x * Real.log (Real.log x))
      ((Real.log (Real.log t) + 1) / t) t
    exact hraw
  have hden0 : tripleLogDen t ≠ 0 := by
    unfold tripleLogDen
    exact mul_ne_zero hlog0 (Real.log_pos hlogOne).ne'
  have hh := (hasDerivAt_id t).fun_div hden hden0
  simp only [id_eq, one_mul] at hh
  have hcoefficient :
      (tripleLogDen t - t * ((Real.log (Real.log t) + 1) / t)) /
          tripleLogDen t ^ 2 = profileDerivative t := by
    unfold profileDerivative
    field_simp [ht0, hden0] <;> ring
  rw [hcoefficient] at hh
  change HasDerivAt (fun x : ℝ => x / tripleLogDen x)
    (profileDerivative t) t
  exact hh

/-- The triple-log profile tends to infinity. -/
theorem tendsto_profile_atTop : Tendsto profile atTop atTop := by
  have hroot : Tendsto (fun t : ℝ => t ^ (1 / 2 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  refine tendsto_atTop_mono' atTop ?_ hroot
  filter_upwards [eventually_log_sq_le_sqrt,
    Real.tendsto_log_atTop.eventually_ge_atTop 4,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with t hsq hlog4 hloglog1 ht
  simp only [Function.comp_apply] at hloglog1
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hlogPos : 0 < Real.log t := Real.log_pos ht
  have hloglogPos : 0 < Real.log (Real.log t) := zero_lt_one.trans_le hloglog1
  have hloglogLe : Real.log (Real.log t) ≤ Real.log t := by
    exact (Real.log_le_sub_one_of_pos hlogPos).trans (by linarith)
  have hdenPos : 0 < tripleLogDen t := by
    unfold tripleLogDen
    positivity
  have hdenLe : tripleLogDen t ≤ Real.log t ^ 2 := by
    unfold tripleLogDen
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left hloglogLe hlogPos.le
  have hroot0 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
  have hrootSq : t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) = t := by
    rw [← Real.rpow_add ht0]
    norm_num
  have hbound : t ^ (1 / 2 : ℝ) ≤ t / tripleLogDen t := by
    apply (le_div_iff₀ hdenPos).mpr
    calc
      t ^ (1 / 2 : ℝ) * tripleLogDen t ≤
          t ^ (1 / 2 : ℝ) * Real.log t ^ 2 :=
        mul_le_mul_of_nonneg_left hdenLe hroot0
      _ ≤ t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hsq hroot0
      _ = t := hrootSq
  simpa only [profile] using hbound

/-- Eventual weighted derivative regularity with the paper's constant one. -/
theorem weightedDerivative :
    CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      profile profileDerivative 1 := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 4,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with t hlog4 hloglog1 ht
  simp only [Function.comp_apply] at hloglog1
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hlogPos : 0 < Real.log t := Real.log_pos ht
  have hloglogPos : 0 < Real.log (Real.log t) := zero_lt_one.trans_le hloglog1
  have hdenPos : 0 < tripleLogDen t := by
    unfold tripleLogDen
    positivity
  have hnum : 0 ≤ tripleLogDen t - Real.log (Real.log t) - 1 := by
    have htwo : Real.log (Real.log t) + 1 ≤
        2 * Real.log (Real.log t) := by linarith
    have hprod : 2 * Real.log (Real.log t) ≤ tripleLogDen t := by
      unfold tripleLogDen
      exact mul_le_mul_of_nonneg_right (by linarith) hloglogPos.le
    linarith
  refine ⟨div_pos ht0 hdenPos, profile_hasDerivAt ht (by linarith), ?_, ?_⟩
  · unfold profileDerivative
    exact mul_nonneg ht0.le (div_nonneg hnum (sq_nonneg _))
  · have hfrac :
        (tripleLogDen t - Real.log (Real.log t) - 1) /
            tripleLogDen t ^ 2 ≤ 1 / tripleLogDen t := by
      apply (div_le_iff₀ (sq_pos_of_pos hdenPos)).mpr
      have hden0 := hdenPos.ne'
      field_simp [hden0] <;> nlinarith
    unfold profileDerivative profile
    rw [one_mul]
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hfrac ht0.le

/-- The explicit profile satisfies the paper's universal little-o condition. -/
theorem hasLittleOSlopeProfile :
    CoreRoughLittleOProfile.HasLittleOSlopeProfile profile := by
  refine ⟨tendsto_profile_atTop, ?_⟩
  refine IsLittleO.of_bound ?_
  intro c hc
  have hloglog : Tendsto (fun t : ℝ => Real.log (Real.log t)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hratio : Tendsto
      (fun t : ℝ => 2 / Real.log (Real.log t)) atTop (nhds 0) := by
    have hh := (tendsto_inv_atTop_zero.comp hloglog).const_mul 2
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using hh
  filter_upwards [hratio.eventually_le_const hc,
    eventually_log_sq_le_sqrt,
    Real.tendsto_log_atTop.eventually_ge_atTop 4,
    hloglog.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with t hratioC hsq hlog4 hloglog1 ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hlogPos : 0 < Real.log t := Real.log_pos ht
  have hloglogPos : 0 < Real.log (Real.log t) := zero_lt_one.trans_le hloglog1
  have hloglogLe : Real.log (Real.log t) ≤ Real.log t :=
    (Real.log_le_sub_one_of_pos hlogPos).trans (by linarith)
  have hdenPos : 0 < tripleLogDen t := by
    unfold tripleLogDen
    positivity
  have hdenLe : tripleLogDen t ≤ Real.log t ^ 2 := by
    unfold tripleLogDen
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left hloglogLe hlogPos.le
  have hroot0 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
  have hrootSq : t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) = t := by
    rw [← Real.rpow_add ht0]
    norm_num
  have hrootOne : 1 ≤ t ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith : 1 ≤ t) (by norm_num)
  have hrootLeT : t ^ (1 / 2 : ℝ) ≤ t := by
    nlinarith
  have hdenLeT : tripleLogDen t ≤ t := hdenLe.trans (hsq.trans hrootLeT)
  have hprofileOne : 1 ≤ profile t := by
    unfold profile
    apply (le_div_iff₀ hdenPos).mpr
    simpa only [one_mul] using hdenLeT
  have hdenOne : 1 ≤ tripleLogDen t := by
    calc
      1 ≤ 4 * 1 := by norm_num
      _ ≤ Real.log t * Real.log (Real.log t) :=
        mul_le_mul hlog4 hloglog1 (by norm_num) (by linarith)
      _ = tripleLogDen t := by rfl
  have hprofileLe : profile t ≤ t := by
    unfold profile
    exact div_le_self ht0.le hdenOne
  have hprofilePos : 0 < profile t := zero_lt_one.trans_le hprofileOne
  have hlogArg : Real.log (3 * profile t) ≤ Real.log (3 * t) := by
    exact Real.log_le_log (by positivity)
      (mul_le_mul_of_nonneg_left hprofileLe (by norm_num))
  have hlogThree : Real.log (3 : ℝ) ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans_eq (by norm_num)
  have hlogUpper : Real.log (3 * profile t) ≤ 2 * Real.log t := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) ht0.ne'] at hlogArg
    linarith
  have hlogNonneg : 0 ≤ Real.log (3 * profile t) :=
    Real.log_nonneg (by nlinarith)
  have hmain : profile t * Real.log (3 * profile t) ≤
      (2 / Real.log (Real.log t)) * t := by
    calc
      profile t * Real.log (3 * profile t) ≤ profile t * (2 * Real.log t) :=
        mul_le_mul_of_nonneg_left hlogUpper hprofilePos.le
      _ = (2 / Real.log (Real.log t)) * t := by
        unfold profile tripleLogDen
        field_simp [hlogPos.ne', hloglogPos.ne']
  have hfinal : profile t * Real.log (3 * profile t) ≤ c * t :=
    hmain.trans (mul_le_mul_of_nonneg_right hratioC ht0.le)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hprofilePos.le hlogNonneg), abs_of_nonneg ht0.le] using hfinal

/-- The literal natural cutoff is the advertised
`floor(n^(1/(log log n * log log log n)))` whenever `n` is positive. -/
theorem zPsi_eq_tripleLog_cutoff {n : ℕ} (hn : 0 < n) :
    zPsi profile n =
      ⌊(n : ℝ) ^
        (1 / (Real.log (Real.log (n : ℝ)) *
          Real.log (Real.log (Real.log (n : ℝ)))))⌋₊ := by
  unfold zPsi profile tripleLogDen
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
  congr 2
  ring

/-- Fully discharged all-fixed local classification for the explicit
triple-log moving-rough sequence. -/
theorem movingRough_local_classification
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) :
    (normalForm hB hk F = 0 ∧
      ∃ q : ℚ,
        coreCyclicFullSeries B hk phase
            (fun n =>
              (seqGap (movingRoughSequence (zPsi profile)) n : ℝ)) F =
          (q : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k)
        (coreCyclicFullSeries B hk phase
          (fun n =>
            (seqGap (movingRoughSequence (zPsi profile)) n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase
          (fun n =>
            (seqGap (movingRoughSequence (zPsi profile)) n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase
          (fun n =>
            (seqGap (movingRoughSequence (zPsi profile)) n : ℝ)) F)) := by
  exact CoreRoughLittleOProfile.movingRough_local_classification
    hasLittleOSlopeProfile (by norm_num : (0 : ℝ) ≤ 1)
    weightedDerivative hB hk phase F

end

end PrimeGapNormality.Prime.CoreRoughTripleLogProfile
