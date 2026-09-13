import PrimeGapNormality.Prime.MertensStepErrorDCT
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Abelian bridge for Mertens II

This file combines Abel summation with the normalized Laplace-kernel
calculation and the dominated-convergence estimate for the floor step
function.  The only asymptotic hypothesis in the main theorem is the
discrete Mertens-II limit itself.
-/

namespace PrimeGapNormality.Prime

open Asymptotics Filter Finset MeasureTheory Set

noncomputable section

private def primeReciprocalTerm (n : ℕ) : ℝ :=
  if n.Prime then (n : ℝ)⁻¹ else 0

private theorem primeReciprocalTerm_nonneg (n : ℕ) :
    0 ≤ primeReciprocalTerm n := by
  by_cases hn : n.Prime
  · simp [primeReciprocalTerm, hn, inv_nonneg]
  · simp [primeReciprocalTerm, hn]

private theorem sum_Icc_primeReciprocalTerm (N : ℕ) :
    ∑ n ∈ Icc 1 N, primeReciprocalTerm n =
      mertensPrimeReciprocalSum N := by
  rw [mertensPrimeReciprocalSum, Nat.primesLE_eq_filter_Icc_one, sum_filter]
  exact sum_congr rfl fun n hn => by simp [primeReciprocalTerm, hn]

private theorem mertensPrimeReciprocalSum_nonneg (N : ℕ) :
    0 ≤ mertensPrimeReciprocalSum N := by
  rw [← sum_Icc_primeReciprocalTerm]
  exact sum_nonneg fun n _ => primeReciprocalTerm_nonneg n

private theorem mertensPrimeReciprocalSum_le_harmonic (N : ℕ) :
    mertensPrimeReciprocalSum N ≤ (harmonic N : ℝ) := by
  rw [← sum_Icc_primeReciprocalTerm, harmonic_eq_sum_Icc]
  simp_rw [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact sum_le_sum fun n _ => by
    by_cases hn : n.Prime
    · simp [primeReciprocalTerm, hn]
    · simp [primeReciprocalTerm, hn, inv_nonneg]

/-- The elementary growth estimate needed to invoke Mathlib's integral
form of Abel summation. -/
private theorem mertensPrimeReciprocalSum_isBigO_rpow {r : ℝ} (hr : 0 < r) :
    (fun N : ℕ => mertensPrimeReciprocalSum N) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r) := by
  have hlog : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ (1 : ℝ) * ‖x ^ r‖ :=
    (isLittleO_log_rpow_atTop hr).bound (by norm_num)
  have hlogNat : ∀ᶠ N : ℕ in atTop,
      ‖Real.log (N : ℝ)‖ ≤ (1 : ℝ) * ‖(N : ℝ) ^ r‖ :=
    tendsto_natCast_atTop_atTop.eventually hlog
  refine isBigO_iff.mpr ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlogNat] with N hN hlog
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow0 : 0 ≤ (N : ℝ) ^ r := Real.rpow_nonneg (Nat.cast_nonneg N) r
  have hpow1 : 1 ≤ (N : ℝ) ^ r := Real.one_le_rpow hNreal hr.le
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
  have hA0 := mertensPrimeReciprocalSum_nonneg N
  have hAle : mertensPrimeReciprocalSum N ≤ 1 + Real.log (N : ℝ) :=
    (mertensPrimeReciprocalSum_le_harmonic N).trans (harmonic_le_one_add_log N)
  have hlogle : Real.log (N : ℝ) ≤ (N : ℝ) ^ r := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg hpow0, one_mul] using hlog
  change |mertensPrimeReciprocalSum N| ≤ 2 * |(N : ℝ) ^ r|
  rw [abs_of_nonneg hA0, abs_of_nonneg hpow0]
  exact hAle.trans (by nlinarith)

private theorem mertensPrimeDirichlet_eq_x_integral {t : ℝ} (ht : 0 < t) :
    mertensPrimeDirichlet (1 + t) =
      t * ∫ x : ℝ in Ioi 1,
        mertensPrimeReciprocalSum ⌊x⌋₊ * x ^ (-t - 1) := by
  let c : ℕ → ℝ := primeReciprocalTerm
  have hO :
      (fun N : ℕ => ∑ n ∈ Icc 1 N, c n) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ (t / 2)) := by
    simpa only [c, sum_Icc_primeReciprocalTerm] using
      (mertensPrimeReciprocalSum_isBigO_rpow (r := t / 2) (by linarith))
  have hL := LSeries_eq_mul_integral_of_nonneg c
    (r := t / 2) (s := (t : ℂ)) (by linarith) (by simp; linarith)
    hO (fun n => primeReciprocalTerm_nonneg n)
  apply Complex.ofReal_injective
  calc
    (mertensPrimeDirichlet (1 + t) : ℂ) =
        ∑' n : ℕ,
          ((if n.Prime then (n : ℝ) ^ (-(1 + t)) else 0 : ℝ) : ℂ) := by
      rw [mertensPrimeDirichlet, Complex.ofReal_tsum]
    _ = ∑' n : ℕ, (c n : ℂ) / (n : ℂ) ^ (t : ℂ) := by
      refine tsum_congr fun n => ?_
      by_cases hn : n.Prime
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
        simp only [c, primeReciprocalTerm, hn, if_true]
        have hreal : (n : ℝ) ^ (-(1 + t)) =
            (n : ℝ)⁻¹ / (n : ℝ) ^ t := by
          rw [show -(1 + t) = (-1 : ℝ) + (-t) by ring,
            Real.rpow_add hn0, Real.rpow_neg_one,
            Real.rpow_neg hn0.le, div_eq_mul_inv]
        calc
          (((n : ℝ) ^ (-(1 + t)) : ℝ) : ℂ) =
              (((n : ℝ)⁻¹ / (n : ℝ) ^ t : ℝ) : ℂ) :=
            congrArg (fun x : ℝ => (x : ℂ)) hreal
          _ = (((n : ℝ)⁻¹ : ℝ) : ℂ) /
              (((n : ℝ) : ℂ)) ^ (t : ℂ) :=
            (Complex.ofReal_div ((n : ℝ)⁻¹) ((n : ℝ) ^ t)).trans
              (congrArg₂ (fun a b : ℂ => a / b)
                rfl
                (Complex.ofReal_cpow hn0.le t))
          _ = (((n : ℝ)⁻¹ : ℝ) : ℂ) / (n : ℂ) ^ (t : ℂ) := by
            have hncast : ((n : ℝ) : ℂ) = (n : ℂ) := by norm_num
            exact congrArg
              (fun z : ℂ => (((n : ℝ)⁻¹ : ℝ) : ℂ) / z ^ (t : ℂ)) hncast
      · simp [c, primeReciprocalTerm, hn]
    _ = LSeries (fun n : ℕ => (c n : ℂ)) (t : ℂ) := by
      rw [LSeries_def₀ (by simp [c, primeReciprocalTerm])]
    _ = (t : ℂ) * ∫ x : ℝ in Ioi 1,
          (∑ n ∈ Icc 1 ⌊x⌋₊, (c n : ℂ)) *
            (x : ℂ) ^ (-((t : ℂ) + 1)) := hL
    _ = ((t * ∫ x : ℝ in Ioi 1,
          mertensPrimeReciprocalSum ⌊x⌋₊ * x ^ (-t - 1) : ℝ) : ℂ) := by
      let f : ℝ → ℝ := fun x =>
        mertensPrimeReciprocalSum ⌊x⌋₊ * (x : ℝ) ^ ((-t - 1 : ℝ))
      have hcast :
          ((∫ x : ℝ in Ioi 1, f x : ℝ) : ℂ) =
            ∫ x : ℝ in Ioi 1,
              ((f x : ℝ) : ℂ) := by
        have hraw := integral_ofReal (𝕜 := ℂ)
          (μ := volume.restrict (Ioi (1 : ℝ))) (f := f)
        exact hraw.symm
      change
        (t : ℂ) * ∫ x : ℝ in Ioi 1,
            (∑ n ∈ Icc 1 ⌊x⌋₊, (c n : ℂ)) *
              (x : ℂ) ^ (-((t : ℂ) + 1)) =
          ((t * ∫ x : ℝ in Ioi 1, f x : ℝ) : ℂ)
      rw [Complex.ofReal_mul, hcast]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
      have he : -((t : ℂ) + 1) = ((-t - 1 : ℝ) : ℂ) := by
        push_cast
        ring
      dsimp only [f]
      rw [he, Complex.ofReal_mul, Complex.ofReal_cpow hx0]
      congr 1
      rw [← sum_Icc_primeReciprocalTerm]
      simp only [c, Complex.ofReal_sum]

private theorem mertensPrimeDirichlet_eq_laplace {t : ℝ} (ht : 0 < t) :
    mertensPrimeDirichlet (1 + t) =
      ∫ u : ℝ in Ioi 0, Real.exp (-u) *
        mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊ := by
  rw [mertensPrimeDirichlet_eq_x_integral ht]
  have hexp :
      (∫ y : ℝ in Ioi 0, Real.exp y *
        (mertensPrimeReciprocalSum ⌊Real.exp y⌋₊ *
          Real.exp y ^ (-t - 1))) =
        ∫ x : ℝ in Ioi 1,
          mertensPrimeReciprocalSum ⌊x⌋₊ * x ^ (-t - 1) := by
    simpa only [Real.exp_zero, smul_eq_mul, Function.comp_apply] using
      (integral_comp_exp_Ioi
        (fun x : ℝ => mertensPrimeReciprocalSum ⌊x⌋₊ * x ^ (-t - 1)) 0)
  have hx_to_y :
      (∫ x : ℝ in Ioi 1,
          mertensPrimeReciprocalSum ⌊x⌋₊ * x ^ (-t - 1)) =
        ∫ y : ℝ in Ioi 0, Real.exp (-(t * y)) *
          mertensPrimeReciprocalSum ⌊Real.exp y⌋₊ := by
    rw [← hexp]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp]
    calc
      Real.exp y *
          (mertensPrimeReciprocalSum ⌊Real.exp y⌋₊ *
            Real.exp (y * (-t - 1))) =
          (Real.exp y * Real.exp (y * (-t - 1))) *
            mertensPrimeReciprocalSum ⌊Real.exp y⌋₊ := by ring
      _ = Real.exp (y + y * (-t - 1)) *
            mertensPrimeReciprocalSum ⌊Real.exp y⌋₊ := by
          rw [Real.exp_add]
      _ = Real.exp (-(t * y)) *
            mertensPrimeReciprocalSum ⌊Real.exp y⌋₊ := by
          rw [show y + y * (-t - 1) = -(t * y) by ring]
  rw [hx_to_y]
  have hscale := integral_comp_mul_left_Ioi'
    (fun u : ℝ => Real.exp (-u) *
      mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊) 0 ht
  calc
    t * ∫ x : ℝ in Ioi 0, Real.exp (-(t * x)) *
          mertensPrimeReciprocalSum ⌊Real.exp x⌋₊ =
        t * ∫ x : ℝ in Ioi 0,
          (fun u : ℝ => Real.exp (-u) *
            mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊) (t * x) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have htx : t * x / t = x := mul_div_cancel_left₀ x ht.ne'
      change Real.exp (-(t * x)) *
          mertensPrimeReciprocalSum ⌊Real.exp x⌋₊ =
        Real.exp (-(t * x)) *
          mertensPrimeReciprocalSum ⌊Real.exp (t * x / t)⌋₊
      rw [htx]
    _ = ∫ u : ℝ in Ioi 0, Real.exp (-u) *
          mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊ := by
      simpa only [smul_eq_mul, mul_zero] using hscale

private theorem integrableOn_mertens_laplace {t : ℝ} (ht : 0 < t) :
    IntegrableOn
      (fun u : ℝ => Real.exp (-u) *
        mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊)
      (Ioi 0) := by
  have hindex : Measurable (fun u : ℝ => ⌊Real.exp (u / t)⌋₊) :=
    (Real.measurable_exp.comp (measurable_id.div_const t)).nat_floor
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-u) *
        mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊)
      (volume.restrict (Ioi 0)) :=
    ((Real.measurable_exp.comp measurable_neg).mul
      ((measurable_of_countable mertensPrimeReciprocalSum).comp hindex)).aestronglyMeasurable
  have huExp : IntegrableOn (fun u : ℝ => u * Real.exp (-u)) (Ioi 0) := by
    simpa only [Real.rpow_one, one_mul] using
      (integrableOn_rpow_mul_exp_neg_rpow
        (by norm_num : (-1 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1))
  have hmajor : IntegrableOn
      (fun u : ℝ => Real.exp (-u) * (1 + u / t)) (Ioi 0) := by
    have hscaled := huExp.const_mul (1 / t)
    refine (integrableOn_exp_neg_Ioi_zero.add hscaled).congr ?_
    filter_upwards with u
    simpa only [Pi.add_apply, div_eq_mul_inv] using
      (show Real.exp (-u) + (1 / t) * (u * Real.exp (-u)) =
          Real.exp (-u) * (1 + u * t⁻¹) by ring)
  refine Integrable.mono' hmajor hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hexp1 : (1 : ℝ) ≤ Real.exp (u / t) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (div_nonneg hu.le ht.le)
  have hfloor1 : 1 ≤ ⌊Real.exp (u / t)⌋₊ :=
    (Nat.one_le_floor_iff (Real.exp (u / t))).2 hexp1
  have hA0 := mertensPrimeReciprocalSum_nonneg ⌊Real.exp (u / t)⌋₊
  have hAle : mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊ ≤
      1 + u / t := by
    calc
      mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊ ≤
          (harmonic ⌊Real.exp (u / t)⌋₊ : ℝ) :=
        mertensPrimeReciprocalSum_le_harmonic _
      _ ≤ 1 + Real.log (Real.exp (u / t)) :=
        harmonic_floor_le_one_add_log _ hexp1
      _ = 1 + u / t := by rw [Real.log_exp]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hA0]
  exact mul_le_mul_of_nonneg_left hAle (Real.exp_pos _).le

private theorem mertens_laplace_add_log_eq_error
    {B t : ℝ} (ht : 0 < t) :
    mertensPrimeDirichlet (1 + t) + Real.log t =
      (∫ u : ℝ in Ioi 0, Real.exp (-u) *
        (mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊ -
          Real.log (u / t) - B)) +
        (B - Real.eulerMascheroniConstant) := by
  have hfull := integrableOn_mertens_laplace ht
  have hlogdiv : IntegrableOn
      (fun u : ℝ => Real.exp (-u) * Real.log (u / t)) (Ioi 0) := by
    refine (integrableOn_exp_neg_mul_log_Ioi_zero.sub
      (integrableOn_exp_neg_Ioi_zero.mul_const (Real.log t))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change Real.exp (-u) * Real.log u - Real.exp (-u) * Real.log t =
      Real.exp (-u) * Real.log (u / t)
    rw [Real.log_div hu.ne' ht.ne']
    ring
  have hbase : IntegrableOn
      (fun u : ℝ => Real.exp (-u) * (Real.log (u / t) + B)) (Ioi 0) := by
    refine (hlogdiv.add (integrableOn_exp_neg_Ioi_zero.mul_const B)).congr ?_
    filter_upwards with u
    simpa only [Pi.add_apply] using
      (show Real.exp (-u) * Real.log (u / t) + Real.exp (-u) * B =
          Real.exp (-u) * (Real.log (u / t) + B) by ring)
  have herr : IntegrableOn
      (fun u : ℝ => Real.exp (-u) *
        (mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊ -
          Real.log (u / t) - B)) (Ioi 0) := by
    refine (hfull.sub hbase).congr ?_
    filter_upwards with u
    change Real.exp (-u) *
        mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊ -
          Real.exp (-u) * (Real.log (u / t) + B) = _
    ring
  rw [mertensPrimeDirichlet_eq_laplace ht]
  have hsplit :
      (∫ u : ℝ in Ioi 0, Real.exp (-u) *
        mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊) =
        (∫ u : ℝ in Ioi 0, Real.exp (-u) *
          (mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊ -
            Real.log (u / t) - B)) +
        ∫ u : ℝ in Ioi 0,
          Real.exp (-u) * (Real.log (u / t) + B) := by
    rw [← MeasureTheory.integral_add herr hbase]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    ring
  rw [hsplit]
  have hbaseValue :
      (∫ u : ℝ in Ioi 0,
        Real.exp (-u) * (Real.log (u / t) + B)) =
        -Real.eulerMascheroniConstant - Real.log t + B := by
    calc
      (∫ u : ℝ in Ioi 0,
          Real.exp (-u) * (Real.log (u / t) + B)) =
          (∫ u : ℝ in Ioi 0, Real.exp (-u) * Real.log (u / t)) +
            ∫ u : ℝ in Ioi 0, Real.exp (-u) * B := by
        rw [← MeasureTheory.integral_add hlogdiv
          (integrableOn_exp_neg_Ioi_zero.mul_const B)]
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        ring
      _ = -Real.eulerMascheroniConstant - Real.log t + B := by
        rw [integral_exp_neg_mul_log_div_Ioi_zero ht, integral_mul_const,
          integral_exp_neg_Ioi_zero_eq_one]
        ring
  rw [hbaseValue]
  ring

/-- The unconditional Abelian passage from the discrete Mertens-II limit to
the right limit of the prime Dirichlet series. -/
theorem tendsto_mertensPrimeDirichlet_add_log_sub_one_of_discrete
    {B : ℝ}
    (hB : Tendsto (fun N : ℕ =>
      mertensPrimeReciprocalSum N - Real.log (Real.log N))
      atTop (nhds B)) :
    Tendsto (fun s : ℝ =>
      mertensPrimeDirichlet s + Real.log (s - 1))
      (nhdsWithin 1 (Ioi 1))
      (nhds (B - Real.eulerMascheroniConstant)) := by
  have ht : Tendsto (fun t : ℝ =>
      mertensPrimeDirichlet (1 + t) + Real.log t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (B - Real.eulerMascheroniConstant)) := by
    have h0 := (tendsto_integral_mertens_step_error hB).add_const
      (B - Real.eulerMascheroniConstant)
    have h : Tendsto (fun t : ℝ =>
        (∫ u in Ioi 0, Real.exp (-u) *
          (mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊ -
            Real.log (u / t) - B)) +
          (B - Real.eulerMascheroniConstant))
        (nhdsWithin 0 (Ioi 0))
        (nhds (B - Real.eulerMascheroniConstant)) := by
      simpa only [zero_add] using h0
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (mertens_laplace_add_log_eq_error ht).symm
  have hsub : Tendsto (fun s : ℝ => s - 1)
      (nhdsWithin (1 : ℝ) (Ioi (1 : ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · change Tendsto (fun s : ℝ => s - 1)
        (nhds (1 : ℝ) ⊓ 𝓟 (Ioi (1 : ℝ))) (nhds (0 : ℝ))
      simpa only [id_eq, sub_self] using
        ((tendsto_id : Tendsto (fun s : ℝ => s) (nhds (1 : ℝ)) (nhds (1 : ℝ))).sub_const
          (1 : ℝ)).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr (show (1 : ℝ) < s from hs)
  have hcomp := ht.comp hsub
  change Tendsto
    (fun s : ℝ =>
      mertensPrimeDirichlet (1 + (s - 1)) + Real.log (s - 1))
    (nhdsWithin (1 : ℝ) (Ioi (1 : ℝ)))
    (nhds (B - Real.eulerMascheroniConstant)) at hcomp
  refine hcomp.congr' (Eventually.of_forall fun s => ?_)
  rw [show 1 + (s - 1) = s by ring]

/-- The now-unconditional identified form of Mertens II. -/
theorem tendsto_mertensPrimeReciprocalSum_sub_log_log :
    Tendsto (fun N : ℕ =>
      mertensPrimeReciprocalSum N - Real.log (Real.log N))
      atTop
      (nhds (Real.eulerMascheroniConstant -
        mertensPrimeCorrectionConstant)) := by
  exact mertensPrimeReciprocalSum_tendsto_of_abelian_bridge
    (fun hB => tendsto_mertensPrimeDirichlet_add_log_sub_one_of_discrete hB)

/-- The classical Mertens product limit in the normalization used by the
project. -/
theorem tendsto_eulerProdNat_mul_log :
    Tendsto (fun N : ℕ => eulerProdNat N * Real.log N) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have harg := tendsto_mertensPrimeReciprocalSum_sub_log_log.neg.sub
    tendsto_mertensPrimeCorrectionSum
  have hexp := harg.rexp
  have hexp' : Tendsto
      (fun N : ℕ => Real.exp
        (-(mertensPrimeReciprocalSum N - Real.log (Real.log N)) -
          mertensPrimeCorrectionSum N))
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    convert hexp using 1 <;> ring
  refine hexp'.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (eulerProdNat_mul_log_eq_mertens_exp hN).symm

/-- The eventual Euler-product lower tail required by the model-cost
argument. -/
theorem eventually_half_lt_eulerProdNat_mul_log :
    ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) < eulerProdNat N * Real.log N := by
  have hgamma : Real.eulerMascheroniConstant < Real.log 2 := by
    exact Real.eulerMascheroniConstant_lt_two_thirds.trans
      (lt_trans (by norm_num : (2 / 3 : ℝ) < 0.6931471803)
        Real.log_two_gt_d9)
  have hlimit : (1 / 2 : ℝ) <
      Real.exp (-Real.eulerMascheroniConstant) := by
    have hexp : Real.exp (-Real.log 2) <
        Real.exp (-Real.eulerMascheroniConstant) :=
      Real.exp_lt_exp.mpr (neg_lt_neg hgamma)
    have hhalf : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rwa [hhalf]
  exact tendsto_eulerProdNat_mul_log.eventually (Ioi_mem_nhds hlimit)

end

end PrimeGapNormality.Prime
