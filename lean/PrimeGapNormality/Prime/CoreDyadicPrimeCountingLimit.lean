import PrimeGapNormality.Prime.CoreDyadicPrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt

/-! An elementary dyadic prime-count lower bound from the retained
central-binomial prime factors. No PNT or prime-distribution hypothesis.
-/

namespace PrimeGapNormality.Prime.CoreDyadicPrimeCounting

open Nat Filter
open scoped Topology

theorem logarithmic_count_bound {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 / 3 ≤ Real.log (n : ℝ) +
      (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) +
        ((dyadicPrimes n).card : ℝ) * Real.log (2 * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hn2 : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have hcomb : (4 : ℝ) ^ n ≤ (n : ℝ) *
      ((2 * (n : ℝ)) ^ (Nat.sqrt (2 * n) + (dyadicPrimes n).card) *
        (4 : ℝ) ^ (2 * n / 3)) := by
    exact_mod_cast (Nat.four_pow_lt_mul_centralBinom n hn).le.trans
      (Nat.mul_le_mul_left n (centralBinom_le_dyadic_count hn))
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 4) n) hcomb
  rw [Real.log_pow, Real.log_mul hn0.ne'
      (mul_ne_zero (pow_ne_zero _ hn2.ne') (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0))),
    Real.log_mul (pow_ne_zero _ hn2.ne') (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)),
    Real.log_pow, Real.log_pow] at hlog
  simp only [Nat.cast_add] at hlog
  have hfloor : ((2 * n / 3 : ℕ) : ℝ) * 3 ≤ 2 * (n : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (2 * n) 3
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hfloorlog := mul_le_mul_of_nonneg_right hfloor hlog4
  nlinarith

/-- The non-large-prime logarithmic contribution is sublinear. -/
theorem tendsto_small_log_error :
    Tendsto (fun x : ℝ ↦
      (Real.log x + Real.sqrt (2 * x) * Real.log (2 * x)) / x)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hscaled : Tendsto (fun x : ℝ ↦ 2 * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
  have hsqrt : Tendsto (fun x : ℝ ↦ Real.log (2 * x) / Real.sqrt (2 * x))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        hscaled
  have hsum := hlog.add (hsqrt.const_mul 2)
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx2 : 0 < 2 * x := by positivity
  have hspos : 0 < Real.sqrt (2 * x) := Real.sqrt_pos.2 hx2
  have hquot : Real.sqrt (2 * x) / x = 2 / Real.sqrt (2 * x) := by
    apply (div_eq_div_iff hx.ne' hspos.ne').2
    nlinarith [Real.sq_sqrt hx2.le]
  symm
  calc
    (Real.log x + Real.sqrt (2 * x) * Real.log (2 * x)) / x =
        Real.log x / x + (Real.sqrt (2 * x) / x) * Real.log (2 * x) := by ring
    _ = Real.log x / x + (2 / Real.sqrt (2 * x)) * Real.log (2 * x) := by rw [hquot]
    _ = Real.log x / x + 2 * (Real.log (2 * x) / Real.sqrt (2 * x)) := by ring

/-- A fully unconditional positive constant in the dyadic count bound. -/
noncomputable def dyadicCountConstant : ℝ := Real.log 4 / 12

theorem dyadicCountConstant_pos : 0 < dyadicCountConstant :=
  div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 4)) (by norm_num)

/-- Quantitative Bertrand, at the strength needed by the weaker-D route:
eventually at least `c n/log n` actual primes lie in `(n,2n]`. -/
theorem eventually_dyadic_prime_count_ge :
    ∀ᶠ n : ℕ in atTop,
      dyadicCountConstant * (n : ℝ) / Real.log (n : ℝ) ≤
        ((dyadicPrimes n).card : ℝ) := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have herr := (tendsto_small_log_error.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_const
      (div_pos hlog4 (by norm_num : (0 : ℝ) < 6))
  filter_upwards [eventually_ge_atTop 4, herr] with n hn he
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hn1 : (1 : ℝ) < n := Nat.one_lt_cast.2 (by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hlog2n : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have herr' : Real.log (n : ℝ) + Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) ≤
      (n : ℝ) * Real.log 4 / 6 := by
    have h := (div_le_iff₀ hn0).1 he
    simpa only [Function.comp_apply, div_mul_eq_mul_div, mul_comm (Real.log 4)] using h
  have hsqrt : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Real.nat_sqrt_le_real_sqrt (a := 2 * n))
  have hsqrtlog := mul_le_mul_of_nonneg_right hsqrt hlog2n
  have hfinite := logarithmic_count_bound hn
  have hlarge : (n : ℝ) * Real.log 4 / 6 ≤
      ((dyadicPrimes n).card : ℝ) * Real.log (2 * (n : ℝ)) := by linarith
  have hdoublelog : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
    have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
    linarith
  have hlarge' := hlarge.trans (mul_le_mul_of_nonneg_left hdoublelog (Nat.cast_nonneg _))
  apply (div_le_iff₀ hlogn).2
  unfold dyadicCountConstant
  nlinarith

theorem eventually_primeCounting_sub_ge :
    ∀ᶠ n : ℕ in atTop,
      dyadicCountConstant * (n : ℝ) / Real.log (n : ℝ) ≤
        ((Nat.primeCounting (2 * n) - Nat.primeCounting n : ℕ) : ℝ) := by
  simpa only [dyadicPrimes_card] using eventually_dyadic_prime_count_ge

end PrimeGapNormality.Prime.CoreDyadicPrimeCounting
