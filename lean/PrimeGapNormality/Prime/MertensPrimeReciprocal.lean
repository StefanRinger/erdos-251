import PrimeGapNormality.Prime.MertensProduct
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The weighted-prime input for Mertens II

This file starts the unconditional elementary proof of

`sum_{p <= N} log p / p = log N + O(1)`.

The finite factorial/von-Mangoldt identity is public here (the earlier copy
in `EulerProd` was private).  Stirling and Chebyshev's elementary bound give
the corresponding two-sided estimate for `sum Λ(n)/n`.  We then split off
the prime terms exactly and record Mathlib's square-root estimate for the
cumulative prime-power remainder.

The remaining step is purely discrete Abel summation: the square-root bound
must be summed against `1/n - 1/(n+1)`, using convergence of
`sum n^(-3/2)`.  No Mertens statement, PNT, or analytic assumption is
introduced in this file.
-/

namespace PrimeGapNormality.Prime

open Filter Finset
open scoped ArithmeticFunction Interval

noncomputable section

/-- The weighted prime sum occurring in the elementary proof of Mertens II. -/
def mertensPrimeLogOverSum (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesLE, Real.log p / p

/-- The companion von-Mangoldt weighted sum. -/
def mertensMangoldtWeightedSum (N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, Λ d / d

/-- The contribution of proper prime powers to the von-Mangoldt weighted
sum.  Its nonnegativity and its exact finite expansion are proved below. -/
def mertensPrimePowerWeightedRemainder (N : ℕ) : ℝ :=
  mertensMangoldtWeightedSum N - mertensPrimeLogOverSum N

/-- The cumulative (unweighted) proper-prime-power contribution. -/
def mertensPrimePowerCounting (N : ℕ) : ℝ :=
  Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)

private theorem prod_Icc_one_eq_factorial (N : ℕ) :
    ∏ n ∈ Icc 1 N, n = N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
      simp [Nat.mul_comm]

/-- The logarithm of `N!` as a finite sum. -/
theorem mertens_log_factorial_eq_sum_log (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ n ∈ Icc 1 N, Real.log n := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← prod_Icc_one_eq_factorial, Nat.cast_prod, Real.log_prod]
  intro n hn
  exact Nat.cast_ne_zero.mpr
    (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1))

private theorem Icc_one_eq_Ioc_zero (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext n
  simp [Nat.succ_le_iff]

private theorem card_Icc_one_filter_dvd (N d : ℕ) :
    #{n ∈ Icc 1 N | d ∣ n} = N / d := by
  rw [Icc_one_eq_Ioc_zero, Nat.Ioc_filter_dvd_card_eq_div]

private theorem divisors_eq_filter_Icc {n N : ℕ} (hn : n ∈ Icc 1 N) :
    n.divisors = (Icc 1 N).filter (fun d => d ∣ n) := by
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · intro h
    have hnpos : 0 < n := Nat.pos_of_ne_zero h.2
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos h.1 hnpos
    exact ⟨⟨Nat.succ_le_of_lt hdpos,
      (Nat.le_of_dvd hnpos h.1).trans (mem_Icc.mp hn).2⟩, h.1⟩
  · intro h
    exact ⟨h.2,
      ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1)⟩

/-- Exact finite von-Mangoldt/factorial identity:
`log(N!) = sum_{d <= N} Λ(d) floor(N/d)`. -/
theorem mertens_log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ d ∈ Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) := by
  rw [mertens_log_factorial_eq_sum_log]
  have hlog :
      ∑ n ∈ Icc 1 N, Real.log n =
        ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, Λ d :=
    sum_congr rfl fun n _ => ArithmeticFunction.vonMangoldt_sum.symm
  rw [hlog]
  have hdiv : ∀ n ∈ Icc 1 N,
      ∑ d ∈ n.divisors, Λ d =
        ∑ d ∈ Icc 1 N, (if d ∣ n then Λ d else 0) := by
    intro n hn
    rw [divisors_eq_filter_Icc hn, sum_filter]
  rw [sum_congr rfl hdiv, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  calc
    ∑ n ∈ Icc 1 N, (if d ∣ n then Λ d else 0) =
        Λ d * (#{n ∈ Icc 1 N | d ∣ n} : ℝ) := by
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    _ = Λ d * ((N / d : ℕ) : ℝ) := by
      rw [card_Icc_one_filter_dvd]

private theorem cast_div_ge_sub_one {N d : ℕ} (hd : 0 < d) :
    (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := by
  have hmod := Nat.div_add_mod N d
  have hcast :
      (N : ℝ) = (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, hmod]
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hsplit :
      (N : ℝ) / d = ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) / d := by
    rw [hcast, add_div, mul_div_cancel_left₀ _ hdpos.ne']
  have hlt : ((N % d : ℕ) : ℝ) / d < 1 := by
    rw [div_lt_one hdpos]
    exact_mod_cast Nat.mod_lt N hd
  linarith

/-- The Mangoldt weighted sum is bounded above by `log N` plus an absolute
constant.  This is the elementary factorial/Chebyshev half of Mertens I. -/
theorem mertensMangoldtWeightedSum_le_log_add {N : ℕ} (hN : 0 < N) :
    mertensMangoldtWeightedSum N ≤ Real.log N + Real.log 4 + 4 := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hfac := mertens_log_factorial_eq_sum_vonMangoldt_mul_div N
  have hpsi : Chebyshev.psi (N : ℝ) ≤ (Real.log 4 + 4) * N :=
    Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
  have hfloor :
      (N : ℝ) * mertensMangoldtWeightedSum N - Chebyshev.psi (N : ℝ) ≤
        Real.log (N.factorial : ℝ) := by
    have hpt : ∀ d ∈ Icc 1 N,
        (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := fun d hd =>
      cast_div_ge_sub_one
        (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd).1)
    have hsum :
        ∑ d ∈ Icc 1 N, Λ d * ((N : ℝ) / d - 1) ≤
          ∑ d ∈ Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) :=
      sum_le_sum fun d hd =>
        mul_le_mul_of_nonneg_left (hpt d hd)
          ArithmeticFunction.vonMangoldt_nonneg
    have hleft :
        ∑ d ∈ Icc 1 N, Λ d * ((N : ℝ) / d - 1) =
          (N : ℝ) * mertensMangoldtWeightedSum N - Chebyshev.psi (N : ℝ) := by
      have hterm : ∀ d ∈ Icc 1 N,
          Λ d * ((N : ℝ) / d - 1) = (N : ℝ) * (Λ d / d) - Λ d :=
        fun d _ => by ring
      rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum,
        mertensMangoldtWeightedSum, Chebyshev.psi_eq_sum_Icc,
        Nat.floor_natCast]
      have hI : Icc (0 : ℕ) N = insert 0 (Icc 1 N) := by
        ext n
        simp [mem_Icc, mem_insert]
        omega
      rw [hI, sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
    rw [← hleft]
    exact hsum.trans_eq hfac.symm
  have hfacUpper : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
    rw [mertens_log_factorial_eq_sum_log]
    calc
      ∑ n ∈ Icc 1 N, Real.log n ≤ ∑ n ∈ Icc 1 N, Real.log N := by
        refine sum_le_sum fun n hn => ?_
        exact Real.log_le_log
          (Nat.cast_pos.mpr
            (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1))
          (Nat.cast_le.mpr (mem_Icc.mp hn).2)
      _ = N * Real.log N := by simp [Nat.card_Icc]
  have hmain :
      mertensMangoldtWeightedSum N ≤
        (Real.log (N.factorial : ℝ) + Chebyshev.psi (N : ℝ)) / N := by
    rw [le_div_iff₀ hNR]
    linarith
  have hfacDiv : Real.log (N.factorial : ℝ) / N ≤ Real.log N := by
    rw [div_le_iff₀ hNR]
    simpa [mul_comm] using hfacUpper
  have hpsiDiv : Chebyshev.psi (N : ℝ) / N ≤ Real.log 4 + 4 := by
    rw [div_le_iff₀ hNR]
    simpa [mul_comm] using hpsi
  calc
    mertensMangoldtWeightedSum N ≤
        (Real.log (N.factorial : ℝ) + Chebyshev.psi (N : ℝ)) / N := hmain
    _ = Real.log (N.factorial : ℝ) / N + Chebyshev.psi (N : ℝ) / N :=
      add_div _ _ _
    _ ≤ Real.log N + (Real.log 4 + 4) := add_le_add hfacDiv hpsiDiv
    _ = Real.log N + Real.log 4 + 4 := by ring

/-- Stirling and the exact factorial identity give the matching elementary
lower bound. -/
theorem log_sub_one_le_mertensMangoldtWeightedSum {N : ℕ} (hN : 0 < N) :
    Real.log N - 1 ≤ mertensMangoldtWeightedSum N := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hstirling := Stirling.le_log_factorial_stirling (n := N) hN.ne'
  have hN_one : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN.ne'
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.mpr hN_one)
  have hone_two_pi : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hlog_two_pi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg hone_two_pi
  have hextra :
      0 ≤ Real.log (N : ℝ) / 2 + Real.log (2 * Real.pi) / 2 := by
    exact add_nonneg (div_nonneg hlogN (by norm_num))
      (div_nonneg hlog_two_pi (by norm_num))
  have hlower :
      (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
    linarith
  have hupper :
      Real.log (N.factorial : ℝ) ≤ (N : ℝ) * mertensMangoldtWeightedSum N := by
    rw [mertens_log_factorial_eq_sum_vonMangoldt_mul_div,
      mertensMangoldtWeightedSum, mul_sum]
    refine sum_le_sum fun d hd => ?_
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr
      (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd).1)
    have hdiv := Nat.cast_div_le (α := ℝ) (m := N) (n := d)
    calc
      Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * ((N : ℝ) / d) :=
        mul_le_mul_of_nonneg_left hdiv ArithmeticFunction.vonMangoldt_nonneg
      _ = (N : ℝ) * (Λ d / d) := by ring
  have hmul :
      (N : ℝ) * Real.log N - N ≤
        (N : ℝ) * mertensMangoldtWeightedSum N := hlower.trans hupper
  nlinarith

/-- Prime terms form a sub-sum of the von-Mangoldt weighted sum. -/
theorem mertensPrimeLogOverSum_le_mangoldt (N : ℕ) :
    mertensPrimeLogOverSum N ≤ mertensMangoldtWeightedSum N := by
  rw [mertensPrimeLogOverSum, mertensMangoldtWeightedSum,
    Nat.primesLE_eq_filter_Icc_one, sum_filter]
  refine sum_le_sum fun d hd => ?_
  split_ifs with hp
  · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

theorem mertensPrimePowerWeightedRemainder_nonneg (N : ℕ) :
    0 ≤ mertensPrimePowerWeightedRemainder N := by
  exact sub_nonneg.mpr (mertensPrimeLogOverSum_le_mangoldt N)

/-- Exact identification of the weighted remainder with proper prime powers
(equivalently, non-primes on the support of `Λ`). -/
theorem mertensPrimePowerWeightedRemainder_eq (N : ℕ) :
    mertensPrimePowerWeightedRemainder N =
      ∑ d ∈ Icc 1 N with ¬d.Prime, Λ d / d := by
  rw [mertensPrimePowerWeightedRemainder, mertensMangoldtWeightedSum,
    mertensPrimeLogOverSum, Nat.primesLE_eq_filter_Icc_one, sum_filter,
    ← sum_sub_distrib, sum_filter]
  refine sum_congr rfl fun d hd => ?_
  by_cases hp : d.Prime
  · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [hp]

/-- Exact unweighted proper-prime-power expansion of `psi - theta`. -/
theorem mertensPrimePowerCounting_eq (N : ℕ) :
    mertensPrimePowerCounting N = ∑ d ∈ Icc 1 N with ¬d.Prime, Λ d := by
  rw [mertensPrimePowerCounting,
    Chebyshev.psi_sub_theta_eq_sum_not_prime]
  simp only [Nat.floor_natCast]
  rw [Icc_one_eq_Ioc_zero]

/-- Proper prime powers have cumulative weight `O(sqrt N)`.  This is the
prime-power input needed by the final discrete Abel step. -/
theorem exists_mertensPrimePowerCounting_le_sqrt :
    ∃ C : ℝ, ∀ N : ℕ,
      0 ≤ mertensPrimePowerCounting N ∧
        mertensPrimePowerCounting N ≤ C * Real.sqrt N := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C, fun N => ⟨?_, ?_⟩⟩
  · exact sub_nonneg.mpr (Chebyshev.theta_le_psi (N : ℝ))
  · exact hC N

/-- The already completed upper half of the desired weighted-prime bound. -/
theorem mertensPrimeLogOverSum_le_log_add {N : ℕ} (hN : 0 < N) :
    mertensPrimeLogOverSum N ≤ Real.log N + Real.log 4 + 4 :=
  (mertensPrimeLogOverSum_le_mangoldt N).trans
    (mertensMangoldtWeightedSum_le_log_add hN)

/-! ### Discrete Abel summation of the proper-prime-power remainder -/

private noncomputable def properPrimePowerWeight (n : ℕ) : ℝ :=
  if ¬n.Prime then Λ n else 0

private theorem sum_range_succ_properPrimePowerWeight (N : ℕ) :
    ∑ n ∈ range (N + 1), properPrimePowerWeight n =
      mertensPrimePowerCounting N := by
  rw [mertensPrimePowerCounting_eq, sum_filter]
  have hI : range (N + 1) = insert 0 (Icc 1 N) := by
    rw [Nat.range_succ_eq_Icc_zero]
    ext n
    simp [mem_Icc, mem_insert]
    omega
  rw [hI, sum_insert (by simp)]
  simp only [properPrimePowerWeight, Nat.not_prime_zero, not_false_eq_true,
    if_true, ArithmeticFunction.map_zero, zero_add]

private theorem sum_Ioc_inv_mul_properPrimePowerWeight (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ * properPrimePowerWeight n =
      mertensPrimePowerWeightedRemainder N := by
  rw [mertensPrimePowerWeightedRemainder_eq, sum_filter,
    Icc_one_eq_Ioc_zero]
  refine sum_congr rfl fun n hn => ?_
  by_cases hp : n.Prime
  · simp [properPrimePowerWeight, hp]
  · simp [properPrimePowerWeight, hp, div_eq_mul_inv, mul_comm]

/-- Finite summation by parts for exactly the weighted proper-prime-power
remainder.  This is the discrete Abel identity used below. -/
theorem mertensPrimePowerWeightedRemainder_eq_abel {N : ℕ} (hN : 0 < N) :
    mertensPrimePowerWeightedRemainder N =
      (N : ℝ)⁻¹ * mertensPrimePowerCounting N +
        ∑ n ∈ Ioc 0 (N - 1),
          mertensPrimePowerCounting n *
            ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) := by
  have hab := Finset.sum_Ioc_by_parts
    (R := ℝ) (M := ℝ)
    (fun n : ℕ => (n : ℝ)⁻¹) properPrimePowerWeight hN
  simp_rw [sum_range_succ_properPrimePowerWeight] at hab
  have hcount0 : mertensPrimePowerCounting 0 = 0 := by
    rw [mertensPrimePowerCounting_eq]
    simp
  rw [hcount0] at hab
  norm_num at hab
  have hsum :
      -∑ n ∈ Ioc 0 (N - 1),
          (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹) *
            mertensPrimePowerCounting n =
        ∑ n ∈ Ioc 0 (N - 1),
          mertensPrimePowerCounting n *
            ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun n hn => ?_
    ring
  calc
    mertensPrimePowerWeightedRemainder N =
        ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ * properPrimePowerWeight n :=
      (sum_Ioc_inv_mul_properPrimePowerWeight N).symm
    _ = (N : ℝ)⁻¹ * mertensPrimePowerCounting N -
          ∑ n ∈ Ioc 0 (N - 1),
            (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹) *
              mertensPrimePowerCounting n := by
      simpa only [smul_eq_mul, Nat.cast_add, Nat.cast_one] using hab
    _ = (N : ℝ)⁻¹ * mertensPrimePowerCounting N +
          ∑ n ∈ Ioc 0 (N - 1),
            mertensPrimePowerCounting n *
              ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) := by
      rw [sub_eq_add_neg, hsum]

private theorem inv_sub_inv_succ_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹ := by
  apply sub_nonneg.mpr
  exact inv_anti₀ (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn))
    (by exact_mod_cast Nat.le_succ n)

private theorem inv_sub_inv_succ_le_sq {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹ ≤ 1 / (n : ℝ) ^ 2 := by
  have hnpos : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : (0 : ℝ) < n + 1 := by positivity
  have heq :
      (n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹ =
        1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by norm_num
    rw [hcast]
    field_simp [hnpos.ne', hspos.ne']
    ring
  rw [heq]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

private theorem sqrt_div_sq_eq_rpow {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) / (n : ℝ) ^ 2 =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hnpos : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_sub hnpos]
  congr 1
  norm_num

private theorem summable_mertens_three_halves :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  exact Real.summable_nat_rpow.mpr (by norm_num)

/-- The total weighted contribution of proper prime powers is bounded by an
absolute constant. -/
theorem exists_mertensPrimePowerWeightedRemainder_le :
    ∃ C : ℝ, ∀ N : ℕ, mertensPrimePowerWeightedRemainder N ≤ C := by
  obtain ⟨C, hC⟩ := exists_mertensPrimePowerCounting_le_sqrt
  let D : ℝ := |C|
  let T : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))
  have hD0 : 0 ≤ D := by simpa [D] using abs_nonneg C
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨D + D * T, ?_⟩
  intro N
  rcases N.eq_zero_or_pos with rfl | hN
  · have hbound0 : 0 ≤ D + D * T :=
      add_nonneg hD0 (mul_nonneg hD0 hT0)
    simpa [mertensPrimePowerWeightedRemainder,
      mertensMangoldtWeightedSum, mertensPrimeLogOverSum] using hbound0
  have hendpoint :
      (N : ℝ)⁻¹ * mertensPrimePowerCounting N ≤ D := by
    have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hcountD : mertensPrimePowerCounting N ≤ D * Real.sqrt N :=
      (hC N).2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _))
    have hsqrt : Real.sqrt (N : ℝ) ≤ N :=
      Real.sqrt_le_self_iff.mpr (Or.inr (Nat.one_le_cast.mpr hN))
    have hsqrtDiv : Real.sqrt (N : ℝ) / N ≤ 1 :=
      (div_le_one hNreal).mpr hsqrt
    calc
      (N : ℝ)⁻¹ * mertensPrimePowerCounting N ≤
          (N : ℝ)⁻¹ * (D * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hcountD (inv_nonneg.mpr hNreal.le)
      _ = D * (Real.sqrt N / N) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left hsqrtDiv hD0
      _ = D := mul_one D
  have hterm : ∀ n ∈ Ioc 0 (N - 1),
      mertensPrimePowerCounting n *
          ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) ≤
        D * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Ioc.mp hn).1
    have hdelta0 := inv_sub_inv_succ_nonneg hn1
    have hcount : mertensPrimePowerCounting n ≤ D * Real.sqrt n :=
      (hC n).2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _))
    have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    calc
      mertensPrimePowerCounting n *
          ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) ≤
          (D * Real.sqrt n) *
            ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hcount hdelta0
      _ ≤ (D * Real.sqrt n) * (1 / (n : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (inv_sub_inv_succ_le_sq hn1)
          (mul_nonneg hD0 hsqrt0)
      _ = D * (Real.sqrt n / (n : ℝ) ^ 2) := by ring
      _ = D * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [sqrt_div_sq_eq_rpow hn1]
  have hfinite :
      ∑ n ∈ Ioc 0 (N - 1),
          mertensPrimePowerCounting n *
            ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) ≤ D * T := by
    calc
      ∑ n ∈ Ioc 0 (N - 1),
          mertensPrimePowerCounting n *
            ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) ≤
          ∑ n ∈ Ioc 0 (N - 1),
            D * (n : ℝ) ^ (-(3 / 2 : ℝ)) := sum_le_sum hterm
      _ = D * ∑ n ∈ Ioc 0 (N - 1),
          (n : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [mul_sum]
      _ ≤ D * T := by
        apply mul_le_mul_of_nonneg_left _ hD0
        exact summable_mertens_three_halves.sum_le_tsum _
          (fun n hn => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [mertensPrimePowerWeightedRemainder_eq_abel hN]
  exact add_le_add hendpoint hfinite

/-- The matching lower bound for the weighted prime sum. -/
theorem log_sub_const_le_mertensPrimeLogOverSum :
    ∃ C : ℝ, ∀ N : ℕ, 0 < N →
      Real.log N - C ≤ mertensPrimeLogOverSum N := by
  obtain ⟨C, hC⟩ := exists_mertensPrimePowerWeightedRemainder_le
  refine ⟨1 + C, ?_⟩
  intro N hN
  have hmang := log_sub_one_le_mertensMangoldtWeightedSum hN
  have hrem := hC N
  rw [mertensPrimePowerWeightedRemainder] at hrem
  linarith

/-- Elementary Mertens-I estimate in the form needed for the next discrete
Abel summation proving existence of the Mertens-II constant. -/
theorem eventually_abs_mertensPrimeLogOverSum_sub_log_le :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      |mertensPrimeLogOverSum N - Real.log N| ≤ C := by
  obtain ⟨C, hlow⟩ := log_sub_const_le_mertensPrimeLogOverSum
  refine ⟨max C (Real.log 4 + 4), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  rw [abs_le]
  constructor
  · have := hlow N hNpos
    linarith [le_max_left C (Real.log 4 + 4)]
  · have := mertensPrimeLogOverSum_le_log_add hNpos
    linarith [le_max_right C (Real.log 4 + 4)]

end

end PrimeGapNormality.Prime
