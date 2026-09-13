import PrimeGapNormality.Prime.EulerProd
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The convergent correction term in Mertens' product theorem

This file isolates the part of Mertens' product theorem which follows from
elementary logarithmic estimates and the convergence of `sum 1 / n^2`.
For a prime `p`, put

`c(p) = -log (1 - 1 / p) - 1 / p`.

Then `0 <= c(p) <= 2 / p^2`, so the correction series is summable, and

`log (eulerProdNat N) = -sum_{p <= N} 1 / p - sum_{p <= N} c(p)`.

The remaining analytic input for the full product limit is the identified
Mertens-II limit

`sum_{p <= N} 1 / p - log (log N) -> gamma - sum_p c(p)`.

Neither `chebyshev_asymptotic` from `PrimeNumberTheoremAnd.Consequences` nor
Mathlib's divergence theorem for prime reciprocals supplies that constant.
In particular, `theta(x) = x + o(x)` alone does not make the error term in
the relevant partial-summation integral summable.  No conditional endpoint
is declared here.
-/

namespace PrimeGapNormality.Prime

open Filter Finset

noncomputable section

/-- The absolutely summable prime-power correction in the logarithm of the
finite Euler product.  It is extended by zero away from primes. -/
def mertensPrimeCorrection (n : ℕ) : ℝ :=
  if n.Prime then -Real.log (1 - (n : ℝ)⁻¹) - (n : ℝ)⁻¹ else 0

/-- Partial sum of reciprocal primes up to `N`. -/
def mertensPrimeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesLE, (p : ℝ)⁻¹

/-- Partial sum of the convergent logarithmic correction up to `N`. -/
def mertensPrimeCorrectionSum (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesLE, mertensPrimeCorrection p

/-- The limiting correction constant
`sum_p (-log (1 - 1/p) - 1/p)`. -/
def mertensPrimeCorrectionConstant : ℝ :=
  ∑' n : ℕ, mertensPrimeCorrection n

private theorem mertens_neg_log_one_sub_sub_nonneg {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ -Real.log (1 - x) - x := by
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith

private theorem mertens_neg_log_one_sub_sub_le_two_sq {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -Real.log (1 - x) - x ≤ 2 * x ^ 2 := by
  have hx1 : x < 1 := hxhalf.trans_lt (by norm_num)
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hneglog : -Real.log (1 - x) ≤ (1 - x)⁻¹ - 1 := by
    linarith
  have hstep :
      -Real.log (1 - x) - x ≤ ((1 - x)⁻¹ - 1) - x :=
    sub_le_sub_right hneglog x
  have hid : ((1 - x)⁻¹ - 1) - x = x ^ 2 / (1 - x) := by
    field_simp [ne_of_gt hpos]
    ring
  have hfrac : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg x]
  rw [hid] at hstep
  exact hstep.trans hfrac

private theorem mertens_prime_inv_bounds {p : ℕ} (hp : p.Prime) :
    0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by positivity
  refine ⟨(inv_nonneg.mpr hp0.le), ?_⟩
  have h := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2
  simpa using h

@[simp] theorem mertensPrimeCorrection_of_prime {p : ℕ} (hp : p.Prime) :
    mertensPrimeCorrection p =
      -Real.log (1 - (p : ℝ)⁻¹) - (p : ℝ)⁻¹ := by
  simp [mertensPrimeCorrection, hp]

@[simp] theorem mertensPrimeCorrection_of_not_prime {n : ℕ} (hn : ¬ n.Prime) :
    mertensPrimeCorrection n = 0 := by
  simp [mertensPrimeCorrection, hn]

theorem mertensPrimeCorrection_nonneg (n : ℕ) :
    0 ≤ mertensPrimeCorrection n := by
  by_cases hn : n.Prime
  · rw [mertensPrimeCorrection_of_prime hn]
    obtain ⟨h0, hhalf⟩ := mertens_prime_inv_bounds hn
    exact mertens_neg_log_one_sub_sub_nonneg h0
      (hhalf.trans_lt (by norm_num))
  · simp [mertensPrimeCorrection, hn]

theorem mertensPrimeCorrection_le_two_inv_sq (n : ℕ) :
    mertensPrimeCorrection n ≤ 2 * ((n : ℝ) ^ 2)⁻¹ := by
  by_cases hn : n.Prime
  · rw [mertensPrimeCorrection_of_prime hn]
    obtain ⟨h0, hhalf⟩ := mertens_prime_inv_bounds hn
    have h := mertens_neg_log_one_sub_sub_le_two_sq h0 hhalf
    simpa [inv_pow] using h
  · simp [mertensPrimeCorrection, hn]

/-- Absolute convergence of the correction term. -/
theorem summable_mertensPrimeCorrection :
    Summable mertensPrimeCorrection := by
  refine Summable.of_nonneg_of_le mertensPrimeCorrection_nonneg
    mertensPrimeCorrection_le_two_inv_sq ?_
  exact (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 2

/-- Ordinary range partial sums of the correction converge to its `tsum`. -/
theorem tendsto_sum_range_mertensPrimeCorrection :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, mertensPrimeCorrection n) atTop
      (nhds mertensPrimeCorrectionConstant) := by
  exact summable_mertensPrimeCorrection.hasSum.tendsto_sum_nat

theorem sum_range_succ_mertensPrimeCorrection (N : ℕ) :
    (∑ n ∈ range (N + 1), mertensPrimeCorrection n) =
      mertensPrimeCorrectionSum N := by
  rw [Nat.range_succ_eq_Icc_zero, mertensPrimeCorrectionSum,
    Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  refine sum_congr rfl fun n hn => ?_
  by_cases hp : n.Prime
  · rw [if_pos hp]
  · rw [if_neg hp, mertensPrimeCorrection_of_not_prime hp]

/-- Prime-indexed partial sums of the correction converge to the same
constant. -/
theorem tendsto_mertensPrimeCorrectionSum :
    Tendsto mertensPrimeCorrectionSum atTop
      (nhds mertensPrimeCorrectionConstant) := by
  have h := tendsto_sum_range_mertensPrimeCorrection.comp
    (tendsto_add_atTop_nat 1)
  refine h.congr' (Filter.Eventually.of_forall ?_)
  intro N
  change (∑ n ∈ range (N + 1), mertensPrimeCorrection n) =
    mertensPrimeCorrectionSum N
  exact sum_range_succ_mertensPrimeCorrection N

/-- Exact finite decomposition of the logarithm of the paper's Euler
product into reciprocal primes and the summable correction. -/
theorem mertens_log_eulerProdNat_eq (N : ℕ) :
    Real.log (eulerProdNat N) =
      -mertensPrimeReciprocalSum N - mertensPrimeCorrectionSum N := by
  rw [eulerProdNat, Real.log_prod]
  · calc
      ∑ p ∈ N.primesLE, Real.log (1 - (p : ℝ)⁻¹) =
          ∑ p ∈ N.primesLE,
            (-(p : ℝ)⁻¹ - mertensPrimeCorrection p) := by
            refine sum_congr rfl fun p hp => ?_
            have hp' : p.Prime := Nat.prime_of_mem_primesLE hp
            rw [mertensPrimeCorrection_of_prime hp']
            ring
      _ = -mertensPrimeReciprocalSum N - mertensPrimeCorrectionSum N := by
        simp only [sum_sub_distrib, sum_neg_distrib,
          mertensPrimeReciprocalSum, mertensPrimeCorrectionSum]
  · intro p hp
    exact one_sub_inv_ne_zero (Nat.prime_of_mem_primesLE hp)

/-- Exact exponential form of the product.  This makes the two limits needed
for Mertens' theorem explicit: the identified reciprocal-prime sum and the
already summable correction. -/
theorem eulerProdNat_mul_log_eq_mertens_exp {N : ℕ} (hN : 2 ≤ N) :
    eulerProdNat N * Real.log N =
      Real.exp
        (-(mertensPrimeReciprocalSum N - Real.log (Real.log N)) -
          mertensPrimeCorrectionSum N) := by
  have hV : 0 < eulerProdNat N := eulerProdNat_pos N
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num) hN))
  calc
    eulerProdNat N * Real.log N =
        Real.exp (Real.log (eulerProdNat N)) *
          Real.exp (Real.log (Real.log N)) := by
            rw [Real.exp_log hV, Real.exp_log hlogN]
    _ = Real.exp
        (Real.log (eulerProdNat N) + Real.log (Real.log N)) := by
          rw [Real.exp_add]
    _ = Real.exp
        (-(mertensPrimeReciprocalSum N - Real.log (Real.log N)) -
          mertensPrimeCorrectionSum N) := by
          rw [mertens_log_eulerProdNat_eq]
          ring

/-
The first genuinely missing analytic theorem is the following identified
Mertens-II limit (shown here only as a comment, not as an assumption):

  Tendsto
    (fun N : ℕ =>
      mertensPrimeReciprocalSum N - Real.log (Real.log N))
    atTop
    (nhds
      (Real.eulerMascheroniConstant - mertensPrimeCorrectionConstant))

Together with `tendsto_mertensPrimeCorrectionSum` and
`mertens_log_eulerProdNat_eq`, it gives

  log (eulerProdNat N) + log (log N) -> -gamma,

and hence `eulerProdNat N * log N -> exp (-gamma)`.

The available theorem `chebyshev_asymptotic` is only
`theta ~ id`.  Its `o(x)` error is not known to be integrable after division
by `x^2 log x`, so it cannot discharge the displayed constant limit without
an additional Mertens argument or a quantitatively stronger PNT remainder.
-/

end

end PrimeGapNormality.Prime
