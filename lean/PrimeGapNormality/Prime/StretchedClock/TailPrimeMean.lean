import PrimeGapNormality.Prime.StretchedClock.TailAndPositions
import PrimeGapNormality.Prime.ChebyshevNthPrime

/-!
# The global first-gap majorant from elementary Chebyshev bounds

The averaging set is the full prime-index prefix. No conditional estimate
on a clock label or short interval is used.
-/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset Filter
open scoped Topology
noncomputable section

def gapMajorant (n : ℕ) : ℝ :=
  ∑' j : ℕ, (primeGap (n + j) : ℝ) / (2 : ℝ) ^ j

theorem shifted_prime_le_product (n j : ℕ) :
    (nthPrime (n + j) : ℝ) ≤
      4 * ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1) *
        ((j + 1 : ℕ) : ℝ) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have h1 : ((n + j + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_nonneg hn hj]
  have h2 : ((n + j + 2 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_nonneg hn hj]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((n + j + 2 : ℕ) : ℝ)) h2
  rw [Real.log_mul (by positivity : (((n + 2 : ℕ) : ℝ)) ≠ 0)
    (by positivity : (((j + 1 : ℕ) : ℝ)) ≠ 0)] at hlog
  have hjlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))
  have hL : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
  have hlogBound : Real.log ((n + j + 2 : ℕ) : ℝ) + 1 ≤
      (Real.log ((n + 2 : ℕ) : ℝ) + 1) * ((j + 1 : ℕ) : ℝ) := by
    push_cast at hlog hL hjlog ⊢
    nlinarith [mul_nonneg hL hj]
  have hlog0 : 0 ≤ Real.log ((n + j + 2 : ℕ) : ℝ) + 1 := by
    have hn2 : (1 : ℝ) ≤ ((n + j + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ n + j + 2 by omega)
    have hh := Real.log_nonneg hn2
    linarith
  calc
    (nthPrime (n + j) : ℝ) ≤
        4 * ((n + j + 1 : ℕ) : ℝ) * (Real.log ((n + j + 2 : ℕ) : ℝ) + 1) :=
      nthPrime_le_succ_mul_log (n + j)
    _ ≤ 4 * (((n + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        ((Real.log ((n + 2 : ℕ) : ℝ) + 1) * ((j + 1 : ℕ) : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hlogBound hlog0 (by positivity)
    _ = _ := by ring

theorem frozenTail_two_le_log (n : ℕ) :
    frozenTail 2 n ≤
      24 * ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1) := by
  let C : ℝ := 4 * ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1)
  have hC : 0 ≤ C := by
    have hn2 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ n + 2 by omega)
    have hh := Real.log_nonneg hn2
    dsimp only [C]
    positivity
  have hs : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ (j + 1)) := by
    simpa only [Nat.zero_add] using summable_succ_sq_div_pow (by norm_num : (1 : ℝ) < 2) 0
  have hsum : (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ (j + 1)) ≤ 6 := by
    have hh := tsum_succ_sq_div_pow_le (by norm_num : (1 : ℝ) < 2) 0
    norm_num [posMassGeomCoeff] at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have ht := (summable_posMass_nthPrime (by norm_num : (1 : ℝ) < 2) n).tsum_le_tsum
    (fun j => (div_le_div_of_nonneg_right (shifted_prime_le_product n j)
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1))).trans_eq (by dsimp [C]; ring))
    (hs.mul_left C)
  rw [tsum_mul_left] at ht
  calc
    frozenTail 2 n ≤ C * ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ (j + 1) := ht
    _ ≤ C * 6 := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by dsimp [C]; ring

theorem frozenGapTail_summable {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    Summable (fun j : ℕ => (primeGap (n + j) : ℝ) / (q : ℝ) ^ (j + 1)) := by
  have hqreal : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  apply Summable.of_nonneg_of_le
    (fun j => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_lt_one.trans hqreal).le _))
    (fun j => ?_) (summable_posMass_nthPrime hqreal (n + 1))
  have hh : (primeGap (n + j) : ℝ) ≤ nthPrime (n + 1 + j) := by
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
      (Nat.cast_le.mpr (primeGap_le_nthPrime_succ (n + j)) :
        (primeGap (n + j) : ℝ) ≤ nthPrime (n + j + 1))
  exact div_le_div_of_nonneg_right hh (pow_nonneg (zero_lt_one.trans hqreal).le _)

theorem gapMajorant_eq_two_frozenGapTail (n : ℕ) :
    gapMajorant n = 2 * frozenGapTail 2 n := by
  unfold gapMajorant frozenGapTail gapTail
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  norm_num only [Nat.cast_ofNat]
  rw [pow_succ]
  field_simp <;> ring

theorem gapMajorant_summable (n : ℕ) :
    Summable (fun j : ℕ => (primeGap (n + j) : ℝ) / (2 : ℝ) ^ j) := by
  apply ((frozenGapTail_summable (by norm_num : 2 ≤ 2) n).mul_left (2 : ℝ)).congr
  intro j
  norm_num only [Nat.cast_ofNat]
  rw [pow_succ]
  field_simp <;> ring

theorem gapMajorant_nonneg (n : ℕ) : 0 ≤ gapMajorant n :=
  tsum_nonneg fun j => div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem frozenGapTail_le_gapMajorant_div {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    frozenGapTail q n ≤ gapMajorant n / (q : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have ht := (frozenGapTail_summable hq n).tsum_le_tsum
    (fun j => show (primeGap (n + j) : ℝ) / (q : ℝ) ^ (j + 1) ≤
        ((primeGap (n + j) : ℝ) / (2 : ℝ) ^ j) / (q : ℝ) from by
      have hp : (2 : ℝ) ^ j * (q : ℝ) ≤ (q : ℝ) ^ (j + 1) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq) j) hqpos.le
      have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg (primeGap (n + j)))
        (mul_pos (by positivity) hqpos) hp
      simpa only [div_mul_eq_div_div] using hh)
    ((gapMajorant_summable n).div_const (q : ℝ))
  simpa only [frozenGapTail, gapTail, gapMajorant, tsum_div_const] using ht

/-- The complete prefix telescopes exactly, before any label restriction. -/
theorem sum_gapMajorant_eq (N : ℕ) :
    (∑ n ∈ range N, gapMajorant n) = 2 * (frozenTail 2 N - frozenTail 2 0) := by
  have ht := sum_gapTail_telescope (by norm_num : (1 : ℝ) < 2)
    (fun k => (nthPrime k : ℝ)) (nthPrime_div_pow_summable (by norm_num)) 0 N
  have ht' : (∑ n ∈ range N, frozenGapTail 2 n) = frozenTail 2 N - frozenTail 2 0 := by
    simpa only [frozenGapTail, frozenTail, Nat.cast_ofNat, Nat.zero_add, ← primeGap_cast] using ht
  simp_rw [gapMajorant_eq_two_frozenGapTail]
  rw [← mul_sum, ht']

/-- Elementary global N log N bound, with no PNT or tuple hypothesis. -/
theorem sum_gapMajorant_le (N : ℕ) :
    (∑ n ∈ range N, gapMajorant n) ≤
      48 * ((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1) := by
  have hzero : 0 ≤ frozenTail 2 0 :=
    posMass_nonneg (by norm_num : (1 : ℝ) < 2)
      (fun k => (nthPrime k : ℝ)) (fun k => Nat.cast_nonneg _) 0
  have hN := frozenTail_two_le_log N
  rw [sum_gapMajorant_eq]
  nlinarith

end
end PrimeGapNormality.Prime.StretchedClock
