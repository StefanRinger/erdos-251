import PrimeGapNormality.Prime.MertensPrimeReciprocal
import Mathlib.Algebra.BigOperators.Module

/-!
# The Mertens-II convergence step

This file applies discrete Abel summation to the unconditional estimate

`sum_{p <= N} log p / p = log N + O(1)`

proved in `MertensPrimeReciprocal`.  The bounded weighted error is multiplied
by the positive telescoping kernel

`1 / log n - 1 / log (n + 1)`.

Consequently its contribution is absolutely summable, without a PNT or a
Mertens hypothesis.  The remaining main-term problem is isolated at the end
of the file.
-/

namespace PrimeGapNormality.Prime

open Filter Finset

noncomputable section

/-- Error in the elementary weighted-prime estimate. -/
def mertensPrimeWeightedError (N : ℕ) : ℝ :=
  mertensPrimeLogOverSum N - Real.log N

/-- The positive Abel kernel, extended by zero at `0` and `1`. -/
def mertensInvLogDelta (N : ℕ) : ℝ :=
  if 2 ≤ N then
    1 / Real.log N - 1 / Real.log (N + 1)
  else 0

/-- The weighted error term in the second Abel summation. -/
def mertensSecondErrorTerm (N : ℕ) : ℝ :=
  mertensPrimeWeightedError N * mertensInvLogDelta N

private theorem weightedPrimeSum_succ (N : ℕ) :
    mertensPrimeLogOverSum (N + 1) =
      mertensPrimeLogOverSum N +
        if (N + 1).Prime then
          Real.log (N + 1) / (N + 1 : ℝ)
        else 0 := by
  rw [mertensPrimeLogOverSum, mertensPrimeLogOverSum, Nat.primesLE_succ]
  split_ifs with hp
  · rw [sum_insert (Nat.notMem_primesLE N)]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (add_comm
        (Real.log (N + 1) / (N + 1 : ℝ))
        (∑ p ∈ N.primesLE, Real.log p / p))
  · rw [add_zero]

private theorem weightedPrimeSum_diff {N : ℕ} (hN : 2 ≤ N) :
    mertensPrimeLogOverSum N - mertensPrimeLogOverSum (N - 1) =
      if N.Prime then Real.log N / N else 0 := by
  have hpred : N = (N - 1) + 1 :=
    (Nat.sub_add_cancel (le_trans (by norm_num : (1 : ℕ) ≤ 2) hN)).symm
  rw [hpred, weightedPrimeSum_succ]
  simp

/-- Exact finite Abel formula converting reciprocal primes into the weighted
prime sum. -/
theorem mertensPrimeReciprocalSum_eq_abel {N : ℕ} (hN : 2 ≤ N) :
    mertensPrimeReciprocalSum N =
      mertensPrimeLogOverSum N / Real.log N +
        ∑ n ∈ Icc 2 (N - 1),
          mertensPrimeLogOverSum n *
            (1 / Real.log n - 1 / Real.log (n + 1)) := by
  have hterm : ∀ n : ℕ, 2 ≤ n → n ≤ N →
      (if n.Prime then (n : ℝ)⁻¹ else 0) =
        (mertensPrimeLogOverSum n - mertensPrimeLogOverSum (n - 1)) /
          Real.log n := by
    intro n hn _hnN
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (Nat.one_lt_cast.mpr
        (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hn))).ne'
    rw [weightedPrimeSum_diff hn]
    split_ifs with hp
    · field_simp [hlog]
    · simp
  have hprime :
      mertensPrimeReciprocalSum N =
        ∑ n ∈ Icc 2 N, (if n.Prime then (n : ℝ)⁻¹ else 0) := by
    rw [mertensPrimeReciprocalSum,
      Nat.primesLE_eq_filter_Icc_two, sum_filter]
  rw [hprime]
  have hdiff :
      ∑ n ∈ Icc 2 N, (if n.Prime then (n : ℝ)⁻¹ else 0) =
        ∑ n ∈ Icc 2 N,
          (mertensPrimeLogOverSum n - mertensPrimeLogOverSum (n - 1)) /
            Real.log n :=
    sum_congr rfl fun n hn => hterm n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
  rw [hdiff]
  have hsplit :
      ∑ n ∈ Icc 2 N,
          (mertensPrimeLogOverSum n - mertensPrimeLogOverSum (n - 1)) /
            Real.log n =
        ∑ n ∈ Icc 2 N, mertensPrimeLogOverSum n / Real.log n -
          ∑ n ∈ Icc 2 N,
            mertensPrimeLogOverSum (n - 1) / Real.log n := by
    simp_rw [sub_div, sum_sub_distrib]
  rw [hsplit]
  have hshift :
      ∑ n ∈ Icc 2 N, mertensPrimeLogOverSum (n - 1) / Real.log n =
        ∑ n ∈ Icc 1 (N - 1),
          mertensPrimeLogOverSum n / Real.log (n + 1) := by
    refine sum_nbij (fun n => n - 1) ?_ ?_ ?_ ?_
    · intro n hn
      rcases mem_Icc.mp hn with ⟨hn2, hnN⟩
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb hab
      have ha1 : 1 ≤ a := le_trans (by norm_num : (1 : ℕ) ≤ 2) (mem_Icc.mp ha).1
      have hb1 : 1 ≤ b := le_trans (by norm_num : (1 : ℕ) ≤ 2) (mem_Icc.mp hb).1
      exact
        (Nat.sub_add_cancel ha1).symm.trans
          ((congrArg (fun n => n + 1) hab).trans (Nat.sub_add_cancel hb1))
    · intro n hn
      rcases mem_Icc.mp hn with ⟨hn1, hnN⟩
      refine ⟨n + 1, mem_Icc.mpr ⟨by omega, by omega⟩, Nat.add_sub_cancel n 1⟩
    · intro n hn
      have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 2) (mem_Icc.mp hn).1
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        exact_mod_cast Nat.sub_add_cancel hn1
      simp [hcast]
  rw [hshift]
  have hA1 : mertensPrimeLogOverSum 1 = 0 := by
    simp [mertensPrimeLogOverSum]
  have hleft : Icc 1 (N - 1) = insert 1 (Icc 2 (N - 1)) := by
    exact (insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ N - 1)).symm
  rw [hleft, sum_insert (by simp), hA1, zero_div, zero_add]
  have hright : Icc 2 N = insert N (Icc 2 (N - 1)) := by
    have hNs : N = N - 1 + 1 :=
      (Nat.sub_add_cancel (le_trans (by norm_num : (1 : ℕ) ≤ 2) hN)).symm
    rw [hNs]
    exact (insert_Icc_right_eq_Icc_add_one (by omega : 2 ≤ N - 1 + 1)).symm
  have hNnot : N ∉ Icc 2 (N - 1) := by
    intro hmem
    have hle := (mem_Icc.mp hmem).2
    omega
  rw [hright, sum_insert hNnot]
  have hmid :
      ∑ n ∈ Icc 2 (N - 1), mertensPrimeLogOverSum n / Real.log n -
          ∑ n ∈ Icc 2 (N - 1), mertensPrimeLogOverSum n / Real.log (n + 1) =
        ∑ n ∈ Icc 2 (N - 1),
          mertensPrimeLogOverSum n *
            (1 / Real.log n - 1 / Real.log (n + 1)) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, one_div, one_div]
  calc
    (mertensPrimeLogOverSum N / Real.log N +
          ∑ n ∈ Icc 2 (N - 1), mertensPrimeLogOverSum n / Real.log n) -
        ∑ n ∈ Icc 2 (N - 1),
          mertensPrimeLogOverSum n / Real.log (n + 1) =
      mertensPrimeLogOverSum N / Real.log N +
        ((∑ n ∈ Icc 2 (N - 1), mertensPrimeLogOverSum n / Real.log n) -
          ∑ n ∈ Icc 2 (N - 1),
            mertensPrimeLogOverSum n / Real.log (n + 1)) := by ring
    _ = mertensPrimeLogOverSum N / Real.log N +
        ∑ n ∈ Icc 2 (N - 1),
          mertensPrimeLogOverSum n *
            (1 / Real.log n - 1 / Real.log (n + 1)) := by rw [hmid]

private theorem invLogDelta_nonneg_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ 1 / Real.log N - 1 / Real.log (N + 1) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (by omega))
  have hlogMono : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_le_log hNpos (Nat.cast_le.mpr (Nat.le_succ N))
  simpa [one_div] using sub_nonneg.mpr (inv_anti₀ hlogN hlogMono)

theorem mertensInvLogDelta_nonneg (N : ℕ) :
    0 ≤ mertensInvLogDelta N := by
  rw [mertensInvLogDelta]
  split_ifs with hN
  · exact invLogDelta_nonneg_of_two_le hN
  · exact le_rfl

private theorem sum_Ico_telescope (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, (f k - f (k + 1)) = f m - f n := by
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro n hmn ih
    rw [sum_Ico_succ_top hmn, ih]
    ring

private theorem sum_range_mertensInvLogDelta_le (M : ℕ) :
    ∑ N ∈ range M, mertensInvLogDelta N ≤ 1 / Real.log 2 := by
  rcases le_total M 2 with hM | hM
  · have hzero : ∑ N ∈ range M, mertensInvLogDelta N = 0 := by
      apply sum_eq_zero
      intro N hN
      have hlt : N < 2 := (mem_range.mp hN).trans_le hM
      rw [mertensInvLogDelta, if_neg (not_le.mpr hlt)]
    rw [hzero]
    exact div_nonneg zero_le_one (Real.log_nonneg (by norm_num))
  · have hdecomp : range M = range 2 ∪ Ico 2 M := by
      ext N
      simp [mem_range, mem_Ico]
      omega
    have hdis : Disjoint (range 2) (Ico 2 M) := by
      rw [disjoint_left]
      intro N hN hI
      have hNlt : N < 2 := mem_range.mp hN
      have hNge : 2 ≤ N := (mem_Ico.mp hI).1
      exact (Nat.not_lt_of_ge hNge) hNlt
    rw [hdecomp, sum_union hdis]
    have hzero : ∑ N ∈ range 2, mertensInvLogDelta N = 0 := by
      apply sum_eq_zero
      intro N hN
      have hlt : N < 2 := mem_range.mp hN
      rw [mertensInvLogDelta, if_neg (not_le.mpr hlt)]
    rw [hzero, zero_add]
    have hrewrite : ∀ N ∈ Ico 2 M,
        mertensInvLogDelta N = 1 / Real.log N - 1 / Real.log (N + 1) := by
      intro N hN
      rw [mertensInvLogDelta, if_pos (mem_Ico.mp hN).1]
    rw [sum_congr rfl hrewrite]
    have htel :
        ∑ N ∈ Ico 2 M, (1 / Real.log N - 1 / Real.log (N + 1)) =
          1 / Real.log 2 - 1 / Real.log M := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        (sum_Ico_telescope (fun N => 1 / Real.log N) hM)
    rw [htel]
    have hnonneg : 0 ≤ 1 / Real.log M := by
      exact div_nonneg zero_le_one
        (Real.log_nonneg (Nat.one_le_cast.mpr (by omega)))
    linarith

/-- The Abel kernel is summable.  This uses its exact telescoping form, a
stronger estimate than comparison with `1/(n log^2 n)`. -/
theorem summable_mertensInvLogDelta : Summable mertensInvLogDelta := by
  exact summable_of_sum_range_le mertensInvLogDelta_nonneg
    sum_range_mertensInvLogDelta_le

/-- Absolute summability of the entire bounded weighted-error contribution. -/
theorem summable_mertensSecondErrorTerm : Summable mertensSecondErrorTerm := by
  obtain ⟨C, hC⟩ := eventually_abs_mertensPrimeLogOverSum_sub_log_le
  refine (summable_mertensInvLogDelta.mul_left |C|).of_norm_bounded_eventually_nat ?_
  filter_upwards [hC] with N hN
  have hdelta := mertensInvLogDelta_nonneg N
  rw [mertensSecondErrorTerm, mertensPrimeWeightedError, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg hdelta]
  exact mul_le_mul_of_nonneg_right (hN.trans (le_abs_self C)) hdelta

/-- Partial sums of the weighted error converge to their absolutely
convergent series. -/
theorem tendsto_sum_range_mertensSecondErrorTerm :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, mertensSecondErrorTerm n) atTop
      (nhds (∑' n : ℕ, mertensSecondErrorTerm n)) :=
  summable_mertensSecondErrorTerm.hasSum.tendsto_sum_nat

/-- The boundary term in the second Abel summation vanishes. -/
theorem tendsto_mertensPrimeWeightedError_div_log :
    Tendsto
      (fun N : ℕ => mertensPrimeWeightedError N / Real.log N)
      atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := eventually_abs_mertensPrimeLogOverSum_sub_log_le
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmajor :
      Tendsto (fun N : ℕ => |C| / Real.log N) atTop (nhds 0) := by
    convert hlog.inv_tendsto_atTop.const_mul |C| using 1 <;>
      simp [div_eq_mul_inv]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hmajor
  filter_upwards [hC, hlog.eventually (eventually_gt_atTop 0)] with N hN hlogN
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlogN]
  exact div_le_div_of_nonneg_right (hN.trans (le_abs_self C)) hlogN.le

/-! ### The main sum-integral correction -/

/-- The difference between the `log log` increment and the main Abel
summand.  It is extended by zero below `2`. -/
def mertensSecondMainCorrection (N : ℕ) : ℝ :=
  if 2 ≤ N then
    (Real.log (Real.log (N + 1)) - Real.log (Real.log N)) -
      Real.log N * (1 / Real.log N - 1 / Real.log (N + 1))
  else 0

/-- The main expression left after separating the bounded weighted error. -/
def mertensSecondMain (N : ℕ) : ℝ :=
  1 + ∑ n ∈ Icc 2 (N - 1),
      Real.log n * (1 / Real.log n - 1 / Real.log (n + 1)) -
    Real.log (Real.log N)

private theorem log_nat_pos_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    0 < Real.log (N : ℝ) :=
  Real.log_pos (Nat.one_lt_cast.mpr
    (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hN))

private theorem log_succ_sub_log_nonneg {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log N := by
  apply sub_nonneg.mpr
  exact Real.log_le_log (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hN))
    (Nat.cast_le.mpr (Nat.le_succ N))

private theorem mainCorrection_nonneg_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ mertensSecondMainCorrection N := by
  let a : ℝ := Real.log N
  let b : ℝ := Real.log (N + 1)
  have ha : 0 < a := log_nat_pos_of_two_le hN
  have hb : 0 < b := by
    simpa [b, Nat.cast_add, Nat.cast_one] using
      (log_nat_pos_of_two_le (by omega : 2 ≤ N + 1))
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Real.log_le_log (Nat.cast_pos.mpr (by omega))
      (by norm_num : (N : ℝ) ≤ (N : ℝ) + 1)
  have hquot : 0 < b / a := div_pos hb ha
  have hlogdiv : Real.log b - Real.log a = Real.log (b / a) :=
    (Real.log_div hb.ne' ha.ne').symm
  have hmain : a * (1 / a - 1 / b) = 1 - a / b := by
    field_simp [ha.ne', hb.ne']
  have hinv : (b / a)⁻¹ = a / b := by
    field_simp [ha.ne', hb.ne']
  have hlog := Real.one_sub_inv_le_log_of_pos hquot
  rw [hinv] at hlog
  rw [mertensSecondMainCorrection, if_pos hN]
  change 0 ≤ (Real.log b - Real.log a) - a * (1 / a - 1 / b)
  rw [hlogdiv, hmain]
  linarith

theorem mertensSecondMainCorrection_nonneg (N : ℕ) :
    0 ≤ mertensSecondMainCorrection N := by
  rw [mertensSecondMainCorrection]
  split_ifs with hN
  · simpa [mertensSecondMainCorrection, hN] using
      (mainCorrection_nonneg_of_two_le hN)
  · exact le_rfl

private theorem log_succ_sub_log_le_inv {N : ℕ} (hN : 1 ≤ N) :
    Real.log ((N + 1 : ℕ) : ℝ) - Real.log N ≤ (N : ℝ)⁻¹ := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hlogdiv :
      Real.log ((N + 1 : ℕ) : ℝ) - Real.log N =
        Real.log ((((N + 1 : ℕ) : ℝ) / N)) :=
    (Real.log_div (by positivity) hNpos.ne').symm
  have hratio : (((N + 1 : ℕ) : ℝ) / N) = 1 + (N : ℝ)⁻¹ := by
    norm_num [Nat.cast_add, Nat.cast_one]
    field_simp [hNpos.ne']
  rw [hlogdiv, hratio]
  have h := Real.log_le_sub_one_of_pos
    (add_pos (by norm_num : (0 : ℝ) < 1) (inv_pos.mpr hNpos))
  simpa using h

private theorem mainCorrection_le_inv_sq {N : ℕ} (hN : 3 ≤ N) :
    mertensSecondMainCorrection N ≤ ((N : ℝ) ^ 2)⁻¹ := by
  let a : ℝ := Real.log N
  let b : ℝ := Real.log (N + 1)
  let d : ℝ := b - a
  have ha : 0 < a := log_nat_pos_of_two_le (by omega)
  have hb : 0 < b := by
    simpa [b, Nat.cast_add, Nat.cast_one] using
      (log_nat_pos_of_two_le (by omega : 2 ≤ N + 1))
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Real.log_le_log (Nat.cast_pos.mpr (by omega))
      (by norm_num : (N : ℝ) ≤ (N : ℝ) + 1)
  have hd0 : 0 ≤ d := sub_nonneg.mpr hab
  have hquot : 0 < b / a := div_pos hb ha
  have hlogdiv : Real.log b - Real.log a = Real.log (b / a) :=
    (Real.log_div hb.ne' ha.ne').symm
  have hmain : a * (1 / a - 1 / b) = 1 - a / b := by
    field_simp [ha.ne', hb.ne']
  have hupper := Real.log_le_sub_one_of_pos hquot
  have hfrac : (b / a - 1) - (1 - a / b) = d ^ 2 / (a * b) := by
    dsimp [d]
    field_simp [ha.ne', hb.ne']
  have hcorrFrac : mertensSecondMainCorrection N ≤ d ^ 2 / (a * b) := by
    rw [mertensSecondMainCorrection, if_pos (by omega : 2 ≤ N)]
    change (Real.log b - Real.log a) - a * (1 / a - 1 / b) ≤ d ^ 2 / (a * b)
    rw [hlogdiv, hmain, ← hfrac]
    linarith
  have hdle : d ≤ (N : ℝ)⁻¹ := by
    dsimp [d, a, b]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (log_succ_sub_log_le_inv (show (1 : ℕ) ≤ N by omega))
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  have ha1 : 1 ≤ a := by
    have h3N : (3 : ℝ) ≤ N := Nat.cast_le.mpr hN
    have hlogmono : Real.log 3 ≤ a := by
      dsimp [a]
      exact Real.log_le_log (by norm_num) h3N
    exact hlog3.le.trans hlogmono
  have hb1 : 1 ≤ b := ha1.trans hab
  have hab1 : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha1 hb1
  have hfracLe : d ^ 2 / (a * b) ≤ d ^ 2 := by
    rw [div_le_iff₀ (mul_pos ha hb)]
    nlinarith [sq_nonneg d]
  have hinv0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hsq : d ^ 2 ≤ ((N : ℝ)⁻¹) ^ 2 :=
    (sq_le_sq₀ hd0 hinv0).mpr hdle
  calc
    mertensSecondMainCorrection N ≤ d ^ 2 / (a * b) := hcorrFrac
    _ ≤ d ^ 2 := hfracLe
    _ ≤ ((N : ℝ)⁻¹) ^ 2 := hsq
    _ = ((N : ℝ) ^ 2)⁻¹ := by rw [inv_pow]

/-- The sum-integral discrepancy corrections are absolutely summable. -/
theorem summable_mertensSecondMainCorrection :
    Summable mertensSecondMainCorrection := by
  have hs : Summable (fun N : ℕ => ((N : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  refine hs.of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (mertensSecondMainCorrection_nonneg N)]
  exact mainCorrection_le_inv_sq hN

private theorem Icc_two_pred_eq_Ico_two {N : ℕ} (hN : 2 ≤ N) :
    Icc 2 (N - 1) = Ico 2 N := by
  ext n
  simp [mem_Icc, mem_Ico]
  omega

private theorem sum_mainCorrection_eq {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Icc 2 (N - 1), mertensSecondMainCorrection n =
      Real.log (Real.log N) - Real.log (Real.log 2) -
        ∑ n ∈ Icc 2 (N - 1),
          Real.log n * (1 / Real.log n - 1 / Real.log (n + 1)) := by
  rw [Icc_two_pred_eq_Ico_two hN]
  have hcorr : ∀ n ∈ Ico 2 N,
      mertensSecondMainCorrection n =
        (Real.log (Real.log (n + 1)) - Real.log (Real.log n)) -
          Real.log n * (1 / Real.log n - 1 / Real.log (n + 1)) := by
    intro n hn
    rw [mertensSecondMainCorrection, if_pos (mem_Ico.mp hn).1]
  rw [sum_congr rfl hcorr, sum_sub_distrib]
  have htel0 := sum_Ico_telescope (fun n => Real.log (Real.log n)) hN
  have htel0' :
      ∑ n ∈ Ico 2 N,
          (Real.log (Real.log n) - Real.log (Real.log (n + 1))) =
        Real.log (Real.log 2) - Real.log (Real.log N) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using htel0
  have htel :
      ∑ n ∈ Ico 2 N,
          (Real.log (Real.log (n + 1)) - Real.log (Real.log n)) =
        Real.log (Real.log N) - Real.log (Real.log 2) := by
    calc
      ∑ n ∈ Ico 2 N,
          (Real.log (Real.log (n + 1)) - Real.log (Real.log n)) =
          -∑ n ∈ Ico 2 N,
            (Real.log (Real.log n) - Real.log (Real.log (n + 1))) := by
              rw [← sum_neg_distrib]
              refine sum_congr rfl fun n hn => ?_
              ring
      _ = -(Real.log (Real.log 2) - Real.log (Real.log N)) := by
        rw [htel0']
      _ = Real.log (Real.log N) - Real.log (Real.log 2) := by ring
  rw [htel]

private theorem sum_range_mainCorrection_eq_Icc {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ range N, mertensSecondMainCorrection n =
      ∑ n ∈ Icc 2 (N - 1), mertensSecondMainCorrection n := by
  rw [Icc_two_pred_eq_Ico_two hN]
  have hdecomp : range N = range 2 ∪ Ico 2 N := by
    ext n
    simp [mem_range, mem_Ico]
    omega
  have hdis : Disjoint (range 2) (Ico 2 N) := by
    rw [disjoint_left]
    intro n hn hI
    exact (Nat.not_lt_of_ge (mem_Ico.mp hI).1) (mem_range.mp hn)
  rw [hdecomp, sum_union hdis]
  have hzero : ∑ n ∈ range 2, mertensSecondMainCorrection n = 0 := by
    apply sum_eq_zero
    intro n hn
    have hlt : n < 2 := mem_range.mp hn
    rw [mertensSecondMainCorrection, if_neg (not_le.mpr hlt)]
  rw [hzero, zero_add]

private theorem main_eq_const_sub_sum {N : ℕ} (hN : 2 ≤ N) :
    mertensSecondMain N =
      1 - Real.log (Real.log 2) -
        ∑ n ∈ Icc 2 (N - 1), mertensSecondMainCorrection n := by
  have hsum := sum_mainCorrection_eq hN
  rw [mertensSecondMain]
  linarith

/-- The assumption-free main-term limit in the second Mertens argument. -/
theorem exists_tendsto_mertensSecondMain :
    ∃ b : ℝ, Tendsto mertensSecondMain atTop (nhds b) := by
  refine ⟨1 - Real.log (Real.log 2) - ∑' n : ℕ, mertensSecondMainCorrection n, ?_⟩
  have hsum := summable_mertensSecondMainCorrection.hasSum.tendsto_sum_nat
  have hconst : Tendsto (fun _ : ℕ => 1 - Real.log (Real.log 2)) atTop
      (nhds (1 - Real.log (Real.log 2))) := tendsto_const_nhds
  have hsub := hconst.sub hsum
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  rw [main_eq_const_sub_sum hN, ← sum_range_mainCorrection_eq_Icc hN]

private theorem sum_range_error_eq_Icc {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ range N, mertensSecondErrorTerm n =
      ∑ n ∈ Icc 2 (N - 1), mertensSecondErrorTerm n := by
  rw [Icc_two_pred_eq_Ico_two hN]
  have hdecomp : range N = range 2 ∪ Ico 2 N := by
    ext n
    simp [mem_range, mem_Ico]
    omega
  have hdis : Disjoint (range 2) (Ico 2 N) := by
    rw [disjoint_left]
    intro n hn hI
    exact (Nat.not_lt_of_ge (mem_Ico.mp hI).1) (mem_range.mp hn)
  rw [hdecomp, sum_union hdis]
  have hzero : ∑ n ∈ range 2, mertensSecondErrorTerm n = 0 := by
    apply sum_eq_zero
    intro n hn
    have hlt : n < 2 := mem_range.mp hn
    rw [mertensSecondErrorTerm, mertensInvLogDelta,
      if_neg (not_le.mpr hlt), mul_zero]
  rw [hzero, zero_add]

private theorem mertensSecond_decomposition {N : ℕ} (hN : 2 ≤ N) :
    mertensPrimeReciprocalSum N - Real.log (Real.log N) =
      mertensSecondMain N +
        mertensPrimeWeightedError N / Real.log N +
        ∑ n ∈ Icc 2 (N - 1), mertensSecondErrorTerm n := by
  have hlogN : Real.log (N : ℝ) ≠ 0 := (log_nat_pos_of_two_le hN).ne'
  rw [mertensPrimeReciprocalSum_eq_abel hN, mertensSecondMain]
  have hend :
      mertensPrimeLogOverSum N / Real.log N =
        1 + mertensPrimeWeightedError N / Real.log N := by
    rw [mertensPrimeWeightedError]
    field_simp [hlogN]
    ring
  rw [hend]
  have hterm : ∀ n ∈ Icc 2 (N - 1),
      mertensPrimeLogOverSum n *
          (1 / Real.log n - 1 / Real.log (n + 1)) =
        Real.log n * (1 / Real.log n - 1 / Real.log (n + 1)) +
          mertensSecondErrorTerm n := by
    intro n hn
    have hn2 := (mem_Icc.mp hn).1
    rw [mertensSecondErrorTerm, mertensPrimeWeightedError,
      mertensInvLogDelta, if_pos hn2]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib]
  ring

/-- Existence of the ordinary Mertens-II constant, without PNT or an
assumed Mertens theorem. -/
theorem exists_tendsto_mertensPrimeReciprocalSum_sub_log_log :
    ∃ B : ℝ, Tendsto
      (fun N : ℕ =>
        mertensPrimeReciprocalSum N - Real.log (Real.log N))
      atTop (nhds B) := by
  obtain ⟨b, hb⟩ := exists_tendsto_mertensSecondMain
  let e : ℝ := ∑' n : ℕ, mertensSecondErrorTerm n
  refine ⟨b + 0 + e, ?_⟩
  have herr : Tendsto
      (fun N : ℕ => ∑ n ∈ Icc 2 (N - 1), mertensSecondErrorTerm n)
      atTop (nhds e) := by
    refine tendsto_sum_range_mertensSecondErrorTerm.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact sum_range_error_eq_Icc hN
  have hall := (hb.add tendsto_mertensPrimeWeightedError_div_log).add herr
  refine hall.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (mertensSecond_decomposition hN).symm

end

end PrimeGapNormality.Prime
