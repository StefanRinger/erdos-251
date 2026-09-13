import PrimeGapNormality.Prime.PrimeIndex
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The actual prime-counting sister series

The summand is the reciprocal of `2 ^ Nat.primeCounting m`. In particular,
the left side is defined independently of the position and gap series.
The finite prime blocks prove summability, then a cofinal sequence of
partial sums gives the infinite identity. Lean `nthPrime n` is paper
`p_(n+1)`, so a prime block has exponent `n+1`. The positive-integer series
retains the term at `m=1` and removes only the auxiliary term at `m=0`.

Source: `prime_gap_normality.tex`, introduction following `eq:abelbasic`,
SHA256 `75703db38e707edf56a5282e4d86a94bcb44dcf080b7a52cf00006c49aec5115`.
-/

namespace PrimeGapNormality.Prime

open Finset Filter
open scoped Topology

set_option maxHeartbeats 800000

/-- The actual summand, including the auxiliary index zero. -/
noncomputable def primeCountingTerm (m : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ Nat.primeCounting m

/-- The actual series over positive integers, written with index `m+1`. -/
noncomputable def primeCountingSeries : ℝ :=
  ∑' m : ℕ, primeCountingTerm (m + 1)

theorem primeCountingTerm_nonneg (m : ℕ) : 0 ≤ primeCountingTerm m := by
  unfold primeCountingTerm
  positivity

@[simp] theorem primeCountingTerm_zero : primeCountingTerm 0 = 1 := by
  simp [primeCountingTerm, Nat.primeCounting_zero]

@[simp] theorem primeCountingTerm_one : primeCountingTerm 1 = 1 := by
  simp [primeCountingTerm, Nat.primeCounting_one]

/-- Prime counting is constant on the entire half-open consecutive-prime block. -/
theorem primeCounting_eq_on_primeBlock {n m : ℕ}
    (hl : nthPrime n ≤ m) (hu : m < nthPrime (n + 1)) :
    Nat.primeCounting m = n + 1 := by
  have hlo := (nthPrime_le_iff_lt_primeCounting n m).mp hl
  have hhi : ¬ n + 1 < Nat.primeCounting m := by
    intro h
    exact (not_le_of_gt hu) ((nthPrime_le_iff_lt_primeCounting (n + 1) m).mpr h)
  omega

/-- Finite block count: its cardinality is the actual consecutive prime gap. -/
theorem sum_primeCountingTerm_primeBlock (n : ℕ) :
    ∑ m ∈ Ico (nthPrime n) (nthPrime (n + 1)), primeCountingTerm m =
      (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1) := by
  calc
    _ = ∑ _m ∈ Ico (nthPrime n) (nthPrime (n + 1)),
        (1 / (2 : ℝ) ^ (n + 1)) := by
      apply sum_congr rfl
      intro m hm
      rw [primeCountingTerm, primeCounting_eq_on_primeBlock
        (mem_Ico.mp hm).1 (mem_Ico.mp hm).2]
    _ = (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1) := by
      simp [primeGap, nsmul_eq_mul, div_eq_mul_inv]

/-- Auxiliary finite identity includes both `m=0` and `m=1`. -/
theorem sum_primeCountingTerm_range_nthPrime (N : ℕ) :
    ∑ m ∈ range (nthPrime N), primeCountingTerm m =
      2 + ∑ n ∈ range N, (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1) := by
  induction N with
  | zero => norm_num [nthPrime_zero, sum_range_succ]
  | succ N ih =>
      have hle := nthPrime_mono (Nat.le_succ N)
      rw [← sum_range_add_sum_Ico primeCountingTerm hle,
        sum_primeCountingTerm_primeBlock, ih, sum_range_succ]
      ring

/-- The paper's finite positive-integer identity, stopping just before `p_(N+1)`. -/
theorem sum_primeCountingTerm_Ico_nthPrime (N : ℕ) :
    ∑ m ∈ Ico 1 (nthPrime N), primeCountingTerm m =
      1 + ∑ n ∈ range N, (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1) := by
  rw [sum_Ico_eq_sub primeCountingTerm (by have := nthPrime_two_le N; omega),
    sum_primeCountingTerm_range_nthPrime]
  simp only [sum_range_one, primeCountingTerm_zero]
  ring

private theorem primeGap_linear_summable :
    Summable (fun n : ℕ => (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  simpa only [pow_one, Nat.cast_ofNat] using
    (primeGapPowerSeries_summable (B := 2) (d := 1) (by decide))

/-- Genuine summability follows by bounding every partial sum by a complete
prime-block partial sum and the already summable actual gap series. -/
theorem primeCountingTerm_summable : Summable primeCountingTerm := by
  apply summable_of_sum_range_le primeCountingTerm_nonneg
    (c := 2 + ∑' n : ℕ, (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1))
  intro N
  calc
    ∑ m ∈ range N, primeCountingTerm m
        ≤ ∑ m ∈ range (nthPrime N), primeCountingTerm m := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact range_mono (by have := nthPrime_ge_add_two N; omega)
      · intro m _ _
        exact primeCountingTerm_nonneg m
    _ = 2 + ∑ n ∈ range N, (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1) :=
      sum_primeCountingTerm_range_nthPrime N
    _ ≤ 2 + ∑' n : ℕ, (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1) := by
      exact add_le_add (le_refl (2 : ℝ))
        (primeGap_linear_summable.sum_le_tsum _ (fun _ _ => by positivity))

/-- Summability of the positive-integer series in its literal reciprocal form. -/
theorem primeCountingSeries_summable :
    Summable (fun m : ℕ => 1 / (2 : ℝ) ^ Nat.primeCounting (m + 1)) := by
  exact (summable_nat_add_iff 1).2 primeCountingTerm_summable

/-- Cofinal partial sums through the actual primes justify the infinite passage. -/
theorem tsum_primeCountingTerm_eq_gap :
    (∑' m : ℕ, primeCountingTerm m) =
      2 + ∑' n : ℕ, (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1) := by
  have hleft := primeCountingTerm_summable.hasSum.tendsto_sum_nat.comp
    nthPrime_strictMono.tendsto_atTop
  have hright := (tendsto_const_nhds (x := (2 : ℝ))).add
    primeGap_linear_summable.hasSum.tendsto_sum_nat
  have heq :
      Tendsto (fun N => ∑ m ∈ range (nthPrime N), primeCountingTerm m)
        atTop (𝓝 (2 + ∑' n : ℕ, (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1))) :=
    hright.congr fun N => (sum_primeCountingTerm_range_nthPrime N).symm
  exact tendsto_nhds_unique hleft heq

/-- The initial positive integer contributes one to the gap-series identity. -/
theorem primeCountingSeries_eq_one_add_gap :
    primeCountingSeries = 1 + primeGapPowerSeries 2 1 := by
  have hshift := primeCountingTerm_summable.sum_add_tsum_nat_add 1
  have hfull := tsum_primeCountingTerm_eq_gap
  simp only [sum_range_one, primeCountingTerm_zero] at hshift
  change 1 + primeCountingSeries = ∑' m : ℕ, primeCountingTerm m at hshift
  have hgap : (∑' n : ℕ, (primeGap n : ℝ) / (2 : ℝ) ^ (n + 1)) =
      primeGapPowerSeries 2 1 := by simp only [primeGapPowerSeries, pow_one, Nat.cast_ofNat]
  rw [hgap] at hfull
  linarith

/-- The prime-counting sister identity, using the existing infinite Abel theorem. -/
theorem primeCountingSeries_eq_primePosSeries_sub_one :
    primeCountingSeries = primePosSeries 2 - 1 := by
  rw [primeCountingSeries_eq_one_add_gap,
    primeGapPowerSeries_one_eq (by decide : 2 ≤ 2), nthPrime_zero]
  norm_num <;> ring

/-- Literal sum over positive integers, with no artificial hypotheses. -/
theorem tsum_primeCounting_recip_eq_primePosSeries_sub_one :
    (∑' m : ℕ, 1 / (2 : ℝ) ^ Nat.primeCounting (m + 1)) =
      primePosSeries 2 - 1 :=
  primeCountingSeries_eq_primePosSeries_sub_one

/-- The paper's negative-exponent notation is also genuinely summable. -/
theorem primeCountingSeries_zpow_summable :
    Summable (fun m : ℕ => (2 : ℝ) ^ (-(Nat.primeCounting (m + 1) : ℤ))) := by
  simpa only [zpow_neg, zpow_natCast, one_div] using primeCountingSeries_summable

/-- Exact paper notation for the sister identity. -/
theorem tsum_primeCounting_zpow_eq_primePosSeries_sub_one :
    (∑' m : ℕ, (2 : ℝ) ^ (-(Nat.primeCounting (m + 1) : ℤ))) =
      primePosSeries 2 - 1 := by
  simpa only [zpow_neg, zpow_natCast, one_div] using
    tsum_primeCounting_recip_eq_primePosSeries_sub_one

/-- The explicitly stated fractional-part consequence in the introduction. -/
theorem primeCountingSeries_fract_eq :
    Int.fract primeCountingSeries = Int.fract (primePosSeries 2) := by
  rw [primeCountingSeries_eq_primePosSeries_sub_one, Int.fract_sub_one]

end PrimeGapNormality.Prime
