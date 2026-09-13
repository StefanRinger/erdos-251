import PrimeGapNormality.Prime.StretchedClock.Definitions
import PrimeGapNormality.Prime.PosMassScale
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Actual tails and every base-B orbit position

The exact prefix identity uses an integer correction. The block sum identity
covers all positions below `position B N`, not just insertion endpoints.
-/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset Filter
open scoped Topology
noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

def actualTail (B n : ℕ) : ℝ :=
  ∑' j : ℕ, (nthPrime (n + j) : ℝ) /
    (B : ℝ) ^ (position B (n + j + 1) - position B n)

def prefixInt (B n : ℕ) : ℤ :=
  ∑ i ∈ range n, (nthPrime i : ℤ) *
    (B : ℤ) ^ (position B n - position B (i + 1))

def orbit (B m : ℕ) : Circle := ((B : ℝ) ^ m * value B : ℝ)

def frozenTail (q n : ℕ) : ℝ :=
  posMass (q : ℝ) (fun i => (nthPrime i : ℝ)) n

def frozenGapTail (q n : ℕ) : ℝ :=
  gapTail (q : ℝ) (fun i => (primeGap i : ℝ)) n

theorem value_summable {B : ℕ} (hB : 2 ≤ B) :
    Summable (fun n : ℕ => (nthPrime n : ℝ) / (B : ℝ) ^ position B (n + 1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (base_pos hB).le _))
    (fun n => ?_) (primePosSeries_summable hB)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos (base_pos hB) _)
    (pow_le_pow_right₀ (one_lt_base hB).le (le_position hB (n + 1)))

theorem scaled_tail_term {B : ℕ} (hB : 2 ≤ B) (n j : ℕ) :
    (B : ℝ) ^ position B n *
        ((nthPrime (n + j) : ℝ) / (B : ℝ) ^ position B (n + j + 1)) =
      (nthPrime (n + j) : ℝ) /
        (B : ℝ) ^ (position B (n + j + 1) - position B n) := by
  have hle := position_mono hB (show n ≤ n + j + 1 by omega)
  have he : position B (n + j + 1) =
      position B n + (position B (n + j + 1) - position B n) := by omega
  have hp : (B : ℝ) ^ position B (n + j + 1) =
      (B : ℝ) ^ position B n *
        (B : ℝ) ^ (position B (n + j + 1) - position B n) := by
    conv_lhs => rw [he, pow_add]
  rw [hp]
  field_simp [(base_pos hB).ne'] <;> ring

theorem actualTail_summable {B : ℕ} (hB : 2 ≤ B) (n : ℕ) :
    Summable (fun j : ℕ => (nthPrime (n + j) : ℝ) /
      (B : ℝ) ^ (position B (n + j + 1) - position B n)) := by
  have hs := (summable_nat_add_iff
    (f := fun i : ℕ => (nthPrime i : ℝ) / (B : ℝ) ^ position B (i + 1)) n).mpr
      (value_summable hB)
  have hm := hs.mul_left ((B : ℝ) ^ position B n)
  apply hm.congr
  intro j
  simpa only [Nat.add_comm j n] using scaled_tail_term hB n j

theorem actualTail_nonneg {B : ℕ} (hB : 2 ≤ B) (n : ℕ) : 0 ≤ actualTail B n :=
  tsum_nonneg fun j =>
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (base_pos hB).le _)

theorem scaled_prefix_term {B n i : ℕ} (hB : 2 ≤ B) (hi : i < n) :
    (B : ℝ) ^ position B n * ((nthPrime i : ℝ) / (B : ℝ) ^ position B (i + 1)) =
      (nthPrime i : ℝ) * (B : ℝ) ^ (position B n - position B (i + 1)) := by
  have hle := position_mono hB (show i + 1 ≤ n by omega)
  have he : position B n = position B (i + 1) +
      (position B n - position B (i + 1)) := by omega
  conv_lhs => rw [he, pow_add]
  field_simp [(base_pos hB).ne'] <;> ring

theorem scaled_value_eq_prefixInt_add_actualTail {B : ℕ} (hB : 2 ≤ B) (n : ℕ) :
    (B : ℝ) ^ position B n * value B = (prefixInt B n : ℝ) + actualTail B n := by
  have hs := (value_summable hB).sum_add_tsum_nat_add n
  change (∑ i ∈ range n, (nthPrime i : ℝ) / (B : ℝ) ^ position B (i + 1)) +
    (∑' j : ℕ, (nthPrime (j + n) : ℝ) / (B : ℝ) ^ position B (j + n + 1)) = value B at hs
  rw [← hs, mul_add, mul_sum, ← tsum_mul_left]
  congr 1
  · simp only [prefixInt, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_pow]
    apply sum_congr rfl
    intro i hi
    exact scaled_prefix_term hB (mem_range.mp hi)
  · unfold actualTail
    apply tsum_congr
    intro j
    simpa only [Nat.add_comm j n] using scaled_tail_term hB n j

private theorem circle_intCast_eq_zero (z : ℤ) : ((z : ℝ) : Circle) = 0 := by
  have h := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := z) (x := (1 : ℝ))
  simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using h

/-- Literal equality for every position inside every insertion block. -/
theorem orbit_position_add {B : ℕ} (hB : 2 ≤ B) (n r : ℕ) :
    orbit B (position B n + r) = ((B : ℝ) ^ r * actualTail B n : ℝ) := by
  have hreal : (B : ℝ) ^ (position B n + r) * value B =
      (((B : ℤ) ^ r * prefixInt B n : ℤ) : ℝ) + (B : ℝ) ^ r * actualTail B n := by
    rw [pow_add]
    have hh := scaled_value_eq_prefixInt_add_actualTail hB n
    push_cast
    calc
      (B : ℝ) ^ position B n * (B : ℝ) ^ r * value B =
          (B : ℝ) ^ r * ((B : ℝ) ^ position B n * value B) := by ring
      _ = (B : ℝ) ^ r * ((prefixInt B n : ℝ) + actualTail B n) := by rw [hh]
      _ = _ := by ring
  unfold orbit
  rw [hreal, AddCircle.coe_add, circle_intCast_eq_zero, zero_add]

/-- Purely finite enumeration of all digit positions. -/
theorem sum_all_positions {M : Type*} [AddCommMonoid M]
    (B N : ℕ) (f : ℕ → M) :
    (∑ j ∈ range (position B N), f j) =
      ∑ n ∈ range N, ∑ r ∈ range (step B n), f (position B n + r) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [position_succ, sum_range_add, ih, sum_range_succ]

theorem sum_orbit_positions {M : Type*} [AddCommMonoid M]
    {B : ℕ} (hB : 2 ≤ B) (N : ℕ) (f : Circle → M) :
    (∑ j ∈ range (position B N), f (orbit B j)) =
      ∑ n ∈ range N, ∑ r ∈ range (step B n),
        f (((B : ℝ) ^ r * actualTail B n : ℝ) : Circle) := by
  rw [sum_all_positions]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro r hr
  rw [orbit_position_add hB]

theorem block_position_lt {B N n r : ℕ} (hB : 2 ≤ B)
    (hn : n < N) (hr : r < step B n) : position B n + r < position B N := by
  have hp : position B n + r < position B (n + 1) := by
    rw [position_succ]
    omega
  exact hp.trans_le (position_mono hB (show n + 1 ≤ N by omega))

theorem exists_position_block {B : ℕ} (hB : 2 ≤ B) (N : ℕ)
    {j : ℕ} (hj : j < position B N) :
    ∃ n < N, ∃ r < step B n, position B n + r = j := by
  induction N with
  | zero => simp at hj
  | succ N ih =>
      by_cases hjN : j < position B N
      · obtain ⟨n, hn, r, hr, he⟩ := ih hjN
        exact ⟨n, by omega, r, hr, he⟩
      · have hle : position B N ≤ j := by omega
        refine ⟨N, by omega, j - position B N, ?_, ?_⟩
        · rw [position_succ] at hj
          omega
        · omega

theorem position_block_unique {B n m r s : ℕ} (hB : 2 ≤ B)
    (hr : r < step B n) (hs : s < step B m)
    (he : position B n + r = position B m + s) : n = m ∧ r = s := by
  have hnm : n = m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := block_position_lt hB hlt hr
      omega
    · have h1 := block_position_lt hB hlt hs
      omega
  subst m
  exact ⟨rfl, by omega⟩

theorem frozenTail_eq_abel {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    frozenTail q n = ((nthPrime n : ℝ) + frozenGapTail q n) / ((q : ℝ) - 1) :=
  posMass_nthPrime_eq (by exact_mod_cast (show 1 < q by omega)) n

end
end PrimeGapNormality.Prime.StretchedClock
