import PrimeGapNormality.Prime.PrimeSeries
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The literal logarithmically stretched prime clock

The prime enumeration is zero based: `nthPrime 0 = 2`. Consequently the
paper's `ceil(log_B(log(n+3)))`, for `n >= 1`, becomes the expression with
`n+4` below. Every prime coefficient is retained.
-/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset Filter
open scoped Topology

noncomputable section

def realStep (B n : ℕ) : ℝ :=
  Real.log (Real.log ((n : ℝ) + 4)) / Real.log (B : ℝ)

def step (B n : ℕ) : ℕ := ⌈realStep B n⌉₊

def position (B n : ℕ) : ℕ := ∑ i ∈ range n, step B i

def localBase (B n : ℕ) : ℕ := B ^ step B n

def value (B : ℕ) : ℝ :=
  ∑' n : ℕ, (nthPrime n : ℝ) / (B : ℝ) ^ position B (n + 1)

theorem base_pos {B : ℕ} (hB : 2 ≤ B) : (0 : ℝ) < B := by
  exact_mod_cast (show 0 < B by omega)

theorem one_lt_base {B : ℕ} (hB : 2 ≤ B) : (1 : ℝ) < B := by
  exact_mod_cast (show 1 < B by omega)

theorem log_base_pos {B : ℕ} (hB : 2 ≤ B) : 0 < Real.log (B : ℝ) :=
  Real.log_pos (one_lt_base hB)

theorem one_lt_log_add_four (n : ℕ) : 1 < Real.log ((n : ℝ) + 4) := by
  have hthree : (3 : ℝ) < (n : ℝ) + 4 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have h := Real.log_lt_log (Real.exp_pos 1)
    (Real.exp_one_lt_three.trans hthree)
  simpa only [Real.log_exp] using h

theorem realStep_pos {B : ℕ} (hB : 2 ≤ B) (n : ℕ) : 0 < realStep B n :=
  div_pos (Real.log_pos (one_lt_log_add_four n)) (log_base_pos hB)

theorem one_le_step {B : ℕ} (hB : 2 ≤ B) (n : ℕ) : 1 ≤ step B n := by
  exact Nat.one_le_ceil_iff.mpr (realStep_pos hB n)

theorem step_pos {B : ℕ} (hB : 2 ≤ B) (n : ℕ) : 0 < step B n :=
  one_le_step hB n

theorem realStep_mono {B : ℕ} (hB : 2 ≤ B) : Monotone (realStep B) := by
  intro m n hmn
  have hcast : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  have hinner : Real.log ((m : ℝ) + 4) ≤ Real.log ((n : ℝ) + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (zero_lt_one.trans (one_lt_log_add_four m)) hinner)
    (log_base_pos hB).le

theorem step_mono {B : ℕ} (hB : 2 ≤ B) : Monotone (step B) :=
  Nat.ceil_mono.comp (realStep_mono hB)

theorem realStep_le_step (B n : ℕ) : realStep B n ≤ (step B n : ℝ) :=
  Nat.le_ceil _

theorem step_lt_realStep_add_one {B : ℕ} (hB : 2 ≤ B) (n : ℕ) :
    (step B n : ℝ) < realStep B n + 1 :=
  Nat.ceil_lt_add_one (realStep_pos hB n).le

@[simp] theorem position_zero (B : ℕ) : position B 0 = 0 := by
  simp [position]

@[simp] theorem position_succ (B n : ℕ) :
    position B (n + 1) = position B n + step B n := by
  simp [position, sum_range_succ]

theorem position_add (B m n : ℕ) :
    position B (m + n) = position B m + ∑ i ∈ range n, step B (m + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show m + (n + 1) = (m + n) + 1 by omega, position_succ, ih,
        sum_range_succ]
      omega

theorem position_strictMono {B : ℕ} (hB : 2 ≤ B) : StrictMono (position B) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [position_succ]
  exact Nat.lt_add_of_pos_right (step_pos hB n)

theorem position_mono {B : ℕ} (hB : 2 ≤ B) : Monotone (position B) :=
  (position_strictMono hB).monotone

theorem le_position {B : ℕ} (hB : 2 ≤ B) (n : ℕ) : n ≤ position B n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [position_succ]
      have := one_le_step hB n
      omega

theorem position_le_mul_step {B : ℕ} (hB : 2 ≤ B) (n : ℕ) :
    position B n ≤ n * step B n := by
  calc
    position B n ≤ ∑ _i ∈ range n, step B n :=
      sum_le_sum fun i hi => step_mono hB (mem_range.mp hi).le
    _ = n * step B n := by simp

theorem position_le_position_add {B : ℕ} (hB : 2 ≤ B) (m n : ℕ) :
    position B m + n ≤ position B (m + n) := by
  rw [position_add]
  have hsum : (∑ _i ∈ range n, 1) ≤ ∑ i ∈ range n, step B (m + i) :=
    sum_le_sum fun i _ => one_le_step hB (m + i)
  simpa using Nat.add_le_add_left hsum (position B m)

theorem localBase_two_le {B : ℕ} (hB : 2 ≤ B) (n : ℕ) :
    2 ≤ localBase B n := by
  have hpow : B ≤ B ^ step B n :=
    le_self_pow₀ (by omega : 1 ≤ B) (Nat.ne_of_gt (step_pos hB n))
  exact hB.trans hpow

theorem localBase_mono {B : ℕ} (hB : 2 ≤ B) : Monotone (localBase B) := by
  intro m n hmn
  exact pow_le_pow_right₀ (by omega : 1 ≤ B) (step_mono hB hmn)

theorem position_tendsto_atTop {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (position B) atTop atTop :=
  tendsto_atTop_mono (le_position hB) tendsto_id

end
end PrimeGapNormality.Prime.StretchedClock
