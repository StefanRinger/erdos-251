import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite block boundary estimates

Shifting a bounded finite average changes only its two endpoint blocks.
Averaging this estimate over a finite time orbit gives the deterministic
boundary term used in the quantitative orbit-discrepancy argument.
-/

namespace PrimeGapNormality.Prime.CoreFiniteOrbitBoundary

open Finset
open scoped BigOperators

noncomputable section

/-- Average of `f` on the natural block `[a,a+m)`. -/
def blockMean (f : ℕ → ℝ) (a m : ℕ) : ℝ :=
  (∑ n ∈ range m, f (a + n)) / (m : ℝ)

/-- Finite time average beginning at `n`. -/
def timeMean (f : ℕ → ℝ) (T n : ℕ) : ℝ :=
  blockMean f n T

/-- Absolute time-average fluctuation around the target `c`. -/
def timeFluctuation (f : ℕ → ℝ) (c : ℝ) (T n : ℕ) : ℝ :=
  |timeMean f T n - c|

/-- Exact endpoint identity for two shifted sums. -/
theorem shifted_sum_add_endpoints
    (f : ℕ → ℝ) (a m h : ℕ) :
    (∑ n ∈ range m, f (a + h + n)) +
        ∑ n ∈ range h, f (a + n) =
      (∑ n ∈ range m, f (a + n)) +
        ∑ n ∈ range h, f (a + m + n) := by
  have hleft : (∑ n ∈ range (h + m), f (a + n)) =
      (∑ n ∈ range h, f (a + n)) +
        ∑ n ∈ range m, f (a + h + n) := by
    simpa only [Nat.add_assoc] using
      sum_range_add (fun n ↦ f (a + n)) h m
  have hright : (∑ n ∈ range (m + h), f (a + n)) =
      (∑ n ∈ range m, f (a + n)) +
        ∑ n ∈ range h, f (a + m + n) := by
    simpa only [Nat.add_assoc] using
      sum_range_add (fun n ↦ f (a + n)) m h
  rw [Nat.add_comm h m] at hleft
  linarith [hleft, hright]

/-- Difference form of the exact endpoint telescope. -/
theorem shifted_sum_sub_eq_endpoints
    (f : ℕ → ℝ) (a m h : ℕ) :
    (∑ n ∈ range m, f (a + h + n)) -
        ∑ n ∈ range m, f (a + n) =
      (∑ n ∈ range h, f (a + m + n)) -
        ∑ n ∈ range h, f (a + n) := by
  linarith [shifted_sum_add_endpoints f a m h]

private theorem abs_sum_range_le
    {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C) (a h : ℕ) :
    |∑ n ∈ range h, f (a + n)| ≤ (h : ℝ) * C := by
  calc
    |∑ n ∈ range h, f (a + n)| ≤
        ∑ n ∈ range h, |f (a + n)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ range h, C := sum_le_sum fun n hn ↦ hf _
    _ = (h : ℝ) * C := by rw [sum_const, card_range, nsmul_eq_mul]

/-- A shift by `h` changes an `m`-block average by at most `2Ch/m`. -/
theorem abs_blockMean_shift_sub_le
    {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C) (a h : ℕ) {m : ℕ} (hm : 0 < m) :
    |blockMean f (a + h) m - blockMean f a m| ≤
      2 * C * (h : ℝ) / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have htail := abs_sum_range_le hf (a + m) h
  have hhead := abs_sum_range_le hf a h
  have hdiff : |(∑ n ∈ range m, f (a + h + n)) -
      ∑ n ∈ range m, f (a + n)| ≤ 2 * C * (h : ℝ) := by
    rw [shifted_sum_sub_eq_endpoints]
    calc
      |(∑ n ∈ range h, f (a + m + n)) -
          ∑ n ∈ range h, f (a + n)| ≤
          |∑ n ∈ range h, f (a + m + n)| +
            |∑ n ∈ range h, f (a + n)| := abs_sub _ _
      _ ≤ (h : ℝ) * C + (h : ℝ) * C := _root_.add_le_add htail hhead
      _ = 2 * C * (h : ℝ) := by ring
  unfold blockMean
  rw [← sub_div, abs_div, abs_of_pos hmR]
  exact div_le_div_of_nonneg_right hdiff hmR.le

private theorem abs_blockMean_sub_const_le
    (g : ℕ → ℝ) (a : ℕ) {m : ℕ} (hm : 0 < m) (c : ℝ) :
    |blockMean g a m - c| ≤ blockMean (fun n ↦ |g n - c|) a m := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have heq : blockMean g a m - c =
      (∑ n ∈ range m, (g (a + n) - c)) / (m : ℝ) := by
    unfold blockMean
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp [hmR.ne']
  rw [heq, abs_div, abs_of_pos hmR]
  unfold blockMean
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hmR.le

private theorem timeMean_blockMean_swap
    (f : ℕ → ℝ) (a : ℕ) {T m : ℕ} (hT : 0 < T) (hm : 0 < m) :
    blockMean (timeMean f T) a m =
      blockMean (fun h ↦ blockMean f (a + h) m) 0 T := by
  unfold timeMean blockMean
  simp_rw [div_eq_mul_inv, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro h hh
  apply sum_congr rfl
  intro n hn
  simp only [Nat.zero_add]
  rw [show a + n + h = a + h + n by omega]
  ring

private theorem abs_timeMeanBlock_sub_le
    {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C) (a : ℕ) {T m : ℕ}
    (hT : 0 < T) (hm : 0 < m) :
    |blockMean (timeMean f T) a m - blockMean f a m| ≤
      2 * C * (T : ℝ) / (m : ℝ) := by
  rw [timeMean_blockMean_swap f a hT hm]
  have hmean :
      |blockMean (fun h ↦ blockMean f (a + h) m) 0 T - blockMean f a m| ≤
        blockMean (fun h ↦ |blockMean f (a + h) m - blockMean f a m|) 0 T := by
    simpa only [Nat.zero_add] using
      (abs_blockMean_sub_const_le
        (fun h ↦ blockMean f (a + h) m) 0 hT (blockMean f a m))
  have hpoint : ∀ h ∈ range T,
      |blockMean f (a + h) m - blockMean f a m| ≤
        2 * C * (T : ℝ) / (m : ℝ) := by
    intro h hh
    have hshift := abs_blockMean_shift_sub_le hC hf a h hm
    have hhT : (h : ℝ) ≤ T := Nat.cast_le.mpr (mem_range.mp hh).le
    have hscale : 2 * C * (h : ℝ) ≤ 2 * C * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hhT (mul_nonneg (by norm_num) hC)
    exact hshift.trans (div_le_div_of_nonneg_right (by
      nlinarith) (Nat.cast_nonneg m))
  have havg : blockMean
      (fun h ↦ |blockMean f (a + h) m - blockMean f a m|) 0 T ≤
      2 * C * (T : ℝ) / (m : ℝ) := by
    change (∑ h ∈ range T, |blockMean f (a + (0 + h)) m - blockMean f a m|) /
      (T : ℝ) ≤ 2 * C * (T : ℝ) / (m : ℝ)
    simp only [Nat.zero_add]
    have hsum := sum_le_sum hpoint
    rw [sum_const, card_range, nsmul_eq_mul] at hsum
    have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
    apply (div_le_iff₀ hTR).2
    calc
      (∑ h ∈ range T, |blockMean f (a + h) m - blockMean f a m|) ≤
          (T : ℝ) * (2 * C * (T : ℝ) / (m : ℝ)) := hsum
      _ = (2 * C * (T : ℝ) / (m : ℝ)) * (T : ℝ) := mul_comm _ _
  exact hmean.trans havg

/-- Finite time-fluctuation domination with the genuine endpoint cost. -/
theorem abs_blockMean_sub_le_timeFluctuation
    {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C) (a : ℕ) {T m : ℕ}
    (hT : 0 < T) (hm : 0 < m) (c : ℝ) :
    |blockMean f a m - c| ≤
      blockMean (timeFluctuation f c T) a m +
        2 * C * (T : ℝ) / (m : ℝ) := by
  have hboundary := abs_timeMeanBlock_sub_le hC hf a hT hm
  have hboundary' :
      |blockMean f a m - blockMean (timeMean f T) a m| ≤
        2 * C * (T : ℝ) / (m : ℝ) := by
    simpa only [abs_sub_comm] using hboundary
  have hjensen := abs_blockMean_sub_const_le (timeMean f T) a hm c
  have htri := abs_add_le
    (blockMean f a m - blockMean (timeMean f T) a m)
    (blockMean (timeMean f T) a m - c)
  rw [sub_add_sub_cancel] at htri
  calc
    |blockMean f a m - c| ≤
        |blockMean f a m - blockMean (timeMean f T) a m| +
          |blockMean (timeMean f T) a m - c| := htri
    _ ≤ 2 * C * (T : ℝ) / (m : ℝ) +
        blockMean (fun n ↦ |timeMean f T n - c|) a m :=
      _root_.add_le_add hboundary' hjensen
    _ = blockMean (timeFluctuation f c T) a m +
        2 * C * (T : ℝ) / (m : ℝ) := by
      unfold timeFluctuation
      ring

end

end PrimeGapNormality.Prime.CoreFiniteOrbitBoundary
