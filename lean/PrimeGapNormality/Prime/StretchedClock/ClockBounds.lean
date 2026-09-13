import PrimeGapNormality.Prime.StretchedClock.Definitions
import Mathlib.Data.Nat.Sqrt

/-!
# Bounds for the literal stretched clock

The square-root window has at most two clock labels. All assertions refer
to the original clock, including its initial values.
-/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset Filter
open scoped Topology
noncomputable section

theorem log_localBase (B n : ℕ) :
    Real.log (localBase B n : ℝ) = (step B n : ℝ) * Real.log (B : ℝ) := by
  simp only [localBase, Nat.cast_pow, Real.log_pow]

theorem log_add_four_le_localBase {B : ℕ} (hB : 2 ≤ B) (n : ℕ) :
    Real.log ((n : ℝ) + 4) ≤ (localBase B n : ℝ) := by
  have hq : (0 : ℝ) < localBase B n := by
    exact_mod_cast (show 0 < localBase B n from (by have := localBase_two_le hB n; omega))
  apply (Real.log_le_log_iff (zero_lt_one.trans (one_lt_log_add_four n)) hq).mp
  rw [log_localBase]
  exact (div_le_iff₀ (log_base_pos hB)).mp (realStep_le_step B n)

theorem localBase_lt_base_mul_log_add_four {B : ℕ} (hB : 2 ≤ B) (n : ℕ) :
    (localBase B n : ℝ) < (B : ℝ) * Real.log ((n : ℝ) + 4) := by
  have hq : (0 : ℝ) < localBase B n := by
    exact_mod_cast (show 0 < localBase B n from (by have := localBase_two_le hB n; omega))
  have hlog : 0 < Real.log ((n : ℝ) + 4) :=
    zero_lt_one.trans (one_lt_log_add_four n)
  apply (Real.log_lt_log_iff hq (mul_pos (base_pos hB) hlog)).mp
  rw [log_localBase, Real.log_mul (base_pos hB).ne' hlog.ne']
  have h := mul_lt_mul_of_pos_right (step_lt_realStep_add_one hB n) (log_base_pos hB)
  have hcancel : realStep B n * Real.log (B : ℝ) =
      Real.log (Real.log ((n : ℝ) + 4)) := by
    unfold realStep
    exact div_mul_cancel₀ _ (log_base_pos hB).ne'
  rw [add_mul, hcancel, one_mul] at h
  linarith

theorem realStep_tendsto_atTop {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (realStep B) atTop atTop := by
  change Tendsto (fun n : ℕ => Real.log (Real.log ((n : ℝ) + 4)) /
    Real.log (B : ℝ)) atTop atTop
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop :=
    tendsto_atTop_mono (fun _n => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 4))
      tendsto_natCast_atTop_atTop
  have hh := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hn)
  have hm := Filter.Tendsto.const_mul_atTop (one_div_pos.mpr (log_base_pos hB)) hh
  simpa only [realStep, Function.comp_def, div_eq_mul_inv, one_mul, mul_comm] using hm

theorem step_tendsto_atTop {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (step B) atTop atTop :=
  tendsto_nat_ceil_atTop.comp (realStep_tendsto_atTop hB)

theorem step_div_realStep_tendsto_one {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun n => (step B n : ℝ) / realStep B n) atTop (𝓝 1) :=
  tendsto_nat_ceil_div_atTop.comp (realStep_tendsto_atTop hB)

/-- The elementary index inequality that makes the clock range shorter
than one real unit on the square-root window. -/
theorem add_four_lt_sqrt_add_four_sq (N : ℕ) :
    (N : ℝ) + 4 < ((Nat.sqrt N : ℝ) + 4) ^ 2 := by
  have hs : (0 : ℝ) ≤ Nat.sqrt N := Nat.cast_nonneg _
  have hN : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' N
  nlinarith

theorem realStep_lt_sqrt_realStep_add_one {B : ℕ} (hB : 2 ≤ B) (N : ℕ) :
    realStep B N < realStep B (Nat.sqrt N) + 1 := by
  let t : ℝ := (Nat.sqrt N : ℝ) + 4
  have ht : 0 < t := by dsimp [t]; positivity
  have hL : 0 < Real.log t := by
    simpa only [t] using zero_lt_one.trans (one_lt_log_add_four (Nat.sqrt N))
  have hfirst : Real.log ((N : ℝ) + 4) < 2 * Real.log t := by
    have hh := Real.log_lt_log (by positivity : (0 : ℝ) < (N : ℝ) + 4)
      (add_four_lt_sqrt_add_four_sq N)
    simpa only [t, Real.log_pow, Nat.cast_ofNat] using hh
  have hsecond := Real.log_lt_log
    (zero_lt_one.trans (one_lt_log_add_four N)) hfirst
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hL.ne'] at hsecond
  have hBLog : Real.log 2 ≤ Real.log (B : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hB)
  have hh : Real.log (Real.log ((N : ℝ) + 4)) <
      Real.log (Real.log t) + Real.log (B : ℝ) := by linarith
  apply (div_lt_iff₀ (log_base_pos hB)).mpr
  have hcancel : (realStep B (Nat.sqrt N) + 1) * Real.log (B : ℝ) =
      Real.log (Real.log t) + Real.log (B : ℝ) := by
    unfold realStep
    dsimp only [t]
    field_simp [(log_base_pos hB).ne']
  simpa only [hcancel] using hh

theorem step_le_sqrt_step_add_one {B : ℕ} (hB : 2 ≤ B) (N : ℕ) :
    step B N ≤ step B (Nat.sqrt N) + 1 := by
  have h := Nat.ceil_mono (realStep_lt_sqrt_realStep_add_one hB N).le
  simpa only [Nat.ceil_add_one (realStep_pos hB (Nat.sqrt N)).le, step] using h

/-- No more than two values occur, with the literal lower label exposed. -/
theorem step_eq_or_eq_succ_on_sqrt_window {B N n : ℕ} (hB : 2 ≤ B)
    (hnlo : Nat.sqrt N ≤ n) (hnhi : n ≤ N) :
    step B n = step B (Nat.sqrt N) ∨ step B n = step B (Nat.sqrt N) + 1 := by
  have hlo := step_mono hB hnlo
  have hhi := (step_mono hB hnhi).trans (step_le_sqrt_step_add_one hB N)
  omega

/-- Distinct strict changes cannot both lie in this window. -/
theorem clock_changes_subsingleton {B N : ℕ} (hB : 2 ≤ B) :
    {n : ℕ | Nat.sqrt N ≤ n ∧ n < N ∧ step B n < step B (n + 1)}.Subsingleton := by
  intro m hm n hn
  change Nat.sqrt N ≤ m ∧ m < N ∧ step B m < step B (m + 1) at hm
  change Nat.sqrt N ≤ n ∧ n < N ∧ step B n < step B (n + 1) at hn
  rcases hm with ⟨hmlo, hmhi, hmstep⟩
  rcases hn with ⟨hnlo, hnhi, hnstep⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hmn | hnm
  · have hmid := step_mono hB (show m + 1 ≤ n by omega)
    have hlo := step_mono hB hmlo
    have hhi := (step_mono hB (show n + 1 ≤ N by omega)).trans
      (step_le_sqrt_step_add_one hB N)
    omega
  · have hmid := step_mono hB (show n + 1 ≤ m by omega)
    have hlo := step_mono hB hnlo
    have hhi := (step_mono hB (show m + 1 ≤ N by omega)).trans
      (step_le_sqrt_step_add_one hB N)
    omega

theorem position_lower_from_index {B : ℕ} (hB : 2 ≤ B) {m N : ℕ} (hm : m ≤ N) :
    (N - m) * step B m ≤ position B N := by
  have hh : (N - m) * step B m ≤ ∑ i ∈ range (N - m), step B (m + i) := by
    calc
      (N - m) * step B m = ∑ _i ∈ range (N - m), step B m := by simp
      _ ≤ ∑ i ∈ range (N - m), step B (m + i) :=
        sum_le_sum fun i _ => step_mono hB (Nat.le_add_right _ _)
  have hp := position_add B m (N - m)
  rw [Nat.add_sub_of_le hm] at hp
  omega

theorem position_sqrt_window_lower {B : ℕ} (hB : 2 ≤ B) (N : ℕ) :
    (N - Nat.sqrt N) * step B (Nat.sqrt N) ≤ position B N :=
  position_lower_from_index hB (Nat.sqrt_le_self N)

end
end PrimeGapNormality.Prime.StretchedClock
