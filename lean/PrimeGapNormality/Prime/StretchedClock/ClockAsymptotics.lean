import PrimeGapNormality.Prime.StretchedClock.ClockBounds
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field

/-!
# Asymptotics of the concrete stretched clock

The two-label estimate yields an elementary squeeze. No regular variation
or additional hypothesis on the clock is used.
-/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset Filter Asymptotics
open scoped Topology
noncomputable section

def normalizedPosition (B N : ℕ) : ℝ :=
  (position B N : ℝ) / ((N : ℝ) * (step B N : ℝ))

theorem natSqrt_tendsto_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop (m * m)] with N hN
  exact Nat.le_sqrt.mpr hN

theorem natSqrt_div_self_tendsto_zero :
    Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hh : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply squeeze_zero (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hh
  intro N
  change (Nat.sqrt N : ℝ) / (N : ℝ) ≤ (Real.sqrt (N : ℝ))⁻¹
  calc
    (Nat.sqrt N : ℝ) / (N : ℝ) ≤ Real.sqrt (N : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right (Real.nat_sqrt_le_real_sqrt (a := N)) (Nat.cast_nonneg _)
    _ = (Real.sqrt (N : ℝ))⁻¹ := Real.sqrt_div_self

theorem inverse_step_tendsto_zero {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N => 1 / (step B N : ℝ)) atTop (𝓝 0) := by
  have hstep : Tendsto (fun N => (step B N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (step_tendsto_atTop hB)
  exact hstep.const_div_atTop 1

/-- The loss from replacing every step by the last step is paid by the
initial square-root prefix and at most one unit per later step. -/
theorem position_product_le_add_errors {B : ℕ} (hB : 2 ≤ B) (N : ℕ) :
    (N : ℝ) * (step B N : ℝ) ≤ (position B N : ℝ) +
      (Nat.sqrt N : ℝ) * (step B N : ℝ) + N := by
  have hsN : (Nat.sqrt N : ℝ) ≤ N := Nat.cast_le.mpr (Nat.sqrt_le_self N)
  have hs0 : (0 : ℝ) ≤ Nat.sqrt N := Nat.cast_nonneg _
  have hp : ((N : ℝ) - Nat.sqrt N) * (step B (Nat.sqrt N) : ℝ) ≤ position B N := by
    have hh := Nat.cast_le (α := ℝ).mpr (position_sqrt_window_lower hB N)
    simpa only [Nat.cast_mul, Nat.cast_sub (Nat.sqrt_le_self N)] using hh
  have hk : (step B N : ℝ) ≤ (step B (Nat.sqrt N) : ℝ) + 1 := by
    exact_mod_cast step_le_sqrt_step_add_one hB N
  have hm := mul_le_mul_of_nonneg_left hk (sub_nonneg.mpr hsN)
  nlinarith

theorem normalizedPosition_bounds {B N : ℕ} (hB : 2 ≤ B) (hN : 0 < N) :
    1 - (Nat.sqrt N : ℝ) / N - 1 / (step B N : ℝ) ≤ normalizedPosition B N ∧
      normalizedPosition B N ≤ 1 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk : (0 : ℝ) < step B N := Nat.cast_pos.mpr (step_pos hB N)
  have hden : 0 < (N : ℝ) * (step B N : ℝ) := mul_pos hNr hk
  constructor
  · unfold normalizedPosition
    apply (le_div_iff₀ hden).mpr
    have he : (1 - (Nat.sqrt N : ℝ) / N - 1 / (step B N : ℝ)) *
        ((N : ℝ) * (step B N : ℝ)) =
        (N : ℝ) * (step B N : ℝ) - (Nat.sqrt N : ℝ) * (step B N : ℝ) - N := by
      field_simp [hNr.ne', hk.ne'] <;> ring
    rw [he]
    linarith [position_product_le_add_errors hB N]
  · unfold normalizedPosition
    apply (div_le_one hden).mpr
    exact_mod_cast position_le_mul_step hB N

theorem normalizedPosition_tendsto_one {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (normalizedPosition B) atTop (𝓝 1) := by
  have hlo : Tendsto
      (fun N : ℕ => 1 - (Nat.sqrt N : ℝ) / N - 1 / (step B N : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub natSqrt_div_self_tendsto_zero).sub
        (inverse_step_tendsto_zero hB)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (normalizedPosition_bounds hB hN).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (normalizedPosition_bounds hB hN).2

theorem step_succ_le_step_add_one {B N : ℕ} (hB : 2 ≤ B) (hN : 0 < N) :
    step B (N + 1) ≤ step B N + 1 := by
  have hs := Nat.add_one_sqrt_le_of_ne_zero (Nat.ne_of_gt hN)
  exact (step_le_sqrt_step_add_one hB (N + 1)).trans
    (Nat.add_le_add_right (step_mono hB hs) 1)

theorem position_pos {B N : ℕ} (hB : 2 ≤ B) (hN : 0 < N) : 0 < position B N :=
  hN.trans_le (le_position hB N)

/-- Every final incomplete insertion block has negligible digit mass. -/
theorem step_succ_div_position_tendsto_zero {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N => (step B (N + 1) : ℝ) / (position B N : ℝ)) atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun N : ℕ => ((2 : ℝ) / N) / normalizedPosition B N) atTop (𝓝 0) := by
    have hd := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).div
      (normalizedPosition_tendsto_one hB) (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun N : ℕ => ((2 : ℝ) / N) / normalizedPosition B N)
      atTop (𝓝 ((0 : ℝ) / 1)) at hd
    simpa only [zero_div] using hd
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hmajor
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk : (0 : ℝ) < step B N := Nat.cast_pos.mpr (step_pos hB N)
  have hP : (0 : ℝ) < position B N := Nat.cast_pos.mpr (position_pos hB hN)
  have hnext : (step B (N + 1) : ℝ) ≤ 2 * (step B N : ℝ) := by
    have hn := step_succ_le_step_add_one hB hN
    have hh := one_le_step hB N
    exact_mod_cast (show step B (N + 1) ≤ 2 * step B N by omega)
  have he : ((2 : ℝ) / N) / normalizedPosition B N =
      2 * (step B N : ℝ) / (position B N : ℝ) := by
    unfold normalizedPosition
    field_simp [hNr.ne', hk.ne', hP.ne'] <;> ring
  rw [he]
  exact div_le_div_of_nonneg_right hnext hP.le

/-- The first square-root many anchors have negligible digit mass. -/
theorem position_sqrt_div_position_tendsto_zero {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N => (position B (Nat.sqrt N) : ℝ) / (position B N : ℝ))
      atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun N : ℕ => ((Nat.sqrt N : ℝ) / N) / normalizedPosition B N) atTop (𝓝 0) := by
    have hd := natSqrt_div_self_tendsto_zero.div
      (normalizedPosition_tendsto_one hB) (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun N : ℕ => ((Nat.sqrt N : ℝ) / N) / normalizedPosition B N)
      atTop (𝓝 ((0 : ℝ) / 1)) at hd
    simpa only [zero_div] using hd
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hmajor
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk : (0 : ℝ) < step B N := Nat.cast_pos.mpr (step_pos hB N)
  have hP : (0 : ℝ) < position B N := Nat.cast_pos.mpr (position_pos hB hN)
  have hprefix : position B (Nat.sqrt N) ≤ Nat.sqrt N * step B N :=
    (position_le_mul_step hB (Nat.sqrt N)).trans
      (Nat.mul_le_mul_left (Nat.sqrt N) (step_mono hB (Nat.sqrt_le_self N)))
  have he : ((Nat.sqrt N : ℝ) / N) / normalizedPosition B N =
      (Nat.sqrt N : ℝ) * (step B N : ℝ) / (position B N : ℝ) := by
    unfold normalizedPosition
    field_simp [hNr.ne', hk.ne', hP.ne'] <;> ring
  rw [he]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hprefix) hP.le

theorem index_div_position_tendsto_zero {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N : ℕ => (N : ℝ) / (position B N : ℝ)) atTop (𝓝 0) := by
  have hh : Tendsto (fun N : ℕ => (1 / (step B N : ℝ)) / normalizedPosition B N)
      atTop (𝓝 0) := by
    have hd := (inverse_step_tendsto_zero hB).div
      (normalizedPosition_tendsto_one hB) (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun N : ℕ => (1 / (step B N : ℝ)) / normalizedPosition B N)
      atTop (𝓝 ((0 : ℝ) / 1)) at hd
    simpa only [zero_div] using hd
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk : (0 : ℝ) < step B N := Nat.cast_pos.mpr (step_pos hB N)
  have hP : (0 : ℝ) < position B N := Nat.cast_pos.mpr (position_pos hB hN)
  unfold normalizedPosition
  field_simp [hNr.ne', hk.ne', hP.ne'] <;> ring

theorem position_div_index_realStep_tendsto_one {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N => (position B N : ℝ) / ((N : ℝ) * realStep B N)) atTop (𝓝 1) := by
  have hh : Tendsto
      (fun N => normalizedPosition B N * ((step B N : ℝ) / realStep B N)) atTop (𝓝 1) := by
    simpa only [one_mul] using
      (normalizedPosition_tendsto_one hB).mul (step_div_realStep_tendsto_one hB)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk : (0 : ℝ) < step B N := Nat.cast_pos.mpr (step_pos hB N)
  unfold normalizedPosition
  field_simp [hNr.ne', hk.ne', (realStep_pos hB N).ne'] <;> ring

theorem log_add_four_div_log_tendsto_one :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 4) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  have hd : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 4) - Real.log (N : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (Real.tendsto_log_comp_add_sub_log 4).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh : Tendsto
      (fun N : ℕ => 1 + (Real.log ((N : ℝ) + 4) - Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add (hd.div_atTop hl)
  apply hh.congr'
  filter_upwards [hl.eventually_gt_atTop (0 : ℝ)] with N hN
  field_simp [hN.ne'] <;> ring

theorem loglog_add_four_sub_loglog_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (Real.log ((N : ℝ) + 4)) -
      Real.log (Real.log (N : ℝ))) atTop (𝓝 0) := by
  have hh : Tendsto
      (fun N : ℕ => Real.log (Real.log ((N : ℝ) + 4) / Real.log (N : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.log_one] using log_add_four_div_log_tendsto_one.log (by norm_num : (1 : ℝ) ≠ 0)
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply hh.congr'
  filter_upwards [hl.eventually_gt_atTop (0 : ℝ)] with N hN
  exact Real.log_div (zero_lt_one.trans (one_lt_log_add_four N)).ne' hN.ne'

theorem loglog_add_four_div_loglog_tendsto_one :
    Tendsto (fun N : ℕ => Real.log (Real.log ((N : ℝ) + 4)) /
      Real.log (Real.log (N : ℝ))) atTop (𝓝 1) := by
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hh : Tendsto
      (fun N : ℕ => 1 + (Real.log (Real.log ((N : ℝ) + 4)) -
        Real.log (Real.log (N : ℝ))) / Real.log (Real.log (N : ℝ))) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add
      (loglog_add_four_sub_loglog_tendsto_zero.div_atTop hll)
  apply hh.congr'
  filter_upwards [hll.eventually_gt_atTop (0 : ℝ)] with N hN
  field_simp [hN.ne'] <;> ring

theorem position_div_index_loglog_tendsto_one {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N : ℕ => (position B N : ℝ) /
      ((N : ℝ) * (Real.log (Real.log (N : ℝ)) / Real.log (B : ℝ)))) atTop (𝓝 1) := by
  have hh : Tendsto
      (fun N : ℕ => ((position B N : ℝ) / ((N : ℝ) * realStep B N)) *
        (Real.log (Real.log ((N : ℝ) + 4)) / Real.log (Real.log (N : ℝ)))) atTop (𝓝 1) := by
    simpa only [one_mul] using (position_div_index_realStep_tendsto_one hB).mul
      loglog_add_four_div_loglog_tendsto_one
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ), hll.eventually_gt_atTop (0 : ℝ)] with N hN hllN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hplus : Real.log (Real.log ((N : ℝ) + 4)) ≠ 0 :=
    (Real.log_pos (one_lt_log_add_four N)).ne'
  unfold realStep
  field_simp [hNr.ne', hplus, hllN.ne', (log_base_pos hB).ne'] <;> ring

/-- The paper's literal asymptotic, with the harmless shift removed only
in this limiting statement. -/
theorem position_isEquivalent_index_loglog {B : ℕ} (hB : 2 ≤ B) :
    (fun N : ℕ => (position B N : ℝ)) ~[atTop]
      (fun N : ℕ => (N : ℝ) * (Real.log (Real.log (N : ℝ)) / Real.log (B : ℝ))) :=
  isEquivalent_of_tendsto_one (position_div_index_loglog_tendsto_one hB)

end
end PrimeGapNormality.Prime.StretchedClock
