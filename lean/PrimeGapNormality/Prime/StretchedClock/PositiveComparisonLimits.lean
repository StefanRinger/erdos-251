import PrimeGapNormality.Prime.StretchedClock.PositiveComparisonFinite
import PrimeGapNormality.Prime.StretchedClock.ClockProfile
import PrimeGapNormality.Prime.StretchedClock.ClockAsymptotics

/-! All errors in the literal prefix comparison vanish on the fixed clock. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000

theorem prefixGapBound_nonneg (N : ℕ) : 0 ≤ prefixGapBound N := by
  have hlog : 0 ≤ Real.log ((N + 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 2 by omega))
  unfold prefixGapBound
  positivity

theorem eventually_prefixGapBound_div_minBase_le {B : ℕ} (hB : 2 ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      prefixGapBound N / (localBase B (Nat.sqrt N) : ℝ) ≤ 576 * (N : ℝ) := by
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (4 : ℕ), hl.eventually_ge_atTop 1] with N hN hlog
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hq : (0 : ℝ) < localBase B (Nat.sqrt N) := by
    exact_mod_cast (show 0 < localBase B (Nat.sqrt N) by have := localBase_two_le hB (Nat.sqrt N); omega)
  have harg : ((N + 2 : ℕ) : ℝ) ≤ 2 * N := by
    have hNr4 : (4 : ℝ) ≤ N := Nat.cast_le.mpr hN
    push_cast
    linarith
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (Nat.cast_le.mpr (show 2 ≤ N by omega))
  have hlogs := Real.log_le_log (by positivity : (0 : ℝ) < ((N + 2 : ℕ) : ℝ)) harg
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNr.ne'] at hlogs
  have hlogSmall : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤ 3 * Real.log (N : ℝ) := by linarith
  have hnSmall : ((N + 1 : ℕ) : ℝ) ≤ 2 * N := by
    have hNr4 : (4 : ℝ) ≤ N := Nat.cast_le.mpr hN
    push_cast
    linarith
  have hlogNon : 0 ≤ Real.log ((N + 2 : ℕ) : ℝ) + 1 := by
    have hh : 0 ≤ Real.log ((N + 2 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 2 by omega))
    linarith
  have hprod := mul_le_mul hnSmall hlogSmall hlogNon (by positivity : (0 : ℝ) ≤ 2 * N)
  have hnum : prefixGapBound N ≤ 288 * (N : ℝ) * Real.log (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 48)
    unfold prefixGapBound
    nlinarith
  have hmin := half_log_le_localBase_sqrt hB (by omega : 0 < N)
  have hm := mul_le_mul_of_nonneg_left hmin (by positivity : (0 : ℝ) ≤ 576 * N)
  apply (div_le_iff₀ hq).mpr
  nlinarith

theorem prefixComparisonError_div_position_tendsto_zero {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N => prefixComparisonError B N (freezeLength N) / (position B N : ℝ))
      atTop (𝓝 0) := by
  have hd : 0 < (B : ℝ) - 1 := sub_pos.mpr (one_lt_base hB)
  have hfreeze : Tendsto (fun N : ℕ =>
      ((N : ℝ) * ((localBase B N : ℝ) / ((B : ℝ) - 1) * freezeError N (freezeLength N))) /
        (position B N : ℝ)) atTop (𝓝 0) := by
    have hh := ((index_div_position_tendsto_zero hB).mul
      (freeze_weighted_error_tendsto_zero hB)).const_mul (864 / ((B : ℝ) - 1))
    change Tendsto (fun N : ℕ => (864 / ((B : ℝ) - 1)) *
      (((N : ℝ) / (position B N : ℝ)) *
        (((N + 1 : ℕ) : ℝ) ^ 2 * (localBase B N : ℝ) *
          (2 : ℝ)⁻¹ ^ freezeLength N))) atTop
      (𝓝 ((864 / ((B : ℝ) - 1)) * (0 * 0))) at hh
    simp only [mul_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun N => by
      simp only [freezeError, div_eq_mul_inv, mul_inv_rev]
      ring
  have hmajor : Tendsto (fun N : ℕ => (576 / ((B : ℝ) - 1)) *
      ((N : ℝ) / (position B N : ℝ))) atTop (𝓝 0) := by
    have hh := (index_div_position_tendsto_zero hB).const_mul (576 / ((B : ℝ) - 1))
    change Tendsto (fun N : ℕ => (576 / ((B : ℝ) - 1)) *
      ((N : ℝ) / (position B N : ℝ))) atTop (𝓝 ((576 / ((B : ℝ) - 1)) * 0)) at hh
    simpa only [mul_zero] using hh
  have hgap : Tendsto (fun N => prefixGapBound N /
      ((localBase B (Nat.sqrt N) : ℝ) * ((B : ℝ) - 1)) / (position B N : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N =>
      div_nonneg (div_nonneg (prefixGapBound_nonneg N)
        (mul_nonneg (Nat.cast_nonneg _) hd.le)) (Nat.cast_nonneg _)) _ hmajor
    filter_upwards [eventually_prefixGapBound_div_minBase_le hB] with N hN
    have hh := div_le_div_of_nonneg_right hN (mul_nonneg hd.le (Nat.cast_nonneg (position B N)))
    calc
      _ = (prefixGapBound N / (localBase B (Nat.sqrt N) : ℝ)) /
          (((B : ℝ) - 1) * (position B N : ℝ)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (576 * (N : ℝ)) / (((B : ℝ) - 1) * (position B N : ℝ)) := hh
      _ = _ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hh := hfreeze.add hgap
  simp only [add_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall fun N => by simp only [prefixComparisonError, add_div]

theorem prefixBadWeight_div_position_tendsto_zero {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N => ((position B (Nat.sqrt N) + 2 * freezeLength N * step B N : ℕ) : ℝ) /
      (position B N : ℝ)) atTop (𝓝 0) := by
  have htail : Tendsto (fun N : ℕ => (2 * ((freezeLength N : ℝ) / N)) / normalizedPosition B N)
      atTop (𝓝 0) := by
    have hh := (freezeLength_div_index_tendsto_zero.const_mul (2 : ℝ)).div
      (normalizedPosition_tendsto_one hB) (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun N : ℕ => (2 * ((freezeLength N : ℝ) / N)) / normalizedPosition B N)
      atTop (𝓝 ((2 * 0) / 1)) at hh
    simpa only [mul_zero, zero_div] using hh
  have hh := (position_sqrt_div_position_tendsto_zero hB).add htail
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hk : (step B N : ℝ) ≠ 0 := (Nat.cast_pos.mpr (step_pos hB N)).ne'
  have hP : (position B N : ℝ) ≠ 0 := (Nat.cast_pos.mpr (position_pos hB hN)).ne'
  unfold normalizedPosition
  push_cast
  field_simp [hNr, hk, hP] <;> ring

end
end PrimeGapNormality.Prime.StretchedClock
