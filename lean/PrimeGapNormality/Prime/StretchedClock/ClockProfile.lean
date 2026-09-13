import PrimeGapNormality.Prime.StretchedClock.ClockBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field

/-!
# Concrete logarithmic profile for the stretched-clock comparison

The freeze horizon is a natural ceiling. All geometric errors use a
natural power of the inverse base, so no integer-exponent cast is involved.
-/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset Filter
open scoped Topology
noncomputable section

def freezeLength (N : ℕ) : ℕ := ⌈Real.log (N : ℝ) ^ 2⌉₊

theorem log_sq_le_freezeLength (N : ℕ) :
    Real.log (N : ℝ) ^ 2 ≤ (freezeLength N : ℝ) := Nat.le_ceil _

theorem freezeLength_lt_log_sq_add_one (N : ℕ) :
    (freezeLength N : ℝ) < Real.log (N : ℝ) ^ 2 + 1 :=
  Nat.ceil_lt_add_one (sq_nonneg _)

theorem half_log_le_localBase_sqrt {B N : ℕ} (hB : 2 ≤ B) (hN : 0 < N) :
    (1 / 2 : ℝ) * Real.log (N : ℝ) ≤ (localBase B (Nat.sqrt N) : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hh := Real.log_lt_log (by positivity : (0 : ℝ) < (N : ℝ) + 4)
    (add_four_lt_sqrt_add_four_sq N)
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hlogN : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 4) :=
    Real.log_le_log hNr (by linarith)
  have hq := log_add_four_le_localBase hB (Nat.sqrt N)
  linarith

theorem localBase_le_two_base_mul_log {B N : ℕ} (hB : 2 ≤ B) (hN : 4 ≤ N) :
    (localBase B N : ℝ) ≤ 2 * (B : ℝ) * Real.log (N : ℝ) := by
  have hNr : (4 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have hNpos : (0 : ℝ) < N := by linarith
  have harg : (N : ℝ) + 4 ≤ 2 * N := by linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) + 4) harg
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNpos.ne'] at hlog
  have hlog2 : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hh : Real.log ((N : ℝ) + 4) ≤ 2 * Real.log (N : ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_left hh (base_pos hB).le
  exact (localBase_lt_base_mul_log_add_four hB N).le.trans (by nlinarith)

theorem eventually_localBase_le_log_sq {B : ℕ} (hB : 2 ≤ B) :
    ∀ᶠ N : ℕ in atTop, (localBase B N : ℝ) ≤ Real.log (N : ℝ) ^ 2 := by
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (4 : ℕ), hl.eventually_ge_atTop (2 * (B : ℝ))] with N hN hlog
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by
    have := base_pos hB
    linarith
  have hm := mul_le_mul_of_nonneg_right hlog hlog0
  exact (localBase_le_two_base_mul_log hB hN).trans (by nlinarith)

theorem log_sq_div_index_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 / N) atTop (𝓝 0) := by
  have hh : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 2 (by norm_num)
  simpa only [Function.comp_def] using hh.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem freezeLength_div_index_tendsto_zero :
    Tendsto (fun N : ℕ => (freezeLength N : ℝ) / N) atTop (𝓝 0) := by
  have hh : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 / N + 1 / (N : ℝ))
      atTop (𝓝 0) := by
    simpa only [add_zero] using log_sq_div_index_tendsto_zero.add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply squeeze_zero (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hh
  intro N
  have ht := div_le_div_of_nonneg_right (freezeLength_lt_log_sq_add_one N).le
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  simpa only [add_div] using ht

theorem eventually_freezeLength_le_index : ∀ᶠ N : ℕ in atTop, freezeLength N ≤ N := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    freezeLength_div_index_tendsto_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hN hh
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hf : (freezeLength N : ℝ) < N := (div_lt_one hNr).mp hh
  exact (Nat.cast_lt.mp hf).le

/-- A fixed polynomial inverse eventually dominates the geometric freeze
factor. The exponent on the left is the actual natural freeze length. -/
theorem eventually_freeze_inverse_pow_le_index_inverse_four :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ)⁻¹ ^ freezeLength N ≤ (N : ℝ)⁻¹ ^ 4 := by
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hl.eventually_ge_atTop (4 / Real.log 2)] with N hN hh
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlogN : 0 ≤ Real.log (N : ℝ) := (div_pos (by norm_num) hlog2).le.trans hh
  have hfour : (4 : ℝ) ≤ Real.log (N : ℝ) * Real.log 2 := (div_le_iff₀ hlog2).mp hh
  have hmul := mul_le_mul_of_nonneg_left hfour hlogN
  have hceil := mul_le_mul_of_nonneg_right (log_sq_le_freezeLength N) hlog2.le
  have hbound : 4 * Real.log (N : ℝ) ≤ (freezeLength N : ℝ) * Real.log 2 := by
    nlinarith
  apply (Real.log_le_log_iff (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ freezeLength N)
    (by positivity : (0 : ℝ) < (N : ℝ)⁻¹ ^ 4)).mp
  rw [Real.log_pow, Real.log_pow, Real.log_inv, Real.log_inv]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Uniform weighted freeze error for the whole anchor prefix. -/
theorem freeze_weighted_error_tendsto_zero {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ 2 * (localBase B N : ℝ) *
      (2 : ℝ)⁻¹ ^ freezeLength N) atTop (𝓝 0) := by
  have hmajor := tendsto_const_div_atTop_nhds_zero_nat (8 * (B : ℝ))
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hmajor
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    eventually_freeze_inverse_pow_le_index_inverse_four] with N hN hgeom
  have hNr : (4 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hq : (localBase B N : ℝ) ≤ 2 * (B : ℝ) * N := by
    have hh := Real.log_le_self hNpos.le
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * (B : ℝ))
    exact (localBase_le_two_base_mul_log hB hN).trans hm
  have hs : ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
    have hh : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by push_cast; linarith
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ)) hh 2
    nlinarith
  have hcoefficient : ((N + 1 : ℕ) : ℝ) ^ 2 * (localBase B N : ℝ) ≤
      8 * (B : ℝ) * (N : ℝ) ^ 3 := by
    have hh := mul_le_mul hs hq (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 4 * (N : ℝ) ^ 2)
    nlinarith
  calc
    ((N + 1 : ℕ) : ℝ) ^ 2 * (localBase B N : ℝ) * (2 : ℝ)⁻¹ ^ freezeLength N ≤
        (8 * (B : ℝ) * (N : ℝ) ^ 3) * ((N : ℝ)⁻¹ ^ 4) :=
      mul_le_mul hcoefficient hgeom (by positivity) (by positivity)
    _ = (8 * (B : ℝ)) / N := by field_simp [hNpos.ne'] <;> ring

end
end PrimeGapNormality.Prime.StretchedClock
