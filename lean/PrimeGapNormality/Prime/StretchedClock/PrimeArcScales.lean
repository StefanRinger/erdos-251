import PrimeGapNormality.Prime.StretchedClock.RestrictedHarmonic
import PrimeGapNormality.Prime.ChebyshevNthPrime
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform analytic bookkeeping for the actual quarter-power sieve level.
The eventual threshold precedes every modulus below `log(N)^2`. -/

namespace PrimeGapNormality.Prime.StretchedClock

open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

def arcSieveLevel (N : ℕ) : ℕ := ⌊(N : ℝ) ^ (1 / 4 : ℝ)⌋₊

theorem arcSieveLevel_sq_le_sqrt (N : ℕ) :
    (arcSieveLevel N : ℝ) ^ 2 ≤ Real.sqrt (N : ℝ) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hq : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hN _
  have hf : (arcSieveLevel N : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Nat.floor_le hq
  have hsq := (sq_le_sq₀ (Nat.cast_nonneg (arcSieveLevel N)) hq).mpr hf
  have he : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN, Real.sqrt_eq_rpow]
    norm_num
  exact hsq.trans_eq he

private theorem log_sq_div_eighth_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 / (N : ℝ) ^ (1 / 8 : ℝ))
      atTop (𝓝 0) := by
  have ht := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 8)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Real.rpow_two] using ht

theorem eventually_arcSieveLevel_data :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ 1 ≤ Real.log (N : ℝ) ∧ 1 ≤ arcSieveLevel N ∧
      (arcSieveLevel N : ℝ) ≤ Real.sqrt (N : ℝ) ∧
      ∀ a : ℕ, 2 ≤ a → (a : ℝ) ≤ Real.log (N : ℝ) ^ 2 →
        a ≤ arcSieveLevel N ∧
        Real.log (N : ℝ) / 8 ≤
          Real.log (((arcSieveLevel N / a : ℕ) : ℝ) + 1) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hq := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hN
  have hlog := Real.tendsto_log_atTop.comp hN
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop 1,
    hq.eventually_ge_atTop 2,
    log_sq_div_eighth_tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)]
      with N hN2 hlog1 hq2 hsmall
  simp only [Function.comp_apply] at hq2 hlog1
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have he0 : 0 < (N : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have he1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  have hs : Real.log (N : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) :=
    (div_le_iff₀ he0).mp hsmall
  have hf := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 4 : ℝ))
  have hhalf : (N : ℝ) ^ (1 / 4 : ℝ) / 2 ≤ (arcSieveLevel N : ℝ) := by
    change (N : ℝ) ^ (1 / 4 : ℝ) < (arcSieveLevel N : ℝ) + 1 at hf
    linarith
  have hR1 : 1 ≤ arcSieveLevel N := by
    have hh : (1 : ℝ) ≤ arcSieveLevel N := by linarith
    exact_mod_cast hh
  have hRsmall : (arcSieveLevel N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hRreal : (1 : ℝ) ≤ arcSieveLevel N := by exact_mod_cast hR1
    have hsq := mul_le_mul_of_nonneg_left hRreal (Nat.cast_nonneg (arcSieveLevel N))
    nlinarith [arcSieveLevel_sq_le_sqrt N]
  refine ⟨hN2, hlog1, hR1, hRsmall, ?_⟩
  intro a ha haUpper
  have ha0 : 0 < a := by omega
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha0
  have hproduct : (a : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) ≤ (arcSieveLevel N : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right (haUpper.trans hs) he0.le
    have hp : (N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) =
        (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hN0]
      norm_num
    nlinarith
  have haLevel : a ≤ arcSieveLevel N := by
    have hm := mul_le_mul_of_nonneg_left he1 haR.le
    have hh : (a : ℝ) ≤ arcSieveLevel N := by nlinarith
    exact_mod_cast hh
  have hquotNat : arcSieveLevel N < a * (arcSieveLevel N / a + 1) := by
    have hmod := Nat.mod_lt (arcSieveLevel N) ha0
    have hdiv := Nat.div_add_mod (arcSieveLevel N) a
    nlinarith
  have hquot : (arcSieveLevel N : ℝ) <
      (a : ℝ) * (((arcSieveLevel N / a : ℕ) : ℝ) + 1) := by exact_mod_cast hquotNat
  have hequot : (N : ℝ) ^ (1 / 8 : ℝ) ≤
      ((arcSieveLevel N / a : ℕ) : ℝ) + 1 := by
    by_contra h
    have hm := mul_lt_mul_of_pos_left (lt_of_not_ge h) haR
    linarith
  have hlogs := Real.log_le_log he0 hequot
  rw [Real.log_rpow hN0] at hlogs
  refine ⟨haLevel, ?_⟩
  linarith

/-- A direct consequence of the accepted Chebyshev inversion. -/
theorem nthPrime_le_twentyFour_mul_log {N : ℕ} (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    (nthPrime N : ℝ) ≤ 24 * (N : ℝ) * Real.log (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hN2 : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hshift : Real.log ((N : ℝ) + 2) ≤ 1 + Real.log (N : ℝ) := by
    have hm := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) + 2)
      (by linarith : (N : ℝ) + 2 ≤ 2 * (N : ℝ))
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at hm
    linarith
  have hbase := nthPrime_le_succ_mul_log N
  push_cast at hbase
  have hleft : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
  have hright : Real.log ((N : ℝ) + 2) + 1 ≤ 3 * Real.log (N : ℝ) := by linarith
  have hlognonneg : 0 ≤ Real.log ((N : ℝ) + 2) + 1 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ (N : ℝ) + 2)
    linarith
  have hm := mul_le_mul hleft hright hlognonneg (by positivity : (0 : ℝ) ≤ 2 * N)
  nlinarith

end
end PrimeGapNormality.Prime.StretchedClock
