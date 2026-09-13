import PrimeGapNormality.Prime.IndexPassageFromPNT
import PrimeGapNormality.Prime.KuperbergSingleton
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field

/-!
# Kuperberg singleton wrapper: `li(x) ∼ x/log x` and `PrimeCountingAsymp`

Wrapper around `kuperberg_singleton_uniform`, not smuggled into the
minimal AHL theorem. One pair `ε,K` for all `x ≥ 16` and `E = {0}`.
Does not use `kuperberg_one_point`. Does not import WeakPNT.

No claim `KuperbergConj13 → weylCriterion`. Kernel stays 0.

Source: R105 G / R106/09; `KuperbergSingleton`;
`IndexPassageFromPNT.PrimeCountingAsymp`.
Contract: API
Audit: GREEN
-/

open Filter Asymptotics MeasureTheory intervalIntegral
open scoped Topology Asymptotics Interval

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

/-! ### Logarithmic integral vs `x / log x` -/

private theorem two_le_of_mem_uIcc {a b t : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (ht : t ∈ [[a, b]]) : 2 ≤ t :=
  (le_min ha hb).trans ht.1

private theorem continuousOn_inv_log {s : Set ℝ} (hs : ∀ t ∈ s, 2 ≤ t) :
    ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) s := by
  have hlog : ContinuousOn Real.log s :=
    Real.continuousOn_log.mono fun t ht =>
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hs t ht)).ne'
  have hdiv : ContinuousOn (fun t : ℝ => (1 : ℝ) / Real.log t) s :=
    continuousOn_const.div hlog fun t ht =>
      (Real.log_pos
          (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hs t ht))).ne'
  simpa [one_div] using hdiv

private theorem intervalIntegrable_inv_log {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume a b := by
  refine (continuousOn_inv_log ?_).intervalIntegrable
  intro t ht
  exact two_le_of_mem_uIcc ha hb ht

private theorem hlIntegral_one_eq_inv_log {x : ℝ} (hx : 2 ≤ x) :
    hlIntegral x 1 = ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ := by
  unfold hlIntegral
  refine integral_congr fun t _ht => ?_
  rw [Nat.cast_one, Real.rpow_neg_one]

private theorem hasDerivAt_id_div_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => s / Real.log s)
      ((Real.log t)⁻¹ - 1 / Real.log t ^ 2) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h := (hasDerivAt_id' t).fun_div (Real.hasDerivAt_log ht0) hlog0
  have hder :
      (1 * Real.log t - t * t⁻¹) / Real.log t ^ 2 =
        (Real.log t)⁻¹ - 1 / Real.log t ^ 2 := by
    have htinv : t * t⁻¹ = (1 : ℝ) := mul_inv_cancel₀ ht0
    rw [one_mul, htinv]
    have hsplit :
        (Real.log t - 1) / Real.log t ^ 2 =
          Real.log t / Real.log t ^ 2 - 1 / Real.log t ^ 2 :=
      sub_div _ _ _
    rw [hsplit]
    have hinv : Real.log t / Real.log t ^ 2 = (Real.log t)⁻¹ := by
      have hsq : Real.log t ^ 2 = Real.log t * Real.log t := by ring
      rw [hsq]
      field_simp [hlog0]
    rw [hinv]
  exact hder ▸ h

/-- Integration by parts / FTC:
`∫_2^x dt/log t = x/log x - 2/log 2 + ∫_2^x dt/(log t)^2`. -/
private theorem hlIntegral_one_eq_id_div_log_add {x : ℝ} (hx : 2 ≤ x) :
    hlIntegral x 1 =
      x / Real.log x - (2 : ℝ) / Real.log 2 +
        ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hli := hlIntegral_one_eq_inv_log hx
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hx
  have hintg : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume (2 : ℝ) x :=
    intervalIntegrable_inv_log (by norm_num : (2 : ℝ) ≤ 2) hx
  have hinth : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume (2 : ℝ) x :=
    Chebyshev.intervalIntegrable_one_div_log_sq
      (by norm_num : (1 : ℝ) < 2) hx1
  have hintf :
      IntervalIntegrable
        (fun t : ℝ => (Real.log t)⁻¹ - 1 / Real.log t ^ 2) volume (2 : ℝ) x :=
    hintg.sub hinth
  have hderiv : ∀ t ∈ [[(2 : ℝ), x]],
      HasDerivAt (fun s : ℝ => s / Real.log s)
        ((Real.log t)⁻¹ - 1 / Real.log t ^ 2) t := by
    intro t ht
    have ht2 : 2 ≤ t := two_le_of_mem_uIcc (by norm_num : (2 : ℝ) ≤ 2) hx ht
    have ht1 : 1 < t := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ht2
    exact hasDerivAt_id_div_log ht1
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv hintf
  have hsub := integral_sub hintg hinth
  have hli' : ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ =
      x / Real.log x - (2 : ℝ) / Real.log 2 +
        ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    have hsplit : ∫ t in (2 : ℝ)..x,
        (Real.log t)⁻¹ - 1 / Real.log t ^ 2 =
        (∫ t in (2 : ℝ)..x, (Real.log t)⁻¹) -
          ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := hsub
    have hbdry :
        (∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ - 1 / Real.log t ^ 2) =
          x / Real.log x - (2 : ℝ) / Real.log 2 := hFTC
    linarith
  exact hli.trans hli'

private theorem isLittleO_id_div_log_sq :
    (fun x : ℝ => x / Real.log x ^ 2) =o[atTop]
      fun x => x / Real.log x := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx hg
    have hpos : 0 < x / Real.log x :=
      div_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)
    exact (hpos.ne' hg).elim
  · have hinv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp [hx0, hlog]

private theorem isLittleO_integral_one_div_log_sq :
    (fun x : ℝ => ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2) =o[atTop]
      fun x => x / Real.log x :=
  Chebyshev.integral_one_div_log_sq_isBigO.trans_isLittleO isLittleO_id_div_log_sq

private theorem isLittleO_const_id_div_log (c : ℝ) :
    (fun _ : ℝ => c) =o[atTop] fun x => x / Real.log x := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx hg
    have hpos : 0 < x / Real.log x :=
      div_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)
    exact (hpos.ne' hg).elim
  · have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h := hlog.const_mul c
    have heq :
        (fun x : ℝ => c * (Real.log x / x)) =ᶠ[atTop]
          fun x => c / (x / Real.log x) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hx0 : x ≠ 0 := by linarith
      have hlog0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      field_simp [hx0, hlog0]
    simpa using h.congr' heq

private theorem isLittleO_hlIntegral_one_sub_id_div_log :
    (fun x : ℝ =>
        (∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2) - (2 : ℝ) / Real.log 2) =o[atTop]
      fun x => x / Real.log x :=
  isLittleO_integral_one_div_log_sq.sub
    (isLittleO_const_id_div_log ((2 : ℝ) / Real.log 2))

/-- Elementary integral asymptotic: `li(x) / (x / log x) → 1`. -/
theorem hlIntegral_one_asymptotic :
    Tendsto (fun x : ℝ => hlIntegral x 1 / (x / Real.log x)) atTop (𝓝 1) := by
  have heq :
      (fun x : ℝ => hlIntegral x 1) =ᶠ[atTop]
        (fun x : ℝ => x / Real.log x) +
          (fun x =>
            (∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2) - (2 : ℝ) / Real.log 2) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    simp only [Pi.add_apply]
    have h := hlIntegral_one_eq_id_div_log_add hx
    linarith
  have hrefl : (fun x : ℝ => x / Real.log x) ~[atTop]
      fun x : ℝ => x / Real.log x :=
    IsEquivalent.refl
  have hadd := hrefl.add_isLittleO isLittleO_hlIntegral_one_sub_id_div_log
  have hmain := hadd.congr_left heq.symm
  have hne : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_ne_zero (by linarith) (Real.log_pos hx).ne'
  exact (isEquivalent_iff_tendsto_one hne).mp hmain

/-! ### Floor comparison for `π(⌊x⌋) / (x / log x)` -/

private theorem two_le_floor_of_two_lt {x : ℝ} (hx : (2 : ℝ) < x) : (2 : ℕ) ≤ ⌊x⌋₊ :=
  (Nat.le_floor_iff (le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hx))).2
    (by
      rw [Nat.cast_two]
      exact le_of_lt hx)

private theorem floor_cast_pos {x : ℝ} (hx : 2 < x) : (0 : ℝ) < ⌊x⌋₊ := by
  have h2 : 2 ≤ ⌊x⌋₊ := two_le_floor_of_two_lt hx
  exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 1) h2)

private theorem one_lt_floor_cast {x : ℝ} (hx : 2 < x) : (1 : ℝ) < ⌊x⌋₊ := by
  have h2 : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (two_le_floor_of_two_lt hx)
  linarith

private theorem tendsto_log_floor_div_self :
    Tendsto (fun x : ℝ => Real.log ((⌊x⌋₊ : ℝ) / x)) atTop (𝓝 0) := by
  have hcont : ContinuousAt Real.log (1 : ℝ) :=
    Real.continuousAt_log (by norm_num)
  have hcomp :=
    hcont.tendsto.comp (tendsto_nat_floor_div_atTop (R := ℝ))
  have hfun :
      (fun x : ℝ => Real.log ((⌊x⌋₊ : ℝ) / x)) =
        Real.log ∘ fun x : ℝ => (⌊x⌋₊ : ℝ) / x := by
    funext x
    rfl
  simpa [hfun, Real.log_one] using hcomp

private theorem tendsto_log_floor_div_log :
    Tendsto (fun x : ℝ => Real.log (⌊x⌋₊ : ℝ) / Real.log x) atTop (𝓝 1) := by
  have hquot :
      Tendsto (fun x : ℝ => Real.log ((⌊x⌋₊ : ℝ) / x) / Real.log x)
        atTop (𝓝 0) := by
    have hinv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hmul := tendsto_log_floor_div_self.mul hinv
    have heq' :
        (fun x : ℝ => Real.log ((⌊x⌋₊ : ℝ) / x) * (Real.log x)⁻¹) =ᶠ[atTop]
          fun x => Real.log ((⌊x⌋₊ : ℝ) / x) / Real.log x := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x _hx
      exact (div_eq_mul_inv _ _).symm
    simpa using hmul.congr' heq'
  have hadd := (tendsto_const_nhds (x := (1 : ℝ))).add hquot
  have heq :
      (fun x : ℝ => Real.log (⌊x⌋₊ : ℝ) / Real.log x) =ᶠ[atTop]
        fun x => 1 + Real.log ((⌊x⌋₊ : ℝ) / x) / Real.log x := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hflpos := floor_cast_pos hx
    have hlogx : Real.log x ≠ 0 :=
      (Real.log_pos (by linarith : (1 : ℝ) < x)).ne'
    have hprod : (⌊x⌋₊ : ℝ) = x * ((⌊x⌋₊ : ℝ) / x) := by
      field_simp [hx0.ne']
    have hlogfl :
        Real.log (⌊x⌋₊ : ℝ) =
          Real.log x + Real.log ((⌊x⌋₊ : ℝ) / x) := by
      have hmul := Real.log_mul hx0.ne' (div_pos hflpos hx0).ne'
      rw [← hprod] at hmul
      exact hmul
    rw [hlogfl, add_div, div_self hlogx]
  have hg := hadd.congr' heq.symm
  simpa using hg

private theorem tendsto_id_div_log_floor_div :
    Tendsto (fun x : ℝ =>
        ((⌊x⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ)) / (x / Real.log x))
      atTop (𝓝 1) := by
  have hfloor : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ) / x) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop (R := ℝ)
  have hlog := tendsto_log_floor_div_log.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hlog' :
      Tendsto (fun x : ℝ => Real.log x / Real.log (⌊x⌋₊ : ℝ)) atTop (𝓝 1) := by
    have heq :
        (fun x : ℝ => (Real.log (⌊x⌋₊ : ℝ) / Real.log x)⁻¹) =ᶠ[atTop]
          fun x => Real.log x / Real.log (⌊x⌋₊ : ℝ) := by
      filter_upwards with x
      rw [inv_div]
    simpa [inv_one] using hlog.congr' heq
  have hmul := hfloor.mul hlog'
  have heq :
      (fun x : ℝ =>
          ((⌊x⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ)) / (x / Real.log x)) =ᶠ[atTop]
        fun x => ((⌊x⌋₊ : ℝ) / x) * (Real.log x / Real.log (⌊x⌋₊ : ℝ)) := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hlogx : Real.log x ≠ 0 :=
      (Real.log_pos (by linarith : (1 : ℝ) < x)).ne'
    have hlogfl : Real.log (⌊x⌋₊ : ℝ) ≠ 0 :=
      (Real.log_pos (one_lt_floor_cast hx)).ne'
    field_simp [hx0, hlogx, hlogfl]
  have hg := hmul.congr' heq.symm
  simpa [mul_one] using hg

private theorem tendsto_hlIntegral_floor_div_id_div_log :
    Tendsto (fun x : ℝ =>
        hlIntegral (⌊x⌋₊ : ℝ) 1 / (x / Real.log x)) atTop (𝓝 1) := by
  have hfloorR : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_nat_floor_atTop
  have hli := hlIntegral_one_asymptotic.comp hfloorR
  have hmul := hli.mul tendsto_id_div_log_floor_div
  have heq :
      (fun x : ℝ => hlIntegral (⌊x⌋₊ : ℝ) 1 / (x / Real.log x)) =ᶠ[atTop]
        fun x =>
          hlIntegral (⌊x⌋₊ : ℝ) 1 /
              ((⌊x⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ)) *
            (((⌊x⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ)) / (x / Real.log x)) := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hlogx : Real.log x ≠ 0 :=
      (Real.log_pos (by linarith : (1 : ℝ) < x)).ne'
    have hfl0 : (⌊x⌋₊ : ℝ) ≠ 0 := (floor_cast_pos hx).ne'
    have hlogfl : Real.log (⌊x⌋₊ : ℝ) ≠ 0 :=
      (Real.log_pos (one_lt_floor_cast hx)).ne'
    have hb : (⌊x⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ) ≠ 0 :=
      div_ne_zero hfl0 hlogfl
    have hc : x / Real.log x ≠ 0 := div_ne_zero hx0 hlogx
    field_simp [hb, hc]
  have hg := hmul.congr' heq.symm
  simpa [mul_one] using hg

private theorem floor_rpow_div_id_div_log {ε x : ℝ} (hx : 2 < x) :
    (⌊x⌋₊ : ℝ) ^ (1 - ε) / (x / Real.log x) =
      ((⌊x⌋₊ : ℝ) / x) ^ (1 - ε) * (Real.log x / x ^ ε) := by
  have hx0 : 0 < x := by linarith
  have hflnn : 0 ≤ (⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
  have hpow : x ^ (1 - ε) * x ^ ε = x := by
    rw [← Real.rpow_add hx0, show (1 - ε) + ε = (1 : ℝ) by ring, Real.rpow_one]
  have hleft :
      (⌊x⌋₊ : ℝ) ^ (1 - ε) / (x / Real.log x) =
        (⌊x⌋₊ : ℝ) ^ (1 - ε) * Real.log x / x :=
    div_div_eq_mul_div _ _ _
  have hright :
      ((⌊x⌋₊ : ℝ) / x) ^ (1 - ε) * (Real.log x / x ^ ε) =
        (⌊x⌋₊ : ℝ) ^ (1 - ε) / x ^ (1 - ε) * (Real.log x / x ^ ε) := by
    rw [Real.div_rpow hflnn hx0.le]
  rw [hleft, hright, div_mul_div_comm, hpow]

private theorem isLittleO_floor_rpow_id_div_log {ε : ℝ} (hε : 0 < ε) :
    (fun x : ℝ => (⌊x⌋₊ : ℝ) ^ (1 - ε)) =o[atTop]
      fun x => x / Real.log x := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx hg
    have hpos : 0 < x / Real.log x :=
      div_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)
    exact (hpos.ne' hg).elim
  · have hpow :
        Tendsto (fun x : ℝ => ((⌊x⌋₊ : ℝ) / x) ^ (1 - ε)) atTop (𝓝 1) := by
      have h := (tendsto_nat_floor_div_atTop (R := ℝ)).rpow_const (p := 1 - ε)
          (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
      simpa [Real.one_rpow] using h
    have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ ε) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
    have hmul := hpow.mul hlog
    have heq :
        (fun x : ℝ =>
            (⌊x⌋₊ : ℝ) ^ (1 - ε) / (x / Real.log x)) =ᶠ[atTop]
          fun x => ((⌊x⌋₊ : ℝ) / x) ^ (1 - ε) * (Real.log x / x ^ ε) := by
      filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
      exact floor_rpow_div_id_div_log hx
    have hg := hmul.congr' heq.symm
    simpa using hg

/-! ### `KuperbergConj13` → `PrimeCountingAsymp` -/

/-- Uniform singleton Kuperberg plus `li(x) ∼ x/log x` yields
`π(⌊x⌋) ∼ x / log x`. Does not use `kuperberg_one_point`. -/
theorem primeCountingAsymp_of_kuperberg (hK : KuperbergConj13) :
    PrimeCountingAsymp := by
  obtain ⟨ε, K, hε, hKpos, hbound⟩ := kuperberg_singleton_uniform hK
  have herr :
      Tendsto (fun x : ℝ =>
          ((Nat.primeCounting ⌊x⌋₊ : ℝ) - hlIntegral (⌊x⌋₊ : ℝ) 1) /
            (x / Real.log x)) atTop (𝓝 0) := by
    have hO :
        (fun x : ℝ =>
            (Nat.primeCounting ⌊x⌋₊ : ℝ) - hlIntegral (⌊x⌋₊ : ℝ) 1) =O[atTop]
          fun x => (⌊x⌋₊ : ℝ) ^ (1 - ε) := by
      refine IsBigO.of_bound K ?_
      filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
      have hN : 16 ≤ ⌊x⌋₊ :=
        (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ x)).2 (by exact_mod_cast hx)
      have hKbound := hbound hN
      rw [hlMain_singleton_zero] at hKbound
      simp only [Real.norm_eq_abs]
      have hgabs :
          |(⌊x⌋₊ : ℝ) ^ (1 - ε)| = (⌊x⌋₊ : ℝ) ^ (1 - ε) :=
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      rw [hgabs]
      exact hKbound
    exact (hO.trans_isLittleO (isLittleO_floor_rpow_id_div_log hε)).tendsto_div_nhds_zero
  have hadd := tendsto_hlIntegral_floor_div_id_div_log.add herr
  have heq :
      (fun x : ℝ =>
          (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) =ᶠ[atTop]
        fun x =>
          hlIntegral (⌊x⌋₊ : ℝ) 1 / (x / Real.log x) +
            ((Nat.primeCounting ⌊x⌋₊ : ℝ) - hlIntegral (⌊x⌋₊ : ℝ) 1) /
              (x / Real.log x) := by
    filter_upwards with x
    rw [← add_div]
    ring
  have hg := hadd.congr' heq.symm
  simpa [PrimeCountingAsymp] using hg

/-- Index inversion on `nthPrime` from the uniform Kuperberg singleton.
Does not claim `KuperbergConj13 → weylCriterion`. -/
theorem indexPassageD_nthPrime_of_kuperberg (hK : KuperbergConj13) :
    IndexPassageD nthPrime :=
  indexPassageD_nthPrime_of_primeCountingAsymp (primeCountingAsymp_of_kuperberg hK)

end

end PrimeGapNormality.Prime
