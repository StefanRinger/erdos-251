import PrimeGapNormality.Prime.KuperbergAHL
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic

/-!
# Kuperberg 1.3 → AHL close

Adapter close for the aggregated AHL budget. Window subtraction,
inadmissible vanishing, profile range, dyadic `N_X` from one-point
Kuperberg, and the polynomial envelope live in `KuperbergAHL`.
This file only turns

  `ℰ_X ≪ log(2X)·(r+1)·(2(S+1))^r·X^{-ε}`

into the paper remainder `X^{-ε} exp(O((log log X)^2))` and the
limit `AHL`. No individual singular-series lower bounds.

Source: `rounds/round104/13_gpt_paper_v0_3.tex`
subsection "Direct implication from Kuperberg's conjecture";
`lean/PrimeGapNormality/Prime/KuperbergAHL.lean`; R104/07.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Filter Topology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

/-! ### Explicit combinatorial constant

`L = O_κ(log log X)`, `r = O_{κ,d0}(L)`, `S = O(L log X)`, so
`r log(2(S+1)) = O((log log X)^2)`. -/

/-- Coefficient in `exp(A (log log X)^2)`: `A = 4((1+d0)(2κ+1)+3)+1`. -/
def ahlCombExpConst (κ d0 : ℝ) : ℝ :=
  4 * ((1 + d0) * (2 * κ + 1) + 3) + 1

theorem ahlCombExpConst_nonneg {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    0 ≤ ahlCombExpConst κ d0 := by
  unfold ahlCombExpConst
  have h1 : 0 < 1 + d0 := add_pos_of_nonneg_of_pos zero_le_one hd0
  have h2 : 0 < 2 * κ + 1 := by
    have : 0 < 2 * κ := mul_pos (by norm_num) hκ
    linarith
  have : 0 < (1 + d0) * (2 * κ + 1) := mul_pos h1 h2
  linarith

private theorem ahlCombFactor_pos {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    0 < (1 + d0) * (2 * κ + 1) + 3 := by
  have h1 : 0 < 1 + d0 := add_pos_of_nonneg_of_pos zero_le_one hd0
  have h2 : 0 < 2 * κ + 1 := by
    have : 0 < 2 * κ := mul_pos (by norm_num) hκ
    linarith
  have : 0 < (1 + d0) * (2 * κ + 1) := mul_pos h1 h2
  linarith

/-! ### Elementary comparisons -/

private theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hsq : x ≤ x ^ 2 := le_self_pow₀ hx (by omega : 2 ≠ 0)
  have : Real.sqrt x ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hx0] at this

private theorem log_two_mul_le_two_log {X : ℕ} (hX : 3 ≤ X) :
    Real.log (2 * (X : ℝ)) ≤ 2 * Real.log (X : ℝ) := by
  have hx : 0 < (X : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 3) hX)
  rw [Real.log_mul (by norm_num) hx.ne']
  have : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num)
      (Nat.cast_le.mpr (le_trans (by omega : 2 ≤ 3) hX))
  linarith

private theorem tendsto_const_mul_nhds_zero {α : Type*} {f : α → ℝ} {l : Filter α}
    {c : ℝ} (hf : Tendsto f l (nhds 0)) :
    Tendsto (fun x => c * f x) l (nhds 0) :=
  mul_zero c ▸ hf.const_mul c

private theorem tendsto_add_nhds_zero {α : Type*} {f g : α → ℝ} {l : Filter α}
    (hf : Tendsto f l (nhds 0)) (hg : Tendsto g l (nhds 0)) :
    Tendsto (fun x => f x + g x) l (nhds 0) :=
  add_zero (0 : ℝ) ▸ hf.add hg

private theorem abs_lt_of_dist_zero {x ε : ℝ} (h : dist x 0 < ε) : |x| < ε := by
  rwa [Real.dist_eq, sub_zero] at h

private theorem tendsto_inv_pow {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun t : ℝ => (t ^ n)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop hn)

private theorem tendsto_div_pow {n : ℕ} (hn : n ≠ 0) (c : ℝ) :
    Tendsto (fun t : ℝ => c / t ^ n) atTop (nhds 0) := by
  have h := tendsto_const_mul_nhds_zero (c := c) (tendsto_inv_pow hn)
  apply h.congr'
  exact Eventually.of_forall fun t => by simp [div_eq_mul_inv]

private theorem tendsto_log_pow_div_id {n : ℕ} :
    Tendsto (fun x : ℝ => Real.log x ^ n / x) atTop (nhds 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 n (by norm_num)
  apply h.congr'
  exact Eventually.of_forall fun x => by ring

private theorem eventually_two_sq_succ_le_pow4 :
    ∀ᶠ t : ℝ in atTop, 2 * (t ^ 2 + 1) ≤ t ^ 4 := by
  have h1 := tendsto_div_pow (n := 2) (by omega) (2 : ℝ)
  have h2 := tendsto_div_pow (n := 4) (by omega) (2 : ℝ)
  have hsum := tendsto_add_nhds_zero h1 h2
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hsum.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))]
    with t ht0 hball
  have hnn : 0 ≤ (2 : ℝ) / t ^ 2 + 2 / t ^ 4 :=
    add_nonneg (div_nonneg (by norm_num) (pow_nonneg ht0.le 2))
      (div_nonneg (by norm_num) (pow_nonneg ht0.le 4))
  have habs : |(2 : ℝ) / t ^ 2 + 2 / t ^ 4| < 1 := abs_lt_of_dist_zero hball
  have hlt : (2 : ℝ) / t ^ 2 + 2 / t ^ 4 < 1 :=
    abs_of_nonneg hnn ▸ habs
  have ht : t ≠ 0 := ht0.ne'
  have hdiv : (2 * (t ^ 2 + 1)) / t ^ 4 = (2 : ℝ) / t ^ 2 + 2 / t ^ 4 := by
    have hpow : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    rw [mul_add, add_div, mul_one]
    have hA : 2 * t ^ 2 / t ^ 4 = (2 : ℝ) / t ^ 2 := by
      rw [hpow]
      field_simp [ht, pow_ne_zero 2 ht]
    rw [hA]
  exact (div_lt_one (pow_pos ht0 4)).mp (by rwa [hdiv]) |>.le

/-! ### Profile `L,r = O(log log X)` -/

private theorem eventually_one_le_kappa_loglog {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, 1 ≤ κ * Real.log (Real.log (X : ℝ)) := by
  have hloglog :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 16,
    hloglog.eventually (eventually_ge_atTop (1 / κ))] with X _hX hℓ
  calc
    (1 : ℝ) = κ * (1 / κ) := by field_simp [hκ.ne']
    _ ≤ κ * Real.log (Real.log (X : ℝ)) := mul_le_mul_of_nonneg_left hℓ hκ.le

private theorem profileL_le_mul_loglog {κ : ℝ} {X : ℕ}
    (hκ : 0 ≤ κ) (hX : 16 ≤ X)
    (hκlog : 1 ≤ κ * Real.log (Real.log (X : ℝ))) :
    (profileL κ X : ℝ) ≤ (2 * κ + 1) * Real.log (Real.log (X : ℝ)) := by
  have hX3 : 3 ≤ X := le_trans (by norm_num) hX
  have hG : windowG X = Real.log (X : ℝ) := windowG_eq_log hX3
  have hL := profileL_cast_le hκ X
  have hℓ : 1 < Real.log (Real.log (X : ℝ)) := one_lt_log_log_of_sixteen_le hX
  have hz : 1 ≤ κ * Real.log (windowG X) := by rwa [hG]
  have hsqrt : Real.sqrt (κ * Real.log (windowG X)) ≤ κ * Real.log (windowG X) :=
    sqrt_le_self_of_one_le hz
  have h1 : (profileL κ X : ℝ) ≤ 2 * κ * Real.log (windowG X) + 1 := by
    have := hL
    linarith
  rw [hG] at h1
  have h2 : 2 * κ * Real.log (Real.log (X : ℝ)) + 1 ≤
      (2 * κ + 1) * Real.log (Real.log (X : ℝ)) := by
    linarith [hℓ.le]
  exact h1.trans h2

private theorem profileR_succ_le_mul_loglog {κ d0 : ℝ} {X : ℕ}
    (hκ : 0 ≤ κ) (hd0 : 0 ≤ d0) (hX : 16 ≤ X)
    (hκlog : 1 ≤ κ * Real.log (Real.log (X : ℝ))) :
    (profileR (profileL κ X) d0 + 1 : ℝ) ≤
      ((1 + d0) * (2 * κ + 1) + 3) * Real.log (Real.log (X : ℝ)) := by
  have hR := profileR_cast_le (profileL κ X) hd0
  have hL := profileL_le_mul_loglog hκ hX hκlog
  have hℓ : 1 < Real.log (Real.log (X : ℝ)) := one_lt_log_log_of_sixteen_le hX
  have hfac : 0 ≤ 1 + d0 := add_nonneg zero_le_one hd0
  have hr1 : (profileR (profileL κ X) d0 + 1 : ℝ) ≤
      (1 + d0) * (profileL κ X : ℝ) + 3 := by
    linarith [hR]
  have hmid : (1 + d0) * (profileL κ X : ℝ) + 3 ≤
      (1 + d0) * ((2 * κ + 1) * Real.log (Real.log (X : ℝ))) + 3 :=
    add_le_add (mul_le_mul_of_nonneg_left hL hfac) (le_rfl : (3 : ℝ) ≤ 3)
  set ℓ := Real.log (Real.log (X : ℝ))
  have htail :
      (1 + d0) * ((2 * κ + 1) * ℓ) + 3 ≤
        ((1 + d0) * (2 * κ + 1) + 3) * ℓ := by
    have h3 : (3 : ℝ) ≤ 3 * ℓ := by
      have : (3 : ℝ) * 1 ≤ 3 * ℓ :=
        mul_le_mul_of_nonneg_left hℓ.le (by norm_num)
      simpa using this
    have hring : ((1 + d0) * (2 * κ + 1) + 3) * ℓ =
        (1 + d0) * ((2 * κ + 1) * ℓ) + 3 * ℓ := by ring
    linarith
  exact hr1.trans (hmid.trans htail)

/-! ### Prefactor `log 2 + t + log C + log t ≤ t^2` -/

private theorem eventually_log_sum_le_sq {c : ℝ} (_hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop,
      Real.log 2 + t + Real.log c + Real.log t ≤ t ^ 2 := by
  have hc2 := tendsto_div_pow (n := 2) (by omega) (Real.log 2)
  have hid : Tendsto (fun t : ℝ => (1 : ℝ) / t) atTop (nhds 0) := by
    apply tendsto_inv_atTop_zero.congr'
    exact Eventually.of_forall fun t => (one_div t).symm
  have hcc := tendsto_div_pow (n := 2) (by omega) (Real.log c)
  have hlog : Tendsto (fun t : ℝ => Real.log t / t ^ 2) atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
      simpa [pow_one] using tendsto_log_pow_div_id (n := 1)
    have h2 : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have hmul : Tendsto (fun t : ℝ => Real.log t / t * t⁻¹) atTop (nhds 0) := by
      simpa using h1.mul h2
    apply hmul.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ht.ne'
    field_simp [ht0]
  have hsum :=
    tendsto_add_nhds_zero hc2
      (tendsto_add_nhds_zero hid (tendsto_add_nhds_zero hcc hlog))
  have hfun :
      Tendsto (fun t : ℝ =>
          (Real.log 2 + t + Real.log c + Real.log t) / t ^ 2) atTop (nhds 0) := by
    apply hsum.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ht.ne'
    have hpow : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    field_simp [ht0, hpow]
    ring
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hfun.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))]
    with t ht1 hball
  have ht0 : 0 < t := lt_trans (by norm_num) ht1
  have habs :
      |(Real.log 2 + t + Real.log c + Real.log t) / t ^ 2| < 1 :=
    abs_lt_of_dist_zero hball
  have hlt : (Real.log 2 + t + Real.log c + Real.log t) / t ^ 2 < 1 :=
    (le_abs_self _).trans_lt habs
  exact (div_lt_one (pow_pos ht0 2)).mp hlt |>.le

/-! ### `exp(A (log log x)^2) x^{-ε} → 0` -/

private theorem tendsto_exp_loglog_sq_mul_rpow_neg {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) :
    Tendsto (fun x : ℝ => Real.exp (A * Real.log (Real.log x) ^ 2) * x ^ (-ε))
      atTop (nhds 0) := by
  have hfrac : Tendsto (fun x : ℝ => Real.log (Real.log x) ^ 2 / Real.log x)
      atTop (nhds 0) :=
    (tendsto_log_pow_div_id (n := 2)).comp Real.tendsto_log_atTop
  have hAfrac := tendsto_const_mul_nhds_zero (c := A) hfrac
  have hhalf : 0 < ε / 2 := half_pos hε
  have hle : ∀ᶠ x : ℝ in atTop,
      Real.exp (A * Real.log (Real.log x) ^ 2) * x ^ (-ε) ≤ x ^ (-(ε / 2)) := by
    filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1)),
      hAfrac.eventually (Metric.ball_mem_nhds (0 : ℝ) hhalf)] with x hxexp hball
    have hx0 : 0 < x := (Real.exp_pos _).trans hxexp
    have hlogx : Real.exp 1 < Real.log x := (Real.lt_log_iff_exp_lt hx0).mpr hxexp
    have hlogx0 : 0 < Real.log x := (Real.exp_pos _).trans hlogx
    have hone : (1 : ℝ) < Real.exp 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    have hllpos : 0 < Real.log (Real.log x) :=
      Real.log_pos (lt_trans hone hlogx)
    have hfracnn : 0 ≤ Real.log (Real.log x) ^ 2 / Real.log x :=
      div_nonneg (pow_nonneg hllpos.le 2) hlogx0.le
    have hAnn : 0 ≤ A * (Real.log (Real.log x) ^ 2 / Real.log x) :=
      mul_nonneg hA hfracnn
    have habs : |A * (Real.log (Real.log x) ^ 2 / Real.log x)| < ε / 2 :=
      abs_lt_of_dist_zero hball
    have hlt : A * (Real.log (Real.log x) ^ 2 / Real.log x) < ε / 2 :=
      abs_of_nonneg hAnn ▸ habs
    have hcmp : A * Real.log (Real.log x) ^ 2 ≤ (ε / 2) * Real.log x := by
      have : A * Real.log (Real.log x) ^ 2 / Real.log x < ε / 2 := by
        convert hlt using 1
        field_simp [hlogx0.ne']
      exact (div_lt_iff₀ hlogx0).mp this |>.le
    have hxpow : x ^ (-ε) = Real.exp (Real.log x * (-ε)) :=
      Real.rpow_def_of_pos hx0 (-ε)
    have hLHS : Real.exp (A * Real.log (Real.log x) ^ 2) * x ^ (-ε) =
        Real.exp (A * Real.log (Real.log x) ^ 2 - ε * Real.log x) := by
      rw [hxpow, ← Real.exp_add]
      ring_nf
    have hRHS : x ^ (-(ε / 2)) = Real.exp (-(ε / 2) * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0 (-(ε / 2))]
      ring_nf
    rw [hLHS, hRHS]
    exact Real.exp_le_exp.mpr (by linarith)
  have hnn : ∀ᶠ x : ℝ in atTop,
      0 ≤ Real.exp (A * Real.log (Real.log x) ^ 2) * x ^ (-ε) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx0
    exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hx0.le _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_rpow_neg_atTop (half_pos hε)) hnn hle

/-! ### Combinatorial factor `≤ exp(A (log log X)^2)` -/

private theorem comb_factor_le_exp_loglog_sq {κ d0 : ℝ} {X : ℕ}
    (hκ : 0 < κ) (hd0 : 0 < d0) (hfit : ProfileFits κ d0 X)
    (hκlog : 1 ≤ κ * Real.log (Real.log (X : ℝ)))
    (hsq : 2 * (Real.log (X : ℝ) ^ 2 + 1) ≤ Real.log (X : ℝ) ^ 4)
    (hpre : Real.log 2 + Real.log (Real.log (X : ℝ)) +
        Real.log ((1 + d0) * (2 * κ + 1) + 3) +
        Real.log (Real.log (Real.log (X : ℝ))) ≤
      Real.log (Real.log (X : ℝ)) ^ 2) :
    Real.log (2 * (X : ℝ)) * (profileR (profileL κ X) d0 + 1 : ℝ) *
        (2 * ((profileS κ X : ℝ) + 1)) ^ profileR (profileL κ X) d0 ≤
      Real.exp (ahlCombExpConst κ d0 * Real.log (Real.log (X : ℝ)) ^ 2) := by
  set L := profileL κ X
  set r := profileR L d0
  set S := profileS κ X
  set ℓ := Real.log (Real.log (X : ℝ))
  set Cκ := (1 + d0) * (2 * κ + 1) + 3
  have hX := hfit.1
  have hX3 : 3 ≤ X := le_trans (by norm_num) hX
  have hlogX : 1 < Real.log (X : ℝ) := one_lt_log_of_three_le hX3
  have hℓ : 1 < ℓ := one_lt_log_log_of_sixteen_le hX
  have hS : (S : ℝ) ≤ Real.log (X : ℝ) ^ 2 := hfit.2.1
  have h2S : 2 * ((S : ℝ) + 1) ≤ Real.log (X : ℝ) ^ 4 := by
    have : 2 * ((S : ℝ) + 1) ≤ 2 * (Real.log (X : ℝ) ^ 2 + 1) := by linarith
    exact this.trans hsq
  have hbasepos : 0 < 2 * ((S : ℝ) + 1) := by
    have : 0 ≤ (S : ℝ) := Nat.cast_nonneg _
    linarith
  have hCκ : 0 < Cκ := ahlCombFactor_pos hκ hd0
  have hRsucc := profileR_succ_le_mul_loglog hκ.le hd0.le hX hκlog
  have hrC : (r : ℝ) ≤ Cκ * ℓ := by
    have : (r : ℝ) ≤ (r + 1 : ℝ) := by linarith
    exact this.trans hRsucc
  have hpowexp : (2 * ((S : ℝ) + 1)) ^ r =
      Real.exp ((r : ℝ) * Real.log (2 * ((S : ℝ) + 1))) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbasepos, mul_comm]
  have hlogle : Real.log (2 * ((S : ℝ) + 1)) ≤ 4 * ℓ := by
    have hu : 0 < Real.log (X : ℝ) := lt_trans (by norm_num) hlogX
    have := Real.log_le_log hbasepos h2S
    have hlogpow : Real.log (Real.log (X : ℝ) ^ 4) = 4 * ℓ := Real.log_pow _ 4
    rwa [hlogpow] at this
  have hrlog : (r : ℝ) * Real.log (2 * ((S : ℝ) + 1)) ≤ 4 * Cκ * ℓ ^ 2 := by
    have hnn : 0 ≤ Real.log (2 * ((S : ℝ) + 1)) := Real.log_nonneg (by linarith)
    have hℓnn : 0 ≤ ℓ := le_of_lt (lt_trans (by norm_num) hℓ)
    have := mul_le_mul hrC hlogle hnn (mul_nonneg hCκ.le hℓnn)
    have hring : Cκ * ℓ * (4 * ℓ) = 4 * Cκ * ℓ ^ 2 := by ring
    linarith
  have hexp : (2 * ((S : ℝ) + 1)) ^ r ≤ Real.exp (4 * Cκ * ℓ ^ 2) := by
    rw [hpowexp]
    exact Real.exp_le_exp.mpr hrlog
  have hpre' : Real.log (2 * (X : ℝ)) * (r + 1 : ℝ) ≤
      2 * Real.log (X : ℝ) * Cκ * ℓ := by
    have h1 := log_two_mul_le_two_log hX3
    have hnn : 0 ≤ (r + 1 : ℝ) := add_nonneg (Nat.cast_nonneg r) zero_le_one
    have := mul_le_mul h1 hRsucc hnn
      (mul_nonneg (by norm_num) (le_of_lt (lt_trans (by norm_num) hlogX)))
    have hring : 2 * Real.log (X : ℝ) * (Cκ * ℓ) = 2 * Real.log (X : ℝ) * Cκ * ℓ :=
      by ring
    linarith
  have hprodpos : 0 < 2 * Real.log (X : ℝ) * Cκ * ℓ := by
    have hu : 0 < Real.log (X : ℝ) := lt_trans (by norm_num) hlogX
    have hℓpos : 0 < ℓ := lt_trans (by norm_num) hℓ
    exact mul_pos (mul_pos (mul_pos (by norm_num) hu) hCκ) hℓpos
  have hlogprod : Real.log (2 * Real.log (X : ℝ) * Cκ * ℓ) =
      Real.log 2 + ℓ + Real.log Cκ + Real.log ℓ := by
    have hu : Real.log (X : ℝ) ≠ 0 := (lt_trans (by norm_num) hlogX).ne'
    have hℓ0 : ℓ ≠ 0 := (lt_trans (by norm_num) hℓ).ne'
    have hC : Cκ ≠ 0 := hCκ.ne'
    have h2u : (2 : ℝ) * Real.log (X : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hu
    have hCℓ : Cκ * ℓ ≠ 0 := mul_ne_zero hC hℓ0
    have hassoc : (2 : ℝ) * Real.log (X : ℝ) * Cκ * ℓ =
        ((2 : ℝ) * Real.log (X : ℝ)) * (Cκ * ℓ) := by ring
    rw [hassoc, Real.log_mul h2u hCℓ, Real.log_mul (by norm_num) hu,
      Real.log_mul hC hℓ0]
    ring
  have hpreexp : 2 * Real.log (X : ℝ) * Cκ * ℓ ≤ Real.exp (ℓ ^ 2) :=
    (Real.log_le_iff_le_exp hprodpos).mp (hlogprod.symm ▸ hpre)
  have hprod :
      Real.log (2 * (X : ℝ)) * (r + 1 : ℝ) * (2 * ((S : ℝ) + 1)) ^ r ≤
        Real.exp (ℓ ^ 2) * Real.exp (4 * Cκ * ℓ ^ 2) := by
    have h1X : 1 < 2 * (X : ℝ) := by
      have : (1 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 16) hX)
      linarith
    have hnn1 : 0 ≤ Real.log (2 * (X : ℝ)) * (r + 1 : ℝ) :=
      mul_nonneg (le_of_lt (Real.log_pos h1X))
        (add_nonneg (Nat.cast_nonneg r) zero_le_one)
    exact mul_le_mul (hpre'.trans hpreexp) hexp
      (pow_nonneg (le_of_lt hbasepos) _) (Real.exp_nonneg _)
  have hsumexp : Real.exp (ℓ ^ 2) * Real.exp (4 * Cκ * ℓ ^ 2) =
      Real.exp (ahlCombExpConst κ d0 * ℓ ^ 2) := by
    rw [← Real.exp_add]
    simp only [ahlCombExpConst, Cκ]
    ring_nf
  exact hprod.trans_eq hsumexp

/-! ### Remainder bound -/

/-- Paper remainder: after subtracting Kuperberg at `2X` and `X`,
`N_X ≫ X / log(2X)` from the one-point case, and `L,r,S` of the
fixed profile, one has
`ℰ_X ≤ C exp(O_{κ,d0}((log log X)^2)) X^{-ε}`. -/
theorem ahlBudget_le_kuperberg_loglog_sq {ε K κ d0 : ℝ}
    (hK : 0 ≤ K) (hκ : 0 < κ) (hd0 : 0 < d0)
    (hbound : ∀ (x : ℕ) (E : Finset ℕ),
      16 ≤ x →
        (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
          (E.card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 →
            hlAdmissible E →
              |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤ K * (x : ℝ) ^ (1 - ε))
    {X : ℕ} (hfit : ProfileFits κ d0 X)
    (hN : (X : ℝ) / (2 * Real.log (2 * (X : ℝ))) ≤ (windowNX X : ℝ))
    (hκlog : 1 ≤ κ * Real.log (Real.log (X : ℝ)))
    (hsq : 2 * (Real.log (X : ℝ) ^ 2 + 1) ≤ Real.log (X : ℝ) ^ 4)
    (hpre : Real.log 2 + Real.log (Real.log (X : ℝ)) +
        Real.log ((1 + d0) * (2 * κ + 1) + 3) +
        Real.log (Real.log (Real.log (X : ℝ))) ≤
      Real.log (Real.log (X : ℝ)) ^ 2) :
    ahlBudget κ d0 X ≤
      (2 * K * ((2 : ℝ) ^ (1 - ε) + 1)) *
        Real.exp (ahlCombExpConst κ d0 * Real.log (Real.log (X : ℝ)) ^ 2) *
        (X : ℝ) ^ (-ε) := by
  have henv := ahlBudget_le_kuperberg_envelope hK hbound hfit hN
  have hcomb := comb_factor_le_exp_loglog_sq hκ hd0 hfit hκlog hsq hpre
  have hxpos : 0 < (X : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 16) hfit.1)
  have hrpow : 0 ≤ (X : ℝ) ^ (-ε) := Real.rpow_nonneg hxpos.le _
  have hC0 : 0 ≤ 2 * K * ((2 : ℝ) ^ (1 - ε) + 1) := by
    have : 0 < (2 : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos (by norm_num) _
    exact mul_nonneg (mul_nonneg (by norm_num) hK) (add_nonneg this.le (by norm_num))
  set C := (2 : ℝ) * K * ((2 : ℝ) ^ (1 - ε) + 1)
  set comb :=
    Real.log (2 * (X : ℝ)) * (profileR (profileL κ X) d0 + 1 : ℝ) *
      (2 * ((profileS κ X : ℝ) + 1)) ^ profileR (profileL κ X) d0
  set expv :=
    Real.exp (ahlCombExpConst κ d0 * Real.log (Real.log (X : ℝ)) ^ 2)
  have hLHS :
      (2 * K * ((2 : ℝ) ^ (1 - ε) + 1) *
          Real.log (2 * (X : ℝ)) *
          (profileR (profileL κ X) d0 + 1 : ℝ) *
          (2 * ((profileS κ X : ℝ) + 1)) ^ profileR (profileL κ X) d0) *
        (X : ℝ) ^ (-ε) =
      (C * comb) * (X : ℝ) ^ (-ε) := by
    dsimp [C, comb]
    ring
  have hRHS :
      (2 * K * ((2 : ℝ) ^ (1 - ε) + 1)) *
        Real.exp (ahlCombExpConst κ d0 * Real.log (Real.log (X : ℝ)) ^ 2) *
        (X : ℝ) ^ (-ε) =
      (C * expv) * (X : ℝ) ^ (-ε) := by
    dsimp [C, expv]
  have hscale : (C * comb) * (X : ℝ) ^ (-ε) ≤ (C * expv) * (X : ℝ) ^ (-ε) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomb hC0) hrpow
  rw [hLHS] at henv
  exact henv.trans (hRHS ▸ hscale)

/-! ### Limit `AHL` -/

theorem kuperberg_implies_AHL (hK : KuperbergConj13) {κ d0 : ℝ}
    (hκ : 0 < κ) (hd0 : 0 < d0) : AHL κ d0 := by
  obtain ⟨ε, K, hε, hKpos, hbound⟩ := hK
  set C := (2 : ℝ) * K * ((2 : ℝ) ^ (1 - ε) + 1)
  set A := ahlCombExpConst κ d0
  have hA : 0 ≤ A := ahlCombExpConst_nonneg hκ hd0
  have hCκ : 0 < (1 + d0) * (2 * κ + 1) + 3 := ahlCombFactor_pos hκ hd0
  have hupper : Tendsto (fun X : ℕ =>
      C * Real.exp (A * Real.log (Real.log (X : ℝ)) ^ 2) * (X : ℝ) ^ (-ε))
      atTop (nhds 0) := by
    have hf := tendsto_exp_loglog_sq_mul_rpow_neg hA hε
    have hnat := hf.comp tendsto_natCast_atTop_atTop
    have hCmul := tendsto_const_mul_nhds_zero (c := C) hnat
    refine hCmul.congr' ?_
    exact Eventually.of_forall fun X => by
      dsimp [Function.comp]
      exact (mul_assoc C (Real.exp (A * Real.log (Real.log (X : ℝ)) ^ 2))
        ((X : ℝ) ^ (-ε))).symm
  have hle : ∀ᶠ X : ℕ in atTop,
      ahlBudget κ d0 X ≤
        C * Real.exp (A * Real.log (Real.log (X : ℝ)) ^ 2) * (X : ℝ) ^ (-ε) := by
    filter_upwards [eventually_profileFits hκ hd0,
      eventually_windowNX_ge_half hε hKpos hbound,
      eventually_one_le_kappa_loglog hκ,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        eventually_two_sq_succ_le_pow4,
      ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
        tendsto_natCast_atTop_atTop).eventually
        (eventually_log_sum_le_sq hCκ)] with X hfit hN hκlog hsq hpre
    have hbound' := ahlBudget_le_kuperberg_loglog_sq hKpos.le hκ hd0 hbound
      hfit hN hκlog hsq hpre
    simpa [C, A] using hbound'
  exact squeeze_zero'
    (Eventually.of_forall (ahlBudget_nonneg κ d0)) hle hupper

theorem kuperbergImpliesAHL_holds : KuperbergImpliesAHL :=
  fun hK _ _ hκ hd0 => kuperberg_implies_AHL hK hκ hd0

end

end PrimeGapNormality.Prime
