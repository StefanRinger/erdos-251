import PrimeGapNormality.Prime.EulerProd
import Mathlib.Algebra.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Sieve-cutoff calibration `V(y)⁻¹ / G → 1`

ModelConcentration leaves open the paper calibration `V(y)⁻¹ / G → 1`.
If `y` is a sieve cutoff for `t` (least prime with `V(y) ≤ 1 / log t`)
and `G = log t` (equivalently `t = e^G`), the exact jump

  `(1 - 1/y) / G < V(y) ≤ 1 / G`

gives `V(y) ≍ 1/G` with absolute constants from `y ≥ 16`, so
`1 / (G V(y))` is bounded. Combined with `y ≥ t^{e^{-30}}`, one has
`V(y)⁻¹ / G → 1` along any such cutoff.

No Mertens constant `e^{-γ}` is used or claimed. The weak two-sided
product `e^{-30} / log y ≤ V(y) ≤ 1 / log y` is recorded at the cutoff,
but the `1/G` comparison comes from the jump, not from Mertens.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` Appendix calibration;
`EulerProd.isSieveCutoff_jump`, `isSieveCutoff_rpow`, `eulerProd_two_sided`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Filter
open scoped Topology

set_option maxHeartbeats 800000

/-! ### Elementary comparisons -/

private theorem one_lt_of_exp_sixteen_le {t : ℝ} (ht : Real.exp 16 ≤ t) :
    1 < t :=
  lt_of_lt_of_le
    (lt_trans (by norm_num : (1 : ℝ) < 2)
      (lt_trans Real.exp_one_gt_two
        (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16))))
    ht

private theorem log_t_pos {t : ℝ} (ht : Real.exp 16 ≤ t) :
    0 < Real.log t :=
  Real.log_pos (one_lt_of_exp_sixteen_le ht)

private theorem inv_mul_eq_div (a b : ℝ) : (a * b)⁻¹ = a⁻¹ / b := by
  rw [mul_inv, div_eq_mul_inv]

private theorem one_div_mul_eq_inv_div (G V : ℝ) : 1 / (G * V) = V⁻¹ / G := by
  rw [one_div, mul_comm G, inv_mul_eq_div]

private theorem one_sub_inv_eq {y : ℕ} (hy : (1 : ℝ) < y) :
    1 - (y : ℝ)⁻¹ = ((y : ℝ) - 1) / y := by
  have hy0 : (y : ℝ) ≠ 0 :=
    (lt_trans (by norm_num : (0 : ℝ) < 1) hy).ne'
  rw [inv_eq_one_div, one_sub_div hy0]

private theorem fifteen_div_sixteen_le_one_sub_inv {y : ℕ} (hy : 16 ≤ y) :
    (15 : ℝ) / 16 ≤ 1 - (y : ℝ)⁻¹ := by
  have hyR : (16 : ℝ) ≤ y := Nat.cast_le.mpr hy
  have hinv : (y : ℝ)⁻¹ ≤ (16 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num : (0 : ℝ) < 16) hyR
  have hsub : 1 - (16 : ℝ)⁻¹ ≤ 1 - (y : ℝ)⁻¹ := sub_le_sub_left hinv 1
  have hval : (1 : ℝ) - (16 : ℝ)⁻¹ = 15 / 16 := by norm_num
  rwa [hval] at hsub

/-! ### Canonical cutoff -/

/-- Least sieve cutoff of `t`, or `2` if `t ≤ 1`. -/
noncomputable def sieveCutoff (t : ℝ) : ℕ :=
  if ht : 1 < t then Classical.choose (exists_isSieveCutoff ht) else 2

theorem sieveCutoff_spec {t : ℝ} (ht : 1 < t) :
    IsSieveCutoff t (sieveCutoff t) := by
  simp only [sieveCutoff, dif_pos ht]
  exact Classical.choose_spec (exists_isSieveCutoff ht)

/-! ### Jump in the gap scale `G = log t` -/

/-- Paper jump in multiplicative form: `(1 - 1/y) < V(y) log t ≤ 1`. -/
theorem isSieveCutoff_mul_log {t : ℝ} {y : ℕ} (ht : Real.exp 16 ≤ t)
    (hy : IsSieveCutoff t y) :
    1 - (y : ℝ)⁻¹ < eulerProd y * Real.log t ∧
      eulerProd y * Real.log t ≤ 1 := by
  have hlog := log_t_pos ht
  have hjump := isSieveCutoff_jump ht hy
  have hle : eulerProd y ≤ 1 / Real.log t := hy.2.1
  constructor
  · have hmul := mul_lt_mul_of_pos_right hjump hlog
    have hrew : (1 - (y : ℝ)⁻¹) / Real.log t * Real.log t =
        1 - (y : ℝ)⁻¹ :=
      div_mul_cancel₀ _ hlog.ne'
    rwa [hrew] at hmul
  · have hmul := mul_le_mul_of_nonneg_right hle hlog.le
    have hrew : 1 / Real.log t * Real.log t = 1 :=
      div_mul_cancel₀ _ hlog.ne'
    rwa [hrew] at hmul

/-- Two-sided comparison `V(y) ≍ 1/G` with `G = log t`. The lower
constant `15/16` uses only `y ≥ 16`, not Mertens. -/
theorem isSieveCutoff_eulerProd_asymp {t : ℝ} {y : ℕ} (ht : Real.exp 16 ≤ t)
    (hy : IsSieveCutoff t y) :
    (15 / 16) / Real.log t < eulerProd y ∧
      eulerProd y ≤ 1 / Real.log t := by
  have hy16 := isSieveCutoff_ge_sixteen ht hy
  have hlog := log_t_pos ht
  have hfac := fifteen_div_sixteen_le_one_sub_inv hy16
  have hjump := isSieveCutoff_jump ht hy
  constructor
  · have hle :
        (15 / 16) / Real.log t ≤ (1 - (y : ℝ)⁻¹) / Real.log t :=
      div_le_div_of_nonneg_right hfac hlog.le
    exact hle.trans_lt hjump
  · exact hy.2.1

/-- Weak Euler-product bounds at a cutoff, from `eulerProd_two_sided`.
Not a Mertens asymptotic. -/
theorem isSieveCutoff_eulerProd_two_sided {t : ℝ} {y : ℕ}
    (ht : Real.exp 16 ≤ t) (hy : IsSieveCutoff t y) :
    eulerProdLowerConst / Real.log y ≤ eulerProd y ∧
      eulerProd y ≤ 1 / Real.log y := by
  have hy16 := isSieveCutoff_ge_sixteen ht hy
  exact eulerProd_two_sided (Nat.cast_le.mpr hy16)

/-- Paper: `log y ≥ e^{-30} log t`, from `y ≥ t^{e^{-30}}`. -/
theorem isSieveCutoff_log_ge {t : ℝ} {y : ℕ} (ht : Real.exp 16 ≤ t)
    (hy : IsSieveCutoff t y) :
    eulerProdLowerConst * Real.log t ≤ Real.log y := by
  have ht1 := one_lt_of_exp_sixteen_le ht
  have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht1
  have hy16 := isSieveCutoff_ge_sixteen ht hy
  have hy0 : (0 : ℝ) < y :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 16) hy16)
  have hrpow := isSieveCutoff_rpow ht hy
  have hlog : Real.log (t ^ eulerProdLowerConst) ≤ Real.log y :=
    Real.log_le_log (Real.rpow_pos_of_pos ht0 _) hrpow
  rwa [Real.log_rpow ht0] at hlog

/-! ### `t = e^G` forms -/

/-- If `y` is a sieve cutoff for `t = e^G` with `G ≥ 16`, then
`(1 - 1/y) < V(y) G ≤ 1`. -/
theorem isSieveCutoff_exp_mul {G : ℝ} {y : ℕ} (hG : 16 ≤ G)
    (hy : IsSieveCutoff (Real.exp G) y) :
    1 - (y : ℝ)⁻¹ < eulerProd y * G ∧ eulerProd y * G ≤ 1 := by
  have ht : Real.exp 16 ≤ Real.exp G := Real.exp_le_exp.mpr hG
  have h := isSieveCutoff_mul_log ht hy
  rwa [Real.log_exp] at h

/-- `V(y) ≍ 1/G` at a cutoff of `e^G`. -/
theorem isSieveCutoff_exp_asymp {G : ℝ} {y : ℕ} (hG : 16 ≤ G)
    (hy : IsSieveCutoff (Real.exp G) y) :
    (15 / 16) / G < eulerProd y ∧ eulerProd y ≤ 1 / G := by
  have ht : Real.exp 16 ≤ Real.exp G := Real.exp_le_exp.mpr hG
  have h := isSieveCutoff_eulerProd_asymp ht hy
  rwa [Real.log_exp] at h

/-! ### Boundedness of `1 / (G V(y))` -/

/-- `1 ≤ V(y)⁻¹ / log t < 16/15`. -/
theorem isSieveCutoff_inv_mul_log_bounded {t : ℝ} {y : ℕ}
    (ht : Real.exp 16 ≤ t) (hy : IsSieveCutoff t y) :
    1 ≤ (eulerProd y)⁻¹ / Real.log t ∧
      (eulerProd y)⁻¹ / Real.log t < 16 / 15 := by
  have hlog := log_t_pos ht
  have hV := eulerProd_pos (y : ℝ)
  have hmul := isSieveCutoff_mul_log ht hy
  have hVG : 0 < eulerProd y * Real.log t := mul_pos hV hlog
  have hrew : (eulerProd y * Real.log t)⁻¹ = (eulerProd y)⁻¹ / Real.log t :=
    inv_mul_eq_div _ _
  constructor
  · have h1 : 1 ≤ (eulerProd y * Real.log t)⁻¹ :=
      (one_le_inv₀ hVG).mpr hmul.2
    rwa [hrew] at h1
  · have hasymp := isSieveCutoff_eulerProd_asymp ht hy
    have hlt : (15 : ℝ) / 16 < eulerProd y * Real.log t := by
      have hmul' := mul_lt_mul_of_pos_right hasymp.1 hlog
      have hcancel : (15 / 16) / Real.log t * Real.log t = (15 : ℝ) / 16 :=
        div_mul_cancel₀ _ hlog.ne'
      rwa [hcancel] at hmul'
    have hinv : (eulerProd y * Real.log t)⁻¹ < ((15 : ℝ) / 16)⁻¹ :=
      inv_strictAnti₀ (by norm_num : (0 : ℝ) < 15 / 16) hlt
    have hval : ((15 : ℝ) / 16)⁻¹ = 16 / 15 := by norm_num
    rwa [hrew, hval] at hinv

/-- Hence `1 / (log t · V(y))` is bounded. -/
theorem isSieveCutoff_one_div_log_mul_bounded {t : ℝ} {y : ℕ}
    (ht : Real.exp 16 ≤ t) (hy : IsSieveCutoff t y) :
    1 ≤ 1 / (Real.log t * eulerProd y) ∧
      1 / (Real.log t * eulerProd y) < 16 / 15 := by
  have hb := isSieveCutoff_inv_mul_log_bounded ht hy
  rw [one_div_mul_eq_inv_div (Real.log t) (eulerProd y)]
  exact hb

/-- Same bound with explicit gap scale `G = log t`. -/
theorem isSieveCutoff_inv_div_G {t G : ℝ} {y : ℕ} (hG : G = Real.log t)
    (ht : Real.exp 16 ≤ t) (hy : IsSieveCutoff t y) :
    1 ≤ (eulerProd y)⁻¹ / G ∧ (eulerProd y)⁻¹ / G < 16 / 15 := by
  rw [hG]
  exact isSieveCutoff_inv_mul_log_bounded ht hy

/-- `1 ≤ 1 / (G V(y)) < 16/15` when `y` cuts off `e^G`. -/
theorem isSieveCutoff_exp_one_div_bounded {G : ℝ} {y : ℕ} (hG : 16 ≤ G)
    (hy : IsSieveCutoff (Real.exp G) y) :
    1 ≤ 1 / (G * eulerProd y) ∧ 1 / (G * eulerProd y) < 16 / 15 := by
  have ht : Real.exp 16 ≤ Real.exp G := Real.exp_le_exp.mpr hG
  have hb := isSieveCutoff_inv_mul_log_bounded ht hy
  rw [Real.log_exp] at hb
  rw [one_div_mul_eq_inv_div G (eulerProd y)]
  exact hb

/-- ModelConcentration hypothesis `V(y) G ≤ 2`, actually `≤ 1`. -/
theorem isSieveCutoff_eulerProdNat_mul_log_le {t : ℝ} {y : ℕ}
    (ht : Real.exp 16 ≤ t) (hy : IsSieveCutoff t y) :
    eulerProdNat y * Real.log t ≤ 1 := by
  have h := (isSieveCutoff_mul_log ht hy).2
  rw [← eulerProd_coe_nat]
  exact h

theorem isSieveCutoff_eulerProdNat_mul_G_le_two {t G : ℝ} {y : ℕ}
    (hG : G = Real.log t) (ht : Real.exp 16 ≤ t) (hy : IsSieveCutoff t y) :
    eulerProdNat y * G ≤ 2 := by
  have h := isSieveCutoff_eulerProdNat_mul_log_le ht hy
  rw [hG]
  exact le_trans h (by norm_num)

/-! ### Pointwise calibration error -/

/-- `|V(y)⁻¹ / log t - 1| < 1 / (y - 1)`. -/
theorem isSieveCutoff_calib_lt {t : ℝ} {y : ℕ} (ht : Real.exp 16 ≤ t)
    (hy : IsSieveCutoff t y) :
    |(eulerProd y)⁻¹ / Real.log t - 1| < ((y : ℝ) - 1)⁻¹ := by
  have hlog := log_t_pos ht
  have hV := eulerProd_pos (y : ℝ)
  have hmul := isSieveCutoff_mul_log ht hy
  have hVG : 0 < eulerProd y * Real.log t := mul_pos hV hlog
  have hy16 := isSieveCutoff_ge_sixteen ht hy
  have hy1 : (1 : ℝ) < y :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 16) hy16)
  have hy1pos : (0 : ℝ) < (y : ℝ) - 1 := sub_pos.mpr hy1
  have hrew : (eulerProd y * Real.log t)⁻¹ = (eulerProd y)⁻¹ / Real.log t :=
    inv_mul_eq_div _ _
  have h1 : 1 ≤ (eulerProd y)⁻¹ / Real.log t := by
    have : 1 ≤ (eulerProd y * Real.log t)⁻¹ :=
      (one_le_inv₀ hVG).mpr hmul.2
    rwa [hrew] at this
  have hnn : 0 ≤ (eulerProd y)⁻¹ / Real.log t - 1 := sub_nonneg.mpr h1
  have hfac : 0 < 1 - (y : ℝ)⁻¹ := one_sub_inv_pos hy.1
  have hlt : (eulerProd y * Real.log t)⁻¹ < (1 - (y : ℝ)⁻¹)⁻¹ :=
    inv_strictAnti₀ hfac hmul.1
  have hiden : (1 - (y : ℝ)⁻¹)⁻¹ = (y : ℝ) / ((y : ℝ) - 1) := by
    rw [one_sub_inv_eq hy1, inv_div]
  have hquot :
      (eulerProd y)⁻¹ / Real.log t < (y : ℝ) / ((y : ℝ) - 1) := by
    rwa [hrew, hiden] at hlt
  have hsub :
      (eulerProd y)⁻¹ / Real.log t - 1 <
        (y : ℝ) / ((y : ℝ) - 1) - 1 :=
    sub_lt_sub_right hquot 1
  have hring : (y : ℝ) / ((y : ℝ) - 1) - 1 = ((y : ℝ) - 1)⁻¹ := by
    rw [div_sub_one hy1pos.ne', sub_sub_cancel (y : ℝ) (1 : ℝ), one_div]
  rw [abs_of_nonneg hnn]
  exact hsub.trans_eq hring

/-- Uniform bound `|V(y)⁻¹ / G - 1| < 1/15` from `y ≥ 16`. -/
theorem isSieveCutoff_calib_lt_inv_fifteen {t : ℝ} {y : ℕ}
    (ht : Real.exp 16 ≤ t) (hy : IsSieveCutoff t y) :
    |(eulerProd y)⁻¹ / Real.log t - 1| < 1 / 15 := by
  have hy16 := isSieveCutoff_ge_sixteen ht hy
  have hmain := isSieveCutoff_calib_lt ht hy
  have hyR : (16 : ℝ) ≤ y := Nat.cast_le.mpr hy16
  have hy1 : (15 : ℝ) ≤ (y : ℝ) - 1 := by
    have h : (16 : ℝ) - 1 ≤ (y : ℝ) - 1 := sub_le_sub_right hyR 1
    have heq : (16 : ℝ) - 1 = 15 := by norm_num
    rwa [heq] at h
  have hinv : ((y : ℝ) - 1)⁻¹ ≤ (15 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num : (0 : ℝ) < 15) hy1
  have : |(eulerProd y)⁻¹ / Real.log t - 1| < (15 : ℝ)⁻¹ :=
    hmain.trans_le hinv
  exact lt_of_lt_of_eq this (inv_eq_one_div (15 : ℝ))

/-! ### Limits -/

theorem tendsto_isSieveCutoff_atTop {y : ℝ → ℕ}
    (hy : ∀ᶠ t : ℝ in atTop, IsSieveCutoff t (y t)) :
    Tendsto (fun t : ℝ => (y t : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_rpow_atTop eulerProdLowerConst_pos)
  filter_upwards [hy, eventually_ge_atTop (Real.exp 16)] with t hyt ht
  exact isSieveCutoff_rpow ht hyt

theorem tendsto_isSieveCutoff_calib {y : ℝ → ℕ}
    (hy : ∀ᶠ t : ℝ in atTop, IsSieveCutoff t (y t)) :
    Tendsto (fun t : ℝ => |(eulerProd (y t))⁻¹ / Real.log t - 1|)
      atTop (nhds 0) := by
  have hy1 : Tendsto (fun t : ℝ => (y t : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (tendsto_isSieveCutoff_atTop hy)
  have hinv : Tendsto (fun t : ℝ => ((y t : ℝ) - 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hy1
  refine squeeze_zero' ?_ ?_ hinv
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [hy, eventually_ge_atTop (Real.exp 16)] with t hyt ht
    exact (isSieveCutoff_calib_lt ht hyt).le

/-- Paper calibration: `V(y(t))⁻¹ / log t → 1` along any sieve cutoff. -/
theorem tendsto_isSieveCutoff_inv_div_log {y : ℝ → ℕ}
    (hy : ∀ᶠ t : ℝ in atTop, IsSieveCutoff t (y t)) :
    Tendsto (fun t : ℝ => (eulerProd (y t))⁻¹ / Real.log t) atTop (nhds 1) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h := tendsto_isSieveCutoff_calib hy
  refine h.congr fun t => ?_
  exact (Real.dist_eq _ _).symm

theorem tendsto_sieveCutoff_atTop :
    Tendsto (fun t : ℝ => (sieveCutoff t : ℝ)) atTop atTop :=
  tendsto_isSieveCutoff_atTop
    ((eventually_gt_atTop (1 : ℝ)).mono fun _ ht => sieveCutoff_spec ht)

/-- Concrete real limit: `V(y(t))⁻¹ / log t → 1` for the least cutoff. -/
theorem tendsto_sieveCutoff_inv_div_log :
    Tendsto (fun t : ℝ => (eulerProd (sieveCutoff t))⁻¹ / Real.log t)
      atTop (nhds 1) :=
  tendsto_isSieveCutoff_inv_div_log
    ((eventually_gt_atTop (1 : ℝ)).mono fun _ ht => sieveCutoff_spec ht)

/-- Concrete sequence in the gap scale: `V(y(e^G))⁻¹ / G → 1`. -/
theorem tendsto_sieveCutoff_exp_inv_div :
    Tendsto (fun G : ℝ => (eulerProd (sieveCutoff (Real.exp G)))⁻¹ / G)
      atTop (nhds 1) := by
  have h := tendsto_sieveCutoff_inv_div_log.comp Real.tendsto_exp_atTop
  refine h.congr fun G => ?_
  simp only [Function.comp_apply, Real.log_exp]

/-- Discrete sequence: `V(y(e^n))⁻¹ / n → 1`. -/
theorem tendsto_sieveCutoff_exp_nat_inv_div :
    Tendsto (fun n : ℕ =>
        (eulerProd (sieveCutoff (Real.exp (n : ℝ))))⁻¹ / (n : ℝ))
      atTop (nhds 1) :=
  tendsto_sieveCutoff_exp_inv_div.comp tendsto_natCast_atTop_atTop

end PrimeGapNormality.Prime
