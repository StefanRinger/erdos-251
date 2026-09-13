import PrimeGapNormality.Prime.ExactRootMix
import PrimeGapNormality.Prime.EulerProd
import PrimeGapNormality.Prime.MixRiemann
import PrimeGapNormality.Prime.SieveCutoffCal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic

/-!
# `ζ_X = Z_X / N_X → 1` from qualitative PNT

`MixRiemann.MixZetaTendstoOne` is the named Prop `Tendsto mixZeta atTop (nhds 1)`.
This file does **not** prove `MixZetaTendstoOne` unconditionally (that would
smuggle PNT into a closed theorem). Mix weights remain `mixWeightV`
(`V(y_t)`); comparison with `f_1(t) = 1/log t` is only through
`mixLogPow (v := 1)`.

On a dyadic window, qualitative `π(⌊x⌋) / (x/log x) → 1` gives
`windowNX X ∼ X / log X`. This is the same statement as
`IndexPassageFromPNT.PrimeCountingAsymp`, inlined as
`MixPrimeCountingAsymp` so this leaf does not import both
`ActualRootLaw.actualBernoulliThin` and `Coupling.bernoulliThin`.
The cutoff jump `(15/16)/log t < V(y_t) ≤ 1/log t` and the calibration
`V(y_t) log t → 1` squeeze `∑ V(y_t)` against `∑ 1/log t ∼ ∫_X^{2X} dt/log t
∼ X / log X`. `|ζ-1|` is not multiplied by `exp(C L)`.

Source: MixRiemann comment on `MixZetaTendstoOne`;
`rounds/round106/09_gpt_v04_lean_audit_and_grok_order.md` Paket 2.
Contract: API
Audit: GREEN
-/

open Finset
open Filter
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000

/-- Same `Tendsto` as `IndexPassageFromPNT.PrimeCountingAsymp`. Inlined
because this module already imports `ActualRootLaw.actualBernoulliThin`
via `ExactRootMix`, while `IndexPassageFromPNT` pulls
`Coupling.bernoulliThin`. The two names are now distinct; this inlining
is only to avoid a lake of `IndexPassageFromPNT` in this leaf. -/
def MixPrimeCountingAsymp : Prop :=
  Tendsto (fun x : ℝ =>
      (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x))
    atTop (nhds 1)

/-! ### Local casts (copied from MixRiemann; that file is not edited) -/

private theorem two_mul_cast (X : ℕ) :
    ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := by
  rw [Nat.cast_mul]
  rfl

private theorem mixWindow_le (X : ℕ) :
    (X : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
  exact_mod_cast (Nat.le_mul_of_pos_left X (by norm_num : (0 : ℕ) < 2))

private theorem one_lt_of_two_le {X : ℕ} (hX : 2 ≤ X) : (1 : ℝ) < X :=
  lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (Nat.cast_le.mpr hX)

private theorem one_lt_two_mul {X : ℕ} (hX : 2 ≤ X) :
    (1 : ℝ) < ((2 * X : ℕ) : ℝ) := by
  have h4 : (4 : ℕ) ≤ 2 * X := Nat.mul_le_mul_left 2 hX
  have h14 : (1 : ℕ) < (4 : ℕ) :=
    lt_trans (Nat.lt_succ_self (1 : ℕ))
      (lt_trans (Nat.lt_succ_self (2 : ℕ)) (Nat.lt_succ_self (3 : ℕ)))
  exact_mod_cast lt_of_lt_of_le h14 h4

private theorem one_lt_two_mul_real {X : ℕ} (hX : 2 ≤ X) :
    (1 : ℝ) < 2 * (X : ℝ) := by
  rw [← two_mul_cast]
  exact one_lt_two_mul hX

private theorem one_lt_of_exp_sixteen_le {t : ℝ} (ht : Real.exp 16 ≤ t) :
    1 < t :=
  lt_of_lt_of_le
    (lt_trans (by norm_num : (1 : ℝ) < 2)
      (lt_trans Real.exp_one_gt_two
        (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16))))
    ht

private theorem X_pos {X : ℕ} (hX : 2 ≤ X) : (0 : ℝ) < X :=
  Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hX)

private theorem log_X_pos {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log X :=
  Real.log_pos (one_lt_of_two_le hX)

private theorem log_two_mul_pos {X : ℕ} (hX : 2 ≤ X) :
    0 < Real.log (2 * (X : ℝ)) :=
  Real.log_pos (one_lt_two_mul_real hX)

private theorem X_div_log_ne {X : ℕ} (hX : 2 ≤ X) :
    (X : ℝ) / Real.log X ≠ 0 :=
  div_ne_zero (X_pos hX).ne' (log_X_pos hX).ne'

/-! ### Degree-one comparison `f_1(t) = 1 / log t` -/

private theorem mixLogPow_one_eq {t : ℝ} (_ht : 1 < t) :
    mixLogPow 1 t = (Real.log t)⁻¹ := by
  unfold mixLogPow
  rw [Nat.cast_one, Real.rpow_neg_one]

private theorem one_lt_of_mem_mixScale {X t : ℕ} (hX : 2 ≤ X)
    (ht : t ∈ mixScale X) : (1 : ℝ) < t := by
  have ht' := mem_Ioc.mp ht
  have ht2 : (2 : ℕ) ≤ t := le_trans hX (Nat.le_of_lt ht'.1)
  exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (Nat.cast_le.mpr ht2)

private theorem mixScale_card (X : ℕ) : (mixScale X).card = X := by
  unfold mixScale
  rw [Nat.card_Ioc]
  omega

private theorem mixScale_nonempty {X : ℕ} (hX : 2 ≤ X) :
    (mixScale X).Nonempty :=
  ⟨2 * X, mem_Ioc.mpr ⟨by omega, le_rfl⟩⟩

private theorem mixLogPowSum_pos {X : ℕ} (hX : 2 ≤ X) :
    0 < mixLogPowSum X 1 :=
  sum_pos (fun _ ht => mixLogPow_pos 1 (one_lt_of_mem_mixScale hX ht))
    (mixScale_nonempty hX)

/-! ### Cutoff jump `V(y_t) ≍ 1 / log t` -/

private theorem mixWeightV_eq_eulerProd (t : ℕ) :
    mixWeightV t = eulerProd (sieveCutoff (t : ℝ)) :=
  (eulerProd_coe_nat _).symm

private theorem two_le_of_exp_sixteen_le {X : ℕ} (hXexp : Real.exp 16 ≤ (X : ℝ)) :
    2 ≤ X := by
  have h2 : (2 : ℝ) < Real.exp 16 :=
    lt_trans Real.exp_one_gt_two
      (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16))
  have h2X : (2 : ℝ) ≤ X := (lt_of_lt_of_le h2 hXexp).le
  exact_mod_cast h2X

/-- Paper jump, upper side: `V(y_t) ≤ 1 / log t` for `t ≥ exp 16`. -/
theorem mixWeightV_le_mixLogPow {t : ℕ} (ht : Real.exp 16 ≤ (t : ℝ)) :
    mixWeightV t ≤ mixLogPow 1 t := by
  have ht1 := one_lt_of_exp_sixteen_le ht
  have hy := sieveCutoff_spec ht1
  have hasymp := isSieveCutoff_eulerProd_asymp ht hy
  rw [mixWeightV_eq_eulerProd, mixLogPow_one_eq ht1, inv_eq_one_div]
  exact hasymp.2

/-- Paper jump, lower side: `(15/16) / log t < V(y_t)` for `t ≥ exp 16`. -/
theorem fifteen_sixteenths_mixLogPow_lt_mixWeightV {t : ℕ}
    (ht : Real.exp 16 ≤ (t : ℝ)) :
    ((15 : ℝ) / 16) * mixLogPow 1 t < mixWeightV t := by
  have ht1 := one_lt_of_exp_sixteen_le ht
  have hy := sieveCutoff_spec ht1
  have hasymp := isSieveCutoff_eulerProd_asymp ht hy
  have hrew : ((15 : ℝ) / 16) * mixLogPow 1 t = (15 / 16) / Real.log t := by
    rw [mixLogPow_one_eq ht1]
    exact (div_eq_mul_inv ((15 : ℝ) / 16) (Real.log t)).symm
  rw [mixWeightV_eq_eulerProd, hrew]
  exact hasymp.1

theorem mixZ_le_mixLogPowSum {X : ℕ} (hXexp : Real.exp 16 ≤ (X : ℝ)) :
    mixZ X ≤ mixLogPowSum X 1 := by
  unfold mixZ mixLogPowSum
  refine sum_le_sum fun t ht => ?_
  have ht' := mem_Ioc.mp ht
  have htX : (X : ℝ) ≤ t := Nat.cast_le.mpr (Nat.le_of_lt ht'.1)
  exact mixWeightV_le_mixLogPow (le_trans hXexp htX)

theorem mixZ_gt_fifteen_sixteenths_mixLogPowSum {X : ℕ}
    (hXexp : Real.exp 16 ≤ (X : ℝ)) :
    ((15 : ℝ) / 16) * mixLogPowSum X 1 < mixZ X := by
  have hX := two_le_of_exp_sixteen_le hXexp
  have hle : ∀ t ∈ mixScale X, ((15 : ℝ) / 16) * mixLogPow 1 t ≤ mixWeightV t := by
    intro t ht
    have ht' := mem_Ioc.mp ht
    have htX : (X : ℝ) ≤ t := Nat.cast_le.mpr (Nat.le_of_lt ht'.1)
    exact (fifteen_sixteenths_mixLogPow_lt_mixWeightV (le_trans hXexp htX)).le
  have hlt : ∃ t ∈ mixScale X, ((15 : ℝ) / 16) * mixLogPow 1 t < mixWeightV t := by
    obtain ⟨t, ht⟩ := mixScale_nonempty hX
    refine ⟨t, ht, ?_⟩
    have ht' := mem_Ioc.mp ht
    have htX : (X : ℝ) ≤ t := Nat.cast_le.mpr (Nat.le_of_lt ht'.1)
    exact fifteen_sixteenths_mixLogPow_lt_mixWeightV (le_trans hXexp htX)
  have hsum := sum_lt_sum hle hlt
  have hfactor :
      ∑ t ∈ mixScale X, ((15 : ℝ) / 16) * mixLogPow 1 t =
        ((15 : ℝ) / 16) * mixLogPowSum X 1 := by
    unfold mixLogPowSum
    rw [← mul_sum]
  unfold mixZ
  rwa [hfactor] at hsum

/-! ### Riemann: `∑_{X<t≤2X} 1/log t ∼ X / log X` -/

private theorem mixLogPowSum_le_X_div_log {X : ℕ} (hX : 2 ≤ X) :
    mixLogPowSum X 1 ≤ (X : ℝ) / Real.log X := by
  have hfX : mixLogPow 1 X = (Real.log X)⁻¹ := mixLogPow_one_eq (one_lt_of_two_le hX)
  have hanti := mixLogPow_antitoneOn (v := 1) hX
  have hle : ∀ t ∈ mixScale X, mixLogPow 1 t ≤ mixLogPow 1 X := by
    intro t ht
    have ht' := mem_Ioc.mp ht
    have htR : (t : ℝ) ∈ Set.Icc (X : ℝ) ((2 * X : ℕ) : ℝ) :=
      ⟨Nat.cast_le.mpr (Nat.le_of_lt ht'.1), Nat.cast_le.mpr ht'.2⟩
    have hXR : (X : ℝ) ∈ Set.Icc (X : ℝ) ((2 * X : ℕ) : ℝ) :=
      ⟨le_rfl, mixWindow_le X⟩
    exact hanti hXR htR (Nat.cast_le.mpr (Nat.le_of_lt ht'.1))
  have hsum := sum_le_sum hle
  have hconst : ∑ t ∈ mixScale X, mixLogPow 1 X =
      ((mixScale X).card : ℝ) * mixLogPow 1 X := by
    rw [sum_const, nsmul_eq_mul]
  have : mixLogPowSum X 1 ≤ (X : ℝ) * mixLogPow 1 X := by
    unfold mixLogPowSum
    rw [hconst, mixScale_card] at hsum
    exact hsum
  rw [hfX, ← div_eq_mul_inv] at this
  exact this

private theorem mixLogPowSum_ge {X : ℕ} (hX : 2 ≤ X) :
    (X : ℝ) * mixLogPow 1 (2 * X) - mixLogPow 1 X ≤ mixLogPowSum X 1 := by
  have hriem := mixLogPow_riemann (v := 1) hX (by norm_num : (1 : ℕ) ≤ 1)
  have hge := mixLogPow_integral_ge (v := 1) hX
  linarith [hriem.2, hge]

private theorem mixLogPow_one_two_mul {X : ℕ} (hX : 2 ≤ X) :
    mixLogPow 1 (2 * X) = (Real.log (2 * (X : ℝ)))⁻¹ :=
  mixLogPow_one_eq (one_lt_two_mul_real hX)

private theorem mixLogPowSum_div_ge {X : ℕ} (hX : 2 ≤ X) :
    Real.log X / Real.log (2 * (X : ℝ)) - (1 : ℝ) / X ≤
      mixLogPowSum X 1 / ((X : ℝ) / Real.log X) := by
  have hx := X_pos hX
  have hL := log_X_pos hX
  have hL2 := log_two_mul_pos hX
  have hfX : mixLogPow 1 X = (Real.log X)⁻¹ := mixLogPow_one_eq (one_lt_of_two_le hX)
  have hf2 := mixLogPow_one_two_mul hX
  have hge := mixLogPowSum_ge hX
  have hden : (0 : ℝ) ≤ (X : ℝ) / Real.log X := div_nonneg hx.le hL.le
  have hrew :
      ((X : ℝ) * mixLogPow 1 (2 * X) - mixLogPow 1 X) /
          ((X : ℝ) / Real.log X) =
        Real.log X / Real.log (2 * (X : ℝ)) - (1 : ℝ) / X := by
    rw [hf2, hfX]
    field_simp [hx.ne', hL.ne', hL2.ne']
  have hle := div_le_div_of_nonneg_right hge hden
  rwa [hrew] at hle

private theorem mixLogPowSum_div_le_one {X : ℕ} (hX : 2 ≤ X) :
    mixLogPowSum X 1 / ((X : ℝ) / Real.log X) ≤ 1 := by
  have hden := div_pos (X_pos hX) (log_X_pos hX)
  have hle := mixLogPowSum_le_X_div_log hX
  exact (div_le_one hden).mpr hle

private theorem tendsto_log_div_log_two_mul :
    Tendsto (fun X : ℕ => Real.log X / Real.log (2 * (X : ℝ)))
      atTop (nhds 1) := by
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv : Tendsto (fun X : ℕ => Real.log 2 / Real.log X) atTop (nhds 0) := by
    have h0 : Tendsto (fun X : ℕ => (Real.log X)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hlog
    simpa [div_eq_mul_inv] using h0.const_mul (Real.log 2)
  have hadd : Tendsto (fun X : ℕ => (1 : ℝ) + Real.log 2 / Real.log X)
      atTop (nhds 1) := by
    simpa using Tendsto.add (tendsto_const_nhds (x := (1 : ℝ))) hinv
  have hinv1 : Tendsto (fun X : ℕ => ((1 : ℝ) + Real.log 2 / Real.log X)⁻¹)
      atTop (nhds 1) := by
    simpa using hadd.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  refine hinv1.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hlogX := log_X_pos hX
  have hlog2X : Real.log (2 * (X : ℝ)) = Real.log 2 + Real.log X :=
    Real.log_mul (by norm_num) (X_pos hX).ne'
  have hden : (1 : ℝ) + Real.log 2 / Real.log X =
      (Real.log X + Real.log 2) / Real.log X := by
    have hone : (1 : ℝ) = Real.log X / Real.log X := (div_self hlogX.ne').symm
    rw [hone, add_div]
  rw [hlog2X, hden, inv_div, add_comm]

private theorem tendsto_mixLogPowSum_div :
    Tendsto (fun X : ℕ => mixLogPowSum X 1 / ((X : ℝ) / Real.log X))
      atTop (nhds 1) := by
  have hlo : Tendsto (fun X : ℕ =>
      Real.log X / Real.log (2 * (X : ℝ)) - (1 : ℝ) / X) atTop (nhds 1) := by
    simpa using tendsto_log_div_log_two_mul.sub tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlo (tendsto_const_nhds (x := (1 : ℝ))) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact mixLogPowSum_div_ge hX
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact mixLogPowSum_div_le_one hX

/-! ### Calibration `V(y_t) log t → 1` -/

private theorem tendsto_eulerProd_sieveCutoff_mul_log :
    Tendsto (fun t : ℝ => eulerProd (sieveCutoff t) * Real.log t)
      atTop (nhds 1) := by
  have h := tendsto_sieveCutoff_inv_div_log
  have hinv : Tendsto (fun t : ℝ =>
      ((eulerProd (sieveCutoff t))⁻¹ / Real.log t)⁻¹) atTop (nhds 1) := by
    simpa using h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [inv_div, div_inv_eq_mul, mul_comm]

private theorem mixWeightV_eq_mul_mixLogPow {t : ℕ} (ht : (1 : ℝ) < t) :
    mixWeightV t = mixLogPow 1 t * (mixWeightV t * Real.log t) := by
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 : mixLogPow 1 t * Real.log t = 1 := by
    rw [mixLogPow_one_eq ht, inv_mul_cancel₀ hlog]
  calc
    mixWeightV t = mixWeightV t * 1 := (mul_one _).symm
    _ = mixWeightV t * (mixLogPow 1 t * Real.log t) := by rw [h1]
    _ = mixLogPow 1 t * (mixWeightV t * Real.log t) := by ring

private theorem mixZ_eq_weighted {X : ℕ} (hX : 2 ≤ X) :
    mixZ X =
      ∑ t ∈ mixScale X, mixLogPow 1 t * (mixWeightV t * Real.log t) := by
  unfold mixZ
  refine sum_congr (s₁ := mixScale X) (s₂ := mixScale X) rfl fun t ht => ?_
  exact mixWeightV_eq_mul_mixLogPow (one_lt_of_mem_mixScale hX ht)

private theorem mixZ_sub_mixLogPowSum {X : ℕ} (hX : 2 ≤ X) :
    mixZ X - mixLogPowSum X 1 =
      ∑ t ∈ mixScale X,
        mixLogPow 1 t * (mixWeightV t * Real.log t - 1) := by
  rw [mixZ_eq_weighted hX, mixLogPowSum, ← sum_sub_distrib]
  refine sum_congr (s₁ := mixScale X) (s₂ := mixScale X) rfl fun t _ => ?_
  rw [← mul_sub_one]

private theorem mixZ_sub_abs_le {X : ℕ} {ε : ℝ} (hX : 2 ≤ X) (_hε : 0 ≤ ε)
    (huni : ∀ t ∈ mixScale X, |mixWeightV t * Real.log t - 1| ≤ ε) :
    |mixZ X - mixLogPowSum X 1| ≤ ε * mixLogPowSum X 1 := by
  have hterm : ∀ t ∈ mixScale X,
      |mixLogPow 1 t * (mixWeightV t * Real.log t - 1)| ≤
        mixLogPow 1 t * ε := by
    intro t ht
    have h1 := one_lt_of_mem_mixScale hX ht
    have hnn := mixLogPow_nonneg 1 h1
    rw [abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (huni t ht) hnn
  have habs :=
    abs_sum_le_sum_abs
      (fun t : ℕ => mixLogPow 1 (t : ℝ) * (mixWeightV t * Real.log t - 1))
      (mixScale X)
  have hsum :
      ∑ t ∈ mixScale X, mixLogPow 1 t * ε =
        (∑ t ∈ mixScale X, mixLogPow 1 t) * ε :=
    (sum_mul (mixScale X) (fun t => mixLogPow 1 t) ε).symm
  rw [mixZ_sub_mixLogPowSum hX]
  calc
    |∑ t ∈ mixScale X, mixLogPow 1 t * (mixWeightV t * Real.log t - 1)|
        ≤ ∑ t ∈ mixScale X,
            |mixLogPow 1 t * (mixWeightV t * Real.log t - 1)| :=
      habs
    _ ≤ ∑ t ∈ mixScale X, mixLogPow 1 t * ε :=
      sum_le_sum hterm
    _ = (∑ t ∈ mixScale X, mixLogPow 1 t) * ε :=
      hsum
    _ = ε * mixLogPowSum X 1 := by
      unfold mixLogPowSum
      rw [mul_comm]

private theorem tendsto_mixZ_div_mixLogPowSum :
    Tendsto (fun X : ℕ => mixZ X / mixLogPowSum X 1) atTop (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hcal : ∀ᶠ t : ℝ in atTop,
      |eulerProd (sieveCutoff t) * Real.log t - 1| < ε / 2 := by
    have h := tendsto_eulerProd_sieveCutoff_mul_log.eventually
      (Metric.ball_mem_nhds (1 : ℝ) hε2)
    refine h.mono fun t ht => ?_
    simpa [Metric.mem_ball, Real.dist_eq] using ht
  rw [eventually_atTop] at hcal
  obtain ⟨T, hT⟩ := hcal
  have hTX : ∀ᶠ X : ℕ in atTop, T ≤ (X : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop T)
  filter_upwards [hTX, eventually_ge_atTop 2] with X hTX hX
  have huni : ∀ t ∈ mixScale X, |mixWeightV t * Real.log t - 1| ≤ ε / 2 := by
    intro t ht
    have ht' := mem_Ioc.mp ht
    have htR : T ≤ (t : ℝ) :=
      le_trans hTX (Nat.cast_le.mpr (Nat.le_of_lt ht'.1))
    have hlt : |eulerProd (sieveCutoff (t : ℝ)) * Real.log (t : ℝ) - 1| < ε / 2 :=
      hT (t : ℝ) htR
    have hrew : mixWeightV t * Real.log t =
        eulerProd (sieveCutoff (t : ℝ)) * Real.log t := by
      rw [mixWeightV_eq_eulerProd]
    rw [hrew]
    exact hlt.le
  have hSpos := mixLogPowSum_pos hX
  have hdiff := mixZ_sub_abs_le hX (le_of_lt hε2) huni
  have hratio : |mixZ X / mixLogPowSum X 1 - 1| ≤ ε / 2 := by
    have hform : |mixZ X / mixLogPowSum X 1 - 1| =
        |mixZ X - mixLogPowSum X 1| / mixLogPowSum X 1 := by
      rw [div_sub_one hSpos.ne', abs_div, abs_of_pos hSpos]
    rw [hform]
    exact (div_le_iff₀ hSpos).mpr hdiff
  have hdist : dist (mixZ X / mixLogPowSum X 1) (1 : ℝ) < ε := by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hratio (half_lt_self hε)
  exact hdist

private theorem div_mul_div_cancel_right_of_ne (a b c : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    a / c = a / b * (b / c) := by
  field_simp [hb, hc]

private theorem tendsto_mixZ_div :
    Tendsto (fun X : ℕ => mixZ X / ((X : ℝ) / Real.log X)) atTop (nhds 1) := by
  have hZS := tendsto_mixZ_div_mixLogPowSum
  have hSX := tendsto_mixLogPowSum_div
  have hmul : Tendsto (fun X : ℕ =>
      (mixZ X / mixLogPowSum X 1) *
        (mixLogPowSum X 1 / ((X : ℝ) / Real.log X))) atTop (nhds 1) := by
    simpa using hZS.mul hSX
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with X hX
  exact (div_mul_div_cancel_right_of_ne (mixZ X) (mixLogPowSum X 1)
    ((X : ℝ) / Real.log X) (mixLogPowSum_pos hX).ne' (X_div_log_ne hX)).symm

/-! ### `windowNX X ∼ X / log X` from `MixPrimeCountingAsymp` -/

private theorem tendsto_primeCounting_div_of_primeCountingAsymp
    (hπ : MixPrimeCountingAsymp) :
    Tendsto (fun X : ℕ =>
      (Nat.primeCounting X : ℝ) / ((X : ℝ) / Real.log X)) atTop (nhds 1) := by
  have h := hπ.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr fun X => ?_
  simp [Function.comp_apply, Nat.floor_natCast]

private theorem tendsto_two_mul_nat_atTop :
    Tendsto (fun X : ℕ => 2 * X) atTop atTop :=
  tendsto_atTop_atTop_of_monotone
    (fun _ _ h => Nat.mul_le_mul_left 2 h)
    fun n => ⟨n, Nat.le_mul_of_pos_left n (by norm_num : (0 : ℕ) < 2)⟩

private theorem tendsto_primeCounting_two_mul_div_of_primeCountingAsymp
    (hπ : MixPrimeCountingAsymp) :
    Tendsto (fun X : ℕ =>
      (Nat.primeCounting (2 * X) : ℝ) /
        ((2 * (X : ℝ)) / Real.log (2 * (X : ℝ)))) atTop (nhds 1) := by
  have hx : Tendsto (fun X : ℕ => (2 : ℝ) * X) atTop atTop :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_two_mul_nat_atTop).congr
      fun X => two_mul_cast X
  have h := hπ.comp hx
  refine h.congr fun X => ?_
  have hfloor : ⌊(2 : ℝ) * X⌋₊ = 2 * X := by
    rw [← two_mul_cast, Nat.floor_natCast]
  simp [Function.comp_apply, hfloor]

private theorem windowNX_div_eq {X : ℕ} (hX : 2 ≤ X) :
    (windowNX X : ℝ) / ((X : ℝ) / Real.log X) =
      (Nat.primeCounting (2 * X) : ℝ) /
          ((2 * (X : ℝ)) / Real.log (2 * (X : ℝ))) *
        (2 : ℝ) * (Real.log X / Real.log (2 * (X : ℝ))) -
      (Nat.primeCounting X : ℝ) / ((X : ℝ) / Real.log X) := by
  have hx := (X_pos hX).ne'
  have hL := (log_X_pos hX).ne'
  have hL2 := (log_two_mul_pos hX).ne'
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hx2 : (2 : ℝ) * (X : ℝ) ≠ 0 := mul_ne_zero h2 hx
  have hle : Nat.primeCounting X ≤ Nat.primeCounting (2 * X) :=
    Nat.monotone_primeCounting
      (Nat.le_mul_of_pos_left X (by norm_num : (0 : ℕ) < 2))
  have hcast : (windowNX X : ℝ) =
      (Nat.primeCounting (2 * X) : ℝ) - (Nat.primeCounting X : ℝ) := by
    rw [windowNX, Nat.cast_sub hle]
  rw [hcast]
  set π2 : ℝ := (Nat.primeCounting (2 * X) : ℝ)
  set π1 : ℝ := (Nat.primeCounting X : ℝ)
  set x : ℝ := (X : ℝ)
  set L : ℝ := Real.log (X : ℝ)
  set L2 : ℝ := Real.log (2 * (X : ℝ))
  have hsplit : (π2 - π1) / (x / L) = π2 * L / x - π1 * L / x := by
    have h : (π2 - π1) / (x / L) = (π2 - π1) * L / x := by
      field_simp [hx, hL]
    rw [h, sub_mul, sub_div]
  have hπ1 : π1 * L / x = π1 / (x / L) := by
    field_simp [hx, hL]
  have hπ2 : π2 * L / x = π2 / (2 * x / L2) * 2 * (L / L2) := by
    have hr : π2 / (2 * x / L2) * 2 * (L / L2) = π2 * L / x := by
      rw [div_div_eq_mul_div]
      field_simp [hx, hL, hL2, h2, hx2]
    exact hr.symm
  rw [hsplit, hπ1, hπ2]

private theorem tendsto_windowNX_div_of_primeCountingAsymp
    (hπ : MixPrimeCountingAsymp) :
    Tendsto (fun X : ℕ =>
      (windowNX X : ℝ) / ((X : ℝ) / Real.log X)) atTop (nhds 1) := by
  have ha := tendsto_primeCounting_two_mul_div_of_primeCountingAsymp hπ
  have hb := tendsto_primeCounting_div_of_primeCountingAsymp hπ
  have hc := tendsto_log_div_log_two_mul
  have hmul : Tendsto (fun X : ℕ =>
      (Nat.primeCounting (2 * X) : ℝ) /
          ((2 * (X : ℝ)) / Real.log (2 * (X : ℝ))) *
        (2 : ℝ) * (Real.log X / Real.log (2 * (X : ℝ))))
      atTop (nhds 2) := by
    have h := ((ha.mul (tendsto_const_nhds (x := (2 : ℝ)))).mul hc)
    simpa using h
  have hsub : Tendsto (fun X : ℕ =>
      (Nat.primeCounting (2 * X) : ℝ) /
          ((2 * (X : ℝ)) / Real.log (2 * (X : ℝ))) *
        (2 : ℝ) * (Real.log X / Real.log (2 * (X : ℝ))) -
      (Nat.primeCounting X : ℝ) / ((X : ℝ) / Real.log X))
      atTop (nhds 1) := by
    have h := hmul.sub hb
    have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    rw [h21] at h
    exact h
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with X hX
  exact (windowNX_div_eq hX).symm

/-! ### Combine: `ζ_X = Z_X / N_X` -/

private theorem div_div_div_eq (a b c : ℝ) (hb : b ≠ 0) :
    a / c = (a / b) / (c / b) := by
  have h : (a / b) / (c / b) = a / c := by
    by_cases hc : c = 0
    · simp [hc]
    · field_simp [hb, hc]
  exact h.symm

private theorem mixZeta_eq_div {X : ℕ} (hX : 2 ≤ X) :
    mixZeta X =
      (mixZ X / ((X : ℝ) / Real.log X)) /
        ((windowNX X : ℝ) / ((X : ℝ) / Real.log X)) := by
  unfold mixZeta
  exact div_div_div_eq (mixZ X) ((X : ℝ) / Real.log X) (windowNX X : ℝ)
    (X_div_log_ne hX)

/-- Qualitative PNT implies the mass ratio `Z_X / N_X → 1`. This is not
an unconditional theorem: `MixPrimeCountingAsymp` remains an input. -/
theorem mixZeta_tendsto_one_of_primeCountingAsymp
    (hπ : MixPrimeCountingAsymp) : MixZetaTendstoOne := by
  unfold MixZetaTendstoOne
  have hnum := tendsto_mixZ_div
  have hden := tendsto_windowNX_div_of_primeCountingAsymp hπ
  have hdiv : Tendsto (fun X : ℕ =>
      (mixZ X / ((X : ℝ) / Real.log X)) /
        ((windowNX X : ℝ) / ((X : ℝ) / Real.log X)))
      atTop (nhds 1) := by
    have h := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    have hone : (1 : ℝ) / 1 = 1 := by norm_num
    rw [hone] at h
    exact h
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with X hX
  exact (mixZeta_eq_div hX).symm

end PrimeGapNormality.Prime
