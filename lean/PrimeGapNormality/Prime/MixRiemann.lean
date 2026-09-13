import PrimeGapNormality.Prime.ExactRootMix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic

/-!
# Monotone Riemann bound for `f_v(t) = (log t)^(-v)`

On `[X, 2X]` with integer `X ≥ 2` and `v ≥ 1`,

    `0 ≤ ∫_X^{2X} f_v - ∑_{t ∈ Ioc X (2X)} f_v(t) ≤ f_v(X)`.

The integral is at least `X f_v(2X)`, so the relative error is at most

    `(1/X) (log(2X)/log X)^v`.

This is `≤ 2/X` whenever `(v : ℝ) ≤ log X`. That band contains every
`v ≤ r+1` with `r = O(log log X)`. Mix weights remain `mixWeightV`
(`V(y_t)`); this file does not introduce `1/log t` mix weights.

`Z_X / N_X → 1` is not a short corollary of `eulerProd_two_sided` and
`windowNX`, and is recorded as `MixZetaTendstoOne`.

R106/09 Paket 2.

Source: `rounds/round106/09_gpt_v04_lean_audit_and_grok_order.md` Paket 2;
`rounds/round106/01_gpt_proof_digestion_audit.md` §9;
`ExactRootMix.mixScale`.
Contract: API
Audit: GREEN
-/

open Finset
open Filter
open MeasureTheory (volume)
open scoped Topology

namespace PrimeGapNormality.Prime

/-! ### Comparison function `f_v` -/

/-- Paper `f_v(t) = (log t)^(-(v : ℝ))`. -/
noncomputable def mixLogPow (v : ℕ) (t : ℝ) : ℝ :=
  Real.log t ^ (-(v : ℝ))

/-- Right-endpoint Riemann sum on `{X+1,…,2X}`. -/
noncomputable def mixLogPowSum (X v : ℕ) : ℝ :=
  ∑ t ∈ mixScale X, mixLogPow v t

/-- Integral of `f_v` on the closed dyadic window. -/
noncomputable def mixLogPowIntegral (X v : ℕ) : ℝ :=
  ∫ t in (X : ℝ)..((2 * X : ℕ) : ℝ), mixLogPow v t

theorem mixLogPow_pos (v : ℕ) {t : ℝ} (ht : 1 < t) : 0 < mixLogPow v t :=
  Real.rpow_pos_of_pos (Real.log_pos ht) _

theorem mixLogPow_nonneg (v : ℕ) {t : ℝ} (ht : 1 < t) : 0 ≤ mixLogPow v t :=
  (mixLogPow_pos v ht).le

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

/-- `1 < ↑(2 * X)` rewritten as `1 < 2 * ↑X`, matching `mixLogPow v (2 * X)`. -/
private theorem one_lt_two_mul_real {X : ℕ} (hX : 2 ≤ X) :
    (1 : ℝ) < 2 * (X : ℝ) := by
  rw [← two_mul_cast]
  exact one_lt_two_mul hX

/-! ### Antitone on the window -/

theorem mixLogPow_antitoneOn {X : ℕ} (v : ℕ) (hX : 2 ≤ X) :
    AntitoneOn (mixLogPow v)
      (Set.Icc (X : ℝ) ((2 * X : ℕ) : ℝ)) := by
  intro x hx y _hy hxy
  have hx1 : (1 : ℝ) < x :=
    lt_of_lt_of_le (one_lt_of_two_le hX) hx.1
  have hx0 : (0 : ℝ) < x := lt_trans (by norm_num : (0 : ℝ) < 1) hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogle : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hvnonpos : -(v : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos hlogx hlogle hvnonpos

private theorem mixLogPow_intervalIntegrable {X : ℕ} (v : ℕ) (hX : 2 ≤ X) :
    IntervalIntegrable (mixLogPow v) volume (X : ℝ) ((2 * X : ℕ) : ℝ) := by
  have hab := mixWindow_le X
  have hanti := mixLogPow_antitoneOn v hX
  have huIcc :
      Set.uIcc (X : ℝ) ((2 * X : ℕ) : ℝ) =
        Set.Icc (X : ℝ) ((2 * X : ℕ) : ℝ) :=
    Set.uIcc_of_le hab
  have hanti' :
      AntitoneOn (mixLogPow v)
        (Set.uIcc (X : ℝ) ((2 * X : ℕ) : ℝ)) := by
    rwa [huIcc]
  exact hanti'.intervalIntegrable

/-! ### Right Riemann sum as an `Ico` sum -/

theorem mixLogPowSum_eq_Ico (X v : ℕ) :
    mixLogPowSum X v = ∑ i ∈ Ico X (2 * X), mixLogPow v (i + 1 : ℕ) := by
  unfold mixLogPowSum mixScale
  refine Eq.symm ?_
  refine sum_nbij (fun i => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    have hi' := mem_Ico.mp hi
    exact mem_Ioc.mpr ⟨Nat.lt_succ_of_le hi'.1, by omega⟩
  · intro a _ha b _hb h
    exact Nat.succ_injective h
  · intro t ht
    have ht' := mem_Ioc.mp ht
    refine ⟨t - 1, mem_Ico.mpr ⟨Nat.le_sub_one_of_lt ht'.1, by omega⟩,
      Nat.sub_add_cancel (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le X) ht'.1))⟩
  · intro i _hi
    simp [Nat.cast_add_one]

private theorem sum_Ico_telescope (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, (f k - f (k + 1)) = f m - f n := by
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro n hmn ih
    rw [sum_Ico_succ_top hmn, ih]
    ring

/-! ### Integral versus right Riemann sum -/

theorem mixLogPow_sum_le_integral {X : ℕ} (v : ℕ) (hX : 2 ≤ X) :
    mixLogPowSum X v ≤ mixLogPowIntegral X v := by
  have hle : X ≤ 2 * X :=
    Nat.le_mul_of_pos_left X (by norm_num : (0 : ℕ) < 2)
  have hanti := mixLogPow_antitoneOn v hX
  have hsum :=
    AntitoneOn.sum_le_integral_Ico (a := X) (b := 2 * X) (f := mixLogPow v)
      hle hanti
  rw [mixLogPowSum_eq_Ico]
  exact hsum

theorem mixLogPow_integral_le_leftSum {X : ℕ} (v : ℕ) (hX : 2 ≤ X) :
    mixLogPowIntegral X v ≤ ∑ i ∈ Ico X (2 * X), mixLogPow v i := by
  have hle : X ≤ 2 * X :=
    Nat.le_mul_of_pos_left X (by norm_num : (0 : ℕ) < 2)
  exact AntitoneOn.integral_le_sum_Ico (a := X) (b := 2 * X)
    (f := mixLogPow v) hle (mixLogPow_antitoneOn v hX)

theorem mixLogPow_leftSum_sub_sum {X : ℕ} (v : ℕ) (hX : 2 ≤ X) :
    (∑ i ∈ Ico X (2 * X), mixLogPow v i) - mixLogPowSum X v =
      mixLogPow v X - mixLogPow v (2 * X) := by
  have hle : X ≤ 2 * X :=
    Nat.le_mul_of_pos_left X (by norm_num : (0 : ℕ) < 2)
  rw [mixLogPowSum_eq_Ico, ← sum_sub_distrib]
  rw [← two_mul_cast]
  exact sum_Ico_telescope (fun i => mixLogPow v (i : ℝ)) hle

/-- Paper monotone Riemann bound:
`0 ≤ ∫_X^{2X} f_v - ∑_{X<t≤2X} f_v(t) ≤ f_v(X)`. -/
theorem mixLogPow_riemann {X : ℕ} (v : ℕ) (hX : 2 ≤ X) (_hv : 1 ≤ v) :
    0 ≤ mixLogPowIntegral X v - mixLogPowSum X v ∧
      mixLogPowIntegral X v - mixLogPowSum X v ≤ mixLogPow v X := by
  have hsum_le := mixLogPow_sum_le_integral v hX
  have hint_le := mixLogPow_integral_le_leftSum v hX
  have hdiff := mixLogPow_leftSum_sub_sum v hX
  have h2X1 := one_lt_two_mul_real hX
  have hf2 : 0 ≤ mixLogPow v (2 * X) := mixLogPow_nonneg v h2X1
  constructor
  · linarith
  · have hsub :
        mixLogPowIntegral X v - mixLogPowSum X v ≤
          mixLogPow v X - mixLogPow v (2 * X) := by
      linarith
    have hX1 := one_lt_of_two_le hX
    linarith [mixLogPow_nonneg v hX1]

/-! ### Integral lower bound `X f_v(2X)` -/

theorem mixLogPow_integral_ge {X : ℕ} (v : ℕ) (hX : 2 ≤ X) :
    (X : ℝ) * mixLogPow v (2 * X) ≤ mixLogPowIntegral X v := by
  have hab := mixWindow_le X
  have hInt := mixLogPow_intervalIntegrable v hX
  have hconst :
      IntervalIntegrable (fun _ : ℝ => mixLogPow v ((2 * X : ℕ) : ℝ))
        volume (X : ℝ) ((2 * X : ℕ) : ℝ) :=
    intervalIntegrable_const
  have hle :
      ∀ t ∈ Set.Icc (X : ℝ) ((2 * X : ℕ) : ℝ),
        mixLogPow v ((2 * X : ℕ) : ℝ) ≤ mixLogPow v t := by
    intro t ht
    exact mixLogPow_antitoneOn v hX ht ⟨hab, le_rfl⟩ ht.2
  have hmono :=
    intervalIntegral.integral_mono_on hab hconst hInt hle
  have hval :
      (∫ _t in (X : ℝ)..((2 * X : ℕ) : ℝ),
          mixLogPow v ((2 * X : ℕ) : ℝ)) =
        (((2 * X : ℕ) : ℝ) - (X : ℝ)) *
          mixLogPow v ((2 * X : ℕ) : ℝ) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hlen : ((2 * X : ℕ) : ℝ) - (X : ℝ) = (X : ℝ) := by
    rw [two_mul_cast]
    ring
  have hrew : mixLogPow v ((2 * X : ℕ) : ℝ) = mixLogPow v (2 * X) := by
    rw [two_mul_cast]
  rw [hval, hlen, hrew] at hmono
  exact hmono

/-! ### Explicit relative factor `(log(2X)/log X)^v` -/

theorem mixLogPow_ratio_eq {X : ℕ} (v : ℕ) (hX : 2 ≤ X) :
    mixLogPow v X / mixLogPow v (2 * X) =
      (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) := by
  have hX1 := one_lt_of_two_le hX
  have h2X1 := one_lt_two_mul_real hX
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have hlog2X : 0 < Real.log (2 * (X : ℝ)) := Real.log_pos h2X1
  have hXpos : 0 < mixLogPow v (2 * X) := mixLogPow_pos v h2X1
  unfold mixLogPow
  rw [two_mul_cast]
  have hnegX : Real.log X ^ (-(v : ℝ)) =
      (Real.log X ^ (v : ℝ))⁻¹ :=
    Real.rpow_neg hlogX.le _
  have hneg2 : Real.log (2 * (X : ℝ)) ^ (-(v : ℝ)) =
      (Real.log (2 * (X : ℝ)) ^ (v : ℝ))⁻¹ :=
    Real.rpow_neg hlog2X.le _
  rw [hnegX, hneg2, div_eq_mul_inv, inv_inv]
  have hdiv :
      Real.log (2 * (X : ℝ)) ^ (v : ℝ) / Real.log X ^ (v : ℝ) =
        (Real.log (2 * (X : ℝ)) / Real.log X) ^ (v : ℝ) :=
    (Real.div_rpow hlog2X.le hlogX.le _).symm
  rw [← hdiv, div_eq_mul_inv, mul_comm]

private theorem log_two_mul_div {X : ℕ} (hX : 2 ≤ X) :
    Real.log ((2 * X : ℕ) : ℝ) / Real.log X =
      1 + Real.log 2 / Real.log X := by
  have hXpos : 0 < (X : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hX)
  have hlogX : 0 < Real.log X := Real.log_pos (one_lt_of_two_le hX)
  have hlog2X : Real.log ((2 * X : ℕ) : ℝ) = Real.log 2 + Real.log X := by
    rw [two_mul_cast, Real.log_mul (by norm_num) hXpos.ne']
  rw [hlog2X, add_div, div_self hlogX.ne', add_comm]

/-- `(log(2X)/log X)^v ≤ 2` on the band `v ≤ log X`. -/
theorem mixLogPow_log_ratio_rpow_le_two {X : ℕ} (v : ℕ) (hX : 3 ≤ X) (_hv : 1 ≤ v)
    (hvlog : (v : ℝ) ≤ Real.log X) :
    (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) ≤ 2 := by
  have hX2 : 2 ≤ X := le_trans (by norm_num : (2 : ℕ) ≤ 3) hX
  have hX1 : (1 : ℝ) < X :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) (Nat.cast_le.mpr hX)
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have hratio := log_two_mul_div hX2
  have hu : 0 < Real.log 2 / Real.log X :=
    div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hlogX
  have h1u : (0 : ℝ) < 1 + Real.log 2 / Real.log X :=
    add_pos_of_pos_of_nonneg (by norm_num) hu.le
  have hrpow :
      (1 + Real.log 2 / Real.log X) ^ (v : ℝ) =
        Real.exp (Real.log (1 + Real.log 2 / Real.log X) * v) :=
    Real.rpow_def_of_pos h1u _
  have hlogu :
      Real.log (1 + Real.log 2 / Real.log X) ≤ Real.log 2 / Real.log X := by
    have := Real.log_le_sub_one_of_pos h1u
    simpa using this
  have hmul :
      Real.log (1 + Real.log 2 / Real.log X) * (v : ℝ) ≤
        (Real.log 2 / Real.log X) * v :=
    mul_le_mul_of_nonneg_right hlogu (Nat.cast_nonneg _)
  have hexp :
      Real.exp (Real.log (1 + Real.log 2 / Real.log X) * v) ≤
        Real.exp ((Real.log 2 / Real.log X) * v) :=
    Real.exp_le_exp.mpr hmul
  have hvbound : (Real.log 2 / Real.log X) * v ≤ Real.log 2 := by
    have hvu :
        (v : ℝ) * (Real.log 2 / Real.log X) =
          ((v : ℝ) / Real.log X) * Real.log 2 := by
      field_simp [hlogX.ne']
    have hdiv1 : (v : ℝ) / Real.log X ≤ 1 := (div_le_one hlogX).mpr hvlog
    have hle :
        ((v : ℝ) / Real.log X) * Real.log 2 ≤ 1 * Real.log 2 :=
      mul_le_mul_of_nonneg_right hdiv1 (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hcomm : (Real.log 2 / Real.log X) * v =
        (v : ℝ) * (Real.log 2 / Real.log X) := mul_comm _ _
    calc
      (Real.log 2 / Real.log X) * v
          = (v : ℝ) * (Real.log 2 / Real.log X) := hcomm
      _ = ((v : ℝ) / Real.log X) * Real.log 2 := hvu
      _ ≤ 1 * Real.log 2 := hle
      _ = Real.log 2 := one_mul _
  have hexp2 :
      Real.exp ((Real.log 2 / Real.log X) * v) ≤ Real.exp (Real.log 2) :=
    Real.exp_le_exp.mpr hvbound
  have htwo : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num : (0 : ℝ) < 2)
  calc
    (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ)
        = (1 + Real.log 2 / Real.log X) ^ (v : ℝ) := by rw [hratio]
    _ = Real.exp (Real.log (1 + Real.log 2 / Real.log X) * v) := hrpow
    _ ≤ Real.exp ((Real.log 2 / Real.log X) * v) := hexp
    _ ≤ Real.exp (Real.log 2) := hexp2
    _ = 2 := htwo

theorem mixLogPow_rel_err_explicit {X : ℕ} (v : ℕ) (hX : 2 ≤ X) (hv : 1 ≤ v) :
    mixLogPowIntegral X v - mixLogPowSum X v ≤
      ((1 : ℝ) / X) *
        (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) *
          mixLogPowIntegral X v := by
  have hriem := mixLogPow_riemann v hX hv
  have hge := mixLogPow_integral_ge v hX
  have h2X1 := one_lt_two_mul_real hX
  have hf2pos : 0 < mixLogPow v (2 * X) := mixLogPow_pos v h2X1
  have hXpos : (0 : ℝ) < X :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hX)
  have hratio := mixLogPow_ratio_eq v hX
  have hratio_pos :
      0 < (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) := by
    have hlogX : 0 < Real.log X := Real.log_pos (one_lt_of_two_le hX)
    have hlog2X : 0 < Real.log ((2 * X : ℕ) : ℝ) := Real.log_pos (one_lt_two_mul hX)
    exact Real.rpow_pos_of_pos (div_pos hlog2X hlogX) _
  have hfX :
      mixLogPow v X =
        (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) *
          mixLogPow v (2 * X) := by
    have := congrArg (fun z => z * mixLogPow v (2 * X)) hratio
    have hcancel : mixLogPow v X / mixLogPow v (2 * X) * mixLogPow v (2 * X) =
        mixLogPow v X := div_mul_cancel₀ _ hf2pos.ne'
    rw [hcancel] at this
    exact this
  have hXnn : 0 ≤ (1 : ℝ) / X := one_div_nonneg.mpr hXpos.le
  have hfX_le :
      mixLogPow v X ≤
        ((1 : ℝ) / X) *
          (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) *
            mixLogPowIntegral X v := by
    have hmul :=
      mul_le_mul_of_nonneg_left hge
        (mul_nonneg hXnn hratio_pos.le)
    have hleft :
        ((1 : ℝ) / X) *
            (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) *
              ((X : ℝ) * mixLogPow v (2 * X)) =
          (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) *
            mixLogPow v (2 * X) := by
      field_simp [hXpos.ne']
    calc
      mixLogPow v X
          = (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) *
              mixLogPow v (2 * X) := hfX
      _ = ((1 : ℝ) / X) *
            (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) *
              ((X : ℝ) * mixLogPow v (2 * X)) := hleft.symm
      _ ≤ ((1 : ℝ) / X) *
            (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) *
              mixLogPowIntegral X v := hmul
  exact hriem.2.trans hfX_le

/-- Relative error `≤ 2/X` for every `v ≤ log X`. This includes the
paper band `v ≤ r+1` with `r = O(log log X)`. -/
theorem mixLogPow_rel_err {X : ℕ} (v : ℕ) (hX : 3 ≤ X) (hv : 1 ≤ v)
    (hvlog : (v : ℝ) ≤ Real.log X) :
    mixLogPowIntegral X v - mixLogPowSum X v ≤
      ((2 : ℝ) / X) * mixLogPowIntegral X v := by
  have hX2 : 2 ≤ X := le_trans (by norm_num : (2 : ℕ) ≤ 3) hX
  have hexp := mixLogPow_rel_err_explicit v hX2 hv
  have hratio := mixLogPow_log_ratio_rpow_le_two v hX hv hvlog
  have hge := mixLogPow_integral_ge v hX2
  have hXpos : (0 : ℝ) < X :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 3) hX)
  have hintnn : 0 ≤ mixLogPowIntegral X v := by
    have hf2 := mixLogPow_nonneg v (one_lt_two_mul_real hX2)
    exact le_trans (mul_nonneg hXpos.le hf2) hge
  have hscale :
      ((1 : ℝ) / X) *
          (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) *
            mixLogPowIntegral X v ≤
        ((2 : ℝ) / X) * mixLogPowIntegral X v := by
    have hfac :
        ((1 : ℝ) / X) *
            (Real.log ((2 * X : ℕ) : ℝ) / Real.log X) ^ (v : ℝ) ≤
          ((1 : ℝ) / X) * 2 :=
      mul_le_mul_of_nonneg_left hratio (one_div_nonneg.mpr hXpos.le)
    have h2 : ((1 : ℝ) / X) * 2 = (2 : ℝ) / X := by
      field_simp [hXpos.ne']
    have hmul :=
      mul_le_mul_of_nonneg_right hfac hintnn
    rwa [h2] at hmul
  exact hexp.trans hscale

/-! ### Uniformity in `v ≤ r+1` for `r = O(log log X)` -/

/-- Eventual relative error `≤ 2/X`, uniform in `v ≤ r X + 1`. -/
def MixLogPowRelErrUniform (r : ℕ → ℕ) : Prop :=
  ∀ᶠ X : ℕ in atTop, ∀ v : ℕ, 1 ≤ v → v ≤ r X + 1 →
    mixLogPowIntegral X v - mixLogPowSum X v ≤
      ((2 : ℝ) / X) * mixLogPowIntegral X v

theorem mixLogPowRelErrUniform_of_le_log {r : ℕ → ℕ}
    (hr : ∀ᶠ X : ℕ in atTop, (r X + 1 : ℝ) ≤ Real.log X) :
    MixLogPowRelErrUniform r := by
  filter_upwards [hr, eventually_ge_atTop 3] with X hlog hX
  intro v hv hvle
  have hvR : (v : ℝ) ≤ Real.log X := by
    refine (Nat.cast_le.mpr hvle).trans ?_
    rw [Nat.cast_add_one]
    exact hlog
  exact mixLogPow_rel_err v hX hv hvR

private theorem tendsto_loglog_div_log :
    Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop

private theorem tendsto_C_loglog_add_inv_log (C : ℝ) :
    Tendsto
      (fun x : ℝ =>
        C * (Real.log (Real.log x) / Real.log x) + (Real.log x)⁻¹)
      atTop (nhds 0) := by
  have hll := tendsto_loglog_div_log.const_mul C
  have hinv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  simpa using Tendsto.add hll hinv

/-- `r = O(log log X)` forces `r X + 1 ≤ log X` eventually, hence the
`2/X` relative error is uniform on `v ≤ r+1`. -/
theorem mixLogPowRelErrUniform_of_mul_loglog {r : ℕ → ℕ} {C : ℝ}
    (hr : ∀ᶠ X : ℕ in atTop, (r X : ℝ) ≤ C * Real.log (Real.log X)) :
    MixLogPowRelErrUniform r := by
  have hC :=
    (tendsto_C_loglog_add_inv_log C).comp tendsto_natCast_atTop_atTop
  refine mixLogPowRelErrUniform_of_le_log ?_
  filter_upwards [hr, eventually_ge_atTop 16,
    hC.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))]
    with X hle hX16 hball
  have hX1 : (1 : ℝ) < X :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) (Nat.cast_le.mpr hX16)
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have habs :
      |C * (Real.log (Real.log X) / Real.log X) + (Real.log X)⁻¹| < 1 := by
    have : |C * (Real.log (Real.log X) / Real.log X) + (Real.log X)⁻¹ - 0| < 1 :=
      hball
    rwa [sub_zero] at this
  have hlt :
      C * (Real.log (Real.log X) / Real.log X) + (Real.log X)⁻¹ < 1 :=
    (abs_lt.mp habs).2
  have hrew :
      (C * (Real.log (Real.log X) / Real.log X) + (Real.log X)⁻¹) *
          Real.log X =
        C * Real.log (Real.log X) + 1 := by
    field_simp [hlogX.ne']
  have hC1 : C * Real.log (Real.log X) + 1 < Real.log X := by
    have := mul_lt_mul_of_pos_right hlt hlogX
    rwa [hrew, one_mul] at this
  have hr1 : (r X : ℝ) + 1 ≤ C * Real.log (Real.log X) + 1 := by
    simpa [add_comm (1 : ℝ)] using add_le_add_right hle (1 : ℝ)
  exact hr1.trans hC1.le

/-! ### Mass ratio `ζ_X = Z_X / N_X` -/

/-- Qualitative PNT, the degree-one case of `mixLogPow_riemann`, and the
cutoff jump `V(y_t) ≍ 1/log t`. Not a short corollary of
`eulerProd_two_sided` and `windowNX` alone. -/
def MixZetaTendstoOne : Prop :=
  Tendsto mixZeta atTop (nhds 1)

end PrimeGapNormality.Prime
