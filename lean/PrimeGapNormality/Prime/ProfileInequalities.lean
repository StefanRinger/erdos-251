import PrimeGapNormality.Prime.EndAPI
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Elementary profile inequalities (paper constants)

Cutoff `d₀ > 24e` (`C_* = 12`), growth of `profileL` / `profileS`, and the
algebraic rank budget `κ > D / log B ⇒ (D / log B) log G ≤ L`. No AHL
argument and no integer rank selector.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` after (eq:budget),
(eq:budgetrange), Appendix moments (`C_*=12`, `d₀>2e C_*`);
`lean/PrimeGapNormality/Prime/EndAPI.lean`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Filter

set_option maxHeartbeats 400000

/-! ### Paper envelope `C_* = 12` and cutoff `d₀ > 24e` -/

/-- Model factorial-moment envelope `C_* = 12`. -/
def paperEnvelope : ℝ := 12

/-- Paper cutoff `d₀ > 2e C_*` with `C_* = 12`. -/
def paperCutoffLarge (d0 : ℝ) : Prop :=
  24 * Real.exp 1 < d0

theorem two_mul_exp_one_mul_paperEnvelope :
    2 * Real.exp 1 * paperEnvelope = 24 * Real.exp 1 := by
  unfold paperEnvelope
  ring

theorem paperCutoffLarge_iff {d0 : ℝ} :
    paperCutoffLarge d0 ↔ 2 * Real.exp 1 * paperEnvelope < d0 := by
  unfold paperCutoffLarge
  rw [two_mul_exp_one_mul_paperEnvelope]

/-- `e < 11/4`, hence `24e < 66`. Avoids `norm_num` on `24 * 2.718…`. -/
theorem twentyFour_mul_exp_one_lt_sixtySix : 24 * Real.exp 1 < 66 := by
  have hexp : Real.exp 1 < (11 : ℝ) / 4 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have hmul : (24 : ℝ) * Real.exp 1 < 24 * ((11 : ℝ) / 4) :=
    mul_lt_mul_of_pos_left hexp (by norm_num)
  have hnum : (24 : ℝ) * ((11 : ℝ) / 4) = 66 := by norm_num
  exact hmul.trans_eq hnum

theorem paperCutoffLarge_sixtySix : paperCutoffLarge 66 :=
  twentyFour_mul_exp_one_lt_sixtySix

theorem paperCutoffLarge_of_sixtySix_le {d0 : ℝ} (hd0 : 66 ≤ d0) :
    paperCutoffLarge d0 :=
  twentyFour_mul_exp_one_lt_sixtySix.trans_le hd0

/-! ### Window helpers (private; public copies live in `KuperbergAHL`) -/

private theorem windowG_one_le (X : ℕ) : (1 : ℝ) ≤ windowG X :=
  le_max_right _ _

private theorem windowG_log_nonneg (X : ℕ) : 0 ≤ Real.log (windowG X) :=
  Real.log_nonneg (windowG_one_le X)

private theorem tendsto_windowG : Tendsto windowG atTop atTop :=
  tendsto_atTop_mono (fun X => le_max_left (Real.log (X : ℝ)) (1 : ℝ))
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem tendsto_log_windowG :
    Tendsto (fun X : ℕ => Real.log (windowG X)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_windowG

private theorem one_lt_base {B : ℕ} (hB : 2 ≤ B) : (1 : ℝ) < B :=
  Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hB)

private theorem log_base_pos {B : ℕ} (hB : 2 ≤ B) : 0 < Real.log B :=
  Real.log_pos (one_lt_base hB)

private theorem kappa_pos_of_degree {B D : ℕ} {κ : ℝ} (hB : 2 ≤ B) (hD : 1 ≤ D)
    (hκ : (D : ℝ) / Real.log B < κ) : 0 < κ :=
  (div_pos
      (Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hD))
      (log_base_pos hB)).trans
    hκ

/-! ### `profileL` / `profileS` grow -/

theorem kappa_log_windowG_le_profileL {κ : ℝ} (hκ : 0 ≤ κ) (X : ℕ) :
    κ * Real.log (windowG X) ≤ (profileL κ X : ℝ) := by
  have _hmul : 0 ≤ κ * Real.log (windowG X) :=
    mul_nonneg hκ (windowG_log_nonneg X)
  have hsqrt : 0 ≤ Real.sqrt (κ * Real.log (windowG X)) := Real.sqrt_nonneg _
  have hle :
      κ * Real.log (windowG X) ≤
        κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X)) :=
    le_add_of_nonneg_right hsqrt
  exact hle.trans (Nat.le_ceil _)

theorem eventually_one_le_profileL {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, 1 ≤ profileL κ X := by
  filter_upwards [tendsto_log_windowG.eventually (eventually_gt_atTop (0 : ℝ))] with
    X hpos
  have hmul : 0 < κ * Real.log (windowG X) := mul_pos hκ hpos
  have harg :
      0 <
        κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X)) :=
    add_pos_of_pos_of_nonneg hmul (Real.sqrt_nonneg _)
  exact Nat.one_le_ceil_iff.mpr harg

theorem one_le_profileS_of_one_le_profileL {κ : ℝ} {X : ℕ}
    (hL : 1 ≤ profileL κ X) : 1 ≤ profileS κ X := by
  have hLre : (1 : ℝ) ≤ (profileL κ X : ℝ) := Nat.one_le_cast.mpr hL
  have hG : (1 : ℝ) ≤ windowG X := windowG_one_le X
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have hL0 : (0 : ℝ) ≤ (profileL κ X : ℝ) := Nat.cast_nonneg _
  have hstep : (4 : ℝ) * 1 ≤ 4 * (profileL κ X : ℝ) :=
    mul_le_mul_of_nonneg_left hLre h4
  have hmid : (4 : ℝ) * (profileL κ X : ℝ) * 1 ≤
      4 * (profileL κ X : ℝ) * windowG X :=
    mul_le_mul_of_nonneg_left hG (mul_nonneg h4 hL0)
  have hprod : (1 : ℝ) ≤ 4 * (profileL κ X : ℝ) * windowG X := by
    calc
      (1 : ℝ) ≤ 4 := by norm_num
      _ = 4 * 1 := by ring
      _ ≤ 4 * (profileL κ X : ℝ) := hstep
      _ = 4 * (profileL κ X : ℝ) * 1 := by ring
      _ ≤ 4 * (profileL κ X : ℝ) * windowG X := hmid
  exact Nat.le_floor (by simpa [Nat.cast_one] using hprod)

theorem eventually_one_le_profileS {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, 1 ≤ profileS κ X := by
  filter_upwards [eventually_one_le_profileL hκ] with X hL
  exact one_le_profileS_of_one_le_profileL hL

/-! ### Rank budget: `κ > D / log B` fits inside `L` -/

/-- Any positive clock eventually absorbs a fixed degree into `κ log G`. -/
theorem eventually_nat_le_kappa_log_windowG {κ : ℝ} (hκ : 0 < κ) (D : ℕ) :
    ∀ᶠ X : ℕ in atTop, (D : ℝ) ≤ κ * Real.log (windowG X) := by
  filter_upwards [tendsto_log_windowG.eventually
      (eventually_ge_atTop ((D : ℝ) / κ))] with X hlog
  exact (div_le_iff₀' hκ).mp hlog

/-- Paper form: `κ > D / log B` (with `B ≥ 2`, `D ≥ 1`) implies
`D ≤ κ log G` for large `X`. -/
theorem eventually_degree_le_kappa_log_windowG {B D : ℕ} {κ : ℝ}
    (hB : 2 ≤ B) (hD : 1 ≤ D) (hκ : (D : ℝ) / Real.log B < κ) :
    ∀ᶠ X : ℕ in atTop, (D : ℝ) ≤ κ * Real.log (windowG X) :=
  eventually_nat_le_kappa_log_windowG (kappa_pos_of_degree hB hD hκ) D

/-- Algebraic rank budget, for every `X`: if `κ ≥ D / log B`, then
`(D / log B) · log G ≤ L`. Integer rounding of a rank lives in
`RankSelect`, not here. -/
theorem degree_logBudget_le_profileL {B D : ℕ} {κ : ℝ} (hB : 2 ≤ B)
    (hκ : (D : ℝ) / Real.log B ≤ κ) (X : ℕ) :
    (D : ℝ) / Real.log B * Real.log (windowG X) ≤ (profileL κ X : ℝ) := by
  have hκ0 : 0 ≤ κ :=
    le_trans (div_nonneg (Nat.cast_nonneg D) (log_base_pos hB).le) hκ
  have hmul :
      (D : ℝ) / Real.log B * Real.log (windowG X) ≤
        κ * Real.log (windowG X) :=
    mul_le_mul_of_nonneg_right hκ (windowG_log_nonneg X)
  exact hmul.trans (kappa_log_windowG_le_profileL hκ0 X)

theorem eventually_degree_le_profileL {B D : ℕ} {κ : ℝ} (hB : 2 ≤ B)
    (hD : 1 ≤ D) (hκ : (D : ℝ) / Real.log B < κ) :
    ∀ᶠ X : ℕ in atTop, D ≤ profileL κ X := by
  have hκ0 : 0 ≤ κ := (kappa_pos_of_degree hB hD hκ).le
  filter_upwards [eventually_degree_le_kappa_log_windowG hB hD hκ] with X hDlog
  have hcast : (D : ℝ) ≤ (profileL κ X : ℝ) :=
    hDlog.trans (kappa_log_windowG_le_profileL hκ0 X)
  exact Nat.cast_le.mp hcast

/-! ### `(12 L)^j / j!` versus Bonferroni cutoff `d₀ L` -/

theorem cutoff_choose_le_pow_div (d0 : ℝ) (L j : ℕ) :
    ((⌈d0 * (L : ℝ)⌉₊).choose j : ℝ) ≤
      (⌈d0 * (L : ℝ)⌉₊ : ℝ) ^ j / (j.factorial : ℝ) := by
  simpa [Nat.cast_pow] using
    (Nat.choose_le_pow_div (α := ℝ) j (⌈d0 * (L : ℝ)⌉₊))

theorem twelve_pow_div_factorial_le_exp_ratio (L j : ℕ) (hj : 0 < j) :
    (12 * (L : ℝ)) ^ j / (j.factorial : ℝ) ≤
      (12 * Real.exp 1 * (L : ℝ) / j) ^ j := by
  have hjpos : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hexp : Real.exp (j : ℝ) = Real.exp 1 ^ j := by
    rw [← Real.exp_nat_mul (1 : ℝ) j]
    congr 1
    exact (mul_one (j : ℝ)).symm
  have hst : (j : ℝ) ^ j / (j.factorial : ℝ) ≤ Real.exp 1 ^ j := by
    have hpow := Real.pow_div_factorial_le_exp (x := (j : ℝ)) (Nat.cast_nonneg j) j
    rw [hexp] at hpow
    exact hpow
  have hnn : 0 ≤ (12 * (L : ℝ) / j) ^ j :=
    pow_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
        (Nat.cast_nonneg j))
      j
  have hscale :
      ((j : ℝ) ^ j / (j.factorial : ℝ)) * (12 * (L : ℝ) / j) ^ j ≤
        Real.exp 1 ^ j * (12 * (L : ℝ) / j) ^ j :=
    mul_le_mul_of_nonneg_right hst hnn
  have hj0 : (j : ℝ) ≠ 0 := hjpos.ne'
  have hfact : (j.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hleft :
      ((j : ℝ) ^ j / (j.factorial : ℝ)) * (12 * (L : ℝ) / j) ^ j =
        (12 * (L : ℝ)) ^ j / (j.factorial : ℝ) := by
    rw [div_pow]
    refine (eq_div_iff hfact).mpr ?_
    rw [mul_right_comm, div_mul_cancel₀ _ hfact, ← mul_div_assoc,
      mul_comm ((j : ℝ) ^ j), mul_div_cancel_right₀ _ (pow_ne_zero j hj0)]
  have hright :
      Real.exp 1 ^ j * (12 * (L : ℝ) / j) ^ j =
        (12 * Real.exp 1 * (L : ℝ) / j) ^ j := by
    rw [← mul_pow]
    congr 1
    rw [← mul_div_assoc, ← mul_assoc, mul_comm (Real.exp 1)]
  rwa [hleft, hright] at hscale

theorem twelve_exp_mul_div_lt_half {d0 : ℝ} {L j : ℕ}
    (hd0 : paperCutoffLarge d0) (hL : 0 < L)
    (hle : d0 * (L : ℝ) ≤ j) :
    12 * Real.exp 1 * (L : ℝ) / j < 1 / 2 := by
  have hd0lt : 24 * Real.exp 1 < d0 := hd0
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have h24 : 0 < 24 * Real.exp 1 :=
    mul_pos (by norm_num) (Real.exp_pos 1)
  have hlt : 24 * Real.exp 1 * (L : ℝ) < d0 * (L : ℝ) :=
    mul_lt_mul_of_pos_right hd0lt hLpos
  have hstrict : 24 * Real.exp 1 * (L : ℝ) < (j : ℝ) := hlt.trans_le hle
  have hnum : 0 < 12 * Real.exp 1 * (L : ℝ) :=
    mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) hLpos
  have hcmp :
      12 * Real.exp 1 * (L : ℝ) / j <
        12 * Real.exp 1 * (L : ℝ) / (24 * Real.exp 1 * (L : ℝ)) :=
    div_lt_div_of_pos_left hnum (mul_pos h24 hLpos) hstrict
  have hsimp :
      12 * Real.exp 1 * (L : ℝ) / (24 * Real.exp 1 * (L : ℝ)) = (1 : ℝ) / 2 := by
    have hc : Real.exp 1 * (L : ℝ) ≠ 0 :=
      mul_ne_zero (Real.exp_pos 1).ne' hLpos.ne'
    have hnum' : 12 * Real.exp 1 * (L : ℝ) =
        12 * (Real.exp 1 * (L : ℝ)) := by
      rw [mul_assoc]
    have hden : 24 * Real.exp 1 * (L : ℝ) =
        24 * (Real.exp 1 * (L : ℝ)) := by
      rw [mul_assoc]
    rw [hnum', hden, mul_div_mul_comm, div_self hc, mul_one]
    norm_num
  exact lt_of_lt_of_eq hcmp hsimp

/-- Bonferroni tail: on the band `j ≥ d₀ L` with `d₀ > 24e`, the model
envelope is at most `(1/2)^j`. -/
theorem twelve_pow_div_factorial_le_half_pow {d0 : ℝ} {L j : ℕ}
    (hd0 : paperCutoffLarge d0) (hL : 0 < L) (hj : 0 < j)
    (hle : d0 * (L : ℝ) ≤ j) :
    (12 * (L : ℝ)) ^ j / (j.factorial : ℝ) ≤ (1 / 2 : ℝ) ^ j := by
  have hratio := twelve_pow_div_factorial_le_exp_ratio L j hj
  have hhalf := twelve_exp_mul_div_lt_half hd0 hL hle
  have hnn : 0 ≤ 12 * Real.exp 1 * (L : ℝ) / j :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le)
        (Nat.cast_nonneg L))
      (Nat.cast_nonneg j)
  have hpow :
      (12 * Real.exp 1 * (L : ℝ) / j) ^ j < (1 / 2 : ℝ) ^ j :=
    pow_lt_pow_left₀ hhalf hnn hj.ne'
  exact hratio.trans hpow.le

end PrimeGapNormality.Prime
