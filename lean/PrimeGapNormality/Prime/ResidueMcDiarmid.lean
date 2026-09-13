import PrimeGapNormality.Prime.ModelConcentration
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic

/-!
# Residue-class McDiarmid widths (paper leftover from ModelConcentration)

The Bernoulli product in `ModelConcentration` is the later thinning stage.
This module compiles the *residue-class* stage: widths `c_p = 2(h/p+1)`,
the comparison `∑_{w < p ≤ y} c_p² ≪ h²/w + h log y + y`, and the
McDiarmid Lipschitz constant for a function of residue indicators.

CRT / neighbouring-Bonferroni cell counts are **not** proved here
(`ModelCellCount`).

Changing the forbidden class at `p` moves at most `h/p+1` integers in a
length-`h` interval, hence a survivor count changes by at most `c_p`.
The one-sided tail reuses `bernoulli_bounded_diff_one_sided` when the
coordinates are `{0,1}`-valued and those Lipschitz numbers fit.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` Appendix C, after
  (eq:bruncell), widths `2(h/p+1)` and `∑ 4(h/p+1)²`; (eq:bd);
`ModelConcentration.bernoulli_bounded_diff_one_sided`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Filter
open scoped Topology

set_option maxHeartbeats 800000

/-! ### Widths `c_p = 2(h/p+1)` -/

/-- Paper width `c_p = 2(h/p+1)` for a residue-class coordinate. -/
noncomputable def residueWidth (h p : ℝ) : ℝ :=
  2 * (h / p + 1)

/-- Paper sieve cutoff `w = (log G)^4`. -/
noncomputable def residueMcDiarmidCutoff (G : ℝ) : ℕ :=
  ⌊Real.log G ^ (4 : ℕ)⌋₊

theorem residueWidth_eq (h p : ℝ) :
    residueWidth h p = 2 * (h / p + 1) :=
  rfl

theorem residueWidth_sq (h p : ℝ) :
    residueWidth h p ^ 2 = 4 * (h / p + 1) ^ 2 := by
  unfold residueWidth
  ring

theorem residueWidth_nonneg {h p : ℝ} (hh : 0 ≤ h) (hp : 0 < p) :
    0 ≤ residueWidth h p :=
  mul_nonneg (by norm_num) (add_nonneg (div_nonneg hh hp.le) (by norm_num))

theorem residueWidth_sq_expand {h p : ℝ} (hp : p ≠ 0) :
    (h / p + 1) ^ 2 = h ^ 2 / p ^ 2 + 2 * h / p + 1 := by
  field_simp [hp]
  ring

/-! ### Prime-to-integer comparison and telescoping `∑ 1/n²` -/

theorem mem_primesLE_sdiff {w y p : ℕ} :
    p ∈ Nat.primesLE y \ Nat.primesLE w ↔
      Nat.Prime p ∧ w < p ∧ p ≤ y := by
  constructor
  · intro h
    have hy := Nat.mem_primesLE.mp (mem_sdiff.mp h).1
    have hw := (mem_sdiff.mp h).2
    have hnot : ¬ p ≤ w := fun hle => hw (Nat.mem_primesLE.mpr ⟨hle, hy.2⟩)
    exact ⟨hy.2, Nat.not_le.mp hnot, hy.1⟩
  · intro h
    exact mem_sdiff.mpr
      ⟨Nat.mem_primesLE.mpr ⟨h.2.2, h.1⟩,
        fun hp => (not_le_of_gt h.2.1) (Nat.le_of_mem_primesLE hp)⟩

theorem primesLE_subset_Icc (y : ℕ) :
    Nat.primesLE y ⊆ Icc 1 y := by
  intro p hp
  exact mem_Icc.mpr
    ⟨le_trans (by omega : (1 : ℕ) ≤ 2) (Nat.two_le_of_mem_primesLE hp),
      Nat.le_of_mem_primesLE hp⟩

theorem primesLE_sdiff_subset_Icc (w y : ℕ) :
    Nat.primesLE y \ Nat.primesLE w ⊆ Icc (w + 1) y := by
  intro p hp
  have hp' := (mem_primesLE_sdiff).mp hp
  exact mem_Icc.mpr ⟨Nat.succ_le_of_lt hp'.2.1, hp'.2.2⟩

/-- Prime sum is at most the integer sum of the same nonnegative weights. -/
theorem sum_residueWidth_sq_le_sum_Icc (h y : ℕ) :
    ∑ p ∈ Nat.primesLE y, residueWidth (h : ℝ) p ^ 2 ≤
      ∑ n ∈ Icc 1 y, residueWidth (h : ℝ) n ^ 2 :=
  sum_le_sum_of_subset_of_nonneg (primesLE_subset_Icc y) fun _ _ _ => sq_nonneg _

theorem sum_residueWidth_sq_sdiff_le_Icc (h w y : ℕ) :
    ∑ p ∈ Nat.primesLE y \ Nat.primesLE w, residueWidth (h : ℝ) p ^ 2 ≤
      ∑ n ∈ Icc (w + 1) y, residueWidth (h : ℝ) n ^ 2 :=
  sum_le_sum_of_subset_of_nonneg (primesLE_sdiff_subset_Icc w y) fun _ _ _ =>
    sq_nonneg _

private theorem one_lt_natCast_of_two_le {n : ℕ} (hn : 2 ≤ n) : (1 : ℝ) < n :=
  Nat.one_lt_cast.mpr (lt_of_lt_of_le (by omega : (1 : ℕ) < 2) hn)

/-- Telescoping comparison: `1/n² ≤ 1/(n(n-1))` for `n ≥ 2`. -/
theorem inv_sq_le_inv_pred_sub {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ)⁻¹) ^ 2 ≤ ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ := by
  have hnR : (1 : ℝ) < n := one_lt_natCast_of_two_le hn
  have hn0 : (0 : ℝ) < n := lt_trans (by norm_num) hnR
  have hn1p : (0 : ℝ) < (n : ℝ) - 1 := sub_pos.mpr hnR
  have hmul : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) * n :=
    mul_le_mul_of_nonneg_left (sub_le_self _ (by norm_num)) hn0.le
  have hinv : ((n : ℝ) * n)⁻¹ ≤ ((n : ℝ) * ((n : ℝ) - 1))⁻¹ :=
    inv_anti₀ (mul_pos hn0 hn1p) hmul
  have hsq : ((n : ℝ)⁻¹) ^ 2 = ((n : ℝ) * n)⁻¹ := by
    rw [inv_pow, sq]
  have hpart : ((n : ℝ) * ((n : ℝ) - 1))⁻¹ = ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ := by
    have hnne : (n : ℝ) ≠ 0 := hn0.ne'
    have hn1ne : ((n : ℝ) - 1) ≠ 0 := hn1p.ne'
    rw [inv_sub_inv hn1ne hnne]
    rw [show (n : ℝ) - ((n : ℝ) - 1) = 1 by ring, one_div, mul_comm ((n : ℝ) - 1)]
  rw [hsq]
  exact hinv.trans_eq hpart

private theorem sum_inv_pred_sub_Icc {z M : ℕ} (_hz : 2 ≤ z) (hM : z ≤ M) :
    ∑ n ∈ Icc z M, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) =
      ((z : ℝ) - 1)⁻¹ - (M : ℝ)⁻¹ := by
  refine Nat.le_induction ?base ?step M hM
  · simp [Icc_self]
  · intro M hM ih
    have hinsert : Icc z (M + 1) = insert (M + 1) (Icc z M) :=
      (insert_Icc_right_eq_Icc_add_one (show z ≤ M + 1 by omega)).symm
    have hnot : M + 1 ∉ Icc z M := fun h =>
      Nat.not_succ_le_self M (mem_Icc.mp h).2
    rw [hinsert, sum_insert hnot, ih]
    have hterm :
        (((M + 1 : ℕ) : ℝ) - 1)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹ =
          (M : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹ := by
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := Nat.cast_succ M
      rw [hcast]
      ring
    rw [hterm]
    ring

/-- Geometric/Chebyshev comparison `∑_{w < n ≤ y} 1/n² ≤ 1/w`. -/
theorem sum_inv_sq_Icc_succ_le {w y : ℕ} (hw : 1 ≤ w) :
    ∑ n ∈ Icc (w + 1) y, ((n : ℝ)⁻¹) ^ 2 ≤ (w : ℝ)⁻¹ := by
  by_cases hle : w + 1 ≤ y
  · have hz : 2 ≤ w + 1 := Nat.succ_le_succ hw
    have hpt : ∀ n ∈ Icc (w + 1) y,
        ((n : ℝ)⁻¹) ^ 2 ≤ ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ := fun n hn =>
      inv_sq_le_inv_pred_sub (le_trans hz (mem_Icc.mp hn).1)
    have hsum := sum_le_sum hpt
    have htel := sum_inv_pred_sub_Icc hz hle
    have hzcast : ((w + 1 : ℕ) : ℝ) - 1 = (w : ℝ) := by
      rw [Nat.cast_succ w]
      ring
    have hy0 : 0 ≤ (y : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hle' : (w : ℝ)⁻¹ - (y : ℝ)⁻¹ ≤ (w : ℝ)⁻¹ := sub_le_self _ hy0
    have htel' :
        ∑ n ∈ Icc (w + 1) y, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) =
          (w : ℝ)⁻¹ - (y : ℝ)⁻¹ := by
      simpa [hzcast] using htel
    exact hsum.trans ((le_of_eq htel').trans hle')
  · rw [Icc_eq_empty_of_lt (Nat.not_le.mp hle), sum_empty]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Harmonic comparison `∑_{n ≤ y} 1/n ≤ 1 + log y`. -/
theorem sum_inv_Icc_le_one_add_log (y : ℕ) :
    ∑ n ∈ Icc 1 y, (n : ℝ)⁻¹ ≤ 1 + Real.log y := by
  have hsum : ∑ n ∈ Icc 1 y, (n : ℝ)⁻¹ = (harmonic y : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    refine sum_congr rfl fun n _ => ?_
    simp [Rat.cast_inv, Rat.cast_natCast]
  rw [hsum]
  exact harmonic_le_one_add_log y

private theorem card_Icc_succ_le_self (w y : ℕ) :
    ((Icc (w + 1) y).card : ℝ) ≤ y := by
  have hsub : Icc (w + 1) y ⊆ Icc 1 y := by
    intro n hn
    have hn' := mem_Icc.mp hn
    exact mem_Icc.mpr
      ⟨le_trans (Nat.succ_le_succ (Nat.zero_le w)) hn'.1, hn'.2⟩
  have hle := card_le_card hsub
  have hcy : (Icc 1 y).card ≤ y := by
    rw [Nat.card_Icc]
    exact Nat.le_refl _
  exact Nat.cast_le.mpr (hle.trans hcy)

private theorem sum_add_one_div_sq {h : ℝ} {s : Finset ℕ}
    (hs : ∀ n ∈ s, n ≠ 0) :
    ∑ n ∈ s, (h / n + 1) ^ 2 =
      h ^ 2 * ∑ n ∈ s, ((n : ℝ)⁻¹) ^ 2 +
        2 * h * ∑ n ∈ s, (n : ℝ)⁻¹ + s.card := by
  have hpt : ∀ n ∈ s,
      (h / n + 1) ^ 2 = h ^ 2 * ((n : ℝ)⁻¹) ^ 2 + 2 * h * (n : ℝ)⁻¹ + 1 :=
    fun n hn => by
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hs n hn)
      have hexp := residueWidth_sq_expand (h := h) (p := n) hn0
      have hrew : h ^ 2 / n ^ 2 = h ^ 2 * ((n : ℝ)⁻¹) ^ 2 := by
        rw [div_eq_mul_inv, ← inv_pow]
      have hrew' : 2 * h / n = 2 * h * (n : ℝ)⁻¹ := by
        rw [div_eq_mul_inv]
      rw [hexp, hrew, hrew']
  rw [sum_congr rfl hpt, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
    sum_const, nsmul_eq_mul, mul_one]

/-- Paper finite bound:
`∑_{w < p ≤ y} 4(h/p+1)² ≤ 4(h²/w + 2h(1+log y) + y)`. -/
theorem sum_residueWidth_sq_Ioc_le {h w y : ℕ} (hw : 1 ≤ w) :
    ∑ p ∈ Nat.primesLE y \ Nat.primesLE w, residueWidth (h : ℝ) p ^ 2 ≤
      4 * ((h : ℝ) ^ 2 / w + 2 * h * (1 + Real.log y) + y) := by
  have hcmp := sum_residueWidth_sq_sdiff_le_Icc h w y
  have hs0' : ∀ n ∈ Icc (w + 1) y, n ≠ 0 := fun n hn =>
    Nat.one_le_iff_ne_zero.mp
      (le_trans (Nat.succ_le_succ (Nat.zero_le w)) (mem_Icc.mp hn).1)
  have hsq : ∀ n ∈ Icc (w + 1) y,
      residueWidth (h : ℝ) n ^ 2 = 4 * ((h : ℝ) / n + 1) ^ 2 := fun n _ =>
    residueWidth_sq _ _
  have hsum :
      ∑ n ∈ Icc (w + 1) y, residueWidth (h : ℝ) n ^ 2 =
        4 * ∑ n ∈ Icc (w + 1) y, ((h : ℝ) / n + 1) ^ 2 := by
    rw [sum_congr rfl hsq, mul_sum]
  have hexp := sum_add_one_div_sq (h := (h : ℝ)) hs0'
  have hinvsq := sum_inv_sq_Icc_succ_le (w := w) (y := y) hw
  have hinv : ∑ n ∈ Icc (w + 1) y, (n : ℝ)⁻¹ ≤ 1 + Real.log y := by
    have hsub : Icc (w + 1) y ⊆ Icc 1 y := by
      intro n hn
      have hn' := mem_Icc.mp hn
      exact mem_Icc.mpr
        ⟨le_trans (Nat.succ_le_succ (Nat.zero_le w)) hn'.1, hn'.2⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => inv_nonneg.mpr
      (Nat.cast_nonneg _)).trans (sum_inv_Icc_le_one_add_log y)
  have hcard := card_Icc_succ_le_self w y
  have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg _
  have hw0 : (0 : ℝ) < w := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : (0 : ℕ) < 1) hw)
  have hstep :
      (h : ℝ) ^ 2 * ∑ n ∈ Icc (w + 1) y, ((n : ℝ)⁻¹) ^ 2 +
          2 * h * ∑ n ∈ Icc (w + 1) y, (n : ℝ)⁻¹ +
            (Icc (w + 1) y).card
        ≤ (h : ℝ) ^ 2 / w + 2 * h * (1 + Real.log y) + y := by
    have h1 :
        (h : ℝ) ^ 2 * ∑ n ∈ Icc (w + 1) y, ((n : ℝ)⁻¹) ^ 2 ≤
          (h : ℝ) ^ 2 * (w : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hinvsq (sq_nonneg _)
    have h1' : (h : ℝ) ^ 2 * (w : ℝ)⁻¹ = (h : ℝ) ^ 2 / w := by
      rw [div_eq_mul_inv]
    have h2 :
        2 * (h : ℝ) * ∑ n ∈ Icc (w + 1) y, (n : ℝ)⁻¹ ≤
          2 * h * (1 + Real.log y) :=
      mul_le_mul_of_nonneg_left hinv (mul_nonneg (by norm_num) hh0)
    exact add_le_add (add_le_add (h1.trans (le_of_eq h1')) h2) hcard
  have : ∑ n ∈ Icc (w + 1) y, residueWidth (h : ℝ) n ^ 2 ≤
      4 * ((h : ℝ) ^ 2 / w + 2 * h * (1 + Real.log y) + y) := by
    rw [hsum, hexp]
    exact mul_le_mul_of_nonneg_left hstep (by norm_num)
  exact hcmp.trans this

/-- Crude full-range comparison `∑_{p ≤ y} c_p² ≤ ∑_{n ≤ y} c_n²`. -/
theorem sum_residueWidth_sq_le_sum_nat (h y : ℕ) :
    ∑ p ∈ Nat.primesLE y, residueWidth (h : ℝ) p ^ 2 ≤
      ∑ n ∈ Icc 1 y, 4 * ((h : ℝ) / n + 1) ^ 2 := by
  have hle := sum_residueWidth_sq_le_sum_Icc h y
  have hsq : ∀ n ∈ Icc 1 y,
      residueWidth (h : ℝ) n ^ 2 = 4 * ((h : ℝ) / n + 1) ^ 2 := fun n _ =>
    residueWidth_sq _ _
  rwa [sum_congr rfl hsq] at hle

/-- Absorb the linear remainder into `K h² / w` once it is small enough. -/
theorem sum_residueWidth_sq_le_mul_div {h w y : ℕ} {K : ℝ}
    (hw : 1 ≤ w) (_hK : 4 ≤ K)
    (hextra : 4 * (2 * (h : ℝ) * (1 + Real.log y) + y) ≤
      (K - 4) * (h : ℝ) ^ 2 / w) :
    ∑ p ∈ Nat.primesLE y \ Nat.primesLE w, residueWidth (h : ℝ) p ^ 2 ≤
      K * (h : ℝ) ^ 2 / w := by
  have hmain := sum_residueWidth_sq_Ioc_le (h := h) (w := w) (y := y) hw
  have hw0 : (0 : ℝ) < w :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : (0 : ℕ) < 1) hw)
  have hsplit :
      4 * ((h : ℝ) ^ 2 / w + 2 * h * (1 + Real.log y) + y) =
        4 * ((h : ℝ) ^ 2 / w) + 4 * (2 * h * (1 + Real.log y) + y) := by
    ring
  have h4 : 4 * ((h : ℝ) ^ 2 / w) = 4 * (h : ℝ) ^ 2 / w := by
    rw [mul_div_assoc]
  have hK4 : 4 * (h : ℝ) ^ 2 / w + (K - 4) * (h : ℝ) ^ 2 / w =
      K * (h : ℝ) ^ 2 / w := by
    rw [← add_div]
    exact congrArg (· / (w : ℝ))
      (by ring : 4 * (h : ℝ) ^ 2 + (K - 4) * (h : ℝ) ^ 2 = K * (h : ℝ) ^ 2)
  calc
    ∑ p ∈ Nat.primesLE y \ Nat.primesLE w, residueWidth (h : ℝ) p ^ 2
        ≤ 4 * ((h : ℝ) ^ 2 / w + 2 * h * (1 + Real.log y) + y) := hmain
    _ = 4 * ((h : ℝ) ^ 2 / w) + 4 * (2 * h * (1 + Real.log y) + y) := hsplit
    _ = 4 * (h : ℝ) ^ 2 / w + 4 * (2 * h * (1 + Real.log y) + y) := by rw [h4]
    _ ≤ 4 * (h : ℝ) ^ 2 / w + (K - 4) * (h : ℝ) ^ 2 / w :=
      _root_.add_le_add_right hextra (4 * (h : ℝ) ^ 2 / w)
    _ = K * (h : ℝ) ^ 2 / w := hK4

/-! ### Paper-scale `∑ c_p² ≪ G² / (log G)^4` -/

private theorem eventually_log_mul_le (C : ℝ) :
    ∀ᶠ t : ℝ in atTop, C + Real.log t ≤ t := by
  have hC : Tendsto (fun t : ℝ => C / t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
    refine (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.rpow_one]
  have hsum : Tendsto (fun t : ℝ => (C + Real.log t) / t) atTop (nhds 0) := by
    have hadd : Tendsto (fun t : ℝ => C / t + Real.log t / t) atTop (nhds (0 : ℝ)) := by
      simpa [add_zero] using hC.add hlog
    refine hadd.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp [ht]
  filter_upwards [hsum.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with t hball ht0
  have habs : |(C + Real.log t) / t| < 1 := by
    have : dist ((C + Real.log t) / t) 0 < 1 := Metric.mem_ball.mp hball
    rw [Real.dist_eq, sub_zero] at this
    exact this
  have : |C + Real.log t| < t := by
    rwa [abs_div, abs_of_pos ht0, div_lt_one ht0] at habs
  exact (le_abs_self (C + Real.log t)).trans this.le

/-- With paper cutoffs `w = (log G)^4`, `h ≤ G`, `L ≤ 2κ log G` and
`y ≤ 5 L G`, eventually `∑_{w < p ≤ y} c_p² ≤ 16 G² / (log G)^4`. -/
theorem eventually_sum_residueWidth_sq_le (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ G : ℝ in atTop,
      ∀ (L : ℝ) (h y : ℕ),
        1 ≤ L →
        L ≤ 2 * κ * Real.log G →
        (h : ℝ) ≤ G →
        (y : ℝ) ≤ 5 * L * G →
        ∑ p ∈ Nat.primesLE y \ Nat.primesLE (residueMcDiarmidCutoff G),
            residueWidth (h : ℝ) p ^ 2 ≤
          16 * G ^ 2 / Real.log G ^ (4 : ℕ) := by
  have hpoly :
      Tendsto (fun t : ℝ => (3 + 5 * κ) * t ^ (5 : ℕ) * Real.exp (-t))
        atTop (nhds 0) := by
    have h0 :
        Tendsto (fun t : ℝ => (3 + 5 * κ) * (t ^ (5 : ℕ) * Real.exp (-t)))
          atTop (nhds 0) := by
      simpa [mul_zero] using
        (tendsto_const_nhds.mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5) :
          Tendsto (fun t : ℝ => (3 + 5 * κ) * (t ^ (5 : ℕ) * Real.exp (-t)))
            atTop (nhds ((3 + 5 * κ) * 0)))
    exact h0.congr fun t =>
      (mul_assoc ((3 + 5 * κ) : ℝ) (t ^ (5 : ℕ)) (Real.exp (-t))).symm
  filter_upwards [
    eventually_gt_atTop (Real.exp 2),
    eventually_gt_atTop (1 : ℝ),
    (hpoly.comp Real.tendsto_log_atTop).eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)),
    Real.tendsto_log_atTop.eventually (eventually_log_mul_le (Real.log (10 * κ))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
    G hGexp hG1 hpolyball hlog10κ ht1
  intro L h y hL hLlog hh hy
  have hGpos : 0 < G := lt_trans (by norm_num) hG1
  have ht : 2 < Real.log G := (Real.lt_log_iff_exp_lt hGpos).mpr hGexp
  have htpos : 0 < Real.log G := lt_trans (by norm_num) ht
  have ht2 : (2 : ℝ) ≤ Real.log G := ht.le
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  set t := Real.log G
  set w := residueMcDiarmidCutoff G
  have ht4 : (16 : ℝ) ≤ t ^ (4 : ℕ) := by
    have hpow : (2 : ℝ) ^ (4 : ℕ) ≤ t ^ (4 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) ht2 4
    have h16 : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
    rwa [h16] at hpow
  have hwR : t ^ (4 : ℕ) - 1 ≤ w := by
    have hgt : t ^ (4 : ℕ) < (w : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (t ^ (4 : ℕ))
      simpa [w, residueMcDiarmidCutoff, t] using this
    linarith
  have hw1 : 1 ≤ w := by
    have : (1 : ℝ) ≤ w := by
      have : (1 : ℝ) ≤ t ^ (4 : ℕ) - 1 := by linarith [ht4]
      exact this.trans hwR
    exact_mod_cast this
  have hw0 : (0 : ℝ) < w :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : (0 : ℕ) < 1) hw1)
  have hhalf : t ^ (4 : ℕ) / 2 ≤ t ^ (4 : ℕ) - 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [ht4]
  have hinvw : (w : ℝ)⁻¹ ≤ 2 / t ^ (4 : ℕ) := by
    have hwge : t ^ (4 : ℕ) / 2 ≤ w := hhalf.trans hwR
    have ht40 : 0 < t ^ (4 : ℕ) := pow_pos htpos 4
    have : (w : ℝ)⁻¹ ≤ (t ^ (4 : ℕ) / 2)⁻¹ :=
      inv_anti₀ (div_pos ht40 (by norm_num)) hwge
    have hrew : (t ^ (4 : ℕ) / 2)⁻¹ = 2 / t ^ (4 : ℕ) := by
      rw [inv_div]
    exact this.trans (le_of_eq hrew)
  by_cases hy0 : y = 0
  · subst hy0
    have hempty : Nat.primesLE 0 \ Nat.primesLE w = ∅ := by
      simp [Nat.primesLE_zero]
    rw [hempty, sum_empty]
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (pow_nonneg htpos.le 4)
  · have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
    have hmain := sum_residueWidth_sq_Ioc_le (h := h) (w := w) (y := y) hw1
    have hypos : 0 < (y : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : (0 : ℕ) < 1) hy1)
    have h5LG : 0 < 5 * L * G := mul_pos (mul_pos (by norm_num) hLpos) hGpos
    have hylog : Real.log y ≤ Real.log (5 * L * G) :=
      (Real.log_le_log_iff hypos h5LG).mpr hy
    have h10 : 0 < 10 * κ * t * G :=
      mul_pos (mul_pos (mul_pos (by norm_num) hκ) htpos) hGpos
    have h5le : 5 * L * G ≤ 10 * κ * t * G := by
      have : 5 * L * G ≤ 5 * (2 * κ * t) * G :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLlog (by norm_num)) hGpos.le
      have hring : 5 * (2 * κ * t) * G = 10 * κ * t * G := by ring
      rwa [hring] at this
    have hlog5 : Real.log (5 * L * G) ≤ Real.log (10 * κ * t * G) :=
      (Real.log_le_log_iff h5LG h10).mpr h5le
    have hlog10 : Real.log (10 * κ * t * G) =
        Real.log (10 * κ) + Real.log t + t := by
      have h10κ : (10 * κ : ℝ) ≠ 0 :=
        mul_ne_zero (by norm_num) hκ.ne'
      have htne : t ≠ 0 := htpos.ne'
      have hprod : 10 * κ * t * G = (10 * κ) * (t * G) := by ring
      calc
        Real.log (10 * κ * t * G)
            = Real.log ((10 * κ) * (t * G)) := by rw [hprod]
        _ = Real.log (10 * κ) + Real.log (t * G) :=
            Real.log_mul h10κ (mul_ne_zero htne hGpos.ne')
        _ = Real.log (10 * κ) + (Real.log t + Real.log G) := by
            rw [Real.log_mul htne hGpos.ne']
        _ = Real.log (10 * κ) + Real.log t + t := by
            rw [show Real.log G = t from rfl, add_assoc]
    have hlogy2 : Real.log y ≤ 2 * t := by
      have : Real.log (10 * κ) + Real.log t + t ≤ 2 * t := by
        linarith [hlog10κ]
      exact hylog.trans (hlog5.trans (hlog10.trans_le this))
    have hextra :
        2 * (h : ℝ) * (1 + Real.log y) + y ≤ t * G * (6 + 10 * κ) := by
      have h1y : 1 + Real.log y ≤ 3 * t := by
        have : (1 : ℝ) ≤ t := ht1
        linarith [hlogy2]
      have h2h : 2 * (h : ℝ) * (1 + Real.log y) ≤ 2 * G * (3 * t) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hh (by norm_num)) h1y
          (add_nonneg (by norm_num)
            (Real.log_nonneg (Nat.one_le_cast.mpr hy1)))
          (mul_nonneg (by norm_num) hGpos.le)
      have h2h' : 2 * G * (3 * t) = 6 * t * G := by ring
      have hy' : (y : ℝ) ≤ 10 * κ * t * G := hy.trans h5le
      have : 2 * (h : ℝ) * (1 + Real.log y) + y ≤ 6 * t * G + 10 * κ * t * G :=
        add_le_add (h2h.trans (le_of_eq h2h')) hy'
      have hring : 6 * t * G + 10 * κ * t * G = t * G * (6 + 10 * κ) := by ring
      rwa [hring] at this
    have hnum :
        4 * ((h : ℝ) ^ 2 / w + 2 * h * (1 + Real.log y) + y) ≤
          8 * G ^ 2 / t ^ (4 : ℕ) + 4 * (t * G * (6 + 10 * κ)) := by
      have hh2 : (h : ℝ) ^ 2 ≤ G ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hh 2
      have hhw : (h : ℝ) ^ 2 / w ≤ G ^ 2 * (w : ℝ)⁻¹ := by
        have : (h : ℝ) ^ 2 / w = (h : ℝ) ^ 2 * (w : ℝ)⁻¹ := by
          rw [div_eq_mul_inv]
        rw [this]
        exact mul_le_mul_of_nonneg_right hh2 (inv_nonneg.mpr hw0.le)
      have hhw' : G ^ 2 * (w : ℝ)⁻¹ ≤ G ^ 2 * (2 / t ^ (4 : ℕ)) :=
        mul_le_mul_of_nonneg_left hinvw (sq_nonneg _)
      have hhw'' : G ^ 2 * (2 / t ^ (4 : ℕ)) = 2 * (G ^ 2 / t ^ (4 : ℕ)) :=
        mul_div_left_comm (G ^ 2) 2 (t ^ (4 : ℕ))
      have hleft : 4 * ((h : ℝ) ^ 2 / w) ≤ 8 * G ^ 2 / t ^ (4 : ℕ) := by
        have := mul_le_mul_of_nonneg_left
          (hhw.trans (hhw'.trans (le_of_eq hhw''))) (by norm_num : (0 : ℝ) ≤ 4)
        have hrew : 4 * (2 * (G ^ 2 / t ^ (4 : ℕ))) = 8 * G ^ 2 / t ^ (4 : ℕ) := by
          rw [← mul_div_assoc, ← mul_div_assoc, ← mul_assoc]
          norm_num
        exact this.trans (le_of_eq hrew)
      have hright :
          4 * (2 * (h : ℝ) * (1 + Real.log y) + y) ≤
            4 * (t * G * (6 + 10 * κ)) :=
        mul_le_mul_of_nonneg_left hextra (by norm_num)
      have hsplit :
          4 * ((h : ℝ) ^ 2 / w + 2 * h * (1 + Real.log y) + y) =
            4 * ((h : ℝ) ^ 2 / w) +
              4 * (2 * (h : ℝ) * (1 + Real.log y) + y) := by
        ring
      rw [hsplit]
      exact add_le_add hleft hright
    have hexpG : Real.exp t = G := Real.exp_log hGpos
    have hpoly' :
        (3 + 5 * κ) * t ^ (5 : ℕ) * Real.exp (-t) < 1 := by
      have : |((3 + 5 * κ) * t ^ (5 : ℕ) * Real.exp (-t))| < 1 := by
        simpa [Metric.mem_ball, Real.dist_eq, sub_zero, Function.comp_apply, t]
          using hpolyball
      exact (le_abs_self _).trans_lt this
    have hpoly_le : (3 + 5 * κ) * t ^ (5 : ℕ) ≤ G := by
      have hle : (3 + 5 * κ) * t ^ (5 : ℕ) * Real.exp (-t) ≤ 1 := hpoly'.le
      have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_nonneg t)
      have hLHS :
          (3 + 5 * κ) * t ^ (5 : ℕ) * Real.exp (-t) * Real.exp t =
            (3 + 5 * κ) * t ^ (5 : ℕ) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      have hRHS : 1 * Real.exp t = G := by
        rw [one_mul, hexpG]
      rwa [hLHS, hRHS] at hmul
    have htail : 4 * (t * G * (6 + 10 * κ)) ≤ 8 * G ^ 2 / t ^ (4 : ℕ) := by
      rw [le_div_iff₀ (pow_pos htpos 4)]
      have hring :
          4 * (t * G * (6 + 10 * κ)) * t ^ (4 : ℕ) =
            8 * G * ((3 + 5 * κ) * t ^ (5 : ℕ)) := by
        have : 6 + 10 * κ = 2 * (3 + 5 * κ) := by ring
        rw [this]
        ring
      rw [hring]
      have hrew : 8 * G * ((3 + 5 * κ) * t ^ (5 : ℕ)) ≤ 8 * G * G :=
        mul_le_mul_of_nonneg_left hpoly_le (mul_nonneg (by norm_num) hGpos.le)
      have hsq : 8 * G * G = 8 * G ^ 2 := by ring
      rwa [hsq] at hrew
    have h16 : 8 * G ^ 2 / t ^ (4 : ℕ) + 8 * G ^ 2 / t ^ (4 : ℕ) =
        16 * G ^ 2 / t ^ (4 : ℕ) := by
      rw [← two_mul, mul_div_assoc]
      have hrew : 2 * (8 * (G ^ 2 / t ^ (4 : ℕ))) = 16 * G ^ 2 / t ^ (4 : ℕ) := by
        rw [← mul_div_assoc, ← mul_div_assoc, ← mul_assoc]
        norm_num
      exact hrew
    have : 4 * ((h : ℝ) ^ 2 / w + 2 * h * (1 + Real.log y) + y) ≤
        16 * G ^ 2 / t ^ (4 : ℕ) :=
      hnum.trans
        ((_root_.add_le_add_right htail (8 * G ^ 2 / t ^ (4 : ℕ))).trans
          (le_of_eq h16))
    exact hmain.trans this

/-! ### Residue class occupancy in a length-`h` interval -/

/-- At most `h/p+1` terms of a fixed residue in `{0,…,h-1}`. -/
theorem card_range_add_mod_le (a h p r : ℕ) (hp : 0 < p) :
    #{k ∈ range h | (a + k) % p = r % p} ≤ h / p + 1 := by
  set s := (range h).filter (fun k => (a + k) % p = r % p)
  let f : ℕ → ℕ := fun k => k / p
  have hinj : Set.InjOn f s := by
    intro k hk k' hk' hf
    have hs := (mem_filter.mp hk).2
    have hs' := (mem_filter.mp hk').2
    have hcong : a % p + k % p ≡ a % p + k' % p [MOD p] := by
      change (a % p + k % p) % p = (a % p + k' % p) % p
      rw [← Nat.add_mod, ← Nat.add_mod, hs, hs']
    have hmod : k % p = k' % p := by
      simpa [Nat.ModEq, Nat.mod_mod] using
        (Nat.ModEq.add_left_cancel' (a % p) hcong)
    have hkdec := (Nat.div_add_mod k p).symm
    have hk'dec := (Nat.div_add_mod k' p).symm
    rw [hkdec, hk'dec, show k / p = k' / p from hf, hmod]
  have himg : s.image f ⊆ range (h / p + 1) := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hm
    have hklt : k < h := mem_range.mp (mem_filter.mp hk).1
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hklt)))
  have hcard : (s.image f).card = s.card := card_image_of_injOn hinj
  have hle : (s.image f).card ≤ (range (h / p + 1)).card := card_le_card himg
  have : s.card ≤ h / p + 1 := by
    simpa [hcard, card_range] using hle
  simpa [s] using this

/-- Paper occupancy: a residue class meets an interval of length `h` in
at most `h/p+1` points. -/
theorem card_Ico_mod_le (a h p r : ℕ) (hp : 0 < p) :
    #{n ∈ Ico a (a + h) | n % p = r % p} ≤ h / p + 1 := by
  let e : ℕ ↪ ℕ := ⟨fun k => a + k, add_right_injective a⟩
  have himg :
      ((range h).filter (fun k => (a + k) % p = r % p)).map e =
        (Ico a (a + h)).filter (fun n => n % p = r % p) := by
    ext n
    constructor
    · intro hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hn
      have hk' := mem_filter.mp hk
      refine mem_filter.mpr ⟨mem_Ico.mpr ⟨?_, ?_⟩, hk'.2⟩
      · exact Nat.le_add_right a k
      · exact Nat.add_lt_add_left (mem_range.mp hk'.1) a
    · intro hn
      have hn' := mem_filter.mp hn
      have hIco := mem_Ico.mp hn'.1
      refine Finset.mem_map.mpr ⟨n - a, mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · exact mem_range.mpr (Nat.sub_lt_left_of_lt_add hIco.1 hIco.2)
      · rw [Nat.add_sub_cancel' hIco.1]
        exact hn'.2
      · simp only [e, Function.Embedding.coeFn_mk]
        exact Nat.add_sub_cancel' hIco.1
  have hcard :
      #{n ∈ Ico a (a + h) | n % p = r % p} =
        #{k ∈ range h | (a + k) % p = r % p} := by
    rw [← himg, Finset.card_map]
  rw [hcard]
  exact card_range_add_mod_le a h p r hp

theorem card_Ico_mod_le_real (a h p r : ℕ) (hp : 0 < p) :
    (#{n ∈ Ico a (a + h) | n % p = r % p} : ℝ) ≤ (h : ℝ) / p + 1 := by
  have hN := card_Ico_mod_le a h p r hp
  have hdiv : ((h / p : ℕ) : ℝ) ≤ (h : ℝ) / p := Nat.cast_div_le
  have : (#{n ∈ Ico a (a + h) | n % p = r % p} : ℝ) ≤ (h / p + 1 : ℕ) :=
    Nat.cast_le.mpr hN
  have hcast : ((h / p + 1 : ℕ) : ℝ) = (h / p : ℕ) + 1 := by simp
  exact this.trans (hcast.trans_le (_root_.add_le_add_left hdiv (1 : ℝ)))

/-! ### Survivor-count Lipschitz when one residue flips -/

/-- Integers in `J` avoiding the chosen residue of each coordinate. -/
def residueAvoidCount {n : ℕ} (moduli : Fin n → ℕ) (J : Finset ℕ)
    (σ : Fin n → ℕ) : ℕ :=
  #{k ∈ J | ∀ i : Fin n, k % moduli i ≠ σ i % moduli i}

instance residueAvoidCount.decidable {n : ℕ} (moduli : Fin n → ℕ)
    (σ : Fin n → ℕ) :
    DecidablePred (fun k : ℕ => ∀ i : Fin n, k % moduli i ≠ σ i % moduli i) :=
  fun a => Nat.decidableForallFin fun i => a % moduli i ≠ σ i % moduli i

private theorem abs_card_sub_le_sdiff {α : Type*} [DecidableEq α] (s t : Finset α) :
    |(s.card : ℝ) - (t.card : ℝ)| ≤
      ((s \ t).card : ℝ) + ((t \ s).card : ℝ) := by
  have hs := card_sdiff_add_card_inter s t
  have ht : (t \ s).card + (t ∩ s).card = t.card := card_sdiff_add_card_inter t s
  have hinter : s ∩ t = t ∩ s := inter_comm _ _
  have hsR : (s.card : ℝ) = (s \ t).card + (s ∩ t).card := by
    exact_mod_cast hs.symm
  have htR : (t.card : ℝ) = (t \ s).card + (s ∩ t).card := by
    rw [hinter]
    exact_mod_cast ht.symm
  have hdiff : (s.card : ℝ) - t.card = ((s \ t).card : ℝ) - (t \ s).card := by
    rw [hsR, htR]
    ring
  rw [hdiff]
  have hnn1 : 0 ≤ ((s \ t).card : ℝ) := Nat.cast_nonneg _
  have hnn2 : 0 ≤ ((t \ s).card : ℝ) := Nat.cast_nonneg _
  have htri := abs_sub_le ((s \ t).card : ℝ) (0 : ℝ) ((t \ s).card : ℝ)
  simpa [abs_of_nonneg hnn1, abs_of_nonneg hnn2, sub_zero, zero_sub, abs_neg] using htri

/-- Flipping coordinate `i` changes the survivor count by at most the
two residue-class occupancies in `J`. -/
theorem residueAvoidCount_update_le {n : ℕ} (moduli : Fin n → ℕ)
    (J : Finset ℕ) (σ : Fin n → ℕ) (i : Fin n) (b : ℕ) :
    |((residueAvoidCount moduli J (Function.update σ i b) : ℝ) -
        (residueAvoidCount moduli J σ : ℝ))| ≤
      (#{k ∈ J | k % moduli i = σ i % moduli i} : ℝ) +
        #{k ∈ J | k % moduli i = b % moduli i} := by
  set A := (J.filter (fun k => ∀ j : Fin n, k % moduli j ≠ σ j % moduli j))
  set B :=
    (J.filter (fun k =>
      ∀ j : Fin n, k % moduli j ≠ Function.update σ i b j % moduli j))
  have hA : residueAvoidCount moduli J σ = A.card := by
    unfold residueAvoidCount A
    exact congrArg Finset.card
      (filter_congr_decidable J _
        (residueAvoidCount.decidable moduli σ))
  have hB : residueAvoidCount moduli J (Function.update σ i b) = B.card := by
    unfold residueAvoidCount B
    exact congrArg Finset.card
      (filter_congr_decidable J _
        (residueAvoidCount.decidable moduli (Function.update σ i b)))
  rw [hA, hB]
  classical
  have hAB : A \ B ⊆ J.filter (fun k => k % moduli i = b % moduli i) := by
    intro k hk
    have hkA := mem_sdiff.mp hk
    have hkJ : k ∈ J := (mem_filter.mp hkA.1).1
    have hσ : ∀ j : Fin n, k % moduli j ≠ σ j % moduli j :=
      (mem_filter.mp hkA.1).2
    have hnot : ¬ ∀ j : Fin n,
        k % moduli j ≠ Function.update σ i b j % moduli j := by
      intro hall
      exact hkA.2 (mem_filter.mpr ⟨hkJ, hall⟩)
    rw [not_forall] at hnot
    obtain ⟨j, hj⟩ := hnot
    have hj' : k % moduli j = Function.update σ i b j % moduli j :=
      not_ne_iff.mp hj
    have hji : j = i := by
      by_contra hne
      have : Function.update σ i b j = σ j := Function.update_of_ne hne _ _
      rw [this] at hj'
      exact (hσ j) hj'
    subst hji
    simp only [Function.update_self] at hj'
    exact mem_filter.mpr ⟨hkJ, hj'⟩
  have hBA : B \ A ⊆ J.filter (fun k => k % moduli i = σ i % moduli i) := by
    intro k hk
    have hkB := mem_sdiff.mp hk
    have hkJ : k ∈ J := (mem_filter.mp hkB.1).1
    have hσu : ∀ j : Fin n,
        k % moduli j ≠ Function.update σ i b j % moduli j :=
      (mem_filter.mp hkB.1).2
    have hnot : ¬ ∀ j : Fin n, k % moduli j ≠ σ j % moduli j := by
      intro hall
      exact hkB.2 (mem_filter.mpr ⟨hkJ, hall⟩)
    rw [not_forall] at hnot
    obtain ⟨j, hj⟩ := hnot
    have hj' : k % moduli j = σ j % moduli j := not_ne_iff.mp hj
    have hji : j = i := by
      by_contra hne
      have : Function.update σ i b j = σ j := Function.update_of_ne hne _ _
      have : k % moduli j ≠ σ j % moduli j := by
        simpa [this] using hσu j
      exact this hj'
    subst hji
    exact mem_filter.mpr ⟨hkJ, hj'⟩
  have h1 : ((A \ B).card : ℝ) ≤
      #{k ∈ J | k % moduli i = b % moduli i} :=
    Nat.cast_le.mpr (card_le_card hAB)
  have h2 : ((B \ A).card : ℝ) ≤
      #{k ∈ J | k % moduli i = σ i % moduli i} :=
    Nat.cast_le.mpr (card_le_card hBA)
  rw [abs_sub_comm]
  exact (abs_card_sub_le_sdiff A B).trans
    ((add_le_add h1 h2).trans_eq (add_comm _ _))

/-- McDiarmid width: flipping residue `i` in a length-`h` cell changes
the survivor count by at most `c_{p_i} = 2(h/p_i+1)`. -/
theorem residueAvoidCount_lipschitz {n : ℕ} (moduli : Fin n → ℕ)
    (a h : ℕ) (σ : Fin n → ℕ) (i : Fin n) (b : ℕ)
    (hp : 0 < moduli i) :
    |((residueAvoidCount moduli (Ico a (a + h)) (Function.update σ i b) : ℝ) -
        (residueAvoidCount moduli (Ico a (a + h)) σ : ℝ))| ≤
      residueWidth h (moduli i) := by
  have hle := residueAvoidCount_update_le moduli (Ico a (a + h)) σ i b
  have h1 := card_Ico_mod_le_real a h (moduli i) (σ i) hp
  have h2 := card_Ico_mod_le_real a h (moduli i) b hp
  have hsumle : (#{k ∈ Ico a (a + h) | k % moduli i = σ i % moduli i} : ℝ) +
        #{k ∈ Ico a (a + h) | k % moduli i = b % moduli i} ≤
      2 * ((h : ℝ) / moduli i + 1) := by
    have hadd := add_le_add h1 h2
    have htwo :
        ((h : ℝ) / moduli i + 1) + ((h : ℝ) / moduli i + 1) =
          2 * ((h : ℝ) / moduli i + 1) := by ring
    exact hadd.trans_eq htwo
  exact hle.trans (hsumle.trans (le_of_eq (residueWidth_eq (h : ℝ) (moduli i)).symm))

/-! ### Abstract Lipschitz on `Fin n → ℝ` -/

/-- Walk from `x` to `y` by replacing the first `k` coordinates. -/
def coordMix {n : ℕ} {α : Type*} (x y : Fin n → α) (k : ℕ) : Fin n → α :=
  fun i => if i.val < k then y i else x i

theorem coordMix_zero {n : ℕ} {α : Type*} (x y : Fin n → α) :
    coordMix x y 0 = x := by
  funext i
  simp [coordMix]

theorem coordMix_length {n : ℕ} {α : Type*} (x y : Fin n → α) :
    coordMix x y n = y := by
  funext i
  simp [coordMix, i.isLt]

theorem coordMix_succ {n : ℕ} {α : Type*} (x y : Fin n → α) {k : ℕ}
    (hk : k < n) :
    coordMix x y (k + 1) =
      Function.update (coordMix x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
  funext i
  by_cases hieq : i.val = k
  · have hi : i = ⟨k, hk⟩ := Fin.ext hieq
    rw [hi, Function.update_self, coordMix]
    simp [Nat.lt_succ_self k]
  · have hne : i ≠ ⟨k, hk⟩ := fun h => hieq (congrArg Fin.val h)
    rw [Function.update_of_ne hne, coordMix, coordMix]
    by_cases hlt : i.val < k
    · have hlt' : i.val < k + 1 := Nat.lt_succ_of_lt hlt
      simp [hlt, hlt']
    · have hlt' : ¬ i.val < k + 1 := by omega
      simp [hlt, hlt']

private theorem abs_telescope (f : ℕ → ℝ) (n : ℕ) :
    |f n - f 0| ≤ ∑ k ∈ range n, |f (k + 1) - f k| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htri : |f (n + 1) - f 0| ≤ |f (n + 1) - f n| + |f n - f 0| :=
      abs_sub_le _ _ _
    calc
      |f (n + 1) - f 0|
          ≤ |f (n + 1) - f n| + |f n - f 0| := htri
      _ ≤ |f (n + 1) - f n| + ∑ k ∈ range n, |f (k + 1) - f k| :=
        _root_.add_le_add_right ih |f (n + 1) - f n|
      _ = ∑ k ∈ range (n + 1), |f (k + 1) - f k| := by
        rw [sum_range_succ, add_comm]

/-- Changing one real coordinate costs at most `c i`, hence the full
displacement is at most `∑ c_i`. This is the McDiarmid Lipschitz constant
on `Fin n → ℝ`. -/
theorem coord_update_lipschitz {n : ℕ} (F : (Fin n → ℝ) → ℝ) (c : Fin n → ℝ)
    (hLip : ∀ (x : Fin n → ℝ) (i : Fin n) (a b : ℝ),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i)
    (x y : Fin n → ℝ) :
    |F y - F x| ≤ ∑ i : Fin n, c i := by
  have hstep : ∀ k : ℕ, (hk : k < n) →
      |F (coordMix x y (k + 1)) - F (coordMix x y k)| ≤ c ⟨k, hk⟩ :=
    fun k hk => by
      have hmix := coordMix_succ (α := ℝ) x y hk
      rw [hmix]
      have hxk : coordMix x y k ⟨k, hk⟩ = x ⟨k, hk⟩ := by
        simp [coordMix]
      have hx : F (coordMix x y k) =
          F (Function.update (coordMix x y k) ⟨k, hk⟩ (x ⟨k, hk⟩)) := by
        rw [← hxk, Function.update_eq_self]
      rw [hx]
      exact hLip (coordMix x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) (x ⟨k, hk⟩)
  have hchain :
      |F (coordMix x y n) - F (coordMix x y 0)| ≤
        ∑ k ∈ range n, |F (coordMix x y (k + 1)) - F (coordMix x y k)| :=
    abs_telescope (fun k => F (coordMix x y k)) n
  rw [coordMix_length, coordMix_zero] at hchain
  refine hchain.trans ?_
  rw [sum_fin_eq_sum_range]
  refine sum_le_sum fun k hk => ?_
  have hk' : k < n := mem_range.mp hk
  have hite : (if h : k < n then c ⟨k, h⟩ else 0) = c ⟨k, hk'⟩ := dif_pos hk'
  rw [hite]
  exact hstep k hk'

theorem coord_update_self {n : ℕ} (F : (Fin n → ℝ) → ℝ) (c : Fin n → ℝ)
    (hLip : ∀ (x : Fin n → ℝ) (i : Fin n) (a b : ℝ),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i)
    (x : Fin n → ℝ) (i : Fin n) (a : ℝ) :
    |F (Function.update x i a) - F x| ≤ c i := by
  have hx : F x = F (Function.update x i (x i)) := by
    rw [Function.update_eq_self]
  rw [hx]
  exact hLip x i a (x i)

/-! ### Bernoulli McDiarmid on `{0,1}` coordinates -/

/-- `{0,1}`-valued reading of a finite subset of `Fin n`. -/
def boolCoord {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ s then true else false

/-- Real indicators `1_{i ∈ s}`. -/
noncomputable def boolToReal {n : ℕ} (x : Fin n → Bool) : Fin n → ℝ :=
  fun i => if x i then (1 : ℝ) else 0

theorem boolCoord_insert {n : ℕ} {s : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ s) :
    boolCoord (insert i s) = Function.update (boolCoord s) i true := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [boolCoord, Function.update_self, hi]
  · rw [Function.update_of_ne hji]
    simp [boolCoord, mem_insert, hji]

theorem boolToReal_update {n : ℕ} (x : Fin n → Bool) (i : Fin n) (v : Bool) :
    boolToReal (Function.update x i v) =
      Function.update (boolToReal x) i (if v then 1 else 0) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [boolToReal, Function.update_self]
  · simp [boolToReal, Function.update_of_ne hji]

/-- One-sided McDiarmid on Boolean coordinates, via the Bernoulli product
already proved in `ModelConcentration`. -/
theorem bernoulli_bounded_diff_of_boolCoord {n : ℕ}
    (q : Fin n → ℝ) (F : (Fin n → Bool) → ℝ) (c : Fin n → ℝ) {u : ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hc : ∀ i, 0 ≤ c i)
    (hLip : ∀ (x : Fin n → Bool) (i : Fin n) (a b : Bool),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i)
    (hu : 0 < u) :
    ∑ s ∈ (univ : Finset (Fin n)).powerset.filter
        (fun s => u ≤ F (boolCoord s) -
          indepBernoulliExpect univ q (fun t => F (boolCoord t))),
      indepBernoulliMass univ q s
      ≤ if ∑ i : Fin n, c i ^ 2 = 0 then 0
        else Real.exp (-u ^ 2 / ∑ i : Fin n, c i ^ 2) := by
  have hI0 : ∀ i ∈ (univ : Finset (Fin n)), 0 ≤ q i := fun i _ => hq0 i
  have hI1 : ∀ i ∈ (univ : Finset (Fin n)), q i ≤ 1 := fun i _ => hq1 i
  have hcI : ∀ i ∈ (univ : Finset (Fin n)), 0 ≤ c i := fun i _ => hc i
  have hdiff : ∀ s : Finset (Fin n), ∀ i ∈ univ, i ∉ s →
      |F (boolCoord (insert i s)) - F (boolCoord s)| ≤ c i :=
    fun s i _ his => by
      have hfalse : boolCoord s i = false := by simp [boolCoord, his]
      have hx : F (boolCoord s) = F (Function.update (boolCoord s) i false) := by
        rw [← hfalse, Function.update_eq_self]
      rw [boolCoord_insert his, hx]
      exact hLip (boolCoord s) i true false
  have hsum : ∑ i ∈ (univ : Finset (Fin n)), c i ^ 2 = ∑ i : Fin n, c i ^ 2 :=
    rfl
  simpa [hsum] using
    bernoulli_bounded_diff_one_sided (univ : Finset (Fin n)) q
      (fun s => F (boolCoord s)) c hI0 hI1 hcI hdiff hu

/-- If `F : (Fin n → ℝ) → ℝ` changes by at most `c i` when coordinate `i`
is rewritten, the Lipschitz numbers fit the Boolean product and the
Bernoulli one-sided tail applies. -/
theorem realCoord_bool_one_sided {n : ℕ}
    (q : Fin n → ℝ) (F : (Fin n → ℝ) → ℝ) (c : Fin n → ℝ) {u : ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hc : ∀ i, 0 ≤ c i)
    (hLip : ∀ (x : Fin n → ℝ) (i : Fin n) (a b : ℝ),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i)
    (hu : 0 < u) :
    ∑ s ∈ (univ : Finset (Fin n)).powerset.filter
        (fun s => u ≤ F (boolToReal (boolCoord s)) -
          indepBernoulliExpect univ q
            (fun t => F (boolToReal (boolCoord t)))),
      indepBernoulliMass univ q s
      ≤ if ∑ i : Fin n, c i ^ 2 = 0 then 0
        else Real.exp (-u ^ 2 / ∑ i : Fin n, c i ^ 2) := by
  refine bernoulli_bounded_diff_of_boolCoord q (fun x => F (boolToReal x)) c
    hq0 hq1 hc ?_ hu
  intro x i a b
  rw [boolToReal_update, boolToReal_update]
  exact hLip (boolToReal x) i _ _

end PrimeGapNormality.Prime
