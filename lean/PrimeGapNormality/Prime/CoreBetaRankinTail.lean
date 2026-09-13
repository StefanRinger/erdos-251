import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite Rankin tail with parameter eight

This is a scalar estimate only.  It has no sieve, weight, or probability
content.  The strict tail is converted to a natural floor endpoint and then
bounded by a finite geometric sum.
-/

namespace PrimeGapNormality.Prime.CoreBetaRankinTail

open Finset

private theorem pow_div_factorial_le_exp_eight (x : ℝ) (r : ℕ)
    (hx : 0 ≤ x) :
    x ^ r / (r.factorial : ℝ) ≤ Real.exp (8 * x) / (8 : ℝ) ^ r := by
  have hraw := Real.pow_div_factorial_le_exp (x := (8 : ℝ) * x)
    (mul_nonneg (by norm_num) hx) r
  have h8 : (0 : ℝ) < (8 : ℝ) ^ r := pow_pos (by norm_num) _
  have hfac : (r.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have heq :
      x ^ r / (r.factorial : ℝ) =
        (((8 : ℝ) * x) ^ r / (r.factorial : ℝ)) / (8 : ℝ) ^ r := by
    rw [mul_pow]
    field_simp [hfac, h8.ne']
  rw [heq]
  exact div_le_div_of_nonneg_right hraw h8.le

private theorem exp_nine_div_eight_le_exp_neg_one {α : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ 1 / 9) :
    Real.exp (9 * α) / 8 ≤ Real.exp (-1) := by
  have h9α : 9 * α ≤ 1 := by linarith
  have hexpα : Real.exp (9 * α) ≤ Real.exp 1 := Real.exp_le_exp.mpr h9α
  have he11 : Real.exp 1 < (11 : ℝ) / 4 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have heSq : Real.exp 1 * Real.exp 1 < 8 := by
    have hepos := Real.exp_pos 1
    nlinarith
  have hfrac : Real.exp 1 / 8 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) (Real.exp_pos 1)).2
      (by nlinarith [heSq])
  exact (div_le_div_of_nonneg_right hexpα (by norm_num)).trans hfrac

private theorem rankin_summand_le
    {K α : ℝ} (hK : 1 ≤ K) (hα0 : 0 ≤ α) (hα : α ≤ 1 / 9)
    (r : ℕ) :
    K * Real.exp (α * (r : ℝ)) *
        (Real.log K + α * (r : ℝ)) ^ r / (r.factorial : ℝ) ≤
      K ^ 9 * Real.exp (-(r : ℝ)) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  let x : ℝ := Real.log K + α * (r : ℝ)
  have hx : 0 ≤ x := add_nonneg hlog (mul_nonneg hα0 (Nat.cast_nonneg r))
  have hfac := pow_div_factorial_le_exp_eight x r hx
  have hscale : 0 ≤ K * Real.exp (α * (r : ℝ)) :=
    mul_nonneg hKpos.le (Real.exp_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hfac hscale
  have hexp8 :
      Real.exp (8 * x) = K ^ 8 * Real.exp (8 * α * (r : ℝ)) := by
    have harg : 8 * x = 8 * Real.log K + 8 * α * (r : ℝ) := by
      dsimp only [x]
      ring
    have hlog8 : Real.exp (8 * Real.log K) = K ^ 8 := by
      simpa only [Nat.cast_ofNat, Real.exp_log hKpos] using
        (Real.exp_nat_mul (Real.log K) 8)
    rw [harg, Real.exp_add, hlog8]
  have hcombine :
      Real.exp (α * (r : ℝ)) * Real.exp (8 * α * (r : ℝ)) =
        (Real.exp (9 * α)) ^ r := by
    rw [← Real.exp_add]
    have harg : α * (r : ℝ) + 8 * α * (r : ℝ) = (r : ℝ) * (9 * α) := by ring
    rw [harg, Real.exp_nat_mul]
  have hform :
      K * Real.exp (α * (r : ℝ)) *
          (Real.exp (8 * x) / (8 : ℝ) ^ r) =
        K ^ 9 * (Real.exp (9 * α) / 8) ^ r := by
    rw [hexp8, div_pow, ← hcombine]
    ring
  have hbase := exp_nine_div_eight_le_exp_neg_one hα0 hα
  have hbase0 : 0 ≤ Real.exp (9 * α) / 8 :=
    div_nonneg (Real.exp_nonneg _) (by norm_num)
  have hpow : (Real.exp (9 * α) / 8) ^ r ≤ (Real.exp (-1)) ^ r :=
    pow_le_pow_left₀ hbase0 hbase r
  have hnegpow : (Real.exp (-1)) ^ r = Real.exp (-(r : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    K * Real.exp (α * (r : ℝ)) *
          (Real.log K + α * (r : ℝ)) ^ r / (r.factorial : ℝ) =
        (K * Real.exp (α * (r : ℝ))) *
          (x ^ r / (r.factorial : ℝ)) := by
      dsimp only [x]
      ring
    _ ≤ (K * Real.exp (α * (r : ℝ))) *
          (Real.exp (8 * x) / (8 : ℝ) ^ r) := hmul
    _ = K ^ 9 * (Real.exp (9 * α) / 8) ^ r := hform
    _ ≤ K ^ 9 * (Real.exp (-1)) ^ r :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hKpos.le 9)
    _ = K ^ 9 * Real.exp (-(r : ℝ)) := by rw [hnegpow]

private theorem finite_exp_tail_le (s β : ℝ) (N : ℕ) (hβs : β ≤ s) :
    ∑ r ∈ (range N).filter (fun r : ℕ ↦ s - β < (r : ℝ)),
        Real.exp (-(r : ℝ)) ≤ 2 * Real.exp (β - s) := by
  let m : ℕ := ⌊s - β⌋₊ + 1
  let q : ℝ := Real.exp (-1)
  have hsβ : 0 ≤ s - β := sub_nonneg.mpr hβs
  have hsubset : (range N).filter (fun r : ℕ ↦ s - β < (r : ℝ)) ⊆ Ico m N := by
    intro r hr
    have hr' := mem_filter.mp hr
    have hfloor : ⌊s - β⌋₊ < r := (Nat.floor_lt hsβ).2 hr'.2
    exact mem_Ico.mpr
      ⟨by simpa only [m, Nat.add_one_le_iff] using hfloor, mem_range.mp hr'.1⟩
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hqhalf : q ≤ 1 / 2 := by
    dsimp only [q]
    rw [Real.exp_neg, inv_eq_one_div]
    exact (div_le_div_iff₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).2
      (by simpa only [one_mul] using Real.exp_one_gt_two.le)
  have hsubsetSum :
      ∑ r ∈ (range N).filter (fun r : ℕ ↦ s - β < (r : ℝ)), q ^ r ≤
        ∑ r ∈ Ico m N, q ^ r :=
    sum_le_sum_of_subset_of_nonneg hsubset
      (fun r _ _ ↦ pow_nonneg hq0 r)
  have hgeom : ∑ r ∈ Ico m N, q ^ r ≤ 2 * q ^ m := by
    by_cases hmN : m ≤ N
    · let S : ℝ := ∑ r ∈ Ico m N, q ^ r
      have hS0 : 0 ≤ S := sum_nonneg fun r _ ↦ pow_nonneg hq0 r
      have hfactor : 1 / 2 ≤ 1 - q := by linarith
      have hfactorMul : S * (1 / 2) ≤ S * (1 - q) :=
        mul_le_mul_of_nonneg_left hfactor hS0
      have hformula : S * (1 - q) = q ^ m - q ^ N := by
        dsimp only [S]
        exact geom_sum_Ico_mul_neg q hmN
      have hpowN : 0 ≤ q ^ N := pow_nonneg hq0 N
      nlinarith
    · have hempty : Ico m N = ∅ := Ico_eq_empty_iff.mpr (by omega)
      rw [hempty, sum_empty]
      positivity
  have hmgt : s - β < (m : ℝ) := by
    dsimp only [m]
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (s - β)
  have hqm : q ^ m = Real.exp (-(m : ℝ)) := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hqmbound : q ^ m ≤ Real.exp (β - s) := by
    rw [hqm]
    exact Real.exp_le_exp.mpr (by linarith)
  have hexpEq (r : ℕ) : Real.exp (-(r : ℝ)) = q ^ r := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [hexpEq]
  exact hsubsetSum.trans (hgeom.trans
    (mul_le_mul_of_nonneg_left hqmbound (by norm_num)))

/-- Finite Rankin tail at parameter eight. -/
theorem beta_rankin_tail_le
    {K α β s : ℝ} {N : ℕ} (hK : 1 ≤ K)
    (hα0 : 0 ≤ α) (hα : α ≤ 1 / 9) (hβs : β ≤ s) :
    ∑ r ∈ (range N).filter (fun r : ℕ ↦ s - β < (r : ℝ)),
        K * Real.exp (α * (r : ℝ)) *
          (Real.log K + α * (r : ℝ)) ^ r / (r.factorial : ℝ) ≤
      2 * K ^ 9 * Real.exp (β - s) := by
  have hpoint : ∀ r : ℕ,
      r ∈ (range N).filter (fun r : ℕ ↦ s - β < (r : ℝ)) →
        K * Real.exp (α * (r : ℝ)) *
            (Real.log K + α * (r : ℝ)) ^ r / (r.factorial : ℝ) ≤
          K ^ 9 * Real.exp (-(r : ℝ)) :=
    fun r _ ↦ rankin_summand_le hK hα0 hα r
  have hsum := sum_le_sum hpoint
  have htail := finite_exp_tail_le s β N hβs
  have hK9 : 0 ≤ K ^ 9 := pow_nonneg (zero_le_one.trans hK) _
  calc
    ∑ r ∈ (range N).filter (fun r : ℕ ↦ s - β < (r : ℝ)),
        K * Real.exp (α * (r : ℝ)) *
          (Real.log K + α * (r : ℝ)) ^ r / (r.factorial : ℝ) ≤
      ∑ r ∈ (range N).filter (fun r : ℕ ↦ s - β < (r : ℝ)),
        K ^ 9 * Real.exp (-(r : ℝ)) := hsum
    _ = K ^ 9 * ∑ r ∈ (range N).filter (fun r : ℕ ↦ s - β < (r : ℝ)),
        Real.exp (-(r : ℝ)) := by rw [mul_sum]
    _ ≤ K ^ 9 * (2 * Real.exp (β - s)) :=
      mul_le_mul_of_nonneg_left htail hK9
    _ = 2 * K ^ 9 * Real.exp (β - s) := by ring

end PrimeGapNormality.Prime.CoreBetaRankinTail
