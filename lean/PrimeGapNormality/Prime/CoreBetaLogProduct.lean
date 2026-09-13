import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Finite logarithmic comparison for the dimensional sieve product.
This is uniform in the dimension and charges the square-error only once,
rather than once for every boundary depth. No prime-sieve bound is assumed. -/

namespace PrimeGapNormality.Prime.CoreBetaLogProduct

open Finset
noncomputable section

theorem neg_log_one_sub_ge {x : ℝ} (hx : x < 1) :
    x ≤ -Real.log (1 - x) := by
  have hh := Real.log_le_sub_one_of_pos (sub_pos.mpr hx)
  linarith

theorem neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ x + 2 * x ^ 2 := by
  have hpos : 0 < 1 - x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hstep : -Real.log (1 - x) - x ≤ ((1 - x)⁻¹ - 1) - x := by linarith
  have hid : ((1 - x)⁻¹ - 1) - x = x ^ 2 / (1 - x) := by
    field_simp [hpos.ne'] <;> ring
  have hfrac : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg x]
  rw [hid] at hstep
  linarith

/-- Coordinatewise domination g_i≤κ a_i yields one aggregate logarithmic
Euler correction. The baseline a_i may be any numbers in [0,1). -/
theorem log_inverse_product_le {ι : Type*} (s : Finset ι) (a g : ι → ℝ)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i < 1)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hghalf : ∀ i ∈ s, g i ≤ 1 / 2)
    (hga : ∀ i ∈ s, g i ≤ κ * a i) :
    -Real.log (∏ i ∈ s, (1 - g i)) ≤
      κ * (-Real.log (∏ i ∈ s, (1 - a i))) +
        2 * κ ^ 2 * ∑ i ∈ s, (a i) ^ 2 := by
  have hgpos : ∀ i ∈ s, 0 < 1 - g i := fun i hi => by have := hghalf i hi; linarith
  have hapos : ∀ i ∈ s, 0 < 1 - a i := fun i hi => sub_pos.mpr (ha1 i hi)
  rw [Real.log_prod (fun i hi => (hgpos i hi).ne'),
    Real.log_prod (fun i hi => (hapos i hi).ne')]
  rw [← sum_neg_distrib, ← sum_neg_distrib, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro i hi
  have hx := neg_log_one_sub_le (hg0 i hi) (hghalf i hi)
  have hb := mul_le_mul_of_nonneg_left (neg_log_one_sub_ge (ha1 i hi)) hκ
  have hs : (g i) ^ 2 ≤ κ ^ 2 * (a i) ^ 2 := by
    have hh := pow_le_pow_left₀ (hg0 i hi) (hga i hi) 2
    simpa only [mul_pow] using hh
  have hbase := (hga i hi).trans hb
  nlinarith

/-- Exponentiated form of the same single aggregate error. -/
theorem inverse_product_le {ι : Type*} (s : Finset ι) (a g : ι → ℝ)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i < 1)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hghalf : ∀ i ∈ s, g i ≤ 1 / 2)
    (hga : ∀ i ∈ s, g i ≤ κ * a i) :
    (∏ i ∈ s, (1 - g i))⁻¹ ≤
      Real.exp (κ * (-Real.log (∏ i ∈ s, (1 - a i)))) *
        Real.exp (2 * κ ^ 2 * ∑ i ∈ s, (a i) ^ 2) := by
  have hpos : 0 < ∏ i ∈ s, (1 - g i) :=
    prod_pos fun i hi => by have := hghalf i hi; linarith
  have hh := Real.exp_le_exp.mpr (log_inverse_product_le s a g hκ ha0 ha1 hg0 hghalf hga)
  simpa only [Real.exp_neg, Real.exp_log hpos, Real.exp_add] using hh

end
end PrimeGapNormality.Prime.CoreBetaLogProduct
