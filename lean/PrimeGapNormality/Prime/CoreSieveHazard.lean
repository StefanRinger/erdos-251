import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite survival products and hazard bounds

Pure finite real inequalities, with no arithmetic or asymptotic input.
-/

namespace PrimeGapNormality.Prime.CoreSieveHazard

open Finset

/-- Finite survival product `∏ i ∈ s, (1-aᵢ)`. -/
def survivalProduct {ι : Type*} (s : Finset ι) (a : ι → ℝ) : ℝ :=
  ∏ i ∈ s, (1 - a i)

theorem survivalProduct_pos {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i < 1) :
    0 < survivalProduct s a := by
  unfold survivalProduct
  exact prod_pos fun i hi ↦ sub_pos.mpr (ha1 i hi)

theorem survivalProduct_le_one {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i < 1) :
    survivalProduct s a ≤ 1 := by
  unfold survivalProduct
  exact prod_le_one (fun i hi ↦ sub_nonneg.mpr (ha1 i hi).le)
    (fun i hi ↦ by
      have h := ha0 i hi
      linarith)

private theorem one_add_sum_mul_survival_le_one
    {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i < 1) :
    (1 + ∑ i ∈ s, a i) * survivalProduct s a ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [survivalProduct]
  | @insert x s hx ih =>
      have hax0 : 0 ≤ a x := ha0 x (mem_insert_self x s)
      have hax1 : a x < 1 := ha1 x (mem_insert_self x s)
      have hs0 : 0 ≤ ∑ i ∈ s, a i :=
        sum_nonneg fun i hi ↦ ha0 i (mem_insert_of_mem hi)
      have hP0 : 0 ≤ survivalProduct s a :=
        (survivalProduct_pos
          (fun i hi ↦ ha0 i (mem_insert_of_mem hi))
          (fun i hi ↦ ha1 i (mem_insert_of_mem hi))).le
      have hfactor :
          (1 + (a x + ∑ i ∈ s, a i)) * (1 - a x) ≤
            1 + ∑ i ∈ s, a i := by
        nlinarith [mul_nonneg hax0 hs0, sq_nonneg (a x)]
      have hmul := mul_le_mul_of_nonneg_right hfactor hP0
      have hrest := ih
        (fun i hi ↦ ha0 i (mem_insert_of_mem hi))
        (fun i hi ↦ ha1 i (mem_insert_of_mem hi))
      simp only [sum_insert hx, survivalProduct, prod_insert hx] at hmul ⊢
      simpa only [mul_assoc] using hmul.trans hrest

/-- The total hazard is at most `θ⁻¹-1`, where `θ` is the finite survival
product. -/
theorem sum_le_survivalProduct_inv_sub_one
    {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i < 1) :
    (∑ i ∈ s, a i) ≤ (survivalProduct s a)⁻¹ - 1 := by
  have hθ := survivalProduct_pos ha0 ha1
  have hcore := one_add_sum_mul_survival_le_one s a ha0 ha1
  have hdiv : 1 + ∑ i ∈ s, a i ≤ 1 / survivalProduct s a :=
    (le_div_iff₀ hθ).2 hcore
  rw [inv_eq_one_div]
  linarith

/-- If survival is at least one half, the total hazard is controlled by
twice the missing survival mass. -/
theorem sum_le_two_mul_one_sub_survivalProduct
    {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i < 1)
    (hhalf : (1 : ℝ) / 2 ≤ survivalProduct s a) :
    (∑ i ∈ s, a i) ≤ 2 * (1 - survivalProduct s a) := by
  let θ := survivalProduct s a
  have hθ : 0 < θ := survivalProduct_pos ha0 ha1
  have hθ1 : θ ≤ 1 := survivalProduct_le_one ha0 ha1
  have hbase := sum_le_survivalProduct_inv_sub_one ha0 ha1
  have heq : θ⁻¹ - 1 = (1 - θ) / θ := by
    field_simp [hθ.ne']
  have hratio : (1 - θ) / θ ≤ 2 * (1 - θ) := by
    apply (div_le_iff₀ hθ).2
    have hnonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    have hfactor : 0 ≤ 2 * θ - 1 := by
      dsimp only [θ] at hhalf ⊢
      linarith
    nlinarith [mul_nonneg hfactor hnonneg]
  dsimp only [θ] at heq hratio
  rw [heq] at hbase
  exact hbase.trans hratio

private theorem one_sub_sum_le_product
    {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (hb0 : ∀ i ∈ s, 0 ≤ b i) (hb1 : ∀ i ∈ s, b i ≤ 1) :
    1 - ∑ i ∈ s, b i ≤ ∏ i ∈ s, (1 - b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      have hbx0 : 0 ≤ b x := hb0 x (mem_insert_self x s)
      have hbx1 : b x ≤ 1 := hb1 x (mem_insert_self x s)
      have hs0 : 0 ≤ ∑ i ∈ s, b i :=
        sum_nonneg fun i hi ↦ hb0 i (mem_insert_of_mem hi)
      have hfactor0 : 0 ≤ 1 - b x := sub_nonneg.mpr hbx1
      have hrest := ih
        (fun i hi ↦ hb0 i (mem_insert_of_mem hi))
        (fun i hi ↦ hb1 i (mem_insert_of_mem hi))
      have hmul := mul_le_mul_of_nonneg_left hrest hfactor0
      simp only [sum_insert hx, prod_insert hx]
      calc
        1 - (b x + ∑ i ∈ s, b i) ≤
            (1 - b x) * (1 - ∑ i ∈ s, b i) := by
          nlinarith [mul_nonneg hbx0 hs0]
        _ ≤ (1 - b x) * ∏ i ∈ s, (1 - b i) := hmul

/-- First Bonferroni inequality after the scalar dilation `bᵢ=j aᵢ`. -/
theorem product_one_sub_mul_ge
    {ι : Type*} {s : Finset ι} {a : ι → ℝ} {j : ℝ}
    (hj : 0 ≤ j)
    (hja0 : ∀ i ∈ s, 0 ≤ j * a i)
    (hja1 : ∀ i ∈ s, j * a i ≤ 1) :
    1 - j * (∑ i ∈ s, a i) ≤ ∏ i ∈ s, (1 - j * a i) := by
  have h := one_sub_sum_le_product s (fun i ↦ j * a i) hja0 hja1
  rw [← mul_sum] at h
  exact h

end PrimeGapNormality.Prime.CoreSieveHazard
