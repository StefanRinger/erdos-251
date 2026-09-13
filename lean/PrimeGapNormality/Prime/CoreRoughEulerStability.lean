import PrimeGapNormality.Prime.FiniteRootMixInclusionProduct
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Stable finite tuple Euler products under a cutoff extension

This file never divides by a tuple Euler product.  Thus an old covering
prime, and the resulting zero product, are handled by the same inequalities
as the nonzero case.  The only analytic input is a bound for the sum of the
new local hazards.
-/

namespace PrimeGapNormality.Prime.CoreRoughEulerStability

open Finset
open scoped BigOperators Classical

noncomputable section

private theorem residueCount_le_modulus (E : Finset ℕ) {p : ℕ}
    (hp : Nat.Prime p) :
    residueCount E p ≤ p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  unfold residueCount
  simpa only [ZMod.card] using
    card_le_univ (E.image fun h : ℕ ↦ (h : ZMod p))

private theorem residueCount_le_card (E : Finset ℕ) (p : ℕ) :
    residueCount E p ≤ E.card := by
  unfold residueCount
  exact card_image_le

private theorem localHazard_nonneg (E : Finset ℕ) (p : ℕ) :
    0 ≤ (residueCount E p : ℝ) / (p : ℝ) :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem localHazard_le_one
    (E : Finset ℕ) {p : ℕ} (hp : Nat.Prime p) :
    (residueCount E p : ℝ) / (p : ℝ) ≤ 1 := by
  exact (div_le_one (Nat.cast_pos.mpr hp.pos)).mpr
    (Nat.cast_le.mpr (residueCount_le_modulus E hp))

private theorem one_sub_sum_le_product
    {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i ≤ 1) :
    1 - ∑ i ∈ s, g i ≤ ∏ i ∈ s, (1 - g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      have hx0 : 0 ≤ g x := hg0 x (mem_insert_self x s)
      have hx1 : g x ≤ 1 := hg1 x (mem_insert_self x s)
      have hs0 : 0 ≤ ∑ i ∈ s, g i :=
        sum_nonneg fun i hi ↦ hg0 i (mem_insert_of_mem hi)
      have hfactor : 0 ≤ 1 - g x := sub_nonneg.mpr hx1
      have hrest := ih
        (fun i hi ↦ hg0 i (mem_insert_of_mem hi))
        (fun i hi ↦ hg1 i (mem_insert_of_mem hi))
      have hmul := mul_le_mul_of_nonneg_left hrest hfactor
      simp only [sum_insert hx, prod_insert hx]
      calc
        1 - (g x + ∑ i ∈ s, g i) ≤
            (1 - g x) * (1 - ∑ i ∈ s, g i) := by
          nlinarith [mul_nonneg hx0 hs0]
        _ ≤ (1 - g x) * ∏ i ∈ s, (1 - g i) := hmul

/-- Exact splitting at nested integer cutoffs. -/
theorem finiteTupleSieveProduct_split
    (E : Finset ℕ) {u v : ℕ} (huv : u ≤ v) :
    finiteTupleSieveProduct E v = finiteTupleSieveProduct E u *
      ∏ p ∈ Nat.primesLE v \ Nat.primesLE u,
        (1 - (residueCount E p : ℝ) / (p : ℝ)) := by
  have hsub : Nat.primesLE u ⊆ Nat.primesLE v := Nat.primesLE_mono huv
  unfold finiteTupleSieveProduct
  calc
    (∏ p ∈ Nat.primesLE v,
        (1 - (residueCount E p : ℝ) / (p : ℝ))) =
      (∏ p ∈ Nat.primesLE v \ Nat.primesLE u,
        (1 - (residueCount E p : ℝ) / (p : ℝ))) *
        ∏ p ∈ Nat.primesLE u,
          (1 - (residueCount E p : ℝ) / (p : ℝ)) :=
      (prod_sdiff hsub).symm
    _ = _ := mul_comm _ _

private theorem finiteTupleSieveProduct_nonneg (E : Finset ℕ) (u : ℕ) :
    0 ≤ finiteTupleSieveProduct E u := by
  unfold finiteTupleSieveProduct
  exact prod_nonneg fun p hp ↦ sub_nonneg.mpr
    (localHazard_le_one E (Nat.prime_of_mem_primesLE hp))

private theorem bandProduct_bounds
    (E : Finset ℕ) {u v : ℕ} {δ : ℝ}
    (hδ : ∑ p ∈ Nat.primesLE v \ Nat.primesLE u,
      (residueCount E p : ℝ) / (p : ℝ) ≤ δ) :
    1 - δ ≤
        ∏ p ∈ Nat.primesLE v \ Nat.primesLE u,
          (1 - (residueCount E p : ℝ) / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE v \ Nat.primesLE u,
          (1 - (residueCount E p : ℝ) / (p : ℝ)) ≤ 1 := by
  let P := Nat.primesLE v \ Nat.primesLE u
  let g : ℕ → ℝ := fun p ↦ (residueCount E p : ℝ) / (p : ℝ)
  have hg0 : ∀ p ∈ P, 0 ≤ g p := fun p hp ↦ localHazard_nonneg E p
  have hg1 : ∀ p ∈ P, g p ≤ 1 := by
    intro p hp
    exact localHazard_le_one E
      (Nat.prime_of_mem_primesLE (sdiff_subset hp))
  have hlower := one_sub_sum_le_product P g hg0 hg1
  have hupper : ∏ p ∈ P, (1 - g p) ≤ 1 :=
    prod_le_one (fun p hp ↦ sub_nonneg.mpr (hg1 p hp))
      (fun p hp ↦ by linarith [hg0 p hp])
  exact ⟨(sub_le_sub_left hδ 1).trans hlower, hupper⟩

/-- Multiplicative stability without a nonvanishing assumption. -/
theorem finiteTupleSieveProduct_bounds
    (E : Finset ℕ) {u v : ℕ} (huv : u ≤ v) {δ : ℝ}
    (hδ : ∑ p ∈ Nat.primesLE v \ Nat.primesLE u,
      (residueCount E p : ℝ) / (p : ℝ) ≤ δ) :
    (1 - δ) * finiteTupleSieveProduct E u ≤ finiteTupleSieveProduct E v ∧
      finiteTupleSieveProduct E v ≤ finiteTupleSieveProduct E u := by
  have hsplit := finiteTupleSieveProduct_split E huv
  have hQ := bandProduct_bounds E hδ
  have hVu : 0 ≤ finiteTupleSieveProduct E u :=
    finiteTupleSieveProduct_nonneg E u
  constructor
  · rw [hsplit]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hQ.1 hVu
  · rw [hsplit]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ.2 hVu

/-- Relative reverse estimate.  The factor `2` uses only `δ ≤ 1/2`, not a
logarithm or division by either Euler product. -/
theorem finiteTupleSieveProduct_abs_sub_le
    (E : Finset ℕ) {u v : ℕ} (huv : u ≤ v) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hδ : ∑ p ∈ Nat.primesLE v \ Nat.primesLE u,
      (residueCount E p : ℝ) / (p : ℝ) ≤ δ) :
    |finiteTupleSieveProduct E u - finiteTupleSieveProduct E v| ≤
      2 * δ * finiteTupleSieveProduct E v := by
  have hb := finiteTupleSieveProduct_bounds E huv hδ
  have hVu : 0 ≤ finiteTupleSieveProduct E u :=
    finiteTupleSieveProduct_nonneg E u
  have hdiff0 : 0 ≤ finiteTupleSieveProduct E u - finiteTupleSieveProduct E v :=
    sub_nonneg.mpr hb.2
  have hdiff : finiteTupleSieveProduct E u - finiteTupleSieveProduct E v ≤
      δ * finiteTupleSieveProduct E u := by
    linarith [hb.1]
  have hhalfFactor : (1 / 2 : ℝ) ≤ 1 - δ := by linarith
  have hhalfProd : (1 / 2 : ℝ) * finiteTupleSieveProduct E u ≤
      finiteTupleSieveProduct E v :=
    (mul_le_mul_of_nonneg_right hhalfFactor hVu).trans hb.1
  have hVu2 : finiteTupleSieveProduct E u ≤
      2 * finiteTupleSieveProduct E v := by linarith
  have hmul := mul_le_mul_of_nonneg_left hVu2 hδ0
  rw [abs_of_nonneg hdiff0]
  exact hdiff.trans (hmul.trans_eq (by ring))

/-- The new hazard sum is bounded by `|E|` times the prime harmonic mass of
the new band. -/
theorem bandHazard_le_card_mul
    (E : Finset ℕ) {u v : ℕ} {h : ℝ}
    (hh : ∑ p ∈ Nat.primesLE v \ Nat.primesLE u, (p : ℝ)⁻¹ ≤ h) :
    (∑ p ∈ Nat.primesLE v \ Nat.primesLE u,
      (residueCount E p : ℝ) / (p : ℝ)) ≤ (E.card : ℝ) * h := by
  calc
    (∑ p ∈ Nat.primesLE v \ Nat.primesLE u,
      (residueCount E p : ℝ) / (p : ℝ)) ≤
        ∑ p ∈ Nat.primesLE v \ Nat.primesLE u,
          (E.card : ℝ) * (p : ℝ)⁻¹ := by
      apply sum_le_sum
      intro p hp
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (residueCount_le_card E p)) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (E.card : ℝ) *
        ∑ p ∈ Nat.primesLE v \ Nat.primesLE u, (p : ℝ)⁻¹ := by
      rw [mul_sum]
    _ ≤ (E.card : ℝ) * h :=
      mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)

/-- Cardinal/harmonic specialization of the relative stability bound. -/
theorem finiteTupleSieveProduct_abs_sub_le_card_harmonic
    (E : Finset ℕ) {u v : ℕ} (huv : u ≤ v) {h : ℝ}
    (h0 : 0 ≤ h) (hhalf : (E.card : ℝ) * h ≤ 1 / 2)
    (hh : ∑ p ∈ Nat.primesLE v \ Nat.primesLE u, (p : ℝ)⁻¹ ≤ h) :
    |finiteTupleSieveProduct E u - finiteTupleSieveProduct E v| ≤
      2 * ((E.card : ℝ) * h) * finiteTupleSieveProduct E v := by
  apply finiteTupleSieveProduct_abs_sub_le E huv
    (mul_nonneg (Nat.cast_nonneg _) h0) hhalf
  exact bandHazard_le_card_mul E hh

end
end PrimeGapNormality.Prime.CoreRoughEulerStability
