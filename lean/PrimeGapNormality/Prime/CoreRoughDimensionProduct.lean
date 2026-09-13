import PrimeGapNormality.Prime.CoreBetaLogProduct
import PrimeGapNormality.Prime.CrtNestedCutoffTheta
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A proved dimensional product bound on the rough prime band

For a dimension `k`, primes up to `4k` are removed before applying the
finite logarithmic product comparison.  The square correction is then at
most `k`, while the baseline Euler quotient is bounded by the proved
two-sided estimates for `V`.  The explicit constant `31` is
`1 + 30`, where `eulerProdLowerConst = exp(-30)`.

This file assumes only the coordinatewise finite inequality `ν(p)≤k`; it
does not assume a sieve dimension-product estimate.
-/

namespace PrimeGapNormality.Prime.CoreRoughDimensionProduct

open Finset

noncomputable section

/-- Prime band after removing both the presieving range and the range where
`ν(p)/p` need not yet be at most one half. -/
def dimensionPrimeBand (w y k : ℕ) : Finset ℕ :=
  Nat.primesLE y \ Nat.primesLE (max w (4 * k))

/-- Baseline one-dimensional Euler product on the dimension band. -/
def dimensionBaselineProduct (w y k : ℕ) : ℝ :=
  ∏ p ∈ dimensionPrimeBand w y k, (1 - (p : ℝ)⁻¹)

/-- Product attached to arbitrary integer local residue ranks `ν(p)`. -/
def dimensionProduct (w y k : ℕ) (ν : ℕ → ℕ) : ℝ :=
  ∏ p ∈ dimensionPrimeBand w y k, (1 - (ν p : ℝ) / (p : ℝ))

private theorem mem_dimensionPrimeBand {w y k p : ℕ}
    (hp : p ∈ dimensionPrimeBand w y k) :
    Nat.Prime p ∧ max w (4 * k) < p ∧ p ≤ y := by
  have hmem := mem_sdiff.mp hp
  have hpy := Nat.mem_primesLE.mp hmem.1
  have hlt : max w (4 * k) < p := by
    by_contra hnot
    have hpm : p ≤ max w (4 * k) := Nat.not_lt.mp hnot
    exact hmem.2 (Nat.mem_primesLE.mpr ⟨hpm, hpy.2⟩)
  exact ⟨hpy.2, hlt, hpy.1⟩

private theorem dimensionPrimeBand_inv_sq_le_pred
    {w y k : ℕ} (hk : 1 ≤ k) :
    ∑ p ∈ dimensionPrimeBand w y k, ((p : ℝ)⁻¹) ^ 2 ≤
      1 / (((4 * k : ℕ) : ℝ) - 1) := by
  let m := max w (4 * k)
  have hm4 : 4 * k ≤ m := le_max_right _ _
  have hm2 : 2 ≤ m := by
    have h24 : 2 ≤ 4 * k := by nlinarith
    exact h24.trans hm4
  have hterm : ∀ p ∈ dimensionPrimeBand w y k,
      ((p : ℝ)⁻¹) ^ 2 ≤ ((p : ℝ) - 1)⁻¹ ^ 2 := by
    intro p hp
    have hpdata := mem_dimensionPrimeBand hp
    have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hpdata.1.one_lt
    have hpred : 0 < (p : ℝ) - 1 := sub_pos.mpr hp1
    have hinv : (p : ℝ)⁻¹ ≤ ((p : ℝ) - 1)⁻¹ :=
      inv_anti₀ hpred (by linarith)
    exact pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg p)) hinv 2
  have hsum := sum_le_sum hterm
  have htail := crtNestTh_sum_inv_sq_le (y1 := m) (y2 := y) hm2
  have hcast : (((4 * k : ℕ) : ℝ) - 1) ≤ (m : ℝ) - 1 := by
    exact sub_le_sub_right (Nat.cast_le.mpr hm4) 1
  have hden : 0 < (((4 * k : ℕ) : ℝ) - 1) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hkR : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
    linarith
  have hinvden : 1 / ((m : ℝ) - 1) ≤
      1 / (((4 * k : ℕ) : ℝ) - 1) :=
    one_div_le_one_div_of_le hden hcast
  calc
    ∑ p ∈ dimensionPrimeBand w y k, ((p : ℝ)⁻¹) ^ 2 ≤
        ∑ p ∈ dimensionPrimeBand w y k, ((p : ℝ) - 1)⁻¹ ^ 2 := hsum
    _ ≤ 1 / ((m : ℝ) - 1) := by
      simpa only [dimensionPrimeBand, m] using htail
    _ ≤ 1 / (((4 * k : ℕ) : ℝ) - 1) := hinvden

private theorem dimension_square_error_le {w y k : ℕ} (hk : 1 ≤ k) :
    2 * (k : ℝ) ^ 2 *
        (∑ p ∈ dimensionPrimeBand w y k, ((p : ℝ)⁻¹) ^ 2) ≤
      (k : ℝ) := by
  have hsum := dimensionPrimeBand_inv_sq_le_pred (w := w) (y := y) hk
  have hcoef : 0 ≤ 2 * (k : ℝ) ^ 2 := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hsum hcoef
  have hkR : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
  have hden : 0 < (4 : ℝ) * k - 1 := by linarith
  calc
    2 * (k : ℝ) ^ 2 *
        (∑ p ∈ dimensionPrimeBand w y k, ((p : ℝ)⁻¹) ^ 2) ≤
      2 * (k : ℝ) ^ 2 * (1 / (((4 * k : ℕ) : ℝ) - 1)) := hfirst
    _ = (2 * (k : ℝ) ^ 2) / ((4 : ℝ) * k - 1) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      rw [one_div]
      ring
    _ ≤ (k : ℝ) := by
      rw [div_le_iff₀ hden]
      nlinarith

private theorem euler_quotient_inverse_le
    {w m y : ℕ} (hw : 2 ≤ w) (hwm : w ≤ m) (hmy : m ≤ y)
    (hy : 16 ≤ y) :
    (eulerProdNat y / eulerProdNat m)⁻¹ ≤
      Real.exp 30 * (Real.log (y : ℝ) / Real.log (w : ℝ)) := by
  have hwR : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hmR : (2 : ℝ) ≤ m := hwR.trans (Nat.cast_le.mpr hwm)
  have hyR : (16 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogw : 0 < Real.log (w : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hwR)
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hmR)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) hyR)
  have hVm : eulerProdNat m ≤ 1 / Real.log (m : ℝ) := by
    simpa only [eulerProd_coe_nat] using eulerProd_le_inv_log hmR
  have hVy : eulerProdLowerConst / Real.log (y : ℝ) ≤ eulerProdNat y := by
    simpa only [eulerProd_coe_nat] using eulerProd_ge_mul_inv_log hyR
  have hlowpos : 0 < eulerProdLowerConst / Real.log (y : ℝ) :=
    div_pos eulerProdLowerConst_pos hlogy
  have hinvVy : (eulerProdNat y)⁻¹ ≤
      (eulerProdLowerConst / Real.log (y : ℝ))⁻¹ :=
    inv_anti₀ hlowpos hVy
  have hmul :
      eulerProdNat m * (eulerProdNat y)⁻¹ ≤
        (1 / Real.log (m : ℝ)) *
          (eulerProdLowerConst / Real.log (y : ℝ))⁻¹ :=
    mul_le_mul hVm hinvVy
      (inv_nonneg.mpr (eulerProdNat_pos y).le)
      (div_nonneg zero_le_one hlogm.le)
  have heq :
      (1 / Real.log (m : ℝ)) *
          (eulerProdLowerConst / Real.log (y : ℝ))⁻¹ =
        eulerProdLowerConst⁻¹ *
          (Real.log (y : ℝ) / Real.log (m : ℝ)) := by
    field_simp [hlogm.ne', hlogy.ne', eulerProdLowerConst_pos.ne']
  have hlogwm : Real.log (w : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log
      (Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 2) hw))
      (Nat.cast_le.mpr hwm)
  have hratio : Real.log (y : ℝ) / Real.log (m : ℝ) ≤
      Real.log (y : ℝ) / Real.log (w : ℝ) :=
    div_le_div_of_nonneg_left hlogy.le hlogw hlogwm
  have hcInv : eulerProdLowerConst⁻¹ = Real.exp 30 := by
    rw [eulerProdLowerConst, Real.exp_neg]
    simp only [inv_inv]
  calc
    (eulerProdNat y / eulerProdNat m)⁻¹ =
        eulerProdNat m * (eulerProdNat y)⁻¹ := by
      field_simp [eulerProdNat_ne_zero]
    _ ≤ (1 / Real.log (m : ℝ)) *
          (eulerProdLowerConst / Real.log (y : ℝ))⁻¹ := hmul
    _ = eulerProdLowerConst⁻¹ *
          (Real.log (y : ℝ) / Real.log (m : ℝ)) := heq
    _ ≤ eulerProdLowerConst⁻¹ *
          (Real.log (y : ℝ) / Real.log (w : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (inv_pos.mpr eulerProdLowerConst_pos).le
    _ = Real.exp 30 * (Real.log (y : ℝ) / Real.log (w : ℝ)) := by rw [hcInv]

private theorem dimensionBaselineProduct_pos {w y k : ℕ} :
    0 < dimensionBaselineProduct w y k := by
  unfold dimensionBaselineProduct
  apply prod_pos
  intro p hp
  have hpPrime := (mem_dimensionPrimeBand hp).1
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hpPrime.one_lt
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)

/-- Uniform finite dimensional product condition on every integer band
`2≤w≤y`, `y≥16`.  The local ranks are only assumed coordinatewise bounded
by `k`; the product estimate itself is proved. -/
theorem dimensionProduct_inv_le
    {w y k : ℕ} (ν : ℕ → ℕ) (hw : 2 ≤ w) (hwy : w ≤ y)
    (hy : 16 ≤ y) (hk : 1 ≤ k)
    (hν : ∀ p ∈ dimensionPrimeBand w y k, ν p ≤ k) :
    (dimensionProduct w y k ν)⁻¹ ≤
      Real.exp (31 * (k : ℝ)) *
        (Real.log (y : ℝ) / Real.log (w : ℝ)) ^ k := by
  let m := max w (4 * k)
  let P := dimensionPrimeBand w y k
  let R := Real.log (y : ℝ) / Real.log (w : ℝ)
  have hwpos : 0 < (w : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 2) hw)
  have hlogw : 0 < Real.log (w : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num) hw))
  have hlogwy : Real.log (w : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log hwpos (Nat.cast_le.mpr hwy)
  have hR : 1 ≤ R := by
    dsimp only [R]
    rw [le_div_iff₀ hlogw, one_mul]
    exact hlogwy
  by_cases hmy : m ≤ y
  · have hbaseEq : dimensionBaselineProduct w y k =
        eulerProdNat y / eulerProdNat m := by
      dsimp only [dimensionBaselineProduct, dimensionPrimeBand, m]
      exact (eulerProdNat_div hmy).symm
    have hbaseInv : (dimensionBaselineProduct w y k)⁻¹ ≤
        Real.exp 30 * R := by
      rw [hbaseEq]
      exact euler_quotient_inverse_le hw (le_max_left _ _) hmy hy
    have hband : ∀ p ∈ P, max w (4 * k) < p :=
      fun p hp ↦ (mem_dimensionPrimeBand (by simpa only [P] using hp)).2.1
    have ha0 : ∀ p ∈ P, 0 ≤ (p : ℝ)⁻¹ :=
      fun p _ ↦ inv_nonneg.mpr (Nat.cast_nonneg p)
    have ha1 : ∀ p ∈ P, (p : ℝ)⁻¹ < 1 := fun p hp ↦ by
      have hpPrime :=
        (mem_dimensionPrimeBand (by simpa only [P] using hp)).1
      exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr hpPrime.one_lt)
    have hg0 : ∀ p ∈ P, 0 ≤ (ν p : ℝ) / (p : ℝ) := fun p _ ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hghalf : ∀ p ∈ P, (ν p : ℝ) / (p : ℝ) ≤ 1 / 2 := by
      intro p hp
      have hpgt := hband p hp
      have hpgt4 : 4 * k < p := (le_max_right w (4 * k)).trans_lt hpgt
      have hpgtR : (4 : ℝ) * k < p := by exact_mod_cast hpgt4
      have hpPrime :=
        (mem_dimensionPrimeBand (by simpa only [P] using hp)).1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hνR : (ν p : ℝ) ≤ k := by
        exact_mod_cast hν p (by simpa only [P] using hp)
      rw [div_le_iff₀ hp0]
      nlinarith
    have hga : ∀ p ∈ P, (ν p : ℝ) / (p : ℝ) ≤
        (k : ℝ) * (p : ℝ)⁻¹ := by
      intro p hp
      have hνR : (ν p : ℝ) ≤ k := by
        exact_mod_cast hν p (by simpa only [P] using hp)
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hνR
        (inv_nonneg.mpr (Nat.cast_nonneg p))
    have hcore := CoreBetaLogProduct.inverse_product_le P
      (fun p ↦ (p : ℝ)⁻¹) (fun p ↦ (ν p : ℝ) / (p : ℝ))
      (κ := (k : ℝ)) (Nat.cast_nonneg k) ha0 ha1 hg0 hghalf hga
    have herr := dimension_square_error_le (w := w) (y := y) hk
    have hexpErr : Real.exp
          (2 * (k : ℝ) ^ 2 *
            ∑ p ∈ dimensionPrimeBand w y k, ((p : ℝ)⁻¹) ^ 2) ≤
        Real.exp (k : ℝ) := Real.exp_le_exp.mpr herr
    have hbasepos := dimensionBaselineProduct_pos (w := w) (y := y) (k := k)
    have hexpBase : Real.exp
          ((k : ℝ) * (-Real.log (dimensionBaselineProduct w y k))) =
        (dimensionBaselineProduct w y k)⁻¹ ^ k := by
      rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hbasepos]
    have hpowBase : (dimensionBaselineProduct w y k)⁻¹ ^ k ≤
        (Real.exp 30 * R) ^ k :=
      pow_le_pow_left₀ (inv_nonneg.mpr hbasepos.le) hbaseInv k
    have hfirst : Real.exp
          ((k : ℝ) * (-Real.log (dimensionBaselineProduct w y k))) ≤
        (Real.exp 30 * R) ^ k := by rw [hexpBase]; exact hpowBase
    have hcombined := mul_le_mul hfirst hexpErr
      (Real.exp_nonneg _)
      (pow_nonneg (mul_nonneg (Real.exp_nonneg _) (zero_le_one.trans hR)) k)
    have hcore' : (dimensionProduct w y k ν)⁻¹ ≤
        Real.exp ((k : ℝ) *
            (-Real.log (dimensionBaselineProduct w y k))) *
          Real.exp (2 * (k : ℝ) ^ 2 *
            ∑ p ∈ dimensionPrimeBand w y k, ((p : ℝ)⁻¹) ^ 2) := by
      simpa only [dimensionProduct, dimensionBaselineProduct, P] using hcore
    have hexpCombine : (Real.exp 30) ^ k * Real.exp (k : ℝ) =
        Real.exp (31 * (k : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    calc
      (dimensionProduct w y k ν)⁻¹ ≤
          Real.exp ((k : ℝ) *
              (-Real.log (dimensionBaselineProduct w y k))) *
            Real.exp (2 * (k : ℝ) ^ 2 *
              ∑ p ∈ dimensionPrimeBand w y k, ((p : ℝ)⁻¹) ^ 2) := hcore'
      _ ≤ (Real.exp 30 * R) ^ k * Real.exp (k : ℝ) := hcombined
      _ = ((Real.exp 30) ^ k * Real.exp (k : ℝ)) * R ^ k := by
        rw [mul_pow]
        ring
      _ = Real.exp (31 * (k : ℝ)) * R ^ k := by rw [hexpCombine]
      _ = Real.exp (31 * (k : ℝ)) *
          (Real.log (y : ℝ) / Real.log (w : ℝ)) ^ k := by rfl
  · have hym : y ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmy)
    have hPempty : P = ∅ := by
      dsimp only [P, dimensionPrimeBand, m]
      exact sdiff_eq_empty_iff_subset.mpr (Nat.primesLE_mono hym)
    have hBandEmpty : dimensionPrimeBand w y k = ∅ := by
      simpa only [P] using hPempty
    have hexpOne : (1 : ℝ) ≤ Real.exp (31 * (k : ℝ)) :=
      Real.one_le_exp (mul_nonneg (by norm_num) (Nat.cast_nonneg k))
    have hpowOne : (1 : ℝ) ≤ R ^ k := one_le_pow₀ hR
    have hmul : (1 : ℝ) * 1 ≤ Real.exp (31 * (k : ℝ)) * R ^ k :=
      mul_le_mul hexpOne hpowOne zero_le_one (Real.exp_nonneg _)
    rw [dimensionProduct, hBandEmpty, prod_empty, inv_one]
    simpa only [one_mul, R] using hmul

end

end PrimeGapNormality.Prime.CoreRoughDimensionProduct
