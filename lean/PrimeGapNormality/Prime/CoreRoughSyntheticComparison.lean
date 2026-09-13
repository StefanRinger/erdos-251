import PrimeGapNormality.Prime.CoreRoughSyntheticScale
import PrimeGapNormality.Prime.CrtNestedCutoffL1Theta

/-! Finite comparison of the literal cutoff-z root law with each law in
the synthetic mixture. The first count moment remains displayed: its
rough-scale bound, and the subsequent limit, are separate suppliers. -/

namespace PrimeGapNormality.Prime.CoreRoughSyntheticComparison

open Finset CoreRoughSyntheticScale
noncomputable section

private theorem ratio_error {G H C δ : ℝ} (hG : 0 < G)
    (hGH : G ≤ H) (hHC : H ≤ G + C) (hC : 0 ≤ C) (hδ : 0 ≤ δ) :
    1 - (1 - δ) * G / H ≤ C / G + δ := by
  have hH : 0 < H := hG.trans_le hGH
  have hdiff : (H - G) / H ≤ C / H :=
    div_le_div_of_nonneg_right (by linarith) hH.le
  have hden : C / H ≤ C / G := div_le_div_of_nonneg_left hC hG hGH
  have hfrac : G / H ≤ 1 := (div_le_one hH).2 hGH
  have hmul : δ * (G / H) ≤ δ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac hδ
  have heq : 1 - (1 - δ) * G / H = (H - G) / H + δ * (G / H) := by
    field_simp [hH.ne'] <;> ring
  rw [heq]
  exact add_le_add (hdiff.trans hden) hmul

/-- The ordinary Euler-product loss is uniformly small throughout the
actual synthetic mixture; its old cutoff is z, not sieveCutoff(T). -/
theorem euler_ratio_error {z t : ℕ}
    (hG : 16 ≤ roughGapScale z) (ht : t ∈ mixScale (roughSyntheticScale z)) :
    1 - eulerProdNat (sieveCutoff (t : ℝ)) / eulerProdNat z ≤
      Real.log 4 / roughGapScale z + 1 / (sieveCutoff (t : ℝ) : ℝ) := by
  have hlogs := mixScale_log_bounds ht
  have hGpos := roughGapScale_pos z
  have hlogpos := hGpos.trans hlogs.1
  have ht1 : (1 : ℝ) < t :=
    (Real.log_pos_iff (Nat.cast_nonneg t)).mp hlogpos
  have ht16 : Real.exp 16 ≤ (t : ℝ) := by
    calc
      Real.exp 16 ≤ Real.exp (Real.log (t : ℝ)) :=
        Real.exp_le_exp.mpr (hG.trans hlogs.1.le)
      _ = (t : ℝ) := Real.exp_log (zero_lt_one.trans ht1)
  have hy := sieveCutoff_spec ht1
  have hjump := isSieveCutoff_jump ht16 hy
  rw [eulerProd_coe_nat] at hjump
  have hmul := mul_le_mul_of_nonneg_right hjump.le hGpos.le
  have hratio :
      (1 - 1 / (sieveCutoff (t : ℝ) : ℝ)) * roughGapScale z / Real.log (t : ℝ) ≤
        eulerProdNat (sieveCutoff (t : ℝ)) / eulerProdNat z := by
    simpa only [roughGapScale, one_div, div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm,
      mul_comm] using hmul
  have hbound := ratio_error hGpos hlogs.1.le hlogs.2
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    (by positivity : (0 : ℝ) ≤ 1 / (sieveCutoff (t : ℝ) : ℝ))
  exact (sub_le_sub_left hratio 1).trans hbound

/-- Uniform defect after also accounting for the rooted correction.
The correction is not silently identified with V(y)/V(z). -/
theorem rooted_retention_error {z t : ℕ} (hz : 2 ≤ z)
    (hG : 16 ≤ roughGapScale z) (ht : t ∈ mixScale (roughSyntheticScale z)) :
    1 - rootedEulerProdNat z (sieveCutoff (t : ℝ)) ≤
      Real.log 4 / roughGapScale z + 1 / (z : ℝ) + 1 / ((z : ℝ) - 1) := by
  have hzy := lt_sieveCutoff_of_mem_mixScale ht
  have hroot := crtNestTh_one_sub_le hz hzy.le
  have herr := euler_ratio_error hG ht
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hinv : 1 / (sieveCutoff (t : ℝ) : ℝ) ≤ 1 / (z : ℝ) :=
    one_div_le_one_div_of_le hzpos (Nat.cast_le.mpr hzy.le)
  exact hroot.trans (_root_.add_le_add
    (herr.trans (_root_.add_le_add le_rfl hinv)) le_rfl)

/-- The concrete L1 comparison for bounded configuration tests. This is
a finite theorem, not a claim that the displayed first moment is O(L). -/
theorem actualRootLaw_massL1_le {z t S : ℕ} (hz : 2 ≤ z) (hS : S ≤ z)
    (hG : 16 ≤ roughGapScale z) (ht : t ∈ mixScale (roughSyntheticScale z)) :
    (∑ U ∈ (offsetWindow S).powerset,
      |actualRootLaw z S U - actualRootLaw (sieveCutoff (t : ℝ)) S U|) ≤
      2 * (∑ U ∈ (offsetWindow S).powerset, (U.card : ℝ) * actualRootLaw z S U) *
        (Real.log 4 / roughGapScale z + 1 / (z : ℝ) + 1 / ((z : ℝ) - 1)) := by
  have hzy := lt_sieveCutoff_of_mem_mixScale ht
  have hbase := crtNestL1_massL1_le z (sieveCutoff (t : ℝ)) S hz hzy.le hS
  have hθ := rooted_retention_error hz hG ht
  have hM : 0 ≤ ∑ U ∈ (offsetWindow S).powerset,
      (U.card : ℝ) * actualRootLaw z S U :=
    sum_nonneg fun U _ => mul_nonneg (Nat.cast_nonneg _) (crtNestL1Th_actualRootLaw_nonneg z S U)
  exact hbase.trans (mul_le_mul_of_nonneg_left hθ (by positivity))

end
end PrimeGapNormality.Prime.CoreRoughSyntheticComparison
