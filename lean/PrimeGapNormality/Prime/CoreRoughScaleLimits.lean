import PrimeGapNormality.Prime.CoreRoughSyntheticScale
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Limits of the synthetic rough scale

For

`G(z) = V(z)⁻¹`,  `T(z) = ceil(exp(G(z)))`,

this file records the asymptotic facts supplied by the proved two-sided
Euler-product estimates.  In particular no rough-number distribution or
prime-pattern hypothesis is introduced here.
-/

namespace PrimeGapNormality.Prime.CoreRoughScaleLimits

open Filter
open scoped Topology

open CoreRoughSyntheticScale

noncomputable section

/-- The elementary upper Euler-product estimate gives the useful pointwise
lower bound `log z ≤ G(z)` once `z ≥ 2`. -/
theorem log_le_roughGapScale {z : ℕ} (hz : 2 ≤ z) :
    Real.log (z : ℝ) ≤ roughGapScale z := by
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlog : 0 < Real.log (z : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hzR)
  have hV : 0 < eulerProdNat z := eulerProdNat_pos z
  have hupper : eulerProdNat z ≤ 1 / Real.log (z : ℝ) := by
    simpa only [eulerProd_coe_nat] using eulerProd_le_inv_log hzR
  unfold roughGapScale
  rw [inv_eq_one_div, le_div_iff₀ hV]
  calc
    Real.log (z : ℝ) * eulerProdNat z =
        eulerProdNat z * Real.log (z : ℝ) := mul_comm _ _
    _ ≤ (1 / Real.log (z : ℝ)) * Real.log (z : ℝ) :=
      mul_le_mul_of_nonneg_right hupper hlog.le
    _ = 1 := by field_simp [hlog.ne']

/-- The proved lower Euler-product estimate supplies the complementary
polylogarithmic upper bound on the synthetic gap scale. -/
theorem roughGapScale_le_log_div_lowerConst {z : ℕ} (hz : 16 ≤ z) :
    roughGapScale z ≤ Real.log (z : ℝ) / eulerProdLowerConst := by
  have hzR : (16 : ℝ) ≤ z := by exact_mod_cast hz
  have hlog : 0 < Real.log (z : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) hzR)
  have hV : 0 < eulerProdNat z := eulerProdNat_pos z
  have hlower : eulerProdLowerConst / Real.log (z : ℝ) ≤ eulerProdNat z := by
    simpa only [eulerProd_coe_nat] using eulerProd_ge_mul_inv_log hzR
  have hfactor : 0 ≤ Real.log (z : ℝ) / eulerProdLowerConst :=
    div_nonneg hlog.le eulerProdLowerConst_pos.le
  have hmul := mul_le_mul_of_nonneg_left hlower hfactor
  have hone :
      (Real.log (z : ℝ) / eulerProdLowerConst) *
          (eulerProdLowerConst / Real.log (z : ℝ)) = 1 := by
    field_simp [hlog.ne', eulerProdLowerConst_pos.ne']
  have hone_le :
      1 ≤ (Real.log (z : ℝ) / eulerProdLowerConst) * eulerProdNat z := by
    rwa [hone] at hmul
  unfold roughGapScale
  rw [inv_eq_one_div, div_le_iff₀ hV]
  exact hone_le

/-- The actual synthetic gap scale tends to infinity.  This follows already
from `V(z) ≤ 1/log z`; no Mertens asymptotic is needed. -/
theorem tendsto_roughGapScale_atTop :
    Tendsto roughGapScale atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [eventually_ge_atTop 2] with z hz
  exact log_le_roughGapScale hz

/-- The literal natural scale `ceil(exp(G(z)))` tends to infinity. -/
theorem tendsto_roughSyntheticScale_atTop :
    Tendsto roughSyntheticScale atTop atTop := by
  have hexp : Tendsto (fun z : ℕ ↦ Real.exp (roughGapScale z)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_roughGapScale_atTop
  apply (tendsto_nat_ceil_atTop.comp hexp).congr'
  exact Eventually.of_forall fun z ↦ rfl

/-- The ceiling changes the logarithmic synthetic scale by at most `log 2`.
This finite estimate is also convenient for later profile bounds. -/
theorem roughGapScale_le_log_synthetic_and_le (z : ℕ) :
    roughGapScale z ≤ Real.log (roughSyntheticScale z : ℝ) ∧
      Real.log (roughSyntheticScale z : ℝ) ≤ roughGapScale z + Real.log 2 := by
  let G := roughGapScale z
  let T := roughSyntheticScale z
  have hG0 : 0 ≤ G := (roughGapScale_pos z).le
  have hceil : Real.exp G ≤ (T : ℝ) := by
    dsimp only [T, roughSyntheticScale]
    exact Nat.le_ceil _
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr (roughSyntheticScale_pos z)
  have hlower : G ≤ Real.log (T : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos G) hceil
    simpa only [Real.log_exp] using h
  have hceilUpper : (T : ℝ) ≤ Real.exp G + 1 := by
    dsimp only [T, roughSyntheticScale]
    exact (Nat.ceil_lt_add_one (Real.exp_nonneg G)).le
  have hexpOne : 1 ≤ Real.exp G := Real.one_le_exp hG0
  have htwo : (T : ℝ) ≤ 2 * Real.exp G := by linarith
  have hupper : Real.log (T : ℝ) ≤ Real.log (2 * Real.exp G) :=
    Real.log_le_log hTpos htwo
  have hlogTwo : Real.log (2 * Real.exp G) = G + Real.log 2 := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero G),
      Real.log_exp]
    ring
  exact ⟨by simpa only [G, T] using hlower,
    by simpa only [hlogTwo, G, T] using hupper⟩

/-- Uniform logarithmic calibration of the literal ceiling scale:
`log T(z) / G(z) → 1`. -/
theorem tendsto_log_roughSyntheticScale_div_roughGapScale :
    Tendsto (fun z : ℕ ↦
      Real.log (roughSyntheticScale z : ℝ) / roughGapScale z)
      atTop (nhds 1) := by
  have hinv : Tendsto (fun z : ℕ ↦ (roughGapScale z)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_roughGapScale_atTop
  have herror : Tendsto (fun z : ℕ ↦
      Real.log 2 / roughGapScale z) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (Real.log 2)
  have hupper : Tendsto (fun z : ℕ ↦
      (1 : ℝ) + Real.log 2 / roughGapScale z) atTop (nhds 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add herror
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (1 : ℝ))) hupper
    (Eventually.of_forall fun z ↦ ?_) (Eventually.of_forall fun z ↦ ?_)
  · have hG := roughGapScale_pos z
    rw [le_div_iff₀ hG, one_mul]
    exact (roughGapScale_le_log_synthetic_and_le z).1
  · have hG := roughGapScale_pos z
    rw [div_le_iff₀ hG]
    have hbound := (roughGapScale_le_log_synthetic_and_le z).2
    have hne := hG.ne'
    have hrhs :
        ((1 : ℝ) + Real.log 2 / roughGapScale z) * roughGapScale z =
          roughGapScale z + Real.log 2 := by
      field_simp [hne]
    rw [hrhs]
    exact hbound

end

end PrimeGapNormality.Prime.CoreRoughScaleLimits
