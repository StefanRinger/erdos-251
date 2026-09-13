import PrimeGapNormality.Prime.ExactRootMix
import PrimeGapNormality.Prime.SieveCutoffCal
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Synthetic scale for reuse of the finite rough model

For `V(z)=eulerProdNat z`, set `G(z)=V(z)⁻¹` and
`T(z)=ceil(exp(G(z)))`.  This file proves only the finite scale and cutoff
ordering facts; it makes no rough-number or asymptotic claim.
-/

namespace PrimeGapNormality.Prime.CoreRoughSyntheticScale

open Finset

noncomputable section

/-- Synthetic logarithmic scale `G(z)=V(z)⁻¹`. -/
def roughGapScale (z : ℕ) : ℝ := (eulerProdNat z)⁻¹

/-- Synthetic mixture scale `T(z)=ceil(exp(G(z)))`. -/
def roughSyntheticScale (z : ℕ) : ℕ := ⌈Real.exp (roughGapScale z)⌉₊

theorem roughGapScale_pos (z : ℕ) : 0 < roughGapScale z := by
  unfold roughGapScale
  exact inv_pos.mpr (eulerProdNat_pos z)

theorem roughSyntheticScale_pos (z : ℕ) : 0 < roughSyntheticScale z := by
  have hceil : Real.exp (roughGapScale z) ≤ (roughSyntheticScale z : ℝ) := by
    exact Nat.le_ceil _
  have hpos : (0 : ℝ) < roughSyntheticScale z :=
    (Real.exp_pos _).trans_le hceil
  exact_mod_cast hpos

/-- Every coordinate of the literal synthetic mixture lies in the uniform
logarithmic window `G < log t ≤ G+log 4`. -/
theorem mixScale_log_bounds {z t : ℕ}
    (ht : t ∈ mixScale (roughSyntheticScale z)) :
    roughGapScale z < Real.log (t : ℝ) ∧
      Real.log (t : ℝ) ≤ roughGapScale z + Real.log 4 := by
  let G := roughGapScale z
  let T := roughSyntheticScale z
  have hG0 : 0 ≤ G := (roughGapScale_pos z).le
  have htIoc := mem_Ioc.mp ht
  have hceil : Real.exp G ≤ (T : ℝ) := by
    dsimp only [T, roughSyntheticScale]
    exact Nat.le_ceil _
  have hTt : (T : ℝ) < t := Nat.cast_lt.mpr htIoc.1
  have hexpt : Real.exp G < (t : ℝ) := hceil.trans_lt hTt
  have htpos : (0 : ℝ) < t := (Real.exp_pos G).trans hexpt
  have hlower : G < Real.log (t : ℝ) :=
    (Real.lt_log_iff_exp_lt htpos).mpr hexpt
  have hTupper : (T : ℝ) ≤ Real.exp G + 1 := by
    dsimp only [T, roughSyntheticScale]
    exact (Nat.ceil_lt_add_one (Real.exp_nonneg G)).le
  have hexp1 : 1 ≤ Real.exp G := Real.one_le_exp hG0
  have hTtwo : (T : ℝ) ≤ 2 * Real.exp G := by linarith
  have httwo : (t : ℝ) ≤ 2 * (T : ℝ) := by
    have hcast : (t : ℝ) ≤ ((2 * T : ℕ) : ℝ) := Nat.cast_le.mpr htIoc.2
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcast
  have htFour : (t : ℝ) ≤ 4 * Real.exp G := httwo.trans (by nlinarith)
  have hlogle : Real.log (t : ℝ) ≤ Real.log (4 * Real.exp G) :=
    Real.log_le_log htpos htFour
  have hlogeq : Real.log (4 * Real.exp G) = G + Real.log 4 := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero G),
      Real.log_exp]
    ring
  exact ⟨by simpa only [G] using hlower,
    by simpa only [hlogeq, G] using hlogle⟩

/-- The synthetic starting cutoff `z` is strictly below every canonical
sieve cutoff occurring in the literal mixture at scale `T(z)`. -/
theorem lt_sieveCutoff_of_mem_mixScale {z t : ℕ}
    (ht : t ∈ mixScale (roughSyntheticScale z)) :
    z < sieveCutoff (t : ℝ) := by
  have hlogs := mixScale_log_bounds ht
  have hGpos := roughGapScale_pos z
  have hlogpos : 0 < Real.log (t : ℝ) := hGpos.trans hlogs.1
  have ht1 : (1 : ℝ) < t :=
    (Real.log_pos_iff (Nat.cast_nonneg t)).mp hlogpos
  have hy := sieveCutoff_spec ht1
  have hyUpper : eulerProdNat (sieveCutoff (t : ℝ)) ≤ 1 / Real.log (t : ℝ) := by
    have h := hy.2.1
    rwa [eulerProd_coe_nat] at h
  have hinv : 1 / Real.log (t : ℝ) < 1 / roughGapScale z :=
    one_div_lt_one_div_of_lt hGpos hlogs.1
  have hrecover : 1 / roughGapScale z = eulerProdNat z := by
    unfold roughGapScale
    simp only [one_div, inv_inv]
  have hstrict : 1 / Real.log (t : ℝ) < eulerProdNat z := by
    rwa [hrecover] at hinv
  by_contra hnot
  have hyz : sieveCutoff (t : ℝ) ≤ z := Nat.not_lt.mp hnot
  have hmono : eulerProdNat z ≤ eulerProdNat (sieveCutoff (t : ℝ)) :=
    eulerProdNat_mono hyz
  exact (not_lt_of_ge (hmono.trans hyUpper)) hstrict

/-- Combined scale package used by the later synthetic rough-model
comparison. -/
theorem mixScale_scale_and_cutoff {z t : ℕ}
    (ht : t ∈ mixScale (roughSyntheticScale z)) :
    roughGapScale z < Real.log (t : ℝ) ∧
      Real.log (t : ℝ) ≤ roughGapScale z + Real.log 4 ∧
        z < sieveCutoff (t : ℝ) :=
  ⟨(mixScale_log_bounds ht).1, (mixScale_log_bounds ht).2,
    lt_sieveCutoff_of_mem_mixScale ht⟩

end

end PrimeGapNormality.Prime.CoreRoughSyntheticScale
