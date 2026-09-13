import PrimeGapNormality.Prime.CoreRoughCutoffInclusion
import PrimeGapNormality.Prime.CoreSieveHazard

/-!
# Finite bounds for the exact rough-cutoff inclusion factor

All statements concern the actual factor from
`CoreRoughCutoffInclusion`.  No Bernoulli replacement or asymptotic input is
used, and moment comparisons never divide by a possibly zero moment.
-/

namespace PrimeGapNormality.Prime.CoreRoughCutoffBounds

open Finset
open scoped BigOperators Classical

noncomputable section

private def newPrimes (z y : ℕ) : Finset ℕ :=
  Nat.primesLE y \ Nat.primesLE z

private def hazard (p : ℕ) : ℝ := (((p - 1 : ℕ) : ℝ))⁻¹

private theorem newPrime_gt {z y p : ℕ} (hp : p ∈ newPrimes z y) : z < p := by
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have hpNot : p ∉ Nat.primesLE z := (mem_sdiff.mp hp).2
  exact Nat.lt_of_not_ge fun hpz ↦
    hpNot (Nat.mem_primesLE.mpr ⟨hpz, hpPrime⟩)

private theorem hazard_nonneg {p : ℕ} : 0 ≤ hazard p := by
  unfold hazard
  positivity

private theorem hazard_lt_one {z y p : ℕ} (hz : 2 ≤ z)
    (hp : p ∈ newPrimes z y) : hazard p < 1 := by
  have hpgt : z < p := newPrime_gt hp
  have hpred : (1 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 1 < p - 1 by omega)
  unfold hazard
  exact inv_lt_one_of_one_lt₀ hpred

private theorem cast_mul_hazard_nonneg {j p : ℕ} :
    0 ≤ (j : ℝ) * hazard p :=
  mul_nonneg (Nat.cast_nonneg j) hazard_nonneg

private theorem cast_mul_hazard_le_one {z y j p : ℕ} (hjz : j ≤ z)
    (hp : p ∈ newPrimes z y) : (j : ℝ) * hazard p ≤ 1 := by
  have hpgt : z < p := newPrime_gt hp
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have hp2 : 2 ≤ p := hpPrime.two_le
  have hpredNat : j ≤ p - 1 := by omega
  have hpredPos : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast (show 0 < p - 1 by omega)
  unfold hazard
  rw [← div_eq_mul_inv]
  exact (div_le_one hpredPos).mpr (by exact_mod_cast hpredNat)

private theorem cutoffFactor_eq_survival (z y : ℕ) :
    CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1 =
      CoreSieveHazard.survivalProduct (newPrimes z y) hazard := by
  unfold CoreRoughCutoffInclusion.cutoffInclusionFactor
  unfold CoreSieveHazard.survivalProduct newPrimes hazard
  apply prod_congr rfl
  intro p _
  simp only [Nat.cast_one, one_div]

/-- The one-point exact cutoff factor is strictly positive. -/
theorem cutoffInclusionFactor_one_pos {z y : ℕ} (hz : 2 ≤ z) :
    0 < CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1 := by
  rw [cutoffFactor_eq_survival]
  exact CoreSieveHazard.survivalProduct_pos
    (fun _ _ ↦ hazard_nonneg)
    (fun p hp ↦ hazard_lt_one hz hp)

/-- The one-point exact cutoff factor is at most one. -/
theorem cutoffInclusionFactor_one_le_one {z y : ℕ} (hz : 2 ≤ z) :
    CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1 ≤ 1 := by
  rw [cutoffFactor_eq_survival]
  exact CoreSieveHazard.survivalProduct_le_one
    (fun _ _ ↦ hazard_nonneg)
    (fun p hp ↦ hazard_lt_one hz hp)

/-- Every local `j`-point factor lies in `[0,1]` once `j≤z<p`. -/
theorem cutoffInclusion_localFactor_bounds
    {z y j p : ℕ} (hjz : j ≤ z) (hp : p ∈ newPrimes z y) :
    0 ≤ 1 - (j : ℝ) / ((p - 1 : ℕ) : ℝ) ∧
      1 - (j : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ 1 := by
  have hja0 := cast_mul_hazard_nonneg (j := j) (p := p)
  have hja1 := cast_mul_hazard_le_one hjz hp
  unfold hazard at hja0 hja1
  rw [div_eq_mul_inv]
  constructor
  · exact sub_nonneg.mpr hja1
  · linarith

/-- Consequently the full exact `j`-point factor lies in `[0,1]`. -/
theorem cutoffInclusionFactor_bounds {z y j : ℕ} (hjz : j ≤ z) :
    0 ≤ CoreRoughCutoffInclusion.cutoffInclusionFactor z y j ∧
      CoreRoughCutoffInclusion.cutoffInclusionFactor z y j ≤ 1 := by
  unfold CoreRoughCutoffInclusion.cutoffInclusionFactor
  constructor
  · exact prod_nonneg fun p hp ↦ (cutoffInclusion_localFactor_bounds hjz hp).1
  · exact prod_le_one
      (fun p hp ↦ (cutoffInclusion_localFactor_bounds hjz hp).1)
      (fun p hp ↦ (cutoffInclusion_localFactor_bounds hjz hp).2)

/-- Hazard lower bound for the exact `j`-point factor. -/
theorem cutoffInclusionFactor_ge_one_sub_two_mul
    {z y j : ℕ} (hz : 2 ≤ z) (hjz : j ≤ z)
    (hhalf : (1 : ℝ) / 2 ≤
      CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1) :
    1 - 2 * (j : ℝ) *
        (1 - CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1) ≤
      CoreRoughCutoffInclusion.cutoffInclusionFactor z y j := by
  have hsum := CoreSieveHazard.sum_le_two_mul_one_sub_survivalProduct
    (s := newPrimes z y) (a := hazard)
    (fun _ _ ↦ hazard_nonneg) (fun p hp ↦ hazard_lt_one hz hp)
    (by simpa only [← cutoffFactor_eq_survival] using hhalf)
  rw [← cutoffFactor_eq_survival z y] at hsum
  have hbonf := CoreSieveHazard.product_one_sub_mul_ge
    (s := newPrimes z y) (a := hazard) (j := (j : ℝ))
    (Nat.cast_nonneg j)
    (fun p _ ↦ cast_mul_hazard_nonneg)
    (fun p hp ↦ cast_mul_hazard_le_one hjz hp)
  have hbonf' :
      1 - (j : ℝ) * (∑ p ∈ newPrimes z y, hazard p) ≤
        CoreRoughCutoffInclusion.cutoffInclusionFactor z y j := by
    simpa only [CoreRoughCutoffInclusion.cutoffInclusionFactor, newPrimes,
      hazard, div_eq_mul_inv] using hbonf
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg j)
  calc
    1 - 2 * (j : ℝ) *
        (1 - CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1) ≤
      1 - (j : ℝ) * (∑ p ∈ newPrimes z y, hazard p) := by
        linarith
    _ ≤ CoreRoughCutoffInclusion.cutoffInclusionFactor z y j := hbonf'

/-- Uniform version when only `j≤r≤z` is retained. -/
theorem cutoffInclusionFactor_ge_of_le_rank
    {z y j r : ℕ} (hz : 2 ≤ z) (hjr : j ≤ r) (hrz : r ≤ z)
    (hhalf : (1 : ℝ) / 2 ≤
      CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1) :
    1 - 2 * (r : ℝ) *
        (1 - CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1) ≤
      CoreRoughCutoffInclusion.cutoffInclusionFactor z y j := by
  have hθ1 := cutoffInclusionFactor_one_le_one (y := y) hz
  have hdef : 0 ≤ 1 - CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1 :=
    sub_nonneg.mpr hθ1
  have hjrR : (j : ℝ) ≤ r := by exact_mod_cast hjr
  have hmain := cutoffInclusionFactor_ge_one_sub_two_mul hz (hjr.trans hrz) hhalf
  have hmul := mul_le_mul_of_nonneg_right hjrR hdef
  nlinarith

private theorem actual_countMoment_nonneg (y S j : ℕ) :
    0 ≤ Stopped.countMoment (offsetWindow S) (actualRootLaw y S) j := by
  unfold Stopped.countMoment
  exact sum_nonneg fun U _ ↦
    mul_nonneg (actualRootLaw_nonneg y S U) (Nat.cast_nonneg _)

/-- Exact multiplicative moment bounds, with no division by the old
moment. -/
theorem actualRootLaw_countMoment_cutoff_bounds
    {S z y j : ℕ} (hSz : S < z) (hzy : z ≤ y) (hz : 2 ≤ z)
    (hjz : j ≤ z)
    (hhalf : (1 : ℝ) / 2 ≤
      CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1) :
    (1 - 2 * (j : ℝ) *
        (1 - CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1)) *
          Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j ≤
      Stopped.countMoment (offsetWindow S) (actualRootLaw y S) j ∧
    Stopped.countMoment (offsetWindow S) (actualRootLaw y S) j ≤
      Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j := by
  have hexact := CoreRoughCutoffInclusion.actualRootLaw_countMoment_cutoff
    (j := j) hSz hzy
  have hM0 := actual_countMoment_nonneg z S j
  have hθlower := cutoffInclusionFactor_ge_one_sub_two_mul hz hjz hhalf
  have hθbounds := cutoffInclusionFactor_bounds (y := y) hjz
  constructor
  · rw [hexact]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hθlower hM0
  · rw [hexact]
    exact mul_le_of_le_one_right hM0 hθbounds.2

/-- Rank-uniform multiplicative lower bound for `j≤r≤z`, together with
the exact upper monotonicity. -/
theorem actualRootLaw_countMoment_cutoff_bounds_of_le_rank
    {S z y j r : ℕ} (hSz : S < z) (hzy : z ≤ y) (hz : 2 ≤ z)
    (hjr : j ≤ r) (hrz : r ≤ z)
    (hhalf : (1 : ℝ) / 2 ≤
      CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1) :
    (1 - 2 * (r : ℝ) *
        (1 - CoreRoughCutoffInclusion.cutoffInclusionFactor z y 1)) *
          Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j ≤
      Stopped.countMoment (offsetWindow S) (actualRootLaw y S) j ∧
    Stopped.countMoment (offsetWindow S) (actualRootLaw y S) j ≤
      Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j := by
  have hexact := CoreRoughCutoffInclusion.actualRootLaw_countMoment_cutoff
    (j := j) hSz hzy
  have hM0 := actual_countMoment_nonneg z S j
  have hθlower := cutoffInclusionFactor_ge_of_le_rank hz hjr hrz hhalf
  have hθbounds := cutoffInclusionFactor_bounds (y := y) (hjr.trans hrz)
  constructor
  · rw [hexact]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hθlower hM0
  · rw [hexact]
    exact mul_le_of_le_one_right hM0 hθbounds.2

end

end PrimeGapNormality.Prime.CoreRoughCutoffBounds
