import PrimeGapNormality.Prime.CoreRoughMovingCount
import PrimeGapNormality.Prime.CoreMovingRoughSequence

/-!
# Literal dyadic root counts from the one-point sieve

Density starts with the one-point arithmetic count. It need not first pass
through the growing-dimensional stopped comparison or its short slices.
This finite supplier is subsequently instantiated with the proved global
cutoff variation and actual beta level. No count asymptotic is assumed.
-/

namespace PrimeGapNormality.Prime.CoreRoughRootCount

open Finset CoreMovingRoughSequence CoreRoughMovingCount
open scoped Classical
noncomputable section

set_option maxHeartbeats 800000

theorem singleton_tupleProduct (y : ℕ) :
    finiteTupleSieveProduct {0} y = eulerProdNat y := by
  unfold finiteTupleSieveProduct eulerProdNat
  apply Finset.prod_congr rfl
  intro p hp
  simp only [residueCount, image_singleton, card_singleton, Nat.cast_one, one_div]

theorem rawPhysicalRoots_eq_singletonTuple (z : ℕ → ℕ) (X : ℕ) :
    rawPhysicalRoots z X = movingTupleInterval z {0} (X + 1) X := by
  ext n
  constructor
  · intro hn
    obtain ⟨hnI, hnR⟩ := mem_filter.mp hn
    have hXn := mem_Ioc.mp hnI
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    intro h hh
    have hh0 : h = 0 := mem_singleton.mp hh
    subst h
    simpa only [Nat.add_zero, IsMovingRough, RoughAt] using hnR
  · intro hn
    obtain ⟨hnI, hnR⟩ := mem_filter.mp hn
    have hXn := mem_Ico.mp hnI
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
    have hh := hnR 0 (mem_singleton_self 0)
    simpa only [Nat.add_zero, IsMovingRough, RoughAt] using hh

/-- Genuine finite root-count error with dimension one. The entire CRT
error is exp(10)*R, with no missing factor from a cell decomposition. -/
theorem rawPhysicalRoots_error
    (z : ℕ → ℕ) (X : ℕ) {yl yu : ℕ} (hyl : 16 ≤ yl) (hlyu : yl ≤ yu)
    (hcut : ∀ n ∈ Ioc X (2 * X), yl ≤ z n ∧ z n ≤ yu)
    {δ R : ℝ} (hδ : δ ≤ 1 / 2)
    (hband : ∑ p ∈ Nat.primesLE yu \ Nat.primesLE yl, (p : ℝ)⁻¹ ≤ δ)
    (hlevel : ((yu : ℝ) + 1 / 2) ^ (10 : ℕ) ≤ R) :
    |((rawPhysicalRoots z X).card : ℝ) - (X : ℝ) * eulerProdNat yl| ≤
      (X : ℝ) * eulerProdNat yl *
        (δ + Real.exp (299 - Real.log R / Real.log ((yu : ℝ) + 1 / 2))) +
      Real.exp 10 * R := by
  have hcut' : ∀ n ∈ Ico (X + 1) (X + 1 + X), ∀ h ∈ ({0} : Finset ℕ),
      yl ≤ z (n + h) ∧ z (n + h) ≤ yu := by
    intro n hn h hh
    have hh0 : h = 0 := mem_singleton.mp hh
    subst h
    have hhI := mem_Ico.mp hn
    simpa only [Nat.add_zero] using hcut n (mem_Ioc.mpr ⟨by omega, by omega⟩)
  have hband' : ∑ p ∈ Nat.primesLE yu \ Nat.primesLE yl,
      (residueCount {0} p : ℝ) / (p : ℝ) ≤ δ := by
    simpa only [residueCount, image_singleton, card_singleton, Nat.cast_one, one_div] using hband
  have hlevel' : ((yu : ℝ) + 1 / 2) ^ (9 * ({0} : Finset ℕ).card + 1) ≤ R := by
    simpa only [card_singleton] using hlevel
  have hcount := movingTupleInterval_error z {0} (by simp) (X + 1) X
    (by omega) hyl hlyu hcut' hδ hband' hlevel'
  rw [← rawPhysicalRoots_eq_singletonTuple, singleton_tupleProduct] at hcount
  simpa only [card_singleton, Nat.cast_one, mul_one, Nat.sub_self, pow_zero] using hcount

/-- Relative root-count error. Positivity of the normalizing one-point
Euler factor is proved, not postulated as a nonzero tuple condition. -/
theorem rawPhysicalRoots_relative_error
    (z : ℕ → ℕ) {X : ℕ} (hX : 0 < X)
    {yl yu : ℕ} (hyl : 16 ≤ yl) (hlyu : yl ≤ yu)
    (hcut : ∀ n ∈ Ioc X (2 * X), yl ≤ z n ∧ z n ≤ yu)
    {δ R : ℝ} (hδ : δ ≤ 1 / 2)
    (hband : ∑ p ∈ Nat.primesLE yu \ Nat.primesLE yl, (p : ℝ)⁻¹ ≤ δ)
    (hlevel : ((yu : ℝ) + 1 / 2) ^ (10 : ℕ) ≤ R) :
    |((rawPhysicalRoots z X).card : ℝ) / ((X : ℝ) * eulerProdNat yl) - 1| ≤
      δ + Real.exp (299 - Real.log R / Real.log ((yu : ℝ) + 1 / 2)) +
        Real.exp 10 * R / ((X : ℝ) * eulerProdNat yl) := by
  have hden : 0 < (X : ℝ) * eulerProdNat yl :=
    mul_pos (Nat.cast_pos.mpr hX) (eulerProdNat_pos yl)
  have hnorm :
      |((rawPhysicalRoots z X).card : ℝ) / ((X : ℝ) * eulerProdNat yl) - 1| =
        |((rawPhysicalRoots z X).card : ℝ) - (X : ℝ) * eulerProdNat yl| /
          ((X : ℝ) * eulerProdNat yl) := by
    rw [div_sub_one hden.ne', abs_div, abs_of_pos hden]
  rw [hnorm]
  have hh := div_le_div_of_nonneg_right
    (rawPhysicalRoots_error z X hyl hlyu hcut hδ hband hlevel) hden.le
  simpa only [add_div, mul_div_cancel_left₀ _ hden.ne'] using hh

end
end PrimeGapNormality.Prime.CoreRoughRootCount
