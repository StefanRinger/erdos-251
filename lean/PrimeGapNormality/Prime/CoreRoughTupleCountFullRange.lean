import PrimeGapNormality.Prime.CoreRoughTupleCount
import PrimeGapNormality.Prime.SingularSeriesTail
import Mathlib.NumberTheory.Primorial

/-!
# The finite rough-tuple bound down to cutoff four

The existing beta-sieve estimate handles y≥16. Below sixteen the exact
CRT discrepancy is at most the actual primorial, hence at most30030.
The original beta-level assumption already makes R at least4^10, so the
same additive error absorbs this finite case. No new sieve assumption
or change of the constants299 and10 is made.
-/
namespace PrimeGapNormality.Prime.CoreRoughTupleCountFullRange
open Finset CoreRoughTupleCount CoreRoughShiftResidues CoreRoughMixedCRT
  CoreRoughSiftedCount CoreRoughResidueCount
open scoped Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Uniform deterministic CRT discrepancy, including zero local factors. -/
theorem avoidedInterval_error_le_primorial (E : Finset ℕ) (y a H : ℕ) :
    |((avoidedInterval E y a H).card : ℝ) - (H : ℝ) * finiteTupleSieveProduct E y| ≤
      (primorial y : ℝ) := by
  let P := Nat.primesLE y
  let B := forbiddenResidues E
  have hprime : ∀ p : ↥(P ∪ (∅ : Finset ℕ)), Nat.Prime p.1 := by
    intro p
    have hp : p.1 ∈ Nat.primesLE y := by simpa only [P, union_empty] using p.2
    exact (Nat.mem_primesLE.mp hp).2
  have hcrt := mixedInterval_count_error B P ∅ (disjoint_empty_right P) hprime a H
  have hinterval : mixedInterval B P ∅ a H = avoidedInterval E y a H := by
    ext n
    simp [mixedInterval, avoidedInterval, B, P, hits]
  have hdensity : earlyDensity B P = finiteTupleSieveProduct E y := by
    rw [earlyDensity_eq_product B P (fun p hp => (Nat.mem_primesLE.mp hp).2)]
    unfold finiteTupleSieveProduct
    apply Finset.prod_congr rfl
    intro p hp
    rw [card_forbiddenResidues_eq_residueCount E (Nat.mem_primesLE.mp hp).2]
  have hmain : (H : ℝ) / (∏ p ∈ P, p : ℕ) * (earlyChoices B P : ℝ) =
      (H : ℝ) * finiteTupleSieveProduct E y := by
    rw [← hdensity]
    unfold earlyDensity residueModulus
    ring
  simp only [hinterval, Finset.prod_empty, Nat.mul_one, lateChoices, Finset.prod_empty,
    Nat.cast_one, mul_one, hmain] at hcrt
  have hchoices : earlyChoices B P ≤ primorial y := by
    rw [primorial_eq_prod_primesLE]
    exact Finset.prod_le_prod' fun p hp => Nat.sub_le p (B p).card
  exact hcrt.trans (Nat.cast_le.mpr hchoices)

/-- The same additive envelope dominates R at every nonnegative order. -/
theorem level_le_additive {k : ℕ} {R : ℝ} (hR : 1 ≤ R) :
    R ≤ Real.exp (10 * (k : ℝ)) * R * (1 + Real.log R) ^ (k - 1) := by
  have he : 1 ≤ Real.exp (10 * (k : ℝ)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hp : 1 ≤ (1 + Real.log R) ^ (k - 1) :=
    one_le_pow₀ (by linarith [Real.log_nonneg hR])
  calc
    R = 1 * R * 1 := by ring
    _ ≤ Real.exp (10 * (k : ℝ)) * R * (1 + Real.log R) ^ (k - 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_right he (zero_le_one.trans hR)) hp
        zero_le_one (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans hR))

theorem avoidedInterval_error_half (E : Finset ℕ) (hE : 1 ≤ E.card)
    {y : ℕ} (hy : 4 ≤ y) {R : ℝ}
    (hlevel : ((y : ℝ) + 1 / 2) ^ (9 * E.card + 1) ≤ R) (a H : ℕ) :
    |((avoidedInterval E y a H).card : ℝ) - (H : ℝ) * finiteTupleSieveProduct E y| ≤
      (H : ℝ) * finiteTupleSieveProduct E y *
        Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log ((y : ℝ) + 1 / 2)) +
      Real.exp (10 * (E.card : ℝ)) * R * (1 + Real.log R) ^ (E.card - 1) := by
  by_cases hlarge : 16 ≤ y
  · exact CoreRoughTupleCount.avoidedInterval_error E hE hlarge
      (by linarith) (by linarith) hlevel a H
  have hprim : (primorial y : ℝ) ≤ 30030 := by
    have h15 : primorial 15 = 30030 := by decide
    exact_mod_cast (primorial_mono (show y ≤ 15 by omega)).trans_eq h15
  have hyR : (4 : ℝ) ≤ y := by exact_mod_cast hy
  have hbase : (4 : ℝ) ≤ (y : ℝ) + 1 / 2 := by linarith
  have hR : (30030 : ℝ) ≤ R := by
    calc
      (30030 : ℝ) ≤ (4 : ℝ) ^ (10 : ℕ) := by norm_num
      _ ≤ ((y : ℝ) + 1 / 2) ^ (10 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hbase 10
      _ ≤ ((y : ℝ) + 1 / 2) ^ (9 * E.card + 1) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      _ ≤ R := hlevel
  have herror := (avoidedInterval_error_le_primorial E y a H).trans hprim
  have hR1 : 1 ≤ R := (by norm_num : (1 : ℝ) ≤ 30030).trans hR
  have hmain0 : 0 ≤ (H : ℝ) * finiteTupleSieveProduct E y *
      Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log ((y : ℝ) + 1 / 2)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (finiteTupleSieveProduct_nonneg E y))
      (Real.exp_pos _).le
  exact (herror.trans (hR.trans (level_le_additive (k := E.card) hR1))).trans
    (le_add_of_nonneg_left hmain0)

/-- Positive natural intervals may equivalently use literal fixed-cutoff roughness. -/
theorem translatedRoughInterval_error_half (E : Finset ℕ) (hE : 1 ≤ E.card)
    {y : ℕ} (hy : 4 ≤ y) {R : ℝ}
    (hlevel : ((y : ℝ) + 1 / 2) ^ (9 * E.card + 1) ≤ R)
    (a H : ℕ) (ha : 1 ≤ a) :
    |((translatedRoughInterval E y a H).card : ℝ) - (H : ℝ) * finiteTupleSieveProduct E y| ≤
      (H : ℝ) * finiteTupleSieveProduct E y *
        Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log ((y : ℝ) + 1 / 2)) +
      Real.exp (10 * (E.card : ℝ)) * R * (1 + Real.log R) ^ (E.card - 1) := by
  rw [← avoidedInterval_eq_translatedRoughInterval E y a H ha]
  exact avoidedInterval_error_half E hE hy hlevel a H

/-- At a real cutoff the actual prime set is its natural-floor prime set.
No strict inequality 4k<floor(y) is imposed. -/
theorem avoidedInterval_error_realCutoff (E : Finset ℕ) (hE : 1 ≤ E.card)
    {y R : ℝ} (hy : 4 * (E.card : ℝ) < y)
    (hlevel : ((⌊y⌋₊ : ℝ) + 1 / 2) ^ (9 * E.card + 1) ≤ R) (a H : ℕ) :
    |((avoidedInterval E ⌊y⌋₊ a H).card : ℝ) - (H : ℝ) * finiteTupleSieveProduct E ⌊y⌋₊| ≤
      (H : ℝ) * finiteTupleSieveProduct E ⌊y⌋₊ *
        Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log ((⌊y⌋₊ : ℝ) + 1 / 2)) +
      Real.exp (10 * (E.card : ℝ)) * R * (1 + Real.log R) ^ (E.card - 1) := by
  have hcard : (1 : ℝ) ≤ E.card := by exact_mod_cast hE
  have hy4 : (4 : ℝ) ≤ y := by linarith
  have hfloor : 4 ≤ ⌊y⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hy4)
  exact avoidedInterval_error_half E hE hfloor hlevel a H

end
end PrimeGapNormality.Prime.CoreRoughTupleCountFullRange
