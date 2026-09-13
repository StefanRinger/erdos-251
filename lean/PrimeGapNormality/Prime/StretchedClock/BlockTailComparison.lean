import PrimeGapNormality.Prime.StretchedClock.TailPrimeMean
import PrimeGapNormality.Prime.StretchedClock.GenericBlockComparison

/-! The actual single-block tail comparison, summed over all its digits.
This is the finite gain used before averaging over prime-index prefixes.
It assumes an explicit freeze error, not a distribution statement. -/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset
open scoped NNReal BoundedContinuousFunction
noncomputable section

def surrogate (B n r : ℕ) : Circle :=
  ((B : ℝ) ^ r * (nthPrime n : ℝ) / ((localBase B n : ℝ) - 1) : ℝ)

private theorem test_coe_diff_le (f : Circle →ᵇ ℝ) {K : ℝ≥0}
    (hK : LipschitzWith K f) (x y : ℝ) :
    |f (x : Circle) - f (y : Circle)| ≤ (K : ℝ) * |x - y| := by
  have hd : dist (x : Circle) (y : Circle) ≤ |x - y| := by
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  have h := hK.dist_le_mul (x : Circle) (y : Circle)
  rw [Real.dist_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_left hd K.coe_nonneg)

/-- The freeze error is multiplied by the geometric sum, while the gap
term loses its full local-base denominator. -/
theorem block_test_error_le {B n : ℕ} (hB : 2 ≤ B)
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    {err : ℝ} (herr : |actualTail B n - frozenTail (localBase B n) n| ≤ err) :
    (∑ r ∈ range (step B n),
      |f (orbit B (position B n + r)) - f (surrogate B n r)|) ≤
      (K : ℝ) * (((localBase B n : ℝ) - 1) / ((B : ℝ) - 1) * err +
        gapMajorant n / ((localBase B n : ℝ) * ((B : ℝ) - 1))) := by
  let q := localBase B n
  let U := frozenGapTail q n
  have hq : 2 ≤ q := localBase_two_le hB n
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hden : 0 < (q : ℝ) - 1 := sub_pos.mpr hqR
  have hU : 0 ≤ U := tsum_nonneg fun j =>
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_lt_one.trans hqR).le _)
  have he : frozenTail q n - (nthPrime n : ℝ) / ((q : ℝ) - 1) =
      U / ((q : ℝ) - 1) := by
    rw [frozenTail_eq_abel hq]
    dsimp only [U]
    ring
  have hreal : |actualTail B n - (nthPrime n : ℝ) / ((q : ℝ) - 1)| ≤
      err + U / ((q : ℝ) - 1) := by
    have ht := abs_sub_le (actualTail B n) (frozenTail q n)
      ((nthPrime n : ℝ) / ((q : ℝ) - 1))
    rw [he, abs_of_nonneg (div_nonneg hU hden.le)] at ht
    exact ht.trans (_root_.add_le_add herr le_rfl)
  have hp (r : ℕ) :
      |f (orbit B (position B n + r)) - f (surrogate B n r)| ≤
        (K : ℝ) * ((B : ℝ) ^ r * (err + U / ((q : ℝ) - 1))) := by
    rw [orbit_position_add hB]
    have ht := test_coe_diff_le f hK ((B : ℝ) ^ r * actualTail B n)
      ((B : ℝ) ^ r * ((nthPrime n : ℝ) / ((q : ℝ) - 1)))
    rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg (base_pos hB).le _)] at ht
    calc
      _ ≤ (K : ℝ) * ((B : ℝ) ^ r *
          |actualTail B n - (nthPrime n : ℝ) / ((q : ℝ) - 1)|) := by
        simpa only [surrogate, q, mul_div_assoc] using ht
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hreal (pow_nonneg (base_pos hB).le _)) K.coe_nonneg
  have hsum := sum_le_sum (fun r (_ : r ∈ range (step B n)) => hp r)
  rw [← mul_sum, ← sum_mul] at hsum
  have hgeo : (∑ r ∈ range (step B n), (B : ℝ) ^ r) =
      ((q : ℝ) - 1) / ((B : ℝ) - 1) := by
    simpa only [q, localBase, Nat.cast_pow] using
      geom_sum_eq (ne_of_gt (one_lt_base hB)) (step B n)
  rw [hgeo] at hsum
  have heq : (((q : ℝ) - 1) / ((B : ℝ) - 1)) *
      (err + U / ((q : ℝ) - 1)) =
        ((q : ℝ) - 1) / ((B : ℝ) - 1) * err + U / ((B : ℝ) - 1) := by
    field_simp [hden.ne', (sub_pos.mpr (one_lt_base hB)).ne']
    <;> ring
  rw [heq] at hsum
  have hgap := div_le_div_of_nonneg_right (frozenGapTail_le_gapMajorant_div hq n)
    (sub_pos.mpr (one_lt_base hB)).le
  have hgap' : U / ((B : ℝ) - 1) ≤
      gapMajorant n / ((q : ℝ) * ((B : ℝ) - 1)) := by
    simpa only [U, div_div] using hgap
  exact hsum.trans (mul_le_mul_of_nonneg_left
    (_root_.add_le_add le_rfl hgap') K.coe_nonneg)

end
end PrimeGapNormality.Prime.StretchedClock
