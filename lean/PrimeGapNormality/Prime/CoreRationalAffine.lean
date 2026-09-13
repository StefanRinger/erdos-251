import PrimeGapNormality.Prime.Independence
import Mathlib.Data.Rat.Lemmas

/-! Minimal rational-translation invariance for the scalar Weyl criterion. -/

namespace PrimeGapNormality.Prime.CoreRationalAffine

/-- Adding a rational number preserves Weyl's criterion.  The denominator
is cleared using integer scaling, followed by an integer translation and
the existing Wall scaling lemma. -/
theorem weylCriterion_add_rat {b : ℕ} (hb : 2 ≤ b) {θ : ℝ} (q : ℚ)
    (h : weylCriterion b θ) : weylCriterion b (θ + q) := by
  have hden1 : 1 ≤ q.den := Nat.succ_le_of_lt q.den_pos
  have hdenZ : (q.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr q.den_ne_zero
  have hmul : weylCriterion b ((q.den : ℤ) * θ) :=
    weylCriterion_int_mul hdenZ h
  have hadd : weylCriterion b ((q.den : ℤ) * θ + q.num) :=
    weylCriterion_add_int q.num hmul
  have hqn : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    exact_mod_cast q.den_mul_eq_num
  have hclear :
      (q.den : ℝ) * (θ + (q : ℝ)) =
        ((q.den : ℤ) : ℝ) * θ + (q.num : ℝ) := by
    have hcast : ((q.den : ℤ) : ℝ) = (q.den : ℝ) := Int.cast_natCast _
    rw [hcast, mul_add, hqn]
  have hscaled : weylCriterion b ((q.den : ℝ) * (θ + (q : ℝ))) := by
    rw [hclear]
    convert hadd
  exact weylCriterion_of_mul hden1 hb hscaled

end PrimeGapNormality.Prime.CoreRationalAffine
