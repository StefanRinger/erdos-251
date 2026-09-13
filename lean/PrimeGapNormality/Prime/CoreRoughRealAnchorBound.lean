import PrimeGapNormality.Prime.CoreRoughPowerBand

/-! Rounding the real anchor in a moving cutoff costs an explicit extra
power-band width. The real anchor is never silently replaced by its floor.
No distribution or density input occurs in these finite inequalities. -/

namespace PrimeGapNormality.Prime.CoreRoughRealAnchorBound

open CoreRoughPowerBand
noncomputable section

def roundedBandWidth (y : ℕ) (η : ℝ) : ℝ :=
  η + 2 / ((y : ℝ) * Real.log (y : ℝ))

theorem log_anchor_le {x : ℝ} (hx : 0 ≤ x) (hy : 2 ≤ ⌊x⌋₊) :
    Real.log x ≤ Real.log (⌊x⌋₊ : ℝ) + 1 / (⌊x⌋₊ : ℝ) := by
  let y : ℝ := ⌊x⌋₊
  have hypos : 0 < y := Nat.cast_pos.mpr (show 0 < ⌊x⌋₊ by omega)
  have hyx : y ≤ x := Nat.floor_le hx
  have hxpos : 0 < x := hypos.trans_le hyx
  have hupper : x < y + 1 := Nat.lt_floor_add_one x
  have hratio : x / y ≤ 1 + 1 / y := by
    apply (div_le_iff₀ hypos).2
    have heq : (1 + 1 / y) * y = y + 1 := by field_simp [hypos.ne']
    rw [heq]
    exact hupper.le
  have hlog := Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
  rw [Real.log_div hxpos.ne' hypos.ne'] at hlog
  change Real.log x ≤ Real.log y + 1 / y
  linarith

theorem upper_power_le_rounded_power {x η : ℝ}
    (hx : 0 ≤ x) (hy : 2 ≤ ⌊x⌋₊) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    x ^ (1 + η) ≤ (⌊x⌋₊ : ℝ) ^ (1 + roundedBandWidth ⌊x⌋₊ η) := by
  let y : ℝ := ⌊x⌋₊
  have hypos : 0 < y := Nat.cast_pos.mpr (show 0 < ⌊x⌋₊ by omega)
  have hy1 : 1 < y := by
    dsimp only [y]
    exact_mod_cast (show 1 < ⌊x⌋₊ by omega)
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hxpos : 0 < x := hypos.trans_le (Nat.floor_le hx)
  have hlog := mul_le_mul_of_nonneg_left (log_anchor_le hx hy)
    (by linarith : 0 ≤ 1 + η)
  have hsmall : (1 + η) / y ≤ 2 / y :=
    div_le_div_of_nonneg_right (by linarith) hypos.le
  have hexponent : (1 + η) * Real.log x ≤
      (1 + roundedBandWidth ⌊x⌋₊ η) * Real.log y := by
    have heq : (1 + roundedBandWidth ⌊x⌋₊ η) * Real.log y =
        (1 + η) * Real.log y + 2 / y := by
      unfold roundedBandWidth
      change (1 + (η + 2 / (y * Real.log y))) * Real.log y = _
      field_simp [hypos.ne', hlogy.ne'] <;> ring
    rw [heq]
    change (1 + η) * Real.log x ≤ _
    change (1 + η) * Real.log x ≤ (1 + η) * (Real.log y + 1 / y) at hlog
    rw [mul_add, mul_one_div] at hlog
    linarith
  rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hypos]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using hexponent

theorem upper_floor_le_powerBandUpper {x η : ℝ}
    (hx : 0 ≤ x) (hy : 2 ≤ ⌊x⌋₊) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ⌊x ^ (1 + η)⌋₊ ≤ powerBandUpper ⌊x⌋₊ (roundedBandWidth ⌊x⌋₊ η) :=
  Nat.floor_le_floor (upper_power_le_rounded_power hx hy hη0 hη1)

theorem roundedBandWidth_admissible {y : ℕ} {η : ℝ}
    (hy : 16 ≤ y) (hη0 : 0 ≤ η) (hη : η * Real.log (y : ℝ) ≤ 1 / 8) :
    0 ≤ roundedBandWidth y η ∧
      roundedBandWidth y η * Real.log (y : ℝ) ≤ 1 / 4 := by
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (show 0 < y by omega)
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hy1
  have hinv : 2 / (y : ℝ) ≤ 1 / 8 := by
    apply (div_le_iff₀ hypos).2
    have hh : (16 : ℝ) ≤ y := Nat.cast_le.mpr hy
    linarith
  constructor
  · unfold roundedBandWidth
    exact add_nonneg hη0 (div_nonneg (by norm_num) (mul_pos hypos hlogy).le)
  · have heq : roundedBandWidth y η * Real.log (y : ℝ) =
        η * Real.log (y : ℝ) + 2 / (y : ℝ) := by
      unfold roundedBandWidth
      field_simp [hypos.ne', hlogy.ne'] <;> ring
    rw [heq]
    linarith

end
end PrimeGapNormality.Prime.CoreRoughRealAnchorBound
