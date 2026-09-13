import PrimeGapNormality.Prime.CoreRoughLogSlopeProfile
import PrimeGapNormality.Prime.CoreRoughPositionEnd

/-!
# Explicit logarithmic-slope specialization of the rough position theorem

The sufficient constant is deliberately conservative. This is a vanishing
exponent c/log log n, not an unconditional fixed positive power theorem.
The infinite position sum is the actual enumeration of the given cutoff.
-/

namespace PrimeGapNormality.Prime.CoreRoughForumThreshold

open CoreMovingRoughSequence CoreRoughThreshold CoreRoughLogSlopeProfile
  CoreRoughPositionEnd
noncomputable section

def cutoff (c : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (c / Real.log (Real.log (n : ℝ)))⌋₊

def series (c : ℝ) (B : ℕ) : ℝ :=
  ∑' n : ℕ, (movingRoughSequence (cutoff c) n : ℝ) / (B : ℝ) ^ (n + 1)

theorem cutoff_eq (c : ℝ) : cutoff c = zPsi (profile c) := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [cutoff, zPsi, profile]
  · exact (zPsi_eq_rpow_cutoff c (Nat.pos_of_ne_zero hn)).symm

theorem series_eq (c : ℝ) (B : ℕ) :
    series c B = movingRoughPositionSeries (profile c) B := by
  simp only [series, cutoff_eq, movingRoughPositionSeries, sequencePositionSeries]

theorem normal_and_irrational {B : ℕ} (hB : 2 ≤ B) {c : ℝ} (hc : 0 < c)
    (hsmall : 1000000 * c ≤ Real.log (B : ℝ)) :
    PrimeGapNormality.BFree.IsNormal B (series c B) ∧ Irrational (series c B) := by
  have hlog : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  let κ : ℝ := 1 / Real.log (B : ℝ)
  have hκ : 0 < κ := div_pos (by norm_num) hlog
  have hA : 0 < 1000000 * κ := mul_pos (by norm_num) hκ
  have hAc : (1000000 * κ) * c ≤ 1 := by
    have hh : (1000000 * c) / Real.log (B : ℝ) ≤ 1 :=
      (div_le_one hlog).mpr hsmall
    simpa only [κ, div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using hh
  have hSlope := hasSlopeBudget hc hA hAc
  have hreg := weightedDerivative hc
  rw [series_eq]
  exact ⟨movingRoughPositionSeries_normal hκ hSlope (by norm_num) hreg hB le_rfl,
    movingRoughPositionSeries_irrational hκ hSlope (by norm_num) hreg hB le_rfl⟩

/-- Every fixed integer base has a concrete positive allowable slope. -/
theorem exists_positive_slope {B : ℕ} (hB : 2 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ PrimeGapNormality.BFree.IsNormal B (series c B) ∧
      Irrational (series c B) := by
  have hlog : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  let c := Real.log (B : ℝ) / 1000000
  have hc : 0 < c := div_pos hlog (by norm_num)
  refine ⟨c, hc, normal_and_irrational hB hc ?_⟩
  dsimp only [c]
  nlinarith

end
end PrimeGapNormality.Prime.CoreRoughForumThreshold
