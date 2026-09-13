import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
An elementary diameter bound implies Lebesgue domination of a finite-
dimensional frame law. Mathlib's exact identification of Hausdorff and
Lebesgue measures for the sup-norm product avoids adding a separate
Carathéodory/rectangle extension engine. The application must still derive
the diameter bound from the actual finite frame counting estimates.
-/

namespace PrimeGapNormality.Prime.CoreFrameMeasureDomination

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A uniform local diameter estimate yields actual measure domination.
The hypothesis only concerns sets of diameter at most one. -/
theorem le_volume_of_diameter_bound {n : ℕ}
    (μ : Measure (Fin n → ℝ)) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ s : Set (Fin n → ℝ), Metric.ediam s ≤ 1 →
      μ s ≤ ENNReal.ofReal C * Metric.ediam s ^ (n : ℝ)) :
    μ ≤ ENNReal.ofReal C • (volume : Measure (Fin n → ℝ)) := by
  let c := ENNReal.ofReal C
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsmall : c⁻¹ • μ ≤
      (Measure.hausdorffMeasure (n : ℝ) : Measure (Fin n → ℝ)) := by
    apply Measure.le_hausdorffMeasure (n : ℝ) (c⁻¹ • μ) 1 zero_lt_one
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul]
    calc
      c⁻¹ * μ s ≤ c⁻¹ * (c * Metric.ediam s ^ (n : ℝ)) :=
        mul_le_mul' le_rfl (hbound s hs)
      _ = Metric.ediam s ^ (n : ℝ) := ENNReal.inv_mul_cancel_left hc0 hct
  have hsmall' : c⁻¹ • μ ≤ (volume : Measure (Fin n → ℝ)) := by
    have hhaus : (Measure.hausdorffMeasure (n : ℝ) : Measure (Fin n → ℝ)) = volume := by
      simpa only [Fintype.card_fin] using
        (MeasureTheory.hausdorffMeasure_pi_real (ι := Fin n))
    rwa [hhaus] at hsmall
  apply Measure.le_iff'.mpr
  intro s
  have hs := Measure.le_iff'.mp hsmall' s
  rw [Measure.smul_apply, smul_eq_mul] at hs
  rw [Measure.smul_apply, smul_eq_mul]
  calc
    μ s = c * (c⁻¹ * μ s) := (ENNReal.mul_inv_cancel_left hc0 hct).symm
    _ ≤ c * volume s := mul_le_mul' le_rfl hs

theorem absolutelyContinuous_of_diameter_bound {n : ℕ}
    (μ : Measure (Fin n → ℝ)) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ s : Set (Fin n → ℝ), Metric.ediam s ≤ 1 →
      μ s ≤ ENNReal.ofReal C * Metric.ediam s ^ (n : ℝ)) :
    μ ≪ volume :=
  Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal C)
    (le_volume_of_diameter_bound μ hC hbound)

end

end PrimeGapNormality.Prime.CoreFrameMeasureDomination
