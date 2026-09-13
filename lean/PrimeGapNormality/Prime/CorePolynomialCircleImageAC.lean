import PrimeGapNormality.Prime.CorePolynomialImageAC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
Polynomial images on the actual unit circle. Folding full Lebesgue measure
to the circle is absolutely continuous but is not asserted to be finite.
The fundamental-domain theorem handles the countably many translates.
-/

namespace PrimeGapNormality.Prime.CorePolynomialImage

open Set MeasureTheory
open scoped Polynomial

noncomputable section

theorem circle_projection_absolutelyContinuous :
    Measure.map (fun x : ℝ ↦ (x : AddCircle (1 : ℝ))) volume ≪
      (volume : Measure (AddCircle (1 : ℝ))) := by
  have hfund := isAddFundamentalDomain_Ioc' (by norm_num : (0 : ℝ) < 1) 0 volume
  have h := hfund.absolutelyContinuous_map
  change Measure.map (fun x : ℝ ↦ (x : AddCircle (1 : ℝ))) volume ≪
    Measure.map (fun x : ℝ ↦ (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ioc 0 (0 + 1))) at h
  rw [(AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq] at h
  exact h

theorem map_circle_restrict_absolutelyContinuous (P : ℝ[X])
    (hP : 0 < P.natDegree) (I : Set ℝ) :
    Measure.map (fun x : ℝ ↦ ((P.eval x : ℝ) : AddCircle (1 : ℝ)))
      (volume.restrict I) ≪ (volume : Measure (AddCircle (1 : ℝ))) := by
  have hcoe : Measurable (fun x : ℝ ↦ (x : AddCircle (1 : ℝ))) :=
    AddCircle.measurable_mk'
  have h := ((map_restrict_absolutelyContinuous P hP I).map hcoe).trans
    circle_projection_absolutelyContinuous
  rw [Measure.map_map hcoe P.continuous.measurable] at h
  exact h

/-- The scalar interval-image ingredient of the paper, modulo one. -/
theorem map_circle_interval_absolutelyContinuous (P : ℝ[X])
    (hP : 0 < P.natDegree) (a b : ℝ) :
    Measure.map (fun x : ℝ ↦ ((P.eval x : ℝ) : AddCircle (1 : ℝ)))
      (volume.restrict (Icc a b)) ≪ (volume : Measure (AddCircle (1 : ℝ))) :=
  map_circle_restrict_absolutelyContinuous P hP (Icc a b)

theorem map_circle_interval_absolutelyContinuous_of_nonconstant (P : ℝ[X])
    (hP : ∀ c : ℝ, P ≠ Polynomial.C c) (a b : ℝ) :
    Measure.map (fun x : ℝ ↦ ((P.eval x : ℝ) : AddCircle (1 : ℝ)))
      (volume.restrict (Icc a b)) ≪ (volume : Measure (AddCircle (1 : ℝ))) := by
  apply map_circle_interval_absolutelyContinuous
  by_contra hdeg
  exact hP (P.coeff 0) (Polynomial.eq_C_of_natDegree_eq_zero (by omega))

end

end PrimeGapNormality.Prime.CorePolynomialImage
