import PrimeGapNormality.Prime.CoreFibreImageAC
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The finite polynomial-image reference measure

The parameter law may correlate the outer phase, the polynomial coefficients,
and the available insertion length. The reference measure is the actual image
of the region `0 < z < W a`, not a probability normalization of that image.
Its mass is exactly the first length moment. Absolute continuity follows from
nonconstancy almost everywhere, without a bounded-density assertion.
-/

namespace PrimeGapNormality.Prime.CorePolynomialReference

open MeasureTheory Set Filter
open scoped Polynomial ENNReal BoundedContinuousFunction

noncomputable section

variable {α : Type*} [MeasurableSpace α]

abbrev Circle := AddCircle (1 : ℝ)

def insertionDomain (W : α → ℝ) : Set (α × ℝ) :=
  {z | 0 < z.2 ∧ z.2 < W z.1}

def circleEval (P : α → ℝ[X]) (z : α × ℝ) : Circle :=
  (((P z.1).eval z.2 : ℝ) : Circle)

def referenceMeasure (Λ : Measure α) (W : α → ℝ) (P : α → ℝ[X]) :
    Measure Circle :=
  Measure.map (circleEval P) ((Λ.prod volume).restrict (insertionDomain W))

theorem measurableSet_insertionDomain {W : α → ℝ} (hW : Measurable W) :
    MeasurableSet (insertionDomain W) :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (hW.comp measurable_fst))

/-- Tonelli computes the mass of the actual variable-length insertion region.
For negative lengths the fibre is empty, as reflected by `ofReal`. -/
theorem insertionDomain_mass (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) :
    Λ.prod volume (insertionDomain W) = ∫⁻ a, ENNReal.ofReal (W a) ∂Λ := by
  rw [Measure.prod_apply (measurableSet_insertionDomain hW)]
  apply lintegral_congr
  intro a
  change (volume : Measure ℝ) (Ioo 0 (W a)) = ENNReal.ofReal (W a)
  rw [Real.volume_Ioo, sub_zero]

/-- Exact reference mass; no finiteness premise is used in this equality. -/
theorem referenceMeasure_mass (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (P : α → ℝ[X]) (hP : Measurable (circleEval P)) :
    referenceMeasure Λ W P univ = ∫⁻ a, ENNReal.ofReal (W a) ∂Λ := by
  rw [referenceMeasure, Measure.map_apply hP MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, insertionDomain_mass Λ hW]

/-- A finite first length moment proves finiteness of the reference measure. -/
theorem referenceMeasure_isFinite (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (P : α → ℝ[X]) (hP : Measurable (circleEval P))
    (hfinite : (∫⁻ a, ENNReal.ofReal (W a) ∂Λ) < ∞) :
    IsFiniteMeasure (referenceMeasure Λ W P) :=
  ⟨by rw [referenceMeasure_mass Λ hW P hP]; exact hfinite⟩

/-- Ordinary-integral form for a nonnegative integrable insertion length. -/
theorem referenceMeasure_mass_eq_integral (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a) (hWi : Integrable W Λ)
    (P : α → ℝ[X]) (hP : Measurable (circleEval P)) :
    referenceMeasure Λ W P univ = ENNReal.ofReal (∫ a, W a ∂Λ) := by
  rw [referenceMeasure_mass Λ hW P hP,
    ← ofReal_integral_eq_lintegral_ofReal hWi hW0]

theorem referenceMeasure_isFinite_of_integrable (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a) (hWi : Integrable W Λ)
    (P : α → ℝ[X]) (hP : Measurable (circleEval P)) :
    IsFiniteMeasure (referenceMeasure Λ W P) :=
  ⟨by rw [referenceMeasure_mass_eq_integral Λ hW hW0 hWi P hP]
      exact ENNReal.ofReal_lt_top⟩

theorem referenceMeasure_mass_le (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a) (hWi : Integrable W Λ)
    (P : α → ℝ[X]) (hP : Measurable (circleEval P))
    {M : ℝ} (hM : ∫ a, W a ∂Λ ≤ M) :
    referenceMeasure Λ W P univ ≤ ENNReal.ofReal M := by
  rw [referenceMeasure_mass_eq_integral Λ hW hW0 hWi P hP]
  exact ENNReal.ofReal_le_ofReal hM

/-- Null critical fibres may be discarded under the parameter law. No
independence of the coefficients, phase, or length is required. -/
theorem referenceMeasure_absolutelyContinuous
    (Λ : Measure α) (W : α → ℝ) (P : α → ℝ[X])
    (hP : Measurable (circleEval P))
    (hnonconstant : ∀ᵐ a ∂Λ, 0 < (P a).natDegree) :
    referenceMeasure Λ W P ≪ (volume : Measure Circle) :=
  CoreFibreImage.polynomial_circle_mixture_absolutelyContinuous
    Λ P hP hnonconstant (insertionDomain W)

/-- Fubini for the actual reference measure. The finite first moment is used
to prove integrability of the bounded test on the restricted product. -/
theorem integral_referenceMeasure
    (Λ : Measure α) [SFinite Λ] {W : α → ℝ} (hW : Measurable W)
    (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a)
    (hfinite : (∫⁻ a, ENNReal.ofReal (W a) ∂Λ) < ∞)
    (P : α → ℝ[X]) (hP : Measurable (circleEval P))
    (f : Circle →ᵇ ℝ) :
    (∫ x, f x ∂referenceMeasure Λ W P) =
      ∫ a, (∫ z in (0 : ℝ)..W a, f (((P a).eval z : ℝ) : Circle)) ∂Λ := by
  letI : IsFiniteMeasure (referenceMeasure Λ W P) :=
    referenceMeasure_isFinite Λ hW P hP hfinite
  have hf : Integrable f (referenceMeasure Λ W P) := f.integrable _
  have hcomp : Integrable (fun z => f (circleEval P z))
      ((Λ.prod volume).restrict (insertionDomain W)) :=
    hf.comp_aemeasurable hP.aemeasurable
  have hind : Integrable
      ((insertionDomain W).indicator (fun z => f (circleEval P z)))
      (Λ.prod volume) :=
    (integrable_indicator_iff (measurableSet_insertionDomain hW)).2 hcomp
  rw [referenceMeasure,
    integral_map_of_stronglyMeasurable hP f.continuous.stronglyMeasurable,
    ← integral_indicator (measurableSet_insertionDomain hW), integral_prod _ hind]
  apply integral_congr_ae
  filter_upwards [hW0] with a ha
  change (∫ z, (Ioo 0 (W a)).indicator
      (fun z => f (((P a).eval z : ℝ) : Circle)) z) = _
  rw [integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le ha,
    integral_Ioc_eq_integral_Ioo]

/-- Convenient ordinary first-moment version for a joint probability law
(and, in fact, for any s-finite parameter measure). -/
theorem integral_referenceMeasure_of_integrable
    (Λ : Measure α) [SFinite Λ] {W : α → ℝ} (hW : Measurable W)
    (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a) (hWi : Integrable W Λ)
    (P : α → ℝ[X]) (hP : Measurable (circleEval P)) (f : Circle →ᵇ ℝ) :
    (∫ x, f x ∂referenceMeasure Λ W P) =
      ∫ a, (∫ z in (0 : ℝ)..W a, f (((P a).eval z : ℝ) : Circle)) ∂Λ := by
  apply integral_referenceMeasure Λ hW hW0 _ P hP f
  rw [← ofReal_integral_eq_lintegral_ofReal hWi hW0]
  exact ENNReal.ofReal_lt_top

end

end PrimeGapNormality.Prime.CorePolynomialReference
