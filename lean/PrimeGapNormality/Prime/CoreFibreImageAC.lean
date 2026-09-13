import PrimeGapNormality.Prime.CorePolynomialCircleImageAC
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Absolute continuity survives mixing one-variable polynomial images

This is the measure-theoretic part of the local-polynomial model argument.
The outer phase and the remaining frame may be arbitrarily correlated.
Only the conditional inserted-coordinate image needs to be absolutely
continuous. Neither independence of the outer phase nor bounded density
near critical polynomial values is assumed.
-/

namespace PrimeGapNormality.Prime.CoreFibreImage

open MeasureTheory Set Filter
open scoped Polynomial

noncomputable section

/-- Mixing absolutely continuous measurable fibre images preserves absolute
continuity. This null-set argument needs no probability normalization. -/
theorem map_prod_absolutelyContinuous
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (τ : Measure γ) (F : α × β → γ)
    (hF : Measurable F)
    (hfibre : ∀ᵐ a ∂μ, Measure.map (fun t => F (a, t)) ν ≪ τ) :
    Measure.map F (μ.prod ν) ≪ τ := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [Measure.map_apply hF hs]
  apply Measure.measure_prod_null_of_ae_null (hs.preimage hF)
  filter_upwards [hfibre] with a ha
  have hzero := ha hs0
  have hFa : Measurable (fun t : β => F (a, t)) :=
    hF.comp (measurable_prodMk_left (x := a))
  rw [Measure.map_apply hFa hs] at hzero
  exact hzero

/-- In particular, arbitrary measurable restrictions of the frame/insertion
domain retain absolute continuity. -/
theorem map_restrict_prod_absolutelyContinuous
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (τ : Measure γ) (F : α × β → γ)
    (hF : Measurable F)
    (hfibre : ∀ᵐ a ∂μ, Measure.map (fun t => F (a, t)) ν ≪ τ)
    (D : Set (α × β)) :
    Measure.map F ((μ.prod ν).restrict D) ≪ τ :=
  (Measure.map_mono Measure.restrict_le_self hF).absolutelyContinuous.trans
    (map_prod_absolutelyContinuous μ ν τ F hF hfibre)

/-- A jointly measurable family of nonconstant real polynomials, reduced
modulo one, gives an absolutely continuous mixed image on every restricted
domain. Constants in each polynomial can encode an arbitrary outer phase. -/
theorem polynomial_circle_mixture_absolutelyContinuous
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (P : α → ℝ[X])
    (hF : Measurable (fun z : α × ℝ => (((P z.1).eval z.2 : ℝ) : AddCircle (1 : ℝ))))
    (hP : ∀ᵐ a ∂μ, 0 < (P a).natDegree)
    (D : Set (α × ℝ)) :
    Measure.map (fun z : α × ℝ => (((P z.1).eval z.2 : ℝ) : AddCircle (1 : ℝ)))
      ((μ.prod volume).restrict D) ≪ (volume : Measure (AddCircle (1 : ℝ))) := by
  apply map_restrict_prod_absolutelyContinuous μ volume volume _ hF _ D
  filter_upwards [hP] with a ha
  simpa only [Measure.restrict_univ] using
    CorePolynomialImage.map_circle_restrict_absolutelyContinuous (P a) ha Set.univ

end

end PrimeGapNormality.Prime.CoreFibreImage
