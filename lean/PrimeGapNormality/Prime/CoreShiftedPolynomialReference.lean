import PrimeGapNormality.Prime.CorePolynomialReferenceMeasure

/-! The polynomial-image reference measure with a genuinely circle-valued
outer phase. A representative is used only to reuse the polynomial algebra;
its circle evaluation is exactly the original phase, so no continuity of a
real lift is assumed. -/

namespace PrimeGapNormality.Prime.CoreShiftedPolynomialReference
open MeasureTheory Set Filter
open scoped Polynomial ENNReal BoundedContinuousFunction
noncomputable section
variable {α : Type*} [MeasurableSpace α]
abbrev Circle := AddCircle (1 : ℝ)

def phasePolynomial (O : α → Circle) (θ : α → ℝ) (P : α → ℝ[X])
    (a : α) : ℝ[X] :=
  Polynomial.C ((AddCircle.equivIco (1 : ℝ) 0 (O a) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ) +
    Polynomial.C (θ a) * P a

@[simp] theorem phasePolynomial_circleEval
    (O : α → Circle) (θ : α → ℝ) (P : α → ℝ[X]) (a : α) (t : ℝ) :
    (((phasePolynomial O θ P a).eval t : ℝ) : Circle) =
      O a + ((θ a * (P a).eval t : ℝ) : Circle) := by
  simp only [phasePolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, AddCircle.coe_add, AddCircle.coe_equivIco]

theorem phasePolynomial_natDegree (O : α → Circle) (θ : α → ℝ)
    (P : α → ℝ[X]) (a : α) (hθ : θ a ≠ 0) :
    (phasePolynomial O θ P a).natDegree = (P a).natDegree := by
  unfold phasePolynomial
  rw [add_comm, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul hθ]

def referenceMeasure (Λ : Measure α) (W : α → ℝ) (O : α → Circle)
    (θ : α → ℝ) (P : α → ℝ[X]) : Measure Circle :=
  CorePolynomialReference.referenceMeasure Λ W (phasePolynomial O θ P)

theorem measurable_circleEval (O : α → Circle) (θ : α → ℝ) (P : α → ℝ[X])
    (hO : Measurable O) (hθ : Measurable θ)
    (hP : Measurable (fun z : α × ℝ ↦ (P z.1).eval z.2)) :
    Measurable (CorePolynomialReference.circleEval (phasePolynomial O θ P)) := by
  have h : CorePolynomialReference.circleEval (phasePolynomial O θ P) =
      fun z : α × ℝ ↦ O z.1 + ((θ z.1 * (P z.1).eval z.2 : ℝ) : Circle) := by
    funext z
    exact phasePolynomial_circleEval O θ P z.1 z.2
  rw [h]
  exact (hO.comp measurable_fst).add
    (AddCircle.measurable_mk'.comp ((hθ.comp measurable_fst).mul hP))

theorem referenceMeasure_mass (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (O : α → Circle) (θ : α → ℝ) (P : α → ℝ[X])
    (hO : Measurable O) (hθ : Measurable θ)
    (hP : Measurable (fun z : α × ℝ ↦ (P z.1).eval z.2)) :
    referenceMeasure Λ W O θ P univ = ∫⁻ a, ENNReal.ofReal (W a) ∂Λ :=
  CorePolynomialReference.referenceMeasure_mass Λ hW (phasePolynomial O θ P)
    (measurable_circleEval O θ P hO hθ hP)

theorem referenceMeasure_isFinite (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (O : α → Circle) (θ : α → ℝ) (P : α → ℝ[X])
    (hO : Measurable O) (hθ : Measurable θ)
    (hP : Measurable (fun z : α × ℝ ↦ (P z.1).eval z.2))
    (hfinite : (∫⁻ a, ENNReal.ofReal (W a) ∂Λ) < ∞) :
    IsFiniteMeasure (referenceMeasure Λ W O θ P) :=
  CorePolynomialReference.referenceMeasure_isFinite Λ hW (phasePolynomial O θ P)
    (measurable_circleEval O θ P hO hθ hP) hfinite

theorem referenceMeasure_absolutelyContinuous
    (Λ : Measure α) (W : α → ℝ) (O : α → Circle)
    (θ : α → ℝ) (P : α → ℝ[X])
    (hO : Measurable O) (hθ : Measurable θ)
    (hP : Measurable (fun z : α × ℝ ↦ (P z.1).eval z.2))
    (hnonconstant : ∀ᵐ a ∂Λ, 0 < (P a).natDegree)
    (hθ0 : ∀ᵐ a ∂Λ, θ a ≠ 0) :
    referenceMeasure Λ W O θ P ≪ (volume : Measure Circle) := by
  apply CorePolynomialReference.referenceMeasure_absolutelyContinuous Λ W
    (phasePolynomial O θ P) (measurable_circleEval O θ P hO hθ hP)
  filter_upwards [hnonconstant, hθ0] with a ha ht
  rw [phasePolynomial_natDegree O θ P a ht]
  exact ha

theorem integral_referenceMeasure
    (Λ : Measure α) [SFinite Λ] {W : α → ℝ} (hW : Measurable W)
    (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a)
    (hfinite : (∫⁻ a, ENNReal.ofReal (W a) ∂Λ) < ∞)
    (O : α → Circle) (θ : α → ℝ) (P : α → ℝ[X])
    (hO : Measurable O) (hθ : Measurable θ)
    (hP : Measurable (fun z : α × ℝ ↦ (P z.1).eval z.2))
    (f : Circle →ᵇ ℝ) :
    (∫ x, f x ∂referenceMeasure Λ W O θ P) =
      ∫ a, (∫ t in (0 : ℝ)..W a, f (O a + ((θ a * (P a).eval t : ℝ) : Circle))) ∂Λ := by
  have h := CorePolynomialReference.integral_referenceMeasure Λ hW hW0 hfinite
    (phasePolynomial O θ P) (measurable_circleEval O θ P hO hθ hP) f
  simpa only [referenceMeasure, phasePolynomial_circleEval] using h

end
end PrimeGapNormality.Prime.CoreShiftedPolynomialReference
