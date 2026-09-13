import PrimeGapNormality.Prime.CoreDigitalWindowConvergence
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Fin

/-! Actual empirical orbit probabilities. The zero-length convention is a
Dirac mass; the integral/average identity is stated only at positive length. -/

open MeasureTheory Filter Finset
open scoped Topology ENNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

noncomputable def coreDigitalWindowMeasure
    (u : ℕ → AddCircle (1 : ℝ)) (a N : ℕ) :
    ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  if h : 0 < N then
    letI : Nonempty (Fin N) := ⟨⟨0, h⟩⟩
    ⟨((PMF.uniformOfFintype (Fin N)).map (fun i : Fin N => u (a + (i : ℕ)))).toMeasure,
      inferInstance⟩
  else ⟨(PMF.pure (u a)).toMeasure, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
theorem coreDigitalWindowMeasure_integral
    (u : ℕ → AddCircle (1 : ℝ)) (a : ℕ) {N : ℕ} (hN : 0 < N)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) :
    (∫ x, f x ∂(coreDigitalWindowMeasure u a N : Measure (AddCircle (1 : ℝ)))) =
      coreDigitalWindowAverage u f a N := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hm : Measurable (fun i : Fin N => u (a + i)) := measurable_of_finite _
  have hmeasure :
      (coreDigitalWindowMeasure u a N : Measure (AddCircle (1 : ℝ))) =
        ((PMF.uniformOfFintype (Fin N)).map (fun i : Fin N => u (a + (i : ℕ)))).toMeasure := by
    unfold coreDigitalWindowMeasure
    rw [dif_pos hN]
    rfl
  rw [hmeasure, ← PMF.toMeasure_map (fun i : Fin N => u (a + (i : ℕ)))
      (PMF.uniformOfFintype (Fin N)) hm, integral_map hm.aemeasurable
    f.continuous.aestronglyMeasurable, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, ← Finset.mul_sum]
  have hs := Fin.sum_univ_eq_sum_range (fun j : ℕ => f (u (a + j))) N
  rw [hs]
  unfold coreDigitalWindowAverage
  rw [div_eq_mul_inv, mul_comm]

/-- The abstract probability-measure supplier in the compactness theorem is
now discharged by the actual uniform window measure. -/
theorem coreDigital_growing_window_tests_tendsto
    {C : ℕ} (hC : 2 ≤ C)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hNpos : ∀ j, 0 < N j)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * ∫ x, f x ∂volume + ε)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) :
    Tendsto (fun j => coreDigitalWindowAverage u f (a j) (N j)) atTop
      (𝓝 (∫ x, f x ∂volume)) :=
  coreDigital_window_tests_tendsto_volume hC u hu a N hN
    (fun j => coreDigitalWindowMeasure u (a j) (N j))
    (fun j f => coreDigitalWindowMeasure_integral u (a j) (hNpos j) f)
    hA hbound f

end PrimeGapNormality.Prime
