import PrimeGapNormality.Prime.CoreDigitalPeriodic

/-!
Polynomial images need not have bounded density at critical values. The
shared digital consumer therefore permits an arbitrary fixed finite
absolutely continuous reference measure, not just a bounded multiple of
circle volume. Its choice precedes every test and accuracy parameter.
-/

open MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

/-- A genuine periodic weak window limit dominated in positive tests by a
fixed finite AC reference measure is Lebesgue measure. The reference may
be a mixed polynomial interval image with unbounded density. -/
theorem coreDigitalPeriodic_window_limit_eq_volume_of_reference_bounds
    {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hlim : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a j) (N j)) atTop
        (nhds (∫ x, f x ∂μ)))
    (σ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure σ]
    (hσ : σ ≪ volume) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤
          A * (∫ x, f x ∂σ) + ε) :
    μ = volume := by
  have hle : μ ≤ ENNReal.ofReal A • σ := by
    letI : IsFiniteMeasure (ENNReal.ofReal A • σ) :=
      Measure.smul_finite σ ENNReal.ofReal_ne_top
    apply coreDigital_measure_le_of_positive_lipschitz_tests
    intro f K hK hf
    rw [integral_smul_measure, ENNReal.toReal_ofReal hA, smul_eq_mul]
    apply le_of_forall_pos_le_add
    intro ε hε
    exact le_of_tendsto (hlim f) (hbound f K hK hf ε hε)
  have hμσ : μ ≪ σ :=
    Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal A) hle
  exact coreDigitalPeriodic_window_limit_eq_volume hC hk u hu a N hN μ hlim
    (hμσ.trans hσ)

end PrimeGapNormality.Prime
