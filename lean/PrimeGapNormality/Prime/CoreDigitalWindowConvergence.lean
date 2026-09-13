import PrimeGapNormality.Prime.CoreDigitalLimitDomination
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

/-! Compactness closes the invariant-limit argument for genuine empirical
window measures. The integral identity explicitly identifies those measures;
positive-test domination is still the upstream analytic/arithmetic obligation. -/

open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

local instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp⟩

noncomputable def coreCircleVolume : ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  ⟨volume, inferInstance⟩

theorem coreDigital_window_measures_tendsto_volume
    {C : ℕ} (hC : 2 ≤ C)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ℕ → ProbabilityMeasure (AddCircle (1 : ℝ)))
    (hμ : ∀ j (f : AddCircle (1 : ℝ) →ᵇ ℝ),
      (∫ x, f x ∂(μ j : Measure (AddCircle (1 : ℝ)))) =
        coreDigitalWindowAverage u f (a j) (N j))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * ∫ x, f x ∂volume + ε) :
    Tendsto μ atTop (𝓝 coreCircleVolume) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro ν hν
  obtain ⟨φ, hφ, hlim⟩ := hν.tendsto_subseq
  have htest : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a (φ j)) (N (φ j)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure (AddCircle (1 : ℝ))))) := by
    intro f
    have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
    simpa only [Function.comp_apply, hμ] using ht
  have heq := coreDigital_window_limit_eq_volume_of_positive_bounds hC u hu
    (a ∘ φ) (N ∘ φ) (hN.comp hφ.tendsto_atTop)
    (ν : Measure (AddCircle (1 : ℝ))) htest hA
    (fun f hf ε hε => hφ.tendsto_atTop.eventually (hbound f hf ε hε))
  exact Subtype.ext heq

theorem coreDigital_window_tests_tendsto_volume
    {C : ℕ} (hC : 2 ≤ C)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ℕ → ProbabilityMeasure (AddCircle (1 : ℝ)))
    (hμ : ∀ j (f : AddCircle (1 : ℝ) →ᵇ ℝ),
      (∫ x, f x ∂(μ j : Measure (AddCircle (1 : ℝ)))) =
        coreDigitalWindowAverage u f (a j) (N j))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * ∫ x, f x ∂volume + ε)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) :
    Tendsto (fun j => coreDigitalWindowAverage u f (a j) (N j)) atTop
      (𝓝 (∫ x, f x ∂volume)) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (coreDigital_window_measures_tendsto_volume hC u hu a N hN μ hμ hA hbound) f
  have hc : (coreCircleVolume : Measure (AddCircle (1 : ℝ))) = volume := rfl
  simpa only [hμ, hc] using h

end PrimeGapNormality.Prime
