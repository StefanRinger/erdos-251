import PrimeGapNormality.Prime.CoreDigitalRigidity
import Mathlib.MeasureTheory.Integral.Regular

/-! Passing actual positive-test bounds to the measure order, then using
the existing exact-recurrence rigidity. No arithmetic domination is assumed
implicitly: the eventual finite-test bound is displayed as the input. -/

open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

local instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp⟩

theorem coreDigital_measure_le_of_positive_tests
    (μ ν : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (htest : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν) : μ ≤ ν := by
  have hcompact : ∀ K : Set (AddCircle (1 : ℝ)), IsCompact K → μ K ≤ ν K := by
    intro K hK
    rw [hK.measure_eq_biInf_integral_hasCompactSupport μ,
      hK.measure_eq_biInf_integral_hasCompactSupport ν]
    apply iInf_mono
    intro f
    apply iInf_mono
    intro hf
    apply iInf_mono
    intro _
    apply iInf_mono
    intro _
    apply iInf_mono
    intro hf0
    exact ENNReal.ofReal_le_ofReal
      (htest (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩) hf0)
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isCompact μ]
  apply iSup_le
  intro K
  apply iSup_le
  intro hKs
  apply iSup_le
  intro hK
  exact (hcompact K hK).trans (measure_mono hKs)

theorem coreDigital_measure_le_smul_of_positive_tests
    (μ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure μ] {A : ℝ} (hA : 0 ≤ A)
    (htest : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ A * ∫ x, f x ∂volume) :
    μ ≤ ENNReal.ofReal A • volume := by
  letI : IsFiniteMeasure (ENNReal.ofReal A •
      (volume : Measure (AddCircle (1 : ℝ)))) :=
    ⟨by simp [Measure.smul_apply]⟩
  apply coreDigital_measure_le_of_positive_tests
  intro f hf
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal hA, smul_eq_mul]
    using htest f hf

theorem coreDigital_window_limit_eq_volume_of_positive_bounds
    {C : ℕ} (hC : 2 ≤ C)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hlim : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a j) (N j)) atTop
        (𝓝 (∫ x, f x ∂μ)))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * ∫ x, f x ∂volume + ε) :
    μ = volume := by
  apply coreDigital_window_limit_eq_volume hC u hu a N hN μ hlim
  apply Measure.absolutelyContinuous_of_le_smul
  apply coreDigital_measure_le_smul_of_positive_tests μ hA
  intro f hf
  apply le_of_forall_pos_le_add
  intro ε hε
  exact le_of_tendsto (hlim f) (hbound f hf ε hε)

end PrimeGapNormality.Prime
