import PrimeGapNormality.Prime.CoreDigitalCharacterMean
import Mathlib.Topology.MetricSpace.ThickenedIndicator

/-! The actual Selberg consumer need only control positive Lipschitz tests.
Thickened closed-set indicators turn those bounds into measure domination;
no extra smoothness or Lipschitz approximation hypothesis is imported. -/

open MeasureTheory Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

local instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp⟩

theorem coreDigital_measure_le_of_positive_lipschitz_tests
    (μ ν : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (htest : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
        (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν) : μ ≤ ν := by
  have hclosed : ∀ F : Set (AddCircle (1 : ℝ)), IsClosed F → μ F ≤ ν F := by
    intro F hF
    let δ : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
    have hδ : ∀ n, 0 < δ n := fun n => Nat.one_div_pos_of_nat
    have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hμ := tendsto_integral_thickenedIndicator_of_isClosed μ hF hδ hδlim
    have hν := tendsto_integral_thickenedIndicator_of_isClosed ν hF hδ hδlim
    have hreal : μ.real F ≤ ν.real F := by
      apply le_of_tendsto_of_tendsto' hμ hν
      intro n
      let f : AddCircle (1 : ℝ) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
        ⟨fun x => (thickenedIndicator (hδ n) F x : ℝ), by fun_prop⟩
      have hLip : LipschitzWith (δ n).toNNReal⁻¹ f := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        exact (lipschitzWith_thickenedIndicator (hδ n) F).dist_le_mul x y
      exact htest f _ hLip (fun x => (thickenedIndicator (hδ n) F x).coe_nonneg)
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ F) (measure_ne_top ν F)).mp hreal
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isCompact μ]
  apply iSup_le
  intro F
  apply iSup_le
  intro hFs
  apply iSup_le
  intro hF
  exact (hclosed F hF.isClosed).trans (measure_mono hFs)

theorem coreDigital_window_limit_eq_volume_of_lipschitz_bounds
    {C : ℕ} (hC : 2 ≤ C)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hlim : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a j) (N j)) atTop
        (𝓝 (∫ x, f x ∂μ)))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * ∫ x, f x ∂volume + ε) :
    μ = volume := by
  apply coreDigital_window_limit_eq_volume hC u hu a N hN μ hlim
  apply Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal A)
  letI : IsFiniteMeasure (ENNReal.ofReal A •
      (volume : Measure (AddCircle (1 : ℝ)))) := ⟨by simp [Measure.smul_apply]⟩
  apply coreDigital_measure_le_of_positive_lipschitz_tests
  intro f K hK hf
  rw [integral_smul_measure, ENNReal.toReal_ofReal hA, smul_eq_mul]
  apply le_of_forall_pos_le_add
  intro ε hε
  exact le_of_tendsto (hlim f) (hbound f K hK hf ε hε)

/-- Positive Lipschitz control suffices for the actual empirical measures;
all subsequential-limit and absolute-continuity suppliers are discharged. -/
theorem coreDigital_window_measures_tendsto_of_lipschitz_bounds
    {C : ℕ} (hC : 2 ≤ C)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hNpos : ∀ j, 0 < N j)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * ∫ x, f x ∂volume + ε) :
    Tendsto (fun j => coreDigitalWindowMeasure u (a j) (N j)) atTop
      (𝓝 coreCircleVolume) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  obtain ⟨φ, hφ, hlim⟩ := hμ.tendsto_subseq
  have htest : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a (φ j)) (N (φ j)))
        atTop (𝓝 (∫ x, f x ∂(μ : Measure (AddCircle (1 : ℝ))))) := by
    intro f
    have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
    simpa only [Function.comp_apply,
      coreDigitalWindowMeasure_integral u _ (hNpos _)] using ht
  have heq := coreDigital_window_limit_eq_volume_of_lipschitz_bounds hC u hu
    (a ∘ φ) (N ∘ φ) (hN.comp hφ.tendsto_atTop)
    (μ : Measure (AddCircle (1 : ℝ))) htest hA
    (fun f K hK hf ε hε => hφ.tendsto_atTop.eventually (hbound f K hK hf ε hε))
  exact Subtype.ext heq

theorem coreDigital_window_character_tendsto_zero_of_lipschitz_bounds
    {C : ℕ} (hC : 2 ≤ C)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hNpos : ∀ j, 0 < N j)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * ∫ x, f x ∂volume + ε)
    {q : ℤ} (hq : q ≠ 0) :
    Tendsto (fun j => (∑ i ∈ Finset.range (N j), fourier q (u (a j + i))) /
      (N j : ℂ)) atTop (𝓝 0) := by
  have hm := coreDigital_window_measures_tendsto_of_lipschitz_bounds hC u hu a N
    hN hNpos hA hbound
  let f : AddCircle (1 : ℝ) →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact (fourier q)
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hm f
  have hc : (coreCircleVolume : Measure (AddCircle (1 : ℝ))) = volume := rfl
  simp only [coreDigitalWindowMeasure_integral_complex u _ (hNpos _), hc] at ht
  change Tendsto (fun j => (∑ i ∈ Finset.range (N j), fourier q (u (a j + i))) /
    (N j : ℂ)) atTop (𝓝 (∫ x : AddCircle (1 : ℝ), fourier q x)) at ht
  rwa [coreDigital_nonzero_character_integral hq] at ht

end PrimeGapNormality.Prime
