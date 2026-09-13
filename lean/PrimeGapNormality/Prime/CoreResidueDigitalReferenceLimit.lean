import PrimeGapNormality.Prime.CoreResidueDigitalReference

/-!
A fixed finite absolutely continuous reference bound on full windows
forces every actual index-residue window to converge to circle volume.
The progression and its diverging lengths are the proved finite objects
from `CoreResidueDigitalReference`, not an index-class distribution input.
-/

namespace PrimeGapNormality.Prime.CoreResidueDigitalReference

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

noncomputable section

def residueMeasure {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (a N : ℕ) :
    ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  coreDigitalWindowMeasure (progression k r u) (start hk r a)
    (coreResidueWindowCount k r a N)

theorem residueMeasure_integral {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (a N : ℕ)
    (hM : 0 < coreResidueWindowCount k r a N) (f : AddCircle (1 : ℝ) →ᵇ ℝ) :
    (∫ x, f x ∂(residueMeasure hk r u a N : Measure (AddCircle (1 : ℝ)))) =
      coreResidueWindowAverage k r u f a N :=
  (coreDigitalWindowMeasure_integral (progression k r u) (start hk r a) hM f).trans
    (average_eq_progression hk r u f a N).symm

theorem residueMeasure_integral_complex {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (a N : ℕ)
    (hM : 0 < coreResidueWindowCount k r a N) (f : AddCircle (1 : ℝ) →ᵇ ℂ) :
    (∫ x, f x ∂(residueMeasure hk r u a N : Measure (AddCircle (1 : ℝ)))) =
      (∑ i ∈ coreResidueWindowOffsets k r a N, f (u (a + i))) /
        (coreResidueWindowCount k r a N : ℂ) := by
  have h := coreDigitalWindowMeasure_integral_complex
    (progression k r u) (start hk r a) hM f
  rw [sum_reindex_range hk r a N (fun n ↦ f (u n))]
  exact h

/-- Positive restriction to an index class costs at most the fixed factor
`2k`, for any reference measure, not only a bounded-density reference. -/
theorem reference_bound_of_full {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (σ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure σ] {A : ℝ}
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * (∫ x, f x ∂σ) + ε) :
    ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreResidueWindowAverage k r u f (a j) (N j) ≤
          (2 * (k : ℝ) * A) * (∫ x, f x ∂σ) + ε := by
  intro f K hK hf ε hε
  have hkpos : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
    positivity
  have hε' : 0 < ε / (2 * (k : ℝ)) := div_pos hε hkpos
  filter_upwards [hN.eventually (eventually_ge_atTop (2 * k)),
    hbound f K hK hf (ε / (2 * (k : ℝ))) hε'] with j hNj hfull
  have hMR := coreResidueWindowCount_pos_and_ratio_le_two_mul
    (r := r) (a := a j) hk hNj
  have hcond := coreResidueWindowAverage_le_countRatio_mul_full
    (k := k) (r := r) u f (by omega : 0 < N j) hMR.1 (fun i _ ↦ hf _)
  have hfull0 : 0 ≤ coreDigitalWindowAverage u f (a j) (N j) := by
    unfold coreDigitalWindowAverage
    exact div_nonneg (sum_nonneg fun i _ ↦ hf _) (Nat.cast_nonneg _)
  calc
    coreResidueWindowAverage k r u f (a j) (N j) ≤
        (2 * (k : ℝ)) * coreDigitalWindowAverage u f (a j) (N j) :=
      hcond.trans (mul_le_mul_of_nonneg_right hMR.2 hfull0)
    _ ≤ (2 * (k : ℝ)) * (A * (∫ x, f x ∂σ) + ε / (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hfull hkpos.le
    _ = (2 * (k : ℝ) * A) * (∫ x, f x ∂σ) + ε := by field_simp [hkpos.ne']

/-- Every genuine residue-window weak limit is volume. Invariance follows
from the derived progression recurrence, and AC follows from the fixed
reference measure, after the proved `2k` restriction cost. -/
theorem residue_limit_eq_volume {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hlim : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j ↦ coreResidueWindowAverage k r u f (a j) (N j)) atTop
        (𝓝 (∫ x, f x ∂μ)))
    (σ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure σ]
    (hσ : σ ≪ volume) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * (∫ x, f x ∂σ) + ε) :
    μ = volume := by
  apply coreDigitalPeriodic_window_limit_eq_volume_of_reference_bounds hC
    (by decide : 1 ≤ (1 : ℕ)) (progression k r u) (progression_recurrence r u hu)
    (fun j ↦ start hk r (a j)) (fun j ↦ coreResidueWindowCount k r (a j) (N j))
    (count_tendsto_atTop hk r a N hN) μ
    (fun f ↦ by simpa only [average_eq_progression hk r u f] using hlim f)
    σ hσ (A := 2 * (k : ℝ) * A)
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) hA)
  intro f K hK hf ε hε
  simpa only [average_eq_progression hk r u f] using
    reference_bound_of_full hk r u a N hN σ hbound f K hK hf ε hε

/-- Actual residue empirical probability measures converge weakly. Empty
residue windows use the existing zero-length convention, which disappears
eventually because their literal counts tend to infinity. -/
theorem residue_measures_tendsto_volume {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (σ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure σ]
    (hσ : σ ≪ volume) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * (∫ x, f x ∂σ) + ε) :
    Tendsto (fun j ↦ residueMeasure hk r u (a j) (N j)) atTop (𝓝 coreCircleVolume) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  obtain ⟨φ, hφ, hweak⟩ := hμ.tendsto_subseq
  have hM := (count_tendsto_atTop hk r a N hN).comp hφ.tendsto_atTop
  have htest : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j ↦ coreResidueWindowAverage k r u f (a (φ j)) (N (φ j))) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure (AddCircle (1 : ℝ))))) := by
    intro f
    have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f
    apply ht.congr'
    filter_upwards [hM.eventually (eventually_gt_atTop 0)] with j hj
    exact residueMeasure_integral hk r u (a (φ j)) (N (φ j)) hj f
  have heq := residue_limit_eq_volume hC hk r u hu (a ∘ φ) (N ∘ φ)
    (hN.comp hφ.tendsto_atTop) (μ : Measure (AddCircle (1 : ℝ))) htest σ hσ hA
    (fun f K hK hf ε hε ↦ hφ.tendsto_atTop.eventually (hbound f K hK hf ε hε))
  exact Subtype.ext heq

theorem residue_tests_tendsto_volume {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (σ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure σ]
    (hσ : σ ≪ volume) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * (∫ x, f x ∂σ) + ε)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) :
    Tendsto (fun j ↦ coreResidueWindowAverage k r u f (a j) (N j)) atTop
      (𝓝 (∫ x, f x ∂volume)) := by
  have hweak := residue_measures_tendsto_volume hC hk r u hu a N hN σ hσ hA hbound
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f
  apply ht.congr'
  filter_upwards [(count_tendsto_atTop hk r a N hN).eventually (eventually_gt_atTop 0)] with j hj
  exact residueMeasure_integral hk r u (a j) (N j) hj f

theorem residue_characters_tendsto_zero {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (σ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure σ]
    (hσ : σ ≪ volume) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * (∫ x, f x ∂σ) + ε)
    {q : ℤ} (hq : q ≠ 0) :
    Tendsto (fun j ↦
      (∑ i ∈ coreResidueWindowOffsets k r (a j) (N j), fourier q (u (a j + i))) /
        (coreResidueWindowCount k r (a j) (N j) : ℂ)) atTop (𝓝 0) := by
  have hweak := residue_measures_tendsto_volume hC hk r u hu a N hN σ hσ hA hbound
  let f : AddCircle (1 : ℝ) →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact (fourier q)
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hweak f
  have hzero : (∫ x, f x ∂(coreCircleVolume : Measure (AddCircle (1 : ℝ)))) = 0 :=
    coreDigital_nonzero_character_integral hq
  rw [hzero] at ht
  apply ht.congr'
  filter_upwards [(count_tendsto_atTop hk r a N hN).eventually (eventually_gt_atTop 0)] with j hj
  exact residueMeasure_integral_complex hk r u (a j) (N j) hj f

end

end PrimeGapNormality.Prime.CoreResidueDigitalReference
