import PrimeGapNormality.Prime.CorePrimeResiduePassage

/-! The reference measure may depend on a subsequence, but must be fixed
before the test and error tolerance. This is the exact quantifier order
provided by joint auxiliary-frame extraction. No globally common reference
measure is assumed. -/

namespace PrimeGapNormality.Prime.CoreResidueDigitalReference
open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section

def SubsequenceReferenceBounds
    (u : ℕ → AddCircle (1 : ℝ)) (a N : ℕ → ℕ) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ σ : Measure (AddCircle (1 : ℝ)), IsFiniteMeasure σ ∧ σ ≪ volume ∧
        ∃ A : ℝ, 0 ≤ A ∧
          ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
            LipschitzWith K f → (∀ x, 0 ≤ f x) →
            ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
              coreDigitalWindowAverage u f (a (φ (ψ j))) (N (φ (ψ j))) ≤
                A * (∫ x, f x ∂σ) + ε

theorem residue_measures_tendsto_volume_of_subsequence_reference
    {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hbound : SubsequenceReferenceBounds u a N) :
    Tendsto (fun j ↦ residueMeasure hk r u (a j) (N j)) atTop (𝓝 coreCircleVolume) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  obtain ⟨φ, hφ, hweak⟩ := hμ.tendsto_subseq
  obtain ⟨ψ, hψ, σ, hσfinite, hσ, A, hA, hbounds⟩ := hbound φ hφ
  letI : IsFiniteMeasure σ := hσfinite
  have hM := (count_tendsto_atTop hk r a N hN).comp
    (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
  have hweak' := hweak.comp hψ.tendsto_atTop
  have htest : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j ↦ coreResidueWindowAverage k r u f
        (a (φ (ψ j))) (N (φ (ψ j)))) atTop
          (𝓝 (∫ x, f x ∂(μ : Measure (AddCircle (1 : ℝ))))) := by
    intro f
    have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak' f
    apply ht.congr'
    filter_upwards [hM.eventually (eventually_gt_atTop 0)] with j hj
    exact residueMeasure_integral hk r u (a (φ (ψ j))) (N (φ (ψ j))) hj f
  have heq := residue_limit_eq_volume hC hk r u hu
    (fun j ↦ a (φ (ψ j))) (fun j ↦ N (φ (ψ j)))
    (hN.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
    (μ : Measure (AddCircle (1 : ℝ))) htest σ hσ hA hbounds
  exact Subtype.ext heq

theorem residue_characters_tendsto_zero_of_subsequence_reference
    {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hbound : SubsequenceReferenceBounds u a N) {z : ℤ} (hz : z ≠ 0) :
    Tendsto (fun j ↦
      (∑ i ∈ coreResidueWindowOffsets k r (a j) (N j), fourier z (u (a j + i))) /
        (coreResidueWindowCount k r (a j) (N j) : ℂ)) atTop (𝓝 0) := by
  have hweak := residue_measures_tendsto_volume_of_subsequence_reference
    hC hk r u hu a N hN hbound
  let f : AddCircle (1 : ℝ) →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact (fourier z)
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hweak f
  have hzero : (∫ x, f x ∂(coreCircleVolume : Measure (AddCircle (1 : ℝ)))) = 0 :=
    coreDigital_nonzero_character_integral hz
  rw [hzero] at ht
  apply ht.congr'
  filter_upwards [(count_tendsto_atTop hk r a N hN).eventually (eventually_gt_atTop 0)] with j hj
  exact residueMeasure_integral_complex hk r u (a j) (N j) hj f

end
end PrimeGapNormality.Prime.CoreResidueDigitalReference

namespace PrimeGapNormality.Prime.CorePrimeResiduePassage
open MeasureTheory
open scoped Topology
noncomputable section

theorem primeResidue_character_cesaro_of_subsequence_reference
    {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k) {r : ℕ} (hr : r < k)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (hbound : CoreResidueDigitalReference.SubsequenceReferenceBounds u
      (fun X ↦ Nat.primeCounting X) windowNX) {z : ℤ} (hz : z ≠ 0) :
    CesaroMeanVanishing (fun q ↦ fourier z (u (q * k + r))) := by
  apply primeResidue_character_cesaro_of_residueWindows hk hr u z
  exact CoreResidueDigitalReference.residue_characters_tendsto_zero_of_subsequence_reference
    hC hk r u hu (fun X ↦ Nat.primeCounting X) windowNX
    CorePrimeDensity.tendsto_windowNX_atTop hbound hz

end
end PrimeGapNormality.Prime.CorePrimeResiduePassage
