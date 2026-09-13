import PrimeGapNormality.Prime.CoreLocalDAssembly

/-! Quantifier-preserving assembly of the arithmetic D transfer with an
actual normalized-model subsequence supplier. The model bound is a named
intermediate contract here, not an additional conjecture or a finished
prime theorem. -/

namespace PrimeGapNormality.Prime
open Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section

def CoreLocalModelSubsequenceBounds
    (B : ℕ) (κ : ℝ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (w : ℕ) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ σ : Measure (AddCircle (1 : ℝ)), IsFiniteMeasure σ ∧ σ ≪ volume ∧
        ∃ A : ℝ, 0 ≤ A ∧
          ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
            LipschitzWith K f → (∀ x, 0 ≤ f x) →
            ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
              coreLocalStoppedMean B (ahlSmall_window κ (φ (ψ n)))
                (profileL κ (φ (ψ n))) w hk phase F
                (finiteRootMix (φ (ψ n)) (ahlSmall_window κ (φ (ψ n)))) f ≤
                  A * (∫ x, f x ∂σ) + ε

theorem coreLocal_subsequenceReference_of_D_and_model
    {B d k : ℕ} (hB : 2 ≤ B) (hd : 1 ≤ d) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) (w : ℕ)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hdeg : ∀ s, (F s).totalDegree ≤ d)
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c)
    (hmodel : CoreLocalModelSubsequenceBounds B κ hk phase F w) :
    CoreResidueDigitalReference.SubsequenceReferenceBounds
      (CoreCyclic.coreLocalSeriesCircle B hk phase (fun q ↦ (primeGap q : ℝ)) F)
      (fun X ↦ Nat.primeCounting X) windowNX := by
  intro φ hφ
  obtain ⟨ψ, hψ, σ, hσfinite, hσ, A, hA, hbound⟩ := hmodel φ hφ
  letI : IsFiniteMeasure σ := hσfinite
  refine ⟨ψ, hψ, σ, hσfinite, hσ, 16 * c * A,
    mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hc)) hA, ?_⟩
  exact coreLocal_positive_reference_of_D_and_model hB hd hk phase F w hw hdeg
    hκ hd0 hc hD (fun n ↦ φ (ψ n))
    (hφ.tendsto_atTop.comp hψ.tendsto_atTop) σ hA hbound

end
end PrimeGapNormality.Prime
