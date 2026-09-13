import PrimeGapNormality.Prime.CoreLocalModelSubsequence
import PrimeGapNormality.Prime.CoreSequenceLocalOrbitEnd
import Mathlib.Order.Filter.AtTopBot.Finite

/-! Quantifier-preserving reuse of the actual model at a synthetic scale.
The model index need only tend to infinity, not be strictly increasing.
The displayed positive comparison is an intermediate input to be proved
from actual pattern and tail control; it is not an unconditional rough
theorem or an assertion that the paper's S/T supplier has been completed. -/

namespace PrimeGapNormality.Prime.CoreSequenceModelReference

open Filter MeasureTheory CoreCyclic
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section

def PositiveModelComparison (B : ℕ) (κ : ℝ) {k : ℕ} (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) (w : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (a N T : ℕ → ℕ) (c : ℝ) : Prop :=
  ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
    LipschitzWith K f → (∀ x, 0 ≤ f x) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      coreDigitalWindowAverage u f (a X) (N X) ≤
        c * coreLocalStoppedMean B (ahlSmall_window κ (T X))
          (profileL κ (T X)) w hk phase F
          (finiteRootMix (T X) (ahlSmall_window κ (T X))) f + ε

/-- Passing to a strict subsequence of the model indices preserves the
outer extraction and fixes the reference measure before all tests. -/
theorem subsequence_reference_of_model_comparison
    {B : ℕ} {κ : ℝ} {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (w : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (a N T : ℕ → ℕ) {c : ℝ} (hc : 0 < c)
    (hT : Tendsto T atTop atTop)
    (hmodel : CoreLocalModelSubsequenceBounds B κ hk phase F w)
    (hcomp : PositiveModelComparison B κ hk phase F w u a N T c) :
    CoreResidueDigitalReference.SubsequenceReferenceBounds u a N := by
  intro φ hφ
  obtain ⟨χ, hχ, hmodelIndex⟩ := strictMono_subseq_of_tendsto_atTop
    (hT.comp hφ.tendsto_atTop)
  obtain ⟨ψ, hψ, σ, hσfinite, hσ, A, hA, hbounds⟩ :=
    hmodel ((T ∘ φ) ∘ χ) hmodelIndex
  refine ⟨χ ∘ ψ, hχ.comp hψ, σ, hσfinite, hσ, c * A,
    mul_nonneg hc.le hA, ?_⟩
  intro f K hf hf0 ε hε
  have hε2 : 0 < ε / 2 := div_pos hε (by norm_num)
  have hδ : 0 < ε / (2 * c) := div_pos hε (mul_pos (by norm_num) hc)
  have hfirst := (hφ.tendsto_atTop.comp (hχ.tendsto_atTop.comp hψ.tendsto_atTop)).eventually
    (hcomp f K hf hf0 (ε / 2) hε2)
  have hsecond := hbounds f K hf hf0 (ε / (2 * c)) hδ
  filter_upwards [hfirst, hsecond] with j hj1 hj2
  dsimp only [Function.comp_apply] at hj1 hj2 ⊢
  have hscaled := mul_le_mul_of_nonneg_left hj2 hc.le
  have heps : c * (ε / (2 * c)) = ε / 2 := by field_simp [hc.ne'] <;> ring
  calc
    coreDigitalWindowAverage u f (a (φ (χ (ψ j)))) (N (φ (χ (ψ j)))) ≤
        c * coreLocalStoppedMean B (ahlSmall_window κ (T (φ (χ (ψ j)))))
          (profileL κ (T (φ (χ (ψ j))))) w hk phase F
          (finiteRootMix (T (φ (χ (ψ j)))) (ahlSmall_window κ (T (φ (χ (ψ j)))))) f + ε / 2 := hj1
    _ ≤ c * (A * (∫ x, f x ∂σ) + ε / (2 * c)) + ε / 2 :=
      _root_.add_le_add hscaled le_rfl
    _ = c * A * (∫ x, f x ∂σ) + ε := by rw [mul_add, heps]; ring

/-- The model-bound premise is discharged for every genuine nonzero rooted
tuple by the already compiled actual finite-model theorem. -/
theorem subsequence_reference_of_rooted_model_comparison
    {B : ℕ} (hB : 2 ≤ B) {κ : ℝ} {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (w : ℕ) (hroot : drop hk F = 0) (hF : F ≠ 0)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hκ : (topDegree F : ℝ) / Real.log (B : ℝ) ≤ κ)
    (u : ℕ → AddCircle (1 : ℝ)) (a N T : ℕ → ℕ) {c : ℝ} (hc : 0 < c)
    (hT : Tendsto T atTop atTop)
    (hcomp : PositiveModelComparison B κ hk phase F w u a N T c) :
    CoreResidueDigitalReference.SubsequenceReferenceBounds u a N :=
  subsequence_reference_of_model_comparison hk phase F w u a N T hc hT
    (CoreLocalModelSubsequence.coreLocalModelSubsequenceBounds_of_rooted
      hB hk phase F w hroot hF hw hκ) hcomp

end
end PrimeGapNormality.Prime.CoreSequenceModelReference
