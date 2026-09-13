import PrimeGapNormality.Prime.CoreAuxiliaryFrameMass
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The actual auxiliary frame probability

Discarded original low-cardinality configurations are placed at the empty
frame. The retained frame masses are unchanged, not renormalized. Thus
tests vanishing at the empty frame retain their exact first-moment formula.
-/

open MeasureTheory Finset
open scoped Classical ENNReal
namespace PrimeGapNormality.Prime
noncomputable section

def coreAuxiliaryCompletedWeight (X S L : ℕ) (F : Finset ℕ) : ℝ :=
  coreAuxiliaryFrameMass X S L F +
    if F = ∅ then coreAuxiliaryFrameMissingMass X S L else 0

theorem coreAuxiliaryCompletedWeight_nonneg (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) (F : Finset ℕ) :
    0 ≤ coreAuxiliaryCompletedWeight X S L F := by
  unfold coreAuxiliaryCompletedWeight
  apply add_nonneg (coreAuxiliaryFrameMass_nonneg X S L hSy hZ F)
  split_ifs
  · exact coreAuxiliaryFrameMissingMass_nonneg X S L hSy hZ
  · exact le_rfl

theorem coreAuxiliaryCompletedWeight_sum (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryCompletedWeight X S L F) = 1 := by
  unfold coreAuxiliaryCompletedWeight
  rw [sum_add_distrib]
  simpa using coreAuxiliaryFrameMass_add_missing_eq_one X S L hSy hZ

/-- The literal finite PMF on complete frames. -/
def coreAuxiliaryFramePMF (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) : PMF ↥((offsetWindow S).powerset) :=
  PMF.ofFintype (fun F ↦ ENNReal.ofReal (coreAuxiliaryCompletedWeight X S L F)) (by
    rw [Finset.sum_coe_sort ((offsetWindow S).powerset)
      (fun F : Finset ℕ ↦ ENNReal.ofReal (coreAuxiliaryCompletedWeight X S L F))]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun F _ ↦ coreAuxiliaryCompletedWeight_nonneg X S L hSy hZ F)]
    rw [coreAuxiliaryCompletedWeight_sum X S L hSy hZ]
    simp)

@[simp] theorem coreAuxiliaryFramePMF_apply (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) (F : ↥((offsetWindow S).powerset)) :
    coreAuxiliaryFramePMF X S L hSy hZ F =
      ENNReal.ofReal (coreAuxiliaryCompletedWeight X S L F) := rfl

/-- Every finite expectation, with the discarded mass still explicit. -/
theorem coreAuxiliaryFramePMF_integral (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) (f : Finset ℕ → ℝ) :
    (∫ F, f F ∂(coreAuxiliaryFramePMF X S L hSy hZ).toMeasure) =
      (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryFrameMass X S L F * f F) +
        coreAuxiliaryFrameMissingMass X S L * f ∅ := by
  rw [PMF.integral_eq_sum]
  have hreal (F : ↥((offsetWindow S).powerset)) :
      (coreAuxiliaryFramePMF X S L hSy hZ F).toReal =
        coreAuxiliaryCompletedWeight X S L F := by
    rw [coreAuxiliaryFramePMF_apply]
    exact ENNReal.toReal_ofReal (coreAuxiliaryCompletedWeight_nonneg X S L hSy hZ F)
  simp only [hreal, smul_eq_mul]
  rw [Finset.sum_coe_sort ((offsetWindow S).powerset)
    (fun F : Finset ℕ ↦ coreAuxiliaryCompletedWeight X S L F * f F)]
  simp only [coreAuxiliaryCompletedWeight, add_mul, sum_add_distrib]
  congr 1
  simp only [ite_mul, zero_mul]
  simp

/-- Zero-at-empty tests have no artificial error or normalization cost. -/
theorem coreAuxiliaryFramePMF_integral_of_empty (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) (f : Finset ℕ → ℝ) (h0 : f ∅ = 0) :
    (∫ F, f F ∂(coreAuxiliaryFramePMF X S L hSy hZ).toMeasure) =
      ∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryFrameMass X S L F * f F := by
  rw [coreAuxiliaryFramePMF_integral, h0, mul_zero, add_zero]

end
end PrimeGapNormality.Prime
