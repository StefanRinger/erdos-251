import PrimeGapNormality.Prime.CoreAuxiliaryFrameProbability
import PrimeGapNormality.Prime.CoreCyclicFiniteExterior
import PrimeGapNormality.Prime.CoreJointFrameLimit

/-!
# The actual auxiliary joint law

Push forward the genuine completed auxiliary-frame PMF, retaining an
arbitrary outer phase. The phase and frame are not made independent.
The scale is a deterministic input at this finite stage; the critical-rank
theorem supplies its bounds at the actual profile.
-/

open MeasureTheory Finset
open scoped Classical ENNReal
namespace PrimeGapNormality.Prime.CoreActualFrameJoint
noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

def localFrame (w j : ℕ) (G : ℝ) (F : Finset ℕ) : Fin (2 * w + 1) → ℝ :=
  fun i ↦ (subsetGap F (CoreCyclic.OnePoint.FiniteExterior.frameRank w j i) : ℝ) / G

theorem localFrame_nonneg (w j : ℕ) {G : ℝ} (hG : 0 ≤ G) (F : Finset ℕ)
    (i : Fin (2 * w + 1)) : 0 ≤ localFrame w j G F i :=
  div_nonneg (Nat.cast_nonneg _) hG

private theorem orderStat_empty (n : ℕ) : orderStat ∅ n = 0 := by
  by_cases hn : n = 0 <;> simp [orderStat, hn]

@[simp] theorem localFrame_empty (w j : ℕ) (G : ℝ) : localFrame w j G ∅ = 0 := by
  funext i
  simp [localFrame, subsetGap, orderStat_empty]

def jointPoint (w j : ℕ) (G θ : ℝ) (O : Finset ℕ → Circle) (F : Finset ℕ) :
    CoreJointFrameLimit.Joint (2 * w + 1) :=
  (O F, (localFrame w j G F, θ))

@[simp] theorem jointPoint_frame (w j : ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle) (F : Finset ℕ) :
    CoreJointFrameLimit.frame (jointPoint w j G θ O F) = localFrame w j G F := rfl

@[simp] theorem jointPoint_scale (w j : ℕ) (G θ : ℝ)
    (O : Finset ℕ → Circle) (F : Finset ℕ) :
    CoreJointFrameLimit.scale (jointPoint w j G θ O F) = θ := rfl

def jointLaw (X S L w j : ℕ) (G θ : ℝ) (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) : ProbabilityMeasure (CoreJointFrameLimit.Joint (2 * w + 1)) :=
  ⟨((coreAuxiliaryFramePMF X S L hSy hZ).map
    (fun F : ↥((offsetWindow S).powerset) ↦ jointPoint w j G θ O F)).toMeasure,
    inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
theorem integral_jointLaw (X S L w j : ℕ) (G θ : ℝ) (O : Finset ℕ → Circle)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    (f : CoreJointFrameLimit.Joint (2 * w + 1) → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂(jointLaw X S L w j G θ O hSy hZ :
      Measure (CoreJointFrameLimit.Joint (2 * w + 1)))) =
      (∑ F ∈ (offsetWindow S).powerset,
        coreAuxiliaryFrameMass X S L F * f (jointPoint w j G θ O F)) +
        coreAuxiliaryFrameMissingMass X S L * f (O ∅, (0, θ)) := by
  have hm : Measurable
      (fun F : ↥((offsetWindow S).powerset) ↦ jointPoint w j G θ O F) :=
    measurable_of_finite _
  change (∫ z, f z ∂((coreAuxiliaryFramePMF X S L hSy hZ).map
    (fun F : ↥((offsetWindow S).powerset) ↦ jointPoint w j G θ O F)).toMeasure) = _
  rw [← PMF.toMeasure_map
    (fun F : ↥((offsetWindow S).powerset) ↦ jointPoint w j G θ O F)
    (coreAuxiliaryFramePMF X S L hSy hZ) hm,
    integral_map hm.aemeasurable hf.aestronglyMeasurable]
  simpa only [jointPoint, localFrame_empty] using
    coreAuxiliaryFramePMF_integral X S L hSy hZ
      (fun F ↦ f (jointPoint w j G θ O F))

end
end PrimeGapNormality.Prime.CoreActualFrameJoint
