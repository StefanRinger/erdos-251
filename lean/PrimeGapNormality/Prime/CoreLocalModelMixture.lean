import PrimeGapNormality.Prime.CoreLocalModelPositive

/-!
# Normalized finite-root mixture for the positive local model

This file averages the actual compact-frame slot bound over the genuine
auxiliary frame mass.  The main term is written as the expectation of the
bounded continuous compact insertion test under the actual joint law.  The
high-count and original fixed-deletion cutoff terms remain separate.
-/

namespace PrimeGapNormality.Prime.CoreLocalModelMixture

open Finset Filter MeasureTheory
open scoped BigOperators Classical Topology Polynomial BoundedContinuousFunction NNReal

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

/-- The frame-only outer phase used after the early-root fibres have been
merged. -/
def outerMap
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (K w J S : ℕ) : Finset ℕ → Circle :=
  CoreLocalModelPositive.outerPhase B hk r P K w J (offsetWindow S)

def compactValueK
    {B : ℕ} {k : ℕ} (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (K w J d S : ℕ)
    (hd : (CoreCyclic.OnePoint.action B hk w s P).totalDegree ≤ d)
    {R : ℝ} (hR : 0 ≤ R) (G : ℝ) (f : Circle →ᵇ ℝ)
    (F : Finset ℕ) : ℝ :=
  CoreLocalModelPositive.compactInsertionTest hR w d
    (CoreCyclic.OnePoint.action B hk w s P) hd G⁻¹ f
    (CoreActualFrameJoint.jointPoint w J G
      (G ^ d / (B : ℝ) ^ (J + 1))
      (outerMap B hk r P K w J S) F)

private theorem compactValueK_nonneg
    {B : ℕ} {k : ℕ} (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (K w J d S : ℕ)
    (hd : (CoreCyclic.OnePoint.action B hk w s P).totalDegree ≤ d)
    {R G : ℝ} (hR : 0 ≤ R) (hG : 0 < G)
    (f : Circle →ᵇ ℝ) (hf0 : ∀ x, 0 ≤ f x) (F : Finset ℕ) :
    0 ≤ compactValueK hk r s P K w J d S hd hR G f F := by
  rw [compactValueK, CoreLocalModelPositive.compactInsertionTest_apply]
  exact (CoreCompactFrameTest.rawTest_nonneg_le_fullIntegral hR
    CoreJointFrameLimit.frame (CoreLocalModelPositive.jointWidth w)
    (CoreLocalModelPositive.jointPhase w d
      (CoreCyclic.OnePoint.action B hk w s P) G⁻¹)
    (CoreLocalModelPositive.continuous_jointPhase_uncurry w d
      (CoreCyclic.OnePoint.action B hk w s P) hd G⁻¹)
    f hf0
    (CoreActualFrameJoint.jointPoint w J G
      (G ^ d / (B : ℝ) ^ (J + 1))
      (outerMap B hk r P K w J S) F)
    (by
      unfold CoreLocalModelPositive.jointWidth
      rw [CoreActualFrameJoint.jointPoint_frame]
      exact CoreActualFrameJoint.localFrame_nonneg w J hG.le F
        (CoreCyclicScaledSlot.centralIndex w))).1

private theorem compactValueK_empty
    {B : ℕ} {k : ℕ} (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (K w J d S : ℕ)
    (hd : (CoreCyclic.OnePoint.action B hk w s P).totalDegree ≤ d)
    {R : ℝ} (hR : 0 ≤ R) (G : ℝ) (f : Circle →ᵇ ℝ) :
    compactValueK hk r s P K w J d S hd hR G f ∅ = 0 := by
  rw [compactValueK, CoreLocalModelPositive.compactInsertionTest_apply]
  unfold CoreCompactFrameTest.rawTest CoreLocalModelPositive.jointWidth
  have hmin : min (0 : ℝ) (R + 1) = 0 := min_eq_left (by linarith)
  simp [CoreCompactFrameTest.clippedWidth, hmin]

/-- Generic expectation identity for the normalized actual auxiliary frame
mass. -/
theorem auxiliaryFrameMass_expectation
    (X S L : ℕ) (v : Finset ℕ → ℝ) :
    (∑ F ∈ (offsetWindow S).powerset,
      coreAuxiliaryFrameMass X S L F * v F) =
      (∑ t ∈ mixScale X, mixWeightV t *
        ∑ F ∈ (offsetWindow S).powerset,
          coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F * v F) /
        mixZ X := by
  unfold coreAuxiliaryFrameMass
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun z : ℝ ↦ z / mixZ X)
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [mul_sum]
  exact sum_congr rfl fun F _ ↦ by ring

/-- The finite frame expectation is literally the integral of the bounded
test under the actual completed joint law; the artificial empty-frame mass
contributes zero. -/
theorem auxiliaryFrameMass_compactValueK_eq_integral
    {B X S L : ℕ} {k : ℕ} (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (K w J d : ℕ)
    (hd : (CoreCyclic.OnePoint.action B hk w s P).totalDegree ≤ d)
    {R : ℝ} (hR : 0 ≤ R) (G : ℝ) (f : Circle →ᵇ ℝ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X) :
    (∑ F ∈ (offsetWindow S).powerset,
      coreAuxiliaryFrameMass X S L F *
        compactValueK hk r s P K w J d S hd hR G f F) =
      ∫ z, CoreLocalModelPositive.compactInsertionTest hR w d
        (CoreCyclic.OnePoint.action B hk w s P) hd G⁻¹ f z
        ∂(CoreActualFrameJoint.jointLaw X S L w J G
          (G ^ d / (B : ℝ) ^ (J + 1))
          (outerMap B hk r P K w J S) hSy hZ :
            Measure (CoreJointFrameLimit.Joint (2 * w + 1))) := by
  have h := CoreActualFrameJoint.integral_jointLaw X S L w J G
    (G ^ d / (B : ℝ) ^ (J + 1)) (outerMap B hk r P K w J S) hSy hZ
    (CoreLocalModelPositive.compactInsertionTest hR w d
      (CoreCyclic.OnePoint.action B hk w s P) hd G⁻¹ f)
    (CoreLocalModelPositive.compactInsertionTest hR w d
      (CoreCyclic.OnePoint.action B hk w s P) hd G⁻¹ f).continuous.measurable
  have hempty :
      CoreLocalModelPositive.compactInsertionTest hR w d
        (CoreCyclic.OnePoint.action B hk w s P) hd G⁻¹ f
          (outerMap B hk r P K w J S ∅,
            (0, G ^ d / (B : ℝ) ^ (J + 1))) = 0 := by
    have hz := compactValueK_empty hk r s P K w J d S hd hR G f
    rw [compactValueK] at hz
    simpa [CoreActualFrameJoint.jointPoint] using hz
  rw [hempty, mul_zero, add_zero] at h
  exact h.symm

/-! ## Uniform retention contraction of the main frame term -/

/-- Weighted good-frame main term. -/
def mainFrameTerm
    (X S L : ℕ) (G ε : ℝ) (v : Finset ℕ → ℝ) : ℝ :=
  (∑ t ∈ mixScale X, mixWeightV t *
    ((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
      ∑ F ∈ (offsetWindow S).powerset,
        coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F *
          (3 * G / Real.log G * (v F + ε)))) / mixZ X

theorem mainFrameTerm_le
    (X S L : ℕ) {G ε T : ℝ} (v : Finset ℕ → ℝ)
    (hG : 1 < G) (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (hv : ∀ F, 0 ≤ v F)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hZ : 0 < mixZ X)
    (hret : ∀ t ∈ mixScale X,
      lateRetention S (sieveCutoff (t : ℝ)) * G / Real.log G ≤ T) :
    mainFrameTerm X S L G ε v ≤
      (12 : ℝ) * T *
        ((∑ F ∈ (offsetWindow S).powerset,
          coreAuxiliaryFrameMass X S L F * v F) + ε) := by
  let layer : ℕ → Finset ℕ → ℝ := fun t F ↦
    coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F
  let mass : Finset ℕ → ℝ := coreAuxiliaryFrameMass X S L
  let a : ℝ := 3 * G / Real.log G
  have ha0 : 0 ≤ a :=
    div_nonneg (mul_nonneg (by norm_num) (zero_lt_one.trans hG).le)
      (Real.log_pos hG).le
  have hlayer0 : ∀ t ∈ mixScale X, ∀ F, 0 ≤ layer t F := by
    intro t ht F
    exact coreAuxiliaryLayerFrameMass_nonneg S _ L (hSy t ht) F
  have hcoef : ∀ t ∈ mixScale X,
      (4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) * a ≤ 12 * T := by
    intro t ht
    calc
      (4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) * a =
          12 * (lateRetention S (sieveCutoff (t : ℝ)) * G / Real.log G) := by
        dsimp only [a]
        ring
      _ ≤ 12 * T := mul_le_mul_of_nonneg_left (hret t ht) (by norm_num)
  have hpoint : ∀ t ∈ mixScale X,
      (4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
          ∑ F ∈ (offsetWindow S).powerset, layer t F * (a * (v F + ε)) ≤
        12 * T * ∑ F ∈ (offsetWindow S).powerset, layer t F * (v F + ε) := by
    intro t ht
    have hsum0 : 0 ≤ ∑ F ∈ (offsetWindow S).powerset,
        layer t F * (v F + ε) :=
      sum_nonneg fun F _ ↦ mul_nonneg (hlayer0 t ht F) (add_nonneg (hv F) hε)
    have heq : ∑ F ∈ (offsetWindow S).powerset,
        layer t F * (a * (v F + ε)) =
      a * ∑ F ∈ (offsetWindow S).powerset, layer t F * (v F + ε) := by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun F _ ↦ by ring
    rw [heq]
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right (hcoef t ht) hsum0)
  have hweighted :
      (∑ t ∈ mixScale X, mixWeightV t *
        ((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
          ∑ F ∈ (offsetWindow S).powerset, layer t F * (a * (v F + ε)))) ≤
      ∑ t ∈ mixScale X, mixWeightV t *
        (12 * T * ∑ F ∈ (offsetWindow S).powerset,
          layer t F * (v F + ε)) :=
    sum_le_sum fun t ht ↦
      mul_le_mul_of_nonneg_left (hpoint t ht) (mixWeightV_nonneg t)
  unfold mainFrameTerm
  change (∑ t ∈ mixScale X, mixWeightV t *
      ((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
        ∑ F ∈ (offsetWindow S).powerset, layer t F * (a * (v F + ε)))) /
      mixZ X ≤ _
  apply (div_le_div_of_nonneg_right hweighted hZ.le).trans
  have hexpect := auxiliaryFrameMass_expectation X S L (fun F ↦ v F + ε)
  have hmassLe := coreAuxiliaryFrameMass_sum_le_one X S L hSy hZ
  calc
    (∑ t ∈ mixScale X, mixWeightV t *
        (12 * T * ∑ F ∈ (offsetWindow S).powerset,
          layer t F * (v F + ε))) / mixZ X =
      12 * T * ∑ F ∈ (offsetWindow S).powerset, mass F * (v F + ε) := by
        have hfactor :
            (∑ t ∈ mixScale X, mixWeightV t *
              (12 * T * ∑ F ∈ (offsetWindow S).powerset,
                layer t F * (v F + ε))) =
              12 * T * ∑ t ∈ mixScale X, mixWeightV t *
                ∑ F ∈ (offsetWindow S).powerset,
                  layer t F * (v F + ε) := by
          rw [Finset.mul_sum]
          exact sum_congr rfl fun t _ ↦ by ring
        rw [hfactor]
        calc
          (12 * T * ∑ t ∈ mixScale X, mixWeightV t *
              ∑ F ∈ (offsetWindow S).powerset,
                layer t F * (v F + ε)) / mixZ X =
              12 * T * ((∑ t ∈ mixScale X, mixWeightV t *
                ∑ F ∈ (offsetWindow S).powerset,
                  layer t F * (v F + ε)) / mixZ X) := by ring
          _ = _ := by
            rw [← hexpect]
    _ = 12 * T * ((∑ F ∈ (offsetWindow S).powerset, mass F * v F) +
        ε * ∑ F ∈ (offsetWindow S).powerset, mass F) := by
      congr 1
      rw [Finset.mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun F _ ↦ by ring
    _ ≤ 12 * T * ((∑ F ∈ (offsetWindow S).powerset, mass F * v F) + ε) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hT)
      exact _root_.add_le_add le_rfl (by
        simpa only [mul_comm, mass] using
          (mul_le_of_le_one_left hε hmassLe))
    _ = (12 : ℝ) * T *
        ((∑ F ∈ (offsetWindow S).powerset,
          coreAuxiliaryFrameMass X S L F * v F) + ε) := rfl

/-! ## The actual finite local-model estimate -/

/-- The two genuine original-law error terms, still under the literal
normalized root-mixture weights. -/
def nonMainTerm
    (X S L : ℕ) (I : Finset ℕ) (j : ℕ) (G R C : ℝ) : ℝ :=
  (∑ t ∈ mixScale X, mixWeightV t *
    (C * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ)) +
      C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
        (fun U ↦ if corePositiveFrameBad I j G R U then 1 else 0))) /
    mixZ X

/-- The generic upper-count component is exactly the previously named
exception when the exposed presieve is the actual small scale. -/
theorem nonMainTerm_upper_eq_exception
    (κ : ℝ) (X L : ℕ) (I : Finset ℕ) (j : ℕ) (G R C : ℝ) :
    nonMainTerm X (ahlSmall_window κ X) L I j G R C =
      C * coreFiniteRootMixUpperException κ X +
        (∑ t ∈ mixScale X, mixWeightV t *
          (C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ))
            (ahlSmall_window κ X) L
            (fun U ↦ if corePositiveFrameBad I j G R U then 1 else 0))) /
          mixZ X := by
  unfold nonMainTerm coreFiniteRootMixUpperException
  calc
    (∑ t ∈ mixScale X, mixWeightV t *
        (C * coreFiniteRootMixUpperRootMass (ahlSmall_window κ X)
            (sieveCutoff (t : ℝ)) +
          C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ))
            (ahlSmall_window κ X) L
            (fun U ↦ if corePositiveFrameBad I j G R U then 1 else 0))) /
        mixZ X =
      (C * (∑ t ∈ mixScale X, mixWeightV t *
          coreFiniteRootMixUpperRootMass (ahlSmall_window κ X)
            (sieveCutoff (t : ℝ))) +
        ∑ t ∈ mixScale X, mixWeightV t *
          (C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ))
            (ahlSmall_window κ X) L
            (fun U ↦ if corePositiveFrameBad I j G R U then 1 else 0))) /
          mixZ X := by
        apply congrArg (fun z : ℝ ↦ z / mixZ X)
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact sum_congr rfl fun t _ ↦ by ring
    _ = C *
          ((∑ t ∈ mixScale X, mixWeightV t *
            coreFiniteRootMixUpperRootMass (ahlSmall_window κ X)
              (sieveCutoff (t : ℝ))) / mixZ X) +
        (∑ t ∈ mixScale X, mixWeightV t *
          (C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ))
            (ahlSmall_window κ X) L
            (fun U ↦ if corePositiveFrameBad I j G R U then 1 else 0))) /
          mixZ X := by ring

/-- At the actual small scale, the remaining original-law cutoff is paid
before deletion reweighting by the first-gap mean.  The constant uses only
the literal `2w+1` frame coordinates and the uniform cutoff calibration
`V(y)⁻¹/G ≤ 4`. -/
theorem nonMainTerm_frameRanks_le
    (κ : ℝ) (X L w J : ℕ) {G R C : ℝ}
    (hZ : 0 < mixZ X) (hwJ : w + 1 ≤ J) (hJL : J + w < L)
    (hG : 0 < G) (hR : 0 < R) (hC : 0 ≤ C)
    (hcal : ∀ t ∈ mixScale X,
      (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / G ≤ (4 : ℝ)) :
    nonMainTerm X (ahlSmall_window κ X) L
        (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
        (J - 1) G R C ≤
      C * coreFiniteRootMixUpperException κ X +
        8 * (2 * w + 1 : ℕ) * C / R := by
  rw [nonMainTerm_upper_eq_exception]
  apply _root_.add_le_add le_rfl
  have hJ : 1 ≤ J := by omega
  have hJle : J ≤ L := by omega
  have hI : ∀ i ∈ CoreCyclic.OnePoint.FiniteExterior.frameRanks w J,
      i + 1 < L :=
    fun i hi ↦ CoreCyclic.OnePoint.FiniteExterior.frameRanks_valid hwJ hJL hi
  have hbad : ∀ t ∈ mixScale X,
      CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ))
          (ahlSmall_window κ X) L
          (fun U ↦ if corePositiveFrameBad
            (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
            (J - 1) G R U then 1 else 0) ≤
        8 * (2 * w + 1 : ℕ) / R := by
    intro t ht
    have hraw := CoreOriginalDeletedFrame.original_bad_frame_mass_le
      (sieveCutoff (t : ℝ)) (ahlSmall_window κ X) L J
      (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
      hJ hJle hI hG hR
    have hraw' :
        CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ))
            (ahlSmall_window κ X) L
            (fun U ↦ if corePositiveFrameBad
              (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
              (J - 1) G R U then 1 else 0) ≤
          (2 * ((CoreCyclic.OnePoint.FiniteExterior.frameRanks w J).card : ℝ)) /
            (R * G * eulerProdNat (sieveCutoff (t : ℝ))) := by
      simpa only [corePositiveFrameBad, Nat.sub_add_cancel hJ] using hraw
    calc
      CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ))
          (ahlSmall_window κ X) L
          (fun U ↦ if corePositiveFrameBad
            (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
            (J - 1) G R U then 1 else 0) ≤
        (2 * ((CoreCyclic.OnePoint.FiniteExterior.frameRanks w J).card : ℝ)) /
          (R * G * eulerProdNat (sieveCutoff (t : ℝ))) := hraw'
      _ =
          (2 * ((CoreCyclic.OnePoint.FiniteExterior.frameRanks w J).card : ℝ) / R) *
            ((eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / G) := by
        field_simp [hR.ne', hG.ne',
          (eulerProdNat_pos (sieveCutoff (t : ℝ))).ne'] <;> ring
      _ ≤
          (2 * ((CoreCyclic.OnePoint.FiniteExterior.frameRanks w J).card : ℝ) / R) *
            4 :=
        mul_le_mul_of_nonneg_left (hcal t ht)
          (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hR.le)
      _ = 8 * (2 * w + 1 : ℕ) / R := by
        rw [CoreCyclic.OnePoint.FiniteExterior.frameRanks_card w J hwJ]
        push_cast
        ring
  have hsum :
      (∑ t ∈ mixScale X, mixWeightV t *
        (C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ))
          (ahlSmall_window κ X) L
          (fun U ↦ if corePositiveFrameBad
            (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
            (J - 1) G R U then 1 else 0))) ≤
      ∑ t ∈ mixScale X, mixWeightV t *
        (8 * (2 * w + 1 : ℕ) * C / R) := by
    apply sum_le_sum
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (mixWeightV_nonneg t)
    calc
      C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ))
          (ahlSmall_window κ X) L
          (fun U ↦ if corePositiveFrameBad
            (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
            (J - 1) G R U then 1 else 0) ≤
        C * (8 * (2 * w + 1 : ℕ) / R) :=
          mul_le_mul_of_nonneg_left (hbad t ht) hC
      _ = 8 * (2 * w + 1 : ℕ) * C / R := by ring
  calc
    (∑ t ∈ mixScale X, mixWeightV t *
        (C * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ))
          (ahlSmall_window κ X) L
          (fun U ↦ if corePositiveFrameBad
            (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
            (J - 1) G R U then 1 else 0))) / mixZ X ≤
      (∑ t ∈ mixScale X, mixWeightV t *
        (8 * (2 * w + 1 : ℕ) * C / R)) / mixZ X :=
      div_le_div_of_nonneg_right hsum hZ.le
    _ = 8 * (2 * w + 1 : ℕ) * C / R := by
      rw [← Finset.sum_mul]
      change (mixZ X * (8 * (2 * w + 1 : ℕ) * C / R)) / mixZ X = _
      field_simp [hZ.ne']

/-- Complete finite local-model estimate.  There is no slot-majorant
hypothesis: the actual Selberg bound is inserted internally.  The outer
phase uses the universal offset slot and hence depends only on the merged
frame `F`, never on the exposed presieve root `σ`. -/
theorem eventually_finiteRootMean_le_joint_add_errors
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (w d : ℕ) (s : Fin k)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (CoreCyclic.OnePoint.action B hk w s P).totalDegree ≤ d)
    {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (f : Circle →ᵇ ℝ) {Kf : ℝ≥0} (hKf : LipschitzWith Kf f)
    (hf0 : ∀ x, 0 ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ G : ℝ in atTop, ∀ (K J X S L : ℕ),
      ∀ (hwJ : w + 1 ≤ J) (hJK : J < K)
        (hlabel : CoreCyclic.phaseAt hk r (J - 1) = s)
        (hG : 1 < G) (hfloor : ⌊G⌋₊ ≤ S) (hJL : J < L)
        (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
        (hZ : 0 < mixZ X)
        (hlate : ∀ t ∈ mixScale X,
          0 < lateRetention S (sieveCutoff (t : ℝ)))
        (hquarter : ∀ t ∈ mixScale X,
          lateRetention S (sieveCutoff (t : ℝ)) ≤ (1 : ℝ) / 4)
        (hθlo : 1 ≤ G ^ d / (B : ℝ) ^ (J + 1))
        (hθhi : G ^ d / (B : ℝ) ^ (J + 1) ≤ (B : ℝ) ^ k)
        (hret : ∀ t ∈ mixScale X,
          lateRetention S (sieveCutoff (t : ℝ)) * G / Real.log G ≤ T),
      corePositiveFiniteRootMean X S L
          (CoreLocalModelPositive.actualTest B hk r P K f) ≤
        (12 : ℝ) * T *
          (∫ z, CoreLocalModelPositive.compactInsertionTest hR.le w d
            (CoreCyclic.OnePoint.action B hk w s P) hd G⁻¹ f z
            ∂(CoreActualFrameJoint.jointLaw X S L w J G
              (G ^ d / (B : ℝ) ^ (J + 1))
              (outerMap B hk r P K w J S)
              hSy hZ :
                Measure (CoreJointFrameLimit.Joint (2 * w + 1))) + ε) +
          nonMainTerm X S L
            (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
            (J - 1) G R ‖f‖ := by
  filter_upwards [CoreLocalModelPositive.eventually_presieve_slot_sum_le_compactTest
    hB hk r P w d s hw hd hR f hKf hf0 hε] with G hslot
  intro K J X S L hwJ hJK hlabel hG hfloor hJL hSy hZ hlate hquarter hθlo hθhi hret
  let p := CoreCyclic.OnePoint.action B hk w s P
  let v : Finset ℕ → ℝ :=
    compactValueK hk r s P K w J d S hd hR.le G f
  let frameBound : ℕ → Finset ℕ → ℝ := fun _ F ↦
    3 * G / Real.log G * (v F + ε)
  have hJ : 1 ≤ J := by omega
  have hjL : J - 1 + 1 < L := by simpa [Nat.sub_add_cancel hJ] using hJL
  have hv0 : ∀ F, 0 ≤ v F :=
    compactValueK_nonneg hk r s P K w J d S hd hR.le
      (zero_lt_one.trans hG) f hf0
  have hframe0 : ∀ t ∈ mixScale X, ∀ F, 0 ≤ frameBound t F := by
    intro t ht F
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (zero_lt_one.trans hG).le)
        (Real.log_pos hG).le)
      (add_nonneg (hv0 F) hε.le)
  have hroot := corePositiveFiniteRootMean_le_frame_high_originalBad
    X S L (J - 1) (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J) G R
    (CoreLocalModelPositive.actualTest B hk r P K f) frameBound hZ hjL
    (fun U ↦ hf0 _)
    (fun U ↦ f.apply_le_norm _)
    hSy hlate hquarter hframe0 (by
      intro t ht σ n hn F hF
      exact hslot K J S L n σ F hwJ hJK hlabel hG.le hfloor hJL
        (mem_Icc.mp (mem_filter.mp hn).1).1 hF hθlo hθhi)
  have hdecomp :
      (∑ t ∈ mixScale X, mixWeightV t *
        (((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
            (∑ F ∈ (offsetWindow S).powerset,
              coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F *
                frameBound t F) +
          ‖f‖ * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) +
          ‖f‖ * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
            (fun U ↦ if corePositiveFrameBad
              (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
              (J - 1) G R U then 1 else 0))) / mixZ X =
        mainFrameTerm X S L G ε v +
          nonMainTerm X S L
            (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
            (J - 1) G R ‖f‖ := by
    unfold mainFrameTerm nonMainTerm
    have hsum :
        (∑ t ∈ mixScale X, mixWeightV t *
          (((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
              (∑ F ∈ (offsetWindow S).powerset,
                coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F *
                  frameBound t F) +
            ‖f‖ * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) +
            ‖f‖ * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
              (fun U ↦ if corePositiveFrameBad
                (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
                (J - 1) G R U then 1 else 0)) =
          (∑ t ∈ mixScale X, mixWeightV t *
            ((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
              ∑ F ∈ (offsetWindow S).powerset,
                coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F *
                  (3 * G / Real.log G * (v F + ε)))) +
          ∑ t ∈ mixScale X, mixWeightV t *
            (‖f‖ * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ)) +
              ‖f‖ * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
                (fun U ↦ if corePositiveFrameBad
                  (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
                  (J - 1) G R U then 1 else 0))) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro t _
      dsimp only [frameBound]
      ring
    rw [hsum, add_div]
  have hmain := mainFrameTerm_le X S L v hG hε.le hT hv0 hSy hZ hret
  have hint := auxiliaryFrameMass_compactValueK_eq_integral
    (L := L) hk r s P K w J d hd hR.le G f hSy hZ
  calc
    corePositiveFiniteRootMean X S L
        (CoreLocalModelPositive.actualTest B hk r P K f) ≤
      mainFrameTerm X S L G ε v +
        nonMainTerm X S L
          (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
          (J - 1) G R ‖f‖ := hroot.trans_eq hdecomp
    _ ≤ (12 : ℝ) * T *
        ((∑ F ∈ (offsetWindow S).powerset,
          coreAuxiliaryFrameMass X S L F * v F) + ε) +
        nonMainTerm X S L
          (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
          (J - 1) G R ‖f‖ := _root_.add_le_add hmain le_rfl
    _ = (12 : ℝ) * T *
          (∫ z, CoreLocalModelPositive.compactInsertionTest hR.le w d p hd G⁻¹ f z
            ∂(CoreActualFrameJoint.jointLaw X S L w J G
              (G ^ d / (B : ℝ) ^ (J + 1))
              (outerMap B hk r P K w J S) hSy hZ :
                Measure (CoreJointFrameLimit.Joint (2 * w + 1))) + ε) +
        nonMainTerm X S L
          (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J)
          (J - 1) G R ‖f‖ := by
      rw [← hint]

end

end PrimeGapNormality.Prime.CoreLocalModelMixture
