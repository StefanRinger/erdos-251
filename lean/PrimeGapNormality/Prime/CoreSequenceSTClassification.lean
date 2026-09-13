import PrimeGapNormality.Prime.CoreSequenceSTNormality
import PrimeGapNormality.Prime.CoreLiftedNormalTuple
import PrimeGapNormality.Prime.CoreRationalAffine

/-!
# Rational-or-normal classification for concrete sequence S/T

This packages the concrete `finiteRootMix (T X)` S/T endpoint for an
arbitrary rational periodic local tuple.  It selects the canonical normal
form, clears its finitely many coefficient denominators, and uses only the
effective degree of that normal form.  The telescope contributes the actual
rational boundary evaluated on the integer gap sequence.

The result remains deliberately scoped to `SequencePositiveShapeS`, not the
paper's still-more-general arbitrary calibrated-mixture hypothesis.
-/

namespace PrimeGapNormality.Prime.CoreSequenceSTClassification

open Finset Filter MvPolynomial CoreCyclic
open CoreSequenceSTConsumer CoreSequenceSTNormality
open CoreSequenceSubexponentialGrowth
open scoped Topology Classical

noncomputable section

private theorem localClock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    2 ≤ B ^ k := by
  have hsplit : k = k - 1 + 1 :=
    (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [hsplit, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

private theorem exists_localWidth {k : ℕ} (N : PeriodicLocal k) :
    ∃ w : ℕ, ∀ s i, i ∈ (N s).vars → i ≤ w := by
  let w := Finset.univ.sup (fun s : Fin k ↦ (N s).vars.sup id)
  refine ⟨w, ?_⟩
  intro s i hi
  exact (Finset.le_sup (f := id) hi).trans
    (Finset.le_sup (f := fun s : Fin k ↦ (N s).vars.sup id) (mem_univ s))

private theorem kappa_pos_of_gapTail
    {κ : ℝ} {a T : ℕ → ℕ}
    (hTail : GapTailT a (localTailBase κ) (windowG ∘ T)) : 0 < κ := by
  have h : 0 < 1 / κ := by
    rw [← Real.one_lt_exp_iff]
    simpa only [localTailBase] using hTail.1
  exact one_div_pos.mp h

/-- The rational endpoint left by the canonical telescope on the actual
integer gap sequence. -/
def sequenceLocalBoundaryRat
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (a : ℕ → ℕ) (F : PeriodicLocal k) : ℚ :=
  localBoundaryRat hB hk phase (fun n ↦ (seqGap a n : ℤ)) F 0

/-- Exact normal-form decomposition under the subexponential growth already
derived from growing sequence windows. -/
theorem coreCyclicFullSeries_eq_normalForm_add_boundary_of_subexponential
    {a : ℕ → ℕ} {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k)
    (hgrowth : HasSubexponentialGrowth (fun n ↦ (seqGap a n : ℝ))) :
    coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F =
      coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ))
          (normalForm hB hk F) +
        (sequenceLocalBoundaryRat hB hk phase a F : ℝ) := by
  have hdiff := infiniteSeries_normalForm_of_subexponential
    hB hk phase (fun n ↦ (seqGap a n : ℝ)) hgrowth F 0
  have hboundary := localBoundaryRat_cast hB hk phase
    (fun n ↦ (seqGap a n : ℤ)) F 0
  simp only [Int.cast_natCast] at hboundary
  have hboundary' : (sequenceLocalBoundaryRat hB hk phase a F : ℝ) =
      localValue hk phase (fun n ↦ (seqGap a n : ℝ))
        (primitive hB hk F) 0 := by
    simpa only [sequenceLocalBoundaryRat] using hboundary
  have hdiff' :
      coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F -
        coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ))
          (normalForm hB hk F) =
        (sequenceLocalBoundaryRat hB hk phase a F : ℝ) := by
    rw [hboundary']
    simpa only [coreCyclicFullSeries, Nat.zero_add,
      sequenceLocalBoundaryRat] using hdiff
  linarith

theorem coreCyclicFullSeries_rational_of_normalForm_zero
    {a : ℕ → ℕ} {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k)
    (hgrowth : HasSubexponentialGrowth (fun n ↦ (seqGap a n : ℝ)))
    (hzero : normalForm hB hk F = 0) :
    ∃ q : ℚ,
      coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F =
        (q : ℝ) := by
  refine ⟨sequenceLocalBoundaryRat hB hk phase a F, ?_⟩
  rw [coreCyclicFullSeries_eq_normalForm_add_boundary_of_subexponential
    hB hk phase F hgrowth, hzero]
  simp [coreCyclicFullSeries, localValue]

/-- Denominator clearing for a nonzero rooted rational tuple preserves its
width and exact effective degree, so the integer S/T theorem applies. -/
theorem rooted_rational_weyl_clock_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    {κ c : ℝ} (hκ : (topDegree N : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    weylCriterion (B ^ k)
      (coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) N) := by
  obtain ⟨w, hw⟩ := exists_localWidth N
  let NI : PeriodicLocal k := liftedIntegerTuple N
  have hNIroot : drop hk NI = 0 := liftedIntegerTuple_rooted hk N hroot
  have hNI : NI ≠ 0 := liftedIntegerTuple_ne_zero N hN
  have hNIw : ∀ s i, i ∈ (NI s).vars → i ≤ w :=
    (liftedIntegerTuple_width_iff N).2 hw
  have hNId : topDegree NI = topDegree N := topDegree_liftedIntegerTuple N
  have hκI : (topDegree NI : ℝ) / Real.log (B : ℝ) ≤ κ := by
    rwa [hNId]
  have hWI := fullSeries_weyl_clock_of_shapeS ha hB hk phase
    (integerTupleLift N).tuple w hNIroot hNI hNIw hκI hc
    hmodelScale hGapTail hS
  change weylCriterion (B ^ k)
    (coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ))
      (liftedIntegerTuple N)) at hWI
  rw [coreCyclicFullSeries_liftedIntegerTuple] at hWI
  exact weylCriterion_of_mul
    (Nat.succ_le_iff.mpr (liftedIntegerScale_pos N)) (localClock_ge hB hk) hWI

/-- Effective normal-form degree is the only profile degree for a general
rational tuple. -/
theorem local_weyl_clock_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hNF : normalForm hB hk F ≠ 0)
    {κ c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    weylCriterion (B ^ k)
      (coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F) := by
  have hNFweyl := rooted_rational_weyl_clock_of_shapeS ha hB hk phase
    (normalForm hB hk F) (drop_normalForm hB hk F) hNF hκ hc
    hmodelScale hGapTail hS
  have hκpos := kappa_pos_of_gapTail hGapTail
  have hcount := CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
    ha hκpos hc hmodelScale hS hGapTail
  have hgrowth := sequenceGap_hasSubexponentialGrowth ha hcount
  have heq := coreCyclicFullSeries_eq_normalForm_add_boundary_of_subexponential
    hB hk phase F hgrowth
  have hshift := CoreRationalAffine.weylCriterion_add_rat
    (localClock_ge hB hk) (sequenceLocalBoundaryRat hB hk phase a F) hNFweyl
  rwa [← heq] at hshift

theorem local_rational_iff_normalForm_zero
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {κ c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    (∃ q : ℚ,
      coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F =
        (q : ℝ)) ↔ normalForm hB hk F = 0 := by
  have hκpos := kappa_pos_of_gapTail hGapTail
  have hcount := CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
    ha hκpos hc hmodelScale hS hGapTail
  have hgrowth := sequenceGap_hasSubexponentialGrowth ha hcount
  constructor
  · rintro ⟨q, hq⟩
    by_contra hnonzero
    have hW := local_weyl_clock_of_shapeS ha hB hk phase F hnonzero hκ hc
      hmodelScale hGapTail hS
    exact (weylCriterion_irrational hW) ⟨q, hq.symm⟩
  · intro hzero
    exact coreCyclicFullSeries_rational_of_normalForm_zero
      hB hk phase F hgrowth hzero

/-- Literal rational-or-normal classification for the concrete model S/T
input.  The normal branch is normal both to the period clock and to `B`. -/
theorem local_classification_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {κ c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    (normalForm hB hk F = 0 ∧
      ∃ q : ℚ,
        coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F =
          (q : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F)) := by
  by_cases hzero : normalForm hB hk F = 0
  · exact Or.inl ⟨hzero,
      (local_rational_iff_normalForm_zero ha hB hk phase F hκ hc
        hmodelScale hGapTail hS).2 hzero⟩
  · have hW := local_weyl_clock_of_shapeS ha hB hk phase F hzero hκ hc
      hmodelScale hGapTail hS
    exact Or.inr ⟨hzero, hW,
      CoreWeylNormality.isNormal_of_weyl (localClock_ge hB hk) hW,
      CoreWeylNormality.isNormal_of_weyl hB
        (weylCriterion_of_pow hB (by omega : 1 ≤ k) hW)⟩

end
end PrimeGapNormality.Prime.CoreSequenceSTClassification
