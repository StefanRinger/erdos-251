import PrimeGapNormality.Prime.CoreSequenceLocalPositiveWindow
import PrimeGapNormality.Prime.CoreSequenceLocalTailAverage
import PrimeGapNormality.Prime.CoreSequenceModelReference
import PrimeGapNormality.Prime.CoreLocalTailAtProfile

/-!
# Generic sequence S/T consumer

`SequencePositiveShapeS` is the honest arithmetic probability input: the
actual first-`L` law of a sequence is dominated by the normalized finite root
mixture at a supplied model scale.  The rest of this file is a consumer.  It
adds the actual local-series tail estimate, converts the physical sequence
window to its exact index interval, and feeds the compiled model-reference
and orbit endpoints.  Window-count growth, gap-tail control, and polynomial
gap growth remain explicit hypotheses.
-/

namespace PrimeGapNormality.Prime.CoreSequenceSTConsumer

open Finset Filter MeasureTheory MvPolynomial CoreCyclic
open CoreSequencePatternLaw CoreSequenceLocalPositiveWindow
open scoped Topology NNReal BoundedContinuousFunction Classical

noncomputable section

/-- The finite positive shape comparison required from sequence arithmetic.
The quantifier over shape tests is inside the eventual statement, so the
same physical scale works uniformly for every `[0,1]` test. -/
def SequencePositiveShapeS
    (a T : ℕ → ℕ) (κ c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
    ∀ f : Finset ℕ → ℝ,
      (∀ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
        (fun U ↦ U.card = profileL κ (T X)), 0 ≤ f U) →
      (∀ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
        (fun U ↦ U.card = profileL κ (T X)), f U ≤ 1) →
      Stopped.failureMass (offsetWindow (ahlSmall_window κ (T X)))
          (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
          (profileL κ (T X)) +
        (∑ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
            (fun U ↦ U.card = profileL κ (T X)),
          f U * Stopped.shortShapeMass
            (offsetWindow (ahlSmall_window κ (T X)))
            (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
            (profileL κ (T X)) U) ≤
        c * (∑ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
            (fun U ↦ U.card = profileL κ (T X)),
          f U * Stopped.shortShapeMass
            (offsetWindow (ahlSmall_window κ (T X)))
            (finiteRootMix (T X) (ahlSmall_window κ (T X)))
            (profileL κ (T X)) U) + ε

/-- The actual relative-label local series attached to the gaps of `a`. -/
def sequenceLocalOrbit
    (B : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (a : ℕ → ℕ) (n : ℕ) : AddCircle (1 : ℝ) :=
  (coreLocalSeries B hk phase (fun q ↦ (seqGap a q : ℝ)) F n :
    AddCircle (1 : ℝ))

/-- Exact physical-window/index-window conversion for an arbitrary strictly
increasing sequence. -/
theorem windowAvgReal_eq_coreDigitalWindowAverage
    {a : ℕ → ℕ} (ha : StrictMono a)
    (u : ℕ → AddCircle (1 : ℝ)) (f : AddCircle (1 : ℝ) →ᵇ ℝ) (X : ℕ) :
    windowAvgReal (seqWindow a X) (fun n ↦ f (u n)) =
      coreDigitalWindowAverage u f (seqCount a X)
        (CoreSequenceResiduePassage.seqCountDifference a X) := by
  unfold windowAvgReal coreDigitalWindowAverage
  rw [CoreSequenceResiduePassage.seqWindow_eq_Ico_seqCount ha,
    Nat.card_Ico, sum_Ico_eq_sum_range]
  rfl

private theorem windowAvgReal_mono
    (I : Finset ℕ) {f g : ℕ → ℝ} (hfg : ∀ n ∈ I, f n ≤ g n) :
    windowAvgReal I f ≤ windowAvgReal I g := by
  unfold windowAvgReal
  exact div_le_div_of_nonneg_right (sum_le_sum hfg) (Nat.cast_nonneg _)

private theorem windowAvgReal_add
    (I : Finset ℕ) (f g : ℕ → ℝ) :
    windowAvgReal I (fun n ↦ f n + g n) =
      windowAvgReal I f + windowAvgReal I g := by
  unfold windowAvgReal
  rw [sum_add_distrib, add_div]

/-- The finite shape input plus the literal sequence tail yields the exact
`PositiveModelComparison` consumed by the reference theorem. -/
theorem positiveModelComparison_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B d : ℕ} (hB : 2 ≤ B) (hd : 1 ≤ d)
    {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k) (w : ℕ)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hdeg : ∀ s, (F s).totalDegree ≤ d)
    (hgrowth : HasPolynomialGrowth (fun q ↦ (seqGap a q : ℝ)))
    {κ c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) (hc : 0 < c)
    (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    CoreSequenceModelReference.PositiveModelComparison B κ hk phase F w
      (sequenceLocalOrbit B hk phase F a)
      (fun X ↦ seqCount a X)
      (CoreSequenceResiduePassage.seqCountDifference a) T c := by
  have hBr : 1 < (B : ℝ) := by
    exact_mod_cast (show 1 < B by omega)
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos hBr
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hκpos : 0 < κ := (div_pos hdR hlogB).trans_le hκ
  intro f K hK hf0 ε hε
  let C : ℝ := ‖f‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hfC (x : AddCircle (1 : ℝ)) : f x ≤ C := by
    exact (f.apply_le_norm x).trans (le_add_of_nonneg_right zero_le_one)
  have htailRaw := CoreCyclic.tendsto_sequence_localPositiveTestRemainder_zero
    ha hcount hB (localTailBase_pow_le hB hd hκ) hk phase F w hd hw hdeg
    hgrowth hGapTail f hK
  have htail : Tendsto (fun X : ℕ ↦
      windowAvgReal (seqWindow a X) (fun n ↦
        |f (sequenceLocalOrbit B hk phase F a n) -
          f (coreLocalSeriesTrunc B hk phase
            (fun q ↦ (seqGap a q : ℝ)) F n
            (profileL κ (T X) - w) : AddCircle (1 : ℝ))|))
      atTop (nhds 0) := by
    simpa only [sequenceLocalOrbit, Function.comp_apply,
      ← profileL_eq_stdProfileL_localTailBase hκpos] using htailRaw
  have hε2 : 0 < ε / 2 := div_pos hε (by norm_num)
  have hδ : 0 < ε / (2 * C) := div_pos hε (mul_pos (by norm_num) hC)
  have hshape := hS (ε / (2 * C)) hδ
  have hL := hmodelScale.eventually
    ((tendsto_profileL_atTop hκpos).eventually_ge_atTop (w + 1))
  have htailClose := htail.eventually
    (Metric.ball_mem_nhds (0 : ℝ) hε2)
  filter_upwards [hshape, hL, htailClose] with X hshapeX hLX htailX
  let shapeTest : Finset ℕ → ℝ := fun U ↦
    f (coreCyclicFinitePhase B hk phase F (profileL κ (T X) - w)
      (orderedRealGap U) : AddCircle (1 : ℝ)) / C
  have hshape0 : ∀ U ∈
      (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
        (fun U ↦ U.card = profileL κ (T X)), 0 ≤ shapeTest U := by
    intro U hU
    exact div_nonneg (hf0 _) hC.le
  have hshape1 : ∀ U ∈
      (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
        (fun U ↦ U.card = profileL κ (T X)), shapeTest U ≤ 1 := by
    intro U hU
    exact (div_le_one hC).mpr (hfC _)
  have hSX := hshapeX shapeTest hshape0 hshape1
  have hscaled := mul_le_mul_of_nonneg_left hSX hC.le
  have hfinite := truncated_positive_window_le
    (a := a) ha B X (ahlSmall_window κ (T X)) hk phase F
    (by omega : w ≤ profileL κ (T X)) (by omega : 1 ≤ profileL κ (T X))
    hw f hfC
  have hgap : CoreSequenceLocalPositiveWindow.realGap a =
      fun q ↦ (seqGap a q : ℝ) := by
    funext q
    rfl
  rw [hgap] at hfinite
  have hactualFactor :
      C * Stopped.failureMass
          (offsetWindow (ahlSmall_window κ (T X)))
          (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
          (profileL κ (T X)) +
        (∑ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
            (fun U ↦ U.card = profileL κ (T X)),
          f (coreCyclicFinitePhase B hk phase F (profileL κ (T X) - w)
            (orderedRealGap U) : AddCircle (1 : ℝ)) *
            Stopped.shortShapeMass
              (offsetWindow (ahlSmall_window κ (T X)))
              (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
              (profileL κ (T X)) U) =
      C * (Stopped.failureMass
          (offsetWindow (ahlSmall_window κ (T X)))
          (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
          (profileL κ (T X)) +
        (∑ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
            (fun U ↦ U.card = profileL κ (T X)),
          shapeTest U * Stopped.shortShapeMass
            (offsetWindow (ahlSmall_window κ (T X)))
            (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
            (profileL κ (T X)) U)) := by
    rw [mul_add, mul_sum]
    apply congrArg (C * Stopped.failureMass
      (offsetWindow (ahlSmall_window κ (T X)))
      (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
      (profileL κ (T X)) + ·)
    apply sum_congr rfl
    intro U hU
    dsimp only [shapeTest]
    field_simp [hC.ne'] <;> ring
  have hmodelFactor :
      C * (c * (∑ U ∈
          (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
            (fun U ↦ U.card = profileL κ (T X)),
        shapeTest U * Stopped.shortShapeMass
          (offsetWindow (ahlSmall_window κ (T X)))
          (finiteRootMix (T X) (ahlSmall_window κ (T X)))
          (profileL κ (T X)) U) + ε / (2 * C)) =
        c * coreLocalStoppedMean B (ahlSmall_window κ (T X))
          (profileL κ (T X)) w hk phase F
          (finiteRootMix (T X) (ahlSmall_window κ (T X))) f + ε / 2 := by
    have heps : C * (ε / (2 * C)) = ε / 2 := by
      field_simp [hC.ne']
    have hsum :
        C * (∑ U ∈
            (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
              (fun U ↦ U.card = profileL κ (T X)),
          shapeTest U * Stopped.shortShapeMass
            (offsetWindow (ahlSmall_window κ (T X)))
            (finiteRootMix (T X) (ahlSmall_window κ (T X)))
            (profileL κ (T X)) U) =
          ∑ U ∈
            (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
              (fun U ↦ U.card = profileL κ (T X)),
            f (coreCyclicFinitePhase B hk phase F (profileL κ (T X) - w)
              (orderedRealGap U) : AddCircle (1 : ℝ)) *
              Stopped.shortShapeMass
                (offsetWindow (ahlSmall_window κ (T X)))
                (finiteRootMix (T X) (ahlSmall_window κ (T X)))
                (profileL κ (T X)) U := by
      rw [mul_sum]
      apply sum_congr rfl
      intro U hU
      dsimp only [shapeTest]
      field_simp [hC.ne'] <;> ring
    unfold coreLocalStoppedMean
    calc
      C * (c * (∑ U ∈
          (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
            (fun U ↦ U.card = profileL κ (T X)),
        shapeTest U * Stopped.shortShapeMass
          (offsetWindow (ahlSmall_window κ (T X)))
          (finiteRootMix (T X) (ahlSmall_window κ (T X)))
          (profileL κ (T X)) U) + ε / (2 * C)) =
        c * (C * (∑ U ∈
          (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
            (fun U ↦ U.card = profileL κ (T X)),
        shapeTest U * Stopped.shortShapeMass
          (offsetWindow (ahlSmall_window κ (T X)))
          (finiteRootMix (T X) (ahlSmall_window κ (T X)))
          (profileL κ (T X)) U)) + C * (ε / (2 * C)) := by ring
      _ = _ := by rw [hsum, heps]
  have htrunc :
      windowAvgReal (seqWindow a X) (fun n ↦
        f (coreLocalSeriesTrunc B hk phase
          (fun q ↦ (seqGap a q : ℝ)) F n
          (profileL κ (T X) - w) : AddCircle (1 : ℝ))) ≤
        c * coreLocalStoppedMean B (ahlSmall_window κ (T X))
          (profileL κ (T X)) w hk phase F
          (finiteRootMix (T X) (ahlSmall_window κ (T X))) f + ε / 2 := by
    have hfinite' :
        windowAvgReal (seqWindow a X) (fun n ↦
          f (coreLocalSeriesTrunc B hk phase
            (fun q ↦ (seqGap a q : ℝ)) F n
            (profileL κ (T X) - w) : AddCircle (1 : ℝ))) ≤
          C * Stopped.failureMass
              (offsetWindow (ahlSmall_window κ (T X)))
              (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
              (profileL κ (T X)) +
            (∑ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
                (fun U ↦ U.card = profileL κ (T X)),
              f (coreCyclicFinitePhase B hk phase F (profileL κ (T X) - w)
                (orderedRealGap U) : AddCircle (1 : ℝ)) *
                Stopped.shortShapeMass
                  (offsetWindow (ahlSmall_window κ (T X)))
                  (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
                  (profileL κ (T X)) U) := by
      simpa only [offsetWindow] using hfinite
    exact ((hfinite'.trans_eq hactualFactor).trans hscaled).trans_eq hmodelFactor
  have htailLe :
      windowAvgReal (seqWindow a X) (fun n ↦
        |f (sequenceLocalOrbit B hk phase F a n) -
          f (coreLocalSeriesTrunc B hk phase
            (fun q ↦ (seqGap a q : ℝ)) F n
            (profileL κ (T X) - w) : AddCircle (1 : ℝ))|) ≤ ε / 2 := by
    have habs :
        |windowAvgReal (seqWindow a X) (fun n ↦
          |f (sequenceLocalOrbit B hk phase F a n) -
            f (coreLocalSeriesTrunc B hk phase
              (fun q ↦ (seqGap a q : ℝ)) F n
              (profileL κ (T X) - w) : AddCircle (1 : ℝ))|) - 0| < ε / 2 := by
      simpa only [Real.dist_eq] using htailX
    rw [sub_zero] at habs
    exact (le_abs_self _).trans habs.le
  have htriangle :
      windowAvgReal (seqWindow a X)
          (fun n ↦ f (sequenceLocalOrbit B hk phase F a n)) ≤
        windowAvgReal (seqWindow a X) (fun n ↦
          f (coreLocalSeriesTrunc B hk phase
            (fun q ↦ (seqGap a q : ℝ)) F n
            (profileL κ (T X) - w) : AddCircle (1 : ℝ))) +
        windowAvgReal (seqWindow a X) (fun n ↦
          |f (sequenceLocalOrbit B hk phase F a n) -
            f (coreLocalSeriesTrunc B hk phase
              (fun q ↦ (seqGap a q : ℝ)) F n
              (profileL κ (T X) - w) : AddCircle (1 : ℝ))|) := by
    rw [← windowAvgReal_add]
    apply windowAvgReal_mono
    intro n hn
    linarith [le_abs_self
      (f (sequenceLocalOrbit B hk phase F a n) -
        f (coreLocalSeriesTrunc B hk phase
          (fun q ↦ (seqGap a q : ℝ)) F n
          (profileL κ (T X) - w) : AddCircle (1 : ℝ)))]
  rw [← windowAvgReal_eq_coreDigitalWindowAverage ha]
  exact htriangle.trans ((_root_.add_le_add htrunc htailLe).trans_eq (by ring))

/-- First checkpoint: the arithmetic shape input and actual tail hypotheses
discharge the reference premise for every genuine rooted rational tuple. -/
theorem subsequenceReference_of_shapeS_rooted
    {a T : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (w : ℕ)
    (hroot : drop hk F = 0) (hF : F ≠ 0)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hgrowth : HasPolynomialGrowth (fun q ↦ (seqGap a q : ℝ)))
    {κ c : ℝ} (hκ : (topDegree F : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    CoreResidueDigitalReference.SubsequenceReferenceBounds
      (sequenceLocalOrbit B hk phase F a)
      (fun X ↦ seqCount a X)
    (CoreSequenceResiduePassage.seqCountDifference a) := by
  have hd : 1 ≤ topDegree F := one_le_topDegree_of_rooted hk F hroot hF
  have hdeg : ∀ s, (F s).totalDegree ≤ topDegree F :=
    fun s ↦ Finset.le_sup (f := fun s ↦ (F s).totalDegree) (mem_univ s)
  have hcomp := positiveModelComparison_of_shapeS ha hcount hB hd hk phase F w
    hw hdeg hgrowth hκ hc hmodelScale hGapTail hS
  exact CoreSequenceModelReference.subsequence_reference_of_rooted_model_comparison
    hB hk phase F w hroot hF hw hκ
    (sequenceLocalOrbit B hk phase F a)
    (fun X ↦ seqCount a X)
    (CoreSequenceResiduePassage.seqCountDifference a) T hc hmodelScale hcomp

/-- Integer rooted endpoint: the arithmetic shape input, count growth,
actual gap growth, and literal gap-tail hypothesis imply Weyl at the common
`B^k` clock.  No model or reference measure is a premise. -/
theorem fullSeries_weyl_clock_of_sequenceShapeS
    {a T : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ) (w : ℕ)
    (hroot : drop hk (mapIntTuple F) = 0) (hF : mapIntTuple F ≠ 0)
    (hw : ∀ s i, i ∈ (mapIntTuple F s).vars → i ≤ w)
    (hgrowth : HasPolynomialGrowth (fun q ↦ (seqGap a q : ℝ)))
    {κ c : ℝ}
    (hκ : (topDegree (mapIntTuple F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    weylCriterion (B ^ k)
      (coreCyclicFullSeries B hk phase
        (fun q ↦ (seqGap a q : ℝ)) (mapIntTuple F)) := by
  have href := subsequenceReference_of_shapeS_rooted ha hcount hB hk phase
    (mapIntTuple F) w hroot hF hw hgrowth hκ hc hmodelScale hGapTail hS
  have horbit : sequenceLocalOrbit B hk phase (mapIntTuple F) a =
      CoreSequenceLocalOrbitEnd.localOrbit B hk phase
        (fun q ↦ (seqGap a q : ℤ)) F := by
    funext n
    unfold sequenceLocalOrbit CoreSequenceLocalOrbitEnd.localOrbit
      CoreCyclic.coreLocalSeriesCircle
    simp only [Int.cast_natCast]
  have href' : CoreResidueDigitalReference.SubsequenceReferenceBounds
      (CoreSequenceLocalOrbitEnd.localOrbit B hk phase
        (fun q ↦ (seqGap a q : ℤ)) F)
      (fun X ↦ seqCount a X)
      (CoreSequenceResiduePassage.seqCountDifference a) := by
    rw [← horbit]
    exact href
  have hgrowth' : HasPolynomialGrowth
      (fun q ↦ ((seqGap a q : ℤ) : ℝ)) := by
    simpa only [Int.cast_natCast] using hgrowth
  simpa only [Int.cast_natCast] using
    (CoreSequenceLocalOrbitEnd.fullSeries_weyl_clock_of_subsequence_reference
      ha hcount hB hk phase (fun q ↦ (seqGap a q : ℤ)) hgrowth' F href')

/-- The same honest sequence inputs give base-`B` normality of the literal
full relative-label series. -/
theorem fullSeries_isNormal_of_sequenceShapeS
    {a T : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ) (w : ℕ)
    (hroot : drop hk (mapIntTuple F) = 0) (hF : mapIntTuple F ≠ 0)
    (hw : ∀ s i, i ∈ (mapIntTuple F s).vars → i ≤ w)
    (hgrowth : HasPolynomialGrowth (fun q ↦ (seqGap a q : ℝ)))
    {κ c : ℝ}
    (hκ : (topDegree (mapIntTuple F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk phase
        (fun q ↦ (seqGap a q : ℝ)) (mapIntTuple F)) := by
  have href := subsequenceReference_of_shapeS_rooted ha hcount hB hk phase
    (mapIntTuple F) w hroot hF hw hgrowth hκ hc hmodelScale hGapTail hS
  have horbit : sequenceLocalOrbit B hk phase (mapIntTuple F) a =
      CoreSequenceLocalOrbitEnd.localOrbit B hk phase
        (fun q ↦ (seqGap a q : ℤ)) F := by
    funext n
    unfold sequenceLocalOrbit CoreSequenceLocalOrbitEnd.localOrbit
      CoreCyclic.coreLocalSeriesCircle
    simp only [Int.cast_natCast]
  have href' : CoreResidueDigitalReference.SubsequenceReferenceBounds
      (CoreSequenceLocalOrbitEnd.localOrbit B hk phase
        (fun q ↦ (seqGap a q : ℤ)) F)
      (fun X ↦ seqCount a X)
      (CoreSequenceResiduePassage.seqCountDifference a) := by
    rw [← horbit]
    exact href
  have hgrowth' : HasPolynomialGrowth
      (fun q ↦ ((seqGap a q : ℤ) : ℝ)) := by
    simpa only [Int.cast_natCast] using hgrowth
  simpa only [Int.cast_natCast] using
    (CoreSequenceLocalOrbitEnd.fullSeries_isNormal_of_subsequence_reference
      ha hcount hB hk phase (fun q ↦ (seqGap a q : ℤ)) hgrowth' F href')

end
end PrimeGapNormality.Prime.CoreSequenceSTConsumer
