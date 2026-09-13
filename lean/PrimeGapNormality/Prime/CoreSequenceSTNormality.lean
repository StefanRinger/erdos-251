import PrimeGapNormality.Prime.CoreSequenceWindowGrowthFromS
import PrimeGapNormality.Prime.CoreSequenceSubexponentialTail
import PrimeGapNormality.Prime.CoreSequenceModelReference
import PrimeGapNormality.Prime.CoreSequenceSTConsumer
import PrimeGapNormality.Prime.CoreWeylNormality

/-!
# Normality from the concrete finite-root-mixture S/T input

This closes the sequence-generic consumer for the concrete shape hypothesis
`SequencePositiveShapeS`, whose model is the literal
`finiteRootMix (T X)`.  Window-count divergence is derived from that shape
input and `GapTailT`; subexponential gap growth is then derived from the
window count.  Neither is retained as a theorem premise.

This is intentionally not advertised as the fully abstract paper S/T
criterion, which permits arbitrary calibrated model mixtures.
-/

namespace PrimeGapNormality.Prime.CoreSequenceSTNormality

open Finset Filter MeasureTheory MvPolynomial CoreCyclic
open CoreSequencePatternLaw CoreSequenceLocalPositiveWindow
open CoreSequenceSTConsumer CoreSequenceSubexponentialGrowth
open scoped Topology NNReal BoundedContinuousFunction Classical

noncomputable section

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

/-- The concrete finite shape comparison plus the genuine sequence tail
gives the positive model comparison with subexponential growth. -/
theorem positiveModelComparison_of_shapeS_subexponential
    {a T : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B d : ℕ} (hB : 2 ≤ B) (hd : 1 ≤ d)
    {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k) (w : ℕ)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hdeg : ∀ s, (F s).totalDegree ≤ d)
    (hgrowth : HasSubexponentialGrowth (fun q ↦ (seqGap a q : ℝ)))
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
  have hfC (x : AddCircle (1 : ℝ)) : f x ≤ C :=
    (f.apply_le_norm x).trans (le_add_of_nonneg_right zero_le_one)
  have htailRaw :=
    tendsto_sequence_localPositiveTestRemainder_zero_of_subexponential
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

private theorem clock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    2 ≤ B ^ k := by
  have heq : k = k - 1 + 1 :=
    (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [heq, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

private theorem fourier_nsmul (z : ℤ) (C q : ℕ) (x : ℝ) :
    fourier z (C ^ q • (x : AddCircle (1 : ℝ))) =
      e ((z : ℝ) * (C : ℝ) ^ q * x) := by
  rw [← AddCircle.coe_nsmul, fourier_coe_apply]
  simp only [nsmul_eq_mul, Nat.cast_pow, e, Complex.ofReal_one, div_one,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

/-- Concrete finite-root-mixture S/T supplies the subsequence reference;
window growth and subexponentiality are conclusions inside the proof. -/
theorem subsequenceReference_of_shapeS_rooted
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (w : ℕ)
    (hroot : drop hk F = 0) (hF : F ≠ 0)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    {κ c : ℝ} (hκ : (topDegree F : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    CoreResidueDigitalReference.SubsequenceReferenceBounds
      (sequenceLocalOrbit B hk phase F a) (fun X ↦ seqCount a X)
      (CoreSequenceResiduePassage.seqCountDifference a) := by
  have hd : 1 ≤ topDegree F := one_le_topDegree_of_rooted hk F hroot hF
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hκpos : 0 < κ :=
    (div_pos (Nat.cast_pos.mpr (by omega)) (Real.log_pos hBr)).trans_le hκ
  have hcount := CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
    ha hκpos hc hmodelScale hS hGapTail
  have hgrowth := sequenceGap_hasSubexponentialGrowth ha hcount
  have hdeg : ∀ s, (F s).totalDegree ≤ topDegree F :=
    fun s ↦ Finset.le_sup (f := fun s ↦ (F s).totalDegree) (mem_univ s)
  have hcomp := positiveModelComparison_of_shapeS_subexponential
    ha hcount hB hd hk phase F w hw hdeg hgrowth hκ hc hmodelScale hGapTail hS
  exact CoreSequenceModelReference.subsequence_reference_of_rooted_model_comparison
    hB hk phase F w hroot hF hw hκ
    (sequenceLocalOrbit B hk phase F a) (fun X ↦ seqCount a X)
    (CoreSequenceResiduePassage.seqCountDifference a) T hc hmodelScale hcomp

/-- Final common-clock Weyl endpoint.  Its only analytic assumptions are the
actual finite-root-mixture shape comparison and the genuine gap-tail input. -/
theorem fullSeries_weyl_clock_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ) (w : ℕ)
    (hroot : drop hk (mapIntTuple F) = 0) (hF : mapIntTuple F ≠ 0)
    (hw : ∀ s i, i ∈ (mapIntTuple F s).vars → i ≤ w)
    {κ c : ℝ}
    (hκ : (topDegree (mapIntTuple F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    weylCriterion (B ^ k)
      (coreCyclicFullSeries B hk phase
        (fun q ↦ (seqGap a q : ℝ)) (mapIntTuple F)) := by
  have hd : 1 ≤ topDegree (mapIntTuple F) :=
    one_le_topDegree_of_rooted hk (mapIntTuple F) hroot hF
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hκpos : 0 < κ :=
    (div_pos (Nat.cast_pos.mpr (by omega)) (Real.log_pos hBr)).trans_le hκ
  have hcount := CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
    ha hκpos hc hmodelScale hS hGapTail
  have hgrowth := sequenceGap_hasSubexponentialGrowth ha hcount
  have href := subsequenceReference_of_shapeS_rooted ha hB hk phase
    (mapIntTuple F) w hroot hF hw hκ hc hmodelScale hGapTail hS
  intro z hz
  have hrec : ∀ n,
      sequenceLocalOrbit B hk phase (mapIntTuple F) a (n + k) =
        B ^ k • sequenceLocalOrbit B hk phase (mapIntTuple F) a n := by
    intro n
    unfold sequenceLocalOrbit
    simpa only [CoreCyclic.coreLocalSeriesCircle, Int.cast_natCast] using
      (coreLocalSeriesCircle_add_period_of_intTuple_subexponential
        hB hk phase (fun q ↦ (seqGap a q : ℤ))
        (by simpa only [Int.cast_natCast] using hgrowth) F n)
  have hchar :=
    CoreSequenceResiduePassage.residue_character_cesaro_of_subsequence_reference
      ha hcount (clock_ge hB hk) (by omega : 1 ≤ k) (r := 0) hk
      (sequenceLocalOrbit B hk phase (mapIntTuple F) a) hrec href hz
  unfold CesaroMeanVanishing at hchar
  apply hchar.congr'
  exact Eventually.of_forall fun N ↦ by
    apply congrArg (fun v : ℂ ↦ v / (N : ℂ))
    apply sum_congr rfl
    intro q hq
    have horbit :=
      coreLocalSeriesCircle_progression_zero_eq_fullSeries_subexponential
        hB hk phase (fun j ↦ (seqGap a j : ℤ))
        (by simpa only [Int.cast_natCast] using hgrowth) F q
    simp only [Int.cast_natCast] at horbit
    change fourier z (coreLocalSeriesCircle B hk phase
      (fun j ↦ (seqGap a j : ℝ)) (mapIntTuple F) (q * k + 0)) = _
    rw [show q * k + 0 = k * q by
      simp only [Nat.add_zero, Nat.mul_comm], horbit]
    exact fourier_nsmul z (B ^ k) q _

theorem fullSeries_isNormal_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ) (w : ℕ)
    (hroot : drop hk (mapIntTuple F) = 0) (hF : mapIntTuple F ≠ 0)
    (hw : ∀ s i, i ∈ (mapIntTuple F s).vars → i ≤ w)
    {κ c : ℝ}
    (hκ : (topDegree (mapIntTuple F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk phase
        (fun q ↦ (seqGap a q : ℝ)) (mapIntTuple F)) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (weylCriterion_of_pow hB (by omega : 1 ≤ k)
      (fullSeries_weyl_clock_of_shapeS ha hB hk phase F w hroot hF hw
        hκ hc hmodelScale hGapTail hS))

end
end PrimeGapNormality.Prime.CoreSequenceSTNormality
