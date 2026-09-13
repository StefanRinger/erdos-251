import PrimeGapNormality.Prime.CoreScaledGapModelReference
import PrimeGapNormality.Prime.CoreSequenceSTMeanTail
import PrimeGapNormality.Prime.CoreSequenceLocalPositiveWindow
import PrimeGapNormality.Prime.CoreSequenceWindowGrowthFromS

/-!
# Deterministically scaled integer observables under concrete sequence S/T

This is the sequence-generic counterpart of the prime D transfer.  Its
Shape S premise is the actual `SequencePositiveShapeS`, hence specifically
uses `finiteRootMix (T X)`; it is not the paper's still more general
arbitrary-calibrated-mixture formulation.

Window growth and subexponential gap growth are conclusions of Shape S and
the genuine gap-tail input.  The finite prefix is transferred exactly,
the unbounded integer observable is restored from the first-gap mean, and
the deterministic compact scaling is passed through the actual model and
reference construction.  The final orbit uses the true positive residue
class passage, never marked tuple statistics.
-/

namespace PrimeGapNormality.Prime.CoreScaledGapSTNormality

open Finset Filter MeasureTheory CoreCyclic
open CoreIntegerGapObservable CoreIntegerGapInsertion
open CoreSequencePattern CoreSequencePatternLaw CoreSequenceSTConsumer
open CoreSequenceSubexponentialGrowth
open scoped Topology Classical NNReal BoundedContinuousFunction

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

def sequenceObservableOrbit
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (a : ℕ → ℕ) (n : ℕ) : Circle :=
  (observableSeries B hk r F (seqGap a) n : Circle)

theorem actualFiniteObservablePhase_prefix_eq
    {a : ℕ → ℕ} (ha : StrictMono a) (B : ℕ)
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : Fin k → ℕ → ℤ)
    (n L : ℕ) :
    actualFiniteObservablePhase B hk r F L (prefixSet a n L) =
      observableTrunc B hk r F (seqGap a) n L := by
  unfold actualFiniteObservablePhase finiteObservablePhase observableTrunc
    observableValue
  apply sum_congr rfl
  intro e he
  dsimp only
  rw [prefixSet_gap ha n L e (mem_range.mp he)]
  simp only [seqGap, Nat.add_assoc]

private theorem windowAvgReal_mono
    (I : Finset ℕ) {f g : ℕ → ℝ} (hfg : ∀ n ∈ I, f n ≤ g n) :
    windowAvgReal I f ≤ windowAvgReal I g := by
  unfold windowAvgReal
  exact div_le_div_of_nonneg_right (sum_le_sum hfg) (Nat.cast_nonneg _)

private theorem windowAvgReal_add (I : Finset ℕ) (f g : ℕ → ℝ) :
    windowAvgReal I (fun n => f n + g n) =
      windowAvgReal I f + windowAvgReal I g := by
  unfold windowAvgReal
  rw [sum_add_distrib, add_div]

/-- The true GapTailT estimate restores every linearly bounded integer
observable at the exact degree-one profile. -/
theorem tendsto_sequence_observableTestRemainder_zero
    {a T : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hT : GapTailT a (localTailBase κ) (windowG ∘ T))
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    Tendsto (fun X : ℕ => windowAvgReal (seqWindow a X) (fun n =>
      |f (sequenceObservableOrbit B hk r F a n) -
        f (observableTrunc B hk r F (seqGap a) n (profileL κ (T X)) : Circle)|))
      atTop (nhds 0) := by
  have hBlog : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hκpos : 0 < κ := (div_pos zero_lt_one hBlog).trans_le hκ
  let rho := localTailBase κ
  have hrho : 1 < rho := localTailBase_one_lt hκpos
  have hrhoB : rho ≤ (B : ℝ) := by
    simpa only [pow_one] using
      (localTailBase_pow_le hB (show 1 ≤ (1 : ℕ) by omega)
        (by simpa only [Nat.cast_one] using hκ))
  have hgrowth := sequenceGap_hasSubexponentialGrowth ha hcount
  have hgapPos : ∀ n, 1 ≤ seqGap a n := by
    intro n
    unfold seqGap
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.sub_ne_zero_of_lt (ha (Nat.lt_succ_self n)))
  have hscaled := tendsto_scaledGapTail_avg_of_GapTailT hT
  have hmajor := hscaled.const_mul ((K : ℝ) * C)
  simp only [mul_zero] at hmajor
  apply squeeze_zero'
  · exact Eventually.of_forall fun X =>
      div_nonneg (sum_nonneg fun n hn => abs_nonneg _) (Nat.cast_nonneg _)
  · apply Eventually.of_forall
    intro X
    have hp : ∀ n,
        |f (sequenceObservableOrbit B hk r F a n) -
          f (observableTrunc B hk r F (seqGap a) n (profileL κ (T X)) : Circle)| ≤
        (K : ℝ) * C * scaledGapTail rho
          (fun q => (seqGap a q : ℝ)) n (profileL κ (T X)) := by
      intro n
      have hsplit := observableSeries_eq_trunc_add_tail hB hk r F hgapPos
        hgrowth hC hF n (profileL κ (T X))
      have hlip := corePositiveTest_real_dist_le f hK
        (observableSeries B hk r F (seqGap a) n)
        (observableTrunc B hk r F (seqGap a) n (profileL κ (T X)))
      have hobs := abs_observableTail_le_firstGapTail hB hk r F ha hgrowth
        hC hF hrho hrhoB n (profileL κ (T X))
      have hdiff :
          |observableSeries B hk r F (seqGap a) n -
              observableTrunc B hk r F (seqGap a) n (profileL κ (T X))| =
            |observableTail B hk r F (seqGap a) n (profileL κ (T X))| := by
        rw [hsplit]
        ring_nf
      rw [hdiff] at hlip
      have heq : C * rho⁻¹ ^ profileL κ (T X) *
          seqGapTail rho a (n + profileL κ (T X)) =
          C * scaledGapTail rho (fun q => (seqGap a q : ℝ)) n
            (profileL κ (T X)) := by
        rw [scaledGapTail_seqGap, inv_pow]
        ring
      exact hlip.trans
        ((mul_le_mul_of_nonneg_left hobs K.coe_nonneg).trans_eq (by rw [heq]; ring))
    have hm := windowAvgReal_mono (seqWindow a X) (fun n hn => hp n)
    calc
      windowAvgReal (seqWindow a X) (fun n =>
          |f (sequenceObservableOrbit B hk r F a n) -
            f (observableTrunc B hk r F (seqGap a) n (profileL κ (T X)) : Circle)|) ≤
        windowAvgReal (seqWindow a X) (fun n =>
          (K : ℝ) * C * scaledGapTail rho (fun q => (seqGap a q : ℝ)) n
            (profileL κ (T X))) := hm
      _ = (K : ℝ) * C * windowAvgReal (seqWindow a X) (fun n =>
          scaledGapTail rho (fun q => (seqGap a q : ℝ)) n
            (profileL κ (T X))) := by
        unfold windowAvgReal
        rw [← Finset.mul_sum]
        ring
      _ = (K : ℝ) * C * windowAvgReal (seqWindow a X) (fun n =>
          scaledGapTail rho (fun q => (seqGap a q : ℝ)) n
            (stdProfileL rho ((windowG ∘ T) X))) := by
        dsimp only [rho, Function.comp_apply]
        rw [← profileL_eq_stdProfileL_localTailBase hκpos]
  · exact hmajor

/-- Concrete Shape S plus the genuine tail gives the physical positive
comparison with the exact deterministic-observable profile mean. -/
theorem eventually_positive_le_profileMean
    {a T : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {Cobs : ℝ} (hCobs : 0 ≤ Cobs)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ Cobs * (q : ℝ))
    {κ c : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hc : 0 < c)
    (hmodelScale : Tendsto T atTop atTop)
    (hTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c)
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    (hf : ∀ x, 0 ≤ f x) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ X : ℕ in atTop,
      coreDigitalWindowAverage (sequenceObservableOrbit B hk r F a) f
        (seqCount a X) (CoreSequenceResiduePassage.seqCountDifference a X) ≤
      c * CoreRoundedModelSubsequence.profileMean B hk r F κ (T X) f + eps := by
  have hκpos : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  let C := ‖f‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hfC (x : Circle) : f x ≤ C :=
    (f.apply_le_norm x).trans (le_add_of_nonneg_right zero_le_one)
  have hrem := tendsto_sequence_observableTestRemainder_zero ha hcount hB hk r
    F hCobs hF hκ hTail f hK
  have hshape := hS (eps / (2 * C))
    (div_pos heps (mul_pos (by norm_num) hC))
  have hL := hmodelScale.eventually (eventually_one_le_profileL hκpos)
  have hremClose := hrem.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (half_pos heps))
  filter_upwards [hshape, hL, hremClose] with X hSX hLX hremX
  let test : Finset ℕ → ℝ := fun U =>
    f (actualFiniteObservablePhase B hk r F (profileL κ (T X)) U : Circle) / C
  have ht0 : ∀ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
      (fun U => U.card = profileL κ (T X)), 0 ≤ test U :=
    fun U hU => div_nonneg (hf _) hC.le
  have ht1 : ∀ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
      (fun U => U.card = profileL κ (T X)), test U ≤ 1 :=
    fun U hU => (div_le_one hC).mpr (hfC _)
  have hs := hSX test ht0 ht1
  have hsC := mul_le_mul_of_nonneg_left hs hC.le
  have hfinite := positive_firstL_window_le ha X (ahlSmall_window κ (T X))
    hLX (fun U => f (actualFiniteObservablePhase B hk r F (profileL κ (T X)) U : Circle))
    (fun U => hfC _)
  simp_rw [actualFiniteObservablePhase_prefix_eq ha B hk r F] at hfinite
  have htrunc : windowAvgReal (seqWindow a X) (fun n =>
      f (observableTrunc B hk r F (seqGap a) n (profileL κ (T X)) : Circle)) ≤
      c * CoreIntegerGapDTransfer.stoppedMean B (ahlSmall_window κ (T X))
        (profileL κ (T X)) hk r F
        (finiteRootMix (T X) (ahlSmall_window κ (T X))) f + eps / 2 := by
    have hactual :
        C * (Stopped.failureMass (offsetWindow (ahlSmall_window κ (T X)))
          (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
          (profileL κ (T X)) +
          ∑ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
            (fun U => U.card = profileL κ (T X)),
            test U * Stopped.shortShapeMass
              (offsetWindow (ahlSmall_window κ (T X)))
              (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
              (profileL κ (T X)) U) =
        C * Stopped.failureMass (offsetWindow (ahlSmall_window κ (T X)))
          (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
          (profileL κ (T X)) +
          ∑ U ∈ (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
            (fun U => U.card = profileL κ (T X)),
            f (actualFiniteObservablePhase B hk r F (profileL κ (T X)) U : Circle) *
              Stopped.shortShapeMass (offsetWindow (ahlSmall_window κ (T X)))
                (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
                (profileL κ (T X)) U := by
      rw [mul_add, mul_sum]
      apply congrArg (fun z : ℝ =>
        C * Stopped.failureMass (offsetWindow (ahlSmall_window κ (T X)))
          (patternMass a X (offsetWindow (ahlSmall_window κ (T X))))
          (profileL κ (T X)) + z)
      apply sum_congr rfl
      intro U hU
      dsimp only [test]
      field_simp [hC.ne']
    have hmodel : C * (c * (∑ U ∈
        (offsetWindow (ahlSmall_window κ (T X))).powerset.filter
          (fun U => U.card = profileL κ (T X)),
        test U * Stopped.shortShapeMass
          (offsetWindow (ahlSmall_window κ (T X)))
          (finiteRootMix (T X) (ahlSmall_window κ (T X)))
          (profileL κ (T X)) U) + eps / (2 * C)) =
        c * CoreIntegerGapDTransfer.stoppedMean B (ahlSmall_window κ (T X))
          (profileL κ (T X)) hk r F
          (finiteRootMix (T X) (ahlSmall_window κ (T X))) f + eps / 2 := by
      unfold CoreIntegerGapDTransfer.stoppedMean
      rw [mul_add]
      have hepsC : C * (eps / (2 * C)) = eps / 2 := by
        field_simp [hC.ne']
      rw [hepsC]
      congr 1
      simp_rw [Finset.mul_sum]
      apply sum_congr rfl
      intro U hU
      dsimp only [test]
      field_simp [hC.ne'] <;> ring
    have hh := hfinite.trans_eq hactual.symm
    exact (hh.trans hsC).trans_eq hmodel
  have hremLe : windowAvgReal (seqWindow a X) (fun n =>
      |f (sequenceObservableOrbit B hk r F a n) -
        f (observableTrunc B hk r F (seqGap a) n (profileL κ (T X)) : Circle)|) ≤
      eps / 2 := by
    have hh : |windowAvgReal (seqWindow a X) (fun n =>
        |f (sequenceObservableOrbit B hk r F a n) -
          f (observableTrunc B hk r F (seqGap a) n (profileL κ (T X)) : Circle)|)| <
        eps / 2 := by simpa only [Real.dist_eq, sub_zero] using hremX
    exact (le_abs_self _).trans hh.le
  have htriangle : windowAvgReal (seqWindow a X) (fun n =>
      f (sequenceObservableOrbit B hk r F a n)) ≤
      windowAvgReal (seqWindow a X) (fun n =>
        f (observableTrunc B hk r F (seqGap a) n (profileL κ (T X)) : Circle)) +
      windowAvgReal (seqWindow a X) (fun n =>
        |f (sequenceObservableOrbit B hk r F a n) -
          f (observableTrunc B hk r F (seqGap a) n (profileL κ (T X)) : Circle)|) := by
    rw [← windowAvgReal_add]
    apply windowAvgReal_mono
    intro n hn
    linarith [le_abs_self (f (sequenceObservableOrbit B hk r F a n) -
      f (observableTrunc B hk r F (seqGap a) n (profileL κ (T X)) : Circle))]
  rw [CoreIntegerGapDTransfer.stoppedMean_finiteRootMix_eq_modelMean] at htrunc
  rw [← CoreSequenceSTConsumer.windowAvgReal_eq_coreDigitalWindowAverage ha]
  exact htriangle.trans ((_root_.add_le_add htrunc hremLe).trans_eq (by
    simp only [CoreIntegerGapDTransfer.finiteRootModelMean,
      CoreRoundedModelSubsequence.profileMean]
    ring))

/-- Concrete-model S/T gives the subsequence reference bound for every
deterministically scaled observable. -/
theorem subsequenceReference_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {Cobs : ℝ} (hCobs : 0 ≤ Cobs)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ Cobs * (q : ℝ))
    {exponent κ : ℝ} (hexp : 0 < exponent) (hexp1 : exponent ≤ 1)
    (lead : Fin k → ℤ) (hlead : lead ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent lead)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    (hmodelScale : Tendsto T atTop atTop)
    (hTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    CoreResidueDigitalReference.SubsequenceReferenceBounds
      (sequenceObservableOrbit B hk r F a) (fun X => seqCount a X)
      (CoreSequenceResiduePassage.seqCountDifference a) := by
  have hκpos : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hcount := CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
    ha hκpos hc hmodelScale hS hTail
  intro φ hφ
  have hTX : Tendsto (fun n => T (φ n)) atTop atTop :=
    hmodelScale.comp hφ.tendsto_atTop
  obtain ⟨ψ, hψ, σ, hσfinite, hσac, hσmass, hmodel⟩ :=
    CoreScaledGapModelReference.exists_reference_subsequence hB hk r F
      hexp hexp1 lead hlead hscale hκ (fun n => T (φ n)) hTX
  refine ⟨ψ, hψ, σ, hσfinite, hσac,
    c * CoreRoundedModelSubsequence.modelConstant,
    mul_nonneg hc.le CoreRoundedModelSubsequence.modelConstant_nonneg, ?_⟩
  intro f K hK hf eps heps
  have heps2 : 0 < eps / 2 := half_pos heps
  have hsmall : 0 < eps / (2 * c) := div_pos heps (mul_pos (by norm_num) hc)
  have hphys := (hφ.tendsto_atTop.comp hψ.tendsto_atTop).eventually
    (eventually_positive_le_profileMean ha hcount hB hk r F hCobs hF hκ hc
      hmodelScale hTail hS f hK hf heps2)
  have hm := hmodel f K hK hf (eps / (2 * c)) hsmall
  filter_upwards [hphys, hm] with n hn hmn
  have hmul := mul_le_mul_of_nonneg_left hmn hc.le
  have herr : c * (eps / (2 * c)) = eps / 2 := by field_simp [hc.ne']
  rw [mul_add, herr] at hmul
  exact hn.trans (by
    calc
      c * CoreRoundedModelSubsequence.profileMean B hk r F κ (T (φ (ψ n))) f +
          eps / 2 ≤
        (c * CoreRoundedModelSubsequence.modelConstant) * (∫ x, f x ∂σ) +
          eps / 2 + eps / 2 := by
        simpa only [mul_assoc] using (_root_.add_le_add hmul le_rfl)
      _ = _ := by ring)

/-- Final common-clock Weyl theorem under the concrete finiteRootMix S/T
criterion. -/
theorem observableFullSeries_weyl_clock_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {Cobs : ℝ} (hCobs : 0 ≤ Cobs)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ Cobs * (q : ℝ))
    {exponent κ : ℝ} (hexp : 0 < exponent) (hexp1 : exponent ≤ 1)
    (lead : Fin k → ℤ) (hlead : lead ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent lead)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    (hmodelScale : Tendsto T atTop atTop)
    (hTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    weylCriterion (B ^ k) (observableFullSeries B hk r F (seqGap a)) := by
  have hκpos : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hcount := CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
    ha hκpos hc hmodelScale hS hTail
  have hgrowth := sequenceGap_hasSubexponentialGrowth ha hcount
  have href := subsequenceReference_of_shapeS ha hB hk r F hCobs hF
    hexp hexp1 lead hlead hscale hκ hc hmodelScale hTail hS
  have hgapPos : ∀ n, 1 ≤ seqGap a n := by
    intro n
    unfold seqGap
    exact Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt (ha (Nat.lt_succ_self n)))
  have hrec : ∀ n, sequenceObservableOrbit B hk r F a (n + k) =
      B ^ k • sequenceObservableOrbit B hk r F a n := fun n =>
    observableSeriesCircle_add_period hB hk r F hgapPos hgrowth hCobs hF n
  have hclock : 2 ≤ B ^ k := by
    have heq : k = k - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
    rw [heq, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  intro z hz
  have hchar := CoreSequenceResiduePassage.residue_character_cesaro_of_subsequence_reference
    ha hcount hclock (by omega : 1 ≤ k) (r := 0) hk
    (sequenceObservableOrbit B hk r F a) hrec href hz
  unfold CesaroMeanVanishing at hchar
  apply hchar.congr'
  exact Eventually.of_forall fun N => by
    apply congrArg (fun v : ℂ => v / (N : ℂ))
    apply sum_congr rfl
    intro q hq
    have horbit := circleOrbit_of_add_period hrec 0 q
    have horbit' : sequenceObservableOrbit B hk r F a (k * q) =
        (B ^ k) ^ q • (observableFullSeries B hk r F (seqGap a) : Circle) := by
      simpa only [Nat.zero_add, sequenceObservableOrbit, observableFullSeries] using horbit
    change fourier z (sequenceObservableOrbit B hk r F a (q * k + 0)) = _
    rw [show q * k + 0 = k * q by simp only [Nat.add_zero, Nat.mul_comm], horbit']
    rw [← AddCircle.coe_nsmul, fourier_coe_apply]
    simp only [nsmul_eq_mul, Nat.cast_pow, e, Complex.ofReal_one, div_one,
      Complex.ofReal_mul, Complex.ofReal_intCast]
    congr 1
    ring

theorem observableFullSeries_isNormal_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {Cobs : ℝ} (hCobs : 0 ≤ Cobs)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ Cobs * (q : ℝ))
    {exponent κ : ℝ} (hexp : 0 < exponent) (hexp1 : exponent ≤ 1)
    (lead : Fin k → ℤ) (hlead : lead ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent lead)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    (hmodelScale : Tendsto T atTop atTop)
    (hTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    PrimeGapNormality.BFree.IsNormal B (observableFullSeries B hk r F (seqGap a)) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (weylCriterion_of_pow hB (by omega : 1 ≤ k)
      (observableFullSeries_weyl_clock_of_shapeS ha hB hk r F hCobs hF
        hexp hexp1 lead hlead hscale hκ hc hmodelScale hTail hS))

end

end PrimeGapNormality.Prime.CoreScaledGapSTNormality
