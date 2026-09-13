import PrimeGapNormality.Prime.CoreRoundedSlotApproximation
import PrimeGapNormality.Prime.CoreRoundedReferenceMeasure
import PrimeGapNormality.Prime.CoreCompactContinuousInsertion
import PrimeGapNormality.Prime.CoreLocalModelMixture

/-!
# Actual rounded slot majorization with the original deletion cutoff

The leading compact test is independent of G. Rounded integer emissions
are compared with it only pointwise inside the actual slot; they are not
used as weak-convergence tests. The selected outer point is taken from
the universal offset slot, before presieve environments are averaged.
-/

namespace PrimeGapNormality.Prime.CoreRoundedModelFinite

open Finset Filter MeasureTheory CoreCyclic CoreRoundedPowerScaling
  CoreIntegerGapInsertion CoreRoundedSlotApproximation
open scoped Topology Classical NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

abbrev Circle := AddCircle (1 : ℝ)
abbrev Joint := CoreJointFrameLimit.Joint 1

def outerMap (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (Fobs : Fin k → ℕ → ℤ) (L J S : ℕ) (F : Finset ℕ) : Circle :=
  if h : (CoreActualCyclicSlot.slot (offsetWindow S) F J).Nonempty then
    (selectedObservableOuter B hk r Fobs L J (offsetWindow S) F h : Circle)
  else 0

def actualTest (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (Fobs : Fin k → ℕ → ℤ) (L : ℕ) (f : Circle →ᵇ ℝ) (U : Finset ℕ) : ℝ :=
  f (actualFiniteObservablePhase B hk r Fobs L U : Circle)

def compactTest {R : ℝ} (hR : 0 ≤ R) {a : ℝ} (ha : 0 < a)
    (A C : ℝ) (f : Circle →ᵇ ℝ) : Joint →ᵇ ℝ :=
  CoreCompactFrameTest.boundedTest hR CoreJointFrameLimit.frame CoreRoundedReferenceMeasure.width
    (fun z t => CoreRoundedReferenceMeasure.phase a A C (z, t))
    CoreJointFrameLimit.continuous_frame CoreRoundedReferenceMeasure.continuous_width
    (CoreRoundedReferenceMeasure.continuous_phase ha A C) f

theorem compactTest_nonneg {R : ℝ} (hR : 0 ≤ R) {a : ℝ} (ha : 0 < a)
    (A C : ℝ) (f : Circle →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (z : Joint)
    (hW : 0 ≤ CoreRoundedReferenceMeasure.width z) : 0 ≤ compactTest hR ha A C f z :=
  (CoreCompactFrameTest.rawTest_nonneg_le_fullIntegral hR CoreJointFrameLimit.frame
    CoreRoundedReferenceMeasure.width (fun z t => CoreRoundedReferenceMeasure.phase a A C (z, t))
    (CoreRoundedReferenceMeasure.continuous_phase ha A C) f hf z hW).1

theorem point_width (J : ℕ) (hJ : 1 ≤ J) (G θ : ℝ) (O : Finset ℕ → Circle) (F : Finset ℕ) :
    CoreRoundedReferenceMeasure.width (CoreActualFrameJoint.jointPoint 0 J G θ O F) =
      (subsetGap F (J - 1) : ℝ) / G := by
  change CoreActualFrameJoint.localFrame 0 J G F 0 = _
  have heq : (0 : Fin (2 * 0 + 1)) = CoreCyclicScaledSlot.centralIndex 0 := by
    apply Fin.ext
    have hi := (CoreCyclicScaledSlot.centralIndex 0).isLt
    simp only [Fin.val_zero]
    omega
  rw [heq]
  exact CoreCyclicScaledSlot.localFrame_centralIndex 0 J hJ G F

def parameterSet (R C : ℝ) : Set Joint :=
  Set.univ ×ˢ (Metric.closedBall (0 : Fin 1 → ℝ) R ×ˢ Set.Icc 1 C)

theorem parameterSet_compact (R C : ℝ) : IsCompact (parameterSet R C) :=
  isCompact_univ.prod ((isCompact_closedBall (0 : Fin 1 → ℝ) R).prod isCompact_Icc)

theorem compactTest_empty {R : ℝ} (hR : 0 ≤ R) {a : ℝ} (ha : 0 < a)
    (A C : ℝ) (f : Circle →ᵇ ℝ) (O : Circle) (θ : ℝ) :
    compactTest hR ha A C f (O, (0, θ)) = 0 := by
  change CoreCompactFrameTest.rawTest R CoreJointFrameLimit.frame CoreRoundedReferenceMeasure.width
    (fun z t => CoreRoundedReferenceMeasure.phase a A C (z, t)) f (O, (0, θ)) = 0
  unfold CoreCompactFrameTest.rawTest CoreCompactFrameTest.clippedWidth CoreRoundedReferenceMeasure.width
    CoreJointFrameLimit.frame
  simp [min_eq_left (by linarith : (0 : ℝ) ≤ R + 1)]

/-- The actual rounded slot estimate, uniform in all later ranks,
presieves, complete retained frames and integer locations. -/
theorem eventually_slot_sum_le
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a R : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hR : 0 < R)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    {B : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (f : Circle →ᵇ ℝ) {Kf : ℝ≥0} (hKf : LipschitzWith Kf f)
    (hf : ∀ x, 0 ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ G : ℝ in atTop, ∀ (L J S n : ℕ) (σ : ResidueChoice S) (F : Finset ℕ),
      1 ≤ J → J < L → phaseAt hk r (J - 1) = s → ⌊G⌋₊ ≤ S → L ≤ n →
      F ∈ (presieveSurvivors S σ).powersetCard (n - 1) →
      1 ≤ G ^ a / (B : ℝ) ^ (J + 1) → G ^ a / (B : ℝ) ^ (J + 1) < (B : ℝ) ^ k →
      auxFrame_slotInsertSum (presieveSurvivors S σ) (J - 1)
        (corePositiveCutTest (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R
          (actualTest B hk r (roundedCombination kind alpha b) L f)) F ≤
        3 * G / Real.log G *
          (compactTest hR.le ha ((B : ℝ) * leadingColumn alpha b a s)
            (leadingColumn alpha b a (cyclicSucc hk s)) f
            (CoreActualFrameJoint.jointPoint 0 J G (G ^ a / (B : ℝ) ^ (J + 1))
              (outerMap B hk r (roundedCombination kind alpha b) L J S) F) + ε) := by
  let Acoef := (B : ℝ) * leadingColumn alpha b a s
  let Ccoef := (leadingColumn alpha b a (cyclicSucc hk s) : ℝ)
  let δ := ε / (2 * (R + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let q := δ / ((Kf : ℝ) + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hKq : (Kf : ℝ) * q ≤ δ := by
    have heq : ((Kf : ℝ) + 1) * q = δ := by
      dsimp [q]
      field_simp [(show 0 < (Kf : ℝ) + 1 from by positivity).ne']
    nlinarith [Kf.coe_nonneg, hq.le]
  let test := fun z : Joint × ℝ => f (CoreRoundedReferenceMeasure.phase a Acoef Ccoef z) + δ
  have htestc : Continuous test := (f.continuous.comp
    (CoreRoundedReferenceMeasure.continuous_phase ha Acoef Ccoef)).add continuous_const
  have htest0 : ∀ z : Joint, ∀ t : ℝ, 0 ≤ test (z, t) := fun z t => add_nonneg (hf _) hδ.le
  have hsel := CoreCompactContinuousInsertion.eventually_positive_insertion
    (parameterSet R ((B : ℝ) ^ k)) (parameterSet_compact R ((B : ℝ) ^ k)) test hR
    htestc.continuousOn (fun z _ t _ => htest0 z t) (show 0 < ε / 2 by positivity)
  have happ := eventually_actualFiniteObservablePhase_test_approx kind alpha b ha ha1 hR.le halpha
    hB hk r f hKf q hq
  filter_upwards [hsel, happ, eventually_gt_atTop (1 : ℝ)] with G hselG happG hG
  intro L J S n σ F hJ hJL hlabel hfloor hLn hF hθlo hθhi
  let Aset := presieveSurvivors S σ
  let E := CoreActualCyclicSlot.slot Aset F J
  let O := outerMap B hk r (roundedCombination kind alpha b) L J S
  let θ := G ^ a / (B : ℝ) ^ (J + 1)
  let z := CoreActualFrameJoint.jointPoint 0 J G θ O F
  let W := (subsetGap F (J - 1) : ℝ) / G
  let left := (CoreLinearInsertion.insertionSlot F J).1
  have hg : 0 < G := zero_lt_one.trans hG
  have hW0 : 0 ≤ W := div_nonneg (Nat.cast_nonneg _) hg.le
  have hpointWidth : CoreRoundedReferenceMeasure.width z = W := point_width J hJ G θ O F
  have hnonneg : 0 ≤ compactTest hR.le ha Acoef Ccoef f z :=
    compactTest_nonneg hR.le ha Acoef Ccoef f hf z (by rwa [hpointWidth])
  have hfactor : 0 ≤ 3 * G / Real.log G := div_nonneg (by positivity) (Real.log_pos hG).le
  by_cases hbad : ∃ q ∈ OnePoint.FiniteExterior.frameRanks 0 J, R < (subsetGap F q : ℝ) / G
  · have hz : ∀ u ∈ E,
        corePositiveCutTest (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R
          (actualTest B hk r (roundedCombination kind alpha b) L f) (insert u F) = 0 := by
      intro u hu
      have hb : corePositiveFrameBad (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R (insert u F) := by
        by_contra hn
        exact ((CoreActualCyclicSlot.not_frameBad_insert_iff 0 G R hJ hu).mp hn) hbad
      simp only [corePositiveCutTest, if_pos hb]
    unfold auxFrame_slotInsertSum
    change (∑ u ∈ E, _) ≤ _
    rw [sum_eq_zero hz]
    exact mul_nonneg hfactor (add_nonneg hnonneg hε.le)
  have hWA : W ≤ R := CoreActualCyclicSlot.centralWidth_le_of_not_bad 0 J hJ F hbad
  have hnorm : ‖CoreJointFrameLimit.frame z‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR.le).2
    intro i
    change ‖CoreActualFrameJoint.localFrame 0 J G F i‖ ≤ R
    rw [Real.norm_eq_abs, abs_of_nonneg (CoreActualFrameJoint.localFrame_nonneg 0 J hg.le F i)]
    exact CoreActualCyclicSlot.localFrame_le_of_not_bad 0 J F hbad i
  have hparam : z ∈ parameterSet R ((B : ℝ) ^ k) :=
    ⟨Set.mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right,
      CoreJointFrameLimit.frame] using hnorm, ⟨hθlo, hθhi.le⟩⟩
  have horder : orderStat F (J - 1) ≤ orderStat F J := by
    have hc := (mem_powersetCard.mp hF).2
    have hidx : J - 1 < F.card := by omega
    simpa only [Nat.sub_add_cancel hJ] using CoreLinearInsertion.orderStat_le_succ F hidx
  have hgap : (subsetGap F (J - 1) : ℝ) =
      ((CoreLinearInsertion.insertionSlot F J).2 : ℝ) - (CoreLinearInsertion.insertionSlot F J).1 := by
    unfold subsetGap
    rw [Nat.sub_add_cancel hJ, Nat.cast_sub horder, CoreLinearInsertion.insertionSlot_left,
      CoreLinearInsertion.insertionSlot_right F hJ]
  have hEA : E ⊆ Aset := fun u hu => (mem_openSlot.mp hu).1
  have hEΩ : E ⊆ CoreActualCyclicSlot.slot (offsetWindow S) F J := by
    intro u hu
    exact mem_openSlot.mpr ⟨corePresieveSurvivors_subset_Icc S σ (hEA hu), (mem_openSlot.mp hu).2⟩
  have hEin : ∀ u ∈ E, left < u ∧ (u : ℝ) - left < W * G := by
    intro u hu
    have hi : (CoreLinearInsertion.insertionSlot F J).1 < u ∧
        u < (CoreLinearInsertion.insertionSlot F J).2 := by
      simpa only [E, CoreActualCyclicSlot.slot, CoreLinearInsertion.insertionSlot,
        Nat.sub_add_cancel hJ] using (mem_openSlot.mp hu).2
    refine ⟨hi.1, ?_⟩
    have heq : W * G = ((CoreLinearInsertion.insertionSlot F J).2 : ℝ) - left := by
      dsimp only [W, left]
      rw [hgap, div_mul_cancel₀ _ hg.ne']
    rw [heq]
    have hh : (u : ℝ) < (CoreLinearInsertion.insertionSlot F J).2 := by exact_mod_cast hi.2
    linarith
  have hwidth : (((CoreLinearInsertion.insertionSlot F J).2 -
      (CoreLinearInsertion.insertionSlot F J).1 : ℕ) : ℝ) ≤ R * G := by
    have heq : (((CoreLinearInsertion.insertionSlot F J).2 -
        (CoreLinearInsertion.insertionSlot F J).1 : ℕ) : ℝ) = W * G := by
      have hnorder : (CoreLinearInsertion.insertionSlot F J).1 ≤ (CoreLinearInsertion.insertionSlot F J).2 := by
        simpa only [CoreLinearInsertion.insertionSlot_left, CoreLinearInsertion.insertionSlot_right F hJ] using horder
      rw [Nat.cast_sub hnorder]
      dsimp only [W]
      rw [hgap, div_mul_cancel₀ _ hg.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_right hWA hg.le
  have happrox : ∀ u ∈ E,
      actualTest B hk r (roundedCombination kind alpha b) L f (insert u F) ≤
        test (z, ((u : ℝ) - left) / G) := by
    intro u hu
    have hE : (CoreActualCyclicSlot.slot (offsetWindow S) F J).Nonempty := ⟨u, hEΩ hu⟩
    have hh := happG L J hJ hJL (offsetWindow S) F hE u (hEΩ hu) hwidth hθlo hθhi
    have hlow : (CoreLinearInsertion.insertionSlot F J).1 ≤ u := (hEin u hu).1.le
    have hWcast : (((CoreLinearInsertion.insertionSlot F J).2 -
        (CoreLinearInsertion.insertionSlot F J).1 : ℕ) : ℝ) / G = W := by
      have hnorder : (CoreLinearInsertion.insertionSlot F J).1 ≤ (CoreLinearInsertion.insertionSlot F J).2 := by
        simpa only [CoreLinearInsertion.insertionSlot_left, CoreLinearInsertion.insertionSlot_right F hJ] using horder
      rw [Nat.cast_sub hnorder, ← hgap]
    rw [hlabel, hWcast, Nat.cast_sub hlow] at hh
    have houter : O F = (selectedObservableOuter B hk r (roundedCombination kind alpha b)
        L J (offsetWindow S) F hE : Circle) := by simp only [O, outerMap, dif_pos hE]
    have hlead : leadingPairAction B hk alpha b a s W (((u : ℝ) - left) / G) =
        CoreRealPowerImageAC.action W a Acoef Ccoef (((u : ℝ) - left) / G) := rfl
    rw [hlead, ← houter] at hh
    have hdiff := (abs_le.mp hh).2
    have heq : test (z, ((u : ℝ) - left) / G) =
        f (O F + ((θ * CoreRealPowerImageAC.action W a Acoef Ccoef (((u : ℝ) - left) / G) : ℝ) : Circle)) + δ := by
      dsimp only [test, CoreRoundedReferenceMeasure.phase]
      rw [hpointWidth]
      rfl
    rw [heq]
    change f _ ≤ _
    dsimp only [θ]
    linarith
  have hsum : auxFrame_slotInsertSum Aset (J - 1)
      (corePositiveCutTest (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R
        (actualTest B hk r (roundedCombination kind alpha b) L f)) F ≤
      ∑ u ∈ E, test (z, ((u : ℝ) - left) / G) := by
    unfold auxFrame_slotInsertSum
    apply sum_le_sum
    intro u hu
    have hgood := (CoreActualCyclicSlot.not_frameBad_insert_iff 0 G R hJ hu).mpr hbad
    rw [corePositiveCutTest, if_neg hgood]
    exact happrox u hu
  have hSelberg := hselG z hparam left W E hW0 hWA hEin
    (coreLinear_presieveSubset_avoids σ hEA hfloor)
  have hraw : compactTest hR.le ha Acoef Ccoef f z =
      ∫ t in (0 : ℝ)..W, f (CoreRoundedReferenceMeasure.phase a Acoef Ccoef (z, t)) := by
    change CoreCompactFrameTest.rawTest R CoreJointFrameLimit.frame
      CoreRoundedReferenceMeasure.width
      (fun z t => CoreRoundedReferenceMeasure.phase a Acoef Ccoef (z, t)) f z = _
    have hh := CoreCompactFrameTest.rawTest_eq_fullIntegral_of_small CoreJointFrameLimit.frame
      CoreRoundedReferenceMeasure.width (fun z t => CoreRoundedReferenceMeasure.phase a Acoef Ccoef (z, t)) f z
      hnorm (by rwa [hpointWidth]) (by rwa [hpointWidth])
    simpa only [hpointWidth] using hh
  have hint : IntervalIntegrable (fun t => f (CoreRoundedReferenceMeasure.phase a Acoef Ccoef (z, t))) volume 0 W :=
    (f.continuous.comp ((CoreRoundedReferenceMeasure.continuous_phase ha Acoef Ccoef).comp
      (continuous_const.prodMk continuous_id))).intervalIntegrable 0 W
  have htestint : (∫ t in 0..W, test (z, t)) = compactTest hR.le ha Acoef Ccoef f z + δ * W := by
    rw [hraw]
    dsimp only [test]
    rw [intervalIntegral.integral_add hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [htestint] at hSelberg
  have herr : δ * W + ε / 2 ≤ ε := by
    have heq : δ * (R + 1) = ε / 2 := by
      dsimp only [δ]
      field_simp [(show 0 < R + 1 from by positivity).ne']
    have hh := mul_le_mul_of_nonneg_left hWA hδ.le
    nlinarith [hδ.le]
  exact (hsum.trans hSelberg).trans (mul_le_mul_of_nonneg_left (by linarith) hfactor)

end
end PrimeGapNormality.Prime.CoreRoundedModelFinite
