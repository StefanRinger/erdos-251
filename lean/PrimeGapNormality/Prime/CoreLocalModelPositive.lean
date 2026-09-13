import PrimeGapNormality.Prime.CoreCyclicScaledSlot
import PrimeGapNormality.Prime.CoreCompactPolynomialInsertion
import PrimeGapNormality.Prime.CoreCompactFrameTest
import PrimeGapNormality.Prime.CoreLinearModelMean

/-!
# Actual positive local-polynomial slot estimate

This file discharges the generic slot-majorant input of
`CorePositiveRootFrameAssembly`.  The original fixed-deletion cutoff is
kept inside `corePositiveCutTest`. Bad frames therefore contribute zero
before auxiliary reweighting; on good frames the exact ordered cyclic phase
is fed to the proved compact-family Selberg insertion theorem.
-/

namespace PrimeGapNormality.Prime.CoreLocalModelPositive

open Finset Filter MeasureTheory
open scoped BigOperators Classical Topology Polynomial BoundedContinuousFunction NNReal

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)
abbrev Joint (w : ℕ) := CoreJointFrameLimit.Joint (2 * w + 1)

/-- Actual bounded positive configuration test on the first `K` cyclic
local-polynomial emissions. -/
def actualTest
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (K : ℕ) (f : Circle →ᵇ ℝ)
    (U : Finset ℕ) : ℝ :=
  f ((CoreActualCyclicSlot.actualFinitePhase B hk r P K U : ℝ) : Circle)

/-- Canonical outer circle phase.  The ambient carrier is the full offset
window, so every nonempty exposed-presieve slot uses the same frame-only
choice. -/
def outerPhase
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (K w J : ℕ)
    (Ω F : Finset ℕ) : Circle :=
  if hE : (CoreActualCyclicSlot.slot Ω F J).Nonempty then
    ((CoreActualCyclicSlot.selectedOuter B hk r P K w J Ω F hE : ℝ) : Circle)
  else 0

/-- Continuous central normalized insertion width on the joint space. -/
def jointWidth (w : ℕ) (z : Joint w) : ℝ :=
  CoreJointFrameLimit.frame z (CoreCyclicScaledSlot.centralIndex w)

/-- Compact normalized polynomial phase on the joint space. -/
def jointPhase
    (w d : ℕ) (p : CoreCyclic.OnePoint.SignedPoly) (γ : ℝ)
    (z : Joint w) (t : ℝ) : Circle :=
  z.1 + (((CoreJointFrameLimit.scale z) *
    Polynomial.eval t
      (CoreCyclicScaledSlot.normalizedActionFamily w d p
        (γ, CoreJointFrameLimit.frame z)) : ℝ) : Circle)

theorem continuous_jointWidth (w : ℕ) : Continuous (jointWidth w) :=
  (continuous_apply (CoreCyclicScaledSlot.centralIndex w)).comp
    CoreJointFrameLimit.continuous_frame

theorem continuous_jointPhase_uncurry
    (w d : ℕ) (p : CoreCyclic.OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (γ : ℝ) : Continuous (jointPhase w d p γ).uncurry := by
  have harg : Continuous fun z : Joint w × ℝ ↦
      ((γ, CoreJointFrameLimit.frame z.1), z.2) := by
    exact (continuous_const.prodMk
      (CoreJointFrameLimit.continuous_frame.comp continuous_fst)).prodMk
        continuous_snd
  have heval : Continuous fun z : Joint w × ℝ ↦
      Polynomial.eval z.2
        (CoreCyclicScaledSlot.normalizedActionFamily w d p
          (γ, CoreJointFrameLimit.frame z.1)) :=
    (CoreCyclicScaledSlot.continuous_normalizedActionFamily_eval w d p hd).comp harg
  unfold jointPhase Function.uncurry
  have hscaled : Continuous fun z : Joint w × ℝ ↦
      CoreJointFrameLimit.scale z.1 *
        Polynomial.eval z.2
          (CoreCyclicScaledSlot.normalizedActionFamily w d p
            (γ, CoreJointFrameLimit.frame z.1)) :=
    (CoreJointFrameLimit.continuous_scale.comp continuous_fst).mul heval
  exact (continuous_fst.comp continuous_fst).add
    ((AddCircle.continuous_mk' (1 : ℝ)).comp hscaled)

/-- Bounded continuous compact-frame insertion integral used for weak
passage. -/
def compactInsertionTest
    {R : ℝ} (hR : 0 ≤ R) (w d : ℕ) (p : CoreCyclic.OnePoint.SignedPoly)
    (hd : p.totalDegree ≤ d) (γ : ℝ) (f : Circle →ᵇ ℝ) :
    Joint w →ᵇ ℝ :=
  CoreCompactFrameTest.boundedTest hR
    CoreJointFrameLimit.frame (jointWidth w) (jointPhase w d p γ)
    CoreJointFrameLimit.continuous_frame (continuous_jointWidth w)
    (continuous_jointPhase_uncurry w d p hd γ) f

theorem compactInsertionTest_apply
    {R : ℝ} (hR : 0 ≤ R) (w d : ℕ) (p : CoreCyclic.OnePoint.SignedPoly)
    (hd : p.totalDegree ≤ d) (γ : ℝ) (f : Circle →ᵇ ℝ)
    (z : Joint w) :
    compactInsertionTest hR w d p hd γ f z =
      CoreCompactFrameTest.rawTest R CoreJointFrameLimit.frame
        (jointWidth w) (jointPhase w d p γ) f z :=
  rfl

private theorem localFrame_norm_le
    (w J : ℕ) {G R : ℝ} (hG : 0 < G) (hR : 0 ≤ R)
    (F : Finset ℕ)
    (hgood : ¬ ∃ q ∈ CoreCyclic.OnePoint.FiniteExterior.frameRanks w J,
      R < (subsetGap F q : ℝ) / G) :
    ‖CoreActualFrameJoint.localFrame w J G F‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).2
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg
    (CoreActualFrameJoint.localFrame_nonneg w J hG.le F i)]
  exact CoreActualCyclicSlot.localFrame_le_of_not_bad w J F hgood i

private theorem frame_point_parameter_mem
    (w J : ℕ) {G R : ℝ} (hG1 : 1 ≤ G) (hR : 0 ≤ R)
    (F : Finset ℕ)
    (hgood : ¬ ∃ q ∈ CoreCyclic.OnePoint.FiniteExterior.frameRanks w J,
      R < (subsetGap F q : ℝ) / G) :
    (G⁻¹, CoreActualFrameJoint.localFrame w J G F) ∈
      CoreCyclicScaledSlot.parameterSet w R := by
  constructor
  · exact ⟨inv_nonneg.mpr (zero_le_one.trans hG1), inv_le_one_of_one_le₀ hG1⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact localFrame_norm_le w J (zero_lt_one.trans_le hG1) hR F hgood

private theorem presieve_slot_subset_offset
    (S : ℕ) (σ : ResidueChoice S) (F : Finset ℕ) (J : ℕ) :
    CoreActualCyclicSlot.slot (presieveSurvivors S σ) F J ⊆
      CoreActualCyclicSlot.slot (offsetWindow S) F J := by
  intro u hu
  apply mem_openSlot.mpr
  exact ⟨by simpa only [offsetWindow] using
      corePresieveSurvivors_subset_Icc S σ (mem_openSlot.mp hu).1,
    (mem_openSlot.mp hu).2⟩

private theorem actual_phase_eq_jointPhase
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (K w J d : ℕ)
    (hwJ : w + 1 ≤ J) (hJK : J < K)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (CoreCyclic.OnePoint.action B hk w
      (CoreCyclic.phaseAt hk r (J - 1)) P).totalDegree ≤ d)
    (S : ℕ) (σ : ResidueChoice S) (F : Finset ℕ)
    {G : ℝ} (hG : G ≠ 0) {u : ℕ}
    (hu : u ∈ CoreActualCyclicSlot.slot (presieveSurvivors S σ) F J) :
    ((CoreActualCyclicSlot.actualFinitePhase B hk r P K (insert u F) : ℝ) : Circle) =
      jointPhase w d
        (CoreCyclic.OnePoint.action B hk w
          (CoreCyclic.phaseAt hk r (J - 1)) P) G⁻¹
        (CoreActualFrameJoint.jointPoint w J G
          (G ^ d / (B : ℝ) ^ (J + 1))
          (outerPhase B hk r P K w J (offsetWindow S)) F)
        (((u : ℝ) - (CoreLinearInsertion.insertionSlot F J).1) / G) := by
  have huΩ := presieve_slot_subset_offset S σ F J hu
  have hEΩ : (CoreActualCyclicSlot.slot (offsetWindow S) F J).Nonempty := ⟨u, huΩ⟩
  have hreal := CoreCyclicScaledSlot.actualFinitePhase_eq_scaledFamily
    hB hk r P K w J d hwJ hJK hw hd (offsetWindow S) F hEΩ hG huΩ
  have hcircle := congrArg (fun x : ℝ ↦ (x : Circle)) hreal
  unfold jointPhase CoreActualFrameJoint.jointPoint
    CoreJointFrameLimit.scale CoreJointFrameLimit.frame
  rw [outerPhase, dif_pos hEΩ]
  simpa only [AddCircle.coe_add] using hcircle

/-! ## The actual good-frame Selberg slot bound -/

/-- The generic `hslot` premise is discharged for the actual cyclic test.
The right side is the bounded continuous compact-frame insertion test plus
the explicit fixed Selberg error. -/
theorem eventually_presieve_slot_sum_le_compactTest
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (w d : ℕ) (s : Fin k)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (CoreCyclic.OnePoint.action B hk w s P).totalDegree ≤ d)
    {R : ℝ} (hR : 0 < R)
    (f : Circle →ᵇ ℝ) {Kf : ℝ≥0} (hKf : LipschitzWith Kf f)
    (hf0 : ∀ x, 0 ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ G : ℝ in atTop,
      ∀ (K J S L n : ℕ) (σ : ResidueChoice S) (F : Finset ℕ),
      w + 1 ≤ J → J < K → CoreCyclic.phaseAt hk r (J - 1) = s →
      1 ≤ G → ⌊G⌋₊ ≤ S → J < L → L ≤ n →
      F ∈ (presieveSurvivors S σ).powersetCard (n - 1) →
      1 ≤ G ^ d / (B : ℝ) ^ (J + 1) →
      G ^ d / (B : ℝ) ^ (J + 1) ≤ (B : ℝ) ^ k →
      auxFrame_slotInsertSum (presieveSurvivors S σ) (J - 1)
          (corePositiveCutTest
            (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J) (J - 1) G R
            (actualTest B hk r P K f)) F ≤
        3 * G / Real.log G *
          (compactInsertionTest hR.le w d
            (CoreCyclic.OnePoint.action B hk w s P) hd G⁻¹ f
            (CoreActualFrameJoint.jointPoint w J G
              (G ^ d / (B : ℝ) ^ (J + 1))
              (outerPhase B hk r P K w J (offsetWindow S)) F) + ε) := by
  let p := CoreCyclic.OnePoint.action B hk w s P
  have hCθ : 0 ≤ (B : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) _
  filter_upwards [CoreCompactPolynomialInsertion.eventually_positive_polynomial_insertion
    (CoreCyclicScaledSlot.normalizedActionFamily w d p)
    (CoreCyclicScaledSlot.parameterSet_compact w R) d
    (fun y _ ↦ CoreCyclicScaledSlot.normalizedActionFamily_natDegree_le w d p hd y)
    (fun m ↦ (CoreCyclicScaledSlot.continuous_normalizedActionFamily_coeff
      w d p m).continuousOn)
    hR hCθ f hKf hf0 hε,
    eventually_gt_atTop (1 : ℝ)] with G hsel hGgt
  intro K J S L n σ F hwJ hJK hlabel hG1 hfloor hJL hLn hF hθlo hθhi
  let A := presieveSurvivors S σ
  let E := CoreActualCyclicSlot.slot A F J
  let Ω := offsetWindow S
  let O := outerPhase B hk r P K w J Ω F
  let θ := G ^ d / (B : ℝ) ^ (J + 1)
  let Y := CoreActualFrameJoint.localFrame w J G F
  let W := (subsetGap F (J - 1) : ℝ) / G
  let a := (CoreLinearInsertion.insertionSlot F J).1
  have hG0 : 0 < G := zero_lt_one.trans hGgt
  have hJ : 1 ≤ J := by omega
  have hFm := mem_powersetCard.mp hF
  have hEA : E ⊆ A := fun u hu ↦ (mem_openSlot.mp hu).1
  have havoid : CoreSelberg.AvoidsResidues E ⌊G⌋₊ :=
    coreLinear_presieveSubset_avoids σ hEA hfloor
  have hW0 : 0 ≤ W := div_nonneg (Nat.cast_nonneg _) hG0.le
  have horder : orderStat F (J - 1) ≤ orderStat F J := by
    have hn1 : 1 ≤ n := by omega
    have hFcard : F.card = n - 1 := hFm.2
    have hJn : J < n := hJL.trans_le hLn
    have hJcard : J - 1 < F.card := by omega
    simpa [Nat.sub_add_cancel hJ] using
      CoreLinearInsertion.orderStat_le_succ F hJcard
  have hgap : (subsetGap F (J - 1) : ℝ) =
      ((CoreLinearInsertion.insertionSlot F J).2 : ℝ) -
        (CoreLinearInsertion.insertionSlot F J).1 := by
    unfold subsetGap
    rw [Nat.sub_add_cancel hJ, Nat.cast_sub horder,
      CoreLinearInsertion.insertionSlot_left,
      CoreLinearInsertion.insertionSlot_right F hJ]
  have hEin : ∀ u ∈ E, a < u ∧ (u : ℝ) - a < W * G := by
    intro u hu
    have hus := (mem_openSlot.mp hu).2
    have huSlot :
        (CoreLinearInsertion.insertionSlot F J).1 < u ∧
          u < (CoreLinearInsertion.insertionSlot F J).2 := by
      simpa [E, A, CoreActualCyclicSlot.slot,
        CoreLinearInsertion.insertionSlot] using hus
    refine ⟨by simpa [a] using huSlot.1, ?_⟩
    have hwidth : W * G =
        ((CoreLinearInsertion.insertionSlot F J).2 : ℝ) -
          (CoreLinearInsertion.insertionSlot F J).1 := by
      dsimp only [W]
      rw [hgap, div_mul_cancel₀ _ hG0.ne']
    rw [hwidth]
    have hur : (u : ℝ) < (CoreLinearInsertion.insertionSlot F J).2 := by
      exact_mod_cast huSlot.2
    dsimp only [a]
    linarith
  by_cases hbad : ∃ q ∈ CoreCyclic.OnePoint.FiniteExterior.frameRanks w J,
      R < (subsetGap F q : ℝ) / G
  · have hzero : ∀ u ∈ E,
        corePositiveCutTest
          (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J) (J - 1) G R
          (actualTest B hk r P K f) (insert u F) = 0 := by
      intro u hu
      have hbadU : corePositiveFrameBad
          (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J) (J - 1) G R
          (insert u F) := by
        by_contra hgoodU
        exact (CoreActualCyclicSlot.not_frameBad_insert_iff w G R hJ hu).1
          hgoodU hbad
      simp [corePositiveCutTest, hbadU]
    unfold auxFrame_slotInsertSum
    change (∑ u ∈ E, _) ≤ _
    rw [sum_eq_zero hzero]
    have hraw0 := (CoreCompactFrameTest.rawTest_nonneg_le_fullIntegral
      hR.le CoreJointFrameLimit.frame (jointWidth w) (jointPhase w d p G⁻¹)
      (continuous_jointPhase_uncurry w d p hd G⁻¹) f hf0
      (CoreActualFrameJoint.jointPoint w J G θ
        (outerPhase B hk r P K w J Ω) F)
      (CoreActualFrameJoint.localFrame_nonneg w J hG0.le F
        (CoreCyclicScaledSlot.centralIndex w))).1
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) hG0.le) (Real.log_pos hGgt).le)
      (add_nonneg (by simpa [compactInsertionTest_apply, p, θ, Ω] using hraw0) hε.le)
  · have hparam : (G⁻¹, Y) ∈ CoreCyclicScaledSlot.parameterSet w R :=
      frame_point_parameter_mem w J hG1 hR.le F hbad
    have hWA : W ≤ R :=
      CoreActualCyclicSlot.centralWidth_le_of_not_bad w J hJ F hbad
    have hYnorm : ‖Y‖ ≤ R := localFrame_norm_le w J hG0 hR.le F hbad
    have hpointWidth : jointWidth w
        (CoreActualFrameJoint.jointPoint w J G θ
          (outerPhase B hk r P K w J Ω) F) = W := by
      unfold jointWidth
      rw [CoreActualFrameJoint.jointPoint_frame,
        CoreCyclicScaledSlot.localFrame_centralIndex w J hJ]
    have hraw : compactInsertionTest hR.le w d p hd G⁻¹ f
        (CoreActualFrameJoint.jointPoint w J G θ
          (outerPhase B hk r P K w J Ω) F) =
        ∫ t in (0 : ℝ)..W,
          f (jointPhase w d p G⁻¹
            (CoreActualFrameJoint.jointPoint w J G θ
              (outerPhase B hk r P K w J Ω) F) t) := by
      rw [compactInsertionTest_apply]
      have hraw' := CoreCompactFrameTest.rawTest_eq_fullIntegral_of_small
        CoreJointFrameLimit.frame (jointWidth w) (jointPhase w d p G⁻¹) f
        (CoreActualFrameJoint.jointPoint w J G θ
          (outerPhase B hk r P K w J Ω) F)
        (by simpa only [CoreActualFrameJoint.jointPoint_frame, Y] using hYnorm)
        (by simpa only [hpointWidth] using hW0)
        (by simpa only [hpointWidth] using hWA)
      simpa only [hpointWidth] using hraw'
    have hmain := hsel (G⁻¹, Y) hparam O θ ⟨hθlo, hθhi⟩ a W E
      hW0 hWA hEin havoid
    have hsum : auxFrame_slotInsertSum A (J - 1)
          (corePositiveCutTest
            (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J) (J - 1) G R
            (actualTest B hk r P K f)) F =
        ∑ u ∈ E, f (jointPhase w d p G⁻¹
          (CoreActualFrameJoint.jointPoint w J G θ
            (outerPhase B hk r P K w J Ω) F)
          (((u : ℝ) - a) / G)) := by
      unfold auxFrame_slotInsertSum
      change (∑ u ∈ E, _) = _
      apply sum_congr rfl
      intro u hu
      have hgoodU : ¬corePositiveFrameBad
          (CoreCyclic.OnePoint.FiniteExterior.frameRanks w J) (J - 1) G R
          (insert u F) :=
        (CoreActualCyclicSlot.not_frameBad_insert_iff w G R hJ hu).2 hbad
      rw [corePositiveCutTest, if_neg hgoodU]
      unfold actualTest
      have hdJ : (CoreCyclic.OnePoint.action B hk w
          (CoreCyclic.phaseAt hk r (J - 1)) P).totalDegree ≤ d := by
        simpa only [hlabel] using hd
      have hid := congrArg f (actual_phase_eq_jointPhase hB hk r P K w J d
        hwJ hJK hw hdJ S σ F hG0.ne' hu)
      simpa only [p, hlabel] using hid
    rw [hsum, hraw]
    simpa [p, O, θ, Y, W, a, jointPhase,
      CoreActualFrameJoint.jointPoint, CoreJointFrameLimit.frame,
      CoreJointFrameLimit.scale] using hmain

end

end PrimeGapNormality.Prime.CoreLocalModelPositive
