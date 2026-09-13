import PrimeGapNormality.Prime.CoreRoundedModelSubsequence
import PrimeGapNormality.Prime.CoreIntegerGapDTransfer

/-!
# Deterministically scaled integer gap observables

This module isolates exactly the deterministic input needed by the rounded
model argument.  An integer observable `F` has a compact leading scaling if

`G⁻ᵃ F_s(q) → b_s (q/G)^a`

uniformly for every fixed compact range `q ≤ A G`.  This is not a model or
normality assumption: it is a pointwise assertion about the explicit
integer function.  `CoreRoundedPolynomialScaling` proves it for polynomial
compositions of actual floors and ceilings.

From this input we prove the actual ordered-slot approximation.  The
remaining probability law, deletion cutoff, Selberg insertion and weak
reference passage are the same genuine finite-root objects as in the
rounded-linear proof.
-/

namespace PrimeGapNormality.Prime.CoreScaledGapModelReference

open Finset Filter MeasureTheory CoreCyclic
open CoreIntegerGapInsertion CoreRoundedModelFinite CoreLocalModelMixture
open CoreRoundedModelSubsequence
open scoped Topology Classical NNReal BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 1500000

abbrev Circle := AddCircle (1 : ℝ)
abbrev Joint := CoreJointFrameLimit.Joint 1

/-- Genuine compact scaling property of a deterministic integer
observable. -/
def CompactScaling {k : ℕ} (F : Fin k → ℕ → ℤ)
    (a : ℝ) (b : Fin k → ℤ) : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∀ ε : ℝ, 0 < ε → ∀ᶠ G : ℝ in atTop,
    ∀ s : Fin k, ∀ q : ℕ, (q : ℝ) ≤ A * G →
      |G ^ (-a) * (F s q : ℝ) - (b s : ℝ) * ((q : ℝ) / G) ^ a| < ε

/-- Continuous leading action of the two adjacent gaps. -/
def leadingPairAction (B : ℕ) {k : ℕ} (hk : 0 < k)
    (a : ℝ) (b : Fin k → ℤ) (s : Fin k) (W z : ℝ) : ℝ :=
  (B : ℝ) * (b s : ℝ) * z ^ a +
    (b (cyclicSucc hk s) : ℝ) * (W - z) ^ a

private theorem pairActionInt_cast
    (B : ℕ) {k : ℕ} (hk : 0 < k) (F : Fin k → ℕ → ℤ)
    (s : Fin k) (left right : ℕ) :
    (pairActionInt B hk s F left right : ℝ) =
      (B : ℝ) * (F s left : ℝ) + (F (cyclicSucc hk s) right : ℝ) := by
  unfold pairActionInt
  push_cast
  ring

private theorem scale_cancel {G a : ℝ} (hG : 0 < G) :
    G ^ a * G ^ (-a) = 1 := by
  rw [← Real.rpow_add hG]
  simp

/-- Compact scaling gives the uniform approximation of the exact integer
pair action. -/
theorem eventually_pairAction_scaled_approx
    {k : ℕ} (F : Fin k → ℕ → ℤ) {a : ℝ} (b : Fin k → ℤ)
    (ha : 0 < a) (hscale : CompactScaling F a b)
    {A : ℝ} (hA : 0 ≤ A) {B : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ G : ℝ in atTop,
      ∀ s : Fin k, ∀ left right j : ℕ,
        (((left + right : ℕ) : ℝ) ≤ A * G) →
        1 ≤ G ^ a / (B : ℝ) ^ (j + 1) →
        G ^ a / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k →
        |(pairActionInt B hk s F left right : ℝ) / (B : ℝ) ^ (j + 1) -
          (G ^ a / (B : ℝ) ^ (j + 1)) *
            leadingPairAction B hk a b s
              (((left + right : ℕ) : ℝ) / G) ((left : ℝ) / G)| < ε := by
  intro ε hε
  let M : ℝ := (B : ℝ) ^ k * ((B : ℝ) + 1)
  have hM : 0 < M := by dsimp only [M]; positivity
  let δ := ε / M
  have hδ : 0 < δ := div_pos hε hM
  filter_upwards [hscale A hA δ hδ, eventually_gt_atTop (0 : ℝ)] with G happ hG
  intro s left right j hwidth hlo hhi
  have hleft : (left : ℝ) ≤ A * G :=
    (Nat.cast_le.mpr (by omega : left ≤ left + right)).trans hwidth
  have hright : (right : ℝ) ≤ A * G :=
    (Nat.cast_le.mpr (by omega : right ≤ left + right)).trans hwidth
  have hu := happ s left hleft
  have hv := happ (cyclicSucc hk s) right hright
  let θ := G ^ a / (B : ℝ) ^ (j + 1)
  let eu := G ^ (-a) * (F s left : ℝ) - (b s : ℝ) * ((left : ℝ) / G) ^ a
  let ev := G ^ (-a) * (F (cyclicSucc hk s) right : ℝ) -
    (b (cyclicSucc hk s) : ℝ) * ((right : ℝ) / G) ^ a
  have heu : |eu| < δ := by simpa only [eu] using hu
  have hev : |ev| < δ := by simpa only [ev] using hv
  have hθ0 : 0 ≤ θ := zero_le_one.trans (by simpa only [θ] using hlo)
  have hθhi : θ < (B : ℝ) ^ k := by simpa only [θ] using hhi
  have hcoord : (((left + right : ℕ) : ℝ) / G) - (left : ℝ) / G =
      (right : ℝ) / G := by push_cast; ring
  have hscaled :
      (pairActionInt B hk s F left right : ℝ) / (B : ℝ) ^ (j + 1) =
        θ * ((B : ℝ) * (G ^ (-a) * (F s left : ℝ)) +
          G ^ (-a) * (F (cyclicSucc hk s) right : ℝ)) := by
    rw [pairActionInt_cast]
    dsimp only [θ]
    have hc := scale_cancel hG (a := a)
    have hden : (B : ℝ) ^ (j + 1) ≠ 0 := by positivity
    calc
      ((B : ℝ) * (F s left : ℝ) + (F (cyclicSucc hk s) right : ℝ)) /
          (B : ℝ) ^ (j + 1) =
        (G ^ a / (B : ℝ) ^ (j + 1)) *
          (G ^ (-a) * ((B : ℝ) * (F s left : ℝ) +
            (F (cyclicSucc hk s) right : ℝ))) := by
              field_simp [hden]
              rw [mul_assoc, hc, mul_one]
      _ = (G ^ a / (B : ℝ) ^ (j + 1)) *
          ((B : ℝ) * (G ^ (-a) * (F s left : ℝ)) +
            G ^ (-a) * (F (cyclicSucc hk s) right : ℝ)) := by ring
  have herr :
      (pairActionInt B hk s F left right : ℝ) / (B : ℝ) ^ (j + 1) -
        θ * leadingPairAction B hk a b s
          (((left + right : ℕ) : ℝ) / G) ((left : ℝ) / G) =
      θ * ((B : ℝ) * eu + ev) := by
    rw [hscaled]
    unfold leadingPairAction
    rw [hcoord]
    dsimp only [eu, ev]
    ring
  rw [herr, abs_mul, abs_of_nonneg hθ0]
  have hinner : |(B : ℝ) * eu + ev| < ((B : ℝ) + 1) * δ := by
    calc
      |(B : ℝ) * eu + ev| ≤ |(B : ℝ) * eu| + |ev| := abs_add_le _ _
      _ = (B : ℝ) * |eu| + |ev| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg B)]
      _ < (B : ℝ) * δ + δ :=
        add_lt_add (mul_lt_mul_of_pos_left heu (by positivity)) hev
      _ = ((B : ℝ) + 1) * δ := by ring
  calc
    θ * |(B : ℝ) * eu + ev| < θ * (((B : ℝ) + 1) * δ) :=
      mul_lt_mul_of_pos_left hinner (zero_lt_one.trans_le hlo)
    _ < (B : ℝ) ^ k * (((B : ℝ) + 1) * δ) :=
      mul_lt_mul_of_pos_right hθhi (by positivity)
    _ = ε := by dsimp only [δ, M]; field_simp [hM.ne']

/-- Phase-test form on the actual ordered insertion slot. -/
theorem eventually_actualPhase_test_approx
    {k : ℕ} (F : Fin k → ℕ → ℤ) {a : ℝ} (b : Fin k → ℤ)
    (ha : 0 < a) (hscale : CompactScaling F a b)
    {A : ℝ} (hA : 0 ≤ A) {B : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ G : ℝ in atTop,
      ∀ L j : ℕ, 1 ≤ j → j < L → ∀ Aset frame : Finset ℕ,
      ∀ hE : (CoreActualCyclicSlot.slot Aset frame j).Nonempty,
      ∀ u ∈ CoreActualCyclicSlot.slot Aset frame j,
      (((CoreLinearInsertion.insertionSlot frame j).2 -
          (CoreLinearInsertion.insertionSlot frame j).1 : ℕ) : ℝ) ≤ A * G →
      1 ≤ G ^ a / (B : ℝ) ^ (j + 1) →
      G ^ a / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k →
      |f (actualFiniteObservablePhase B hk r F L (insert u frame) : Circle) -
        f ((selectedObservableOuter B hk r F L j Aset frame hE : Circle) +
          (((G ^ a / (B : ℝ) ^ (j + 1)) *
            leadingPairAction B hk a b (phaseAt hk r (j - 1))
              ((((CoreLinearInsertion.insertionSlot frame j).2 -
                (CoreLinearInsertion.insertionSlot frame j).1 : ℕ) : ℝ) / G)
              (((u - (CoreLinearInsertion.insertionSlot frame j).1 : ℕ) : ℝ) / G) : ℝ) :
            Circle))| ≤ K * ε := by
  intro ε hε
  filter_upwards [eventually_pairAction_scaled_approx F b ha hscale hA hB hk ε hε,
    eventually_gt_atTop (0 : ℝ)] with G happ hG
  intro L j hj hjL Aset frame hE u hu hwidth hlo hhi
  have hs := (mem_openSlot.mp hu).2
  have hleft : (CoreLinearInsertion.insertionSlot frame j).1 ≤ u := hs.1.le
  have hright : u ≤ (CoreLinearInsertion.insertionSlot frame j).2 := hs.2.le
  let ql := u - (CoreLinearInsertion.insertionSlot frame j).1
  let qr := (CoreLinearInsertion.insertionSlot frame j).2 - u
  have hsum : ql + qr = (CoreLinearInsertion.insertionSlot frame j).2 -
      (CoreLinearInsertion.insertionSlot frame j).1 := by dsimp only [ql, qr]; omega
  have hp := happ (phaseAt hk r (j - 1)) ql qr j
    (by simpa only [hsum] using hwidth) hlo hhi
  have hphase := actualFiniteObservablePhase_eq_outer_add hB hk r F hj hjL
    Aset frame hE hu
  have hphaseCircle := congrArg (fun x : ℝ ↦ (x : Circle)) hphase
  simp only [AddCircle.coe_add] at hphaseCircle
  rw [hphaseCircle]
  have ht := CoreRoundedSlotApproximation.lipschitz_circleTest_add_error f hK
    (selectedObservableOuter B hk r F L j Aset frame hE)
    ((pairActionInt B hk (phaseAt hk r (j - 1)) F ql qr : ℝ) /
      (B : ℝ) ^ (j + 1))
    ((G ^ a / (B : ℝ) ^ (j + 1)) *
      leadingPairAction B hk a b (phaseAt hk r (j - 1))
        (((ql + qr : ℕ) : ℝ) / G) ((ql : ℝ) / G))
  have hh := ht.trans (mul_le_mul_of_nonneg_left hp.le K.coe_nonneg)
  rw [hsum] at hh
  simpa only [ql, qr] using hh

/-- Actual Selberg slot estimate for a deterministically scaled observable.
It is uniform in every later rank, presieve, retained frame and insertion
location. -/
theorem eventually_slot_sum_le
    {k : ℕ} (Fobs : Fin k → ℕ → ℤ) {a : ℝ} (b : Fin k → ℤ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hscale : CompactScaling Fobs a b)
    {R : ℝ} (hR : 0 < R) {B : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r s : Fin k) (f : Circle →ᵇ ℝ) {Kf : ℝ≥0}
    (hKf : LipschitzWith Kf f) (hf : ∀ x, 0 ≤ f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ G : ℝ in atTop, ∀ (L J S n : ℕ) (σ : ResidueChoice S) (frame : Finset ℕ),
      1 ≤ J → J < L → phaseAt hk r (J - 1) = s → ⌊G⌋₊ ≤ S → L ≤ n →
      frame ∈ (presieveSurvivors S σ).powersetCard (n - 1) →
      1 ≤ G ^ a / (B : ℝ) ^ (J + 1) →
      G ^ a / (B : ℝ) ^ (J + 1) < (B : ℝ) ^ k →
      auxFrame_slotInsertSum (presieveSurvivors S σ) (J - 1)
        (corePositiveCutTest (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R
          (actualTest B hk r Fobs L f)) frame ≤
        3 * G / Real.log G *
          (compactTest hR.le ha ((B : ℝ) * (b s : ℝ))
            (b (cyclicSucc hk s) : ℝ) f
            (CoreActualFrameJoint.jointPoint 0 J G (G ^ a / (B : ℝ) ^ (J + 1))
              (outerMap B hk r Fobs L J S) frame) + ε) := by
  let Acoef := (B : ℝ) * (b s : ℝ)
  let Ccoef := (b (cyclicSucc hk s) : ℝ)
  let δ := ε / (2 * (R + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let q := δ / ((Kf : ℝ) + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hKq : (Kf : ℝ) * q ≤ δ := by
    have heq : ((Kf : ℝ) + 1) * q = δ := by
      dsimp only [q]
      field_simp [(show 0 < (Kf : ℝ) + 1 from by positivity).ne']
    nlinarith [Kf.coe_nonneg, hq.le]
  let test := fun z : Joint × ℝ =>
    f (CoreRoundedReferenceMeasure.phase a Acoef Ccoef z) + δ
  have htestc : Continuous test := (f.continuous.comp
    (CoreRoundedReferenceMeasure.continuous_phase ha Acoef Ccoef)).add continuous_const
  have htest0 : ∀ z : Joint, ∀ t : ℝ, 0 ≤ test (z, t) :=
    fun z t => add_nonneg (hf _) hδ.le
  have hsel := CoreCompactContinuousInsertion.eventually_positive_insertion
    (parameterSet R ((B : ℝ) ^ k)) (parameterSet_compact R ((B : ℝ) ^ k))
    test hR htestc.continuousOn (fun z hz t ht => htest0 z t)
    (show 0 < ε / 2 by positivity)
  have happ := eventually_actualPhase_test_approx Fobs b ha hscale hR.le
    hB hk r f hKf q hq
  filter_upwards [hsel, happ, eventually_gt_atTop (1 : ℝ)] with G hselG happG hG
  intro L J S n σ frame hJ hJL hlabel hfloor hLn hframe
    hθlo hθhi
  let Aset := presieveSurvivors S σ
  let E := CoreActualCyclicSlot.slot Aset frame J
  let O := outerMap B hk r Fobs L J S
  let θ := G ^ a / (B : ℝ) ^ (J + 1)
  let z := CoreActualFrameJoint.jointPoint 0 J G θ O frame
  let W := (subsetGap frame (J - 1) : ℝ) / G
  let left := (CoreLinearInsertion.insertionSlot frame J).1
  have hg : 0 < G := zero_lt_one.trans hG
  have hW0 : 0 ≤ W := div_nonneg (Nat.cast_nonneg _) hg.le
  have hpointWidth : CoreRoundedReferenceMeasure.width z = W :=
    point_width J hJ G θ O frame
  have hnonneg : 0 ≤ compactTest hR.le ha Acoef Ccoef f z :=
    compactTest_nonneg hR.le ha Acoef Ccoef f hf z (by rwa [hpointWidth])
  have hfactor : 0 ≤ 3 * G / Real.log G :=
    div_nonneg (by positivity) (Real.log_pos hG).le
  by_cases hbad : ∃ i ∈ OnePoint.FiniteExterior.frameRanks 0 J,
      R < (subsetGap frame i : ℝ) / G
  · have hz : ∀ u ∈ E,
        corePositiveCutTest (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R
          (actualTest B hk r Fobs L f) (insert u frame) = 0 := by
      intro u hu
      have hb' : corePositiveFrameBad (OnePoint.FiniteExterior.frameRanks 0 J)
          (J - 1) G R (insert u frame) := by
        by_contra hn
        exact ((CoreActualCyclicSlot.not_frameBad_insert_iff 0 G R hJ hu).mp hn) hbad
      simp only [corePositiveCutTest, if_pos hb']
    unfold auxFrame_slotInsertSum
    change (∑ u ∈ E, _) ≤ _
    rw [sum_eq_zero hz]
    exact mul_nonneg hfactor (add_nonneg hnonneg hε.le)
  have hWA : W ≤ R :=
    CoreActualCyclicSlot.centralWidth_le_of_not_bad 0 J hJ frame hbad
  have hnorm : ‖CoreJointFrameLimit.frame z‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR.le).2
    intro i
    change ‖CoreActualFrameJoint.localFrame 0 J G frame i‖ ≤ R
    rw [Real.norm_eq_abs,
      abs_of_nonneg (CoreActualFrameJoint.localFrame_nonneg 0 J hg.le frame i)]
    exact CoreActualCyclicSlot.localFrame_le_of_not_bad 0 J frame hbad i
  have hparam : z ∈ parameterSet R ((B : ℝ) ^ k) :=
    ⟨Set.mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right,
      CoreJointFrameLimit.frame] using hnorm,
      ⟨hθlo, hθhi.le⟩⟩
  have horder : orderStat frame (J - 1) ≤ orderStat frame J := by
    have hc := (mem_powersetCard.mp hframe).2
    have hidx : J - 1 < frame.card := by omega
    simpa only [Nat.sub_add_cancel hJ] using
      CoreLinearInsertion.orderStat_le_succ frame hidx
  have hgap : (subsetGap frame (J - 1) : ℝ) =
      ((CoreLinearInsertion.insertionSlot frame J).2 : ℝ) -
        (CoreLinearInsertion.insertionSlot frame J).1 := by
    unfold subsetGap
    rw [Nat.sub_add_cancel hJ, Nat.cast_sub horder,
      CoreLinearInsertion.insertionSlot_left,
      CoreLinearInsertion.insertionSlot_right frame hJ]
  have hEA : E ⊆ Aset := fun u hu => (mem_openSlot.mp hu).1
  have hEΩ : E ⊆ CoreActualCyclicSlot.slot (offsetWindow S) frame J := by
    intro u hu
    exact mem_openSlot.mpr
      ⟨corePresieveSurvivors_subset_Icc S σ (hEA hu), (mem_openSlot.mp hu).2⟩
  have hEin : ∀ u ∈ E, left < u ∧ (u : ℝ) - left < W * G := by
    intro u hu
    have hi : (CoreLinearInsertion.insertionSlot frame J).1 < u ∧
        u < (CoreLinearInsertion.insertionSlot frame J).2 := by
      simpa only [E, CoreActualCyclicSlot.slot, CoreLinearInsertion.insertionSlot,
        Nat.sub_add_cancel hJ] using (mem_openSlot.mp hu).2
    refine ⟨hi.1, ?_⟩
    have heq : W * G = ((CoreLinearInsertion.insertionSlot frame J).2 : ℝ) - left := by
      dsimp only [W, left]
      rw [hgap, div_mul_cancel₀ _ hg.ne']
    rw [heq]
    have hh : (u : ℝ) < (CoreLinearInsertion.insertionSlot frame J).2 := by
      exact_mod_cast hi.2
    linarith
  have hwidth : (((CoreLinearInsertion.insertionSlot frame J).2 -
      (CoreLinearInsertion.insertionSlot frame J).1 : ℕ) : ℝ) ≤ R * G := by
    have hnorder : (CoreLinearInsertion.insertionSlot frame J).1 ≤
        (CoreLinearInsertion.insertionSlot frame J).2 := by
      simpa only [CoreLinearInsertion.insertionSlot_left,
        CoreLinearInsertion.insertionSlot_right frame hJ] using horder
    have heq : (((CoreLinearInsertion.insertionSlot frame J).2 -
        (CoreLinearInsertion.insertionSlot frame J).1 : ℕ) : ℝ) = W * G := by
      rw [Nat.cast_sub hnorder]
      dsimp only [W]
      rw [hgap, div_mul_cancel₀ _ hg.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_right hWA hg.le
  have happrox : ∀ u ∈ E, actualTest B hk r Fobs L f (insert u frame) ≤
      test (z, ((u : ℝ) - left) / G) := by
    intro u hu
    have hE : (CoreActualCyclicSlot.slot (offsetWindow S) frame J).Nonempty :=
      ⟨u, hEΩ hu⟩
    have hh := happG L J hJ hJL (offsetWindow S) frame hE u (hEΩ hu)
      hwidth hθlo hθhi
    have hlow : (CoreLinearInsertion.insertionSlot frame J).1 ≤ u :=
      (hEin u hu).1.le
    have hnorder : (CoreLinearInsertion.insertionSlot frame J).1 ≤
        (CoreLinearInsertion.insertionSlot frame J).2 := by
      simpa only [CoreLinearInsertion.insertionSlot_left,
        CoreLinearInsertion.insertionSlot_right frame hJ] using horder
    have hWcast : (((CoreLinearInsertion.insertionSlot frame J).2 -
        (CoreLinearInsertion.insertionSlot frame J).1 : ℕ) : ℝ) / G = W := by
      rw [Nat.cast_sub hnorder, ← hgap]
    rw [hlabel, hWcast, Nat.cast_sub hlow] at hh
    have houter : O frame =
        (selectedObservableOuter B hk r Fobs L J (offsetWindow S) frame hE : Circle) := by
      simp only [O, CoreRoundedModelFinite.outerMap, dif_pos hE]
    have hlead : leadingPairAction B hk a b s W (((u : ℝ) - left) / G) =
        CoreRealPowerImageAC.action W a Acoef Ccoef (((u : ℝ) - left) / G) := rfl
    rw [hlead, ← houter] at hh
    have hdiff := (abs_le.mp hh).2
    have heq : test (z, ((u : ℝ) - left) / G) =
        f (O frame + ((θ * CoreRealPowerImageAC.action W a Acoef Ccoef
          (((u : ℝ) - left) / G) : ℝ) : Circle)) + δ := by
      dsimp only [test, CoreRoundedReferenceMeasure.phase]
      rw [hpointWidth]
      rfl
    rw [heq]
    change f _ ≤ _
    dsimp only [θ]
    linarith
  have hsum : auxFrame_slotInsertSum Aset (J - 1)
      (corePositiveCutTest (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R
        (actualTest B hk r Fobs L f)) frame ≤
      ∑ u ∈ E, test (z, ((u : ℝ) - left) / G) := by
    unfold auxFrame_slotInsertSum
    apply sum_le_sum
    intro u hu
    have hgood :=
      (CoreActualCyclicSlot.not_frameBad_insert_iff 0 G R hJ hu).mpr hbad
    rw [corePositiveCutTest, if_neg hgood]
    exact happrox u hu
  have hSelberg := hselG z hparam left W E hW0 hWA hEin
    (coreLinear_presieveSubset_avoids σ hEA hfloor)
  have hraw : compactTest hR.le ha Acoef Ccoef f z =
      ∫ t in (0 : ℝ)..W,
        f (CoreRoundedReferenceMeasure.phase a Acoef Ccoef (z, t)) := by
    change CoreCompactFrameTest.rawTest R CoreJointFrameLimit.frame
      CoreRoundedReferenceMeasure.width
        (fun z t => CoreRoundedReferenceMeasure.phase a Acoef Ccoef (z, t)) f z = _
    have hh := CoreCompactFrameTest.rawTest_eq_fullIntegral_of_small
      CoreJointFrameLimit.frame CoreRoundedReferenceMeasure.width
      (fun z t => CoreRoundedReferenceMeasure.phase a Acoef Ccoef (z, t)) f z
      hnorm (by rwa [hpointWidth]) (by rwa [hpointWidth])
    simpa only [hpointWidth] using hh
  have hint : IntervalIntegrable
      (fun t => f (CoreRoundedReferenceMeasure.phase a Acoef Ccoef (z, t)))
      volume 0 W :=
    (f.continuous.comp ((CoreRoundedReferenceMeasure.continuous_phase ha Acoef Ccoef).comp
      (continuous_const.prodMk continuous_id))).intervalIntegrable 0 W
  have htestint : (∫ t in 0..W, test (z, t)) =
      compactTest hR.le ha Acoef Ccoef f z + δ * W := by
    rw [hraw]
    dsimp only [test]
    rw [intervalIntegral.integral_add hint intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [htestint] at hSelberg
  have herr : δ * W + ε / 2 ≤ ε := by
    have heq : δ * (R + 1) = ε / 2 := by
      dsimp only [δ]
      field_simp [(show 0 < R + 1 from by positivity).ne']
    have hh := mul_le_mul_of_nonneg_left hWA hδ.le
    nlinarith [hδ.le]
  exact (hsum.trans hSelberg).trans
    (mul_le_mul_of_nonneg_left (by linarith) hfactor)

/-- Aggregation of the generic slot estimate through the actual finite root
mixture, retaining both original-law exceptional terms. -/
theorem eventually_finiteRootMean_le_joint_add_errors
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (Fobs : Fin k → ℕ → ℤ) {a : ℝ} (b : Fin k → ℤ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hscale : CompactScaling Fobs a b)
    {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (f : Circle →ᵇ ℝ) {Kf : ℝ≥0} (hKf : LipschitzWith Kf f)
    (hf : ∀ x, 0 ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ G : ℝ in atTop, ∀ (J X S L : ℕ),
      1 ≤ J → J < L → phaseAt hk r (J - 1) = s →
      ∀ (hG : 1 < G) (hfloor : ⌊G⌋₊ ≤ S)
        (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
        (hZ : 0 < mixZ X),
      (∀ t ∈ mixScale X, 0 < lateRetention S (sieveCutoff (t : ℝ))) →
      (∀ t ∈ mixScale X,
        lateRetention S (sieveCutoff (t : ℝ)) ≤ (1 : ℝ) / 4) →
      1 ≤ G ^ a / (B : ℝ) ^ (J + 1) →
      G ^ a / (B : ℝ) ^ (J + 1) < (B : ℝ) ^ k →
      (∀ t ∈ mixScale X,
        lateRetention S (sieveCutoff (t : ℝ)) * G / Real.log G ≤ T) →
      corePositiveFiniteRootMean X S L (actualTest B hk r Fobs L f) ≤
        12 * T * ((∫ z, compactTest hR.le ha ((B : ℝ) * (b s : ℝ))
          (b (cyclicSucc hk s) : ℝ) f z
          ∂(CoreActualFrameJoint.jointLaw X S L 0 J G
            (G ^ a / (B : ℝ) ^ (J + 1))
            (outerMap B hk r Fobs L J S) hSy hZ : Measure Joint)) + ε) +
          nonMainTerm X S L (OnePoint.FiniteExterior.frameRanks 0 J)
            (J - 1) G R ‖f‖ := by
  filter_upwards [eventually_slot_sum_le Fobs b ha ha1 hscale hR hB hk r s
    f hKf hf hε] with G hslot
  intro J X S L hJ hJL hlabel hG hfloor hSy hZ hlate hquarter
    hθlo hθhi hret
  let v : Finset ℕ → ℝ := fun frame =>
    compactTest hR.le ha ((B : ℝ) * (b s : ℝ)) (b (cyclicSucc hk s) : ℝ) f
      (CoreActualFrameJoint.jointPoint 0 J G (G ^ a / (B : ℝ) ^ (J + 1))
        (outerMap B hk r Fobs L J S) frame)
  let frameBound : ℕ → Finset ℕ → ℝ := fun _ frame =>
    3 * G / Real.log G * (v frame + ε)
  have hv0 : ∀ frame, 0 ≤ v frame := by
    intro frame
    apply compactTest_nonneg hR.le ha _ _ f hf
    rw [point_width J hJ]
    exact div_nonneg (Nat.cast_nonneg _) (zero_lt_one.trans hG).le
  have hframe0 : ∀ t ∈ mixScale X, ∀ frame, 0 ≤ frameBound t frame := by
    intro t ht frame
    exact mul_nonneg
      (div_nonneg (by positivity) (Real.log_pos hG).le)
      (add_nonneg (hv0 frame) hε.le)
  have hroot := corePositiveFiniteRootMean_le_frame_high_originalBad
    X S L (J - 1) (OnePoint.FiniteExterior.frameRanks 0 J) G R
    (actualTest B hk r Fobs L f) frameBound hZ
    (by omega : J - 1 + 1 < L) (fun U => hf _) (fun U => f.apply_le_norm _)
    hSy hlate hquarter hframe0 (by
      intro t ht σ n hn frame hframe
      exact hslot L J S n σ frame hJ hJL hlabel hfloor
        (mem_Icc.mp (mem_filter.mp hn).1).1 hframe hθlo hθhi)
  have hdecomp :
      (∑ t ∈ mixScale X, mixWeightV t *
        (((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
            (∑ frame ∈ (offsetWindow S).powerset,
              coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L frame *
                frameBound t frame) +
          ‖f‖ * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) +
          ‖f‖ * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
            (fun U => if corePositiveFrameBad
              (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R U then 1 else 0))) /
          mixZ X =
        mainFrameTerm X S L G ε v +
          nonMainTerm X S L (OnePoint.FiniteExterior.frameRanks 0 J)
            (J - 1) G R ‖f‖ := by
    unfold mainFrameTerm nonMainTerm
    rw [← add_div, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro t ht
    dsimp only [frameBound]
    ring
  have hmain := mainFrameTerm_le X S L v hG hε.le hT hv0 hSy hZ hret
  have hint := CoreRoundedModelSubsequence.compact_expectation_eq_joint
    X S L J G (G ^ a / (B : ℝ) ^ (J + 1)) (outerMap B hk r Fobs L J S)
    hR.le ha ((B : ℝ) * (b s : ℝ)) (b (cyclicSucc hk s) : ℝ) f hSy hZ
  change (∑ frame ∈ (offsetWindow S).powerset,
    coreAuxiliaryFrameMass X S L frame * v frame) = _ at hint
  have hh := (hroot.trans_eq hdecomp).trans (_root_.add_le_add hmain le_rfl)
  rw [hint] at hh
  exact hh

private theorem mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos'
  · exact fun t ht => mixWeightV_nonneg t
  · refine ⟨2 * X, ?_, eulerProdNat_pos _⟩
    simp only [mixScale, mem_Ioc]
    omega

/-- One algebraic label is fixed before the physical scale and all its
critical ranks are genuinely admissible for the actual mixture. -/
theorem exists_fixed_label_admissible
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (b : Fin k → ℤ) (hb : b ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∃ s : Fin k, CoreRoundedCriticalRank.UsableLeadingLabel B hk a b s ∧
      ∀ᶠ X : ℕ in atTop, ∃ J : ℕ,
        CoreRoundedModelSubsequence.Admissible B hk r s a κ X J := by
  have hκ0 : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  obtain ⟨s, hs, hrank⟩ :=
    CoreRoundedCriticalRank.exists_usableLabel_eventually_rank
      hB hk r ha ha1 hκ b hb
  refine ⟨s, hs, ?_⟩
  filter_upwards [hrank, eventually_coreLinearMixtureScales hκ0,
    coreFRMUpper_eventually_lateRetention_le_quarter hκ0,
    eventually_ge_atTop (1 : ℕ)] with X hrankX hscale hret hX
  obtain ⟨J, hJ, hL, hlabel, hlo, hhi⟩ := hrankX
  refine ⟨J, ⟨hscale.1, hscale.2.2.2.1, hJ, hL, hlabel, hlo, hhi,
    ?_, ?_, hret, ?_, ?_, mixZ_pos hX⟩⟩
  · exact fun t ht => (hscale.2.2.2.2 t ht).1
  · intro t ht
    exact rootedEulerProdNat_pos (by have hh := hscale.2.2.1; omega)
  · exact fun t ht => (hscale.2.2.2.2 t ht).2.2.2.1
  · exact fun t ht => (hscale.2.2.2.2 t ht).2.2.2.2

/-- Profile form of the generic finite bound. -/
theorem eventually_profile_compact_bound
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (Fobs : Fin k → ℕ → ℤ) {a : ℝ} (b : Fin k → ℤ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hscale : CompactScaling Fobs a b)
    {κ : ℝ} (X j : ℕ → ℕ) (hX : Tendsto X atTop atTop)
    (had : ∀ n, CoreRoundedModelSubsequence.Admissible
      B hk r s a κ (X n) (j n))
    (R : ℝ) (hR : 0 < R) (f : Circle →ᵇ ℝ) (K : ℝ≥0)
    (hK : LipschitzWith K f) (hf : ∀ x, 0 ≤ f x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      CoreRoundedModelSubsequence.profileMean B hk r Fobs κ (X n) f ≤
        CoreRoundedModelSubsequence.modelConstant *
          (∫ z, compactTest hR.le ha ((B : ℝ) * (b s : ℝ))
            (b (cyclicSucc hk s) : ℝ) f z
            ∂(CoreRoundedModelSubsequence.profileLaw B hk r s Fobs a κ
              (X n) (j n) (had n) : Measure Joint)) +
        8 * ‖f‖ / R + coreFiniteRootMixUpperException κ (X n) * ‖f‖ +
          CoreRoundedModelSubsequence.modelConstant * δ := by
  have he := (tendsto_windowG_atTop.comp hX).eventually
    (eventually_finiteRootMean_le_joint_add_errors hB hk r s Fobs b ha ha1
      hscale hR coreLinearScales_retentionConst_pos.le f hK hf hδ)
  filter_upwards [he] with n hn
  have hm := hn (j n) (X n) (ahlSmall_window κ (X n)) (profileL κ (X n))
    (had n).lower (had n).upper (had n).label (had n).gap_gt
    (had n).floor_le (had n).cutoff (had n).normalization_pos
    (had n).retention_pos (had n).retention_small
    (had n).scale_lower (had n).scale_upper (had n).retention_bound
  have herr := CoreRoundedModelSubsequence.nonMainTerm_profile_le
    κ (X n) (j n) hR (had n).normalization_pos (had n).lower
    (had n).upper (zero_lt_one.trans (had n).gap_gt) f (had n).calibration
  have hh := hm.trans (_root_.add_le_add le_rfl herr)
  change CoreRoundedModelSubsequence.profileMean B hk r Fobs κ (X n) f ≤
    CoreRoundedModelSubsequence.modelConstant * (_ + δ) +
      (‖f‖ * coreFiniteRootMixUpperException κ (X n) + 8 * ‖f‖ / R) at hh
  exact hh.trans_eq (by
    dsimp only [CoreRoundedModelSubsequence.profileLaw,
      CoreRoundedModelSubsequence.profileScale, Function.comp_apply]
    ring)

/-- Final actual reference subsequence for every deterministically scaled
integer observable.  No distributional or reference-measure hypothesis is
an input. -/
theorem exists_reference_subsequence
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (Fobs : Fin k → ℕ → ℤ) {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (b : Fin k → ℤ) (hb : b ≠ 0) (hscale : CompactScaling Fobs a b)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (X : ℕ → ℕ) (hX : Tendsto X atTop atTop) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ σ : Measure Circle,
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 8 ∧
      ∀ (f : Circle →ᵇ ℝ) (K : ℝ≥0), LipschitzWith K f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          CoreRoundedModelSubsequence.profileMean B hk r Fobs κ (X (ψ n)) f ≤
            CoreRoundedModelSubsequence.modelConstant * (∫ x, f x ∂σ) + ε := by
  have hκ0 : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  obtain ⟨s, hs, he⟩ :=
    exists_fixed_label_admissible hB hk r ha ha1 b hb hκ
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hX.eventually he)
  let Y := fun n => X (n + n₀)
  have hY : Tendsto Y atTop atTop := hX.comp (tendsto_add_atTop_nat n₀)
  have hchoose : ∀ n, ∃ J,
      CoreRoundedModelSubsequence.Admissible B hk r s a κ (Y n) J :=
    fun n => hn₀ (n + n₀) (Nat.le_add_left _ _)
  let j := fun n => Classical.choose (hchoose n)
  have had : ∀ n, CoreRoundedModelSubsequence.Admissible
      B hk r s a κ (Y n) (j n) := fun n => Classical.choose_spec (hchoose n)
  let θ := fun n => CoreRoundedModelSubsequence.profileScale B a (Y n) (j n)
  let O := fun n => outerMap B hk r Fobs (profileL κ (Y n))
    (j n) (ahlSmall_window κ (Y n))
  obtain ⟨ν, χ, hχ, hweak, hW, hθrange, hWi, hfinite, hac, hmass⟩ :=
    CoreRoundedReferenceMeasure.exists_actual_profile_reference hB hk ha ha1 hκ0
      b s hs Y hY j θ O (fun n => (had n).cutoff)
      (fun n => (had n).normalization_pos)
      (fun n => zero_lt_one.trans (had n).gap_gt) (fun n => (had n).lower)
      (fun n => (had n).upper) (fun n => (had n).calibration)
      (fun n => ⟨(had n).scale_lower, (had n).scale_upper.le⟩)
  let Acoef := (B : ℝ) * (b s : ℝ)
  let Ccoef := (b (cyclicSucc hk s) : ℝ)
  have href : CoreRoundedReferenceMeasure.labelledReference ν B hk a b s =
      CoreRoundedReferenceMeasure.referenceMeasure ν a Acoef Ccoef := by
    rfl
  rw [href] at hfinite hac hmass
  let μ := fun n => CoreRoundedModelSubsequence.profileLaw B hk r s Fobs a κ
    (Y (χ n)) (j (χ n)) (had (χ n))
  have hweak' : Tendsto μ atTop (nhds ν) := hweak
  let mean := fun n f =>
    CoreRoundedModelSubsequence.profileMean B hk r Fobs κ (Y (χ n)) f
  have hη : Tendsto (fun n => coreFiniteRootMixUpperException κ (Y (χ n)))
      atTop (nhds 0) :=
    (tendsto_coreFiniteRootMixUpperException hκ0).comp
      (hY.comp hχ.tendsto_atTop)
  have hbound := CoreRoundedModelSubsequence.reference_domination_of_finite_bounds
    (a := a) (A := Acoef) (C := Ccoef) ha μ ν hweak' hW hWi mean
    CoreRoundedModelSubsequence.modelConstant_nonneg
    (fun n => coreFiniteRootMixUpperException κ (Y (χ n))) hη (by
      intro R hR f K hK hf δ hδ
      exact eventually_profile_compact_bound hB hk r s Fobs b ha ha1 hscale
        (fun n => Y (χ n)) (fun n => j (χ n))
        (hY.comp hχ.tendsto_atTop) (fun n => had (χ n))
        R hR f K hK hf δ hδ)
  refine ⟨fun n => χ n + n₀, ?_,
    CoreRoundedReferenceMeasure.referenceMeasure ν a Acoef Ccoef,
    hfinite, hac, hmass, ?_⟩
  · exact fun m n hmn => Nat.add_lt_add_right (hχ hmn) n₀
  · exact hbound

/-- Compose the generic deterministic model reference with the actual D
transfer and the unconditional prime first-gap mean. -/
theorem subsequenceReference_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (Fobs : Fin k → ℕ → ℤ) {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (b : Fin k → ℤ) (hb : b ≠ 0) (hscale : CompactScaling Fobs a b)
    {C : ℝ} (hC : 0 ≤ C)
    (hlin : ∀ s q, 1 ≤ q → |(Fobs s q : ℝ)| ≤ C * (q : ℝ))
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {d0 c : ℝ} (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    CoreResidueDigitalReference.SubsequenceReferenceBounds
      (fun n => (CoreIntegerGapObservable.observableSeries
        B hk r Fobs primeGap n : Circle))
      (fun X => Nat.primeCounting X) windowNX := by
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  intro φ hφ
  obtain ⟨ψ, hψ, σ, hσfinite, hσac, hσmass, hmodel⟩ :=
    exists_reference_subsequence hB hk r Fobs ha ha1 b hb hscale hκ
      φ hφ.tendsto_atTop
  refine ⟨ψ, hψ, σ, hσfinite, hσac,
    16 * c * CoreRoundedModelSubsequence.modelConstant,
    mul_nonneg (mul_nonneg (by norm_num) hcpos.le)
      CoreRoundedModelSubsequence.modelConstant_nonneg, ?_⟩
  intro f K hK hf eps heps
  have heps2 : 0 < eps / 2 := half_pos heps
  have hsmall : 0 < eps / (32 * c) :=
    div_pos heps (mul_pos (by norm_num) hcpos)
  have hindices : Tendsto (fun n => φ (ψ n)) atTop atTop := by
    simpa only [Function.comp_def] using hφ.tendsto_atTop.comp hψ.tendsto_atTop
  have harith := hindices.eventually
    (CoreIntegerGapDTransfer.eventually_prime_observableMean_le_finiteRootModel_of_D
      hB hk r Fobs hC hlin hκ hd0 hc hD f hK hf heps2)
  have hmod := hmodel f K hK hf (eps / (32 * c)) hsmall
  filter_upwards [harith, hmod] with n hn hm
  have hm' : CoreIntegerGapDTransfer.finiteRootModelMean B (φ (ψ n))
      (ahlSmall_window κ (φ (ψ n))) (profileL κ (φ (ψ n))) hk r Fobs f ≤
      CoreRoundedModelSubsequence.modelConstant * (∫ x, f x ∂σ) +
        eps / (32 * c) := by
    simpa only [CoreIntegerGapDTransfer.finiteRootModelMean,
      CoreRoundedModelSubsequence.profileMean] using hm
  have hmul := mul_le_mul_of_nonneg_left hm'
    (show (0 : ℝ) ≤ 16 * c from mul_nonneg (by norm_num) hcpos.le)
  have herr : 16 * c * (eps / (32 * c)) = eps / 2 := by
    field_simp [hcpos.ne'] <;> ring
  rw [mul_add, herr] at hmul
  exact hn.trans (by
    calc
      16 * c * CoreIntegerGapDTransfer.finiteRootModelMean B (φ (ψ n))
          (ahlSmall_window κ (φ (ψ n))) (profileL κ (φ (ψ n))) hk r Fobs f +
          eps / 2 ≤
        (16 * c * CoreRoundedModelSubsequence.modelConstant) *
          (∫ x, f x ∂σ) + eps / 2 + eps / 2 := by
        simpa only [mul_assoc] using
          (_root_.add_le_add hmul (le_refl (eps / 2)))
      _ = (16 * c * CoreRoundedModelSubsequence.modelConstant) *
          (∫ x, f x ∂σ) + eps := by ring)

end

end PrimeGapNormality.Prime.CoreScaledGapModelReference
