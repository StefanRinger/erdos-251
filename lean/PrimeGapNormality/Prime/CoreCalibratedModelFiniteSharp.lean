import PrimeGapNormality.Prime.CoreCalibratedModelSubsequence
import PrimeGapNormality.Prime.CoreCalibratedRetentionSharp

/-!
# The actual arbitrary-mixture finite model with coefficient 24

This precision variant reuses the genuine ordered-slot, original-law
cutoff and full-cardinality layer proofs of CoreCalibratedModelFinite.
The layer contraction is evaluated at T=2. Its final profile theorem
derives that retention bound from qualitative calibration and the actual
Mertens product limit; it has no retention or model-estimate premise.

Original count M, emission horizon M-w, span floor(6MG/5), cutoff weights,
high-count exception and original-law frame-tail error are unchanged.
No comparison with the canonical finiteRootMix is made.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedModelFiniteSharp

open Filter Finset MeasureTheory CoreCyclic CoreLocalReferencePassage
open CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
  CoreCalibratedAuxiliaryFrame CoreCalibratedFrameProbability CoreCalibratedFrameLimit
  CoreCalibratedModelFinite CoreCalibratedModelSubsequence CoreRoughSyntheticScale
open scoped Classical Topology ENNReal NNReal Polynomial BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Genuine one-cutoff Selberg resampling with contraction threshold two.
The threshold is a finite intermediate, discharged by the final theorem. -/
theorem eventually_single_cutoff
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (w d : ℕ)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (OnePoint.action B hk w s P).totalDegree ≤ d)
    {R : ℝ} (hR : 0 < R) (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) {Kf : ℝ≥0}
    (hKf : LipschitzWith Kf f) (hf : ∀ x, 0 ≤ f x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ G : ℝ in atTop, ∀ K J S M y : ℕ,
      w + 1 ≤ J → J < K → J + w < M → phaseAt hk r (J - 1) = s →
      1 < G → ⌊G⌋₊ ≤ S → S ≤ y →
      0 < lateRetention S y → lateRetention S y ≤ (1 : ℝ) / 4 →
      lateRetention S y * G / Real.log G ≤ 2 →
      roughGapScale y / G ≤ 2 →
      1 ≤ G ^ d / (B : ℝ) ^ (J + 1) →
      G ^ d / (B : ℝ) ^ (J + 1) ≤ (B : ℝ) ^ k →
      CoreOriginalDeletedFrame.highMean y S M (CoreLocalModelPositive.actualTest B hk r P K f) ≤
        (24 : ℝ) * ((∑ F ∈ (offsetWindow S).powerset,
          coreAuxiliaryLayerFrameMass S y M F *
            CoreLocalModelMixture.compactValueK hk r s P K w J d S hd hR.le G f F) + δ) +
        ‖f‖ * coreFiniteRootMixUpperRootMass S y + 4 * (2 * w + 1 : ℕ) * ‖f‖ / R := by
  filter_upwards [CoreLocalModelPositive.eventually_presieve_slot_sum_le_compactTest
    hB hk r P w d s hw hd hR f hKf hf hδ] with G hslot
  intro K J S M y hJ hJK hJM hlabel hG hfloor hSy hθ hquarter hret hcal hθlo hθhi
  let v := CoreLocalModelMixture.compactValueK hk r s P K w J d S hd hR.le G f
  let test := CoreLocalModelPositive.actualTest B hk r P K f
  let I := OnePoint.FiniteExterior.frameRanks w J
  let bound := fun F => 3 * G / Real.log G * (v F + δ)
  have hJ1 : 1 ≤ J := by omega
  have hjM : J - 1 + 1 < M := by omega
  have hv : ∀ F, 0 ≤ v F := compactValue_nonneg hk r s P K w J d S hd hR.le
    (zero_lt_one.trans hG) f hf
  have hcut0 : ∀ U, 0 ≤ corePositiveCutTest I (J - 1) G R test U := by
    intro U
    unfold corePositiveCutTest
    split_ifs <;> first | exact le_rfl | exact hf _
  have hcutC : ∀ U, corePositiveCutTest I (J - 1) G R test U ≤ ‖f‖ := by
    intro U
    unfold corePositiveCutTest
    split_ifs <;> first | exact norm_nonneg _ | exact f.apply_le_norm _
  have hg := corePositive_highMean_le_frame_add_high S y M (J - 1)
    (corePositiveCutTest I (J - 1) G R test) bound hSy hjM hcut0 hcutC
    (fun F => mul_nonneg (div_nonneg (by positivity) (Real.log_pos hG).le)
      (add_nonneg (hv F) hδ.le)) hθ hquarter (by
        intro σ n hn F hF
        exact hslot K J S M n σ F hJ hJK hlabel hG.le hfloor (by omega)
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1 hF hθlo hθhi)
  have hc := corePositive_highMean_le_cut_add_originalTail y S M I (J - 1) G R test
    (by omega) (fun i hi => OnePoint.FiniteExterior.frameRanks_valid hJ hJM hi)
    (zero_lt_one.trans hG) hR (fun U => hf _) (fun U => f.apply_le_norm _)
  have hmain := layer_contraction S y M hSy hG
    (by norm_num : (0 : ℝ) ≤ 2) hδ.le hret v hv
  have htail : (2 * (I.card : ℝ)) / (R * G * eulerProdNat y) ≤
      4 * (2 * w + 1 : ℕ) / R := by
    have hh := mul_le_mul_of_nonneg_left hcal
      (show 0 ≤ 2 * (I.card : ℝ) / R by positivity)
    have he : (2 * (I.card : ℝ)) / (R * G * eulerProdNat y) =
        (2 * (I.card : ℝ) / R) * (roughGapScale y / G) := by
      unfold roughGapScale
      field_simp [hR.ne', (zero_lt_one.trans hG).ne', (eulerProdNat_pos y).ne'] <;> ring
    rw [he]
    exact hh.trans_eq (by
      dsimp only [I]
      rw [OnePoint.FiniteExterior.frameRanks_card w J hJ]
      ring)
  have htail' := mul_le_mul_of_nonneg_left htail (norm_nonneg f)
  have hh := hc.trans (_root_.add_le_add hg le_rfl)
  have hh' := hh.trans (_root_.add_le_add (_root_.add_le_add hmain le_rfl) htail')
  exact hh'.trans_eq (by dsimp only [v, test, bound]; ring)

/-- Exact averaging over the actual cutoff weights, retaining both original-law errors. -/
theorem eventually_mixture
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (w d : ℕ)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (OnePoint.action B hk w s P).totalDegree ≤ d)
    {R : ℝ} (hR : 0 < R) (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) {Kf : ℝ≥0}
    (hKf : LipschitzWith Kf f) (hf : ∀ x, 0 ≤ f x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ G : ℝ in atTop, ∀ (K J S M : ℕ) (ω : ℕ → ℝ),
      Weights ω S → w + 1 ≤ J → J < K → J + w < M → phaseAt hk r (J - 1) = s →
      1 < G → ⌊G⌋₊ ≤ S →
      (∀ y, ω y ≠ 0 → 0 < lateRetention S y ∧ lateRetention S y ≤ (1 : ℝ) / 4 ∧
        lateRetention S y * G / Real.log G ≤ 2 ∧ roughGapScale y / G ≤ 2) →
      1 ≤ G ^ d / (B : ℝ) ^ (J + 1) →
      G ^ d / (B : ℝ) ^ (J + 1) ≤ (B : ℝ) ^ k →
      mean ω S M (CoreLocalModelPositive.actualTest B hk r P K f) ≤
        (24 : ℝ) * ((∫ z,
          CoreLocalModelPositive.compactInsertionTest hR.le w d (OnePoint.action B hk w s P) hd G⁻¹ f z
          ∂(jointLaw ω S M (OnePoint.FiniteExterior.frameRank w J) G
            (G ^ d / (B : ℝ) ^ (J + 1)) (CoreLocalModelMixture.outerMap B hk r P K w J S) :
              Measure (CoreJointFrameLimit.Joint (2 * w + 1)))) + δ) +
        CoreCalibratedMixtureCountException.highMass ω S * ‖f‖ +
        4 * (2 * w + 1 : ℕ) * ‖f‖ / R := by
  filter_upwards [eventually_single_cutoff hB hk r s P w d hw hd hR f hKf hf hδ] with G hg
  intro K J S M ω hω hJ hJK hJM hlabel hG hfloor hret hθlo hθhi
  obtain ⟨N, hz, hs⟩ := hω.2.2
  let v := CoreLocalModelMixture.compactValueK hk r s P K w J d S hd hR.le G f
  have hpoint (y : ℕ) : ω y * CoreOriginalDeletedFrame.highMean y S M
      (CoreLocalModelPositive.actualTest B hk r P K f) ≤
      ω y * ((24 : ℝ) * ((∑ F ∈ (offsetWindow S).powerset,
        coreAuxiliaryLayerFrameMass S y M F * v F) + δ) +
        ‖f‖ * coreFiniteRootMixUpperRootMass S y + 4 * (2 * w + 1 : ℕ) * ‖f‖ / R) := by
    by_cases hy : ω y = 0
    · simp only [hy, zero_mul, le_refl]
    · have hr := hret y hy
      exact mul_le_mul_of_nonneg_left
        (hg K J S M y hJ hJK hJM hlabel hG hfloor (hω.2.1 y hy)
          hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 hθlo hθhi) (hω.1 y)
  rw [mean_eq_finite ω S M hz]
  refine (Finset.sum_le_sum fun y _ => hpoint y).trans_eq ?_
  rw [weighted_three_terms _ _ _ N hs]
  rw [← expectation_eq_finite ω S M hz v,
    compact_expectation_eq_joint hk r s P K w J d S M hd ω hω hR.le G f]
  unfold CoreCalibratedMixtureCountException.highMass
  rw [weighted_tsum_eq_sum_of_tail_zero ω _ hz]
  ring

/-- Final calibrated-profile estimate with literal coefficient 24. No retention, slot or model bound is assumed. -/
theorem eventually_compact_bound
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (w d : ℕ)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (OnePoint.action B hk w s P).totalDegree ≤ d)
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G)
    (J : ℕ → ℕ) (hJ : ∀ᶠ X in atTop, RankAdmissible B hk r s w d G M J X)
    {R : ℝ} (hR : 0 < R) (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) {Kf : ℝ≥0}
    (hKf : LipschitzWith Kf f) (hf : ∀ x, 0 ≤ f x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X in atTop, modelMean B hk r P w G M ω X f ≤
      (24 : ℝ) * (∫ z,
        CoreLocalModelPositive.compactInsertionTest hR.le w d (OnePoint.action B hk w s P) hd (G X)⁻¹ f z
          ∂(modelLaw B hk r P w d G M J ω X : Measure (CoreLocalReferencePassage.Joint w))) +
      (4 * (2 * w + 1 : ℕ)) * ‖f‖ / R +
      CoreCalibratedMixtureCountException.highMass (ω X) (physicalSpan G M X) * ‖f‖ +
      (24 : ℝ) * δ := by
  filter_upwards [hG.eventually (eventually_mixture hB hk r s P w d hw hd hR f hKf hf hδ),
    eventually_profile_data hG hκ hM hω hsum hcal,
    eventually_scaled_retention hG hκ hM hcal,
    CoreCalibratedRetentionSharp.eventually_scaled_retention_lt_two hG hκ hM hcal,
    hJ] with X hfinite hdata hret hsharp hj
  have hweights : Weights (ω X) (physicalSpan G M X) := ⟨hω X, hdata.2.1, hdata.2.2.2⟩
  have hs : ∀ y, ω X y ≠ 0 →
      0 < lateRetention (physicalSpan G M X) y ∧
      lateRetention (physicalSpan G M X) y ≤ (1 : ℝ) / 4 ∧
      lateRetention (physicalSpan G M X) y * G X / Real.log (G X) ≤ 2 ∧
      CoreRoughSyntheticScale.roughGapScale y / G X ≤ 2 := by
    intro y hy
    have hh := hret.2.2.2 y (lt_of_le_of_ne (hω X y) (Ne.symm hy))
    exact ⟨hh.2.1, hh.2.2.1,
      (hsharp y (lt_of_le_of_ne (hω X y) (Ne.symm hy))).le, hdata.2.2.1 y hy⟩
  have hh := hfinite (M X - w) (J X) (physicalSpan G M X) (M X) (ω X)
    hweights hj.1 (by have hh := hj.2.1; omega) hj.2.1 hj.2.2.1
    hret.1 hret.2.2.1 hs hj.2.2.2.1 hj.2.2.2.2
  exact hh.trans_eq (by
    dsimp only [modelLaw, profileLaw, outer, criticalScale, Function.comp_apply]
    ring)

end
end PrimeGapNormality.Prime.CoreCalibratedModelFiniteSharp
