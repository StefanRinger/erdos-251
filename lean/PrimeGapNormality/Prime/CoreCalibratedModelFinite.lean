import PrimeGapNormality.Prime.CoreCalibratedFrameProbability
import PrimeGapNormality.Prime.CoreLocalModelMixture

/-!
# Positive resampling under arbitrary actual cutoff weights

The original cutoff loss is charged in each original rooted law before
using the exact full-cardinality resampling identity. Only afterwards are
the arbitrary nonnegative cutoff weights averaged. There is no comparison
with the canonical finiteRootMix and no supplied slot majorant.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedModelFinite
open Finset Filter MeasureTheory CoreCyclic
open CoreCalibratedAuxiliaryFrame CoreCalibratedFrameProbability
  CoreCalibratedMixtureFiniteSupport CoreCalibratedMixtureProfile
  CoreCalibratedFrameLimit CoreRoughSyntheticScale
open scoped Classical Topology ENNReal NNReal Polynomial BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Literal original-law mean, keeping all survivors and discarding only
the original low-cardinality event. -/
def mean (ω : ℕ → ℝ) (S M : ℕ) (test : Finset ℕ → ℝ) : ℝ :=
  ∑' y, ω y * CoreOriginalDeletedFrame.highMean y S M test

theorem mean_eq_finite (ω : ℕ → ℝ) (S M : ℕ) {N : ℕ}
    (hz : ∀ y, N ≤ y → ω y = 0) (test : Finset ℕ → ℝ) :
    mean ω S M test = ∑ y ∈ range N, ω y * CoreOriginalDeletedFrame.highMean y S M test :=
  weighted_tsum_eq_sum_of_tail_zero ω _ hz

/-- The mean is exactly the high-cardinality test of the actual mixed law. -/
theorem mean_eq_law (ω : ℕ → ℝ) (S M : ℕ) {N : ℕ}
    (hz : ∀ y, N ≤ y → ω y = 0) (test : Finset ℕ → ℝ) :
    mean ω S M test = ∑ U ∈ (offsetWindow S).powerset,
      CoreCalibratedMixtureMoments.law ω S U * if M ≤ U.card then test U else 0 := by
  rw [mean_eq_finite ω S M hz]
  unfold CoreOriginalDeletedFrame.highMean CoreCalibratedMixtureMoments.law
  simp_rw [weighted_tsum_eq_sum_of_tail_zero ω _ hz, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun U hU => Finset.sum_congr rfl fun y hy => by ring

def modelConstant : ℝ := 12 * (6 / eulerProdLowerConst)
theorem modelConstant_nonneg : 0 ≤ modelConstant := by
  unfold modelConstant
  exact mul_nonneg (by norm_num) (div_nonneg (by norm_num) eulerProdLowerConst_pos.le)

theorem layer_contraction (S y M : ℕ) (hSy : S ≤ y)
    {G T δ : ℝ} (hG : 1 < G) (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (hret : lateRetention S y * G / Real.log G ≤ T)
    (v : Finset ℕ → ℝ) (hv : ∀ F, 0 ≤ v F) :
    4 * lateRetention S y * (∑ F ∈ (offsetWindow S).powerset,
      coreAuxiliaryLayerFrameMass S y M F * (3 * G / Real.log G * (v F + δ))) ≤
    12 * T * ((∑ F ∈ (offsetWindow S).powerset,
      coreAuxiliaryLayerFrameMass S y M F * v F) + δ) := by
  let a F := coreAuxiliaryLayerFrameMass S y M F
  have ha F : 0 ≤ a F := coreAuxiliaryLayerFrameMass_nonneg S y M hSy F
  have hmass : (∑ F ∈ (offsetWindow S).powerset, a F) ≤ 1 := by
    have hh := coreAuxiliaryLayerFrameMass_add_low_eq_one S y M hSy
    have hl := coreAuxiliaryLayerLowCountMass_nonneg S y M hSy
    dsimp only [a]
    linarith
  have hcoef : 4 * lateRetention S y * (3 * G / Real.log G) ≤ 12 * T := by
    calc
      4 * lateRetention S y * (3 * G / Real.log G) =
          12 * (lateRetention S y * G / Real.log G) := by ring
      _ ≤ 12 * T := mul_le_mul_of_nonneg_left hret (by norm_num : (0 : ℝ) ≤ 12)
  have hsum0 : 0 ≤ ∑ F ∈ (offsetWindow S).powerset, a F * (v F + δ) :=
    Finset.sum_nonneg fun F _ => mul_nonneg (ha F) (add_nonneg (hv F) hδ)
  have hfactor : (∑ F ∈ (offsetWindow S).powerset,
      a F * (3 * G / Real.log G * (v F + δ))) =
      (3 * G / Real.log G) * ∑ F ∈ (offsetWindow S).powerset, a F * (v F + δ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun F _ => by ring
  change 4 * lateRetention S y * (∑ F ∈ (offsetWindow S).powerset,
    a F * (3 * G / Real.log G * (v F + δ))) ≤ _
  rw [hfactor, ← mul_assoc]
  refine (mul_le_mul_of_nonneg_right hcoef hsum0).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hT)
  have he : (∑ F ∈ (offsetWindow S).powerset, a F * (v F + δ)) =
      (∑ F ∈ (offsetWindow S).powerset, a F * v F) +
        δ * ∑ F ∈ (offsetWindow S).powerset, a F := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_comm δ]
  rw [he]
  exact _root_.add_le_add le_rfl (mul_le_of_le_one_right hδ hmass)

theorem compactValue_nonneg
    {B k : ℕ} (hk : 0 < k) (r s : Fin k) (P : PeriodicLocal k)
    (K w J d S : ℕ) (hd : (OnePoint.action B hk w s P).totalDegree ≤ d)
    {R G : ℝ} (hR : 0 ≤ R) (hG : 0 < G)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (F : Finset ℕ) :
    0 ≤ CoreLocalModelMixture.compactValueK hk r s P K w J d S hd hR G f F := by
  rw [CoreLocalModelMixture.compactValueK, CoreLocalModelPositive.compactInsertionTest_apply]
  exact (CoreCompactFrameTest.rawTest_nonneg_le_fullIntegral hR
    CoreJointFrameLimit.frame (CoreLocalModelPositive.jointWidth w)
    (CoreLocalModelPositive.jointPhase w d (OnePoint.action B hk w s P) G⁻¹)
    (CoreLocalModelPositive.continuous_jointPhase_uncurry w d (OnePoint.action B hk w s P) hd G⁻¹)
    f hf _ (by
      unfold CoreLocalModelPositive.jointWidth
      exact CoreActualFrameJoint.localFrame_nonneg w J hG.le F _)).1

theorem compactValue_empty
    {B k : ℕ} (hk : 0 < k) (r s : Fin k) (P : PeriodicLocal k)
    (K w J d S : ℕ) (hd : (OnePoint.action B hk w s P).totalDegree ≤ d)
    {R : ℝ} (hR : 0 ≤ R) (G : ℝ) (f : AddCircle (1 : ℝ) →ᵇ ℝ) :
    CoreLocalModelMixture.compactValueK hk r s P K w J d S hd hR G f ∅ = 0 := by
  rw [CoreLocalModelMixture.compactValueK, CoreLocalModelPositive.compactInsertionTest_apply]
  unfold CoreCompactFrameTest.rawTest CoreLocalModelPositive.jointWidth
  have hmin : min (0 : ℝ) (R + 1) = 0 := min_eq_left (by linarith)
  simp [CoreCompactFrameTest.clippedWidth, hmin]

/-- Genuine single-cutoff resampling, uniform in the retained count and
varying rank. Both the Selberg majorant and the original cutoff tail are
proved internally. -/
theorem eventually_single_cutoff
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (w d : ℕ)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (OnePoint.action B hk w s P).totalDegree ≤ d)
    {R : ℝ} (hR : 0 < R) (f : AddCircle (1 : ℝ) →ᵇ ℝ) {Kf : ℝ≥0}
    (hKf : LipschitzWith Kf f) (hf : ∀ x, 0 ≤ f x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ G : ℝ in atTop, ∀ K J S M y : ℕ,
      w + 1 ≤ J → J < K → J + w < M → phaseAt hk r (J - 1) = s →
      1 < G → ⌊G⌋₊ ≤ S → S ≤ y →
      0 < lateRetention S y → lateRetention S y ≤ (1 : ℝ) / 4 →
      lateRetention S y * G / Real.log G ≤ 6 / eulerProdLowerConst →
      roughGapScale y / G ≤ 2 →
      1 ≤ G ^ d / (B : ℝ) ^ (J + 1) →
      G ^ d / (B : ℝ) ^ (J + 1) ≤ (B : ℝ) ^ k →
      CoreOriginalDeletedFrame.highMean y S M (CoreLocalModelPositive.actualTest B hk r P K f) ≤
        modelConstant * ((∑ F ∈ (offsetWindow S).powerset,
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
    (div_nonneg (by norm_num) eulerProdLowerConst_pos.le) hδ.le hret v hv
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
  exact hh'.trans_eq (by dsimp only [modelConstant, v, test, bound]; ring)

theorem compact_expectation_eq_joint
    {B k : ℕ} (hk : 0 < k) (r s : Fin k) (P : PeriodicLocal k)
    (K w J d S M : ℕ) (hd : (OnePoint.action B hk w s P).totalDegree ≤ d)
    (ω : ℕ → ℝ) (hω : Weights ω S) {R : ℝ} (hR : 0 ≤ R)
    (G : ℝ) (f : AddCircle (1 : ℝ) →ᵇ ℝ) :
    (∑ F ∈ (offsetWindow S).powerset, mass ω S M F *
      CoreLocalModelMixture.compactValueK hk r s P K w J d S hd hR G f F) =
    ∫ z, CoreLocalModelPositive.compactInsertionTest hR w d (OnePoint.action B hk w s P) hd G⁻¹ f z
      ∂(jointLaw ω S M (OnePoint.FiniteExterior.frameRank w J) G
        (G ^ d / (B : ℝ) ^ (J + 1)) (CoreLocalModelMixture.outerMap B hk r P K w J S) :
          Measure (CoreJointFrameLimit.Joint (2 * w + 1))) := by
  rw [integral_jointLaw _ _ _ hω _ _ _ _ _
    (CoreLocalModelPositive.compactInsertionTest hR w d (OnePoint.action B hk w s P) hd G⁻¹ f).continuous.measurable]
  change _ = ∑ F ∈ (offsetWindow S).powerset, completed ω S M F *
    CoreLocalModelMixture.compactValueK hk r s P K w J d S hd hR G f F
  rw [completed_expectation, compactValue_empty hk r s P K w J d S hd hR G f,
    mul_zero, add_zero]

/-- Pure finite averaging; support size is not bounded uniformly. -/
theorem weighted_three_terms (ω g h : ℕ → ℝ) (N : ℕ)
    (hs : ∑ y ∈ range N, ω y = 1) (A δ C D : ℝ) :
    (∑ y ∈ range N, ω y * (A * (g y + δ) + C * h y + D)) =
      A * ((∑ y ∈ range N, ω y * g y) + δ) +
        C * (∑ y ∈ range N, ω y * h y) + D := by
  calc
    _ = ∑ y ∈ range N,
        (A * (ω y * g y) + (A * δ) * ω y + C * (ω y * h y) + D * ω y) :=
      Finset.sum_congr rfl fun y _ => by ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_one]
      ring

/-- Average the genuine one-cutoff inequalities, then identify the actual
joint integral. No slot bound remains as an end premise. -/
theorem eventually_mixture
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (w d : ℕ)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (OnePoint.action B hk w s P).totalDegree ≤ d)
    {R : ℝ} (hR : 0 < R) (f : AddCircle (1 : ℝ) →ᵇ ℝ) {Kf : ℝ≥0}
    (hKf : LipschitzWith Kf f) (hf : ∀ x, 0 ≤ f x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ G : ℝ in atTop, ∀ (K J S M : ℕ) (ω : ℕ → ℝ),
      Weights ω S → w + 1 ≤ J → J < K → J + w < M → phaseAt hk r (J - 1) = s →
      1 < G → ⌊G⌋₊ ≤ S →
      (∀ y, ω y ≠ 0 → 0 < lateRetention S y ∧ lateRetention S y ≤ (1 : ℝ) / 4 ∧
        lateRetention S y * G / Real.log G ≤ 6 / eulerProdLowerConst ∧ roughGapScale y / G ≤ 2) →
      1 ≤ G ^ d / (B : ℝ) ^ (J + 1) →
      G ^ d / (B : ℝ) ^ (J + 1) ≤ (B : ℝ) ^ k →
      mean ω S M (CoreLocalModelPositive.actualTest B hk r P K f) ≤
        modelConstant * ((∫ z,
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
      ω y * (modelConstant * ((∑ F ∈ (offsetWindow S).powerset,
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

end
end PrimeGapNormality.Prime.CoreCalibratedModelFinite
