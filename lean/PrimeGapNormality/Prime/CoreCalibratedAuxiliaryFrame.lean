import PrimeGapNormality.Prime.CoreCalibratedMixtureCountException
import PrimeGapNormality.Prime.CoreAuxiliaryFrameMass
import PrimeGapNormality.Prime.CoreActualFrameRectangleLimit
import PrimeGapNormality.Prime.CoreOriginalDeletedFrameTail

/-!
# Actual auxiliary frames under arbitrary calibrated cutoff weights

Only the outer cutoff average changes. Each summand is the actual
coreAuxiliaryLayerFrameMass, retaining the original presieve and survivor
count before drawing every (N-1)-subset. Missing mass is not renormalized.
Original fixed-rank deletion cutoffs are estimated separately, under the
original rooted law, before auxiliary reweighting.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedAuxiliaryFrame

open Finset Filter CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
  CoreCalibratedMixtureCountException CoreRoughSyntheticScale
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1000000

def mass (w : ℕ → ℝ) (S M : ℕ) (F : Finset ℕ) : ℝ :=
  ∑' y : ℕ, w y * coreAuxiliaryLayerFrameMass S y M F

def missing (w : ℕ → ℝ) (S M : ℕ) : ℝ :=
  ∑' y : ℕ, w y * coreAuxiliaryLayerLowCountMass S y M

def Valid (w : ℕ → ℝ) (S : ℕ) : Prop := ∀ y, w y ≠ 0 → S ≤ y

theorem mass_nonneg (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y) (S M : ℕ)
    (hvalid : Valid w S) (F : Finset ℕ) : 0 ≤ mass w S M F := by
  apply tsum_nonneg
  intro y
  by_cases hy : w y = 0
  · simp only [hy, zero_mul, le_refl]
  · exact mul_nonneg (hw y) (coreAuxiliaryLayerFrameMass_nonneg S y M (hvalid y hy) F)

theorem missing_nonneg (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y) (S M : ℕ)
    (hvalid : Valid w S) : 0 ≤ missing w S M := by
  apply tsum_nonneg
  intro y
  by_cases hy : w y = 0
  · simp only [hy, zero_mul, le_refl]
  · exact mul_nonneg (hw y) (coreAuxiliaryLayerLowCountMass_nonneg S y M (hvalid y hy))

theorem expectation_eq_finite (w : ℕ → ℝ) (S M : ℕ) {N : ℕ}
    (hzero : ∀ y, N ≤ y → w y = 0) (f : Finset ℕ → ℝ) :
    (∑ F ∈ (offsetWindow S).powerset, mass w S M F * f F) =
      ∑ y ∈ range N, w y *
        (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryLayerFrameMass S y M F * f F) := by
  unfold mass
  simp_rw [weighted_tsum_eq_sum_of_tail_zero w _ hzero, sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, mul_sum]

/-- Explicit (cutoff,presieve,original-count) expectation formula. -/
theorem expectation_eq_retained_layers (w : ℕ → ℝ) (S M : ℕ) {N : ℕ}
    (hzero : ∀ y, N ≤ y → w y = 0) (f : Finset ℕ → ℝ) :
    (∑ F ∈ (offsetWindow S).powerset, mass w S M F * f F) =
      ∑ y ∈ range N, w y *
        ((∑ σ : ResidueChoice S, ∑ n ∈ Icc M (presieveSurvivors S σ).card,
          cardinalityLayer (presieveSurvivors S σ) (lateRootLaw S y (presieveSurvivors S σ)) n *
            auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) f) /
              (Fintype.card (ResidueChoice S) : ℝ)) := by
  rw [expectation_eq_finite w S M hzero]
  simp_rw [CoreActualFrameRectangles.layer_expectation]

theorem mass_add_missing (w : ℕ → ℝ) (S M : ℕ) {N : ℕ}
    (hzero : ∀ y, N ≤ y → w y = 0) (hsum : ∑ y ∈ range N, w y = 1)
    (hvalid : Valid w S) :
    (∑ F ∈ (offsetWindow S).powerset, mass w S M F) + missing w S M = 1 := by
  have he := expectation_eq_finite w S M hzero (fun _ => 1)
  simp only [mul_one] at he
  rw [he, missing, weighted_tsum_eq_sum_of_tail_zero w _ hzero,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ y ∈ range N, w y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← mul_add]
      by_cases hw : w y = 0
      · simp only [hw, zero_mul]
      · rw [coreAuxiliaryLayerFrameMass_add_low_eq_one S y M (hvalid y hw), mul_one]
    _ = 1 := hsum

theorem missing_eq_original_failure (w : ℕ → ℝ) (S M : ℕ) {N : ℕ}
    (hzero : ∀ y, N ≤ y → w y = 0) (hvalid : Valid w S) :
    missing w S M = Stopped.failureMass (offsetWindow S) (CoreCalibratedMixtureMoments.law w S) M := by
  rw [CoreCalibratedMixtureCountException.failureMass_eq_finite w S M hzero,
    missing, weighted_tsum_eq_sum_of_tail_zero w _ hzero]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hw : w y = 0
  · simp only [hw, zero_mul]
  · rw [CoreActualFrameRectangleLimit.lowCountMass_eq_failure S y M (hvalid y hw)]

def completed (w : ℕ → ℝ) (S M : ℕ) (F : Finset ℕ) : ℝ :=
  mass w S M F + if F = ∅ then missing w S M else 0

theorem completed_nonneg (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y) (S M : ℕ)
    (hvalid : Valid w S) (F : Finset ℕ) : 0 ≤ completed w S M F := by
  unfold completed
  apply add_nonneg (mass_nonneg w hw S M hvalid F)
  split_ifs
  · exact missing_nonneg w hw S M hvalid
  · exact le_rfl

theorem completed_expectation (w : ℕ → ℝ) (S M : ℕ) (f : Finset ℕ → ℝ) :
    (∑ F ∈ (offsetWindow S).powerset, completed w S M F * f F) =
      (∑ F ∈ (offsetWindow S).powerset, mass w S M F * f F) + missing w S M * f ∅ := by
  simp only [completed, add_mul, Finset.sum_add_distrib]
  congr 1
  simp [ite_mul]

theorem completed_total (w : ℕ → ℝ) (S M : ℕ) {N : ℕ}
    (hzero : ∀ y, N ≤ y → w y = 0) (hsum : ∑ y ∈ range N, w y = 1)
    (hvalid : Valid w S) : (∑ F ∈ (offsetWindow S).powerset, completed w S M F) = 1 := by
  have hh := completed_expectation w S M (fun _ => 1)
  simp only [mul_one] at hh
  rw [hh]
  exact mass_add_missing w S M hzero hsum hvalid

theorem coordinate_mean_le (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y) (S M j : ℕ) {N : ℕ}
    (hzero : ∀ y, N ≤ y → w y = 0) (hsum : ∑ y ∈ range N, w y = 1)
    (hvalid : Valid w S) (hj : j + 1 < M) {G C : ℝ} (hG : 0 < G)
    (hcal : ∀ y, w y ≠ 0 → roughGapScale y / G ≤ C) :
    (∑ F ∈ (offsetWindow S).powerset, mass w S M F * ((subsetGap F j : ℝ) / G)) ≤ 2 * C := by
  rw [expectation_eq_finite w S M hzero]
  calc
    _ ≤ ∑ y ∈ range N, w y * (2 * C) := by
      apply sum_le_sum
      intro y hy
      by_cases hwy : w y = 0
      · simp only [hwy, zero_mul, le_refl]
      · apply mul_le_mul_of_nonneg_left _ (hw y)
        simp_rw [← mul_div_assoc]
        rw [← Finset.sum_div, coreAuxiliaryLayerFrameMass_subsetGap_expectation,
          coreAuxiliaryLayerPhysicalGapMean_eq_actual S y M j (hvalid y hwy) (by omega)]
        have hmean := div_le_div_of_nonneg_right (coreAuxiliaryPhysicalGapMean_le y S M j hj) hG.le
        have hbound := mul_le_mul_of_nonneg_left (hcal y hwy) (by norm_num : (0 : ℝ) ≤ 2)
        exact hmean.trans (by change 2 * (eulerProdNat y)⁻¹ / G ≤ _; simpa only [roughGapScale, mul_div_assoc] using hbound)
    _ = 2 * C := by rw [← Finset.sum_mul, hsum, one_mul]

theorem subsetGap_empty (j : ℕ) : subsetGap ∅ j = 0 := by simp [subsetGap, orderStat]

def frame {r : ℕ} (q : Fin r → ℕ) (G : ℝ) (F : Finset ℕ) : Fin r → ℝ :=
  fun i => (subsetGap F (q i) : ℝ) / G

theorem frame_nonneg {r : ℕ} (q : Fin r → ℕ) {G : ℝ} (hG : 0 ≤ G)
    (F : Finset ℕ) (i : Fin r) : 0 ≤ frame q G F i := div_nonneg (Nat.cast_nonneg _) hG

theorem frame_empty {r : ℕ} (q : Fin r → ℕ) (G : ℝ) : frame q G ∅ = 0 := by
  funext i
  simp only [frame, subsetGap_empty, Nat.cast_zero, zero_div, Pi.zero_apply]

theorem completed_norm_mean_le {r : ℕ} (q : Fin r → ℕ)
    (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y) (S M : ℕ) {N : ℕ}
    (hzero : ∀ y, N ≤ y → w y = 0) (hsum : ∑ y ∈ range N, w y = 1)
    (hvalid : Valid w S) (hq : ∀ i, q i + 1 < M) {G C : ℝ} (hG : 0 < G)
    (hcal : ∀ y, w y ≠ 0 → roughGapScale y / G ≤ C) :
    (∑ F ∈ (offsetWindow S).powerset, completed w S M F * ‖frame q G F‖) ≤ (r : ℝ) * (2 * C) := by
  rw [completed_expectation, frame_empty, norm_zero, mul_zero, add_zero]
  have hn (F : Finset ℕ) : ‖frame q G F‖ ≤ ∑ i : Fin r, frame q G F i := by
    apply (pi_norm_le_iff_of_nonneg (sum_nonneg fun i _ => frame_nonneg q hG.le F i)).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (frame_nonneg q hG.le F i)]
    exact Finset.single_le_sum (f := fun j : Fin r ↦ frame q G F j)
      (fun j _ ↦ frame_nonneg q hG.le F j) (Finset.mem_univ i)
  calc
    _ ≤ ∑ F ∈ (offsetWindow S).powerset, mass w S M F * ∑ i : Fin r, frame q G F i :=
      sum_le_sum fun F hF => mul_le_mul_of_nonneg_left (hn F) (mass_nonneg w hw S M hvalid F)
    _ = ∑ i : Fin r, ∑ F ∈ (offsetWindow S).powerset, mass w S M F * frame q G F i := by
      simp_rw [mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ _i : Fin r, 2 * C :=
      sum_le_sum fun i _ => coordinate_mean_le w hw S M (q i) hzero hsum hvalid (hq i) hG hcal
    _ = (r : ℝ) * (2 * C) := by simp

/-- The cutoff remains an ORIGINAL-law expectation, not a tail estimate
under the auxiliary reweighting. -/
def originalBad (w : ℕ → ℝ) (S M j : ℕ) (J : Finset ℕ) (G R : ℝ) : ℝ :=
  ∑' y : ℕ, w y * CoreOriginalDeletedFrame.highMean y S M (fun U =>
    if ∃ i ∈ J, R < (subsetGap (CoreOriginalDeletedFrame.deleted j U) i : ℝ) / G then 1 else 0)

theorem originalBad_le (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y) (S M j : ℕ) (J : Finset ℕ)
    {N : ℕ} (hzero : ∀ y, N ≤ y → w y = 0) (hsum : ∑ y ∈ range N, w y = 1)
    (hj0 : 1 ≤ j) (hjM : j ≤ M) (hJ : ∀ i ∈ J, i + 1 < M)
    {G R C : ℝ} (hG : 0 < G) (hR : 0 < R)
    (hcal : ∀ y, w y ≠ 0 → roughGapScale y / G ≤ C) :
    originalBad w S M j J G R ≤ 2 * (J.card : ℝ) * C / R := by
  unfold originalBad
  rw [weighted_tsum_eq_sum_of_tail_zero w _ hzero]
  calc
    _ ≤ ∑ y ∈ range N, w y * (2 * (J.card : ℝ) * C / R) := by
      apply sum_le_sum
      intro y hy
      by_cases hwy : w y = 0
      · simp only [hwy, zero_mul, le_refl]
      · apply mul_le_mul_of_nonneg_left _ (hw y)
        have hh := CoreOriginalDeletedFrame.original_bad_frame_mass_le y S M j J hj0 hjM hJ hG hR
        have hc := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hcal y hwy) (by positivity : 0 ≤ 2 * (J.card : ℝ))) hR.le
        exact hh.trans (by simpa only [roughGapScale, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hc)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Exact actual profile validity and finite support are derived, not
supplied as assumptions about the auxiliary law. -/
theorem eventually_profile_data {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, 0 < G X ∧ Valid (w X) (physicalSpan G M X) ∧
      (∀ y, w X y ≠ 0 → roughGapScale y / G X ≤ 2) ∧
      ∃ N : ℕ, (∀ y, N ≤ y → w X y = 0) ∧ (∑ y ∈ range N, w X y) = 1 := by
  filter_upwards [hG.eventually_gt_atTop 0, hcal 1 (by norm_num),
    eventually_support_above_span hG hκ hM hcal] with X hg hc hsup
  obtain ⟨N, hzero, hsumN, heval⟩ := exists_real_finite_representation (w X) (hw X) (hsum X) hg hc
  refine ⟨hg, (fun y hy => (hsup y (lt_of_le_of_ne (hw X y) (Ne.symm hy))).le), ?_, N, hzero, hsumN⟩
  intro y hy
  have hh := (abs_le.mp (hc y (lt_of_le_of_ne (hw X y) (Ne.symm hy)))).2
  linarith

theorem tendsto_missing_zero {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G) :
    Tendsto (fun X => missing (w X) (physicalSpan G M X) (M X)) atTop (𝓝 0) := by
  apply (tendsto_mixture_failure_zero hG hκ hM hw hsum hcal).congr'
  filter_upwards [eventually_profile_data hG hκ hM hw hsum hcal] with X hX
  obtain ⟨N, hzero, hsumN⟩ := hX.2.2.2
  exact (missing_eq_original_failure (w X) _ _ hzero hX.2.1).symm

theorem eventually_completed_norm_mean_le {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G) (r : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ q : Fin r → ℕ, (∀ i, q i + 1 < M X) →
      (∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
        completed (w X) (physicalSpan G M X) (M X) F * ‖frame q (G X) F‖) ≤ 4 * (r : ℝ) := by
  filter_upwards [eventually_profile_data hG hκ hM hw hsum hcal] with X hX
  obtain ⟨N, hzero, hsumN⟩ := hX.2.2.2
  intro q hq
  have hh := completed_norm_mean_le q (w X) (hw X) _ _ hzero hsumN hX.2.1 hq hX.1 hX.2.2.1
  exact hh.trans_eq (by ring)

end
end PrimeGapNormality.Prime.CoreCalibratedAuxiliaryFrame
