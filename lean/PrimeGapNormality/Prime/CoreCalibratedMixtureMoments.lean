import PrimeGapNormality.Prime.CoreCalibratedMixtureProfile
import PrimeGapNormality.Prime.FiniteSelbergAsymptoticCap
import PrimeGapNormality.Prime.PresieveSelbergCap
import PrimeGapNormality.Prime.MertensAbelianBridge
import PrimeGapNormality.Prime.ModelMoments
import PrimeGapNormality.Prime.CrtNestedCutoffFirstMoment

/-!
# All-order factorial moments of actual calibrated mixtures

Selberg with slack 1/24, the proved Euler tail V(S) log S > 1/2,
and calibration tolerance 1/100 give conditional mean <= (490/99)M < 5M.
Only a fixed tolerance is used, never an error rate times M. The exact
late-root moments are used below, including their zero branch beyond the
candidate cardinality. Arbitrary mass-one real cutoff weights are reduced
exactly to finite support by calibration, uniformly before every j.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedMixtureMoments

open Finset Filter CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
  CoreRoughSyntheticScale
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1500000

theorem eulerProd_le_calibrated_fraction {G : ℝ} (hG : 0 < G) (y : ℕ)
    (hcal : |roughGapScale y / G - 1| ≤ 1 / 100) :
    eulerProdNat y ≤ (100 / 99 : ℝ) / G := by
  have hl := (abs_le.mp hcal).1
  have hh : (99 / 100 : ℝ) * G ≤ roughGapScale y :=
    (le_div_iff₀ hG).mp (by linarith)
  have hi := one_div_le_one_div_of_le (by positivity : 0 < (99 / 100 : ℝ) * G) hh
  calc
    eulerProdNat y = 1 / roughGapScale y := by simp [roughGapScale]
    _ ≤ 1 / ((99 / 100 : ℝ) * G) := hi
    _ = (100 / 99 : ℝ) / G := by ring

/-- Uniform actual presieve mean cap at arbitrary calibrated model
profiles. No presieve distribution or mean estimate is an input. -/
theorem eventually_presieve_mean_le_five {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, 2 ≤ physicalSpan G M X ∧
      ∀ y : ℕ, 0 < w X y → physicalSpan G M X ≤ y ∧
        ∀ σ : ResidueChoice (physicalSpan G M X),
          ((presieveSurvivors (physicalSpan G M X) σ).card : ℝ) *
            lateRetention (physicalSpan G M X) y ≤ 5 * (M X : ℝ) := by
  have hS := tendsto_physicalSpan_atTop hG hκ hM
  filter_upwards [hS.eventually (eventually_presieveSurvivors_card_le_two_add_eps
      (by norm_num : (0 : ℝ) < 1 / 24)),
    hS.eventually eventually_half_lt_eulerProdNat_mul_log,
    hS.eventually_ge_atTop 2, hG.eventually_gt_atTop 0,
    eventually_support_above_span hG hκ hM hcal,
    hcal (1 / 100) (by norm_num)] with X hcap hEuler hS2 hg hsup hcalX
  refine ⟨hS2, ?_⟩
  intro y hy
  refine ⟨(hsup y hy).le, ?_⟩
  intro σ
  let S := physicalSpan G M X
  change (1 / 2 : ℝ) < eulerProdNat S * Real.log (S : ℝ) at hEuler
  have hlog : 0 < Real.log (S : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < S from lt_of_lt_of_le (by norm_num) hS2))
  have hV : 0 < eulerProdNat S := eulerProdNat_pos S
  have hinv : 1 / eulerProdNat S ≤ 2 * Real.log (S : ℝ) := by
    apply (div_le_iff₀ hV).2
    nlinarith
  have hyV := eulerProd_le_calibrated_fraction hg y (hcalX y hy)
  have hret : lateRetention S y ≤ (200 / 99 : ℝ) * Real.log (S : ℝ) / G X := by
    calc
      lateRetention S y ≤ eulerProdNat y / eulerProdNat S :=
        rootedEulerProdNat_le_div (hsup y hy).le hS2
      _ = eulerProdNat y * (1 / eulerProdNat S) := by ring
      _ ≤ ((100 / 99 : ℝ) / G X) * (2 * Real.log (S : ℝ)) :=
        mul_le_mul hyV hinv (by positivity) (by positivity)
      _ = (200 / 99 : ℝ) * Real.log (S : ℝ) / G X := by ring
  have hcard : ((presieveSurvivors S σ).card : ℝ) ≤
      (49 / 24 : ℝ) * (S : ℝ) / Real.log (S : ℝ) := by
    simpa only [show (2 : ℝ) + 1 / 24 = 49 / 24 by norm_num] using hcap σ
  have hspan : (S : ℝ) ≤ (6 / 5 : ℝ) * (M X : ℝ) * G X :=
    Nat.floor_le (by positivity)
  have hratio : (S : ℝ) / G X ≤ (6 / 5 : ℝ) * (M X : ℝ) :=
    (div_le_iff₀ hg).mpr hspan
  calc
    ((presieveSurvivors S σ).card : ℝ) * lateRetention S y ≤
        ((49 / 24 : ℝ) * (S : ℝ) / Real.log (S : ℝ)) *
          ((200 / 99 : ℝ) * Real.log (S : ℝ) / G X) :=
      mul_le_mul hcard hret (rootedEulerProdNat_pos hS2).le (by positivity)
    _ = (1225 / 297 : ℝ) * ((S : ℝ) / G X) := by
      field_simp [hlog.ne', hg.ne'] <;> ring
    _ ≤ (1225 / 297 : ℝ) * ((6 / 5 : ℝ) * (M X : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = (490 / 99 : ℝ) * (M X : ℝ) := by ring
    _ ≤ 5 * (M X : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (M X : ℝ) from Nat.cast_nonneg _]

/-! The following finite steps generalize the private helpers in
FiniteRootMixSmallMomentBound. No private-name access or new probabilistic
assumption is used. -/

theorem lateInclusionFactor_le_retention_pow {S y j : ℕ} (hS : 2 ≤ S) (hjS : j ≤ S) :
    lateInclusionFactor S y j ≤ lateRetention S y ^ j := by
  have hps : ∀ p ∈ latePrimes S y, 2 ≤ p := by
    intro p hp
    exact (Nat.prime_of_mem_primesLE (sdiff_subset hp)).two_le
  have hjp : ∀ p ∈ latePrimes S y, j ≤ p - 1 := by
    intro p hp
    have hpprime := Nat.prime_of_mem_primesLE (sdiff_subset hp)
    have hpnot : p ∉ Nat.primesLE S := (Finset.mem_sdiff.mp hp).2
    have hSp : S < p := by
      by_contra h
      exact hpnot (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt h, hpprime⟩)
    omega
  have hh := palmJointSurvivePrimes_le_theta_pow (latePrimes S y) j hps hjp
  simpa [lateInclusionFactor, lateRetention, rootedEulerProdNat,
    palmJointSurvivePrimes, palmJointSurvive, palmThetaPrimes, palmTheta,
    palmHitProb, div_eq_mul_inv] using hh

theorem lateRootLaw_countMoment_le {S y m j : ℕ} (hS : 2 ≤ S) (hSy : S ≤ y)
    (σ : ResidueChoice S)
    (hmean : ((presieveSurvivors S σ).card : ℝ) * lateRetention S y ≤ (5 : ℝ) * m) :
    Stopped.countMoment (offsetWindow S) (lateRootLaw S y (presieveSurvivors S σ)) j ≤
      ((5 : ℝ) * m) ^ j / (j.factorial : ℝ) := by
  let A := presieveSurvivors S σ
  have hA : A ⊆ offsetWindow S := corePresieveSurvivors_subset_Icc S σ
  have hAS : A.card ≤ S := by
    have hh := Finset.card_le_card hA
    simpa only [offsetWindow, Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hrestrict : Stopped.countMoment (offsetWindow S) (lateRootLaw S y A) j =
      ∑ E ∈ A.powerset, lateRootLaw S y A E * (Nat.choose E.card j : ℝ) := by
    unfold Stopped.countMoment
    refine (sum_subset (powerset_mono.mpr hA) ?_).symm
    intro E hE hnot
    rw [lateRootLaw_eq_zero_of_not_subset (fun hEA => hnot (mem_powerset.mpr hEA)), zero_mul]
  rw [hrestrict]
  have hcomm : (∑ E ∈ A.powerset, lateRootLaw S y A E * (Nat.choose E.card j : ℝ)) =
      ∑ E ∈ A.powerset, (Nat.choose E.card j : ℝ) * lateRootLaw S y A E :=
    Finset.sum_congr rfl fun E _ => mul_comm _ _
  rw [hcomm]
  by_cases hj : j ≤ A.card
  · have hmom := (corePresieveLaw_exactCountMoments S y σ hSy).2.2.1 j hj
    rw [hmom]
    have hfac := lateInclusionFactor_le_retention_pow (y := y) hS (hj.trans hAS)
    have hθ0 : 0 ≤ lateRetention S y := (rootedEulerProdNat_pos hS).le
    have hm0 : 0 ≤ (A.card : ℝ) * lateRetention S y := mul_nonneg (Nat.cast_nonneg _) hθ0
    calc
      (Nat.choose A.card j : ℝ) * lateInclusionFactor S y j ≤
          (Nat.choose A.card j : ℝ) * lateRetention S y ^ j :=
        mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg _)
      _ ≤ ((A.card : ℝ) ^ j / (j.factorial : ℝ)) * lateRetention S y ^ j :=
        mul_le_mul_of_nonneg_right (choose_le_pow_div_real A.card j) (pow_nonneg hθ0 j)
      _ = ((A.card : ℝ) * lateRetention S y) ^ j / (j.factorial : ℝ) := by
        rw [mul_pow]
        ring
      _ ≤ ((5 : ℝ) * m) ^ j / (j.factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hm0 hmean j) (Nat.cast_nonneg _)
  · rw [(corePresieveLaw_exactCountMoments S y σ hSy).2.2.2 j (Nat.lt_of_not_ge hj)]
    positivity

theorem actualRootLaw_countMoment_eq_avg (S y j : ℕ) (hSy : S ≤ y) :
    Stopped.countMoment (offsetWindow S) (actualRootLaw y S) j =
      (∑ σ : ResidueChoice S, Stopped.countMoment (offsetWindow S)
        (lateRootLaw S y (presieveSurvivors S σ)) j) /
          (Fintype.card (ResidueChoice S) : ℝ) := by
  unfold Stopped.countMoment
  simp_rw [coreActualRootLaw_eq_avg_presieve S y hSy, div_mul_eq_mul_div, sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]

theorem actualRootLaw_countMoment_le {S y m : ℕ} (hS : 2 ≤ S) (hSy : S ≤ y)
    (hmean : ∀ σ : ResidueChoice S,
      ((presieveSurvivors S σ).card : ℝ) * lateRetention S y ≤ (5 : ℝ) * m) (j : ℕ) :
    Stopped.countMoment (offsetWindow S) (actualRootLaw y S) j ≤
      ((5 : ℝ) * m) ^ j / (j.factorial : ℝ) := by
  rw [actualRootLaw_countMoment_eq_avg S y j hSy]
  have hC : (0 : ℝ) < Fintype.card (ResidueChoice S) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ResidueChoice S))
  apply (div_le_iff₀ hC).2
  calc
    (∑ σ : ResidueChoice S, Stopped.countMoment (offsetWindow S)
        (lateRootLaw S y (presieveSurvivors S σ)) j) ≤
        ∑ _σ : ResidueChoice S, ((5 : ℝ) * m) ^ j / (j.factorial : ℝ) :=
      sum_le_sum fun σ _ => lateRootLaw_countMoment_le hS hSy σ (hmean σ)
    _ = (((5 : ℝ) * m) ^ j / (j.factorial : ℝ)) *
        (Fintype.card (ResidueChoice S) : ℝ) := by
      simp only [sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

theorem eventually_support_all_moments_le {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, 0 < w X y → ∀ j : ℕ,
      Stopped.countMoment (offsetWindow (physicalSpan G M X))
        (actualRootLaw y (physicalSpan G M X)) j ≤
          ((5 : ℝ) * M X) ^ j / (j.factorial : ℝ) := by
  filter_upwards [eventually_presieve_mean_le_five hG hκ hM hcal] with X hX
  intro y hy j
  exact actualRootLaw_countMoment_le hX.1 (hX.2 y hy).1 (hX.2 y hy).2 j

/-- Actual countable-cutoff mixture. Uniform calibration will prove that
this tsum is eventually exactly finite, even for unbounded test functions. -/
def law (w : ℕ → ℝ) (S : ℕ) (U : Finset ℕ) : ℝ :=
  ∑' y : ℕ, w y * actualRootLaw y S U

theorem law_nonneg (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y) (S : ℕ) (U : Finset ℕ) :
    0 ≤ law w S U :=
  tsum_nonneg fun y => mul_nonneg (hw y) (crtNestFM_actualRootLaw_nonneg y S U)

theorem law_total_of_tail_zero (w : ℕ → ℝ) (S : ℕ) {N : ℕ}
    (hzero : ∀ y : ℕ, N ≤ y → w y = 0) (hsum : ∑ y ∈ range N, w y = 1) :
    (∑ U ∈ (offsetWindow S).powerset, law w S U) = 1 := by
  unfold law
  simp_rw [weighted_tsum_eq_sum_of_tail_zero w _ hzero]
  rw [Finset.sum_comm]
  simp only [← mul_sum, crtNestFM_actualRootLaw_sum, mul_one]
  exact hsum

theorem eventually_law_total {G : ℕ → ℝ} {w : ℕ → ℕ → ℝ}
    (hG : Tendsto G atTop atTop) (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G) (S : ℕ → ℕ) :
    ∀ᶠ X : ℕ in atTop, (∑ U ∈ (offsetWindow (S X)).powerset, law (w X) (S X) U) = 1 := by
  filter_upwards [hcal 1 (by norm_num), hG.eventually_gt_atTop 0] with X hcalX hg
  obtain ⟨N, hzero, hsumN, heval⟩ := exists_real_finite_representation
    (w X) (hw X) (hsum X) hg hcalX
  exact law_total_of_tail_zero (w X) (S X) hzero hsumN

theorem countMoment_eq_finite (w : ℕ → ℝ) (S j : ℕ) {N : ℕ}
    (hzero : ∀ y : ℕ, N ≤ y → w y = 0) :
    Stopped.countMoment (offsetWindow S) (law w S) j =
      ∑ y ∈ range N, w y * Stopped.countMoment (offsetWindow S) (actualRootLaw y S) j := by
  unfold Stopped.countMoment law
  simp_rw [weighted_tsum_eq_sum_of_tail_zero w _ hzero, sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, mul_sum]

/-- The paper's exact all-order bound. The eventual scale is chosen BEFORE
all natural j, and includes j=0 and every j above the window cardinality.
No factorial moment, presieve cap, or finite support is an end hypothesis. -/
theorem eventually_all_countMoments_le_five {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, ∀ j : ℕ,
      Stopped.countMoment (offsetWindow (physicalSpan G M X))
        (law (w X) (physicalSpan G M X)) j ≤
          ((5 : ℝ) * M X) ^ j / (j.factorial : ℝ) := by
  filter_upwards [eventually_support_all_moments_le hG hκ hM hcal,
    hcal 1 (by norm_num), hG.eventually_gt_atTop 0] with X hm hcalX hg
  obtain ⟨N, hzero, hsumN, heval⟩ := exists_real_finite_representation
    (w X) (hw X) (hsum X) hg hcalX
  intro j
  rw [countMoment_eq_finite (w X) _ j hzero]
  calc
    (∑ y ∈ range N, w X y * Stopped.countMoment (offsetWindow (physicalSpan G M X))
        (actualRootLaw y (physicalSpan G M X)) j) ≤
        ∑ y ∈ range N, w X y * (((5 : ℝ) * M X) ^ j / (j.factorial : ℝ)) := by
      apply sum_le_sum
      intro y hy
      by_cases hwy : w X y = 0
      · simp only [hwy, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left
          (hm y (lt_of_le_of_ne (hw X y) (Ne.symm hwy)) j) (hw X y)
    _ = ((5 : ℝ) * M X) ^ j / (j.factorial : ℝ) := by
      rw [← Finset.sum_mul, hsumN, one_mul]

end
end PrimeGapNormality.Prime.CoreCalibratedMixtureMoments
