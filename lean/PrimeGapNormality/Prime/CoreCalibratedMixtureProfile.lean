import PrimeGapNormality.Prime.CoreCalibratedMixtureFiniteSupport
import PrimeGapNormality.Prime.CoreModelSingleSite
import PrimeGapNormality.Prime.CrtPhysicalRetentionLeEulerQuot
import PrimeGapNormality.Prime.CoreRootedGapExpectation

/-!
# Scalar profiles for arbitrary qualitatively calibrated rooted mixtures

The physical window is floor((6/5) M G), with M/log G -> kappa > 0.
Support separation and a vanishing singleton cap are proved from the
actual inverse Euler product, not assumed as model estimates. Nonnegative
weights may have arbitrary support; no quantitative calibration rate,
normalization, or finite-support hypothesis is needed for these outputs.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedMixtureProfile

open Finset Filter CoreRoughSyntheticScale CoreRoughScaleLimits
  CoreCalibratedMixtureFiniteSupport
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1000000

def physicalSpan (G : ℕ → ℝ) (M : ℕ → ℕ) (X : ℕ) : ℕ :=
  ⌊((6 : ℝ) / 5) * (M X : ℝ) * G X⌋₊

theorem eventually_rank_pos {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ)) :
    ∀ᶠ X : ℕ in atTop, 1 ≤ M X := by
  filter_upwards [(tendsto_order.mp hM).1 (κ / 2) (by linarith),
    (Real.tendsto_log_atTop.comp hG).eventually_gt_atTop 0] with X hr hl
  simp only [Function.comp_apply] at hl
  have hh := (lt_div_iff₀ hl).mp hr
  have hp : (0 : ℝ) < M X := (mul_pos (by positivity : 0 < κ / 2) hl).trans hh
  exact Nat.succ_le_iff.mpr (Nat.cast_pos.mp hp)

theorem tendsto_physicalSpan_atTop {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ)) :
    Tendsto (physicalSpan G M) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_nat_floor_atTop.comp hG)
  filter_upwards [eventually_rank_pos hG hκ hM, hG.eventually_ge_atTop 0] with X hMX hGX
  apply Nat.floor_mono
  have hm : (1 : ℝ) ≤ M X := by exact_mod_cast hMX
  have hc : (1 : ℝ) ≤ (6 / 5) * (M X : ℝ) := by nlinarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hGX

theorem eventually_physicalSpan_le_quadratic {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ)) :
    ∀ᶠ X : ℕ in atTop,
      (physicalSpan G M X : ℝ) ≤ (2 * (κ + 1)) * (G X) ^ 2 := by
  filter_upwards [(tendsto_order.mp hM).2 (κ + 1) (by linarith),
    (Real.tendsto_log_atTop.comp hG).eventually_gt_atTop 0,
    hG.eventually_gt_atTop 0] with X hr hl hg
  simp only [Function.comp_apply] at hl
  have hm : (M X : ℝ) ≤ (κ + 1) * G X := by
    have hh := (div_lt_iff₀ hl).mp hr
    have hlog : Real.log (G X) ≤ G X := (Real.log_le_sub_one_of_pos hg).trans (by linarith)
    exact hh.le.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
  have hfloor : (physicalSpan G M X : ℝ) ≤ ((6 : ℝ) / 5) * (M X : ℝ) * G X :=
    Nat.floor_le (by positivity)
  calc
    (physicalSpan G M X : ℝ) ≤ ((6 : ℝ) / 5) * (M X : ℝ) * G X := hfloor
    _ ≤ (2 * (M X : ℝ)) * G X := by
      apply mul_le_mul_of_nonneg_right _ hg.le
      nlinarith [show (0 : ℝ) ≤ (M X : ℝ) from Nat.cast_nonneg (M X)]
    _ ≤ (2 * ((κ + 1) * G X)) * G X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) hg.le
    _ = (2 * (κ + 1)) * (G X) ^ 2 := by ring

private theorem tendsto_log_div_zero {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) :
    Tendsto (fun X => Real.log (G X) / G X) atTop (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  exact (hl.comp hG).congr' (Eventually.of_forall fun X => rfl)

theorem tendsto_log_physicalSpan_div_zero {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ)) :
    Tendsto (fun X => Real.log (physicalSpan G M X : ℝ) / G X) atTop (𝓝 0) := by
  let c := 2 * (κ + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hi := (tendsto_inv_atTop_zero.comp hG).const_mul (Real.log c)
  have hl := (tendsto_log_div_zero hG).const_mul 2
  have hlim : Tendsto (fun X => (Real.log c + 2 * Real.log (G X)) / G X) atTop (𝓝 0) := by
    have hh := hi.add hl
    simp only [mul_zero, add_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun X => by dsimp only [Function.comp_apply]; ring
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [(tendsto_physicalSpan_atTop hG hκ hM).eventually_ge_atTop 1,
      hG.eventually_ge_atTop 0] with X hS hg
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hS)) hg
  · filter_upwards [eventually_physicalSpan_le_quadratic hG hκ hM,
      (tendsto_physicalSpan_atTop hG hκ hM).eventually_ge_atTop 1,
      hG.eventually_gt_atTop 0] with X hbound hS hg
    have hSp : (0 : ℝ) < physicalSpan G M X := Nat.cast_pos.mpr (by omega)
    have hh := Real.log_le_log hSp hbound
    have heq : Real.log (c * (G X) ^ 2) = Real.log c + 2 * Real.log (G X) := by
      rw [Real.log_mul hc.ne' (pow_ne_zero _ hg.ne'), Real.log_pow]
      norm_num
    rw [heq] at hh
    exact div_le_div_of_nonneg_right hh hg.le

/-- Crucial scale separation: the Euler scale at the physical presieve
window is negligible compared with the calibrated final Euler scale. -/
theorem tendsto_presieve_gap_div_zero {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ)) :
    Tendsto (fun X => roughGapScale (physicalSpan G M X) / G X) atTop (𝓝 0) := by
  have hh := (tendsto_log_physicalSpan_div_zero hG hκ hM).div_const eulerProdLowerConst
  simp only [zero_div] at hh
  refine squeeze_zero' ?_ ?_ hh
  · filter_upwards [hG.eventually_ge_atTop 0] with X hg
    exact div_nonneg (roughGapScale_pos _).le hg
  · filter_upwards [(tendsto_physicalSpan_atTop hG hκ hM).eventually_ge_atTop 16,
      hG.eventually_ge_atTop 0] with X hS hg
    have he := div_le_div_of_nonneg_right (roughGapScale_le_log_div_lowerConst hS) hg
    exact he.trans_eq (by ring)

theorem roughGapScale_mono {a b : ℕ} (hab : a ≤ b) : roughGapScale a ≤ roughGapScale b := by
  unfold roughGapScale
  exact inv_anti₀ (eulerProdNat_pos b) (eulerProdNat_mono hab)

/-- Supported cutoffs lie STRICTLY above the entire physical window.
Only a fixed calibration tolerance 1/2 is used; no rate is required. -/
theorem eventually_support_above_span {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, 0 < w X y → physicalSpan G M X < y := by
  have hs := (tendsto_order.mp (tendsto_presieve_gap_div_zero hG hκ hM)).2
    (1 / 2) (by norm_num)
  filter_upwards [hs, hcal (1 / 2) (by norm_num), hG.eventually_gt_atTop 0]
    with X hsmall hcalX hg
  intro y hy
  have hlo := (abs_le.mp (hcalX y hy)).1
  by_contra hnot
  have hm := div_le_div_of_nonneg_right (roughGapScale_mono (Nat.not_lt.mp hnot)) hg.le
  linarith

def singletonCap (G : ℕ → ℝ) (M : ℕ → ℕ) (X : ℕ) : ℝ :=
  (2 / eulerProdLowerConst) * (Real.log (physicalSpan G M X : ℝ) / G X)

theorem tendsto_singletonCap_zero {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ)) :
    Tendsto (singletonCap G M) atTop (𝓝 0) := by
  change Tendsto (fun X =>
    (2 / eulerProdLowerConst) * (Real.log (physicalSpan G M X : ℝ) / G X))
    atTop (𝓝 0)
  have hh := (tendsto_log_physicalSpan_div_zero hG hκ hM).const_mul (2 / eulerProdLowerConst)
  simpa only [mul_zero] using hh

theorem eulerProd_le_two_div {G : ℝ} (hG : 0 < G) (y : ℕ)
    (hcal : |roughGapScale y / G - 1| ≤ 1 / 2) : eulerProdNat y ≤ 2 / G := by
  have hlo := (abs_le.mp hcal).1
  have hhalf : G / 2 ≤ roughGapScale y := by
    have hh : (1 / 2 : ℝ) ≤ roughGapScale y / G := by linarith
    have ht := (le_div_iff₀ hG).mp hh
    linarith
  have hi := one_div_le_one_div_of_le (by positivity : 0 < G / 2) hhalf
  simpa only [roughGapScale, one_div, inv_inv, inv_div, inv_inv] using hi

theorem eventually_support_retention_le {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, 16 ≤ physicalSpan G M X ∧
      ∀ y : ℕ, 0 < w X y → physicalSpan G M X < y ∧
        lateRetention (physicalSpan G M X) y ≤ singletonCap G M X := by
  filter_upwards [eventually_support_above_span hG hκ hM hcal,
    (tendsto_physicalSpan_atTop hG hκ hM).eventually_ge_atTop 16,
    hcal (1 / 2) (by norm_num), hG.eventually_gt_atTop 0] with X hsup hS hcalX hg
  refine ⟨hS, ?_⟩
  intro y hy
  refine ⟨hsup y hy, ?_⟩
  have hV := eulerProd_le_two_div hg y (hcalX y hy)
  have hlog : 0 ≤ Real.log (physicalSpan G M X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ physicalSpan G M X by omega))
  calc
    lateRetention (physicalSpan G M X) y ≤
        eulerProdNat y * Real.log (physicalSpan G M X : ℝ) / eulerProdLowerConst :=
      crtPhysRet_le_eulerProd_mul_log (by omega) hS (hsup y hy).le
    _ ≤ (2 / G X) * Real.log (physicalSpan G M X : ℝ) / eulerProdLowerConst :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hV hlog) eulerProdLowerConst_pos.le
    _ = singletonCap G M X := by unfold singletonCap; ring

/-- Nonzero support formulation for arbitrary nonnegative real weights. -/
theorem eventually_nonzero_support_retention_le {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y) (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, 16 ≤ physicalSpan G M X ∧
      ∀ y : ℕ, w X y ≠ 0 → physicalSpan G M X < y ∧
        lateRetention (physicalSpan G M X) y ≤ singletonCap G M X := by
  filter_upwards [eventually_support_retention_le hG hκ hM hcal] with X hX
  exact ⟨hX.1, fun y hy => hX.2 y (lt_of_le_of_ne (hw X y) (Ne.symm hy))⟩

theorem eventually_support_singleton_le {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, 0 < w X y → ∀ d : ℕ,
      1 ≤ d → d ≤ physicalSpan G M X →
      Stopped.inclusionMass (offsetWindow (physicalSpan G M X))
        (actualRootLaw y (physicalSpan G M X)) {d} ≤ singletonCap G M X := by
  filter_upwards [eventually_support_retention_le hG hκ hM hcal] with X hX
  intro y hy d hd1 hdS
  exact (CoreModelSingleSite.actualRootLaw_singleton_inclusion_le
    (by omega) (hX.2 y hy).1.le hd1 hdS).trans (hX.2 y hy).2

/-- The actual rooted physical gap, at arbitrary rank, averaged over the
literal residue-choice law. It is not a Bernoulli surrogate. -/
def rootedGapMean (y r : ℕ) : ℝ :=
  (∑ σ : ResidueChoice y,
    ((sievePoint y (residueOfChoice y σ) (r + 1) : ℝ) -
      (sievePoint y (residueOfChoice y σ) r : ℝ))) /
        (Fintype.card (ResidueChoice y) : ℝ)

theorem rootedGapMean_eq (y r : ℕ) : rootedGapMean y r = roughGapScale y :=
  core_rooted_sieve_gap_mean y r

theorem uniform_rootedGapMean_calibration {w : ℕ → ℕ → ℝ} {G : ℕ → ℝ}
    (hcal : UniformCalibration w G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, 0 < w X y → ∀ r : ℕ,
      |rootedGapMean y r / G X - 1| ≤ ε := by
  filter_upwards [hcal ε hε] with X hX
  intro y hy r
  rw [rootedGapMean_eq]
  exact hX y hy

def mixtureGapMean (w : ℕ → ℝ) (r : ℕ) : ℝ := ∑' y : ℕ, w y * rootedGapMean y r

/-- Actual gap means of a probability mixture inherit calibration. The
input weights may have arbitrary support; its eventual finite reduction is
proved from calibration, rather than supplied as a hypothesis. -/
theorem eventually_mixtureGapMean_calibrated {w : ℕ → ℕ → ℝ} {G : ℕ → ℝ}
    (hG : Tendsto G atTop atTop) (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ r : ℕ, |mixtureGapMean (w X) r / G X - 1| ≤ ε := by
  filter_upwards [hG.eventually_gt_atTop 0, hcal 1 (by norm_num), hcal ε hε]
    with X hg hcal1 hcale
  obtain ⟨N, hzero, hsumN, heval⟩ := exists_real_finite_representation
    (w X) (hw X) (hsum X) hg hcal1
  intro r
  have hid : mixtureGapMean (w X) r / G X - 1 =
      ∑ y ∈ range N, w X y * (rootedGapMean y r / G X - 1) := by
    unfold mixtureGapMean
    rw [heval]
    simp_rw [mul_sub, mul_one, ← mul_div_assoc]
    rw [Finset.sum_sub_distrib, Finset.sum_div, hsumN]
  rw [hid]
  calc
    |∑ y ∈ range N, w X y * (rootedGapMean y r / G X - 1)| ≤
        ∑ y ∈ range N, |w X y * (rootedGapMean y r / G X - 1)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ range N, w X y * ε := by
      apply sum_le_sum
      intro y hy
      rw [abs_mul, abs_of_nonneg (hw X y)]
      by_cases hwy : w X y = 0
      · simp only [hwy, zero_mul, le_refl]
      · apply mul_le_mul_of_nonneg_left _ (hw X y)
        rw [rootedGapMean_eq]
        exact hcale y (lt_of_le_of_ne (hw X y) (Ne.symm hwy))
    _ = ε := by rw [← Finset.sum_mul, hsumN, one_mul]

theorem tendsto_mixtureGapMean_normalized {w : ℕ → ℕ → ℝ} {G : ℕ → ℝ}
    (hG : Tendsto G atTop atTop) (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G)
    (r : ℕ → ℕ) :
    Tendsto (fun X => mixtureGapMean (w X) (r X) / G X) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_mixtureGapMean_calibrated hG hw hsum hcal
    (show 0 < ε / 2 by positivity)] with X hX
  rw [Real.dist_eq]
  exact (hX (r X)).trans_lt (by linarith)

end
end PrimeGapNormality.Prime.CoreCalibratedMixtureProfile
