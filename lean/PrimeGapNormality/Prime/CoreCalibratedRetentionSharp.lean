import PrimeGapNormality.Prime.CoreCalibratedMixtureProfile
import PrimeGapNormality.Prime.MertensAbelianBridge

/-!
# The paper's strict positive-insertion coefficient

For the literal physical span `floor((6/5) M G)`, qualitative calibration
alone gives `lateRetention S y * G / log G < 2`, simultaneously for every
positive-weight cutoff. Thus the finite resampling coefficient is strictly
less than 24. The identified Mertens product limit supplies the strict
margin; the coarse Euler lower constant is not substituted for that limit.

No calibration rate, bound on the support cardinality, or moment hypothesis
is used. This is a standalone precision supplier: it does not alter the
larger constants of existing qualitative model consumers.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedRetentionSharp

open Filter CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
open CoreRoughSyntheticScale
open scoped Topology

noncomputable section

/-- The exact logarithmic scale of the physical presieve span. -/
theorem tendsto_log_physicalSpan_div_log
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ)) :
    Tendsto (fun X => Real.log (physicalSpan G M X : ℝ) / Real.log (G X))
      atTop (𝓝 1) := by
  let c : ℝ := (6 / 5 : ℝ) * (κ + 1)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hlogG : Tendsto (fun X => Real.log (G X)) atTop atTop :=
    Real.tendsto_log_atTop.comp hG
  have hlogDiv : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  have hconst : Tendsto (fun X => Real.log c / Real.log (G X))
      atTop (𝓝 0) := by
    have hh := (tendsto_inv_atTop_zero.comp hlogG).const_mul (Real.log c)
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using hh
  have hloglog : Tendsto (fun X =>
      Real.log (Real.log (G X)) / Real.log (G X)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hlogDiv.comp hlogG
  have hupper : Tendsto (fun X => 1 +
      (Real.log c / Real.log (G X) +
        Real.log (Real.log (G X)) / Real.log (G X))) atTop (𝓝 1) := by
    simpa only [zero_add, add_zero] using (hconst.add hloglog).const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (1 : ℝ))) hupper ?_ ?_
  · filter_upwards [eventually_rank_pos hG hκ hM,
      hG.eventually_ge_atTop 5] with X hM1 hG5
    have hg : 0 < G X := by linarith
    have hlg : 0 < Real.log (G X) := Real.log_pos (by linarith)
    have hm : (1 : ℝ) ≤ M X := by exact_mod_cast hM1
    have hfloor := Nat.lt_floor_add_one ((6 / 5 : ℝ) * (M X : ℝ) * G X)
    change (6 / 5 : ℝ) * (M X : ℝ) * G X <
      (physicalSpan G M X : ℝ) + 1 at hfloor
    have hMG : G X ≤ (M X : ℝ) * G X := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm hg.le
    have hGS : G X ≤ (physicalSpan G M X : ℝ) := by nlinarith
    apply (le_div_iff₀ hlg).2
    simpa only [one_mul] using Real.log_le_log hg hGS
  · filter_upwards [(tendsto_order.mp hM).2 (κ + 1) (by linarith),
      hG.eventually_gt_atTop 1,
      (tendsto_physicalSpan_atTop hG hκ hM).eventually_ge_atTop 1]
        with X hMr hG1 hS1
    have hg : 0 < G X := zero_lt_one.trans hG1
    have hlg : 0 < Real.log (G X) := Real.log_pos hG1
    have hMupper : (M X : ℝ) ≤ (κ + 1) * Real.log (G X) :=
      ((div_lt_iff₀ hlg).mp hMr).le
    have hfloor : (physicalSpan G M X : ℝ) ≤
        (6 / 5 : ℝ) * (M X : ℝ) * G X := Nat.floor_le (by positivity)
    have hspan : (physicalSpan G M X : ℝ) ≤ c * Real.log (G X) * G X := by
      calc
        (physicalSpan G M X : ℝ) ≤ (6 / 5 : ℝ) * (M X : ℝ) * G X := hfloor
        _ ≤ (6 / 5 : ℝ) * ((κ + 1) * Real.log (G X)) * G X :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hMupper (by norm_num)) hg.le
        _ = c * Real.log (G X) * G X := by dsimp only [c]; ring
    have hSpos : (0 : ℝ) < physicalSpan G M X :=
      Nat.cast_pos.mpr (by omega)
    have hlogbound := Real.log_le_log hSpos hspan
    rw [Real.log_mul (mul_pos hc hlg).ne' hg.ne',
      Real.log_mul hc.ne' hlg.ne'] at hlogbound
    calc
      Real.log (physicalSpan G M X : ℝ) / Real.log (G X) ≤
          (Real.log c + Real.log (Real.log (G X)) + Real.log (G X)) /
            Real.log (G X) := div_le_div_of_nonneg_right hlogbound hlg.le
      _ = 1 + (Real.log c / Real.log (G X) +
          Real.log (Real.log (G X)) / Real.log (G X)) := by
        field_simp [hlg.ne'] <;> ring

private theorem exp_neg_gamma_gt_half :
    (1 / 2 : ℝ) < Real.exp (-Real.eulerMascheroniConstant) := by
  have hgamma : Real.eulerMascheroniConstant < Real.log 2 :=
    Real.eulerMascheroniConstant_lt_two_thirds.trans
      ((by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9)
  have hh := Real.exp_lt_exp.mpr (neg_lt_neg hgamma)
  simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] using hh

/-- Calibration turns an inverse-Euler bound into the corresponding
ordinary-Euler factor bound, without a count normalization. -/
private theorem euler_mul_scale_le
    {G δ : ℝ} (hG : 0 < G) (hδ : δ < 1) (y : ℕ)
    (hcal : |roughGapScale y / G - 1| ≤ δ) :
    eulerProdNat y * G ≤ 1 / (1 - δ) := by
  have hd : 0 < 1 - δ := sub_pos.mpr hδ
  have hratio : 1 - δ ≤ roughGapScale y / G := by
    have hh := (abs_le.mp hcal).1
    linarith
  have hgap : (1 - δ) * G ≤ roughGapScale y := (le_div_iff₀ hG).mp hratio
  have hi := one_div_le_one_div_of_le (mul_pos hd hG) hgap
  have he : eulerProdNat y ≤ 1 / ((1 - δ) * G) := by
    simpa only [roughGapScale, one_div, inv_inv] using hi
  calc
    eulerProdNat y * G ≤ (1 / ((1 - δ) * G)) * G :=
      mul_le_mul_of_nonneg_right he hG.le
    _ = 1 / (1 - δ) := by field_simp [hd.ne', hG.ne']

/-- The literal paper coefficient, uniformly over all positive-weight
cutoffs, under qualitative calibration only. -/
theorem eventually_scaled_retention_lt_two
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, 0 < w X y →
      lateRetention (physicalSpan G M X) y * G X / Real.log (G X) < 2 := by
  let v : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  have hv : 0 < v := Real.exp_pos _
  have hvhalf : (1 / 2 : ℝ) < v := exp_neg_gamma_gt_half
  let δ : ℝ := (v - 1 / 2) / (2 * v)
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  have hδ1 : δ < 1 := (div_lt_one (by positivity : 0 < 2 * v)).2 (by linarith)
  have hd : 0 < 1 - δ := sub_pos.mpr hδ1
  have hidentity : (1 - δ) * v = (v + 1 / 2) / 2 := by
    dsimp only [δ]
    field_simp [hv.ne'] <;> ring
  let a : ℝ := 1 / (1 - δ)
  have ha : 0 < a := div_pos zero_lt_one hd
  have hlimit : a / v < 2 := by
    apply (div_lt_iff₀ hv).2
    change 1 / (1 - δ) < 2 * v
    apply (div_lt_iff₀ hd).2
    nlinarith
  have hS := tendsto_physicalSpan_atTop hG hκ hM
  have hEuler : Tendsto (fun X =>
      eulerProdNat (physicalSpan G M X) * Real.log (physicalSpan G M X : ℝ))
      atTop (𝓝 v) := by
    simpa only [Function.comp_def, v] using tendsto_eulerProdNat_mul_log.comp hS
  have hbound : Tendsto (fun X =>
      (a * (Real.log (physicalSpan G M X : ℝ) / Real.log (G X))) /
        (eulerProdNat (physicalSpan G M X) * Real.log (physicalSpan G M X : ℝ)))
      atTop (𝓝 (a / v)) := by
    have hh :=
      ((tendsto_log_physicalSpan_div_log hG hκ hM).const_mul a).div hEuler hv.ne'
    simp only [mul_one] at hh
    exact hh.congr' (Eventually.of_forall fun X => rfl)
  filter_upwards [hbound.eventually_lt_const hlimit,
    eventually_support_above_span hG hκ hM hcal, hcal δ hδ,
    hG.eventually_gt_atTop 1, hS.eventually_ge_atTop 2]
      with X hboundX hsupport hcalX hG1 hS2
  intro y hy
  let S := physicalSpan G M X
  have hg : 0 < G X := zero_lt_one.trans hG1
  have hlg : 0 < Real.log (G X) := Real.log_pos hG1
  have hVS : 0 < eulerProdNat S := eulerProdNat_pos S
  have hls : 0 < Real.log (S : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < S by dsimp only [S]; omega))
  have hyEuler : eulerProdNat y * G X ≤ a :=
    euler_mul_scale_le hg hδ1 y (hcalX y hy)
  have hret : lateRetention S y ≤ eulerProdNat y / eulerProdNat S :=
    crtPhysRet_le_div hS2 (hsupport y hy).le
  calc
    lateRetention S y * G X / Real.log (G X) ≤
        ((eulerProdNat y / eulerProdNat S) * G X) / Real.log (G X) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hret hg.le) hlg.le
    _ = ((eulerProdNat y * G X) / eulerProdNat S) / Real.log (G X) := by ring
    _ ≤ (a / eulerProdNat S) / Real.log (G X) :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hyEuler hVS.le) hlg.le
    _ = (a * (Real.log (S : ℝ) / Real.log (G X))) /
        (eulerProdNat S * Real.log (S : ℝ)) := by
      field_simp [hVS.ne', hlg.ne', hls.ne'] <;> ring
    _ < 2 := hboundX

/-- The resampling factor appearing literally in the paper's frame
average is eventually strictly below 24. -/
theorem eventually_insertion_prefactor_lt_twenty_four
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, 0 < w X y →
      12 * lateRetention (physicalSpan G M X) y * G X / Real.log (G X) < 24 := by
  filter_upwards [eventually_scaled_retention_lt_two hG hκ hM hcal] with X hX
  intro y hy
  have hh := mul_lt_mul_of_pos_left (hX y hy) (by norm_num : (0 : ℝ) < 12)
  exact (show 12 * lateRetention (physicalSpan G M X) y * G X / Real.log (G X) =
      12 * (lateRetention (physicalSpan G M X) y * G X / Real.log (G X)) by ring).trans_lt
    (by simpa only [show (12 : ℝ) * 2 = 24 by norm_num] using hh)

end
end PrimeGapNormality.Prime.CoreCalibratedRetentionSharp
