import PrimeGapNormality.Prime.CoreRoughMeanTail
import PrimeGapNormality.Prime.ModelCellCount

/-!
# Actual rough mean tails for every fixed auxiliary base

The original sieve slope budget is retained. The auxiliary base rho is
arbitrary and does not force a new slope at kappa=1/log rho. Only its
profile length needs a new elementary polylogarithmic bound. The same two
adjacent actual counts and the global prime-containment quadratic bound
then supply the mean tail and the full summable GapTailT bundle.
-/

namespace PrimeGapNormality.Prime.CoreRoughAnyRhoTail

open Finset Filter
open CoreRoughThreshold CoreRoughSyntheticScale CoreRoughScaleLimits
  CoreRoughSubpower CoreRoughSieveBudget CoreRoughSieveBudgetLimits
  CoreMovingRoughSequence CoreMovingRoughPolynomialGrowth
  CoreSequenceAdjacentWindowTail CoreSequenceSTMeanTail CoreRoughDyadicDensity
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000

def syntheticGap (Ψ : ℝ → ℝ) : ℕ → ℝ :=
  windowG ∘ fun X => roughSyntheticScale (zPsi Ψ X)

theorem roughGap_le_syntheticGap (Ψ : ℝ → ℝ) (X : ℕ) :
    roughGapScale (zPsi Ψ X) ≤ syntheticGap Ψ X :=
  (roughGapScale_le_log_synthetic_and_le _).1.trans (le_max_left _ _)

theorem syntheticGap_one_le (Ψ : ℝ → ℝ) (X : ℕ) : 1 ≤ syntheticGap Ψ X :=
  le_max_right _ _

theorem roughGap_one_le (z : ℕ) : 1 ≤ roughGapScale z := by
  rw [roughGapScale, ← one_div]
  apply (le_div_iff₀ (eulerProdNat_pos z)).mpr
  simpa only [one_mul] using eulerProdNat_le_one z

private theorem log_atTop : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem two_mul_atTop : Tendsto (fun X : ℕ => 2 * X) atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h => Nat.mul_le_mul_left 2 h)
    (fun n => ⟨n, Nat.le_mul_of_pos_left n (by norm_num : 0 < 2)⟩)

def gapLogConstant : ℝ := eulerProdLowerConst⁻¹ + Real.log 2 + 1

theorem gapLogConstant_pos : 0 < gapLogConstant := by
  unfold gapLogConstant
  have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hc := inv_pos.mpr eulerProdLowerConst_pos
  positivity

theorem eventually_syntheticGap_le_log {Ψ : ℝ → ℝ} {A : ℝ}
    (hSlope : HasSlopeBudget Ψ A) :
    ∀ᶠ X : ℕ in atTop, syntheticGap Ψ X ≤ gapLogConstant * Real.log (X : ℝ) := by
  filter_upwards [eventually_model_gap_le_log hSlope, log_atTop.eventually_ge_atTop 1]
    with X hG ht
  have hb := (roughGapScale_le_log_synthetic_and_le (zPsi Ψ X)).2
  have hlog2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hc := inv_pos.mpr eulerProdLowerConst_pos
  have hside := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ Real.log 2 + 1 by linarith)
  have hproduct : 0 ≤ eulerProdLowerConst⁻¹ * Real.log (X : ℝ) :=
    mul_nonneg hc.le (zero_le_one.trans ht)
  unfold syntheticGap windowG
  dsimp only [Function.comp_apply]
  apply max_le
  · unfold gapLogConstant
    rw [div_eq_mul_inv] at hG
    nlinarith
  · unfold gapLogConstant
    nlinarith

theorem eventually_syntheticGap_le_log_sq {Ψ : ℝ → ℝ} {A : ℝ}
    (hSlope : HasSlopeBudget Ψ A) :
    ∀ᶠ X : ℕ in atTop, syntheticGap Ψ X ≤ Real.log (X : ℝ) ^ 2 := by
  filter_upwards [eventually_syntheticGap_le_log hSlope,
    log_atTop.eventually_ge_atTop (max 1 gapLogConstant)] with X hG ht
  have ht0 : 0 ≤ Real.log (X : ℝ) := (by norm_num : (0 : ℝ) ≤ 1).trans ((le_max_left _ _).trans ht)
  have hK : gapLogConstant ≤ Real.log (X : ℝ) := (le_max_right _ _).trans ht
  exact hG.trans (by nlinarith [mul_le_mul_of_nonneg_right hK ht0])

theorem stdProfileL_le_linear {rho G : ℝ} (hrho : 1 < rho) (hG : 1 ≤ G) :
    (stdProfileL rho G : ℝ) ≤ 2 * G / Real.log rho + 2 := by
  have hlr := Real.log_pos hrho
  have hlg := Real.log_nonneg hG
  let x := Real.log G / Real.log rho
  have hx : 0 ≤ x := div_nonneg hlg hlr.le
  have hs : Real.sqrt x ≤ x + 1 := by
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]
  have hceil := (Nat.ceil_lt_add_one (add_nonneg hx (Real.sqrt_nonneg x))).le
  have hlog : Real.log G ≤ G :=
    (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hG)).trans (by linarith)
  have hdiv := div_le_div_of_nonneg_right hlog hlr.le
  change (⌈x + Real.sqrt x⌉₊ : ℝ) ≤ _
  calc
    (⌈x + Real.sqrt x⌉₊ : ℝ) ≤ 2 * x + 2 := by linarith only [hceil, hs]
    _ ≤ 2 * (G / Real.log rho) + 2 :=
      _root_.add_le_add
        (mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ = 2 * G / Real.log rho + 2 := by ring

/-- The auxiliary base is fixed independently of the original sieve slope.
This bound replaces the special rho=localTailBase kappa identification. -/
theorem eventually_stdProfileL_le_log_five_of_scale {G : ℕ → ℝ} {rho : ℝ}
    (hrho : 1 < rho)
    (hscale : ∀ᶠ X : ℕ in atTop, 1 ≤ G X ∧ G X ≤ gapLogConstant * Real.log (X : ℝ)) :
    ∀ᶠ X : ℕ in atTop,
      (stdProfileL rho (G X) : ℝ) ≤ Real.log (X : ℝ) ^ 5 := by
  let K := 2 * gapLogConstant / Real.log rho
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact div_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) gapLogConstant_pos.le)
      (Real.log_pos hrho).le
  filter_upwards [hscale,
    log_atTop.eventually_ge_atTop (max 2 (K + 2))] with X hGX ht
  obtain ⟨hGone, hG⟩ := hGX
  have ht2 : 2 ≤ Real.log (X : ℝ) := (le_max_left _ _).trans ht
  have htK : K + 2 ≤ Real.log (X : ℝ) := (le_max_right _ _).trans ht
  have hp := stdProfileL_le_linear hrho hGone
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 2)) (Real.log_pos hrho).le
  have hlinear : (stdProfileL rho (G X) : ℝ) ≤
      K * Real.log (X : ℝ) + 2 := by
    calc
      _ ≤ 2 * G X / Real.log rho + 2 := hp
      _ ≤ (2 * (gapLogConstant * Real.log (X : ℝ))) / Real.log rho + 2 :=
        _root_.add_le_add hm le_rfl
      _ = _ := by dsimp only [K]; ring
  have hsq : K * Real.log (X : ℝ) + 2 ≤ Real.log (X : ℝ) ^ 2 := by nlinarith
  exact hlinear.trans (hsq.trans (pow_le_pow_right₀ (by linarith) (by norm_num : 2 ≤ 5)))

theorem eventually_stdProfileL_le_log_five {Ψ : ℝ → ℝ} {A rho : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hrho : 1 < rho) :
    ∀ᶠ X : ℕ in atTop,
      (stdProfileL rho (syntheticGap Ψ X) : ℝ) ≤ Real.log (X : ℝ) ^ 5 :=
  eventually_stdProfileL_le_log_five_of_scale hrho
    ((eventually_syntheticGap_le_log hSlope).mono fun X hX => ⟨syntheticGap_one_le Ψ X, hX⟩)

/-- The actual first-gap mean tail, at every fixed rho>1, under the
original slope budget A. No new slope involving rho is assumed. -/
theorem movingRough_meanGapTailT_of_scale
    {Ψ dΨ : ℝ → ℝ} {A Creg rho : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hCreg : 0 ≤ Creg)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ Creg)
    (hrho : 1 < rho) (G : ℕ → ℝ)
    (hscale : ∀ᶠ X : ℕ in atTop, roughGapScale (zPsi Ψ X) ≤ G X ∧
      1 ≤ G X ∧ G X ≤ gapLogConstant * Real.log (X : ℝ)) :
    MeanGapTailT (movingRoughSequence (zPsi Ψ)) rho G := by
  let a := movingRoughSequence (zPsi Ψ)
  have hz := hSlope.eventually_zPsi_lt
  have ha : StrictMono a := movingRoughSequence_strictMono hz
  obtain ⟨Cnat, hquadNat⟩ := exists_global_quadratic_bound hz
  let C : ℝ := Cnat
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hquad : ∀ n : ℕ, (a n : ℝ) ≤ C * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n
    dsimp only [a, C]
    exact_mod_cast hquadNat n
  apply meanGapTailT_of_adjacentWindow ha hrho hC hquad (H := cubeRootLevel)
  refine ⟨2, 1, by norm_num, by norm_num, ?_⟩
  have hc := eventually_rawPhysicalRoots_main_comparable hSlope hCreg hreg
  have hroom := CoreRoughMeanTail.tendsto_adjacentRoomEnvelope_zero.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)
  have hdeep : Tendsto (fun X : ℕ => rho⁻¹ ^ cubeRootLevel X *
      (C * posMassGeomCoeff rho * ((4 * X + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
    have hh := (CoreRoughMeanTail.tendsto_cubeRoot_quadratic_geometric_zero hrho).const_mul
      (C * posMassGeomCoeff rho)
    simp only [mul_zero] at hh
    exact hh.congr' (Eventually.of_forall fun X => by
      dsimp only [Function.comp_apply]
      ring)
  filter_upwards [hc, two_mul_atTop.eventually hc,
    eventually_stdProfileL_le_log_five_of_scale hrho (hscale.mono fun X hX => hX.2),
    two_mul_atTop.eventually (eventually_syntheticGap_le_log_sq hSlope),
    hroom, hdeep.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 2, hscale] with X hcX hc2X hL hG2 hroomX hdeepX hX hscaleX
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hV := eulerProdNat_pos (zPsi Ψ X)
  have hV2 := eulerProdNat_pos (zPsi Ψ (2 * X))
  rw [rawPhysicalRoots_card_eq_seqWindow hz X] at hcX
  rw [rawPhysicalRoots_card_eq_seqWindow hz (2 * X)] at hc2X
  have hNpos : (0 : ℝ) < (seqWindow a X).card :=
    (div_pos_iff_of_pos_right (mul_pos hXp hV)).mp
      ((by norm_num : (0 : ℝ) < 1 / 2).trans_le hcX.1)
  have hN : 0 < (seqWindow a X).card := Nat.cast_pos.mp hNpos
  have hmain : (X : ℝ) * eulerProdNat (zPsi Ψ X) ≤
      2 * ((seqWindow a X).card : ℝ) := by
    have hh := (le_div_iff₀ (mul_pos hXp hV)).mp hcX.1
    change (1 / 2 : ℝ) * ((X : ℝ) * eulerProdNat (zPsi Ψ X)) ≤ _ at hh
    linarith
  have hnorm : (X : ℝ) / ((seqWindow a X).card : ℝ) ≤ 2 * G X := by
    have hrough : (X : ℝ) / ((seqWindow a X).card : ℝ) ≤ 2 * roughGapScale (zPsi Ψ X) := by
      apply (div_le_iff₀ hNpos).mpr
      have hm := mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hV.le)
      unfold roughGapScale
      have heq : (eulerProdNat (zPsi Ψ X))⁻¹ *
          ((X : ℝ) * eulerProdNat (zPsi Ψ X)) = X := by
        field_simp [hV.ne'] <;> ring
      rw [heq] at hm
      nlinarith
    exact hrough.trans (mul_le_mul_of_nonneg_left hscaleX.1 (by norm_num))
  have hnextMain : (X : ℝ) ≤ roughGapScale (zPsi Ψ (2 * X)) *
      ((seqWindow a (2 * X)).card : ℝ) := by
    have hh := (le_div_iff₀ (show (0 : ℝ) < ((2 * X : ℕ) : ℝ) *
      eulerProdNat (zPsi Ψ (2 * X)) by positivity)).mp hc2X.1
    have hm : (X : ℝ) * eulerProdNat (zPsi Ψ (2 * X)) ≤
        ((seqWindow a (2 * X)).card : ℝ) := by push_cast at hh; nlinarith
    have hs := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hV2.le)
    have heq : (eulerProdNat (zPsi Ψ (2 * X)))⁻¹ *
        ((X : ℝ) * eulerProdNat (zPsi Ψ (2 * X))) = X := by
      field_simp [hV2.ne'] <;> ring
    rw [heq] at hs
    exact hs
  have hroomLt : (Real.log (X : ℝ) ^ 5 + (X : ℝ) ^ (1 / 3 : ℝ)) *
      Real.log ((2 * X : ℕ) : ℝ) ^ 2 < (X : ℝ) :=
    (div_lt_one hXp).mp hroomX
  have hH : (cubeRootLevel X : ℝ) ≤ (X : ℝ) ^ (1 / 3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hXp.le _)
  have hLH : ((stdProfileL rho (G X) + cubeRootLevel X : ℕ) : ℝ) ≤
      Real.log (X : ℝ) ^ 5 + (X : ℝ) ^ (1 / 3 : ℝ) := by
    push_cast
    exact _root_.add_le_add hL hH
  have hg2 : roughGapScale (zPsi Ψ (2 * X)) ≤ Real.log ((2 * X : ℕ) : ℝ) ^ 2 :=
    (roughGap_le_syntheticGap Ψ (2 * X)).trans hG2
  have hreserve := (mul_le_mul hLH hg2 (roughGapScale_pos _).le
    (_root_.add_nonneg
      (pow_nonneg (Real.log_nonneg
        (show (1 : ℝ) ≤ (X : ℝ) by exact_mod_cast (show 1 ≤ X by omega))) 5)
      (Real.rpow_nonneg hXp.le (1 / 3 : ℝ)))).trans_lt hroomLt
  have hnextReal : ((stdProfileL rho (G X) + cubeRootLevel X : ℕ) : ℝ) <
      ((seqWindow a (2 * X)).card : ℝ) := by
    have hs := hreserve.trans_le hnextMain
    apply (mul_lt_mul_iff_left₀ (roughGapScale_pos (zPsi Ψ (2 * X)))).mp
    simpa only [mul_comm] using hs
  exact ⟨hN, hnorm, (by exact_mod_cast hnextReal),
    (by simpa only [one_mul] using hdeepX.le.trans hscaleX.2.1)⟩

theorem movingRough_meanGapTailT_any_rho
    {Ψ dΨ : ℝ → ℝ} {A Creg rho : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hCreg : 0 ≤ Creg)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ Creg)
    (hrho : 1 < rho) :
    MeanGapTailT (movingRoughSequence (zPsi Ψ)) rho (syntheticGap Ψ) :=
  movingRough_meanGapTailT_of_scale hSlope hCreg hreg hrho (syntheticGap Ψ)
    ((eventually_syntheticGap_le_log hSlope).mono fun X hX =>
      ⟨roughGap_le_syntheticGap Ψ X, syntheticGap_one_le Ψ X, hX⟩)

/-- Paper's actual Euler scale and its own exact standard profile, for
every fixed rho>1. No comparison of shifted gap tails is used. -/
theorem movingRough_meanGapTailT_roughScale
    {Ψ dΨ : ℝ → ℝ} {A Creg rho : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hCreg : 0 ≤ Creg)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ Creg)
    (hrho : 1 < rho) :
    MeanGapTailT (movingRoughSequence (zPsi Ψ)) rho
      (fun X => roughGapScale (zPsi Ψ X)) :=
  movingRough_meanGapTailT_of_scale hSlope hCreg hreg hrho _
    ((eventually_syntheticGap_le_log hSlope).mono fun X hX =>
      ⟨le_rfl, roughGap_one_le _, (roughGap_le_syntheticGap Ψ X).trans hX⟩)

private theorem gapTailT_of_actual_mean
    {Ψ : ℝ → ℝ} {A rho : ℝ} (hSlope : HasSlopeBudget Ψ A) (hrho : 1 < rho)
    {G : ℕ → ℝ} (hscale : Tendsto G atTop atTop)
    (hMean : MeanGapTailT (movingRoughSequence (zPsi Ψ)) rho G) :
    GapTailT (movingRoughSequence (zPsi Ψ)) rho G := by
  obtain ⟨C, hC⟩ := exists_global_quadratic_bound hSlope.eventually_zPsi_lt
  have hsum := sequence_div_pow_summable_of_quadratic
    (a := movingRoughSequence (zPsi Ψ)) (C := (C : ℝ)) (Nat.cast_nonneg _)
    (fun n => by exact_mod_cast hC n) hrho
  obtain ⟨K, hK, hmean⟩ := hMean
  exact ⟨hrho, hscale, hsum, K, hK, hmean⟩

/-- Legacy summable TailT, with summability proved directly from prime
containment, independently of ShapeS. -/
theorem movingRough_gapTailT_any_rho
    {Ψ dΨ : ℝ → ℝ} {A Creg rho : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hCreg : 0 ≤ Creg)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ Creg)
    (hrho : 1 < rho) :
    GapTailT (movingRoughSequence (zPsi Ψ)) rho
      (windowG ∘ fun X => roughSyntheticScale (zPsi Ψ X)) := by
  have hscale : Tendsto (syntheticGap Ψ) atTop atTop := by
    change Tendsto (fun X : ℕ => windowG (roughSyntheticScale (zPsi Ψ X))) atTop atTop
    simpa only [Function.comp_def] using tendsto_windowG_atTop.comp
      (tendsto_roughSyntheticScale_atTop.comp hSlope.tendsto_zPsi_atTop)
  exact gapTailT_of_actual_mean hSlope hrho hscale
    (movingRough_meanGapTailT_any_rho hSlope hCreg hreg hrho)

/-- Complete TailT at the paper's actual scale V(z(X))⁻¹, with its exact
rho-dependent truncation depth and independently proved summability. -/
theorem movingRough_gapTailT_roughScale
    {Ψ dΨ : ℝ → ℝ} {A Creg rho : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hCreg : 0 ≤ Creg)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ Creg)
    (hrho : 1 < rho) :
    GapTailT (movingRoughSequence (zPsi Ψ)) rho
      (fun X => roughGapScale (zPsi Ψ X)) :=
  gapTailT_of_actual_mean hSlope hrho
    (tendsto_roughGapScale_atTop.comp hSlope.tendsto_zPsi_atTop)
    (movingRough_meanGapTailT_roughScale hSlope hCreg hreg hrho)

end
end PrimeGapNormality.Prime.CoreRoughAnyRhoTail
