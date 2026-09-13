import PrimeGapNormality.Prime.PresieveSmallGlobalConcentration
import PrimeGapNormality.Prime.FiniteRootMixSmallCosts

/-!
# Vanishing lower-count exception and failure mass of the small root mix

The global presieve lower tail is uniform before the final cutoff is
chosen.  Elementary cutoff calibration puts the late conditional mean
above `28 L/25` on the full presieve main term.  Thus a fibre with late
mean below `11 L/10` lies in the global one-percent lower tail.  Averaging
with the actual normalized root-mix weights preserves this bound.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-- A coarse but sufficient calibration of the full presieve main
term to the final expected count, uniformly in the actual mix scales. -/
theorem eventually_presieve_main_mul_lateRetention_ge
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X,
      (28 / 25 : ℝ) * (profileL κ X : ℝ) ≤
        ((ahlSmall_window κ X : ℝ) * eulerProdNat (ahlSmall_window κ X)) *
          lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) := by
  filter_upwards [eventually_one_le_profileL hκ,
    (tendsto_ahlSmall_window_atTop hκ).eventually_ge_atTop 4000,
    eventually_profileS_le_sieveCutoff hκ,
    crtNestVR_eventually_exp_sixteen,
    tendsto_windowG_atTop.eventually_ge_atTop (max 1000 (999 * Real.log 2)),
    eventually_ge_atTop 3] with X hL hS hprofile hXexp hGlarge hX3
  intro t ht
  let S := ahlSmall_window κ X
  let L := profileL κ X
  let G := windowG X
  let y := sieveCutoff (t : ℝ)
  have htI : t ∈ Ioc X (2 * X) := by simpa only [mixScale] using ht
  have hXt : (X : ℝ) < t := Nat.cast_lt.mpr (mem_Ioc.mp htI).1
  have htUpper : (t : ℝ) ≤ 2 * (X : ℝ) := by
    exact_mod_cast (mem_Ioc.mp htI).2
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hX1 : (1 : ℝ) < X := Nat.one_lt_cast.mpr (by omega)
  have htpos : (0 : ℝ) < t := hXpos.trans hXt
  have ht1 : (1 : ℝ) < t := hX1.trans hXt
  have htexp : Real.exp 16 ≤ (t : ℝ) := hXexp.trans hXt.le
  have hlogX : (16 : ℝ) ≤ Real.log (X : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos 16) hXexp
  have hGlog : G = Real.log (X : ℝ) := by
    dsimp only [G, windowG]
    exact max_eq_left (by linarith)
  have hG1000 : (1000 : ℝ) ≤ G := (le_max_left _ _).trans hGlarge
  have hGlog2 : 999 * Real.log 2 ≤ G := (le_max_right _ _).trans hGlarge
  have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hG1000
  have hLR : (1 : ℝ) ≤ L := Nat.one_le_cast.mpr hL
  have hLG : (1000 : ℝ) ≤ (L : ℝ) * G := by
    exact hG1000.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hLR hGpos.le)
  have hfloor : (6 / 5 : ℝ) * (L : ℝ) * G < (S : ℝ) + 1 := by
    simpa only [S, L, G, ahlSmall_window_eq] using
      Nat.lt_floor_add_one ((6 / 5 : ℝ) * (profileL κ X : ℝ) * windowG X)
  have hSlow : (1199 / 1000 : ℝ) * (L : ℝ) * G ≤ S := by nlinarith
  have hSpos : (0 : ℝ) < S := Nat.cast_pos.mpr (by omega)
  have hS2 : 2 ≤ S := by omega
  have hSy : S ≤ y :=
    (ahlSmall_window_le_profileS κ X).trans
      ((Nat.cast_le.mp hprofile).trans (crtNestVR_sieveCutoff_mono hX1 hXt))
  have hVS : 0 < eulerProdNat S := eulerProdNat_pos S
  have hVy : 0 < eulerProdNat y := eulerProdNat_pos y
  have htlog : 0 < Real.log (t : ℝ) := Real.log_pos ht1
  have hVyt : (15 / 16 : ℝ) ≤ eulerProdNat y * Real.log (t : ℝ) := by
    have h := (isSieveCutoff_eulerProd_asymp htexp (sieveCutoff_spec ht1)).1
    rw [eulerProd_coe_nat] at h
    exact ((div_lt_iff₀ htlog).mp h).le
  have hlogt : Real.log (t : ℝ) ≤ Real.log 2 + G := by
    calc
      Real.log (t : ℝ) ≤ Real.log (2 * (X : ℝ)) := Real.log_le_log htpos htUpper
      _ = Real.log 2 + G := by rw [Real.log_mul (by norm_num) hXpos.ne', hGlog]
  have hratio : (999 / 1000 : ℝ) * Real.log (t : ℝ) ≤ G := by linarith
  have hVyG : (15 / 16 : ℝ) * (999 / 1000) ≤ eulerProdNat y * G := by
    have h1 := mul_le_mul_of_nonneg_right hVyt (by norm_num : (0 : ℝ) ≤ 999 / 1000)
    have h2 := mul_le_mul_of_nonneg_left hratio hVy.le
    nlinarith
  have hsmall : (4 : ℝ) / S ≤ 1 / 1000 := by
    apply (div_le_iff₀ hSpos).mpr
    have hSR : (4000 : ℝ) ≤ S := Nat.cast_le.mpr hS
    linarith
  have hroot : (999 / 1000 : ℝ) * (eulerProdNat y / eulerProdNat S) ≤
      lateRetention S y := by
    have h := (abs_le.mp (rootedEulerProdNat_rel_div hS2 hSy)).1
    have hq : 0 ≤ eulerProdNat y / eulerProdNat S := div_nonneg hVy.le hVS.le
    have hmul := mul_le_mul_of_nonneg_right hsmall hq
    change (999 / 1000 : ℝ) * (eulerProdNat y / eulerProdNat S) ≤ rootedEulerProdNat S y
    nlinarith
  have hcal := mul_le_mul_of_nonneg_left hroot
    (mul_nonneg (Nat.cast_nonneg S) hVS.le)
  have hcaleq : ((S : ℝ) * eulerProdNat S) *
      ((999 / 1000 : ℝ) * (eulerProdNat y / eulerProdNat S)) =
      (999 / 1000 : ℝ) * (S : ℝ) * eulerProdNat y := by
    field_simp [hVS.ne'] <;> ring
  rw [hcaleq] at hcal
  have hSscale := mul_le_mul_of_nonneg_right hSlow
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 999 / 1000) hVy.le)
  have hVscale := mul_le_mul_of_nonneg_left hVyG
    (show 0 ≤ (999 / 1000 : ℝ) * (1199 / 1000) * (L : ℝ) by positivity)
  have hnumeric : (28 / 25 : ℝ) * (L : ℝ) ≤
      (999 / 1000 : ℝ) * (1199 / 1000) * (L : ℝ) * ((15 / 16) * (999 / 1000)) := by
    have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    nlinarith
  nlinarith [hcal, hSscale, hVscale, hnumeric]

/-- Every low late-mean fibre lies in the concrete global one-percent
presieve lower tail. -/
theorem eventually_finiteRootMixSmallLowerFibreMass_le_global
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X,
      finiteRootMixSmallLowerFibreMass (ahlSmall_window κ X)
        (sieveCutoff (t : ℝ)) (profileL κ X) ≤
      presieveSmallGlobalLowerMass (ahlSmall_window κ X)
        ((1 - (1 / 100 : ℝ)) * ((ahlSmall_window κ X : ℝ) *
          eulerProdNat (ahlSmall_window κ X))) := by
  filter_upwards [eventually_presieve_main_mul_lateRetention_ge hκ,
    eventually_one_le_profileL hκ,
    (tendsto_ahlSmall_window_atTop hκ).eventually_ge_atTop 2] with X hcal hL hS
  intro t ht
  let S := ahlSmall_window κ X
  let L := profileL κ X
  let y := sieveCutoff (t : ℝ)
  have hθ : 0 ≤ lateRetention S y := (rootedEulerProdNat_pos hS).le
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hsub : finiteRootMixSmallLowerFibreSet S y L ⊆
      (univ : Finset (ResidueChoice S)).filter fun σ =>
        ((presieveSurvivors S σ).card : ℝ) <
          (1 - (1 / 100 : ℝ)) * ((S : ℝ) * eulerProdNat S) := by
    intro σ hσ
    have hlow := (mem_filter.mp hσ).2
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    by_contra hnot
    have hN := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hθ
    have hmain := mul_le_mul_of_nonneg_left (hcal t ht)
      (by norm_num : (0 : ℝ) ≤ 1 - 1 / 100)
    change ((presieveSurvivors S σ).card : ℝ) * lateRetention S y <
      (11 / 10 : ℝ) * (L : ℝ) at hlow
    nlinarith
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card hsub)) (Nat.cast_nonneg _)

theorem tendsto_finiteRootMixSmallLowerException {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (finiteRootMixSmallLowerException κ) atTop (nhds 0) := by
  have hglobal := tendsto_presieveSmallGlobalLowerMass hκ
    (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (1 / 100 : ℝ) ≤ 1)
  refine squeeze_zero' (Eventually.of_forall fun X => finiteRootMixSmallLowerException_nonneg κ X)
    ?_ hglobal
  filter_upwards [eventually_finiteRootMixSmallLowerFibreMass_le_global hκ,
    eventually_ge_atTop 1] with X hbound hX
  have hZ : 0 < mixZ X := by
    unfold mixZ
    apply sum_pos'
    · intro t _
      exact mixWeightV_nonneg t
    · refine ⟨2 * X, ?_, ?_⟩
      · simp only [mixScale, mem_Ioc]
        omega
      · exact eulerProdNat_pos (sieveCutoff ((2 * X : ℕ) : ℝ))
  unfold finiteRootMixSmallLowerException
  apply (div_le_iff₀ hZ).mpr
  calc
    _ ≤ ∑ t ∈ mixScale X, mixWeightV t *
      presieveSmallGlobalLowerMass (ahlSmall_window κ X)
        ((1 - (1 / 100 : ℝ)) * ((ahlSmall_window κ X : ℝ) *
          eulerProdNat (ahlSmall_window κ X))) :=
      sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hbound t ht) (mixWeightV_nonneg t)
    _ = _ := by rw [← sum_mul]; unfold mixZ; ring

/-- Failure mass of the concrete small finite-root mixture vanishes,
with no lower-count or calibration hypothesis remaining. -/
theorem tendsto_finiteRootMix_small_failureMass {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      Stopped.failureMass (ahlSmall_omega κ X)
        (finiteRootMix X (ahlSmall_window κ X)) (profileL κ X)) atTop (nhds 0) := by
  have hlim := (tendsto_five_hundred_div_profileL hκ).add
    (tendsto_finiteRootMixSmallLowerException hκ)
  simp only [add_zero] at hlim
  refine squeeze_zero' ?_ (finiteRootMix_small_failureMass_le_lowerException hκ) hlim
  exact Eventually.of_forall fun X =>
    finiteRootMix_failureMass_nonneg X (ahlSmall_window κ X) (profileL κ X)

end

end PrimeGapNormality.Prime
