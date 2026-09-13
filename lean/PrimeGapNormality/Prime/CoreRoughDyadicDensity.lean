import PrimeGapNormality.Prime.CoreRoughCellAsymptotics
import PrimeGapNormality.Prime.CoreRoughGlobalCutoff
import PrimeGapNormality.Prime.CoreRoughRootCount
import PrimeGapNormality.Prime.CoreRoughSieveBudgetLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic density of the literal moving-rough roots

The one-point finite sieve is applied once on `(X,2X]`.  Variation of the
literal cutoff is charged by the global reciprocal-prime loss, while the
fixed beta level and the cube-root additive error are discharged from the
slope budget.  There is no density, shape, or Euler-continuity premise.
-/

namespace PrimeGapNormality.Prime.CoreRoughDyadicDensity

open Filter Set Finset
open scoped Topology

open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSubpower
  CoreRoughCellAsymptotics CoreRoughGlobalCutoff CoreRoughRootCount
  CoreRoughSieveBudget CoreRoughSieveBudgetLimits CoreRoughSyntheticScale CoreRoughProfileError

noncomputable section

set_option maxHeartbeats 1200000

/-- Whole-dyadic reciprocal hazard supplied by the global cutoff bound. -/
def dyadicRootHazard (C : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  globalCutoffConstant C / Real.log (X : ℝ) +
    globalCutoffConstant C / Real.sqrt (zPsi Ψ X : ℝ)

/-- Upper cutoff in the form used by the beta-sieve logarithmic level. -/
def dyadicUpperCutoff (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  (zPsi Ψ (2 * X) : ℝ) + 1 / 2

/-- Additive one-point CRT error after division by the main term. -/
def dyadicRootAdditiveError (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  Real.exp 10 * (cubeRootLevel X : ℝ) /
    ((X : ℝ) * eulerProdNat (zPsi Ψ X))

theorem tendsto_dyadicRootHazard_zero
    {Ψ : ℝ → ℝ} {A C : ℝ} (hSlope : HasSlopeBudget Ψ A) :
    Tendsto (dyadicRootHazard C Ψ) atTop (nhds 0) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfirst : Tendsto (fun X : ℕ ↦
      globalCutoffConstant C / Real.log (X : ℝ)) atTop (nhds 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hlog
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      hinv.const_mul (globalCutoffConstant C)
  have hzReal : Tendsto (fun X : ℕ ↦ (zPsi Ψ X : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hSlope.tendsto_zPsi_atTop
  have hsqrt : Tendsto (fun X : ℕ ↦ Real.sqrt (zPsi Ψ X : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hzReal
  have hsecond : Tendsto (fun X : ℕ ↦
      globalCutoffConstant C / Real.sqrt (zPsi Ψ X : ℝ)) atTop (nhds 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hsqrt
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      hinv.const_mul (globalCutoffConstant C)
  have hsum := hfirst.add hsecond
  simp only [add_zero] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun X ↦ rfl

/-- The eventual derivative condition makes the literal cutoff monotone on
the whole coarse physical range. -/
theorem eventually_zPsi_mono_on_triple
    {Ψ dΨ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    ∀ᶠ X : ℕ in atTop, ∀ a ∈ Set.Icc X (3 * X), ∀ b ∈ Set.Icc X (3 * X),
      a ≤ b → zPsi Ψ a ≤ zPsi Ψ b := by
  rcases eventually_atTop.1 hreg with ⟨t₀, ht₀⟩
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlog.eventually_ge_atTop t₀, eventually_ge_atTop 3]
      with X hlogt₀ hX3
  intro a ha b hb hab
  have hXpos : (0 : ℝ) < X :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 3) hX3)
  have haOne : (1 : ℝ) < a := by
    exact_mod_cast (lt_of_lt_of_le
      (lt_of_lt_of_le (by norm_num : 1 < 3) hX3) ha.1)
  have haPos : (0 : ℝ) < a := zero_lt_one.trans haOne
  have habR : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  have hlogab : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log haPos habR
  have hlogXa : Real.log (X : ℝ) ≤ Real.log (a : ℝ) :=
    Real.log_le_log hXpos (Nat.cast_le.mpr ha.1)
  have hdata : ∀ t ∈ Set.Icc (Real.log (a : ℝ)) (Real.log (b : ℝ)),
      0 < Ψ t ∧ HasDerivAt Ψ (dΨ t) t ∧
        0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t := by
    intro t ht
    exact ht₀ t (hlogt₀.trans (hlogXa.trans ht.1))
  have hcmp := CoreRoughThresholdRegularity.psi_interval_comparison
    (u := Real.log (a : ℝ)) (v := Real.log (b : ℝ)) (C := C)
    (Real.log_pos haOne) hlogab hC
    (fun t ht ↦ (hdata t ht).1)
    (fun t ht ↦ (hdata t ht).2.1)
    (fun t ht ↦ (hdata t ht).2.2)
  unfold zPsi
  exact Nat.floor_le_floor (Real.exp_le_exp.mpr hcmp.1)

private theorem eventually_dyadicUpperCutoff_bounds
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    ∀ᶠ X : ℕ in atTop,
      1 < dyadicUpperCutoff Ψ X ∧
        dyadicUpperCutoff Ψ X ≤
          Real.exp (2 * Ψ (Real.log (X : ℝ))) + 1 := by
  have hdouble := eventually_psi_log_cellStart_le_two hSlope hC hreg
  have hz16 := hSlope.tendsto_zPsi_atTop.eventually_ge_atTop 16
  have hmono := eventually_zPsi_mono_on_triple hC hreg
  filter_upwards [hdouble, hz16, hmono, eventually_ge_atTop 1]
      with X hdoubleX hzX hmonoX hX
  have htwoMem : 2 * X ∈ Set.Icc X (2 * X) := by constructor <;> omega
  have htwoMem3 : 2 * X ∈ Set.Icc X (3 * X) := by constructor <;> omega
  have hXMem3 : X ∈ Set.Icc X (3 * X) := by constructor <;> omega
  have hcutMono : zPsi Ψ X ≤ zPsi Ψ (2 * X) :=
    hmonoX X hXMem3 (2 * X) htwoMem3 (by omega)
  have hΨtwo := hdoubleX (2 * X) htwoMem
  have hfloor : (zPsi Ψ (2 * X) : ℝ) ≤
      Real.exp (Ψ (Real.log ((2 * X : ℕ) : ℝ))) :=
    Nat.floor_le (Real.exp_pos _).le
  have hexp : Real.exp (Ψ (Real.log ((2 * X : ℕ) : ℝ))) ≤
      Real.exp (2 * Ψ (Real.log (X : ℝ))) :=
    Real.exp_le_exp.mpr hΨtwo
  constructor
  · unfold dyadicUpperCutoff
    have hzTwo : 16 ≤ zPsi Ψ (2 * X) := hzX.trans hcutMono
    have hzTwoR : (16 : ℝ) ≤ zPsi Ψ (2 * X) := Nat.cast_le.mpr hzTwo
    linarith
  · unfold dyadicUpperCutoff
    linarith

private theorem tendsto_fixedBetaError_zero
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun X : ℕ ↦ Real.exp
      (299 - Real.log (cubeRootLevel X : ℝ) /
        Real.log (dyadicUpperCutoff Ψ X))) atTop (nhds 0) := by
  let κ₀ := A / 1000000
  have hκ₀ : 0 < κ₀ := by
    dsimp only [κ₀]
    exact div_pos hSlope.1 (by norm_num)
  have hscale : (1000000 : ℝ) * κ₀ = A := by
    dsimp only [κ₀]
    field_simp
  have hSlope' : HasSlopeBudget Ψ (1000000 * κ₀) := by
    rw [hscale]
    exact hSlope
  have hZ := eventually_dyadicUpperCutoff_bounds hSlope hC hreg
  have hmajor := tendsto_relativeCost_zero hκ₀ hSlope'
    (dyadicUpperCutoff Ψ) hZ
  refine squeeze_zero' (Eventually.of_forall fun X ↦ (Real.exp_pos _).le) ?_ hmajor
  exact Eventually.of_forall fun X ↦ by
    apply Real.exp_le_exp.mpr
    have hr : (1 : ℝ) ≤ ((profileRank κ₀ Ψ X + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos (profileRank κ₀ Ψ X)
    have hL : 0 ≤ (roughProfileL κ₀ (zPsi Ψ X) : ℝ) := Nat.cast_nonneg _
    nlinarith

private theorem eventually_fixedRootLevel
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    ∀ᶠ X : ℕ in atTop,
      (dyadicUpperCutoff Ψ X) ^ (10 : ℕ) ≤ cubeRootLevel X := by
  let κ₀ := A / 1000000
  have hκ₀ : 0 < κ₀ := by
    dsimp only [κ₀]
    exact div_pos hSlope.1 (by norm_num)
  have hscale : (1000000 : ℝ) * κ₀ = A := by
    dsimp only [κ₀]
    field_simp
  have hSlope' : HasSlopeBudget Ψ (1000000 * κ₀) := by
    rw [hscale]
    exact hSlope
  have hZ := eventually_dyadicUpperCutoff_bounds hSlope hC hreg
  have hall := eventually_all_tuple_levels hκ₀ hSlope'
    (dyadicUpperCutoff Ψ) hZ
  filter_upwards [hall] with X hX
  have hone : 1 ≤ profileRank κ₀ Ψ X + 1 := Nat.succ_pos _
  have hh := hX 1 hone
  simpa only [Nat.cast_one, mul_one] using hh

private theorem tendsto_log_div_twoThird_rpow_zero :
    Tendsto (fun X : ℕ ↦ Real.log (X : ℝ) /
      (X : ℝ) ^ (2 / 3 : ℝ)) atTop (nhds 0) := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hnat.congr'
  exact Eventually.of_forall fun X => by
    simp only [Function.comp_apply, Real.rpow_one]

theorem tendsto_dyadicRootAdditiveError_zero
    {Ψ : ℝ → ℝ} {A : ℝ} (hSlope : HasSlopeBudget Ψ A) :
    Tendsto (dyadicRootAdditiveError Ψ) atTop (nhds 0) := by
  let c := eulerProdLowerConst
  have hc : 0 < c := by dsimp only [c]; exact eulerProdLowerConst_pos
  have hmajor : Tendsto (fun X : ℕ ↦
      (Real.exp 10 / c) *
        (Real.log (X : ℝ) / (X : ℝ) ^ (2 / 3 : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_log_div_twoThird_rpow_zero.const_mul (Real.exp 10 / c)
  refine squeeze_zero' ?_ ?_ hmajor
  · exact Eventually.of_forall fun X ↦ by
      unfold dyadicRootAdditiveError
      exact div_nonneg
        (mul_nonneg (Real.exp_pos 10).le (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (eulerProdNat_pos _).le)
  · filter_upwards [eventually_model_gap_le_log hSlope,
      eventually_ge_atTop 3] with X hG hX3
    have hXpos : (0 : ℝ) < X :=
      Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 3) hX3)
    have hfloor : (cubeRootLevel X : ℝ) ≤ (X : ℝ) ^ (1 / 3 : ℝ) := by
      unfold cubeRootLevel
      exact Nat.floor_le (Real.rpow_nonneg hXpos.le _)
    have hG0 : 0 ≤ roughGapScale (zPsi Ψ X) :=
      (roughGapScale_pos _).le
    have hlog0 : 0 ≤ Real.log (X : ℝ) :=
      (Real.log_pos (Nat.one_lt_cast.mpr
        (lt_of_lt_of_le (by norm_num : 1 < 3) hX3))).le
    have hprod := mul_le_mul hfloor hG hG0
      (Real.rpow_nonneg hXpos.le _)
    have hXsplit : (X : ℝ) ^ (1 / 3 : ℝ) *
        (X : ℝ) ^ (2 / 3 : ℝ) = (X : ℝ) := by
      rw [← Real.rpow_add hXpos]
      norm_num
    have hmain : (cubeRootLevel X : ℝ) * roughGapScale (zPsi Ψ X) /
        (X : ℝ) ≤
      (1 / c) * (Real.log (X : ℝ) / (X : ℝ) ^ (2 / 3 : ℝ)) := by
      have hdiv := div_le_div_of_nonneg_right hprod hXpos.le
      refine hdiv.trans_eq ?_
      dsimp only [c]
      field_simp [hXpos.ne', eulerProdLowerConst_pos.ne',
        (Real.rpow_pos_of_pos hXpos (2 / 3 : ℝ)).ne']
      nlinarith [congrArg (fun t : ℝ => Real.log (X : ℝ) * t) hXsplit]
    have hscaled := mul_le_mul_of_nonneg_left hmain (Real.exp_pos 10).le
    have heq : dyadicRootAdditiveError Ψ X =
        Real.exp 10 *
          ((cubeRootLevel X : ℝ) * roughGapScale (zPsi Ψ X) / (X : ℝ)) := by
      unfold dyadicRootAdditiveError roughGapScale
      have hV := (eulerProdNat_pos (zPsi Ψ X)).ne'
      field_simp [hXpos.ne', hV] <;> ring
    rw [heq]
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hscaled

/-- Actual normalized dyadic root count tends to one. -/
theorem tendsto_rawPhysicalRoots_div_main_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun X : ℕ ↦
      ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) /
        ((X : ℝ) * eulerProdNat (zPsi Ψ X))) atTop (nhds 1) := by
  have hglobalReg : CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative Ψ dΨ C := by
    simpa only [CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative,
      CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative] using hreg
  have hglobal := eventually_global_cutoff_and_primeLoss hSlope hC hglobalReg
  have hmono := eventually_zPsi_mono_on_triple hC hreg
  have hlevel := eventually_fixedRootLevel hSlope hC hreg
  have hhazard := tendsto_dyadicRootHazard_zero (C := C) hSlope
  have hbeta := tendsto_fixedBetaError_zero hSlope hC hreg
  have hadd := tendsto_dyadicRootAdditiveError_zero hSlope
  have hmajor : Tendsto (fun X : ℕ ↦
      dyadicRootHazard C Ψ X +
        Real.exp (299 - Real.log (cubeRootLevel X : ℝ) /
          Real.log (dyadicUpperCutoff Ψ X)) +
        dyadicRootAdditiveError Ψ X) atTop (nhds 0) := by
    have hh := (hhazard.add hbeta).add hadd
    simp only [add_zero] at hh
    exact hh
  have hhazardHalf : ∀ᶠ X : ℕ in atTop,
      dyadicRootHazard C Ψ X ≤ 1 / 2 := by
    filter_upwards [hhazard.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))]
        with X hball
    have hdist : dist (dyadicRootHazard C Ψ X) 0 < 1 / 2 :=
      Metric.mem_ball.mp hball
    rw [Real.dist_eq, sub_zero] at hdist
    exact (le_abs_self _).trans hdist.le
  have habs : Tendsto (fun X : ℕ ↦
      |((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) /
        ((X : ℝ) * eulerProdNat (zPsi Ψ X)) - 1|) atTop (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun X ↦ abs_nonneg _) ?_ hmajor
    filter_upwards [hglobal, hmono, hlevel, hhazardHalf,
      hSlope.tendsto_zPsi_atTop.eventually_ge_atTop 16,
      eventually_ge_atTop 1] with X hglob hmonoX hlevelX hδhalf hy16 hX
    have hXMem : X ∈ Set.Icc X (3 * X) := by constructor <;> omega
    have htwoMem : 2 * X ∈ Set.Icc X (3 * X) := by constructor <;> omega
    have hlyu : zPsi Ψ X ≤ zPsi Ψ (2 * X) :=
      hmonoX X hXMem (2 * X) htwoMem (by omega)
    have hcut : ∀ n ∈ Finset.Ioc X (2 * X),
        zPsi Ψ X ≤ zPsi Ψ n ∧ zPsi Ψ n ≤ zPsi Ψ (2 * X) := by
      intro n hn
      have hn3 : n ∈ Set.Icc X (3 * X) := by
        exact ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2.trans (by omega)⟩
      exact ⟨hmonoX X hXMem n hn3 (Finset.mem_Ioc.mp hn).1.le,
        hmonoX n hn3 (2 * X) htwoMem (Finset.mem_Ioc.mp hn).2⟩
    have hglobTwo := hglob (2 * X) htwoMem
    have hband : ∑ p ∈ Nat.primesLE (zPsi Ψ (2 * X)) \
        Nat.primesLE (zPsi Ψ X), (p : ℝ)⁻¹ ≤ dyadicRootHazard C Ψ X := by
      simpa only [cutoffPrimeReciprocalLoss, dyadicRootHazard] using hglobTwo.2.2
    have hfinite := rawPhysicalRoots_relative_error (zPsi Ψ)
      (hX := (by omega : 0 < X)) hy16 hlyu hcut hδhalf hband hlevelX
    simpa only [dyadicUpperCutoff, dyadicRootAdditiveError] using hfinite
  have hsub := (tendsto_const_nhds (x := (1 : ℝ))).add
    (show Tendsto (fun X : ℕ ↦
      ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) /
        ((X : ℝ) * eulerProdNat (zPsi Ψ X)) - 1) atTop (nhds 0) from
      (tendsto_zero_iff_norm_tendsto_zero.mpr (by
        simpa only [Real.norm_eq_abs] using habs)))
  simp only [add_zero] at hsub
  apply hsub.congr'
  exact Eventually.of_forall fun X ↦ by ring

/-- Eventual two-sided comparability of the actual dyadic root count. -/
theorem eventually_rawPhysicalRoots_main_comparable
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    ∀ᶠ X : ℕ in atTop,
      (1 / 2 : ℝ) ≤
          ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) /
            ((X : ℝ) * eulerProdNat (zPsi Ψ X)) ∧
        ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) /
            ((X : ℝ) * eulerProdNat (zPsi Ψ X)) ≤ 2 := by
  have hlim := tendsto_rawPhysicalRoots_div_main_one hSlope hC hreg
  filter_upwards [hlim.eventually
    (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))]
      with X hball
  have hdist : dist
      (((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) /
        ((X : ℝ) * eulerProdNat (zPsi Ψ X))) 1 < 1 / 2 :=
    Metric.mem_ball.mp hball
  rw [Real.dist_eq] at hdist
  constructor <;> linarith [le_abs_self
    (((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) /
      ((X : ℝ) * eulerProdNat (zPsi Ψ X)) - 1),
    neg_le_abs (((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) /
      ((X : ℝ) * eulerProdNat (zPsi Ψ X)) - 1)]

end

end PrimeGapNormality.Prime.CoreRoughDyadicDensity
