import PrimeGapNormality.Prime.CoreSequenceAdjacentWindowTail
import PrimeGapNormality.Prime.CoreMovingRoughPolynomialGrowth
import PrimeGapNormality.Prime.CoreRoughDyadicDensity
import PrimeGapNormality.Prime.CoreRoughAdditiveBudget
import PrimeGapNormality.Prime.CoreRoughProfileError
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The actual first-gap tail bound for moving rough numbers

The dyadic one-point sieve gives the correct count in both `(X,2X]` and
`(2X,4X]`.  We spend only `cubeRootLevel X` points of the second window.
The finite part of every shifted gap tail therefore stays below `4X`, while
the remaining geometric part is negligible by the proved global quadratic
bound for the moving-rough enumeration.

Thus the paper's first-moment tail condition is obtained directly from two
adjacent physical windows.  No four-doubling property and no density or
growth hypothesis is exposed by the final theorem.
-/

namespace PrimeGapNormality.Prime.CoreRoughMeanTail

open Finset Filter CoreCyclic
open CoreRoughThreshold CoreRoughSyntheticScale CoreRoughScaleLimits
open CoreRoughProfileError CoreRoughSieveBudget CoreRoughSieveBudgetLimits
open CoreRoughAdditiveBudget CoreRoughDyadicDensity
open CoreMovingRoughSequence CoreMovingRoughPolynomialGrowth
open CoreSequenceAdjacentWindowTail CoreSequenceSTMeanTail
open scoped Topology BigOperators

noncomputable section

private theorem tendsto_two_mul_nat_atTop :
    Tendsto (fun X : ℕ ↦ 2 * X) atTop atTop :=
  tendsto_atTop_atTop_of_monotone
    (fun _ _ h ↦ Nat.mul_le_mul_left 2 h)
    fun n ↦ ⟨n, Nat.le_mul_of_pos_left n (by norm_num : 0 < 2)⟩

private theorem tendsto_log_pow_seven_div_self_zero :
    Tendsto (fun X : ℕ ↦ Real.log (X : ℝ) ^ (7 : ℕ) / (X : ℝ))
      atTop (nhds 0) := by
  have hreal :=
    (Real.isLittleO_pow_log_id_atTop (n := 7)).tendsto_div_nhds_zero
  exact hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem tendsto_log_sq_div_twoThird_zero :
    Tendsto (fun X : ℕ ↦ Real.log (X : ℝ) ^ (2 : ℕ) /
      (X : ℝ) ^ (2 / 3 : ℝ)) atTop (nhds 0) := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
  have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hcomp.congr'
  exact Eventually.of_forall fun X ↦ by
    simp only [Function.comp_apply, Real.rpow_two]

/-- The polylogarithmic profile and the cube-root reserve together occupy
`o(X / log^2 X)` points. -/
theorem tendsto_adjacentRoomEnvelope_zero :
    Tendsto (fun X : ℕ ↦
      ((Real.log (X : ℝ)) ^ (5 : ℕ) + (X : ℝ) ^ (1 / 3 : ℝ)) *
        (Real.log ((2 * X : ℕ) : ℝ)) ^ (2 : ℕ) / (X : ℝ))
      atTop (nhds 0) := by
  have hmajor : Tendsto (fun X : ℕ ↦
      4 * (Real.log (X : ℝ) ^ (7 : ℕ) / (X : ℝ) +
        Real.log (X : ℝ) ^ (2 : ℕ) /
          (X : ℝ) ^ (2 / 3 : ℝ))) atTop (nhds 0) := by
    have hsum := tendsto_log_pow_seven_div_self_zero.add
      tendsto_log_sq_div_twoThird_zero
    simpa only [add_zero, mul_zero] using hsum.const_mul (4 : ℝ)
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_ge_atTop 1] with X hX
    have hX0 : (0 : ℝ) < X := Nat.cast_pos.mpr hX
    have hlog0 : 0 ≤ Real.log (X : ℝ) :=
      Real.log_nonneg (Nat.one_le_cast.mpr hX)
    exact div_nonneg
      (mul_nonneg (add_nonneg (pow_nonneg hlog0 _)
        (Real.rpow_nonneg hX0.le _)) (pow_nonneg (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ 2 * X by omega))) _)) hX0.le
  · filter_upwards [eventually_ge_atTop 2] with X hX
    let x : ℝ := X
    let l : ℝ := Real.log x
    have hx0 : 0 < x := Nat.cast_pos.mpr (by omega)
    have hx1 : 1 ≤ x := Nat.one_le_cast.mpr (by omega)
    have hl0 : 0 ≤ l := Real.log_nonneg hx1
    have htwo : (2 : ℝ) * x ≤ x ^ (2 : ℕ) := by
      dsimp only [x]
      nlinarith [show (2 : ℝ) ≤ X by exact_mod_cast hX]
    have hlogTwo : Real.log ((2 * X : ℕ) : ℝ) ≤ 2 * l := by
      have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2 * x) htwo
      rw [Real.log_pow] at hh
      simpa only [Nat.cast_mul, Nat.cast_ofNat, l, x] using hh
    have hlogTwo0 : 0 ≤ Real.log ((2 * X : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * X by omega))
    have hlogSq : Real.log ((2 * X : ℕ) : ℝ) ^ (2 : ℕ) ≤
        4 * l ^ (2 : ℕ) := by
      have hh := pow_le_pow_left₀ hlogTwo0 hlogTwo 2
      nlinarith
    have hxsplit : x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hrootDiv : x ^ (1 / 3 : ℝ) * l ^ (2 : ℕ) / x =
        l ^ (2 : ℕ) / x ^ (2 / 3 : ℝ) := by
      have hp := Real.rpow_pos_of_pos hx0 (2 / 3 : ℝ)
      field_simp [hx0.ne', hp.ne']
      nlinarith
    have hnum0 : 0 ≤ l ^ (5 : ℕ) + x ^ (1 / 3 : ℝ) :=
      add_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg hx0.le _)
    calc
      ((Real.log (X : ℝ)) ^ (5 : ℕ) + (X : ℝ) ^ (1 / 3 : ℝ)) *
          Real.log ((2 * X : ℕ) : ℝ) ^ (2 : ℕ) / (X : ℝ) ≤
        (l ^ (5 : ℕ) + x ^ (1 / 3 : ℝ)) *
          (4 * l ^ (2 : ℕ)) / x := by
            apply div_le_div_of_nonneg_right _ hx0.le
            simpa only [l, x] using mul_le_mul_of_nonneg_left hlogSq hnum0
      _ = 4 * (l ^ (7 : ℕ) / x +
          l ^ (2 : ℕ) / x ^ (2 / 3 : ℝ)) := by
            rw [← hrootDiv]
            ring
      _ = 4 * (Real.log (X : ℝ) ^ (7 : ℕ) / (X : ℝ) +
          Real.log (X : ℝ) ^ (2 : ℕ) /
            (X : ℝ) ^ (2 / 3 : ℝ)) := by rfl

private theorem summable_succ_pow_mul_geometric
    {r : ℝ} (hr : ‖r‖ < 1) (hr0 : r ≠ 0) (d : ℕ) :
    Summable (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ d) * r ^ n) := by
  have hbase := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d hr
  have hshift := (summable_nat_add_iff
    (f := fun n : ℕ ↦ (n : ℝ) ^ d * r ^ n) 1).2 hbase
  refine (hshift.mul_left r⁻¹).congr fun n ↦ ?_
  rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by norm_num,
    pow_add]
  field_simp [hr0]

/-- A cube-root number of geometric steps beats the quadratic physical
endpoint. -/
theorem tendsto_cubeRoot_quadratic_geometric_zero
    {rho : ℝ} (hrho : 1 < rho) :
    Tendsto (fun X : ℕ ↦ rho⁻¹ ^ cubeRootLevel X *
      (((4 * X + 1 : ℕ) : ℝ) ^ (2 : ℕ))) atTop (nhds 0) := by
  have hr0 : 0 ≤ rho⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hrho).le
  have hrNorm : ‖rho⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact inv_lt_one_of_one_lt₀ hrho
  have hseries := summable_succ_pow_mul_geometric hrNorm
    (inv_ne_zero (zero_lt_one.trans hrho).ne') 6
  have hlimit : Tendsto (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ) ^ (6 : ℕ)) * rho⁻¹ ^ n)
      atTop (nhds 0) := hseries.tendsto_atTop_zero
  have hcomp := hlimit.comp tendsto_cubeRootLevel_atTop
  have hmajor := hcomp.const_mul (25 : ℝ)
  simp only [mul_zero] at hmajor
  apply squeeze_zero' _ _ hmajor
  · exact Eventually.of_forall fun X ↦ mul_nonneg (pow_nonneg hr0 _)
      (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with X hX
    let x : ℝ := X
    let R : ℝ := cubeRootLevel X
    have hx0 : 0 < x := Nat.cast_pos.mpr hX
    have hroot0 : 0 ≤ x ^ (1 / 3 : ℝ) := Real.rpow_nonneg hx0.le _
    have hfloor := Nat.lt_floor_add_one (x ^ (1 / 3 : ℝ))
    have hrootLt : x ^ (1 / 3 : ℝ) < R + 1 := by
      simpa only [R, x, cubeRootLevel, Nat.cast_add, Nat.cast_one] using hfloor
    have hcube : x < (R + 1) ^ (3 : ℕ) := by
      have hh := pow_lt_pow_left₀ hrootLt hroot0 (by norm_num : (3 : ℕ) ≠ 0)
      have hrootCube : (x ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = x := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        norm_num
      rwa [hrootCube] at hh
    have hphysical : (4 * x + 1) ^ (2 : ℕ) ≤
        25 * (R + 1) ^ (6 : ℕ) := by
      have hfour : 4 * x + 1 ≤ 5 * x := by
        have hx1 : 1 ≤ x := Nat.one_le_cast.mpr hX
        linarith
      have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * x + 1) hfour 2
      have hpow : x ^ (2 : ℕ) ≤ (R + 1) ^ (6 : ℕ) := by
        have hh := pow_le_pow_left₀ hx0.le hcube.le 2
        nlinarith
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hphysical
      (pow_nonneg hr0 (cubeRootLevel X))
    simpa only [Function.comp_apply, x, R, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- The literal moving-rough enumeration satisfies the paper's bare
first-gap mean tail bound at its synthetic model scale. -/
theorem movingRough_meanGapTailT
    {Ψ dΨ : ℝ → ℝ} {κ Creg : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hCreg : 0 ≤ Creg)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ Creg) :
    MeanGapTailT (movingRoughSequence (zPsi Ψ)) (localTailBase κ)
      (windowG ∘ fun X ↦ roughSyntheticScale (zPsi Ψ X)) := by
  let a := movingRoughSequence (zPsi Ψ)
  let rho := localTailBase κ
  let G : ℕ → ℝ := fun X ↦ windowG (roughSyntheticScale (zPsi Ψ X))
  let H : ℕ → ℕ := cubeRootLevel
  have hz : ∀ᶠ n : ℕ in atTop, zPsi Ψ n < n := hSlope.eventually_zPsi_lt
  have ha : StrictMono a := movingRoughSequence_strictMono hz
  have hrho : 1 < rho := by
    simpa only [rho] using localTailBase_one_lt hκ
  obtain ⟨Cnat, hquadNat⟩ := exists_global_quadratic_bound hz
  let C : ℝ := Cnat
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hquad : ∀ n : ℕ, (a n : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    dsimp only [a, C]
    exact_mod_cast hquadNat n
  apply meanGapTailT_of_adjacentWindow ha hrho hC hquad
  refine ⟨2, 1, by norm_num, by norm_num, ?_⟩
  have hcount := eventually_rawPhysicalRoots_main_comparable hSlope hCreg hreg
  have hcountTwo := tendsto_two_mul_nat_atTop.eventually hcount
  have hprofile := eventually_window_gap_bounds hκ hSlope
  have hprofileTwo := tendsto_two_mul_nat_atTop.eventually hprofile
  have hroom := tendsto_adjacentRoomEnvelope_zero
  have hroomSmall := hroom.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
  have hdeepRaw := tendsto_cubeRoot_quadratic_geometric_zero hrho
  have hdeep : Tendsto (fun X : ℕ ↦ rho⁻¹ ^ H X *
      (C * posMassGeomCoeff rho * (((4 * X + 1 : ℕ) : ℝ) ^ 2)))
      atTop (nhds 0) := by
    have hh := hdeepRaw.const_mul (C * posMassGeomCoeff rho)
    simpa only [rho, H, mul_zero] using hh.congr' (Eventually.of_forall fun X ↦ by ring)
  have hdeepSmall := hdeep.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hcount, hcountTwo, hprofile, hprofileTwo,
    hroomSmall, hdeepSmall, eventually_ge_atTop 2] with
      X hcountX hcount2X hprofX hprof2X hroomX hdeepX hX
  have hX0 : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hV : 0 < eulerProdNat (zPsi Ψ X) := eulerProdNat_pos _
  have hV2 : 0 < eulerProdNat (zPsi Ψ (2 * X)) := eulerProdNat_pos _
  have hcardEq := rawPhysicalRoots_card_eq_seqWindow hz X
  have hcardEq2 := rawPhysicalRoots_card_eq_seqWindow hz (2 * X)
  rw [hcardEq] at hcountX
  rw [hcardEq2] at hcount2X
  have hcardPos : (0 : ℝ) < (seqWindow a X).card := by
    dsimp only [a] at hcountX ⊢
    have hden : 0 < (X : ℝ) * eulerProdNat (zPsi Ψ X) := mul_pos hX0 hV
    have hratioPos := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hcountX.1
    rcases div_pos_iff.mp hratioPos with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge hden.le) hneg.2)
  have hN : 0 < (seqWindow a X).card := Nat.cast_pos.mp hcardPos
  have hmain : (X : ℝ) * eulerProdNat (zPsi Ψ X) ≤
      2 * ((seqWindow a X).card : ℝ) := by
    dsimp only [a] at hcountX ⊢
    have hden : 0 < (X : ℝ) * eulerProdNat (zPsi Ψ X) := mul_pos hX0 hV
    have hh := (le_div_iff₀ hden).mp hcountX.1
    nlinarith
  have hnormRough : (X : ℝ) / ((seqWindow a X).card : ℝ) ≤
      2 * roughGapScale (zPsi Ψ X) := by
    rw [div_le_iff₀ hcardPos]
    unfold roughGapScale
    have hs := mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hV.le)
    calc
      (X : ℝ) = (eulerProdNat (zPsi Ψ X))⁻¹ *
          ((X : ℝ) * eulerProdNat (zPsi Ψ X)) := by
        field_simp [hV.ne']
      _ ≤ (eulerProdNat (zPsi Ψ X))⁻¹ *
          (2 * ((seqWindow a X).card : ℝ)) := hs
      _ = 2 * (eulerProdNat (zPsi Ψ X))⁻¹ *
          ((seqWindow a X).card : ℝ) := by ring
  have hroughG : roughGapScale (zPsi Ψ X) ≤ G X := by
    dsimp only [G]
    exact (roughGapScale_le_log_synthetic_and_le _).1.trans
      (le_max_left _ _)
  have hnorm : (X : ℝ) / ((seqWindow a X).card : ℝ) ≤ 2 * G X :=
    hnormRough.trans (mul_le_mul_of_nonneg_left hroughG (by norm_num))
  have hnextMain : (X : ℝ) ≤
      roughGapScale (zPsi Ψ (2 * X)) *
        ((seqWindow a (2 * X)).card : ℝ) := by
    dsimp only [a] at hcount2X ⊢
    have hden : 0 < ((2 * X : ℕ) : ℝ) *
        eulerProdNat (zPsi Ψ (2 * X)) := by positivity
    have hh := (le_div_iff₀ hden).mp hcount2X.1
    unfold roughGapScale
    have hmain2 : (X : ℝ) * eulerProdNat (zPsi Ψ (2 * X)) ≤
        ((seqWindow a (2 * X)).card : ℝ) := by
      push_cast at hh ⊢
      nlinarith
    have hs := mul_le_mul_of_nonneg_left hmain2 (inv_nonneg.mpr hV2.le)
    calc
      (X : ℝ) = (eulerProdNat (zPsi Ψ (2 * X)))⁻¹ *
          ((X : ℝ) * eulerProdNat (zPsi Ψ (2 * X))) := by
        field_simp [hV2.ne']
      _ ≤ (eulerProdNat (zPsi Ψ (2 * X)))⁻¹ *
          ((seqWindow a (2 * X)).card : ℝ) := hs
      _ = (eulerProdNat (zPsi Ψ (2 * X)))⁻¹ *
          ((seqWindow a (2 * X)).card : ℝ) := rfl
  have hroomLt :
      ((Real.log (X : ℝ)) ^ (5 : ℕ) + (X : ℝ) ^ (1 / 3 : ℝ)) *
        (Real.log ((2 * X : ℕ) : ℝ)) ^ (2 : ℕ) < (X : ℝ) := by
    rw [Real.dist_eq, sub_zero] at hroomX
    have hnonneg : 0 ≤
        ((Real.log (X : ℝ)) ^ (5 : ℕ) + (X : ℝ) ^ (1 / 3 : ℝ)) *
          Real.log ((2 * X : ℕ) : ℝ) ^ (2 : ℕ) / (X : ℝ) := by
      positivity
    have hratio :
        ((Real.log (X : ℝ)) ^ (5 : ℕ) + (X : ℝ) ^ (1 / 3 : ℝ)) *
          Real.log ((2 * X : ℕ) : ℝ) ^ (2 : ℕ) / (X : ℝ) < 1 :=
      (le_abs_self _).trans_lt hroomX
    exact (div_lt_one hX0).mp hratio
  have hLcast : (stdProfileL rho (G X) : ℝ) ≤
      Real.log (X : ℝ) ^ (5 : ℕ) := by
    have hLS : profileL κ (roughSyntheticScale (zPsi Ψ X)) ≤
        ahlSmall_window κ (roughSyntheticScale (zPsi Ψ X)) := by
      unfold ahlSmall_window
      apply Nat.le_floor
      have hGone : (1 : ℝ) ≤
          windowG (roughSyntheticScale (zPsi Ψ X)) := le_max_right _ _
      have hL0 : (0 : ℝ) ≤
          profileL κ (roughSyntheticScale (zPsi Ψ X)) := Nat.cast_nonneg _
      have hfactor : (1 : ℝ) ≤ (6 / 5 : ℝ) *
          windowG (roughSyntheticScale (zPsi Ψ X)) := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (6 / 5 : ℝ) *
              windowG (roughSyntheticScale (zPsi Ψ X)) :=
            mul_le_mul (by norm_num) hGone (by norm_num) (by norm_num)
      have hh := mul_le_mul_of_nonneg_left hfactor hL0
      nlinarith
    have hcast :
        (profileL κ (roughSyntheticScale (zPsi Ψ X)) : ℝ) ≤
          (ahlSmall_window κ (roughSyntheticScale (zPsi Ψ X)) : ℝ) := by
      exact_mod_cast hLS
    have hSbound := hprofX.1
    unfold roughProfileS at hSbound
    rw [← profileL_eq_stdProfileL_localTailBase hκ]
    simpa only [rho, G, roughProfileS, Function.comp_apply] using
      hcast.trans (by linarith :
        (ahlSmall_window κ (roughSyntheticScale (zPsi Ψ X)) : ℝ) ≤
          Real.log (X : ℝ) ^ (5 : ℕ))
  have hHcast : (H X : ℝ) ≤ (X : ℝ) ^ (1 / 3 : ℝ) := by
    dsimp only [H, cubeRootLevel]
    exact Nat.floor_le (Real.rpow_nonneg hX0.le _)
  have hG2bound : roughGapScale (zPsi Ψ (2 * X)) ≤
      Real.log ((2 * X : ℕ) : ℝ) ^ (2 : ℕ) := hprof2X.2
  have hgap2 : 0 ≤ roughGapScale (zPsi Ψ (2 * X)) :=
    (roughGapScale_pos _).le
  have hreserve :
      ((stdProfileL rho (G X) + H X : ℕ) : ℝ) *
          roughGapScale (zPsi Ψ (2 * X)) < (X : ℝ) := by
    have hLH : ((stdProfileL rho (G X) + H X : ℕ) : ℝ) ≤
        Real.log (X : ℝ) ^ (5 : ℕ) + (X : ℝ) ^ (1 / 3 : ℝ) := by
      push_cast
      exact _root_.add_le_add hLcast hHcast
    have hupper0 : 0 ≤
        Real.log (X : ℝ) ^ (5 : ℕ) + (X : ℝ) ^ (1 / 3 : ℝ) := by
      positivity
    exact (mul_le_mul hLH hG2bound hgap2 hupper0).trans_lt hroomLt
  have hnextCast : ((stdProfileL rho (G X) + H X : ℕ) : ℝ) <
      ((seqWindow a (2 * X)).card : ℝ) := by
    have hs := hreserve.trans_le hnextMain
    exact (mul_lt_mul_iff_left₀ (roughGapScale_pos (zPsi Ψ (2 * X)))).mp
      (by simpa only [mul_comm] using hs)
  have hnext : stdProfileL rho (G X) + H X <
      (seqWindow a (2 * X)).card := by exact_mod_cast hnextCast
  have hdeepLt : rho⁻¹ ^ H X *
      (C * posMassGeomCoeff rho * (((4 * X + 1 : ℕ) : ℝ) ^ 2)) < 1 := by
    rw [Real.dist_eq, sub_zero] at hdeepX
    exact (le_abs_self _).trans_lt hdeepX
  have hGone : (1 : ℝ) ≤ G X := by
    dsimp only [G]
    exact le_max_right _ _
  have hdeepFinal : rho⁻¹ ^ H X *
      (C * posMassGeomCoeff rho * (((4 * X + 1 : ℕ) : ℝ) ^ 2)) ≤
        1 * (windowG ∘ fun Y ↦ roughSyntheticScale (zPsi Ψ Y)) X := by
    simpa only [G, Function.comp_apply, one_mul] using hdeepLt.le.trans hGone
  exact ⟨hN, hnorm, hnext, hdeepFinal⟩

end
end PrimeGapNormality.Prime.CoreRoughMeanTail
