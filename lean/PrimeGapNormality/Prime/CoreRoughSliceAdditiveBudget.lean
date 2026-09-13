import PrimeGapNormality.Prime.CoreRoughPhysicalSlices
import PrimeGapNormality.Prime.CoreRoughAdditiveBudget
import PrimeGapNormality.Prime.CoreRoughLayerMultiplicity

/-!
# Actual normalized additive CRT cost of the physical slices

The floor cell length and the common Euler normalization are the literal
ones from the moving-rough construction. Their lower bounds give a factor
at most 4*G*(log X)^J/X per uniform additive cell error. All growing layer
multiplicities are kept in the envelope whose limit was already proved.
-/

namespace PrimeGapNormality.Prime.CoreRoughSliceAdditiveBudget

open Filter Finset CoreRoughThreshold CoreRoughSyntheticScale CoreRoughProfileError
  CoreRoughCellAsymptotics CoreRoughPhysicalSlices CoreRoughSieveBudget
  CoreRoughSieveBudgetLimits
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

private theorem log_atTop : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem eventually_cellLength_lower (J : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ) / (2 * Real.log (X : ℝ) ^ J) ≤ (roughCellLength J X : ℝ) := by
  have hlim : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ J / (X : ℝ))
      atTop (𝓝 0) := by
    have hr := Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 J (by norm_num)
    have hn := hr.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    apply hn.congr'
    exact Eventually.of_forall fun X => by
      simp only [Function.comp_apply, one_mul, add_zero]
  filter_upwards [hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
    log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1] with X hsmall hlog hX
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hP : 0 < Real.log (X : ℝ) ^ J := pow_pos (by linarith) _
  have hPX := (div_le_iff₀ hXp).mp hsmall
  have hbig : (2 : ℝ) ≤ (X : ℝ) / Real.log (X : ℝ) ^ J :=
    (le_div_iff₀ hP).mpr (by linarith)
  have hf := Nat.lt_floor_add_one ((X : ℝ) / Real.log (X : ℝ) ^ J)
  have hid : (X : ℝ) / (2 * Real.log (X : ℝ) ^ J) =
      ((X : ℝ) / Real.log (X : ℝ) ^ J) / 2 := by ring
  unfold roughCellLength
  rw [hid]
  linarith

theorem eventually_cellCount_div_normalization_le
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    ∀ᶠ X : ℕ in atTop,
      (cellCount J X : ℝ) / rootNormalization J Ψ X ≤
        4 * roughGapScale (zPsi Ψ X) * Real.log (X : ℝ) ^ J / X := by
  have hz := (tendsto_rootNormalization_div_main_one hSlope hC hreg hJ).eventually_const_le
    (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [hz, eventually_cellLength_lower J,
    eventually_rootNormalization_pos hSlope hC hreg hJ,
    log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1]
      with X hZratio hH hZ hlog hX
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hP : 0 < Real.log (X : ℝ) ^ J := pow_pos (by linarith) _
  have hV := eulerProdNat_pos (zPsi Ψ X)
  have hmain := mainMass_pos Ψ (by omega : 0 < X)
  have hZlower : mainMass Ψ X / 2 ≤ rootNormalization J Ψ X := by
    have hZmul := (le_div_iff₀ hmain).mp hZratio
    linarith
  have hqH : (cellCount J X : ℝ) * (roughCellLength J X : ℝ) ≤ X := by
    have hh := coveredLength_le J X
    unfold coveredLength at hh
    exact_mod_cast hh
  have hprod := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg (cellCount J X))
  have hq : (cellCount J X : ℝ) ≤ 2 * Real.log (X : ℝ) ^ J := by
    have hbound : (cellCount J X : ℝ) * (X : ℝ) /
        (2 * Real.log (X : ℝ) ^ J) ≤ X := by
      simpa only [mul_div_assoc] using hprod.trans hqH
    have hh := (div_le_iff₀ (mul_pos (by norm_num) hP)).mp hbound
    nlinarith
  calc
    _ ≤ (2 * Real.log (X : ℝ) ^ J) / (mainMass Ψ X / 2) :=
      div_le_div₀ (by positivity) hq (div_pos hmain (by norm_num)) hZlower
    _ = _ := by
      unfold mainMass roughGapScale
      field_simp [hXp.ne', hV.ne'] <;> ring

/-- A uniform cell CRT error, already divided by the actual common mass. -/
def uniformCRT (κ : ℝ) (J : ℕ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  Real.exp (10 * ((profileRank κ Ψ X + 1 : ℕ) : ℝ)) *
    (cubeRootLevel X : ℝ) * (1 + Real.log (cubeRootLevel X : ℝ)) ^ profileRank κ Ψ X *
    ((cellCount J X : ℝ) / rootNormalization J Ψ X)

def layeredCost (κ : ℝ) (J : ℕ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  2 ^ profileRank κ Ψ X *
    (1 + (roughProfileS κ (zPsi Ψ X) : ℝ)) ^ profileRank κ Ψ X *
      uniformCRT κ J Ψ X

theorem tendsto_layeredCost_zero
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    Tendsto (layeredCost κ J Ψ) atTop (𝓝 0) := by
  have hlim := (CoreRoughAdditiveBudget.tendsto_envelope_zero hκ hSlope
    (C := 10) (by norm_num) (J := (J : ℝ)) (Nat.cast_nonneg _)).const_mul 4
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [tendsto_cubeRootLevel_atTop.eventually_ge_atTop 1] with X hR
    have hRreal : (1 : ℝ) ≤ cubeRootLevel X := by exact_mod_cast hR
    have hlR : 0 ≤ Real.log (cubeRootLevel X : ℝ) := Real.log_nonneg hRreal
    have hZ : 0 ≤ rootNormalization J Ψ X :=
      CoreRoughSliceLaws.normalization_nonneg _ _ _
    unfold layeredCost uniformCRT
    positivity
  · filter_upwards [eventually_cellCount_div_normalization_le hSlope hC hreg hJ,
      tendsto_cubeRootLevel_atTop.eventually_ge_atTop 1,
      log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1]
        with X hq hR hlog hX
    let r := profileRank κ Ψ X
    let S := roughProfileS κ (zPsi Ψ X)
    have hRreal : (1 : ℝ) ≤ cubeRootLevel X := by exact_mod_cast hR
    have hlR : 0 ≤ Real.log (cubeRootLevel X : ℝ) := Real.log_nonneg hRreal
    have hG := roughGapScale_pos (zPsi Ψ X)
    have hp2 : (2 : ℝ) ^ r ≤ 2 ^ (r + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ r)
    have hpS : (1 + (S : ℝ)) ^ r ≤ (1 + (S : ℝ)) ^ (r + 1) :=
      pow_le_pow_right₀ (by
        have hS0 : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
        linarith) (Nat.le_succ r)
    have hc := mul_le_mul hp2 hpS (by positivity) (by positivity)
    have hcoef : 0 ≤ Real.exp (10 * ((r + 1 : ℕ) : ℝ)) *
        (cubeRootLevel X : ℝ) * (1 + Real.log (cubeRootLevel X : ℝ)) ^ r := by positivity
    have hq0 : 0 ≤ (cellCount J X : ℝ) / rootNormalization J Ψ X :=
      div_nonneg (Nat.cast_nonneg _) (CoreRoughSliceLaws.normalization_nonneg _ _ _)
    calc
      layeredCost κ J Ψ X ≤
          (2 : ℝ) ^ (r + 1) * (1 + (S : ℝ)) ^ (r + 1) *
            (Real.exp (10 * ((r + 1 : ℕ) : ℝ)) *
              (cubeRootLevel X : ℝ) * (1 + Real.log (cubeRootLevel X : ℝ)) ^ r *
              (4 * roughGapScale (zPsi Ψ X) * Real.log (X : ℝ) ^ J / X)) :=
        mul_le_mul hc (mul_le_mul_of_nonneg_left hq hcoef)
          (mul_nonneg hcoef hq0) (by positivity)
      _ = 4 * CoreRoughAdditiveBudget.envelope κ 10 (J : ℝ) Ψ X := by
        unfold CoreRoughAdditiveBudget.envelope
        rw [Real.rpow_natCast]
        dsimp only [r, S]
        ring

end
end PrimeGapNormality.Prime.CoreRoughSliceAdditiveBudget
