import PrimeGapNormality.Prime.CoreRoughCellCountBounds

/-!
# A common vanishing relative error for all rough cells

The cell-dependent beta error is bounded by the common lower sieve level
`log X / (8 Ψ(log X))`.  After multiplication by the stopped moment envelope
`exp(10L)`, the slope budget leaves the existing negative margin
`exp(-(log X / Ψ(log X))/16)`.  The cutoff-hazard part is handled by the
weighted relative-hazard theorem.
-/

namespace PrimeGapNormality.Prime.CoreRoughCellErrorLimit

open Filter Set Finset
open scoped Topology Classical

open CoreRoughThreshold CoreRoughProfileError CoreRoughSieveBudget
  CoreRoughSieveBudgetLimits CoreRoughRelativeHazardBudget
  CoreRoughCellAsymptotics CoreRoughCellCountBounds
  CoreRoughPhysicalSlices CoreRoughPowerBand CoreRoughCellCutoff

noncomputable section

set_option maxHeartbeats 1200000

/-- Common beta major, independent of the cell index. -/
def uniformCellBetaError (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  Real.exp (299 * ((profileRank κ Ψ X + 1 : ℕ) : ℝ) -
    Real.log (X : ℝ) / (8 * Ψ (Real.log (X : ℝ))))

/-- Single relative error chosen before the cell and tuple. -/
def uniformCellRelativeError
    (κ C : ℝ) (J : ℕ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  cellHazardError κ C J Ψ X + uniformCellBetaError κ Ψ X

theorem uniformCellRelativeError_nonneg
    (κ : ℝ) {C : ℝ} (hC : 0 ≤ C) (J : ℕ) (Ψ : ℝ → ℝ) (X : ℕ) :
    0 ≤ uniformCellRelativeError κ C J Ψ X := by
  unfold uniformCellRelativeError uniformCellBetaError
  have hh : 0 ≤ cellHazardError κ C J Ψ X := by
    unfold cellHazardError cellPrimeLossBound
    positivity
  positivity

private theorem cellUpper_log_le
    {Ψ : ℝ → ℝ} {κ C : ℝ} {J X i : ℕ}
    (hP : 5 ≤ Ψ (Real.log (X : ℝ)))
    (hpsi : Ψ (Real.log (cellStart J X i : ℝ)) ≤
      2 * Ψ (Real.log (X : ℝ)))
    (hdata :
      16 ≤ cellCutoff J Ψ X i ∧
      cellCutoff J Ψ X i ≤ cellUpperCutoff κ C J Ψ X i ∧
      (∀ n ∈ Finset.Ico (cellStart J X i)
          (cellStart J X i + roughCellLength J X),
        ∀ h ≤ roughCellShift κ Ψ X,
          cellCutoff J Ψ X i ≤ zPsi Ψ (n + h) ∧
            zPsi Ψ (n + h) ≤ cellUpperCutoff κ C J Ψ X i) ∧
      (∑ p ∈ Nat.primesLE (cellUpperCutoff κ C J Ψ X i) \
          Nat.primesLE (cellCutoff J Ψ X i), (p : ℝ)⁻¹) ≤
        cellPrimeLossBound C J Ψ X ∧
      0 ≤ cellEpsRound C (cellStart J X i) (roughCellLength J X)
          (roughCellShift κ Ψ X) (cellCutoff J Ψ X i) ∧
        cellEpsRound C (cellStart J X i) (roughCellLength J X)
            (roughCellShift κ Ψ X) (cellCutoff J Ψ X i) *
          Real.log (cellCutoff J Ψ X i : ℝ) ≤ 1 / 4) :
    Real.log ((cellUpperCutoff κ C J Ψ X i : ℝ) + 1 / 2) ≤
      (12 / 5 : ℝ) * Ψ (Real.log (X : ℝ)) := by
  let y := cellCutoff J Ψ X i
  let u := cellUpperCutoff κ C J Ψ X i
  let ε := cellEpsRound C (cellStart J X i) (roughCellLength J X)
    (roughCellShift κ Ψ X) y
  have hy16 : 16 ≤ y := hdata.1
  have hu16 : 16 ≤ u := hy16.trans hdata.2.1
  have hε0 : 0 ≤ ε := by simpa only [ε, y] using hdata.2.2.2.2.1
  have hεsmall : ε * Real.log (y : ℝ) ≤ 1 / 4 := by
    simpa only [ε, y] using hdata.2.2.2.2.2
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (by omega)
  have hpowOne : 1 ≤ (y : ℝ) ^ (1 + ε) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ y by omega)) (by linarith)
  have huFloor : (u : ℝ) ≤ (y : ℝ) ^ (1 + ε) := by
    dsimp only [u, cellUpperCutoff, ε, y]
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hZupper : (u : ℝ) + 1 / 2 ≤ 2 * ((y : ℝ) ^ (1 + ε)) := by
    linarith
  have hlogZ := Real.log_le_log (by
    have huR : (16 : ℝ) ≤ u := Nat.cast_le.mpr hu16
    linarith : (0 : ℝ) < (u : ℝ) + 1 / 2) hZupper
  have hlogPower : Real.log (2 * ((y : ℝ) ^ (1 + ε))) =
      Real.log 2 + (1 + ε) * Real.log (y : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hypos _).ne', Real.log_rpow hypos]
  rw [hlogPower] at hlogZ
  have hlogyPsi : Real.log (y : ℝ) ≤
      Ψ (Real.log (cellStart J X i : ℝ)) := by
    have hyposNat : 0 < y := by omega
    dsimp only [y, cellCutoff] at hyposNat ⊢
    exact log_zPsi_le hyposNat
  have hlogTwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  nlinarith

/-- Every actual cell beta error is bounded by the same `X`-dependent
quantity, before the cell index is chosen. -/
theorem eventually_cellBetaError_le_uniform
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    ∀ᶠ X : ℕ in atTop, ∀ i ∈ range (cellCount J X),
      cellBetaError κ C J Ψ X i ≤ uniformCellBetaError κ Ψ X := by
  have ht : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpsiStart := eventually_psi_log_cellStart_le_two hSlope hC hreg
  have hP5 := (hSlope.2.1.comp ht).eventually_ge_atTop 5
  filter_upwards [eventually_cell_cutoff_band_data hκ hSlope hC hreg hJ,
    hpsiStart, hP5, eventually_log_cubeRootLevel_ge,
    ht.eventually_ge_atTop 0] with X hcell hpsiX hP5X hlogR ht0
  simp only [Function.comp_apply] at hP5X
  intro i hi
  let P := Ψ (Real.log (X : ℝ))
  let t := Real.log (X : ℝ)
  let R := cubeRootLevel X
  let Z := (cellUpperCutoff κ C J Ψ X i : ℝ) + 1 / 2
  have hdata := hcell i hi
  have hlogZ : Real.log Z ≤ (12 / 5 : ℝ) * P := by
    dsimp only [Z, P]
    exact cellUpper_log_le hP5X (hpsiX _ (cellStart_mem hi)) hdata
  have hZ : 1 < Z := by
    have hu16 : 16 ≤ cellUpperCutoff κ C J Ψ X i :=
      hdata.1.trans hdata.2.1
    have huR : (16 : ℝ) ≤ cellUpperCutoff κ C J Ψ X i :=
      Nat.cast_le.mpr hu16
    dsimp only [Z]
    linarith
  have hPpos : 0 < P := by dsimp only [P]; linarith
  have hs : t / (8 * P) ≤ Real.log R / Real.log Z :=
    sieve_s_ge ht0 hPpos hZ (by simpa only [t, R] using hlogR) hlogZ
  apply Real.exp_le_exp.mpr
  dsimp only [P, t, R, Z] at hs
  linarith

/-- The cell-dependent relative error is dominated by a single common
error, uniformly in the cell. -/
theorem eventually_cellRelativeError_le_uniform
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    ∀ᶠ X : ℕ in atTop, ∀ i ∈ range (cellCount J X),
      cellRelativeError κ C J Ψ X i ≤
        uniformCellRelativeError κ C J Ψ X := by
  filter_upwards [eventually_cellBetaError_le_uniform hκ hSlope hC hreg hJ]
      with X hX
  intro i hi
  unfold cellRelativeError uniformCellRelativeError
  exact _root_.add_le_add le_rfl (hX i hi)

/-- The finite per-cell tuple estimate with the single common relative
coefficient chosen before the cell and tuple. -/
theorem eventually_cell_tuple_error_uniform
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) (hJrank : 168 * κ < (J : ℝ) + 1) :
    ∀ᶠ X : ℕ in atTop, ∀ i ∈ range (cellCount J X),
      ∀ F : Finset ℕ,
      F ⊆ insert 0 (offsetWindow (roughCellShift κ Ψ X)) →
      1 ≤ F.card → F.card ≤ profileRank κ Ψ X + 1 →
      |((CoreRoughMovingCount.movingTupleInterval (zPsi Ψ) F
          (cellStart J X i) (roughCellLength J X)).card : ℝ) -
        (roughCellLength J X : ℝ) *
          finiteTupleSieveProduct F (cellCutoff J Ψ X i)| ≤
        uniformCellRelativeError κ C J Ψ X *
          ((roughCellLength J X : ℝ) *
            finiteTupleSieveProduct F (cellCutoff J Ψ X i)) +
          cellCRTError κ Ψ X := by
  filter_upwards [eventually_cell_tuple_error hκ hSlope hC hreg hJ hJrank,
    eventually_cellRelativeError_le_uniform hκ hSlope hC hreg hJ]
      with X hfinite huniform
  intro i hi F hF hFone hFrank
  have hraw := hfinite i hi F hF hFone hFrank
  have hmain0 : 0 ≤ (roughCellLength J X : ℝ) *
      finiteTupleSieveProduct F (cellCutoff J Ψ X i) :=
    mul_nonneg (Nat.cast_nonneg _)
      (finiteTupleSieveProduct_nonneg F (cellCutoff J Ψ X i))
  have hmul := mul_le_mul_of_nonneg_right (huniform i hi) hmain0
  exact hraw.trans (_root_.add_le_add hmul le_rfl)

private theorem tendsto_weighted_cellHazard_zero
    {Ψ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ))
    {J : ℕ} (hJrank : 168 * κ < (J : ℝ) + 1) :
    Tendsto (fun X : ℕ ↦
      cellHazardError κ C J Ψ X *
        Real.exp (10 * (roughProfileL κ (zPsi Ψ X) : ℝ)))
      atTop (nhds 0) := by
  have hpow := tendsto_power_hazard_zero hκ hSlope J hJrank
  have hsqrt := (tendsto_weightedRank_div_sqrt_zero hκ).comp
    hSlope.tendsto_zPsi_atTop
  have hsum := (hpow.const_mul (288 * C)).add (hsqrt.const_mul 144)
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  have ht : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually_ge_atTop 1] with X ht1
  have htpos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le ht1
  have hpowEq : 1 / Real.log (X : ℝ) ^ (J + 1) =
      Real.log (X : ℝ) ^ (-(J : ℝ) - 1) := by
    rw [show -(J : ℝ) - 1 = -((J + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg htpos.le, Real.rpow_natCast]
    simp only [one_div]
  unfold cellHazardError cellPrimeLossBound weightedRank profileRank
  simp only [Function.comp_apply]
  simp only [div_eq_mul_inv, one_mul] at hpowEq ⊢
  rw [hpowEq]
  ring

private theorem tendsto_weighted_uniformBeta_zero
    {Ψ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) :
    Tendsto (fun X : ℕ ↦ uniformCellBetaError κ Ψ X *
      Real.exp (10 * (roughProfileL κ (zPsi Ψ X) : ℝ)))
      atTop (nhds 0) := by
  have ht : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hmajor := tendsto_exp_negative_ratio_zero hSlope
  refine squeeze_zero' (Eventually.of_forall fun X ↦ by
    unfold uniformCellBetaError
    positivity) ?_ hmajor
  filter_upwards [eventually_profileRank_bound hSlope.2.1 hκ,
    ht.eventually hSlope.2.2, (hSlope.2.1.comp ht).eventually_ge_atTop 1,
    ht.eventually_ge_atTop 0] with X hr hslope hP1 ht0
  simp only [Function.comp_apply] at hslope hP1
  let P := Ψ (Real.log (X : ℝ))
  let t := Real.log (X : ℝ)
  have hPpos : 0 < P := by dsimp only [P]; linarith
  have hbudget :
      299 * ((profileRank κ Ψ X + 1 : ℕ) : ℝ) +
        10 * (roughProfileL κ (zPsi Ψ X) : ℝ) - t / (8 * P) ≤
          -(t / P) / 16 := by
    apply relative_exponent_budget hκ.le
      (Real.log_nonneg (by dsimp only [P]; linarith : 1 ≤ 3 * P))
      hPpos hr
      ((profileR_ge (roughProfileL κ (zPsi Ψ X)) 20).trans (Nat.le_succ _))
      le_rfl
    simpa only [P, t] using hslope
  unfold uniformCellBetaError
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp only [P, t] at hbudget ⊢
  nlinarith

/-- Final adverse-gate limit: the one common relative error absorbs the
full stopped moment envelope. -/
theorem tendsto_uniformCellRelativeError_mul_exp_zero
    {Ψ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    {J : ℕ} (hJrank : 168 * κ < (J : ℝ) + 1) :
    Tendsto (fun X : ℕ ↦ uniformCellRelativeError κ C J Ψ X *
      Real.exp (10 * (roughProfileL κ (zPsi Ψ X) : ℝ)))
      atTop (nhds 0) := by
  have hh := (tendsto_weighted_cellHazard_zero (C := C) hκ hSlope hJrank).add
    (tendsto_weighted_uniformBeta_zero hκ hSlope)
  simp only [add_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall fun X ↦ by
    unfold uniformCellRelativeError
    ring

/-- Consumer-facing name for the final weighted relative-error limit. -/
theorem tendsto_uniformCellRelativeError_weighted_zero
    {Ψ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    {J : ℕ} (hJrank : 168 * κ < (J : ℝ) + 1) :
    Tendsto (fun X : ℕ ↦ uniformCellRelativeError κ C J Ψ X *
      Real.exp (10 * (roughProfileL κ (zPsi Ψ X) : ℝ)))
      atTop (nhds 0) :=
  tendsto_uniformCellRelativeError_mul_exp_zero hκ hSlope hC hJrank

end

end PrimeGapNormality.Prime.CoreRoughCellErrorLimit
