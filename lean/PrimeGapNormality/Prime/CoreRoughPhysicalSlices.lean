import PrimeGapNormality.Prime.CoreRoughDyadicDensity
import PrimeGapNormality.Prime.CoreRoughSliceLaws
import PrimeGapNormality.Prime.CoreRoughSliceModelBounds

/-!
# Literal physical slices and their common normalization

The full cells start at X+1, have length floor(X/(log X)^J), and retain
the Euler weight of their actual moving cutoff. Their common normalization
is asymptotic to X V(z(X)). The actual empirical mass tends to one by the
proved one-point dyadic density, charging the final discarded interval
once. No shape-comparison or assumed density statement is a premise.
-/

namespace PrimeGapNormality.Prime.CoreRoughPhysicalSlices

open Filter Finset
open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSubpower
  CoreRoughSyntheticScale CoreRoughProfileError CoreRoughCellAsymptotics
  CoreRoughGlobalCutoff CoreRoughDyadicDensity CoreRoughSliceLaws
  CoreRoughIntervalSlices
open scoped Topology Classical

noncomputable section
set_option maxHeartbeats 1000000

def cellCount (J X : ℕ) : ℕ := X / roughCellLength J X

def cellStart (J X i : ℕ) : ℕ := X + 1 + i * roughCellLength J X

def cellCutoff (J : ℕ) (Ψ : ℝ → ℝ) (X i : ℕ) : ℕ :=
  zPsi Ψ (cellStart J X i)

def coveredLength (J X : ℕ) : ℕ := cellCount J X * roughCellLength J X

def rootNormalization (J : ℕ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  normalization (roughCellLength J X) (cellCount J X) (cellCutoff J Ψ X)

def mainMass (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  (X : ℝ) * eulerProdNat (zPsi Ψ X)

theorem mainMass_pos (Ψ : ℝ → ℝ) {X : ℕ} (hX : 0 < X) :
    0 < mainMass Ψ X := mul_pos (Nat.cast_pos.mpr hX) (eulerProdNat_pos _)

theorem coveredLength_le (J X : ℕ) : coveredLength J X ≤ X :=
  Nat.div_mul_le_self _ _

theorem coveredLength_add_mod (J X : ℕ) :
    coveredLength J X + X % roughCellLength J X = X := by
  simpa only [coveredLength, cellCount, Nat.mul_comm] using
    Nat.div_add_mod X (roughCellLength J X)

theorem cellStart_mem {J X i : ℕ} (hi : i ∈ range (cellCount J X)) :
    cellStart J X i ∈ Set.Icc X (2 * X) := by
  have hiq : i + 1 ≤ cellCount J X := Nat.succ_le_iff.mpr (mem_range.mp hi)
  have hH : 0 < roughCellLength J X := by
    by_contra hh
    have hz : roughCellLength J X = 0 := by omega
    simp only [cellCount, hz, Nat.div_zero] at hiq
    omega
  have hmul := Nat.mul_le_mul_right (roughCellLength J X) hiq
  have hcover := coveredLength_le J X
  dsimp only [coveredLength] at hcover
  simp only [Nat.add_mul, one_mul] at hmul
  dsimp only [cellStart]
  constructor <;> omega

theorem eventually_cellLength_pos {Ψ : ℝ → ℝ} {A : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (J : ℕ) :
    ∀ᶠ X : ℕ in atTop, 0 < roughCellLength J X := by
  have hfit := eventually_roughCellShift_le_roughCellLength
    (κ := 1) (by norm_num) hSlope J
  have hlarge := ((tendsto_roughProfileS_atTop (κ := 1) (by norm_num)).comp
    hSlope.tendsto_zPsi_atTop).eventually_ge_atTop 1
  filter_upwards [hfit, hlarge] with X hfitX hlargeX
  simp only [Function.comp_apply] at hlargeX
  change roughProfileS 1 (zPsi Ψ X) ≤ roughCellLength J X at hfitX
  exact lt_of_lt_of_le (by omega : 0 < roughProfileS 1 (zPsi Ψ X)) hfitX

private theorem log_atTop :
    Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem eventually_cellLength_div_le {J : ℕ} (hJ : 2 < J) :
    ∀ᶠ X : ℕ in atTop,
      (roughCellLength J X : ℝ) / (X : ℝ) ≤ 1 / Real.log (X : ℝ) ^ 2 := by
  filter_upwards [log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1]
    with X hlog hX
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hlp : 0 < Real.log (X : ℝ) := by linarith
  have hfloor : (roughCellLength J X : ℝ) ≤ (X : ℝ) / Real.log (X : ℝ) ^ J :=
    Nat.floor_le (div_nonneg hXp.le (pow_nonneg hlp.le _))
  have hpows : Real.log (X : ℝ) ^ 2 ≤ Real.log (X : ℝ) ^ J :=
    pow_le_pow_right₀ hlog (by omega)
  calc
    (roughCellLength J X : ℝ) / X ≤ ((X : ℝ) / Real.log (X : ℝ) ^ J) / X :=
      div_le_div_of_nonneg_right hfloor hXp.le
    _ = 1 / Real.log (X : ℝ) ^ J := by field_simp [hXp.ne', hlp.ne']
    _ ≤ 1 / Real.log (X : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hlp _) hpows

theorem tendsto_cellLength_div_zero {J : ℕ} (hJ : 2 < J) :
    Tendsto (fun X : ℕ => (roughCellLength J X : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun X : ℕ => 1 / Real.log (X : ℝ) ^ 2) atTop (𝓝 0) := by
    exact (tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp log_atTop)).congr'
        (Eventually.of_forall fun X => by simp only [Function.comp_apply, one_div])
  exact squeeze_zero' (Eventually.of_forall fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (eventually_cellLength_div_le hJ) hlim

theorem tendsto_cellLength_div_main_zero {Ψ : ℝ → ℝ} {A : ℝ}
    (hSlope : HasSlopeBudget Ψ A) {J : ℕ} (hJ : 2 < J) :
    Tendsto (fun X : ℕ => (roughCellLength J X : ℝ) / mainMass Ψ X) atTop (𝓝 0) := by
  have hlim : Tendsto (fun X : ℕ =>
      (1 / eulerProdLowerConst) * (Real.log (X : ℝ))⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp log_atTop).const_mul
      (1 / eulerProdLowerConst)
    simp only [mul_zero] at h
    exact h.congr' (Eventually.of_forall fun X => rfl)
  refine squeeze_zero' (Eventually.of_forall fun X => by
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
      (eulerProdNat_pos _).le)) ?_ hlim
  filter_upwards [eventually_cellLength_div_le hJ, eventually_model_gap_le_log hSlope,
    log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1] with X hδ hG hlog hX
  have hlp : 0 < Real.log (X : ℝ) := by linarith
  have hprod := mul_le_mul hδ hG (roughGapScale_pos _).le
    (by positivity : 0 ≤ 1 / Real.log (X : ℝ) ^ 2)
  calc
    (roughCellLength J X : ℝ) / mainMass Ψ X =
        ((roughCellLength J X : ℝ) / X) * roughGapScale (zPsi Ψ X) := by
      unfold mainMass roughGapScale
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (1 / Real.log (X : ℝ) ^ 2) * (Real.log (X : ℝ) / eulerProdLowerConst) := hprod
    _ = (1 / eulerProdLowerConst) * (Real.log (X : ℝ))⁻¹ := by
      field_simp [hlp.ne']

theorem tendsto_coveredLength_div_one {Ψ : ℝ → ℝ} {A : ℝ}
    (hSlope : HasSlopeBudget Ψ A) {J : ℕ} (hJ : 2 < J) :
    Tendsto (fun X : ℕ => (coveredLength J X : ℝ) / X) atTop (𝓝 1) := by
  have hrem : Tendsto (fun X : ℕ => ((X % roughCellLength J X : ℕ) : ℝ) / X)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun X => by positivity) ?_
      (tendsto_cellLength_div_zero hJ)
    filter_upwards [eventually_cellLength_pos hSlope J] with X hH
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.mod_lt X hH).le) (Nat.cast_nonneg X)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hrem
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hXp : (X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have heq : (coveredLength J X : ℝ) + (X % roughCellLength J X : ℕ) = (X : ℝ) := by
    exact_mod_cast coveredLength_add_mod J X
  field_simp [hXp]
  linarith

theorem eventually_cell_euler_bounds {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) (J : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ i ∈ range (cellCount J X),
      (1 - dyadicRootHazard C Ψ X) * eulerProdNat (zPsi Ψ X) ≤
          eulerProdNat (cellCutoff J Ψ X i) ∧
        eulerProdNat (cellCutoff J Ψ X i) ≤ eulerProdNat (zPsi Ψ X) := by
  have hglobal := eventually_global_cutoff_and_primeLoss hSlope hC
    (show CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative Ψ dΨ C from hreg)
  filter_upwards [hglobal] with X hX
  intro i hi
  have hs := cellStart_mem hi
  have hc := hX (cellStart J X i) ⟨hs.1, hs.2.trans (by omega)⟩
  have hband : (∑ p ∈ Nat.primesLE (cellCutoff J Ψ X i) \ Nat.primesLE (zPsi Ψ X),
      (residueCount ({0} : Finset ℕ) p : ℝ) / (p : ℝ)) ≤ dyadicRootHazard C Ψ X := by
    simpa only [residueCount, image_singleton, card_singleton, Nat.cast_one, one_div,
      cellCutoff, cutoffPrimeReciprocalLoss, dyadicRootHazard] using hc.2.2
  simpa only [CoreRoughRootCount.singleton_tupleProduct, cellCutoff] using
    CoreRoughEulerStability.finiteTupleSieveProduct_bounds ({0} : Finset ℕ) hc.1 hband

theorem eventually_normalization_bounds {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) (J : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (1 - dyadicRootHazard C Ψ X) * ((coveredLength J X : ℝ) / X) ≤
          rootNormalization J Ψ X / mainMass Ψ X ∧
        rootNormalization J Ψ X / mainMass Ψ X ≤ (coveredLength J X : ℝ) / X := by
  filter_upwards [eventually_cell_euler_bounds hSlope hC hreg J, eventually_ge_atTop 1]
    with X hb hX
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hV := eulerProdNat_pos (zPsi Ψ X)
  have hsumlo := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (hb i hi).1 (Nat.cast_nonneg (roughCellLength J X)))
  have hsumhi := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (hb i hi).2 (Nat.cast_nonneg (roughCellLength J X)))
  have hlo : (1 - dyadicRootHazard C Ψ X) * (coveredLength J X : ℝ) *
      eulerProdNat (zPsi Ψ X) ≤ rootNormalization J Ψ X := by
    simpa only [rootNormalization, normalization, sum_const, card_range, nsmul_eq_mul,
      coveredLength, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hsumlo
  have hhi : rootNormalization J Ψ X ≤
      (coveredLength J X : ℝ) * eulerProdNat (zPsi Ψ X) := by
    simpa only [rootNormalization, normalization, sum_const, card_range, nsmul_eq_mul,
      coveredLength, Nat.cast_mul, mul_assoc] using hsumhi
  constructor
  · have hh := div_le_div_of_nonneg_right hlo (mainMass_pos Ψ (by omega : 0 < X)).le
    have heq : ((1 - dyadicRootHazard C Ψ X) * (coveredLength J X : ℝ) *
        eulerProdNat (zPsi Ψ X)) / mainMass Ψ X =
        (1 - dyadicRootHazard C Ψ X) * ((coveredLength J X : ℝ) / X) := by
      unfold mainMass
      field_simp [hXp.ne', hV.ne']
    rw [heq] at hh
    exact hh
  · have hh := div_le_div_of_nonneg_right hhi (mainMass_pos Ψ (by omega : 0 < X)).le
    have heq : ((coveredLength J X : ℝ) * eulerProdNat (zPsi Ψ X)) /
        mainMass Ψ X = (coveredLength J X : ℝ) / X := by
      unfold mainMass
      field_simp [hXp.ne', hV.ne']
    rw [heq] at hh
    exact hh

theorem tendsto_rootNormalization_div_main_one {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    Tendsto (fun X : ℕ => rootNormalization J Ψ X / mainMass Ψ X) atTop (𝓝 1) := by
  have hcover := tendsto_coveredLength_div_one hSlope hJ
  have hlo := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_dyadicRootHazard_zero
    (C := C) hSlope)).mul hcover
  simp only [sub_zero, one_mul] at hlo
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hcover
    ((eventually_normalization_bounds hSlope hC hreg J).mono fun X h => h.1)
    ((eventually_normalization_bounds hSlope hC hreg J).mono fun X h => h.2)

theorem eventually_rootNormalization_pos {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    ∀ᶠ X : ℕ in atTop, 0 < rootNormalization J Ψ X := by
  have hp := (tendsto_order.mp (tendsto_rootNormalization_div_main_one hSlope hC hreg hJ)).1
    0 (by norm_num)
  filter_upwards [hp, eventually_ge_atTop 1] with X hratio hX
  exact (div_pos_iff_of_pos_right (mainMass_pos Ψ (by omega))).mp hratio

theorem anchors_count_eq_predicate (J X : ℕ) (Ψ : ℝ → ℝ) :
    ((anchors (zPsi Ψ) (X + 1) (roughCellLength J X) (cellCount J X)).card : ℝ) =
      predicateCount (IsMovingRough (zPsi Ψ)) (X + 1) (coveredLength J X) := by
  unfold anchors predicateCount coveredLength
  congr

theorem raw_count_eq_predicate (X : ℕ) (Ψ : ℝ → ℝ) :
    ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) =
      predicateCount (IsMovingRough (zPsi Ψ)) (X + 1) X := by
  have hI : Finset.Ioc X (2 * X) = Finset.Ico (X + 1) (X + 1 + X) := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  simp only [rawPhysicalRoots, predicateCount, hI]

/-- One remainder interval, charged before any pattern multiplicities. -/
theorem full_cell_count_error_le (J X : ℕ) (Ψ : ℝ → ℝ) :
    |((anchors (zPsi Ψ) (X + 1) (roughCellLength J X) (cellCount J X)).card : ℝ) -
      ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ)| ≤ (X % roughCellLength J X : ℕ) := by
  rw [anchors_count_eq_predicate, raw_count_eq_predicate, abs_sub_comm,
    show coveredLength J X = cellCount J X * roughCellLength J X from rfl,
    predicateCount_mul]
  exact discarded_count_bound (IsMovingRough (zPsi Ψ)) (X + 1) X (roughCellLength J X)

theorem tendsto_full_cell_count_div_main_one {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    Tendsto (fun X : ℕ =>
      ((anchors (zPsi Ψ) (X + 1) (roughCellLength J X) (cellCount J X)).card : ℝ) /
        mainMass Ψ X) atTop (𝓝 1) := by
  have herr : Tendsto (fun X : ℕ =>
      (((anchors (zPsi Ψ) (X + 1) (roughCellLength J X) (cellCount J X)).card : ℝ) -
        ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ)) / mainMass Ψ X) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_cellLength_div_main_zero hSlope hJ)
    filter_upwards [eventually_cellLength_pos hSlope J, eventually_ge_atTop 1] with X hH hX
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mainMass_pos Ψ (by omega))]
    apply div_le_div_of_nonneg_right _ (mainMass_pos Ψ (by omega : 0 < X)).le
    exact (full_cell_count_error_le J X Ψ).trans (Nat.cast_le.mpr (Nat.mod_lt X hH).le)
  have h := herr.add (tendsto_rawPhysicalRoots_div_main_one hSlope hC hreg)
  simp only [zero_add] at h
  apply h.congr'
  exact Eventually.of_forall fun X => by unfold mainMass; ring

theorem tendsto_empirical_total_one {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) (S : ℕ → ℕ) :
    Tendsto (fun X : ℕ => ∑ U ∈ (offsetWindow (S X)).powerset,
      empiricalLaw (zPsi Ψ) (cellCutoff J Ψ X) (X + 1)
        (roughCellLength J X) (cellCount J X) (S X) U) atTop (𝓝 1) := by
  have h := (tendsto_full_cell_count_div_main_one hSlope hC hreg hJ).div
    (tendsto_rootNormalization_div_main_one hSlope hC hreg hJ) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [one_div_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [empiricalLaw_total]
  change (_ / mainMass Ψ X) / (rootNormalization J Ψ X / mainMass Ψ X) =
    _ / rootNormalization J Ψ X
  rw [div_div_div_cancel_right₀ (mainMass_pos Ψ (by omega : 0 < X)).ne']

end
end PrimeGapNormality.Prime.CoreRoughPhysicalSlices
