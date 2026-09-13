import PrimeGapNormality.Prime.CoreRoughPhysicalSlices
import PrimeGapNormality.Prime.CoreRoughRelativeHazardBudget
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual uniform tuple counts on rough physical cells

The cutoff and reciprocal-band hypotheses of the finite moving-tuple sieve
are discharged here from the literal moving cutoff and its eventual
weighted derivative condition.  The result is uniform in every complete
cell and every rooted tuple of the prescribed growing rank.

No per-cell cutoff, count, or comparison estimate is retained as a premise.
-/

namespace PrimeGapNormality.Prime.CoreRoughCellCountBounds

open Filter Set Finset
open scoped Topology Classical

open CoreRoughThreshold CoreRoughProfileError CoreRoughSieveBudget
  CoreRoughCellCutoff CoreRoughCellAsymptotics CoreRoughPhysicalSlices
  CoreRoughPowerBand CoreRoughMovingCount CoreRoughEulerStability

noncomputable section

set_option maxHeartbeats 1400000

/-- Concrete upper cutoff used on a complete physical cell. -/
def cellUpperCutoff (κ C : ℝ) (J : ℕ) (Ψ : ℝ → ℝ) (X i : ℕ) : ℕ :=
  powerBandUpper (cellCutoff J Ψ X i)
    (cellEpsRound C (cellStart J X i) (roughCellLength J X)
      (roughCellShift κ Ψ X) (cellCutoff J Ψ X i))

/-- Uniform reciprocal-prime loss before multiplication by tuple rank. -/
def cellPrimeLossBound (C : ℝ) (J : ℕ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  288 * C / Real.log (X : ℝ) ^ (J + 1) +
    144 / Real.sqrt (zPsi Ψ X : ℝ)

/-- Uniform relative Euler loss for all tuples through the paper rank. -/
def cellHazardError (κ C : ℝ) (J : ℕ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  ((profileRank κ Ψ X + 1 : ℕ) : ℝ) * cellPrimeLossBound C J Ψ X

/-- The actual beta error at the concrete upper cutoff of one cell. -/
def cellBetaError (κ C : ℝ) (J : ℕ) (Ψ : ℝ → ℝ) (X i : ℕ) : ℝ :=
  Real.exp (299 * ((profileRank κ Ψ X + 1 : ℕ) : ℝ) -
    Real.log (cubeRootLevel X : ℝ) /
      Real.log ((cellUpperCutoff κ C J Ψ X i : ℝ) + 1 / 2))

/-- Complete relative cell error: cutoff hazard plus the genuine beta term. -/
def cellRelativeError (κ C : ℝ) (J : ℕ) (Ψ : ℝ → ℝ) (X i : ℕ) : ℝ :=
  cellHazardError κ C J Ψ X + cellBetaError κ C J Ψ X i

/-- Uniform additive CRT envelope for all tuple sizes at most `r+1`. -/
def cellCRTError (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  Real.exp (10 * ((profileRank κ Ψ X + 1 : ℕ) : ℝ)) *
    (cubeRootLevel X : ℝ) *
      (1 + Real.log (cubeRootLevel X : ℝ)) ^ profileRank κ Ψ X

private theorem powerBandUpper_ge
    {y : ℕ} {ε : ℝ} (hy : 1 ≤ y) (hε : 0 ≤ ε) :
    y ≤ powerBandUpper y ε := by
  unfold powerBandUpper
  apply Nat.le_floor
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hy) (by linarith : (1 : ℝ) ≤ 1 + ε)

private theorem reciprocal_rounding_le_sqrt
    {y : ℕ} (hy : 16 ≤ y) :
    2 / ((y : ℝ) * Real.log (y : ℝ)) ≤ 2 / Real.sqrt (y : ℝ) := by
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (by omega : 1 < y))
  have hsqrt : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.2 hypos
  have hsqrtLeY : Real.sqrt (y : ℝ) ≤ (y : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ y by omega)))
  have hlogOne : (1 : ℝ) ≤ Real.log (y : ℝ) := by
    apply (Real.le_log_iff_exp_le hypos).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ y by omega))
  have hden : Real.sqrt (y : ℝ) ≤ (y : ℝ) * Real.log (y : ℝ) :=
    hsqrtLeY.trans (le_mul_of_one_le_right hypos.le hlogOne)
  exact div_le_div_of_nonneg_left (by norm_num) hsqrt hden

private theorem anchoredPrimeBand_le_powerPrimeBand
    {y : ℕ} {ε : ℝ} (hy : 1 ≤ y) (hε : 0 ≤ ε) :
    (∑ p ∈ Nat.primesLE (powerBandUpper y ε) \ Nat.primesLE y,
      (p : ℝ)⁻¹) ≤
        ∑ p ∈ powerPrimeBand y ε, (p : ℝ)⁻¹ := by
  have hlower : powerBandLower y ε ≤ y := by
    unfold powerBandLower
    have hp := Real.rpow_le_rpow_of_exponent_le
      (Nat.one_le_cast.mpr hy) (by linarith : (1 : ℝ) - ε ≤ 1)
    have hf := Nat.floor_le_floor hp
    simpa only [Real.rpow_one, Nat.floor_natCast] using hf
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpDiff := Finset.mem_sdiff.mp hp
    unfold powerPrimeBand
    apply Finset.mem_sdiff.mpr
    refine ⟨hpDiff.1, ?_⟩
    intro hpLower
    apply hpDiff.2
    have hh := Nat.mem_primesLE.mp hpLower
    exact Nat.mem_primesLE.mpr ⟨hh.1.trans hlower, hh.2⟩
  · intro p hp hnot
    exact inv_nonneg.mpr (Nat.cast_nonneg p)

/-- All finite cutoff data needed by the tuple sieve, with a uniform
reciprocal-prime loss. -/
theorem eventually_cell_cutoff_band_data
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    ∀ᶠ X : ℕ in atTop, ∀ i ∈ range (cellCount J X),
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
          Real.log (cellCutoff J Ψ X i : ℝ) ≤ 1 / 4 := by
  rcases eventually_atTop.1 eventually_cell_cutoff_and_primeBand with
    ⟨y₀, hy₀⟩
  have hdelta := eventually_cellDelta_roughCell_le hκ hSlope J
  have heps := eventually_cellEpsRound_le hκ hSlope hC J
  have hdata := eventually_weightedDerivative_on_roughCells hreg
  have hpsiStart := eventually_psi_log_cellStart_le_two hSlope hC hreg
  have hpsiOne : ∀ᶠ X : ℕ in atTop,
      Ψ (Real.log (X : ℝ)) ≤ Real.log (X : ℝ) := by
    have ht : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [one_mul] using ht.eventually
      (CoreRoughSubpower.eventually_psi_le_mul hSlope (by norm_num : (0 : ℝ) < 1))
  have hglobalReg : CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative Ψ dΨ C := by
    simpa only [CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative,
      HasEventuallyWeightedDerivative] using hreg
  have hglobal := CoreRoughGlobalCutoff.eventually_global_cutoff_and_primeLoss
    hSlope hC hglobalReg
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hdelta, heps, hdata, hpsiStart, hpsiOne, hglobal,
    hSlope.tendsto_zPsi_atTop.eventually_ge_atTop (max 16 y₀),
    hlog.eventually_ge_atTop (max 1 (96 * C)), eventually_ge_atTop 3]
      with X hdeltaX hepsX hdataX hpsiStartX hpsiOneX hglobalX hzlarge hloglarge hX3
  intro i hi
  let a := cellStart J X i
  let H := roughCellLength J X
  let S := roughCellShift κ Ψ X
  let y := cellCutoff J Ψ X i
  let ε := cellEpsRound C a H S y
  have haMem : a ∈ Set.Icc X (2 * X) := cellStart_mem hi
  have ha3 : a ∈ Set.Icc X (3 * X) := ⟨haMem.1, haMem.2.trans (by omega)⟩
  have hglobalA := hglobalX a ha3
  have hyLower : zPsi Ψ X ≤ y := by
    simpa only [y, cellCutoff, a] using hglobalA.1
  have hy16 : 16 ≤ y :=
    (le_max_left 16 y₀).trans hzlarge |>.trans hyLower
  have hyY₀ : y₀ ≤ y :=
    (le_max_right 16 y₀).trans hzlarge |>.trans hyLower
  have hXone : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hX3)
  have hXpos : (0 : ℝ) < X := zero_lt_one.trans hXone
  have hlX : 0 < Real.log (X : ℝ) := Real.log_pos hXone
  have hla : 0 < Real.log (a : ℝ) :=
    Real.log_pos (lt_of_lt_of_le hXone (Nat.cast_le.mpr haMem.1))
  have hlogXa : Real.log (X : ℝ) ≤ Real.log (a : ℝ) :=
    Real.log_le_log hXpos (Nat.cast_le.mpr haMem.1)
  have hdeltaA : cellDelta a H S ≤ 3 / Real.log (X : ℝ) ^ J := by
    simpa only [a, H, S] using hdeltaX a haMem
  have hdelta0 : 0 ≤ cellDelta a H S := by
    unfold cellDelta
    positivity
  have hPpos : 0 < Real.log (X : ℝ) ^ J := pow_pos hlX J
  have hδP : cellDelta a H S * Real.log (X : ℝ) ^ J ≤ 3 :=
    (le_div_iff₀ hPpos).mp hdeltaA
  have hPone : 1 ≤ Real.log (X : ℝ) ^ J :=
    one_le_pow₀ ((le_max_left _ _).trans hloglarge)
  have hlargeC : 96 * C ≤ Real.log (X : ℝ) :=
    (le_max_right _ _).trans hloglarge
  have hlocal : C * cellDelta a H S / Real.log (a : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ hla).2
    have hmul := mul_le_mul_of_nonneg_left hδP hC
    have hdenLarge : 12 * C ≤ Real.log (a : ℝ) * Real.log (X : ℝ) ^ J := by
      nlinarith
    nlinarith
  have hdataA := hdataX a H S haMem.1
  have hlogy : Real.log (y : ℝ) ≤ Ψ (Real.log (a : ℝ)) := by
    have hyposNat : 0 < y := by omega
    dsimp only [y, cellCutoff] at hyposNat ⊢
    exact log_zPsi_le hyposNat
  have hpsiA : Ψ (Real.log (a : ℝ)) ≤ 2 * Ψ (Real.log (X : ℝ)) := by
    simpa only [a] using hpsiStartX a haMem
  have hlogyUpper : Real.log (y : ℝ) ≤ 2 * Real.log (a : ℝ) := by
    calc
      Real.log (y : ℝ) ≤ Ψ (Real.log (a : ℝ)) := hlogy
      _ ≤ 2 * Ψ (Real.log (X : ℝ)) := hpsiA
      _ ≤ 2 * Real.log (X : ℝ) :=
        mul_le_mul_of_nonneg_left hpsiOneX (by norm_num)
      _ ≤ 2 * Real.log (a : ℝ) :=
        mul_le_mul_of_nonneg_left hlogXa (by norm_num)
  have heta0 : 0 ≤ cellEta C a H S := by
    unfold cellEta
    positivity
  have hroundSmall : cellEta C a H S * Real.log (y : ℝ) ≤ 1 / 8 := by
    have hnum : 2 * C * cellDelta a H S ≤
        6 * C / Real.log (X : ℝ) ^ J := by
      have hmul : 2 * C * cellDelta a H S ≤
          (2 * C) * (3 / Real.log (X : ℝ) ^ J) :=
        mul_le_mul_of_nonneg_left hdeltaA (show 0 ≤ 2 * C by positivity)
      calc
        2 * C * cellDelta a H S ≤
            (2 * C) * (3 / Real.log (X : ℝ) ^ J) := hmul
        _ = 6 * C / Real.log (X : ℝ) ^ J := by ring
    have heta : cellEta C a H S ≤
        (6 * C / Real.log (X : ℝ) ^ J) / Real.log (a : ℝ) := by
      unfold cellEta
      exact div_le_div_of_nonneg_right hnum hla.le
    have hright0 : 0 ≤ (6 * C / Real.log (X : ℝ) ^ J) /
        Real.log (a : ℝ) := by positivity
    have hmul := mul_le_mul heta hlogyUpper
      (Real.log_nonneg (Nat.one_le_cast.mpr (by omega : 1 ≤ y))) hright0
    have hbound : ((6 * C / Real.log (X : ℝ) ^ J) /
        Real.log (a : ℝ)) * (2 * Real.log (a : ℝ)) =
        12 * C / Real.log (X : ℝ) ^ J := by
      field_simp [hla.ne', hPpos.ne']
      ring
    rw [hbound] at hmul
    have hlast : 12 * C / Real.log (X : ℝ) ^ J ≤ 1 / 8 := by
      apply (div_le_iff₀ hPpos).2
      have hlogPow : Real.log (X : ℝ) ≤ Real.log (X : ℝ) ^ J := by
        have hh := pow_le_pow_right₀
          ((le_max_left _ _).trans hloglarge) (show (1 : ℕ) ≤ J by omega)
        simpa only [pow_one] using hh
      nlinarith
    exact hmul.trans hlast
  have haOne : 1 < a := by
    have hXa : X ≤ a := haMem.1
    have hXoneNat : 1 < X := lt_of_lt_of_le (by norm_num) hX3
    exact hXoneNat.trans_le hXa
  have hcell := hy₀ y hyY₀ Ψ dΨ C a H S rfl
    haOne hC
    (fun t ht ↦ (hdataA t ht).1)
    (fun t ht ↦ (hdataA t ht).2.1)
    (fun t ht ↦ (hdataA t ht).2.2)
    hlocal hroundSmall
  have hadm := CoreRoughRealAnchorBound.roundedBandWidth_admissible
    hy16 heta0 hroundSmall
  have hbandRaw := (anchoredPrimeBand_le_powerPrimeBand
    (by omega : 1 ≤ y) hadm.1).trans hcell.2
  have hepsA : ε ≤ 6 * C / Real.log (X : ℝ) ^ (J + 1) +
      2 / ((y : ℝ) * Real.log (y : ℝ)) := by
    simpa only [ε, a, H, S] using hepsX a haMem y
  have hroundRoot := reciprocal_rounding_le_sqrt hy16
  have hsqrtMono : 1 / Real.sqrt (y : ℝ) ≤
      1 / Real.sqrt (zPsi Ψ X : ℝ) := by
    have hzpos : (0 : ℝ) < zPsi Ψ X := Nat.cast_pos.mpr (by omega)
    have hsqrtPos : 0 < Real.sqrt (zPsi Ψ X : ℝ) := Real.sqrt_pos.2 hzpos
    apply one_div_le_one_div_of_le hsqrtPos
    exact Real.sqrt_le_sqrt (Nat.cast_le.mpr hyLower)
  have hbandFinal : (∑ p ∈ Nat.primesLE (cellUpperCutoff κ C J Ψ X i) \
      Nat.primesLE (cellCutoff J Ψ X i), (p : ℝ)⁻¹) ≤
      cellPrimeLossBound C J Ψ X := by
    change (∑ p ∈ Nat.primesLE (powerBandUpper y ε) \ Nat.primesLE y,
      (p : ℝ)⁻¹) ≤ cellPrimeLossBound C J Ψ X
    have hepsRoot : ε ≤ 6 * C / Real.log (X : ℝ) ^ (J + 1) +
        2 / Real.sqrt (y : ℝ) :=
      hepsA.trans (_root_.add_le_add le_rfl hroundRoot)
    calc
      _ ≤ 48 * (ε + 1 / Real.sqrt (y : ℝ)) := hbandRaw
      _ ≤ 48 * ((6 * C / Real.log (X : ℝ) ^ (J + 1) +
          2 / Real.sqrt (y : ℝ)) + 1 / Real.sqrt (y : ℝ)) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add hepsRoot le_rfl)
          (by norm_num : (0 : ℝ) ≤ 48)
      _ = 288 * C / Real.log (X : ℝ) ^ (J + 1) +
          144 * (1 / Real.sqrt (y : ℝ)) := by ring
      _ ≤ 288 * C / Real.log (X : ℝ) ^ (J + 1) +
          144 * (1 / Real.sqrt (zPsi Ψ X : ℝ)) :=
        _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hsqrtMono
          (by norm_num : (0 : ℝ) ≤ 144))
      _ = cellPrimeLossBound C J Ψ X := by
        unfold cellPrimeLossBound
        ring
  refine ⟨hy16, ?_, ?_, hbandFinal, ?_⟩
  · unfold cellUpperCutoff
    exact powerBandUpper_ge (by omega) (by
      unfold cellEpsRound CoreRoughRealAnchorBound.roundedBandWidth
        cellEta cellDelta
      positivity)
  · simpa only [cellUpperCutoff, ε, y, a, H, S] using hcell.1
  · simpa only [ε, y, a, H, S, cellEpsRound] using hadm

private def weightedCellHazard
    (κ C : ℝ) (J : ℕ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  288 * C * (CoreRoughRelativeHazardBudget.weightedRank κ (zPsi Ψ X) *
      Real.log (X : ℝ) ^ (-(J : ℝ) - 1)) +
    144 * (CoreRoughRelativeHazardBudget.weightedRank κ (zPsi Ψ X) /
      Real.sqrt (zPsi Ψ X : ℝ))

private theorem tendsto_weightedCellHazard_zero
    {Ψ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ))
    {J : ℕ} (hJ : 168 * κ < (J : ℝ) + 1) :
    Tendsto (weightedCellHazard κ C J Ψ) atTop (nhds 0) := by
  have hpow := CoreRoughRelativeHazardBudget.tendsto_power_hazard_zero
    hκ hSlope J hJ
  have hsqrt :=
    (CoreRoughRelativeHazardBudget.tendsto_weightedRank_div_sqrt_zero hκ).comp
      hSlope.tendsto_zPsi_atTop
  have hsum := (hpow.const_mul (288 * C)).add (hsqrt.const_mul 144)
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun X ↦ by
    unfold weightedCellHazard
    simp only [Function.comp_apply]

theorem tendsto_cellHazardError_zero
    {Ψ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    {J : ℕ} (hJ : 168 * κ < (J : ℝ) + 1) :
    Tendsto (cellHazardError κ C J Ψ) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_weightedCellHazard_zero (C := C) hκ hSlope hJ)
  · exact Eventually.of_forall fun X ↦ by
      unfold cellHazardError cellPrimeLossBound
      positivity
  · have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [hlog.eventually_ge_atTop 1] with X hlX1
    have hlX : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlX1
    have hpowEq : 1 / Real.log (X : ℝ) ^ (J + 1) =
        Real.log (X : ℝ) ^ (-(J : ℝ) - 1) := by
      rw [show -(J : ℝ) - 1 = -((J + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_neg hlX.le, Real.rpow_natCast]
      simp only [one_div]
    have hrank : ((profileRank κ Ψ X + 1 : ℕ) : ℝ) ≤
        CoreRoughRelativeHazardBudget.weightedRank κ (zPsi Ψ X) := by
      unfold CoreRoughRelativeHazardBudget.weightedRank profileRank
      have hone : (1 : ℝ) ≤ Real.exp (10 * (roughProfileL κ (zPsi Ψ X) : ℝ)) :=
        Real.one_le_exp (by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg _)
    have hlogTerm0 : 0 ≤ Real.log (X : ℝ) ^ (-(J : ℝ) - 1) :=
      Real.rpow_nonneg hlX.le _
    have hsqrtTerm0 : 0 ≤ 1 / Real.sqrt (zPsi Ψ X : ℝ) := by positivity
    have hfirst := mul_le_mul_of_nonneg_right hrank hlogTerm0
    have hsecond := mul_le_mul_of_nonneg_right hrank hsqrtTerm0
    unfold cellHazardError cellPrimeLossBound weightedCellHazard
    simp only [div_eq_mul_inv, one_mul] at hpowEq hsecond ⊢
    rw [hpowEq]
    nlinarith

/-- Actual per-cell moving-tuple estimate, uniform in every rooted tuple
through the growing rank.  Its relative error is the explicit local hazard
plus the genuine beta term; the additive term is paid once per cell. -/
theorem eventually_cell_tuple_error
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) (hJrank : 168 * κ < (J : ℝ) + 1) :
    ∀ᶠ X : ℕ in atTop, ∀ i ∈ range (cellCount J X),
      ∀ F : Finset ℕ,
      F ⊆ insert 0 (offsetWindow (roughCellShift κ Ψ X)) →
      1 ≤ F.card → F.card ≤ profileRank κ Ψ X + 1 →
      |((movingTupleInterval (zPsi Ψ) F (cellStart J X i)
          (roughCellLength J X)).card : ℝ) -
        (roughCellLength J X : ℝ) *
          finiteTupleSieveProduct F (cellCutoff J Ψ X i)| ≤
        cellRelativeError κ C J Ψ X i *
          ((roughCellLength J X : ℝ) *
            finiteTupleSieveProduct F (cellCutoff J Ψ X i)) +
          cellCRTError κ Ψ X := by
  have hδlim := tendsto_cellHazardError_zero hκ hSlope hC hJrank
  have hδhalf : ∀ᶠ X : ℕ in atTop,
      cellHazardError κ C J Ψ X ≤ 1 / 2 := by
    filter_upwards [hδlim.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))]
        with X hball
    have hdist : dist (cellHazardError κ C J Ψ X) 0 < 1 / 2 :=
      Metric.mem_ball.mp hball
    rw [Real.dist_eq, sub_zero] at hdist
    exact (le_abs_self _).trans hdist.le
  have ht : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpsiStart := eventually_psi_log_cellStart_le_two hSlope hC hreg
  have hP5 := (hSlope.2.1.comp ht).eventually_ge_atTop 5
  have hrank := eventually_profileRank_bound hSlope.2.1 hκ
  have hslope := ht.eventually hSlope.2.2
  filter_upwards [eventually_cell_cutoff_band_data hκ hSlope hC hreg hJ,
    hδhalf, CoreRoughSieveBudgetLimits.tendsto_cubeRootLevel_atTop.eventually_ge_atTop 1,
    eventually_log_cubeRootLevel_ge, hpsiStart, hP5, hrank, hslope,
    ht.eventually_ge_atTop 0, eventually_ge_atTop 3]
      with X hcell hδhalfX hR hlogR hpsiStartX hP5X hrankX hslopeX ht0 hX3
  simp only [Function.comp_apply] at hP5X hslopeX
  intro i hi F hF hFone hFrank
  let a := cellStart J X i
  let y := cellCutoff J Ψ X i
  let u := cellUpperCutoff κ C J Ψ X i
  let ε := cellEpsRound C a (roughCellLength J X)
    (roughCellShift κ Ψ X) y
  let δ := cellHazardError κ C J Ψ X
  let R := cubeRootLevel X
  let P := Ψ (Real.log (X : ℝ))
  let t := Real.log (X : ℝ)
  have hdata := hcell i hi
  have hbandHazard : (∑ p ∈ Nat.primesLE u \ Nat.primesLE y,
      (residueCount F p : ℝ) / (p : ℝ)) ≤ δ := by
    have hh := bandHazard_le_card_mul F (h := cellPrimeLossBound C J Ψ X)
      (by simpa only [u, y] using hdata.2.2.2.1)
    have hcard : (F.card : ℝ) ≤ ((profileRank κ Ψ X + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr hFrank
    have hbase0 : 0 ≤ cellPrimeLossBound C J Ψ X := by
      unfold cellPrimeLossBound
      positivity
    exact hh.trans (by
      unfold δ cellHazardError
      exact mul_le_mul_of_nonneg_right hcard hbase0)
  have hcutF : ∀ n ∈ Finset.Ico (cellStart J X i)
      (cellStart J X i + roughCellLength J X),
      ∀ h ∈ F, y ≤ zPsi Ψ (n + h) ∧ zPsi Ψ (n + h) ≤ u := by
    intro n hn h hh
    apply hdata.2.2.1 n hn h
    rcases mem_insert.mp (hF hh) with rfl | hwin
    · omega
    · exact (mem_Icc.mp hwin).2
  have hδhalf' : δ ≤ 1 / 2 := by simpa only [δ] using hδhalfX
  have hy16 : 16 ≤ y := hdata.1
  have hu16 : 16 ≤ u := hy16.trans hdata.2.1
  have hZ : 1 < (u : ℝ) + 1 / 2 := by
    have huR : (16 : ℝ) ≤ u := Nat.cast_le.mpr hu16
    linarith
  have hε0 : 0 ≤ ε := by simpa only [ε, a, y] using hdata.2.2.2.2.1
  have hεsmall : ε * Real.log (y : ℝ) ≤ 1 / 4 := by
    simpa only [ε, a, y] using hdata.2.2.2.2.2
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (by omega)
  have hpowOne : 1 ≤ (y : ℝ) ^ (1 + ε) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ y by omega)) (by linarith)
  have huFloor : (u : ℝ) ≤ (y : ℝ) ^ (1 + ε) := by
    dsimp only [u, cellUpperCutoff, ε, y, a]
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hZupper : (u : ℝ) + 1 / 2 ≤ 2 * ((y : ℝ) ^ (1 + ε)) := by
    linarith
  have hlogZ := Real.log_le_log (by linarith : 0 < (u : ℝ) + 1 / 2) hZupper
  have hlogPower : Real.log (2 * ((y : ℝ) ^ (1 + ε))) =
      Real.log 2 + (1 + ε) * Real.log (y : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hypos _).ne', Real.log_rpow hypos]
  rw [hlogPower] at hlogZ
  have haMem := cellStart_mem hi
  have hpsiA := hpsiStartX (cellStart J X i) haMem
  have hlogyPsi : Real.log (y : ℝ) ≤ Ψ (Real.log (a : ℝ)) := by
    have hyposNat : 0 < y := by omega
    dsimp only [y, cellCutoff, a] at hyposNat ⊢
    exact log_zPsi_le hyposNat
  have hP5' : 5 ≤ P := by simpa only [P] using hP5X
  have hPpos : 0 < P := by linarith
  have hlogTwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlogZupper : Real.log ((u : ℝ) + 1 / 2) ≤ (12 / 5 : ℝ) * P := by
    have hpsiA' : Ψ (Real.log (a : ℝ)) ≤ 2 * P := by
      simpa only [P, a] using hpsiA
    nlinarith
  have hs : t / (8 * P) ≤ Real.log R / Real.log ((u : ℝ) + 1 / 2) :=
    sieve_s_ge ht0 hPpos hZ (by simpa only [t, R] using hlogR) hlogZupper
  have hbudget :
      299 * ((profileRank κ Ψ X + 1 : ℕ) : ℝ) +
        10 * (roughProfileL κ (zPsi Ψ X) : ℝ) -
          Real.log R / Real.log ((u : ℝ) + 1 / 2) ≤ -(t / P) / 16 := by
    apply relative_exponent_budget hκ.le
      (Real.log_nonneg (by linarith : 1 ≤ 3 * P)) hPpos hrankX
      ((profileR_ge (roughProfileL κ (zPsi Ψ X)) 20).trans (Nat.le_succ _))
      hs
    simpa only [P, t] using hslopeX
  have hdegree : ((9 * F.card + 1 : ℕ) : ℝ) ≤
      Real.log R / Real.log ((u : ℝ) + 1 / 2) := by
    have hcast : (F.card : ℝ) ≤ ((profileRank κ Ψ X + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr hFrank
    have hFoneR : (1 : ℝ) ≤ F.card := by exact_mod_cast hFone
    have hratio0 : 0 ≤ t / P := div_nonneg ht0 hPpos.le
    have hL0 : 0 ≤ (roughProfileL κ (zPsi Ψ X) : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith
  have hlevel : ((u : ℝ) + 1 / 2) ^ (9 * F.card + 1) ≤ R := by
    have hlogLevel := (le_div_iff₀ (Real.log_pos hZ)).mp hdegree
    have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr hR
    apply (Real.log_le_log_iff (pow_pos (zero_lt_one.trans hZ) _) hRpos).mp
    simpa only [Real.log_pow] using hlogLevel
  have hstart : 0 < cellStart J X i := by
    exact (show 0 < X by omega).trans_le haMem.1
  have hraw := movingTupleInterval_error (zPsi Ψ) F hFone
    (cellStart J X i) (roughCellLength J X)
    hstart
    hdata.1 hdata.2.1 hcutF hδhalf' hbandHazard hlevel
  have hmain0 : 0 ≤ (roughCellLength J X : ℝ) *
      finiteTupleSieveProduct F y :=
    mul_nonneg (Nat.cast_nonneg _) (finiteTupleSieveProduct_nonneg F y)
  have hbeta : Real.exp (299 * (F.card : ℝ) -
      Real.log R / Real.log ((u : ℝ) + 1 / 2)) ≤
      cellBetaError κ C J Ψ X i := by
    apply Real.exp_le_exp.mpr
    have hcast : (F.card : ℝ) ≤ ((profileRank κ Ψ X + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr hFrank
    dsimp only [R, u]
    nlinarith
  have hrel := _root_.add_le_add (le_rfl : δ ≤ δ) hbeta
  have hmain := mul_le_mul_of_nonneg_left hrel hmain0
  have hbase : 1 ≤ 1 + Real.log R :=
    le_add_of_nonneg_right (Real.log_nonneg (Nat.one_le_cast.mpr hR))
  have hpow : (1 + Real.log R) ^ (F.card - 1) ≤
      (1 + Real.log R) ^ profileRank κ Ψ X :=
    pow_le_pow_right₀ hbase (by omega)
  have hexp : Real.exp (10 * (F.card : ℝ)) ≤
      Real.exp (10 * ((profileRank κ Ψ X + 1 : ℕ) : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr hFrank) (by norm_num))
  have hcrt := mul_le_mul (mul_le_mul hexp le_rfl
    (Nat.cast_nonneg R) (Real.exp_pos _).le) hpow
    (by positivity) (by positivity)
  unfold cellRelativeError cellCRTError
  dsimp only [δ, R, u, y] at hraw hmain hcrt ⊢
  nlinarith

end

end PrimeGapNormality.Prime.CoreRoughCellCountBounds
