import PrimeGapNormality.Prime.CoreRoughPrimeBand
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prime reciprocal mass in a narrow multiplicative power band

The real width calculation is separated from the exact natural interval
geometry.  The final estimate uses only `CoreRoughPrimeBand`; no PNT or
short-interval prime estimate is assumed.
-/

namespace PrimeGapNormality.Prime.CoreRoughPowerBand

open Filter Finset
open scoped Topology

open CoreRoughPrimeBand

noncomputable section

def powerBandLower (y : ℕ) (ε : ℝ) : ℕ :=
  ⌊(y : ℝ) ^ (1 - ε)⌋₊

def powerBandUpper (y : ℕ) (ε : ℝ) : ℕ :=
  ⌊(y : ℝ) ^ (1 + ε)⌋₊

def powerBandStart (y : ℕ) (ε : ℝ) : ℕ :=
  powerBandLower y ε + 1

def powerBandWidth (y : ℕ) (ε : ℝ) : ℕ :=
  powerBandUpper y ε - powerBandLower y ε

def powerPrimeBand (y : ℕ) (ε : ℝ) : Finset ℕ :=
  Nat.primesLE (powerBandUpper y ε) \ Nat.primesLE (powerBandLower y ε)

private theorem exp_le_one_add_two_mul {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4) :
    Real.exp u ≤ 1 + 2 * u := by
  have hrat := Real.exp_le_two_add_div_two_sub hu0 (by linarith : u < 2)
  have hden : 0 < 2 - u := by linarith
  have hfrac : (2 + u) / (2 - u) ≤ 1 + 2 * u := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg u]
  exact hrat.trans hfrac

private theorem rpow_add_eq {y : ℕ} (hy : 1 ≤ y) (ε : ℝ) :
    (y : ℝ) ^ (1 + ε) = (y : ℝ) * Real.exp (ε * Real.log (y : ℝ)) := by
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (zero_lt_one.trans_le hy)
  rw [Real.rpow_def_of_pos hypos]
  calc
    Real.exp (Real.log (y : ℝ) * (1 + ε)) =
        Real.exp (Real.log (y : ℝ) + ε * Real.log (y : ℝ)) := by
      congr 1
      ring
    _ = Real.exp (Real.log (y : ℝ)) *
        Real.exp (ε * Real.log (y : ℝ)) := Real.exp_add _ _
    _ = (y : ℝ) * Real.exp (ε * Real.log (y : ℝ)) := by
      rw [Real.exp_log hypos]

private theorem rpow_sub_eq {y : ℕ} (hy : 1 ≤ y) (ε : ℝ) :
    (y : ℝ) ^ (1 - ε) = (y : ℝ) * Real.exp (-(ε * Real.log (y : ℝ))) := by
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (zero_lt_one.trans_le hy)
  rw [Real.rpow_def_of_pos hypos]
  calc
    Real.exp (Real.log (y : ℝ) * (1 - ε)) =
        Real.exp (Real.log (y : ℝ) + -(ε * Real.log (y : ℝ))) := by
      congr 1
      ring
    _ = Real.exp (Real.log (y : ℝ)) *
        Real.exp (-(ε * Real.log (y : ℝ))) := Real.exp_add _ _
    _ = (y : ℝ) * Real.exp (-(ε * Real.log (y : ℝ))) := by
      rw [Real.exp_log hypos]

theorem powerBandLower_le_upper {y : ℕ} {ε : ℝ}
    (hy : 1 ≤ y) (hε : 0 ≤ ε) :
    powerBandLower y ε ≤ powerBandUpper y ε := by
  unfold powerBandLower powerBandUpper
  apply Nat.floor_le_floor
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hy) (by linarith)

/-- Exact conversion of the power band into the half-open interval used by
the prime-band cap. -/
theorem powerPrimeBand_eq_primeIco {y : ℕ} {ε : ℝ}
    (hy : 1 ≤ y) (hε : 0 ≤ ε) :
    powerPrimeBand y ε = primeIco (powerBandStart y ε) (powerBandWidth y ε) := by
  have hlu := powerBandLower_le_upper hy hε
  have hend : powerBandStart y ε + powerBandWidth y ε =
      powerBandUpper y ε + 1 := by
    unfold powerBandStart powerBandWidth
    omega
  ext p
  change p ∈ Nat.primesLE (powerBandUpper y ε) \
      Nat.primesLE (powerBandLower y ε) ↔
    p ∈ (Ico (powerBandStart y ε)
      (powerBandStart y ε + powerBandWidth y ε)).filter Nat.Prime
  constructor
  · intro hp
    have hpDiff := Finset.mem_sdiff.mp hp
    have hpU := Nat.mem_primesLE.mp hpDiff.1
    have hpPrime := hpU.2
    have hpLower : powerBandLower y ε < p := by
      by_contra hnot
      exact hpDiff.2 (Nat.mem_primesLE.mpr ⟨Nat.not_lt.mp hnot, hpPrime⟩)
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨?_, ?_⟩, hpPrime⟩
    · unfold powerBandStart
      omega
    · rw [hend]
      omega
  · intro hp
    have hpFilter := mem_filter.mp hp
    have hpI := mem_Ico.mp hpFilter.1
    have hpPrime := hpFilter.2
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨?_, hpPrime⟩, ?_⟩
    · rw [hend] at hpI
      omega
    · intro hpL
      have := (Nat.mem_primesLE.mp hpL).1
      unfold powerBandStart at hpI
      omega

/-- The exact natural width loses at most one unit beyond the real power
width. -/
theorem powerBandWidth_cast_le_real
    {y : ℕ} {ε : ℝ} (hy : 1 ≤ y) (hε : 0 ≤ ε) :
    (powerBandWidth y ε : ℝ) ≤
      (y : ℝ) ^ (1 + ε) - (y : ℝ) ^ (1 - ε) + 1 := by
  have hlu := powerBandLower_le_upper hy hε
  have hu0 : 0 ≤ (y : ℝ) ^ (1 + ε) :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (zero_lt_one.trans_le hy)) _).le
  have hlFloor : (y : ℝ) ^ (1 - ε) < (powerBandLower y ε : ℝ) + 1 := by
    unfold powerBandLower
    simpa only [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((y : ℝ) ^ (1 - ε))
  have huFloor : (powerBandUpper y ε : ℝ) ≤ (y : ℝ) ^ (1 + ε) := by
    unfold powerBandUpper
    exact Nat.floor_le hu0
  unfold powerBandWidth
  rw [Nat.cast_sub hlu]
  linarith

/-- Real width bound under the paper's small logarithmic budget. -/
theorem powerBandWidth_le
    {y : ℕ} {ε : ℝ} (hy : 1 ≤ y) (hε : 0 ≤ ε)
    (hsmall : ε * Real.log (y : ℝ) ≤ 1 / 4) :
    (powerBandWidth y ε : ℝ) ≤
      3 * ε * (y : ℝ) * Real.log (y : ℝ) + 1 := by
  let u := ε * Real.log (y : ℝ)
  have hlog : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hy)
  have hu0 : 0 ≤ u := mul_nonneg hε hlog
  have huexp := exp_le_one_add_two_mul hu0 (by simpa only [u] using hsmall)
  have hlexp : 1 - u ≤ Real.exp (-u) := Real.one_sub_le_exp_neg u
  have hreal :
      (y : ℝ) ^ (1 + ε) - (y : ℝ) ^ (1 - ε) ≤
        3 * ε * (y : ℝ) * Real.log (y : ℝ) := by
    rw [rpow_add_eq hy ε, rpow_sub_eq hy ε]
    have hy0 : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
    have hupp := mul_le_mul_of_nonneg_left huexp hy0
    have hlow := mul_le_mul_of_nonneg_left hlexp hy0
    dsimp only [u] at hupp hlow
    nlinarith
  exact (powerBandWidth_cast_le_real hy hε).trans
    (_root_.add_le_add hreal le_rfl)

private theorem powerBand_scale_bounds
    {y : ℕ} {ε : ℝ} (hy : 16 ≤ y) (hε : 0 ≤ ε)
    (hsmall : ε * Real.log (y : ℝ) ≤ 1 / 4) :
    y ≤ 2 * powerBandStart y ε ∧ powerBandWidth y ε ≤ y := by
  have hy1 : 1 ≤ y := le_trans (by norm_num) hy
  let u := ε * Real.log (y : ℝ)
  have hlog : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hy1)
  have hu0 : 0 ≤ u := mul_nonneg hε hlog
  have hlowExp : 1 - u ≤ Real.exp (-u) := Real.one_sub_le_exp_neg u
  have hlower : (y : ℝ) / 2 ≤ (y : ℝ) ^ (1 - ε) := by
    rw [rpow_sub_eq hy1 ε]
    have hu : u ≤ 1 / 4 := by simpa only [u] using hsmall
    have : (1 / 2 : ℝ) ≤ Real.exp (-u) := by linarith
    have hy0 : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
    nlinarith
  have hstart : (y : ℝ) / 2 < (powerBandStart y ε : ℝ) := by
    have hfloor : (y : ℝ) ^ (1 - ε) <
        (powerBandLower y ε : ℝ) + 1 := by
      unfold powerBandLower
      simpa only [Nat.cast_add, Nat.cast_one] using
        Nat.lt_floor_add_one ((y : ℝ) ^ (1 - ε))
    unfold powerBandStart
    simpa only [Nat.cast_add, Nat.cast_one] using hlower.trans_lt hfloor
  have hstartR : (y : ℝ) ≤ 2 * (powerBandStart y ε : ℝ) := by
    linarith
  have hstartNat : y ≤ 2 * powerBandStart y ε := by
    exact_mod_cast hstartR
  have hwidth := powerBandWidth_le hy1 hε hsmall
  have hyR : (16 : ℝ) ≤ y := Nat.cast_le.mpr hy
  have hwidthR : (powerBandWidth y ε : ℝ) ≤ (y : ℝ) := by
    have hu : ε * Real.log (y : ℝ) ≤ 1 / 4 := hsmall
    have hscaled := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg y)
    have hmain : 3 * ε * (y : ℝ) * Real.log (y : ℝ) + 1 ≤ (y : ℝ) := by
      nlinarith
    exact hwidth.trans hmain
  exact ⟨hstartNat, Nat.cast_le.mp hwidthR⟩

/-- Actual reciprocal mass of the narrow power band. -/
theorem eventually_powerPrimeBand_reciprocal_le :
    ∀ᶠ y : ℕ in atTop, ∀ ε : ℝ, 0 ≤ ε →
      ε * Real.log (y : ℝ) ≤ 1 / 4 →
      (∑ p ∈ powerPrimeBand y ε, (p : ℝ)⁻¹) ≤
        48 * (ε + 1 / Real.sqrt (y : ℝ)) := by
  filter_upwards [eventually_primeIcoReciprocal_le,
    eventually_ge_atTop 16] with y hband hy16
  intro ε hε hsmall
  have hy1 : 1 ≤ y := le_trans (by norm_num) hy16
  have hscale := powerBand_scale_bounds hy16 hε hsmall
  have hwidth := powerBandWidth_le hy1 hε hsmall
  have hcap := hband (powerBandStart y ε) (powerBandWidth y ε)
    hscale.1 hscale.2
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (le_trans (by norm_num) hy16))
  have hypos : (0 : ℝ) < y :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 16) hy16)
  have hsqrtPos : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.2 hypos
  have hsqrtLeY : Real.sqrt (y : ℝ) ≤ (y : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr (Nat.one_le_cast.mpr hy1))
  rw [powerPrimeBand_eq_primeIco hy1 hε]
  unfold primeIcoReciprocal at hcap
  have hwidthTerm :
      12 * (powerBandWidth y ε : ℝ) /
          ((y : ℝ) * Real.log (y : ℝ)) ≤
        36 * ε + 12 / ((y : ℝ) * Real.log (y : ℝ)) := by
    have hden : 0 < (y : ℝ) * Real.log (y : ℝ) := mul_pos hypos hlog
    apply (div_le_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0 : ℝ) ≤ 12)
    field_simp [hypos.ne', hlog.ne'] at hmul ⊢
    nlinarith
  have hround : 12 / ((y : ℝ) * Real.log (y : ℝ)) ≤
      12 / Real.sqrt (y : ℝ) := by
    have hlogOne : (1 : ℝ) ≤ Real.log (y : ℝ) := by
      apply (Real.le_log_iff_exp_le hypos).2
      have hexp : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have hyR : (16 : ℝ) ≤ y := Nat.cast_le.mpr hy16
      exact hexp.le.trans ((by norm_num : (3 : ℝ) ≤ 16).trans hyR)
    have hden : Real.sqrt (y : ℝ) ≤ (y : ℝ) * Real.log (y : ℝ) :=
      hsqrtLeY.trans (le_mul_of_one_le_right hypos.le
        hlogOne)
    exact div_le_div_of_nonneg_left (by norm_num) hsqrtPos hden
  calc
    ∑ p ∈ primeIco (powerBandStart y ε) (powerBandWidth y ε), (p : ℝ)⁻¹ ≤
        12 * (powerBandWidth y ε : ℝ) /
            ((y : ℝ) * Real.log (y : ℝ)) +
          12 / Real.sqrt (y : ℝ) := hcap
    _ ≤ (36 * ε + 12 / ((y : ℝ) * Real.log (y : ℝ))) +
          12 / Real.sqrt (y : ℝ) := _root_.add_le_add hwidthTerm le_rfl
    _ ≤ (36 * ε + 12 / Real.sqrt (y : ℝ)) +
          12 / Real.sqrt (y : ℝ) :=
      _root_.add_le_add (_root_.add_le_add le_rfl hround) le_rfl
    _ ≤ 48 * (ε + 1 / Real.sqrt (y : ℝ)) := by
      have hε0 := hε
      have hinv0 : 0 ≤ 1 / Real.sqrt (y : ℝ) := by positivity
      simp only [div_eq_mul_inv, one_mul] at hinv0 ⊢
      nlinarith

end

end PrimeGapNormality.Prime.CoreRoughPowerBand
