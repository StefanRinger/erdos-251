import PrimeGapNormality.Prime.CoreRoughCellCutoff
import PrimeGapNormality.Prime.CoreRoughSieveBudget
import PrimeGapNormality.Prime.CoreRoughSubpower
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Global control of a derivative-regular moving rough cutoff

For bounded-model comparisons it is enough to compare the literal cutoffs
throughout the coarse physical range `[X,3X]`.  The weighted derivative
condition encloses every such cutoff in one power band based at the actual
natural anchor `zPsi Ψ X`.  The reciprocal prime loss is consequently
`O_C(1 / log X + 1 / sqrt (zPsi Ψ X))`.

This is only a cutoff and Euler-factor loss estimate.  It does not use or
assert a rough-number density or a one-point counting theorem.
-/

namespace PrimeGapNormality.Prime.CoreRoughGlobalCutoff

open Filter Set Finset
open scoped Topology

open CoreRoughThreshold CoreRoughSubpower CoreRoughCutoffLocality
  CoreRoughRealAnchorBound CoreRoughPowerBand CoreRoughSieveBudget

noncomputable section

/-- Exponent loss for the full physical range `[X,3X]`. -/
def globalCutoffEta (C : ℝ) (X : ℕ) : ℝ :=
  4 * C / Real.log (X : ℝ)

/-- Power-band width after retaining the actual floored anchor. -/
def globalCutoffEps (C : ℝ) (X y : ℕ) : ℝ :=
  roundedBandWidth y (globalCutoffEta C X)

/-- Reciprocal mass of the primes introduced between two literal cutoffs. -/
def cutoffPrimeReciprocalLoss (Ψ : ℝ → ℝ) (X a : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE (zPsi Ψ a) \ Nat.primesLE (zPsi Ψ X), (p : ℝ)⁻¹

/-- A convenient common coefficient for the logarithmic and square-root
parts of the global loss. -/
def globalCutoffConstant (C : ℝ) : ℝ :=
  192 * C + 144

private theorem zPsi_eq_realEndpointCutoff (Ψ : ℝ → ℝ) (m : ℕ) :
    zPsi Ψ m = realEndpointCutoff Ψ (m : ℝ) := rfl

/-- Finite enclosure on `[X,3X]`, anchored at the actual natural cutoff at
`X`. -/
theorem global_cutoff_enclosure
    {Ψ dΨ : ℝ → ℝ} {C : ℝ} {X a : ℕ}
    (hX : 2 ≤ X) (ha : a ∈ Set.Icc X (3 * X)) (hC : 0 ≤ C)
    (hpos : ∀ t ∈ Set.Icc (Real.log (X : ℝ)) (Real.log (a : ℝ)), 0 < Ψ t)
    (hderiv : ∀ t ∈ Set.Icc (Real.log (X : ℝ)) (Real.log (a : ℝ)),
      HasDerivAt Ψ (dΨ t) t)
    (hweighted : ∀ t ∈ Set.Icc (Real.log (X : ℝ)) (Real.log (a : ℝ)),
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t)
    (hy : 2 ≤ zPsi Ψ X)
    (hlocal : C * 2 / Real.log (X : ℝ) ≤ 1 / 4) :
    zPsi Ψ X ≤ zPsi Ψ a ∧
      zPsi Ψ a ≤ powerBandUpper (zPsi Ψ X)
        (globalCutoffEps C X (zPsi Ψ X)) := by
  have hXone : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hX)
  have hXa : (X : ℝ) ≤ a := Nat.cast_le.mpr ha.1
  have hdiff : (a : ℝ) - (X : ℝ) ≤ 2 * (X : ℝ) := by
    have haUpper : (a : ℝ) ≤ 3 * (X : ℝ) := by exact_mod_cast ha.2
    linarith
  have hfloor := realEndpointCutoff_bounds
    (Ψ := Ψ) (dΨ := dΨ) (C := C) (δ := (2 : ℝ))
    hXone hXa (by norm_num) hdiff hC hlocal hpos hderiv hweighted
  let x := Real.exp (Ψ (Real.log (X : ℝ)))
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have heta0 : 0 ≤ globalCutoffEta C X := by
    unfold globalCutoffEta
    have hlog : 0 < Real.log (X : ℝ) := Real.log_pos hXone
    positivity
  have hetaHalf : globalCutoffEta C X ≤ 1 / 2 := by
    unfold globalCutoffEta
    have heq : 4 * C / Real.log (X : ℝ) =
        2 * (C * 2 / Real.log (X : ℝ)) := by ring
    rw [heq]
    nlinarith
  have hround := upper_floor_le_powerBandUpper (x := x)
    (η := globalCutoffEta C X) hx0
    (by simpa only [x, zPsi] using hy) heta0 (hetaHalf.trans (by norm_num))
  have hetaEq : globalCutoffEta C X =
      2 * (C * 2 / Real.log (X : ℝ)) := by
    unfold globalCutoffEta
    ring
  have hlower : zPsi Ψ X ≤ zPsi Ψ a := by
    simpa only [zPsi_eq_realEndpointCutoff] using hfloor.1
  have hupper : zPsi Ψ a ≤ ⌊x ^ (1 + globalCutoffEta C X)⌋₊ := by
    rw [hetaEq]
    simpa only [zPsi_eq_realEndpointCutoff, x] using hfloor.2
  exact ⟨hlower, hupper.trans (by
    simpa only [x, zPsi, globalCutoffEps] using hround)⟩

private theorem powerBandLower_le_anchor
    {y : ℕ} {ε : ℝ} (hy : 1 ≤ y) (hε : 0 ≤ ε) :
    powerBandLower y ε ≤ y := by
  unfold powerBandLower
  have hpow : (y : ℝ) ^ (1 - ε) ≤ (y : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hy) (by linarith)
  have hfloor := Nat.floor_le_floor hpow
  simpa only [Real.rpow_one, Nat.floor_natCast] using hfloor

/-- The literal new-prime interval is contained in any enclosing power
band based at its lower cutoff. -/
theorem cutoffPrimeReciprocalLoss_le_powerBand
    {Ψ : ℝ → ℝ} {X a : ℕ} {ε : ℝ}
    (hy : 1 ≤ zPsi Ψ X) (hε : 0 ≤ ε)
    (hupper : zPsi Ψ a ≤ powerBandUpper (zPsi Ψ X) ε) :
    cutoffPrimeReciprocalLoss Ψ X a ≤
      ∑ p ∈ powerPrimeBand (zPsi Ψ X) ε, (p : ℝ)⁻¹ := by
  have hlower := powerBandLower_le_anchor hy hε
  have hsub : Nat.primesLE (zPsi Ψ a) \ Nat.primesLE (zPsi Ψ X) ⊆
      powerPrimeBand (zPsi Ψ X) ε := by
    intro p hp
    have hpDiff := Finset.mem_sdiff.mp hp
    unfold powerPrimeBand
    apply Finset.mem_sdiff.mpr
    have hpData := Nat.mem_primesLE.mp hpDiff.1
    constructor
    · exact Nat.mem_primesLE.mpr ⟨hpData.1.trans hupper, hpData.2⟩
    · intro hpLower
      apply hpDiff.2
      have hpLowerData := Nat.mem_primesLE.mp hpLower
      exact Nat.mem_primesLE.mpr ⟨hpLowerData.1.trans hlower, hpData.2⟩
  unfold cutoffPrimeReciprocalLoss
  exact sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦
    inv_nonneg.mpr (Nat.cast_nonneg p))

/-- The eventual weighted derivative condition, in the literal form used
by the paper. -/
def HasEventuallyWeightedDerivative
    (Ψ dΨ : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ t : ℝ in atTop,
    0 < Ψ t ∧ HasDerivAt Ψ (dΨ t) t ∧
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t

/-- Uniform coarse-range cutoff enclosure and reciprocal prime loss.  The
constant depends only on the derivative constant `C`. -/
theorem eventually_global_cutoff_and_primeLoss
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : HasEventuallyWeightedDerivative Ψ dΨ C) :
    ∀ᶠ X : ℕ in atTop, ∀ a ∈ Set.Icc X (3 * X),
      zPsi Ψ X ≤ zPsi Ψ a ∧
        zPsi Ψ a ≤ powerBandUpper (zPsi Ψ X)
          (globalCutoffEps C X (zPsi Ψ X)) ∧
        cutoffPrimeReciprocalLoss Ψ X a ≤
          globalCutoffConstant C / Real.log (X : ℝ) +
            globalCutoffConstant C / Real.sqrt (zPsi Ψ X : ℝ) := by
  let ε₀ : ℝ := 1 / (64 * (C + 1))
  have hε₀ : 0 < ε₀ := by
    dsimp only [ε₀]
    positivity
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpsi : ∀ᶠ X : ℕ in atTop,
      Ψ (Real.log (X : ℝ)) ≤ ε₀ * Real.log (X : ℝ) :=
    hlog.eventually (eventually_psi_le_mul hSlope hε₀)
  rcases eventually_atTop.1 hreg with ⟨t₀, ht₀⟩
  have hband := hSlope.tendsto_zPsi_atTop.eventually
    eventually_powerPrimeBand_reciprocal_le
  filter_upwards [hpsi, hband, hSlope.tendsto_zPsi_atTop.eventually_ge_atTop 16,
    hlog.eventually_ge_atTop (max t₀ (max 1 (8 * C))),
    eventually_ge_atTop 3] with X hpsiX hbandX hy16 hlarge hX3
  intro a ha
  let y := zPsi Ψ X
  let lX := Real.log (X : ℝ)
  have hXone : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hX3)
  have hXpos : (0 : ℝ) < X := zero_lt_one.trans hXone
  have hlX : 0 < lX := by dsimp only [lX]; exact Real.log_pos hXone
  have hlogt₀ : t₀ ≤ lX := (le_max_left _ _).trans hlarge
  have hlX1 : 1 ≤ lX :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hlXC : 8 * C ≤ lX :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have haR : (X : ℝ) ≤ a := Nat.cast_le.mpr ha.1
  have hlogXa : lX ≤ Real.log (a : ℝ) := by
    dsimp only [lX]
    exact Real.log_le_log hXpos haR
  have hdata : ∀ t ∈ Icc lX (Real.log (a : ℝ)),
      0 < Ψ t ∧ HasDerivAt Ψ (dΨ t) t ∧
        0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t := by
    intro t ht
    exact ht₀ t (hlogt₀.trans ht.1)
  have hlocal : C * 2 / lX ≤ 1 / 4 := by
    apply (div_le_iff₀ hlX).2
    nlinarith
  have henc := global_cutoff_enclosure
    (Ψ := Ψ) (dΨ := dΨ) (C := C) (by omega : 2 ≤ X) ha hC
    (fun t ht ↦ (hdata t (by simpa only [lX] using ht)).1)
    (fun t ht ↦ (hdata t (by simpa only [lX] using ht)).2.1)
    (fun t ht ↦ (hdata t (by simpa only [lX] using ht)).2.2)
    (by omega : 2 ≤ zPsi Ψ X)
    (by simpa only [lX] using hlocal)
  have hlogy : Real.log (y : ℝ) ≤ Ψ lX := by
    dsimp only [y, lX]
    exact log_zPsi_le (by omega : 0 < zPsi Ψ X)
  have heta0 : 0 ≤ globalCutoffEta C X := by
    unfold globalCutoffEta
    positivity
  have hpsiX' : Ψ lX ≤ ε₀ * lX := by
    simpa only [lX] using hpsiX
  have hroundSmall : globalCutoffEta C X * Real.log (y : ℝ) ≤ 1 / 8 := by
    have hmul := mul_le_mul_of_nonneg_left (hlogy.trans hpsiX') heta0
    have hcancel : globalCutoffEta C X * (ε₀ * lX) = 4 * C * ε₀ := by
      unfold globalCutoffEta
      dsimp only [lX]
      field_simp [(Real.log_pos hXone).ne'] <;> ring
    rw [hcancel] at hmul
    have hconst : 4 * C * ε₀ ≤ 1 / 8 := by
      dsimp only [ε₀]
      have hden : 0 < 64 * (C + 1) := by positivity
      simp only [one_div]
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ hden).2
      nlinarith
    exact hmul.trans hconst
  have hadm := roundedBandWidth_admissible hy16 heta0 hroundSmall
  have hpower := hbandX (globalCutoffEps C X y) hadm.1 (by
    simpa only [globalCutoffEps] using hadm.2)
  have hlossPower := cutoffPrimeReciprocalLoss_le_powerBand
    (Ψ := Ψ) (X := X) (a := a) (ε := globalCutoffEps C X y)
    (by omega : 1 ≤ zPsi Ψ X) hadm.1 (by
      simpa only [y] using henc.2)
  have hloss : cutoffPrimeReciprocalLoss Ψ X a ≤
      48 * (globalCutoffEps C X y + 1 / Real.sqrt (y : ℝ)) :=
    hlossPower.trans hpower
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (by omega)
  have hlogyPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (by omega : 1 < y))
  have hsqrtPos : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.2 hypos
  have hsqrtLeY : Real.sqrt (y : ℝ) ≤ (y : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ y by omega)))
  have hroundTerm : 2 / ((y : ℝ) * Real.log (y : ℝ)) ≤
      2 / Real.sqrt (y : ℝ) := by
    have hlogOne : (1 : ℝ) ≤ Real.log (y : ℝ) := by
      apply (Real.le_log_iff_exp_le hypos).2
      exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ y by omega))
    have hden : Real.sqrt (y : ℝ) ≤ (y : ℝ) * Real.log (y : ℝ) :=
      hsqrtLeY.trans (le_mul_of_one_le_right hypos.le hlogOne)
    exact div_le_div_of_nonneg_left (by norm_num) hsqrtPos hden
  have hetaEq : globalCutoffEta C X = 4 * C / lX := by
    rfl
  have hexpanded : cutoffPrimeReciprocalLoss Ψ X a ≤
      192 * C / lX + 144 / Real.sqrt (y : ℝ) := by
    refine hloss.trans ?_
    unfold globalCutoffEps roundedBandWidth
    rw [hetaEq]
    have hscaled := mul_le_mul_of_nonneg_left hroundTerm (by norm_num : (0 : ℝ) ≤ 48)
    simp only [div_eq_mul_inv] at hscaled ⊢
    nlinarith
  have hK0 : 0 ≤ globalCutoffConstant C := by
    unfold globalCutoffConstant
    positivity
  have hfirst : 192 * C / lX ≤ globalCutoffConstant C / lX := by
    exact div_le_div_of_nonneg_right (by unfold globalCutoffConstant; linarith) hlX.le
  have hsecond : 144 / Real.sqrt (y : ℝ) ≤
      globalCutoffConstant C / Real.sqrt (y : ℝ) := by
    exact div_le_div_of_nonneg_right (by unfold globalCutoffConstant; linarith)
      hsqrtPos.le
  refine ⟨henc.1, henc.2, ?_⟩
  simpa only [y, lX] using hexpanded.trans (_root_.add_le_add hfirst hsecond)

end

end PrimeGapNormality.Prime.CoreRoughGlobalCutoff
