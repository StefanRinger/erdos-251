import PrimeGapNormality.Prime.CoreRoughCellCutoff
import PrimeGapNormality.Prime.CoreRoughProfileError
import PrimeGapNormality.Prime.CoreRoughSmallWindow
import PrimeGapNormality.Prime.CoreRoughSubpower
import PrimeGapNormality.Prime.CoreRoughSieveBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Asymptotic data for derivative-controlled rough cells

For a fixed natural exponent `J`, the physical cell length is

`Delta_J(X) = floor (X / (log X)^J)`.

The paper's small synthetic profile is smaller than the literal cutoff,
and the slope budget makes that cutoff at most `X^(1/2)` eventually.
Consequently the whole local shift fits inside `Delta_J(X)`, without using
the additive sieve envelope.  This file also restricts the paper's eventual
weighted derivative hypothesis uniformly to every cell based in `[X,2X]`
and records the resulting explicit cell and rounded power-band errors.

No cutoff-continuity, prime-density, or short-interval hypothesis is added.
-/

namespace PrimeGapNormality.Prime.CoreRoughCellAsymptotics

open Filter Set
open scoped Topology

open CoreRoughThreshold CoreRoughSubpower CoreRoughProfileError
  CoreRoughSmallWindow CoreRoughCellCutoff CoreRoughRealAnchorBound
  CoreRoughSieveBudget CoreRoughThresholdRegularity

noncomputable section

/-- The paper's physical cell length with a fixed logarithmic exponent. -/
def roughCellLength (J X : ℕ) : ℕ :=
  ⌊(X : ℝ) / Real.log (X : ℝ) ^ J⌋₊

/-- The forward profile shift at the literal moving rough cutoff. -/
def roughCellShift (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) : ℕ :=
  roughProfileS κ (zPsi Ψ X)

/-- Literal eventual form of the paper's positive weighted `C¹` condition. -/
def HasEventuallyWeightedDerivative
    (Ψ dΨ : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ t : ℝ in atTop,
    0 < Ψ t ∧ HasDerivAt Ψ (dΨ t) t ∧
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t

private theorem eventually_log_pow_le_half_rpow (J : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ^ J ≤ (X : ℝ) ^ (1 / 2 : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ J ≤ x ^ (1 / 2 : ℝ) := by
    have hnorm :=
      (isLittleO_log_rpow_rpow_atTop (J : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).eventuallyLE
    filter_upwards [hnorm, eventually_gt_atTop (1 : ℝ)] with x hxnorm hx1
    have hlog0 : 0 ≤ Real.log x := (Real.log_pos hx1).le
    have hx0 : 0 < x := zero_lt_one.trans hx1
    have hnum : 0 ≤ Real.log x ^ (J : ℝ) :=
      Real.rpow_nonneg hlog0 _
    have hden : 0 ≤ x ^ (1 / 2 : ℝ) :=
      (Real.rpow_pos_of_pos hx0 _).le
    have hle : Real.log x ^ (J : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
      rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnum,
        abs_of_nonneg hden] at hxnorm
    simpa only [Real.rpow_natCast] using hle
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal

/-- For every fixed logarithmic cell exponent, the actual synthetic profile
shift fits into the physical cell eventually.  The proof uses only
`S < zPsi(X) ≤ X^(1/2)` and logarithms being smaller than powers. -/
theorem eventually_roughCellShift_le_roughCellLength
    {κ A : ℝ} {Ψ : ℝ → ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ A) (J : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      roughCellShift κ Ψ X ≤ roughCellLength J X := by
  have hsmall := hSlope.tendsto_zPsi_atTop.eventually
    (eventually_ahlSmall_window_roughSyntheticScale_lt hκ)
  have hcut := eventually_zPsi_le_rpow hSlope
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hsmall, hcut, eventually_log_pow_le_half_rpow J,
    eventually_ge_atTop 3] with X hsmallX hcutX hlogPow hX3
  have hXpos : (0 : ℝ) < X :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 3) hX3)
  have hlogPos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr
      (lt_of_lt_of_le (by norm_num : 1 < 3) hX3))
  have hlogPowPos : 0 < Real.log (X : ℝ) ^ J :=
    pow_pos hlogPos J
  have hshiftCut : roughCellShift κ Ψ X ≤ zPsi Ψ X := by
    exact hsmallX.le
  have hshiftRoot : (roughCellShift κ Ψ X : ℝ) ≤
      (X : ℝ) ^ (1 / 2 : ℝ) := by
    exact (Nat.cast_le.mpr hshiftCut).trans hcutX
  have hroot0 : 0 ≤ (X : ℝ) ^ (1 / 2 : ℝ) :=
    (Real.rpow_pos_of_pos hXpos _).le
  have hrootSq :
      (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) = (X : ℝ) := by
    rw [← Real.rpow_add hXpos]
    norm_num
  have hrootDiv : (X : ℝ) ^ (1 / 2 : ℝ) ≤
      (X : ℝ) / Real.log (X : ℝ) ^ J := by
    apply (le_div_iff₀ hlogPowPos).2
    calc
      (X : ℝ) ^ (1 / 2 : ℝ) * Real.log (X : ℝ) ^ J ≤
          (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogPow hroot0
      _ = (X : ℝ) := hrootSq
  unfold roughCellLength
  apply Nat.le_floor
  exact hshiftRoot.trans hrootDiv

/-- A finite cell-diameter estimate.  If the forward shift is no larger
than the cell itself, its relative diameter is at most
`3 / (log X)^J` (the proof in fact has constant `2`). -/
theorem cellDelta_roughCellLength_le
    {J X a S : ℕ} (hX : 3 ≤ X) (ha : X ≤ a)
    (hS : S ≤ roughCellLength J X) :
    cellDelta a (roughCellLength J X) S ≤
      3 / Real.log (X : ℝ) ^ J := by
  let l := Real.log (X : ℝ)
  let P := l ^ J
  let H := roughCellLength J X
  have hXpos : (0 : ℝ) < X :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 3) hX)
  have haPos : (0 : ℝ) < a :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < X) ha)
  have hlPos : 0 < l := by
    dsimp only [l]
    exact Real.log_pos (Nat.one_lt_cast.mpr
      (lt_of_lt_of_le (by norm_num : 1 < 3) hX))
  have hPPos : 0 < P := by
    dsimp only [P]
    exact pow_pos hlPos J
  have hH : (H : ℝ) ≤ (X : ℝ) / P := by
    dsimp only [H, roughCellLength, P, l]
    exact Nat.floor_le (div_nonneg hXpos.le (pow_nonneg hlPos.le J))
  have hScast : (S : ℝ) ≤ H := Nat.cast_le.mpr hS
  have hnum : ((H + S : ℕ) : ℝ) ≤ 2 * ((X : ℝ) / P) := by
    norm_num only [Nat.cast_add]
    linarith
  have hXa : (X : ℝ) / P ≤ (a : ℝ) / P :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr ha) hPPos.le
  unfold cellDelta
  dsimp only [H] at hnum
  apply (div_le_iff₀ haPos).2
  have htarget : 2 * ((X : ℝ) / P) ≤ (3 / P) * (a : ℝ) := by
    have htwo : 2 * ((X : ℝ) / P) ≤ 2 * ((a : ℝ) / P) :=
      mul_le_mul_of_nonneg_left hXa (by norm_num)
    have haDiv0 : 0 ≤ (a : ℝ) / P := div_nonneg (Nat.cast_nonneg a) hPPos.le
    calc
      2 * ((X : ℝ) / P) ≤ 2 * ((a : ℝ) / P) := htwo
      _ ≤ 3 * ((a : ℝ) / P) := by linarith
      _ = (3 / P) * (a : ℝ) := by ring
  simpa only [P, l] using hnum.trans htarget

/-- Uniform relative-diameter bound for all cell starts in `[X,2X]`. -/
theorem eventually_cellDelta_roughCell_le
    {κ A : ℝ} {Ψ : ℝ → ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ A) (J : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ a ∈ Icc X (2 * X),
      cellDelta a (roughCellLength J X) (roughCellShift κ Ψ X) ≤
        3 / Real.log (X : ℝ) ^ J := by
  filter_upwards [eventually_roughCellShift_le_roughCellLength hκ hSlope J,
    eventually_ge_atTop 3] with X hshift hX
  intro a ha
  exact cellDelta_roughCellLength_le hX ha.1 hshift

/-- An eventual weighted derivative hypothesis holds uniformly on every
cell interval whose lower endpoint is based in `[X,2X]`. -/
theorem eventually_weightedDerivative_on_roughCells
    {Ψ dΨ : ℝ → ℝ} {C : ℝ}
    (hreg : HasEventuallyWeightedDerivative Ψ dΨ C) :
    ∀ᶠ X : ℕ in atTop, ∀ a H S : ℕ, X ≤ a →
      ∀ t ∈ Icc (Real.log (a : ℝ))
          (Real.log ((a + H + S : ℕ) : ℝ)),
        0 < Ψ t ∧ HasDerivAt Ψ (dΨ t) t ∧
          0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t := by
  rcases eventually_atTop.1 hreg with ⟨t₀, ht₀⟩
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlog.eventually_ge_atTop t₀, eventually_ge_atTop 1]
      with X hlogX hX
  intro a H S hXa t ht
  have hXpos : (0 : ℝ) < X :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 1) hX)
  have hlogXa : Real.log (X : ℝ) ≤ Real.log (a : ℝ) :=
    Real.log_le_log hXpos (Nat.cast_le.mpr hXa)
  exact ht₀ t (hlogX.trans (hlogXa.trans ht.1))

/-- On starts `a ∈ [X,2X]`, the derivative condition changes the profile
by at most a factor two eventually. -/
theorem eventually_psi_log_cellStart_le_two
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : HasEventuallyWeightedDerivative Ψ dΨ C) :
    ∀ᶠ X : ℕ in atTop, ∀ a ∈ Icc X (2 * X),
      Ψ (Real.log (a : ℝ)) ≤ 2 * Ψ (Real.log (X : ℝ)) := by
  rcases eventually_atTop.1 hreg with ⟨t₀, ht₀⟩
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [hlog.eventually_ge_atTop (max t₀ (max 1 (C / Real.log 2))),
    eventually_ge_atTop 3] with X hlarge hX
  intro a ha
  have hlogXt₀ : t₀ ≤ Real.log (X : ℝ) :=
    (le_max_left _ _).trans hlarge
  have hlogX1 : 1 ≤ Real.log (X : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hlogXC : C / Real.log 2 ≤ Real.log (X : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hXone : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hX)
  have hXpos : (0 : ℝ) < X := zero_lt_one.trans hXone
  have haR : (X : ℝ) ≤ a := Nat.cast_le.mpr ha.1
  have hlogXa : Real.log (X : ℝ) ≤ Real.log (a : ℝ) :=
    Real.log_le_log hXpos haR
  have hdata : ∀ t ∈ Icc (Real.log (X : ℝ)) (Real.log (a : ℝ)),
      0 < Ψ t ∧ HasDerivAt Ψ (dΨ t) t ∧
        0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t := by
    intro t ht
    exact ht₀ t (hlogXt₀.trans ht.1)
  have hdiff : (a : ℝ) - (X : ℝ) ≤ 1 * (X : ℝ) := by
    have haUpper : (a : ℝ) ≤ 2 * (X : ℝ) := by
      exact_mod_cast ha.2
    linarith
  have hcmp := CoreRoughCutoffLocality.psi_log_interval_comparison
    (Ψ := Ψ) (dΨ := dΨ) (C := C) (δ := (1 : ℝ))
    hXone haR (by norm_num) hdiff hC
    (fun t ht ↦ (hdata t ht).1)
    (fun t ht ↦ (hdata t ht).2.1)
    (fun t ht ↦ (hdata t ht).2.2)
  have hCLog : C / Real.log (X : ℝ) ≤ Real.log 2 := by
    have hmul : C ≤ Real.log (X : ℝ) * Real.log 2 :=
      (div_le_iff₀ hlogTwo).mp hlogXC
    exact (div_le_iff₀ (by linarith : 0 < Real.log (X : ℝ))).2 (by
      simpa only [mul_comm] using hmul)
  have hexp : Real.exp (C * 1 / Real.log (X : ℝ)) ≤ 2 := by
    calc
      Real.exp (C * 1 / Real.log (X : ℝ)) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr (by simpa only [mul_one] using hCLog)
      _ = 2 := Real.exp_log (by norm_num)
  have hΨX : 0 ≤ Ψ (Real.log (X : ℝ)) :=
    ((hdata _ ⟨le_rfl, hlogXa⟩).1).le
  calc
    Ψ (Real.log (a : ℝ)) ≤
        Ψ (Real.log (X : ℝ)) *
          Real.exp (C * 1 / Real.log (X : ℝ)) := hcmp.2
    _ ≤ Ψ (Real.log (X : ℝ)) * 2 :=
      mul_le_mul_of_nonneg_left hexp hΨX
    _ = 2 * Ψ (Real.log (X : ℝ)) := by ring

/-- Explicit rounded-band error resulting from the uniform cell-diameter
bound.  The coefficient `6*C` is independent of the cell start. -/
theorem cellEpsRound_le
    {C : ℝ} {J X a H S y : ℕ}
    (hC : 0 ≤ C) (hX : 3 ≤ X) (ha : X ≤ a)
    (hdelta : cellDelta a H S ≤ 3 / Real.log (X : ℝ) ^ J) :
    cellEpsRound C a H S y ≤
      6 * C / Real.log (X : ℝ) ^ (J + 1) +
        2 / ((y : ℝ) * Real.log (y : ℝ)) := by
  let lX := Real.log (X : ℝ)
  let la := Real.log (a : ℝ)
  let P := lX ^ J
  have hXpos : (0 : ℝ) < X :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 3) hX)
  have hlX : 0 < lX := by
    dsimp only [lX]
    exact Real.log_pos (Nat.one_lt_cast.mpr
      (lt_of_lt_of_le (by norm_num : 1 < 3) hX))
  have hla : 0 < la := by
    dsimp only [la]
    exact Real.log_pos (lt_of_lt_of_le
      (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : 1 < 3) hX))
      (Nat.cast_le.mpr ha))
  have hlogLe : lX ≤ la := by
    dsimp only [lX, la]
    exact Real.log_le_log hXpos (Nat.cast_le.mpr ha)
  have hP : 0 < P := by dsimp only [P]; exact pow_pos hlX J
  have hnum : 2 * C * cellDelta a H S ≤ 6 * C / P := by
    have hmul := mul_le_mul_of_nonneg_left hdelta
      (show (0 : ℝ) ≤ 2 * C by positivity)
    calc
      2 * C * cellDelta a H S ≤ (2 * C) * (3 / Real.log (X : ℝ) ^ J) := hmul
      _ = 6 * C / P := by dsimp only [P, lX]; ring
  have hnum0 : 0 ≤ 6 * C / P := div_nonneg (by positivity) hP.le
  have heta : cellEta C a H S ≤ 6 * C / (lX ^ (J + 1)) := by
    calc
      cellEta C a H S = (2 * C * cellDelta a H S) / la := by
        unfold cellEta
        rfl
      _ ≤ (6 * C / P) / la :=
        div_le_div_of_nonneg_right hnum hla.le
      _ ≤ (6 * C / P) / lX :=
        div_le_div_of_nonneg_left hnum0 hlX hlogLe
      _ = 6 * C / (lX ^ (J + 1)) := by
        dsimp only [P]
        rw [pow_succ]
        field_simp [hlX.ne']
  unfold cellEpsRound roundedBandWidth
  exact _root_.add_le_add heta le_rfl

/-- Eventual uniform rounded-band error on the paper cells. -/
theorem eventually_cellEpsRound_le
    {κ A C : ℝ} {Ψ : ℝ → ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C) (J : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ a ∈ Icc X (2 * X), ∀ y : ℕ,
      cellEpsRound C a (roughCellLength J X) (roughCellShift κ Ψ X) y ≤
        6 * C / Real.log (X : ℝ) ^ (J + 1) +
          2 / ((y : ℝ) * Real.log (y : ℝ)) := by
  filter_upwards [eventually_cellDelta_roughCell_le hκ hSlope J,
    eventually_ge_atTop 3] with X hdelta hX
  intro a ha y
  exact cellEpsRound_le hC hX ha.1 (hdelta a ha)

end

end PrimeGapNormality.Prime.CoreRoughCellAsymptotics
