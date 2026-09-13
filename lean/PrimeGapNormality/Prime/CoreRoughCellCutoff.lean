import PrimeGapNormality.Prime.CoreRoughCutoffLocality
import PrimeGapNormality.Prime.CoreRoughRealAnchorBound
import PrimeGapNormality.Prime.CoreRoughThreshold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Literal moving cutoffs on one finite cell

The lower anchor is always the actual natural cutoff
`y = floor(exp(Ψ(log a)))`.  Its replacement inside the upper real power
is performed only through the explicit rounding theorem from
`CoreRoughRealAnchorBound`.
-/

namespace PrimeGapNormality.Prime.CoreRoughCellCutoff

open Set Filter Finset
open scoped Topology

open CoreRoughThreshold CoreRoughThresholdRegularity
  CoreRoughCutoffLocality CoreRoughRealAnchorBound CoreRoughPowerBand

noncomputable section

/-- Relative physical diameter of a cell together with its local window. -/
def cellDelta (a H S : ℕ) : ℝ :=
  ((H + S : ℕ) : ℝ) / (a : ℝ)

/-- Exponent loss after the finite derivative comparison. -/
def cellEta (C : ℝ) (a H S : ℕ) : ℝ :=
  2 * C * cellDelta a H S / Real.log (a : ℝ)

/-- Exponent loss after retaining the actual floored lower anchor. -/
def cellEpsRound (C : ℝ) (a H S y : ℕ) : ℝ :=
  roundedBandWidth y (cellEta C a H S)

private theorem zPsi_eq_realEndpointCutoff (Ψ : ℝ → ℝ) (m : ℕ) :
    zPsi Ψ m = realEndpointCutoff Ψ (m : ℝ) := rfl

private theorem cell_point_bounds
    {a H S n h : ℕ} (ha : 2 ≤ a) (hn : n ∈ Finset.Ico a (a + H))
    (hh : h ≤ S) :
    a ≤ n + h ∧ n + h ≤ a + H + S := by
  have hnI := Finset.mem_Ico.mp hn
  omega

/-- Every literal cutoff in the cell and its forward window is enclosed by
the actual lower anchor and the rounded power-band upper endpoint. -/
theorem cell_cutoff_enclosure
    {Ψ dΨ : ℝ → ℝ} {C : ℝ} {a H S n h : ℕ}
    (ha : 2 ≤ a) (hn : n ∈ Finset.Ico a (a + H)) (hh : h ≤ S)
    (hC : 0 ≤ C)
    (hpos : ∀ t ∈ Icc (Real.log (a : ℝ))
        (Real.log ((a + H + S : ℕ) : ℝ)), 0 < Ψ t)
    (hderiv : ∀ t ∈ Icc (Real.log (a : ℝ))
        (Real.log ((a + H + S : ℕ) : ℝ)), HasDerivAt Ψ (dΨ t) t)
    (hweighted : ∀ t ∈ Icc (Real.log (a : ℝ))
        (Real.log ((a + H + S : ℕ) : ℝ)),
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t)
    (hy : 2 ≤ zPsi Ψ a)
    (hlocal : C * cellDelta a H S / Real.log (a : ℝ) ≤ 1 / 4) :
    zPsi Ψ a ≤ zPsi Ψ (n + h) ∧
      zPsi Ψ (n + h) ≤
        powerBandUpper (zPsi Ψ a) (cellEpsRound C a H S (zPsi Ψ a)) := by
  have hpoint := cell_point_bounds ha hn hh
  have haR : (1 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) ha)
  have hbR : (a : ℝ) ≤ (n + h : ℕ) := Nat.cast_le.mpr hpoint.1
  have hbpos : (0 : ℝ) < (n + h : ℕ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < a) hpoint.1)
  have hendpos : (0 : ℝ) < (a + H + S : ℕ) := by positivity
  have hbEnd : (n + h : ℕ) ≤ a + H + S := hpoint.2
  have hlogbEnd : Real.log ((n + h : ℕ) : ℝ) ≤
      Real.log ((a + H + S : ℕ) : ℝ) :=
    Real.log_le_log hbpos (Nat.cast_le.mpr hbEnd)
  have hpos' : ∀ t ∈ Icc (Real.log (a : ℝ))
      (Real.log ((n + h : ℕ) : ℝ)), 0 < Ψ t := by
    intro t ht
    exact hpos t ⟨ht.1, ht.2.trans hlogbEnd⟩
  have hderiv' : ∀ t ∈ Icc (Real.log (a : ℝ))
      (Real.log ((n + h : ℕ) : ℝ)), HasDerivAt Ψ (dΨ t) t := by
    intro t ht
    exact hderiv t ⟨ht.1, ht.2.trans hlogbEnd⟩
  have hweighted' : ∀ t ∈ Icc (Real.log (a : ℝ))
      (Real.log ((n + h : ℕ) : ℝ)),
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t := by
    intro t ht
    exact hweighted t ⟨ht.1, ht.2.trans hlogbEnd⟩
  have haPos : (0 : ℝ) < a := zero_lt_one.trans haR
  have hdelta0 : 0 ≤ cellDelta a H S := by
    unfold cellDelta
    positivity
  have hdiffNat : n + h - a ≤ H + S := by omega
  have hdiff : ((n + h : ℕ) : ℝ) - (a : ℝ) ≤
      cellDelta a H S * (a : ℝ) := by
    have hcast : ((n + h - a : ℕ) : ℝ) ≤ (H + S : ℕ) :=
      Nat.cast_le.mpr hdiffNat
    rw [Nat.cast_sub hpoint.1] at hcast
    have hcancel : cellDelta a H S * (a : ℝ) = (H + S : ℕ) := by
      unfold cellDelta
      field_simp [haPos.ne']
    rwa [hcancel]
  have hlocalFloor := realEndpointCutoff_bounds haR hbR hdelta0 hdiff hC
    hlocal hpos' hderiv' hweighted'
  have heta0 : 0 ≤ cellEta C a H S := by
    unfold cellEta
    have hloga : 0 < Real.log (a : ℝ) := Real.log_pos haR
    positivity
  have hetaHalf : cellEta C a H S ≤ 1 / 2 := by
    calc
      cellEta C a H S = 2 * (C * cellDelta a H S / Real.log (a : ℝ)) := by
        unfold cellEta
        ring
      _ ≤ 1 / 2 := by linarith
  have hetaOne : cellEta C a H S ≤ 1 := hetaHalf.trans (by norm_num)
  have hetaEq : cellEta C a H S =
      2 * (C * cellDelta a H S / Real.log (a : ℝ)) := by
    unfold cellEta
    ring
  let x := Real.exp (Ψ (Real.log (a : ℝ)))
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hround := upper_floor_le_powerBandUpper (x := x)
    (η := cellEta C a H S) hx0 (by simpa only [x, zPsi] using hy)
    heta0 hetaOne
  have hlower : zPsi Ψ a ≤ zPsi Ψ (n + h) := by
    simpa only [zPsi_eq_realEndpointCutoff] using hlocalFloor.1
  have hupperLocal : zPsi Ψ (n + h) ≤
      ⌊x ^ (1 + cellEta C a H S)⌋₊ := by
    rw [hetaEq]
    simpa only [zPsi_eq_realEndpointCutoff, x] using hlocalFloor.2
  exact ⟨hlower, hupperLocal.trans (by
    simpa only [x, zPsi, cellEpsRound] using hround)⟩

/-- Eventual large-anchor cell package.  The eventual threshold comes only
from the proved reciprocal power-band estimate and is uniform in all cell
and derivative data. -/
theorem eventually_cell_cutoff_and_primeBand :
    ∀ᶠ y : ℕ in atTop,
      ∀ (Ψ dΨ : ℝ → ℝ) (C : ℝ) (a H S : ℕ),
      y = zPsi Ψ a → 2 ≤ a → 0 ≤ C →
      (∀ t ∈ Icc (Real.log (a : ℝ))
          (Real.log ((a + H + S : ℕ) : ℝ)), 0 < Ψ t) →
      (∀ t ∈ Icc (Real.log (a : ℝ))
          (Real.log ((a + H + S : ℕ) : ℝ)), HasDerivAt Ψ (dΨ t) t) →
      (∀ t ∈ Icc (Real.log (a : ℝ))
          (Real.log ((a + H + S : ℕ) : ℝ)),
        0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t) →
      C * cellDelta a H S / Real.log (a : ℝ) ≤ 1 / 4 →
      cellEta C a H S * Real.log (y : ℝ) ≤ 1 / 8 →
      (∀ n ∈ Finset.Ico a (a + H), ∀ h ≤ S,
        y ≤ zPsi Ψ (n + h) ∧
          zPsi Ψ (n + h) ≤ powerBandUpper y (cellEpsRound C a H S y)) ∧
        (∑ p ∈ powerPrimeBand y (cellEpsRound C a H S y), (p : ℝ)⁻¹) ≤
          48 * (cellEpsRound C a H S y + 1 / Real.sqrt (y : ℝ)) := by
  filter_upwards [eventually_powerPrimeBand_reciprocal_le,
    eventually_ge_atTop 16] with y hband hy16
  intro Ψ dΨ C a H S hyEq ha hC hpos hderiv hweighted hlocal hroundSmall
  have heta0 : 0 ≤ cellEta C a H S := by
    unfold cellEta cellDelta
    have haR : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
    have hloga : 0 < Real.log (a : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < a by omega))
    positivity
  have hadm := roundedBandWidth_admissible hy16 heta0 hroundSmall
  constructor
  · intro n hn h hh
    have hy2 : 2 ≤ zPsi Ψ a := by
      rw [← hyEq]
      omega
    have henc := cell_cutoff_enclosure ha hn hh hC hpos hderiv hweighted
      hy2 hlocal
    simpa only [hyEq, cellEpsRound] using henc
  · exact hband (cellEpsRound C a H S y) hadm.1 hadm.2

end

end PrimeGapNormality.Prime.CoreRoughCellCutoff
