import PrimeGapNormality.Prime.CardinalitySymMass
import PrimeGapNormality.Prime.CompleteFrameMass
import PrimeGapNormality.Prime.KuperbergAHL
import PrimeGapNormality.Prime.PrimeShortS
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic

/-!
# CRT-law HL-inclusion mismatch: compiled comparisons, remaining Tendsto

`PrimeShortS.HLMismatchVanishes` is weighted `|M_X/N_X - q_H|` on
profile layers `L ≤ j ≤ r`, with `q_H` the inclusion mass of the model.
This leaf instantiates the model by the actual finite CRT law

  `actualRootLaw (sieveCutoff X) (profileS κ X)`

on `windowOmega = {1,…,S_X}`. It does **not** declare a second
`crtCutoffMass`.

**Compiled.**
1. CRT law is a probability on `offsetWindow` / `windowOmega`
   (nonneg, sum `= 1`), re-proved from `ActualRootLaw` (not imported
   from `CrtMixtureTransfer`).
2. `Stopped.inclusionMass` of the CRT law is the residue-choice
   survival probability of `H`. It is `≤ 1`. On a late fibre,
   `H ⊆ A` implies inclusion `= lateInclusionFactor S y |H|`.
3. Odd offsets: CRT mass of every superset is `0` (`y ≥ 2`), and
   `insert 0 H` is HL-inadmissible, so `rootedMainTerm = 0`. Those
   layer terms of `hlModelMismatch` vanish.
4. Typical-count late fibres with mean in `[3L, 5L]`: exception
   mass and `failureMass` are `≤ 5/L` (`countBandException`). CRT
   `{N ≥ L}` mass is `≤ 1`, same type as
   `completeFrameOccupancyMass_le_one` but for `lateRootLaw`.
5. Off-band contribution to a *single* fibre inclusion mass is
   `≤ 5/L`, uniformly in `H`. `5 / profileL → 0`.
6. Exact inclusion calibration `q_H = M_X/N_X` implies
   `HLMismatchVanishes` (via `hlModelMismatch_eq_zero`).

**Not compiled.** `HLMismatchVanishes` itself at the CRT law.
Off-band mass `O(1/L)` does not close the *window* mismatch: the
definition sums `|M/N - q_H|` over every layer set `H`, and there is
no compiled comparison that this sum is supported on the exception
fibres. The remaining gap is typical-count
`|M_X(H)/N_X - q_H|` (truncated CRT Euler product versus the HL main
term). Do not fake that `Tendsto 0` from Chebyshev density: a typed
bound that stays `O(1)` is not a vanishing remainder. `G(X) = X` is
not the Kuperberg remainder scale.

Does not discharge `ConfigShapeDiscrepancy`, `MixtureSieveVanishing`,
Bernoulli `ModelRemainderVanishes` / `HLMismatchVanishes` on `ν`, or
`UniformOrbitTail`.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| CRT law nonnegative | theorem |
| CRT law sums to 1 | theorem |
| CRT inclusion = survival probability | theorem |
| CRT inclusion `≤ 1` | theorem |
| late inclusion = `lateInclusionFactor` | theorem |
| odd-`H` mismatch terms vanish | theorem |
| late `{N ≥ L}` mass `≤ 1` | theorem |
| late exception / failure mass `O(1/L)` on the mean band | theorem |
| off-band fibre inclusion `≤ 5/L` uniformly in `H` | theorem |
| `5 / profileL → 0` | theorem |
| `HLMismatchVanishes` from exact `M/N` calibration | theorem |
| `HLMismatchVanishes` at the CRT cutoff law | remaining hyp |

Source: `ActualRootLaw`; `CardinalitySymMass.lateRootLaw`,
`countBandException`, `actualRootLaw_eq_avg_lateRootLaw`;
`CompleteFrameMass.geLConfigs`; `StoppedAHL.hlModelMismatch`;
`PrimeShortS.HLMismatchVanishes`; `ProfileInequalities`.
Contract: API
Audit: GREEN
-/

open Finset Filter
open scoped Topology Classical

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

/-! ### Concrete CRT mass (not `crtCutoffMass`) -/

/-- Physical-scale CRT law at the least sieve cutoff of `X`. Named
apart from `crtCutoffMass`. -/
noncomputable abbrev sieveCutoffRootLaw (κ : ℝ) (X : ℕ) :
    Finset ℕ → ℝ :=
  actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X)

theorem crtHL_windowOmega_eq_offsetWindow (κ : ℝ) (X : ℕ) :
    windowOmega κ X = offsetWindow (profileS κ X) :=
  rfl

/-! ### Residue-choice cardinality -/

private theorem crtHL_residueChoice_card_pos (y : ℕ) :
    0 < Fintype.card (ResidueChoice y) :=
  Fintype.card_pos

private theorem crtHL_residueChoice_card_ne_zero (y : ℕ) :
    (Fintype.card (ResidueChoice y) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
    (crtHL_residueChoice_card_pos y))

private theorem crtHL_survivors_mem_powerset (y S : ℕ)
    (σ : ResidueChoice y) :
    sieveSurvivorsFin y σ S ∈ (offsetWindow S).powerset :=
  mem_powerset.mpr (filter_subset _ _)

/-! ### Probability of `actualRootLaw` -/

theorem crtHL_actualRootLaw_nonneg (y S : ℕ) (U : Finset ℕ) :
    0 ≤ actualRootLaw y S U :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem crtHL_sieveCutoffRootLaw_nonneg (κ : ℝ) (X : ℕ) (U : Finset ℕ) :
    0 ≤ sieveCutoffRootLaw κ X U :=
  crtHL_actualRootLaw_nonneg _ _ _

theorem crtHL_actualRootLaw_sum (y S : ℕ) :
    ∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U = 1 := by
  have hmaps : ∀ σ ∈ (univ : Finset (ResidueChoice y)),
      sieveSurvivorsFin y σ S ∈ (offsetWindow S).powerset :=
    fun σ _ => crtHL_survivors_mem_powerset y S σ
  have hcard :=
    card_eq_sum_card_fiberwise (s := univ)
      (t := (offsetWindow S).powerset)
      (f := fun σ => sieveSurvivorsFin y σ S) hmaps
  have hsum :
      ∑ U ∈ (offsetWindow S).powerset,
          (((univ : Finset (ResidueChoice y)).filter
              fun σ => sieveSurvivorsFin y σ S = U).card : ℝ) =
        (Fintype.card (ResidueChoice y) : ℝ) := by
    rw [← Nat.cast_sum, ← hcard, card_univ]
  unfold actualRootLaw
  rw [← sum_div, hsum]
  exact div_self (crtHL_residueChoice_card_ne_zero y)

/-- CRT cutoff law is a probability on the physical window. -/
theorem crtHL_sieveCutoffRootLaw_sum (κ : ℝ) (X : ℕ) :
    ∑ U ∈ (windowOmega κ X).powerset, sieveCutoffRootLaw κ X U = 1 := by
  rw [crtHL_windowOmega_eq_offsetWindow]
  exact crtHL_actualRootLaw_sum _ _

theorem crtHL_sieveCutoffRootLaw_nonneg_on_window (κ : ℝ) (X : ℕ) :
    ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ sieveCutoffRootLaw κ X U :=
  fun U _ => crtHL_sieveCutoffRootLaw_nonneg κ X U

/-! ### Inclusion mass of the CRT law -/

/-- Inclusion mass is the residue-choice probability that `H`
survives the finite sieve on `{1,…,S}`. -/
theorem crtHL_inclusionMass_eq_survivalProb (y S : ℕ) (H : Finset ℕ) :
    Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) H =
      (((univ : Finset (ResidueChoice y)).filter
          fun σ => H ⊆ sieveSurvivorsFin y σ S).card : ℝ) /
        (Fintype.card (ResidueChoice y) : ℝ) := by
  let t := (offsetWindow S).powerset.filter (fun U => H ⊆ U)
  let sSurv := (univ : Finset (ResidueChoice y)).filter
    fun σ => H ⊆ sieveSurvivorsFin y σ S
  have hmaps : ∀ σ ∈ sSurv,
      sieveSurvivorsFin y σ S ∈ t := by
    intro σ hσ
    have hsub : H ⊆ sieveSurvivorsFin y σ S := (mem_filter.mp hσ).2
    exact mem_filter.mpr ⟨crtHL_survivors_mem_powerset y S σ, hsub⟩
  have hfiber :=
    card_eq_sum_card_fiberwise (s := sSurv) (t := t)
      (f := fun σ => sieveSurvivorsFin y σ S) hmaps
  have hfib : ∀ U ∈ t,
      (sSurv.filter (fun σ => sieveSurvivorsFin y σ S = U)).card =
        ((univ : Finset (ResidueChoice y)).filter
            fun σ => sieveSurvivorsFin y σ S = U).card := by
    intro U hU
    have hH : H ⊆ U := (mem_filter.mp hU).2
    congr 1
    ext σ
    simp only [sSurv, mem_filter, mem_univ, true_and]
    constructor
    · intro h
      exact h.2
    · intro hUσ
      refine ⟨?_, hUσ⟩
      rwa [hUσ]
  have hsum :
      ∑ U ∈ t,
          (((univ : Finset (ResidueChoice y)).filter
              fun σ => sieveSurvivorsFin y σ S = U).card : ℝ) =
        (sSurv.card : ℝ) := by
    rw [← Nat.cast_sum]
    refine congrArg (Nat.cast : ℕ → ℝ) ?_
    have hswap :
        ∑ U ∈ t, ((univ : Finset (ResidueChoice y)).filter
            fun σ => sieveSurvivorsFin y σ S = U).card =
          ∑ U ∈ t, (sSurv.filter
              fun σ => sieveSurvivorsFin y σ S = U).card :=
      sum_congr rfl fun U hU => (hfib U hU).symm
    rw [hswap]
    exact hfiber.symm
  unfold Stopped.inclusionMass actualRootLaw
  rw [← sum_div, hsum]

theorem crtHL_inclusionMass_nonneg (y S : ℕ) (H : Finset ℕ) :
    0 ≤ Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) H :=
  sum_nonneg fun U _ => crtHL_actualRootLaw_nonneg y S U

theorem crtHL_inclusionMass_le_one (y S : ℕ) (H : Finset ℕ) :
    Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) H ≤ 1 := by
  have hsub :
      (offsetWindow S).powerset.filter (fun U => H ⊆ U) ⊆
        (offsetWindow S).powerset :=
    filter_subset _ _
  have hnn : ∀ U ∈ (offsetWindow S).powerset, 0 ≤ actualRootLaw y S U :=
    fun U _ => crtHL_actualRootLaw_nonneg y S U
  exact (sum_le_sum_of_subset_of_nonneg hsub fun U hU _ =>
      hnn U hU).trans_eq (crtHL_actualRootLaw_sum y S)

theorem crtHL_sieveCutoffRootLaw_inclusionMass_le_one
    (κ : ℝ) (X : ℕ) (H : Finset ℕ) :
    Stopped.inclusionMass (windowOmega κ X) (sieveCutoffRootLaw κ X) H ≤
      1 := by
  rw [crtHL_windowOmega_eq_offsetWindow]
  exact crtHL_inclusionMass_le_one _ _ _

/-! ### Late-fibre inclusion versus `lateInclusionFactor` -/

theorem crtHL_late_inclusionMass_eq_factor
    (S y : ℕ) {T : ℕ} {A H : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hH : H ⊆ A) :
    Stopped.inclusionMass A (lateRootLaw S y A) H =
      lateInclusionFactor S y H.card := by
  simpa [Stopped.inclusionMass, lateRootLaw] using
    lateProductMass_superset_sum S y hA hT hH

theorem crtHL_late_inclusionMass_eq_zero_of_not_subset
    {S y : ℕ} {A H : Finset ℕ} (hH : ¬ H ⊆ A) :
    Stopped.inclusionMass A (lateRootLaw S y A) H = 0 := by
  have hempty :
      A.powerset.filter (fun U => H ⊆ U) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro U hU
    have hUA : U ⊆ A := mem_powerset.mp (mem_filter.mp hU).1
    have hHU : H ⊆ U := (mem_filter.mp hU).2
    exact hH (hHU.trans hUA)
  unfold Stopped.inclusionMass
  rw [hempty, sum_empty]

/-- Average of late fibres recovers the global CRT law. Needs
`S_X ≤ y` (cutoff at least the window). -/
theorem crtHL_actualRootLaw_eq_avg_late
    {κ : ℝ} {X : ℕ} (hSy : profileS κ X ≤ sieveCutoff (X : ℝ))
    (U : Finset ℕ) :
    sieveCutoffRootLaw κ X U =
      (∑ σ : ResidueChoice (profileS κ X),
          lateRootLaw (profileS κ X) (sieveCutoff (X : ℝ))
            (lateCandidateSet (profileS κ X) (profileS κ X) σ) U) /
        (Fintype.card (ResidueChoice (profileS κ X)) : ℝ) :=
  actualRootLaw_eq_avg_lateRootLaw (profileS κ X)
    (sieveCutoff (X : ℝ)) (profileS κ X) le_rfl hSy U

/-! ### Odd offsets: both sides of the mismatch vanish -/

private theorem crtHL_zmod_two_of_odd {n : ℕ} (hodd : Odd n) :
    (n : ZMod 2) = 1 :=
  (ZMod.natCast_eq_natCast_iff' n 1 2).mpr
    ((Nat.odd_iff.mp hodd).trans (rfl : 1 = 1 % 2))

theorem crtHL_not_hlAdmissible_of_odd_mem {H : Finset ℕ} {n : ℕ}
    (hn : n ∈ H) (hodd : Odd n) : ¬ hlAdmissible (insert 0 H) := by
  intro hadm
  have h2 := hadm 2 Nat.prime_two
  have h0 : (0 : ZMod 2) ∈
      (insert 0 H).image (fun h : ℕ => (h : ZMod 2)) :=
    mem_image.mpr ⟨0, mem_insert_self 0 H, Nat.cast_zero⟩
  have h1 : (1 : ZMod 2) ∈
      (insert 0 H).image (fun h : ℕ => (h : ZMod 2)) :=
    mem_image.mpr ⟨n, mem_insert_of_mem hn, crtHL_zmod_two_of_odd hodd⟩
  have hsub : ({(0 : ZMod 2), 1} : Finset (ZMod 2)) ⊆
      (insert 0 H).image (fun h : ℕ => (h : ZMod 2)) := by
    intro x hx
    have hx' : x = 0 ∨ x = 1 := by
      simpa [mem_insert, mem_singleton] using hx
    rcases hx' with rfl | rfl
    · exact h0
    · exact h1
  have hcard : ({(0 : ZMod 2), 1} : Finset (ZMod 2)).card = 2 :=
    card_pair zero_ne_one
  have hle : 2 ≤ residueCount (insert 0 H) 2 := by
    unfold residueCount
    exact hcard.symm.trans_le (card_le_card hsub)
  exact (not_lt.mpr hle) h2

theorem crtHL_inclusionMass_eq_zero_of_odd_mem
    {y S n : ℕ} {H : Finset ℕ}
    (hy : 2 ≤ y) (hnH : n ∈ H) (hodd : Odd n) :
    Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) H = 0 := by
  unfold Stopped.inclusionMass
  refine sum_eq_zero fun U hU => ?_
  have hnU : n ∈ U := (mem_filter.mp hU).2 hnH
  exact actualRootLaw_eq_zero_of_odd_mem hy hnU hodd

/-- On any odd offset the HL main term and the CRT inclusion both vanish,
so that layer summand of `hlModelMismatch` is `0`. -/
theorem crtHL_mismatch_term_eq_zero_of_odd_mem
    {κ : ℝ} {X n : ℕ} {H : Finset ℕ}
    (hnH : n ∈ H) (hodd : Odd n) :
    |rootedMainTerm X H / (windowNX X : ℝ) -
      Stopped.inclusionMass (windowOmega κ X)
        (sieveCutoffRootLaw κ X) H| = 0 := by
  have hy : 2 ≤ sieveCutoff (X : ℝ) := sieveCutoff_ge_two _
  have hq :
      Stopped.inclusionMass (windowOmega κ X) (sieveCutoffRootLaw κ X) H =
        0 := by
    rw [crtHL_windowOmega_eq_offsetWindow]
    exact crtHL_inclusionMass_eq_zero_of_odd_mem hy hnH hodd
  have hM : rootedMainTerm X H = 0 :=
    rootedMainTerm_eq_zero_of_not_hlAdmissible
      (crtHL_not_hlAdmissible_of_odd_mem hnH hodd)
  rw [hM, hq, zero_div, sub_self, abs_zero]

/-! ### Late `{N ≥ L}` mass and Chebyshev band -/

/-- CRT `{N ≥ L}` mass is at most `1`. Same type as
`completeFrameOccupancyMass_le_one`, for `lateRootLaw` rather than
Bernoulli occupancy weights. -/
theorem crtHL_late_geL_mass_le_one (S y : ℕ) (A : Finset ℕ) (L : ℕ) :
    ∑ E ∈ geLConfigs A L, lateRootLaw S y A E ≤ 1 := by
  have hsub : geLConfigs A L ⊆ A.powerset := filter_subset _ _
  have hnn : ∀ E ∈ A.powerset, 0 ≤ lateRootLaw S y A E :=
    fun E _ => lateProductMass_nonneg S y A E
  exact (sum_le_sum_of_subset_of_nonneg hsub fun E hE _ =>
      hnn E hE).trans_eq (lateProductMass_sum S y A)

/-- Off-band mass `O(1/L)` on a late fibre whose mean count lies in
`[3L, 5L]`. Not `Tendsto 0` of the window mismatch. -/
theorem crtHL_late_exceptionMass_le_of_meanBand
    (S y T L : ℕ) (hT : T ≤ S) (hL : 0 < L) (σ : ResidueChoice S)
    (hlo : (3 : ℝ) * L ≤
      ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y)
    (hhi : ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ≤
      (5 : ℝ) * L) :
    ∑ E ∈ (lateCandidateSet S T σ).powerset.filter
        (fun E => E.card < 2 * L ∨ 6 * L < E.card),
      lateRootLaw S y (lateCandidateSet S T σ) E ≤
      (5 : ℝ) / (L : ℝ) :=
  (countBandException S y T L hT) hL σ hlo hhi

/-- `failureMass` (`|E| < L`) is contained in the low-count half of the
Chebyshev band, hence `O(1/L)` on the same mean-band fibres. -/
theorem crtHL_late_failureMass_le_of_meanBand
    (S y : ℕ) {T : ℕ} {A : Finset ℕ} {L : ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hSy : S ≤ y) (hL : 0 < L)
    (hlo : (3 : ℝ) * L ≤ (A.card : ℝ) * lateRetention S y)
    (hhi : (A.card : ℝ) * lateRetention S y ≤ (5 : ℝ) * L) :
    Stopped.failureMass A (lateRootLaw S y A) L ≤ (5 : ℝ) / (L : ℝ) := by
  have hμ := lateRootLaw_cardinalitySymmetric S y hA hT hSy
  have hMom := exactCountMoments_lateRootLaw S y hA hT hSy
  have hband :=
    countBand_of_second_moment (A := A) (μ := lateRootLaw S y A)
      (S := S) (y := y) (L := L) (C := (5 : ℝ)) hμ hMom hL hlo hhi hhi
  have hsub :
      A.powerset.filter (fun U => U.card < L) ⊆
        A.powerset.filter
          (fun E => E.card < 2 * L ∨ 6 * L < E.card) := by
    intro U hU
    have hU' := mem_filter.mp hU
    refine mem_filter.mpr ⟨hU'.1, Or.inl ?_⟩
    have h2 : L ≤ 2 * L := by omega
    exact Nat.lt_of_lt_of_le hU'.2 h2
  have hnn : ∀ E ∈ A.powerset, 0 ≤ lateRootLaw S y A E := hμ.1
  unfold Stopped.failureMass
  refine (sum_le_sum_of_subset_of_nonneg hsub ?_).trans hband
  intro E hE _
  exact hnn E (mem_filter.mp hE).1

/-- Off-band contribution to a *single* fibre inclusion mass is
`≤ 5/L`, uniformly in `H`. Summing over all layer sets `H` is not
compiled from this comparison. -/
theorem crtHL_late_inclusion_exception_le_of_meanBand
    (S y T L : ℕ) {H : Finset ℕ} (hT : T ≤ S) (hL : 0 < L)
    (σ : ResidueChoice S)
    (hlo : (3 : ℝ) * L ≤
      ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y)
    (hhi : ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ≤
      (5 : ℝ) * L) :
    ∑ E ∈ (lateCandidateSet S T σ).powerset.filter
        (fun E => (E.card < 2 * L ∨ 6 * L < E.card) ∧ H ⊆ E),
      lateRootLaw S y (lateCandidateSet S T σ) E ≤
      (5 : ℝ) / (L : ℝ) := by
  set A := lateCandidateSet S T σ
  have hband :=
    crtHL_late_exceptionMass_le_of_meanBand S y T L hT hL σ hlo hhi
  have hsub :
      A.powerset.filter
          (fun E => (E.card < 2 * L ∨ 6 * L < E.card) ∧ H ⊆ E) ⊆
        A.powerset.filter
          (fun E => E.card < 2 * L ∨ 6 * L < E.card) := by
    intro E hE
    have hE' := mem_filter.mp hE
    exact mem_filter.mpr ⟨hE'.1, hE'.2.1⟩
  have hnn : ∀ E ∈ A.powerset, 0 ≤ lateRootLaw S y A E :=
    fun E _ => lateProductMass_nonneg S y A E
  exact (sum_le_sum_of_subset_of_nonneg hsub fun E hE _ =>
      hnn E (mem_filter.mp hE).1).trans hband

/-! ### Profile length: `5/L → 0` is not the window mismatch -/

private theorem crtHL_tendsto_windowG : Tendsto windowG atTop atTop :=
  tendsto_atTop_mono
    (fun X => le_max_left (Real.log (X : ℝ)) (1 : ℝ))
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem crtHL_tendsto_log_windowG :
    Tendsto (fun X : ℕ => Real.log (windowG X)) atTop atTop :=
  Real.tendsto_log_atTop.comp crtHL_tendsto_windowG

theorem crtHL_tendsto_profileL {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ => profileL κ X) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun N => ?_
  have hmul :
      Tendsto (fun X : ℕ => κ * Real.log (windowG X)) atTop atTop := by
    simpa [mul_comm] using crtHL_tendsto_log_windowG.atTop_mul_const' hκ
  obtain ⟨X0, hX0⟩ := tendsto_atTop_atTop.mp hmul (N : ℝ)
  refine ⟨X0, fun X hX => ?_⟩
  have hle : (N : ℝ) ≤ κ * Real.log (windowG X) := hX0 X hX
  exact Nat.cast_le.mp
    (hle.trans (kappa_log_windowG_le_profileL (le_of_lt hκ) X))

/-- Fibrewise Chebyshev scale vanishes. This is **not**
`hlModelMismatch → 0`: the typed window sum is not known to be
`O(1/L)`. -/
theorem crtHL_tendsto_five_div_profileL {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ => (5 : ℝ) / (profileL κ X : ℝ))
      atTop (nhds 0) :=
  (tendsto_const_div_atTop_nhds_zero_nat (5 : ℝ)).comp
    (crtHL_tendsto_profileL hκ)

/-! ### Nonnegativity of the weighted mismatch -/

theorem crtHL_hlModelMismatch_nonneg (κ d0 : ℝ) (X : ℕ) :
    0 ≤ hlModelMismatch κ X (sieveCutoffRootLaw κ X)
      (profileL κ X) (profileR (profileL κ X) d0) :=
  hlModelMismatch_nonneg κ X (sieveCutoffRootLaw κ X) _ _

/-! ### Exact inclusion calibration implies vanishing mismatch -/

/-- If CRT inclusion masses match the HL main term on the window, the
weighted mismatch is identically zero. -/
theorem crtHL_hlModelMismatch_eq_zero_of_calibrated
    {κ : ℝ} {X L r : ℕ} (hN : 0 < windowNX X)
    (hq : ∀ H ∈ (windowOmega κ X).powerset,
      Stopped.inclusionMass (windowOmega κ X) (sieveCutoffRootLaw κ X) H =
        rootedMainTerm X H / (windowNX X : ℝ)) :
    hlModelMismatch κ X (sieveCutoffRootLaw κ X) L r = 0 := by
  -- Explicit `ν` so Lean does not `whnf` `inclusionMass` / `hlModelMismatch`
  -- in order to infer the model from `hq`.
  apply hlModelMismatch_eq_zero (κ := κ) (X := X) (L := L) (r := r)
    (ν := sieveCutoffRootLaw κ X)
  · exact hN
  · exact hq

/-- The remaining analytic gap, packaged: eventual exact calibration
of CRT inclusion against `M_X/N_X` yields `HLMismatchVanishes`. -/
theorem crtHL_HLMismatchVanishes_of_calibrated {κ d0 : ℝ}
    (hN : ∀ᶠ X : ℕ in atTop, 0 < windowNX X)
    (hq : ∀ᶠ X : ℕ in atTop,
      ∀ H ∈ (windowOmega κ X).powerset,
        Stopped.inclusionMass (windowOmega κ X)
          (sieveCutoffRootLaw κ X) H =
          rootedMainTerm X H / (windowNX X : ℝ)) :
    HLMismatchVanishes κ d0 (fun X => sieveCutoffRootLaw κ X) := by
  have heq :
      (fun X : ℕ =>
          hlModelMismatch κ X (sieveCutoffRootLaw κ X)
            (profileL κ X) (profileR (profileL κ X) d0)) =ᶠ[atTop]
        fun _ => (0 : ℝ) := by
    filter_upwards [hN, hq] with X hN' hq'
    exact crtHL_hlModelMismatch_eq_zero_of_calibrated hN' hq'
  exact Tendsto.congr' heq.symm tendsto_const_nhds

/-! ### Remaining hypothesis: window `Tendsto 0` -/

/-- Named remaining obligation. Not an axiom. Typical-count
`|M_X/N_X - q_H|` on profile layers is not compiled; the fibrewise
`O(1/L)` band does not supply a support lemma for the full weighted
`H`-sum. -/
def HLMismatchVanishes_sieveCutoffRootLaw (κ d0 : ℝ) : Prop :=
  HLMismatchVanishes κ d0 (fun X => sieveCutoffRootLaw κ X)

theorem crtHL_HLMismatchVanishes_iff (κ d0 : ℝ) :
    HLMismatchVanishes_sieveCutoffRootLaw κ d0 ↔
      HLMismatchVanishes κ d0 (fun X => sieveCutoffRootLaw κ X) :=
  Iff.rfl

end

end PrimeGapNormality.Prime
