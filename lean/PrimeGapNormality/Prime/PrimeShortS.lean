import PrimeGapNormality.Prime.CouplingDisc
import PrimeGapNormality.Prime.ModelShortPattern
import PrimeGapNormality.Prime.PrimeSTD
import PrimeGapNormality.Prime.ProfileInequalities
import PrimeGapNormality.Prime.SieveCutoffCal
import PrimeGapNormality.Prime.StoppedAHL
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic

/-!
# S-link: AHL plus named remainders to short-pattern window averages

Paper (eq:S) on `nthPrime`. StoppedAHL makes first-`L` shape L¹ of
`actualConfigMass` small. ModelShortPattern compares Bernoulli product
means to rooted-sieve means. This file identifies genuine prime-window
averages of **first-`L` tests** with those empirical config means, then
closes the triangle to the Dirac cutoff mixture.

Calibration `V(y)⁻¹ / G → 1` is discharged with `SieveCutoffCal` at
`G = windowG` and `y = sieveCutoff X`. Remaining named `Prop`s (not
axioms): model remainder (including model failure mass), HL-inclusion
mismatch, config-versus-Bernoulli L¹, and rooted-sieve versus Bernoulli.

Does **not** claim `ShortPatternS nthPrime`. That definition quantifies
over every span-truncated `F : (ℕ → ℕ) → ℂ`, including tests that read
offsets `k > L`. Stopped L¹ only sees first-`L` shapes on `windowOmega`.
The isolated remaining lemma is recorded at the end.

Source: `StatisticalCriterion.ShortPatternS`; `StoppedAHL`;
  `ModelShortPattern`; `CouplingDisc.ShapeDiscrepancy`; `EndAPI.AHL`;
  `SieveCutoffCal`; paper (eq:S), `lem:stopped`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Filter Polynomial
open scoped Topology

set_option maxHeartbeats 800000

noncomputable section

/-! ### Profile identification `stdProfile` ↔ EndAPI `profile` -/

/-- Clock `κ = 1 / log ρ` matching `log_ρ G = κ log G`. -/
noncomputable def stdKappa (ρ : ℝ) : ℝ :=
  (Real.log ρ)⁻¹

theorem stdKappa_pos {ρ : ℝ} (hρ : 1 < ρ) : 0 < stdKappa ρ :=
  inv_pos.mpr (Real.log_pos hρ)

theorem logρ_eq_stdKappa_mul {ρ G : ℝ} (hρ : 1 < ρ) :
    logρ ρ G = stdKappa ρ * Real.log G := by
  unfold logρ stdKappa
  exact div_eq_inv_mul _ _

theorem profileL_eq_stdProfileL {ρ : ℝ} (hρ : 1 < ρ) (X : ℕ) :
    profileL (stdKappa ρ) X = stdProfileL ρ (windowG X) := by
  unfold profileL stdProfileL
  rw [logρ_eq_stdKappa_mul hρ]

theorem profileS_eq_floor_stdProfileS {ρ : ℝ} (hρ : 1 < ρ) (X : ℕ) :
    profileS (stdKappa ρ) X = ⌊stdProfileS ρ (windowG X)⌋₊ := by
  unfold profileS stdProfileS
  rw [profileL_eq_stdProfileL hρ]

private theorem one_lt_log_of_three_le {X : ℕ} (hX : 3 ≤ X) :
    1 < Real.log (X : ℝ) := by
  have hpos : 0 < (X : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 3) hX)
  have : Real.exp 1 < (X : ℝ) :=
    Real.exp_one_lt_three.trans_le (Nat.cast_le.mpr hX)
  exact (Real.lt_log_iff_exp_lt hpos).mpr this

private theorem windowG_eq_log {X : ℕ} (hX : 3 ≤ X) :
    windowG X = Real.log (X : ℝ) :=
  max_eq_left (one_lt_log_of_three_le hX).le

theorem eventually_one_le_stdProfileL {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop, 1 ≤ stdProfileL ρ (windowG X) := by
  have h := eventually_one_le_profileL (stdKappa_pos hρ)
  refine h.mono fun X hX => ?_
  rwa [← profileL_eq_stdProfileL hρ]

theorem eventually_windowNX_pos :
    ∀ᶠ X : ℕ in atTop, 0 < windowNX X := by
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hpos : 0 < X := Nat.succ_le_iff.mp hX
  rw [← seqWindow_nthPrime_card]
  exact card_seqWindow_nthPrime_pos hpos

/-! ### First-`L` tests -/

/-- `F` is a function of the first `L` rooted offsets only. -/
def DependsOnFirstL (L : ℕ) (F : (ℕ → ℕ) → ℂ) : Prop :=
  ∀ v w : ℕ → ℕ, (∀ k : ℕ, k ≤ L → v k = w k) → F v = F w

theorem truncatedPhaseTest_dependsOnFirstL (P : ℝ[X]) (B L : ℕ) (τ : ℤ) :
    DependsOnFirstL L (truncatedPhaseTest P B L τ) := by
  intro v w hvw
  unfold truncatedPhaseTest
  have hsum :
      ∑ j ∈ range L,
          eval ((v (j + 1) - v j : ℕ) : ℝ) P / (B : ℝ) ^ (j + 1) =
        ∑ j ∈ range L,
          eval ((w (j + 1) - w j : ℕ) : ℝ) P / (B : ℝ) ^ (j + 1) := by
    refine sum_congr rfl fun j hj => ?_
    have hjL : j < L := mem_range.mp hj
    have hj1 : j + 1 ≤ L := Nat.succ_le_of_lt hjL
    rw [hvw j (Nat.le_of_lt hjL), hvw (j + 1) hj1]
  rw [hsum]

theorem DependsOnFirstL_spanCut {L : ℕ} {S : ℝ} {F : (ℕ → ℕ) → ℂ}
    (h : DependsOnFirstL L F) :
    DependsOnFirstL L (spanCut L S F) := by
  intro v w hvw
  unfold PrimeGapNormality.Prime.spanCut
  have hL : v L = w L := hvw L le_rfl
  split_ifs with hv hw
  · rfl
  · exact (hw (by rwa [← hL])).elim
  · exact (hv (by rwa [hL])).elim
  · exact h v w hvw

theorem truncatedPhaseTestCut_dependsOnFirstL (P : ℝ[X]) (B L : ℕ)
    (S : ℝ) (τ : ℤ) :
    DependsOnFirstL L (truncatedPhaseTestCut P B L S τ) := by
  intro v w hvw
  unfold truncatedPhaseTestCut
  have hL : v L = w L := hvw L le_rfl
  split_ifs with hv hw
  · rfl
  · exact (hw (by rwa [← hL])).elim
  · exact (hv (by rwa [hL])).elim
  · exact truncatedPhaseTest_dependsOnFirstL P B L τ v w hvw

/-! ### Dirac cutoff mixture and discharged calibration -/

theorem sieveCutoff_ge_two (t : ℝ) : 2 ≤ sieveCutoff t := by
  by_cases ht : 1 < t
  · exact (sieveCutoff_spec ht).1.two_le
  · simp [sieveCutoff, ht]

/-- One-point mixture at a sieve level `y ≥ 2`. -/
noncomputable def diracSieveMixture (y : ℕ) (hy : 2 ≤ y) : SieveMixture where
  support := {y}
  weight := fun z => if z = y then 1 else 0
  support_nonempty := singleton_nonempty y
  support_ge_two := by
    intro z hz
    have : z = y := mem_singleton.mp hz
    exact this ▸ hy
  weight_nonneg := by
    intro z hz
    have : z = y := mem_singleton.mp hz
    simp [this]
  weight_sum := by
    simp

/-- Least cutoff of the physical scale `X`, as a mixture. -/
noncomputable def cutoffMixture (X : ℕ) : SieveMixture :=
  diracSieveMixture (sieveCutoff (X : ℝ)) (sieveCutoff_ge_two _)

theorem mixtureMean_dirac (y : ℕ) (hy : 2 ≤ y) (μ : ℕ → ℂ) :
    mixtureMean (diracSieveMixture y hy) μ = μ y := by
  unfold mixtureMean diracSieveMixture
  simp [sum_singleton]

theorem mixtureMean_cutoff (X : ℕ) (μ : ℕ → ℂ) :
    mixtureMean (cutoffMixture X) μ = μ (sieveCutoff (X : ℝ)) :=
  mixtureMean_dirac _ _ _

theorem mixtureCalib_dirac (y : ℕ) (hy : 2 ≤ y) (G : ℝ) :
    mixtureCalib (diracSieveMixture y hy) G =
      |(eulerProd (y : ℝ))⁻¹ / G - 1| := by
  unfold mixtureCalib diracSieveMixture
  rw [sup'_singleton]

theorem mixtureCalib_cutoff (X : ℕ) :
    mixtureCalib (cutoffMixture X) (windowG X) =
      |(eulerProd (sieveCutoff (X : ℝ) : ℝ))⁻¹ / windowG X - 1| :=
  mixtureCalib_dirac _ _ _

/-- Paper calibration at `G = windowG` and the least sieve cutoff of `X`. -/
theorem tendsto_cutoffMixture_calib :
    Tendsto (fun X : ℕ => mixtureCalib (cutoffMixture X) (windowG X))
      atTop (nhds 0) := by
  have hreal := tendsto_sieveCutoff_inv_div_log.comp
    tendsto_natCast_atTop_atTop
  have hdist :
      Tendsto (fun X : ℕ =>
        |(eulerProd (sieveCutoff (X : ℝ)))⁻¹ / Real.log (X : ℝ) - 1|)
        atTop (nhds 0) := by
    rw [tendsto_iff_dist_tendsto_zero] at hreal
    exact hreal.congr fun X => Real.dist_eq _ _
  have heq :
      (fun X : ℕ => mixtureCalib (cutoffMixture X) (windowG X)) =ᶠ[atTop]
        fun X =>
          |(eulerProd (sieveCutoff (X : ℝ)))⁻¹ / Real.log (X : ℝ) - 1| := by
    filter_upwards [eventually_ge_atTop 3] with X hX
    rw [mixtureCalib_cutoff, windowG_eq_log hX]
  exact Tendsto.congr' heq.symm hdist

/-! ### Named remaining obligations (not axioms) -/

/-- Model-side smallness used by StoppedAHL: `ν` is a probability,
failure mass of fewer than `L` points vanishes, and the Bonferroni
remainder vanishes. -/
def ModelRemainderVanishes (κ d0 : ℝ) (ν : ℕ → Finset ℕ → ℝ) : Prop :=
  (∀ᶠ X : ℕ in atTop,
      ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν X U) ∧
    (∀ᶠ X : ℕ in atTop,
      ∑ U ∈ (windowOmega κ X).powerset, ν X U = 1) ∧
      Tendsto (fun X : ℕ =>
          Stopped.failureMass (windowOmega κ X) (ν X) (profileL κ X))
        atTop (nhds 0) ∧
        Tendsto (fun X : ℕ =>
            Stopped.modelRemainder (windowOmega κ X) (ν X)
              (profileL κ X) (profileR (profileL κ X) d0))
          atTop (nhds 0)

/-- Weighted `|M_X/N_X - q_H|` remainder on the profile layers. -/
def HLMismatchVanishes (κ d0 : ℝ) (ν : ℕ → Finset ℕ → ℝ) : Prop :=
  Tendsto (fun X : ℕ =>
      hlModelMismatch κ X (ν X) (profileL κ X)
        (profileR (profileL κ X) d0))
    atTop (nhds 0)

/-- Config-mass L¹ against independent Bernoulli thinning. This is
`ShapeDiscrepancy` in the limit. -/
def ConfigShapeDiscrepancy (κ : ℝ) (ν : ℕ → Finset ℕ → ℝ)
    (ret : ℕ → ℝ) : Prop :=
  (∀ᶠ X : ℕ in atTop, 0 ≤ ret X ∧ ret X ≤ 1) ∧
    Tendsto (fun X : ℕ =>
        massL1 (windowOmega κ X).powerset (ν X)
          (bernoulliConfigMass (windowOmega κ X) (ret X)))
      atTop (nhds 0)

/-- Rooted sieve at the cutoff versus Bernoulli, uniformly in admissible
short-pattern tests. -/
def MixtureSieveVanishing (κ ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
    RootedSieveVsBernoulli (sieveCutoff (X : ℝ)) (windowOmega κ X)
      (eulerProdNat (sieveCutoff (X : ℝ)))
      (stdProfileL ρ (windowG X)) (stdProfileS ρ (windowG X)) ε

theorem configShapeDiscrepancy_of_bernoulli (κ : ℝ) {ret : ℕ → ℝ}
    (hret : ∀ᶠ X : ℕ in atTop, 0 ≤ ret X ∧ ret X ≤ 1) :
    ConfigShapeDiscrepancy κ
      (fun X => bernoulliConfigMass (windowOmega κ X) (ret X)) ret := by
  refine ⟨hret, ?_⟩
  have h0 : (fun X : ℕ =>
      massL1 (windowOmega κ X).powerset
        (bernoulliConfigMass (windowOmega κ X) (ret X))
        (bernoulliConfigMass (windowOmega κ X) (ret X))) =
      fun _ => (0 : ℝ) := by
    funext X
    exact massL1_self _ _
  simpa [h0] using tendsto_const_nhds

private theorem eulerProdNat_nonneg (n : ℕ) : 0 ≤ eulerProdNat n :=
  (eulerProdNat_pos n).le

private theorem eulerProdNat_le_one (n : ℕ) : eulerProdNat n ≤ 1 := by
  have h0 : eulerProdNat 0 = 1 := by
    rw [eulerProdNat, Nat.primesLE_zero, prod_empty]
  exact (eulerProdNat_mono (Nat.zero_le n)).trans_eq h0

theorem cutoff_retention_bounds (X : ℕ) :
    0 ≤ eulerProdNat (sieveCutoff (X : ℝ)) ∧
      eulerProdNat (sieveCutoff (X : ℝ)) ≤ 1 :=
  ⟨eulerProdNat_nonneg _, eulerProdNat_le_one _⟩

/-! ### Rooted offsets of a genuine prime -/

theorem seqOffset_strictMono (n : ℕ) :
    StrictMono (seqOffset nthPrime n) := by
  intro a b hab
  unfold seqOffset
  have hlt : nthPrime (n + a) < nthPrime (n + b) :=
    nthPrime_strictMono (Nat.add_lt_add_left hab n)
  have hle : nthPrime n ≤ nthPrime (n + a) :=
    nthPrime_mono (Nat.le_add_right n a)
  exact Nat.sub_lt_sub_right hle hlt

theorem seqOffset_mono (n : ℕ) : Monotone (seqOffset nthPrime n) :=
  (seqOffset_strictMono n).monotone

theorem seqOffset_ge_self (n k : ℕ) : k ≤ seqOffset nthPrime n k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hle0 : nthPrime n ≤ nthPrime (n + k) :=
      nthPrime_mono (Nat.le_add_right n k)
    have hlt : nthPrime (n + k) < nthPrime (n + k + 1) :=
      nthPrime_strictMono (Nat.lt_succ_self _)
    have hsplit :
        nthPrime (n + k + 1) - nthPrime n =
          (nthPrime (n + k + 1) - nthPrime (n + k)) +
            (nthPrime (n + k) - nthPrime n) :=
      (Nat.sub_add_sub_cancel (Nat.le_of_lt hlt) hle0).symm
    have hgap : 1 ≤ nthPrime (n + k + 1) - nthPrime (n + k) :=
      Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt)
    unfold seqOffset at ih ⊢
    rw [← Nat.add_assoc n k 1]
    have hsum := Nat.add_le_add hgap ih
    rw [Nat.add_comm 1 k] at hsum
    rw [hsplit]
    exact hsum

theorem nthPrime_primeCounting' {q : ℕ} (hq : Nat.Prime q) :
    nthPrime (Nat.primeCounting' q) = q := by
  simpa [nthPrime, Nat.primeCounting'] using Nat.nth_count hq

theorem seqOffset_mem_rootedPattern {κ : ℝ} {X n k : ℕ}
    (hk : 1 ≤ k) (hle : seqOffset nthPrime n k ≤ profileS κ X) :
    seqOffset nthPrime n k ∈ rootedPattern κ X (nthPrime n) := by
  have hlt : nthPrime n < nthPrime (n + k) :=
    nthPrime_strictMono (Nat.lt_add_of_pos_right hk)
  have h1 : 1 ≤ seqOffset nthPrime n k :=
    Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt)
  have hΩ : seqOffset nthPrime n k ∈ windowOmega κ X :=
    mem_Icc.mpr ⟨h1, hle⟩
  have hle' : nthPrime n ≤ nthPrime (n + k) :=
    nthPrime_mono (Nat.le_add_right n k)
  refine mem_filter.mpr ⟨hΩ, ?_⟩
  unfold seqOffset
  rw [Nat.add_sub_cancel' hle']
  exact prime_nthPrime (n + k)

theorem exists_rank_of_mem_rootedPattern {κ : ℝ} {X n : ℕ} {h : ℕ}
    (hh : h ∈ rootedPattern κ X (nthPrime n)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ profileS κ X ∧ seqOffset nthPrime n k = h := by
  have hmem := mem_filter.mp hh
  have hIcc := mem_Icc.mp hmem.1
  have hp : Nat.Prime (nthPrime n + h) := hmem.2
  set q := nthPrime n + h with hqdef
  have hq : nthPrime (Nat.primeCounting' q) = q :=
    nthPrime_primeCounting' hp
  have hltp : nthPrime n < q := Nat.lt_add_of_pos_right hIcc.1
  have hltn : n < Nat.primeCounting' q :=
    (nthPrime_strictMono.lt_iff_lt).mp (by rwa [hq])
  have hseq :
      seqOffset nthPrime n (Nat.primeCounting' q - n) = h := by
    unfold seqOffset
    rw [Nat.add_sub_of_le hltn.le, hq, hqdef, Nat.add_sub_cancel_left]
  refine ⟨Nat.primeCounting' q - n, Nat.sub_pos_of_lt hltn, ?_, hseq⟩
  have hge : Nat.primeCounting' q - n ≤ h := by
    rw [← hseq]
    exact seqOffset_ge_self n _
  exact hge.trans hIcc.2

/-- Ranks `k` whose `k`-th prime offset still lies in `Ω_X`. -/
noncomputable def survivingRanks (κ : ℝ) (X n : ℕ) : Finset ℕ :=
  (Icc 1 (profileS κ X)).filter
    (fun k => seqOffset nthPrime n k ≤ profileS κ X)

theorem survivingRanks_image (κ : ℝ) (X n : ℕ) :
    (survivingRanks κ X n).image (seqOffset nthPrime n) =
      rootedPattern κ X (nthPrime n) := by
  ext h
  constructor
  · intro hh
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hh
    have hkf := mem_filter.mp hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hkf.1).1
    exact seqOffset_mem_rootedPattern hk1 hkf.2
  · intro hh
    obtain ⟨k, hk1, hkS, hseq⟩ := exists_rank_of_mem_rootedPattern hh
    refine mem_image.mpr ⟨k, ?_, hseq⟩
    have hkIcc : k ∈ Icc 1 (profileS κ X) := mem_Icc.mpr ⟨hk1, hkS⟩
    have hle : seqOffset nthPrime n k ≤ profileS κ X := by
      rw [hseq]
      exact (mem_Icc.mp (mem_filter.mp hh).1).2
    exact mem_filter.mpr ⟨hkIcc, hle⟩

theorem survivingRanks_card (κ : ℝ) (X n : ℕ) :
    (survivingRanks κ X n).card =
      (rootedPattern κ X (nthPrime n)).card := by
  rw [← survivingRanks_image κ X n]
  refine (card_image_of_injOn ?_).symm
  intro a _ b _ h
  exact (seqOffset_strictMono n).injective h

theorem survivingRanks_eq_Icc {κ : ℝ} {X n : ℕ}
    (hs : (survivingRanks κ X n).Nonempty) :
    survivingRanks κ X n =
      Icc (1 : ℕ) ((survivingRanks κ X n).max' hs) := by
  let s := survivingRanks κ X n
  let M := s.max' hs
  ext k
  constructor
  · intro hk
    have hIcc := mem_Icc.mp (mem_filter.mp hk).1
    exact mem_Icc.mpr ⟨hIcc.1, s.le_max' k hk⟩
  · intro hk
    have ⟨hk1, hkM⟩ := mem_Icc.mp hk
    have hMmem := s.max'_mem hs
    have hMf := mem_filter.mp hMmem
    have hMS : seqOffset nthPrime n M ≤ profileS κ X := hMf.2
    have hle : seqOffset nthPrime n k ≤ seqOffset nthPrime n M :=
      (seqOffset_mono n) hkM
    have hkS : seqOffset nthPrime n k ≤ profileS κ X := hle.trans hMS
    have hMIcc := mem_Icc.mp hMf.1
    have hkIcc : k ∈ Icc 1 (profileS κ X) :=
      mem_Icc.mpr ⟨hk1, hkM.trans hMIcc.2⟩
    exact mem_filter.mpr ⟨hkIcc, hkS⟩

theorem survivingRanks_card_eq_max {κ : ℝ} {X n : ℕ}
    (hs : (survivingRanks κ X n).Nonempty) :
    (survivingRanks κ X n).card = (survivingRanks κ X n).max' hs := by
  have hIcc := survivingRanks_eq_Icc hs
  have hcard := congrArg Finset.card hIcc
  rw [Nat.card_Icc] at hcard
  simpa [Nat.add_sub_cancel] using hcard

theorem seqOffset_mem_of_le_card {κ : ℝ} {X n k : ℕ}
    (hk : 1 ≤ k) (hkU : k ≤ (rootedPattern κ X (nthPrime n)).card) :
    seqOffset nthPrime n k ∈ rootedPattern κ X (nthPrime n) := by
  let U := rootedPattern κ X (nthPrime n)
  let s := survivingRanks κ X n
  have hcard : s.card = U.card := survivingRanks_card κ X n
  have hs : s.Nonempty := by
    rw [← one_le_card, hcard]
    exact hk.trans hkU
  have hIcc : s = Icc (1 : ℕ) (s.max' hs) := survivingRanks_eq_Icc hs
  have hmax : s.card = s.max' hs := survivingRanks_card_eq_max hs
  have hkM : k ≤ s.max' hs := by
    rw [← hmax, hcard]
    exact hkU
  have hks : k ∈ s := by
    rw [hIcc]
    exact mem_Icc.mpr ⟨hk, hkM⟩
  have himg := survivingRanks_image κ X n
  exact himg ▸ mem_image.mpr ⟨k, hks, rfl⟩

theorem seqOffset_le_profileS_of_le_card {κ : ℝ} {X n k : ℕ}
    (hk : 1 ≤ k) (hkU : k ≤ (rootedPattern κ X (nthPrime n)).card) :
    seqOffset nthPrime n k ≤ profileS κ X :=
  (mem_Icc.mp (mem_filter.mp (seqOffset_mem_of_le_card hk hkU)).1).2

theorem seqOffset_eq_orderEmb {κ : ℝ} {X n : ℕ}
    (_hU : 0 < (rootedPattern κ X (nthPrime n)).card) :
    (fun i : Fin (rootedPattern κ X (nthPrime n)).card =>
        seqOffset nthPrime n (i.val + 1)) =
      orderEmbOfFin (rootedPattern κ X (nthPrime n)) rfl := by
  let U := rootedPattern κ X (nthPrime n)
  let M := U.card
  let f : Fin M → ℕ := fun i => seqOffset nthPrime n (i.val + 1)
  have hfs : ∀ i : Fin M, f i ∈ U := by
    intro i
    have hk : 1 ≤ i.val + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hkU : i.val + 1 ≤ M := Nat.succ_le_of_lt i.2
    exact seqOffset_mem_of_le_card hk hkU
  have hmono : StrictMono f := by
    intro i j hij
    exact seqOffset_strictMono n (Nat.succ_lt_succ hij)
  exact orderEmbOfFin_unique rfl hfs hmono

theorem configOffset_eq_seqOffset {κ : ℝ} {X n k : ℕ} {S : ℝ}
    (hk : 1 ≤ k)
    (hkU : k ≤ (rootedPattern κ X (nthPrime n)).card) :
    configOffset (rootedPattern κ X (nthPrime n)) S k =
      seqOffset nthPrime n k := by
  let U := rootedPattern κ X (nthPrime n)
  have hpos : 0 < U.card := lt_of_lt_of_le hk hkU
  rw [configOffset_of_le_card hk hkU]
  have hfin : k - 1 < U.card :=
    Nat.lt_of_succ_le (by
      simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hk] using
        (hkU : k ≤ U.card))
  have hks : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hfun :
      seqOffset nthPrime n k = orderEmbOfFin U rfl ⟨k - 1, hfin⟩ := by
    simpa [hks] using
      congrFun (seqOffset_eq_orderEmb (κ := κ) (X := X) (n := n) hpos)
        ⟨k - 1, hfin⟩
  have hget :
      (U.sort (· ≤ ·))[k - 1]'(by simp [length_sort]; exact hfin) =
        orderEmbOfFin U rfl ⟨k - 1, hfin⟩ := by
    rw [orderEmbOfFin_apply]
    simp [Fin.getElem_fin]
  exact hget.trans hfun.symm

/-! ### Span cut matches missing `L`-th window point -/

theorem stdProfileS_nonneg (ρ : ℝ) (X : ℕ) :
    0 ≤ stdProfileS ρ (windowG X) := by
  unfold stdProfileS
  exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg _))
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _))

theorem lt_stdProfileS_iff_profileS {ρ : ℝ} (hρ : 1 < ρ) (X vL : ℕ) :
    stdProfileS ρ (windowG X) < (vL : ℝ) ↔
      profileS (stdKappa ρ) X < vL := by
  have hS : 0 ≤ stdProfileS ρ (windowG X) := stdProfileS_nonneg ρ X
  rw [profileS_eq_floor_stdProfileS hρ X]
  exact (Nat.floor_lt hS).symm

theorem seqOffset_zero (n : ℕ) : seqOffset nthPrime n 0 = 0 := by
  simp [seqOffset]

theorem le_card_iff_seqOffset_le {κ : ℝ} {X n L : ℕ} :
    L ≤ (rootedPattern κ X (nthPrime n)).card ↔
      seqOffset nthPrime n L ≤ profileS κ X := by
  constructor
  · intro hcard
    by_cases hL : L = 0
    · subst hL
      rw [seqOffset_zero]
      exact Nat.zero_le _
    · have hk : 1 ≤ L := Nat.pos_of_ne_zero hL
      exact seqOffset_le_profileS_of_le_card hk hcard
  · intro hle
    by_cases hL : L = 0
    · subst hL
      exact Nat.zero_le _
    · have hk : 1 ≤ L := Nat.pos_of_ne_zero hL
      have hIcc : L ∈ Icc 1 (profileS κ X) :=
        mem_Icc.mpr ⟨hk, (seqOffset_ge_self n L).trans hle⟩
      have hmem : L ∈ survivingRanks κ X n := mem_filter.mpr ⟨hIcc, hle⟩
      have hs : (survivingRanks κ X n).Nonempty := ⟨L, hmem⟩
      have hmax : L ≤ (survivingRanks κ X n).max' hs :=
        (survivingRanks κ X n).le_max' L hmem
      have hcard :
          (survivingRanks κ X n).card = (survivingRanks κ X n).max' hs :=
        survivingRanks_card_eq_max hs
      rw [← survivingRanks_card κ X n, hcard]
      exact hmax

theorem firstL_sort_eq {L : ℕ} {U : Finset ℕ} (_h : L ≤ U.card) :
    (Stopped.firstL L U).sort (· ≤ ·) = (U.sort (· ≤ ·)).take L := by
  have hnd :
      ((U.sort (· ≤ ·)).take L).Nodup :=
    (U.sort_nodup (· ≤ ·)).sublist (List.take_sublist L _)
  have hpw : ((U.sort (· ≤ ·)).take L).Pairwise (· ≤ ·) :=
    (pairwise_sort U (· ≤ ·)).take
  exact (List.toFinset_sort (· ≤ ·) hnd).mpr hpw

theorem configOffset_firstL {U : Finset ℕ} {S : ℝ} {L k : ℕ}
    (hLcard : L ≤ U.card) (hk : 1 ≤ k) (hkL : k ≤ L) :
    configOffset (Stopped.firstL L U) S k = configOffset U S k := by
  have hKcard : (Stopped.firstL L U).card = L := Stopped.firstL_card hLcard
  have hkK : k ≤ (Stopped.firstL L U).card := by rwa [hKcard]
  have hkU : k ≤ U.card := hkL.trans hLcard
  have hk1 : k - 1 < L :=
    Nat.lt_of_succ_le (by
      simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hk] using hkL)
  rw [configOffset_of_le_card hk hkK, configOffset_of_le_card hk hkU]
  have hsort := firstL_sort_eq hLcard
  have hlenTake : ((U.sort (· ≤ ·)).take L).length = L := by
    rw [List.length_take, length_sort, min_eq_left hLcard]
  have hgetK :
      ((Stopped.firstL L U).sort (· ≤ ·))[k - 1]'(by
          simp [length_sort, hKcard]; exact hk1) =
        ((U.sort (· ≤ ·)).take L)[k - 1]'(by
          rw [hlenTake]; exact hk1) := by
    simp [hsort]
  have hgetU :
      ((U.sort (· ≤ ·)).take L)[k - 1]'(by rw [hlenTake]; exact hk1) =
        (U.sort (· ≤ ·))[k - 1]'(by
          simp [length_sort]
          exact Nat.lt_of_lt_of_le hk1 hLcard) :=
    List.getElem_take
  exact hgetK.trans hgetU

theorem configOffset_eq_firstL_offsets {U : Finset ℕ} {S : ℝ} {L : ℕ}
    (hLcard : L ≤ U.card) :
    ∀ k, k ≤ L →
      configOffset U S k = configOffset (Stopped.firstL L U) S k := by
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simp [configOffset_zero]
  · exact (configOffset_firstL hLcard (Nat.pos_of_ne_zero hk0) hk).symm

theorem F_eq_of_dependsOnFirstL {U : Finset ℕ} {S : ℝ} {L : ℕ}
    {F : (ℕ → ℕ) → ℂ} (hDep : DependsOnFirstL L F) (hLcard : L ≤ U.card) :
    F (configOffset U S) =
      F (configOffset (Stopped.firstL L U) S) :=
  hDep _ _ (configOffset_eq_firstL_offsets hLcard)

theorem F_seqOffset_eq_configOffset {ρ : ℝ} {X n : ℕ} {F : (ℕ → ℕ) → ℂ}
    (hρ : 1 < ρ) (hL : 1 ≤ stdProfileL ρ (windowG X))
    (hF : IsAdmissibleShortPattern (stdProfileL ρ (windowG X))
      (stdProfileS ρ (windowG X)) F)
    (hDep : DependsOnFirstL (stdProfileL ρ (windowG X)) F) :
    F (seqOffset nthPrime n) =
      F (configOffset (rootedPattern (stdKappa ρ) X (nthPrime n))
          (stdProfileS ρ (windowG X))) := by
  set L := stdProfileL ρ (windowG X)
  set S := stdProfileS ρ (windowG X)
  set U := rootedPattern (stdKappa ρ) X (nthPrime n)
  by_cases hcard : L ≤ U.card
  · exact hDep _ _ fun k hk => by
      by_cases hk0 : k = 0
      · subst hk0
        simp [seqOffset, configOffset_zero]
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
        have hkU : k ≤ U.card := hk.trans hcard
        exact (configOffset_eq_seqOffset (S := S) hk1 hkU).symm
  · have hlt : U.card < L := Nat.not_le.mp hcard
    have hcfg : F (configOffset U S) = 0 :=
      admissible_eq_zero_of_card_lt hF hL hlt
    have hnat : profileS (stdKappa ρ) X < seqOffset nthPrime n L :=
      Nat.not_le.mp fun hle => hcard (le_card_iff_seqOffset_le.mpr hle)
    have hspan : S < seqOffset nthPrime n L :=
      (lt_stdProfileS_iff_profileS hρ X _).mpr hnat
    have hseq : F (seqOffset nthPrime n) = 0 := hF.span hspan
    rw [hseq, hcfg]

/-! ### Config means of first-`L` tests -/

noncomputable def configTestMean (Ω : Finset ℕ) (μ : Finset ℕ → ℝ)
    (S : ℝ) (F : (ℕ → ℕ) → ℂ) : ℂ :=
  ∑ U ∈ Ω.powerset, (μ U : ℂ) * F (configOffset U S)

theorem rootedPattern_mem_powerset' (κ : ℝ) (X n : ℕ) :
    rootedPattern κ X n ∈ (windowOmega κ X).powerset :=
  mem_powerset.mpr (filter_subset _ _)

theorem seqWindow_image_nthPrime (X : ℕ) :
    (seqWindow nthPrime X).image nthPrime =
      (Ioc X (2 * X)).filter Nat.Prime := by
  ext q
  constructor
  · intro hq
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
    have hIX := mem_primeIndexBlock_iff.mp
      (seqWindow_nthPrime_eq_primeIndexBlock X ▸ hn)
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hIX.1, hIX.2⟩, prime_nthPrime n⟩
  · intro hq
    have hq' := mem_filter.mp hq
    have hIoc := mem_Ioc.mp hq'.1
    have hp := hq'.2
    refine mem_image.mpr ⟨Nat.primeCounting' q, ?_,
      nthPrime_primeCounting' hp⟩
    rw [seqWindow_nthPrime_eq_primeIndexBlock]
    refine (mem_primeIndexBlock_iff).mpr ?_
    rw [nthPrime_primeCounting' hp]
    exact hIoc

theorem actualPatternCount_eq_seqWindow_filter (κ : ℝ) (X : ℕ)
    (U : Finset ℕ) :
    actualPatternCount κ X U =
      ((seqWindow nthPrime X).filter
        (fun n => rootedPattern κ X (nthPrime n) = U)).card := by
  unfold actualPatternCount
  let s := (seqWindow nthPrime X).filter
    (fun n => rootedPattern κ X (nthPrime n) = U)
  have hinj : Set.InjOn nthPrime (s : Set ℕ) :=
    fun _ _ _ _ h => nthPrime_strictMono.injective h
  rw [← card_image_of_injOn hinj]
  congr 1
  ext q
  constructor
  · intro hq
    have hq' := mem_filter.mp hq
    have hp := hq'.2.1
    have hpat := hq'.2.2
    have hIoc := mem_Ioc.mp hq'.1
    have hn : Nat.primeCounting' q ∈ seqWindow nthPrime X := by
      rw [seqWindow_nthPrime_eq_primeIndexBlock]
      refine (mem_primeIndexBlock_iff).mpr ?_
      rw [nthPrime_primeCounting' hp]
      exact hIoc
    refine mem_image.mpr ⟨Nat.primeCounting' q,
      mem_filter.mpr ⟨hn, ?_⟩, nthPrime_primeCounting' hp⟩
    rwa [nthPrime_primeCounting' hp]
  · intro hq
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
    have hn' := mem_filter.mp hn
    have hIX := mem_primeIndexBlock_iff.mp
      (seqWindow_nthPrime_eq_primeIndexBlock X ▸ hn'.1)
    exact mem_filter.mpr
      ⟨mem_Ioc.mpr ⟨hIX.1, hIX.2⟩, ⟨prime_nthPrime n, hn'.2⟩⟩

theorem windowAvg_eq_configTestMean {κ : ℝ} {X : ℕ} {S : ℝ}
    {F : (ℕ → ℕ) → ℂ}
    (hF : ∀ n ∈ seqWindow nthPrime X,
      F (seqOffset nthPrime n) =
        F (configOffset (rootedPattern κ X (nthPrime n)) S)) :
    windowAvg (seqWindow nthPrime X) (fun n => F (seqOffset nthPrime n)) =
      configTestMean (windowOmega κ X) (actualConfigMass κ X) S F := by
  set s := seqWindow nthPrime X
  by_cases h0 : s.card = 0
  · have hs : s = ∅ := card_eq_zero.mp h0
    have hNX : windowNX X = 0 := by
      rw [← seqWindow_nthPrime_card]
      exact h0
    simp [windowAvg, configTestMean, actualConfigMass, hs, hNX]
  · have hN : 0 < windowNX X := by
      rw [← seqWindow_nthPrime_card]
      exact Nat.pos_of_ne_zero h0
    have hNX : (s.card : ℂ) = (windowNX X : ℂ) := by
      rw [seqWindow_nthPrime_card]
    have hsum :
        ∑ n ∈ s, F (seqOffset nthPrime n) =
          ∑ n ∈ s,
            F (configOffset (rootedPattern κ X (nthPrime n)) S) :=
      sum_congr rfl hF
    let g : ℕ → Finset ℕ := fun n => rootedPattern κ X (nthPrime n)
    let t := (windowOmega κ X).powerset
    have hmaps : ∀ n ∈ s, g n ∈ t := fun n _ =>
      rootedPattern_mem_powerset' κ X (nthPrime n)
    have hfib :=
      sum_fiberwise_of_maps_to' (s := s) (t := t) (g := g) hmaps
        (fun U => F (configOffset U S))
    have hinner :
        ∑ U ∈ t, ∑ n ∈ s.filter (fun n => g n = U),
            F (configOffset U S) =
          ∑ U ∈ t,
            (s.filter (fun n => g n = U)).card •
              F (configOffset U S) :=
      sum_congr rfl fun U _ => sum_const _
    have hcast :
        ∑ U ∈ t,
            (s.filter (fun n => g n = U)).card •
              F (configOffset U S) =
          ∑ U ∈ t,
            ((s.filter (fun n => g n = U)).card : ℂ) *
              F (configOffset U S) :=
      sum_congr rfl fun U _ => nsmul_eq_mul _ _
    have hcount : ∀ U ∈ t,
        (s.filter (fun n => g n = U)).card = actualPatternCount κ X U :=
      fun U _ => (actualPatternCount_eq_seqWindow_filter κ X U).symm
    have hmass : ∀ U ∈ t,
        actualConfigMass κ X U =
          (actualPatternCount κ X U : ℝ) / (windowNX X : ℝ) := by
      intro U _
      unfold actualConfigMass
      rw [if_neg (ne_of_gt hN)]
    unfold windowAvg configTestMean
    rw [hsum, ← hfib, hinner, hcast]
    have hdiv :=
      Finset.sum_div t
        (fun U =>
          ((s.filter (fun n => g n = U)).card : ℂ) *
            F (configOffset U S))
        (s.card : ℂ)
    rw [hdiv]
    refine sum_congr rfl fun U hU => ?_
    have hcard :
        (s.filter (fun n => g n = U)).card = actualPatternCount κ X U :=
      hcount U hU
    have hsplit :
        ((actualPatternCount κ X U : ℂ) * F (configOffset U S)) /
            (windowNX X : ℂ) =
          ((actualPatternCount κ X U : ℂ) / (windowNX X : ℂ)) *
            F (configOffset U S) := by
      rw [mul_comm, mul_div_assoc, mul_comm]
    rw [hcard, hNX, hsplit, hmass U hU, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_natCast]

theorem windowAvg_eq_configTestMean_of_dependsOnFirstL {ρ : ℝ} {X : ℕ}
    {F : (ℕ → ℕ) → ℂ} (hρ : 1 < ρ)
    (hL : 1 ≤ stdProfileL ρ (windowG X))
    (hF : IsAdmissibleShortPattern (stdProfileL ρ (windowG X))
      (stdProfileS ρ (windowG X)) F)
    (hDep : DependsOnFirstL (stdProfileL ρ (windowG X)) F) :
    windowAvg (seqWindow nthPrime X) (fun n => F (seqOffset nthPrime n)) =
      configTestMean (windowOmega (stdKappa ρ) X)
        (actualConfigMass (stdKappa ρ) X)
        (stdProfileS ρ (windowG X)) F :=
  windowAvg_eq_configTestMean fun n _ =>
    F_seqOffset_eq_configOffset hρ hL hF hDep

theorem firstL_mem_shapes' {Ω U : Finset ℕ} {L : ℕ}
    (hU : U ⊆ Ω) (hLcard : L ≤ U.card) :
    Stopped.firstL L U ∈ Ω.powerset.filter (fun K => K.card = L) :=
  mem_filter.mpr ⟨mem_powerset.mpr (Stopped.firstL_subset.trans hU),
    Stopped.firstL_card hLcard⟩

theorem configTestMean_eq_shortShape {Ω : Finset ℕ} {μ : Finset ℕ → ℝ}
    {L : ℕ} {S : ℝ} {F : (ℕ → ℕ) → ℂ} (hL : 1 ≤ L)
    (hF : IsAdmissibleShortPattern L S F) (hDep : DependsOnFirstL L F) :
    configTestMean Ω μ S F =
      ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        (Stopped.shortShapeMass Ω μ L K : ℂ) *
          F (configOffset K S) := by
  set t := Ω.powerset.filter (fun K => K.card = L)
  set s := Ω.powerset.filter (fun U => L ≤ U.card)
  have hmaps : ∀ U ∈ s, Stopped.firstL L U ∈ t := by
    intro U hU
    have hU' := mem_filter.mp hU
    exact firstL_mem_shapes' (mem_powerset.mp hU'.1) hU'.2
  have hterm : ∀ U ∈ Ω.powerset,
      (μ U : ℂ) * F (configOffset U S) =
        if L ≤ U.card then
          (μ U : ℂ) * F (configOffset (Stopped.firstL L U) S)
        else 0 := by
    intro U _hU
    by_cases hcard : L ≤ U.card
    · rw [if_pos hcard, F_eq_of_dependsOnFirstL hDep hcard]
    · rw [if_neg hcard]
      have hlt : U.card < L := Nat.not_le.mp hcard
      rw [admissible_eq_zero_of_card_lt hF hL hlt, mul_zero]
  unfold configTestMean
  rw [sum_congr rfl hterm]
  have hfilter :
      ∑ U ∈ Ω.powerset,
          (if L ≤ U.card then
            (μ U : ℂ) * F (configOffset (Stopped.firstL L U) S)
           else 0) =
        ∑ U ∈ s, (μ U : ℂ) * F (configOffset (Stopped.firstL L U) S) :=
    (sum_filter (p := fun U => L ≤ U.card) (f := fun U =>
      (μ U : ℂ) * F (configOffset (Stopped.firstL L U) S))).symm
  rw [hfilter]
  have hfib :=
    sum_fiberwise_of_maps_to (s := s) (t := t) (g := Stopped.firstL L)
      hmaps
      (fun U => (μ U : ℂ) * F (configOffset (Stopped.firstL L U) S))
  rw [← hfib]
  refine sum_congr rfl fun K _hK => ?_
  have hfiber :
      ∑ U ∈ s.filter (fun U => Stopped.firstL L U = K),
          (μ U : ℂ) * F (configOffset (Stopped.firstL L U) S) =
        ∑ U ∈ s.filter (fun U => Stopped.firstL L U = K),
          (μ U : ℂ) * F (configOffset K S) := by
    refine sum_congr rfl fun U hU => ?_
    have hUK : Stopped.firstL L U = K := (mem_filter.mp hU).2
    rw [hUK]
  rw [hfiber, ← sum_mul]
  have hmass :
      ∑ U ∈ s.filter (fun U => Stopped.firstL L U = K), (μ U : ℂ) =
        (Stopped.shortShapeMass Ω μ L K : ℂ) := by
    have hset :
        s.filter (fun U => Stopped.firstL L U = K) =
          Ω.powerset.filter
            (fun U => L ≤ U.card ∧ Stopped.firstL L U = K) := by
      simp [s, filter_filter]
    rw [hset, ← Complex.ofReal_sum]
    congr 1
    unfold Stopped.shortShapeMass
    exact sum_filter (p := fun U => L ≤ U.card ∧ Stopped.firstL L U = K)
      (f := μ)
  rw [hmass]

theorem configTestMean_sub_le_shapeL1 {Ω : Finset ℕ}
    {μ ν : Finset ℕ → ℝ} {L : ℕ} {S : ℝ} {F : (ℕ → ℕ) → ℂ} (hL : 1 ≤ L)
    (hF : IsAdmissibleShortPattern L S F) (hDep : DependsOnFirstL L F) :
    ‖configTestMean Ω μ S F - configTestMean Ω ν S F‖ ≤
      Stopped.shapeL1 Ω μ ν L := by
  rw [configTestMean_eq_shortShape hL hF hDep,
    configTestMean_eq_shortShape hL hF hDep]
  set t := Ω.powerset.filter (fun K => K.card = L)
  have hterm : ∀ K ∈ t,
      (Stopped.shortShapeMass Ω μ L K : ℂ) * F (configOffset K S) -
          (Stopped.shortShapeMass Ω ν L K : ℂ) * F (configOffset K S) =
        ((Stopped.shortShapeMass Ω μ L K -
            Stopped.shortShapeMass Ω ν L K : ℝ) : ℂ) *
          F (configOffset K S) := by
    intro K _
    rw [← sub_mul, Complex.ofReal_sub]
  have hsum :
      ∑ K ∈ t, (Stopped.shortShapeMass Ω μ L K : ℂ) *
            F (configOffset K S) -
          ∑ K ∈ t, (Stopped.shortShapeMass Ω ν L K : ℂ) *
            F (configOffset K S) =
        ∑ K ∈ t,
          ((Stopped.shortShapeMass Ω μ L K -
              Stopped.shortShapeMass Ω ν L K : ℝ) : ℂ) *
            F (configOffset K S) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl hterm
  rw [hsum]
  have hpt : ∀ K ∈ t,
      ‖((Stopped.shortShapeMass Ω μ L K -
            Stopped.shortShapeMass Ω ν L K : ℝ) : ℂ) *
          F (configOffset K S)‖ ≤
        |Stopped.shortShapeMass Ω μ L K -
          Stopped.shortShapeMass Ω ν L K| := by
    intro K _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hF.norm _)
  exact (norm_sum_le _ _).trans (sum_le_sum hpt)

theorem abs_configTestMean_sub_le_massL1 (Ω : Finset ℕ)
    (μ ν : Finset ℕ → ℝ) (S : ℝ) (F : (ℕ → ℕ) → ℂ)
    (hF : ∀ v, ‖F v‖ ≤ 1) :
    ‖configTestMean Ω μ S F - configTestMean Ω ν S F‖ ≤
      massL1 Ω.powerset μ ν := by
  unfold configTestMean
  have h :=
    abs_weighted_sub_le_tvHalf Ω.powerset μ ν
      (fun U => F (configOffset U S)) fun _ _ => hF _
  rwa [← massL1_eq_two_tvHalf] at h

/-! ### Nonnegativity used in the AHL remainder bound -/

theorem countEnvelope_nonneg (L r N : ℕ) :
    0 ≤ Stopped.countEnvelope L r N :=
  sum_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem failureMass_nonneg_of_nonneg {Ω : Finset ℕ} {μ : Finset ℕ → ℝ}
    {L : ℕ} (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U) :
    0 ≤ Stopped.failureMass Ω μ L :=
  sum_nonneg fun U hU => hμ U (mem_filter.mp hU).1

theorem modelRemainder_nonneg_of_nonneg {Ω : Finset ℕ} {ν : Finset ℕ → ℝ}
    {L r : ℕ} (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U) :
    0 ≤ Stopped.modelRemainder Ω ν L r :=
  sum_nonneg fun U hU =>
    mul_nonneg (hν U hU) (countEnvelope_nonneg L r U.card)

theorem ahlBudget_nonneg' (κ d0 : ℝ) (X : ℕ) : 0 ≤ ahlBudget κ d0 X := by
  unfold ahlBudget
  split_ifs
  · exact zero_le_one
  · apply mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _))
    apply sum_nonneg
    intro j _
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold ahlLayer
    exact sum_nonneg fun _ _ => posPart_nonneg _

theorem tendsto_two_mul_nhds_zero {α : Type*} {f : α → ℝ} {l : Filter α}
    (hf : Tendsto f l (nhds 0)) :
    Tendsto (fun x => (2 : ℝ) * f x) l (nhds 0) :=
  mul_zero (2 : ℝ) ▸ (tendsto_const_nhds (x := (2 : ℝ))).mul hf

theorem tendsto_add5_nhds_zero {α : Type*}
    {f1 f2 f3 f4 f5 : α → ℝ} {l : Filter α}
    (h1 : Tendsto f1 l (nhds 0)) (h2 : Tendsto f2 l (nhds 0))
    (h3 : Tendsto f3 l (nhds 0)) (h4 : Tendsto f4 l (nhds 0))
    (h5 : Tendsto f5 l (nhds 0)) :
    Tendsto (fun x => f1 x + f2 x + f3 x + f4 x + f5 x) l (nhds 0) := by
  have h12 := add_zero (0 : ℝ) ▸ h1.add h2
  have h123 := add_zero (0 : ℝ) ▸ h12.add h3
  have h1234 := add_zero (0 : ℝ) ▸ h123.add h4
  exact add_zero (0 : ℝ) ▸ h1234.add h5

/-! ### Finite first-`L` triangle -/

/-- AHL remainder plus config-versus-Bernoulli L¹. -/
noncomputable def ahlRemainderBound (κ d0 : ℝ) (ν : ℕ → Finset ℕ → ℝ)
    (ret : ℕ → ℝ) (X : ℕ) : ℝ :=
  Stopped.failureMass (windowOmega κ X) (ν X) (profileL κ X) +
    2 * Stopped.modelRemainder (windowOmega κ X) (ν X) (profileL κ X)
      (profileR (profileL κ X) d0) +
    2 * ahlBudget κ d0 X +
    2 * hlModelMismatch κ X (ν X) (profileL κ X)
      (profileR (profileL κ X) d0) +
    massL1 (windowOmega κ X).powerset (ν X)
      (bernoulliConfigMass (windowOmega κ X) (ret X))

theorem ahlRemainderBound_nonneg {κ d0 : ℝ} {ν : ℕ → Finset ℕ → ℝ}
    {ret : ℕ → ℝ} {X : ℕ}
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν X U) :
    0 ≤ ahlRemainderBound κ d0 ν ret X := by
  unfold ahlRemainderBound
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_
  · exact failureMass_nonneg_of_nonneg hν
  · exact mul_nonneg (by norm_num) (modelRemainder_nonneg_of_nonneg hν)
  · exact mul_nonneg (by norm_num) (ahlBudget_nonneg' κ d0 X)
  · exact mul_nonneg (by norm_num) (hlModelMismatch_nonneg κ X (ν X) _ _)
  · exact massL1_nonneg _ _ _

theorem windowAvg_sub_sieve_le_of_ahlBudget {ρ d0 : ℝ} {X : ℕ}
    {ν : Finset ℕ → ℝ} {F : (ℕ → ℕ) → ℂ} {δ : ℝ} (hρ : 1 < ρ)
    (hL : 1 ≤ stdProfileL ρ (windowG X)) (hN : 0 < windowNX X)
    (hν : ∀ U ∈ (windowOmega (stdKappa ρ) X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega (stdKappa ρ) X).powerset, ν U = 1)
    (hF : IsAdmissibleShortPattern (stdProfileL ρ (windowG X))
      (stdProfileS ρ (windowG X)) F)
    (hDep : DependsOnFirstL (stdProfileL ρ (windowG X)) F)
    (hδ : RootedSieveVsBernoulli (sieveCutoff (X : ℝ))
      (windowOmega (stdKappa ρ) X)
      (eulerProdNat (sieveCutoff (X : ℝ)))
      (stdProfileL ρ (windowG X)) (stdProfileS ρ (windowG X)) δ) :
    ‖windowAvg (seqWindow nthPrime X)
          (fun n => F (seqOffset nthPrime n)) -
        rootedSieveMean (sieveCutoff (X : ℝ)) F‖ ≤
      ahlRemainderBound (stdKappa ρ) d0 (fun _ => ν)
        (fun _ => eulerProdNat (sieveCutoff (X : ℝ))) X + δ := by
  set κ := stdKappa ρ
  set L := stdProfileL ρ (windowG X)
  set S := stdProfileS ρ (windowG X)
  set Ω := windowOmega κ X
  set actualMean :=
    configTestMean Ω (actualConfigMass κ X) S F
  set nuMean := configTestMean Ω ν S F
  set bernMean :=
    bernoulliShortPatternMean Ω (eulerProdNat (sieveCutoff (X : ℝ))) S F
  set sieveMean := rootedSieveMean (sieveCutoff (X : ℝ)) F
  have hid :
      windowAvg (seqWindow nthPrime X)
          (fun n => F (seqOffset nthPrime n)) =
        actualMean :=
    windowAvg_eq_configTestMean_of_dependsOnFirstL hρ hL hF hDep
  have hLeq : profileL κ X = L := profileL_eq_stdProfileL hρ X
  have hLκ : 1 ≤ profileL κ X := by rwa [hLeq]
  have hshape :=
    shapeL1_actual_add_failure_le_of_ahlBudget (κ := κ) (d0 := d0)
      (X := X) (ν := ν) hLκ hN hν hmass
  have hfail_act :
      0 ≤ Stopped.failureMass Ω (actualConfigMass κ X) (profileL κ X) :=
    failureMass_nonneg_of_nonneg fun U _ =>
      actualConfigMass_nonneg κ X U
  have hshape_le :
      Stopped.shapeL1 Ω (actualConfigMass κ X) ν (profileL κ X) ≤
        Stopped.failureMass Ω ν (profileL κ X) +
          2 * Stopped.modelRemainder Ω ν (profileL κ X)
            (profileR (profileL κ X) d0) +
          2 * ahlBudget κ d0 X +
          2 * hlModelMismatch κ X ν (profileL κ X)
            (profileR (profileL κ X) d0) := by
    linarith [hshape, hfail_act]
  have h1 :
      ‖actualMean - nuMean‖ ≤
        Stopped.shapeL1 Ω (actualConfigMass κ X) ν L :=
    configTestMean_sub_le_shapeL1 (Ω := Ω) (μ := actualConfigMass κ X)
      (ν := ν) (L := L) (S := S) (F := F) hL hF hDep
  have h1' :
      ‖actualMean - nuMean‖ ≤
        Stopped.failureMass Ω ν (profileL κ X) +
          2 * Stopped.modelRemainder Ω ν (profileL κ X)
            (profileR (profileL κ X) d0) +
          2 * ahlBudget κ d0 X +
          2 * hlModelMismatch κ X ν (profileL κ X)
            (profileR (profileL κ X) d0) := by
    have hshapeL :
        Stopped.shapeL1 Ω (actualConfigMass κ X) ν L =
          Stopped.shapeL1 Ω (actualConfigMass κ X) ν (profileL κ X) := by
      rw [hLeq]
    rw [hshapeL] at h1
    exact h1.trans hshape_le
  have hbern_eq :
      bernMean =
        configTestMean Ω
          (bernoulliConfigMass Ω (eulerProdNat (sieveCutoff (X : ℝ))))
          S F :=
    rfl
  have h2 : ‖nuMean - bernMean‖ ≤
      massL1 Ω.powerset ν
        (bernoulliConfigMass Ω (eulerProdNat (sieveCutoff (X : ℝ)))) := by
    rw [hbern_eq]
    exact abs_configTestMean_sub_le_massL1 Ω ν
      (bernoulliConfigMass Ω (eulerProdNat (sieveCutoff (X : ℝ)))) S F
      fun v => hF.norm v
  have h3 : ‖bernMean - sieveMean‖ ≤ δ := by
    rw [norm_sub_rev]
    exact hδ.2 F hF
  have hdecomp :
      (actualMean - nuMean) + (nuMean - bernMean) + (bernMean - sieveMean) =
        actualMean - sieveMean := by
    ring
  have htri :
      ‖actualMean - sieveMean‖ ≤
        ‖actualMean - nuMean‖ + ‖nuMean - bernMean‖ +
          ‖bernMean - sieveMean‖ := by
    have h :=
      (norm_add_le ((actualMean - nuMean) + (nuMean - bernMean))
        (bernMean - sieveMean)).trans
        (add_le_add
          (norm_add_le (actualMean - nuMean) (nuMean - bernMean))
          (le_rfl : ‖bernMean - sieveMean‖ ≤ ‖bernMean - sieveMean‖))
    rwa [hdecomp] at h
  rw [hid]
  exact htri.trans (add_le_add (add_le_add h1' h2) h3)

theorem bernoulli_cutoff_nonneg (κ : ℝ) (X : ℕ) (U : Finset ℕ) :
    0 ≤ bernoulliConfigMass (windowOmega κ X)
      (eulerProdNat (sieveCutoff (X : ℝ))) U :=
  bernoulliConfigMass_nonneg _
    (cutoff_retention_bounds X).1 (cutoff_retention_bounds X).2 U

theorem bernoulli_cutoff_sum (κ : ℝ) (X : ℕ) :
    ∑ U ∈ (windowOmega κ X).powerset,
      bernoulliConfigMass (windowOmega κ X)
        (eulerProdNat (sieveCutoff (X : ℝ))) U = 1 :=
  bernoulliConfigMass_sum _
    (cutoff_retention_bounds X).1 (cutoff_retention_bounds X).2

theorem modelRemainderVanishes_bernoulli (κ d0 : ℝ)
    (hfail : Tendsto (fun X : ℕ =>
        Stopped.failureMass (windowOmega κ X)
          (bernoulliConfigMass (windowOmega κ X)
            (eulerProdNat (sieveCutoff (X : ℝ))))
          (profileL κ X)) atTop (nhds 0))
    (hrem : Tendsto (fun X : ℕ =>
        Stopped.modelRemainder (windowOmega κ X)
          (bernoulliConfigMass (windowOmega κ X)
            (eulerProdNat (sieveCutoff (X : ℝ))))
          (profileL κ X) (profileR (profileL κ X) d0))
      atTop (nhds 0)) :
    ModelRemainderVanishes κ d0
      (fun X => bernoulliConfigMass (windowOmega κ X)
        (eulerProdNat (sieveCutoff (X : ℝ)))) :=
  ⟨Eventually.of_forall fun X U _ => bernoulli_cutoff_nonneg κ X U,
    Eventually.of_forall fun X => bernoulli_cutoff_sum κ X, hfail, hrem⟩

theorem tendsto_ahlRemainderBound {κ d0 : ℝ} {ν : ℕ → Finset ℕ → ℝ}
    {ret : ℕ → ℝ} (hAHL : AHL κ d0)
    (hRem : ModelRemainderVanishes κ d0 ν)
    (hHL : HLMismatchVanishes κ d0 ν)
    (hDisc : ConfigShapeDiscrepancy κ ν ret) :
    Tendsto (fun X : ℕ => ahlRemainderBound κ d0 ν ret X)
      atTop (nhds 0) :=
  tendsto_add5_nhds_zero hRem.2.2.1 (tendsto_two_mul_nhds_zero hRem.2.2.2)
    (tendsto_two_mul_nhds_zero hAHL) (tendsto_two_mul_nhds_zero hHL)
    hDisc.2

/-- AHL plus the named remainders imply that window averages of
**first-`L` admissible tests** on genuine prime windows are close to the
Dirac cutoff mixture of rooted-sieve means. Calibration of that mixture
is proved. This is not `ShortPatternS nthPrime`: that definition
quantifies over tests that may read offsets `k > L`. -/
theorem windowAvg_admissible_close_to_mixture {ρ d0 : ℝ}
    {ν : ℕ → Finset ℕ → ℝ} (hρ : 1 < ρ)
    (hAHL : AHL (stdKappa ρ) d0)
    (hRem : ModelRemainderVanishes (stdKappa ρ) d0 ν)
    (hHL : HLMismatchVanishes (stdKappa ρ) d0 ν)
    (hDisc : ConfigShapeDiscrepancy (stdKappa ρ) ν
      (fun X => eulerProdNat (sieveCutoff (X : ℝ))))
    (hMix : MixtureSieveVanishing (stdKappa ρ) ρ) :
    ∀ ε : ℝ, 0 < ε → ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      ∀ F : (ℕ → ℕ) → ℂ,
        IsAdmissibleShortPattern (stdProfileL ρ (windowG X))
          (stdProfileS ρ (windowG X)) F →
        DependsOnFirstL (stdProfileL ρ (windowG X)) F →
        ‖windowAvg (seqWindow nthPrime X)
              (fun n => F (seqOffset nthPrime n)) -
            mixtureMean (cutoffMixture X)
              (fun y => rootedSieveMean y F)‖ < ε := by
  intro ε hε
  set κ := stdKappa ρ
  set ret : ℕ → ℝ := fun X => eulerProdNat (sieveCutoff (X : ℝ))
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨Xmix, hmix⟩ := hMix (ε / 2) hε2
  have hTendsto := tendsto_ahlRemainderBound hAHL hRem hHL hDisc
  have hsmall :
      ∀ᶠ X : ℕ in atTop, ahlRemainderBound κ d0 ν ret X < ε / 2 := by
    have hTendsto' := hTendsto
    rw [Metric.tendsto_nhds] at hTendsto'
    have hd := hTendsto' (ε / 2) hε2
    filter_upwards [hd, hRem.1] with X hdist hνX
    have hnn : 0 ≤ ahlRemainderBound κ d0 ν ret X :=
      ahlRemainderBound_nonneg hνX
    have hdist' : dist (ahlRemainderBound κ d0 ν ret X) 0 < ε / 2 := hdist
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hdist'
  have hev :
      ∀ᶠ X : ℕ in atTop,
        1 ≤ stdProfileL ρ (windowG X) ∧
          0 < windowNX X ∧
            (∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν X U) ∧
              (∑ U ∈ (windowOmega κ X).powerset, ν X U = 1) ∧
                ahlRemainderBound κ d0 ν ret X < ε / 2 := by
    filter_upwards [eventually_one_le_stdProfileL hρ,
      eventually_windowNX_pos, hRem.1, hRem.2.1, hsmall] with
      X hL hN hν hsum hb
    exact ⟨hL, hN, hν, hsum, hb⟩
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp hev
  refine ⟨max X1 Xmix, fun X hX F hF hDep => ?_⟩
  have hX1' : X1 ≤ X := le_trans (le_max_left X1 Xmix) hX
  have hXmix' : Xmix ≤ X := le_trans (le_max_right X1 Xmix) hX
  obtain ⟨hL, hN, hν, hsum, hb⟩ := hX1 X hX1'
  have hsieve :
      RootedSieveVsBernoulli (sieveCutoff (X : ℝ)) (windowOmega κ X)
        (eulerProdNat (sieveCutoff (X : ℝ)))
        (stdProfileL ρ (windowG X)) (stdProfileS ρ (windowG X))
        (ε / 2) :=
    hmix X hXmix'
  have hfin :=
    windowAvg_sub_sieve_le_of_ahlBudget (ρ := ρ) (d0 := d0) (X := X)
      (ν := ν X) (F := F) (δ := ε / 2) hρ hL hN hν hsum hF hDep hsieve
  have hmixeq :
      mixtureMean (cutoffMixture X) (fun y => rootedSieveMean y F) =
        rootedSieveMean (sieveCutoff (X : ℝ)) F :=
    mixtureMean_cutoff X _
  rw [hmixeq]
  have hbound_eq :
      ahlRemainderBound κ d0 (fun _ => ν X)
          (fun _ => eulerProdNat (sieveCutoff (X : ℝ))) X =
        ahlRemainderBound κ d0 ν ret X :=
    rfl
  rw [hbound_eq] at hfin
  have hlt : ahlRemainderBound κ d0 ν ret X + ε / 2 < ε := by
    have h := add_lt_add_left hb (ε / 2)
    rwa [add_halves ε] at h
  exact lt_of_le_of_lt hfin hlt

theorem windowAvg_admissible_close_to_mixture_bernoulli {ρ d0 : ℝ}
    (hρ : 1 < ρ) (hAHL : AHL (stdKappa ρ) d0)
    (hRem : ModelRemainderVanishes (stdKappa ρ) d0
      (fun X => bernoulliConfigMass (windowOmega (stdKappa ρ) X)
        (eulerProdNat (sieveCutoff (X : ℝ)))))
    (hHL : HLMismatchVanishes (stdKappa ρ) d0
      (fun X => bernoulliConfigMass (windowOmega (stdKappa ρ) X)
        (eulerProdNat (sieveCutoff (X : ℝ)))))
    (hMix : MixtureSieveVanishing (stdKappa ρ) ρ) :
    ∀ ε : ℝ, 0 < ε → ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      ∀ F : (ℕ → ℕ) → ℂ,
        IsAdmissibleShortPattern (stdProfileL ρ (windowG X))
          (stdProfileS ρ (windowG X)) F →
        DependsOnFirstL (stdProfileL ρ (windowG X)) F →
        ‖windowAvg (seqWindow nthPrime X)
              (fun n => F (seqOffset nthPrime n)) -
            mixtureMean (cutoffMixture X)
              (fun y => rootedSieveMean y F)‖ < ε :=
  windowAvg_admissible_close_to_mixture hρ hAHL hRem hHL
    (configShapeDiscrepancy_of_bernoulli _
      (Eventually.of_forall cutoff_retention_bounds)) hMix

theorem windowAvg_truncatedPhaseTestCut_close_to_mixture {ρ d0 : ℝ}
    {ν : ℕ → Finset ℕ → ℝ} (hρ : 1 < ρ)
    (hAHL : AHL (stdKappa ρ) d0)
    (hRem : ModelRemainderVanishes (stdKappa ρ) d0 ν)
    (hHL : HLMismatchVanishes (stdKappa ρ) d0 ν)
    (hDisc : ConfigShapeDiscrepancy (stdKappa ρ) ν
      (fun X => eulerProdNat (sieveCutoff (X : ℝ))))
    (hMix : MixtureSieveVanishing (stdKappa ρ) ρ) :
    ∀ ε : ℝ, 0 < ε → ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      ∀ P : ℝ[X], ∀ B : ℕ, ∀ τ : ℤ,
        ‖windowAvg (seqWindow nthPrime X)
              (fun n =>
                truncatedPhaseTestCut P B
                  (stdProfileL ρ (windowG X))
                  (stdProfileS ρ (windowG X)) τ
                  (seqOffset nthPrime n)) -
            mixtureMean (cutoffMixture X) (fun y =>
              rootedSieveMean y
                (truncatedPhaseTestCut P B
                  (stdProfileL ρ (windowG X))
                  (stdProfileS ρ (windowG X)) τ))‖ < ε := by
  intro ε hε
  obtain ⟨X0, hX0⟩ :=
    windowAvg_admissible_close_to_mixture hρ hAHL hRem hHL hDisc hMix
      ε hε
  refine ⟨X0, fun X hX P B τ => ?_⟩
  exact hX0 X hX _
    (truncatedPhaseTestCut_admissible P B
      (stdProfileL ρ (windowG X)) (stdProfileS ρ (windowG X)) τ)
    (truncatedPhaseTestCut_dependsOnFirstL P B
      (stdProfileL ρ (windowG X)) (stdProfileS ρ (windowG X)) τ)

/-!
### Remaining lemma (not claimed)

`ShortPatternS nthPrime ρ windowG` is **not** a theorem of this file.

* Average: `windowAvg (seqWindow nthPrime X)` of `F ∘ seqOffset nthPrime`.
* Sequence: genuine primes with index in the dyadic block `I_X`.
* Proved test class: `IsAdmissibleShortPattern` **and** `DependsOnFirstL`.
* Missing test class: admissible tests that read offsets `k > L`.
  Stopped AHL only controls first-`L` shape L¹ of `actualConfigMass` on
  `windowOmega`. The identification
  `windowAvg = configTestMean actual` needs `DependsOnFirstL` (or a
  matching span cut) to pass from `seqOffset` to `configOffset`.

Used named `Prop`s, not axioms: `ModelRemainderVanishes`,
`HLMismatchVanishes`, `ConfigShapeDiscrepancy`, `MixtureSieveVanishing`.
Calibration `mixtureCalib (cutoffMixture X) (windowG X) → 0` is proved.
-/

def ShortPatternS_fullSpanTransfer (ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
    ∀ F : (ℕ → ℕ) → ℂ,
      IsAdmissibleShortPattern (stdProfileL ρ (windowG X))
        (stdProfileS ρ (windowG X)) F →
      ‖windowAvg (seqWindow nthPrime X)
            (fun n => F (seqOffset nthPrime n)) -
          configTestMean (windowOmega (stdKappa ρ) X)
            (actualConfigMass (stdKappa ρ) X)
            (stdProfileS ρ (windowG X)) F‖ < ε

end
end PrimeGapNormality.Prime
