import PrimeGapNormality.Prime.CardinalitySymMass
import PrimeGapNormality.Prime.PrimeShortS
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic

/-!
# CRT failure mass of `actualRootLaw` (not Bernoulli)

`ModelRemainderVanishes` wants a probability `ν` whose
`Stopped.failureMass` and Bonferroni `modelRemainder` vanish. The
target mass here is the actual finite CRT law

  `actualRootLaw (sieveCutoff X) (profileS κ X)`

on `windowOmega κ X = offsetWindow (profileS κ X)`.

**Compiled.**
1. `actualRootLaw` is a probability on the offset window (nonneg, sum 1).
2. On a late fibre whose mean count lies in `[3L, 5L]`, Chebyshev
   (`countBand_of_second_moment`) gives `failureMass ≤ 5/L`.
3. Full-window `failureMass` is the uniform average of fibre
   `failureMass`. Hence it is `≤ 5/L +` off-band fibre mass.
4. `profileL κ X → ∞` for `κ > 0`, so `5/L → 0`. Off-band mass `→ 0`
   (named) therefore yields `failureMass → 0`.
5. `ModelRemainderVanishes` follows from that limit plus a named
   `modelRemainder → 0`. Nonnegativity and total mass 1 are discharged.

**Not compiled.** Window mean of `actualRootLaw` in `[3L, 5L]`;
unconditional `failureMass → 0` without an off-band hypothesis;
`Stopped.modelRemainder → 0`; `HLMismatchVanishes`;
`ConfigShapeDiscrepancy`; `MixtureSieveVanishing`. Exact-count moments
control fibres, not the unsieved window.

Source: `PrimeShortS.ModelRemainderVanishes`; `ActualRootLaw`;
  `CardinalitySymMass.countBand_of_second_moment`,
  `actualRootLaw_eq_avg_lateRootLaw`.
Contract: API
Audit: GREEN
-/

open Finset Filter
open scoped Topology Classical

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

/-! ### Window identification and probability of `actualRootLaw` -/

theorem windowOmega_eq_offsetWindow (κ : ℝ) (X : ℕ) :
    windowOmega κ X = offsetWindow (profileS κ X) :=
  rfl

theorem residueChoice_card_pos (y : ℕ) :
    0 < Fintype.card (ResidueChoice y) :=
  Fintype.card_pos

theorem residueChoice_card_ne_zero (y : ℕ) :
    (Fintype.card (ResidueChoice y) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (residueChoice_card_pos y))

theorem actualRootLaw_nonneg (y S : ℕ) (U : Finset ℕ) :
    0 ≤ actualRootLaw y S U :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem sieveSurvivorsFin_mem_powerset (y S : ℕ) (σ : ResidueChoice y) :
    sieveSurvivorsFin y σ S ∈ (offsetWindow S).powerset :=
  mem_powerset.mpr (filter_subset _ _)

theorem actualRootLaw_sum (y S : ℕ) :
    ∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U = 1 := by
  have hmaps :
      ((univ : Finset (ResidueChoice y)) : Set (ResidueChoice y)).MapsTo
        (fun σ => sieveSurvivorsFin y σ S) (offsetWindow S).powerset :=
    fun σ _ => sieveSurvivorsFin_mem_powerset y S σ
  have hcard :=
    card_eq_sum_card_fiberwise (s := univ) (t := (offsetWindow S).powerset)
      (f := fun σ => sieveSurvivorsFin y σ S) hmaps
  have hsum :
      ∑ U ∈ (offsetWindow S).powerset,
          (((univ : Finset (ResidueChoice y)).filter
              fun σ => sieveSurvivorsFin y σ S = U).card : ℝ) =
        (Fintype.card (ResidueChoice y) : ℝ) := by
    rw [← Nat.cast_sum, ← hcard, card_univ]
  unfold actualRootLaw
  rw [← sum_div, hsum]
  exact div_self (residueChoice_card_ne_zero y)

theorem actualRootLaw_sum_windowOmega (κ : ℝ) (X : ℕ) :
    ∑ U ∈ (windowOmega κ X).powerset,
        actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X) U = 1 := by
  rw [windowOmega_eq_offsetWindow]
  exact actualRootLaw_sum _ _

theorem actualRootLaw_failureMass_nonneg (y S L : ℕ) :
    0 ≤ Stopped.failureMass (offsetWindow S) (actualRootLaw y S) L :=
  failureMass_nonneg_of_nonneg fun U _ => actualRootLaw_nonneg y S U

/-! ### Late fibre: vanishing off `A`, Chebyshev failure mass -/

theorem lateRootLaw_eq_zero_of_not_subset {S y : ℕ} {A E : Finset ℕ}
    (hE : ¬ E ⊆ A) : lateRootLaw S y A E = 0 := by
  have hempty :
      ((univ : Finset (LateResidueChoice S y)).filter
          fun σ => lateSurvivors S y A σ = E) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro σ hσ
    have hE' : lateSurvivors S y A σ = E := (mem_filter.mp hσ).2
    have hsub : lateSurvivors S y A σ ⊆ A := by
      unfold lateSurvivors
      exact filter_subset _ _
    exact hE (hE' ▸ hsub)
  simp [lateRootLaw, lateProductMass, hempty]

theorem lateRootLaw_failureMass_le_one (S y : ℕ) (A : Finset ℕ) (L : ℕ) :
    Stopped.failureMass A (lateRootLaw S y A) L ≤ 1 := by
  have hnn : ∀ E ∈ A.powerset, 0 ≤ lateRootLaw S y A E := fun E _ =>
    lateProductMass_nonneg S y A E
  have hsum : ∑ E ∈ A.powerset, lateRootLaw S y A E = 1 := by
    simpa [lateRootLaw] using lateProductMass_sum S y A
  unfold Stopped.failureMass
  exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun E hE _ => hnn E hE).trans_eq hsum

theorem lateRootLaw_failureMass_window_eq_fibre
    (S y T : ℕ) {A : Finset ℕ} (hA : A ⊆ offsetWindow T) (L : ℕ) :
    Stopped.failureMass (offsetWindow T) (lateRootLaw S y A) L =
      Stopped.failureMass A (lateRootLaw S y A) L := by
  unfold Stopped.failureMass
  refine (sum_subset ?hsub ?hzero).symm
  · intro U hU
    have hU' := mem_filter.mp hU
    exact mem_filter.mpr ⟨powerset_mono.mpr hA hU'.1, hU'.2⟩
  · intro U hU hnot
    have hcard : U.card < L := (mem_filter.mp hU).2
    have hnotA : ¬ U ⊆ A := by
      intro hUA
      exact hnot (mem_filter.mpr ⟨mem_powerset.mpr hUA, hcard⟩)
    exact lateRootLaw_eq_zero_of_not_subset hnotA

/-- Fibre `failureMass` is `O(1/L)` when the exact mean lies in `[3L, 5L]`.
Not a statement about the full-window `actualRootLaw`. -/
theorem lateRootLaw_failureMass_le_of_meanBand
    (S y : ℕ) {T : ℕ} {A : Finset ℕ} {L : ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hSy : S ≤ y) (hL : 0 < L)
    (hlo : (3 : ℝ) * L ≤ (A.card : ℝ) * lateRetention S y)
    (hhi : (A.card : ℝ) * lateRetention S y ≤ (5 : ℝ) * L) :
    Stopped.failureMass A (lateRootLaw S y A) L ≤
      (5 : ℝ) / (L : ℝ) := by
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
    have h2 : L ≤ 2 * L := Nat.le_mul_of_pos_left L (by decide : 0 < 2)
    exact Nat.lt_of_lt_of_le hU'.2 h2
  have hnn : ∀ E ∈ A.powerset, 0 ≤ lateRootLaw S y A E := hμ.1
  unfold Stopped.failureMass
  refine (sum_le_sum_of_subset_of_nonneg hsub ?_).trans hband
  intro E hE _
  exact hnn E (mem_filter.mp hE).1

/-! ### Off-band fibre mass and averaging -/

/-- Presieve fibres whose exact mean count lies outside `[3L, 5L]`. -/
noncomputable def lateFibreOffBandSet (S y T L : ℕ) :
    Finset (ResidueChoice S) :=
  (univ : Finset (ResidueChoice S)).filter fun σ =>
    ¬ ((3 : ℝ) * L ≤
          ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ∧
        ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ≤
          (5 : ℝ) * L)

/-- Complementary band set. -/
noncomputable def lateFibreMeanBandSet (S y T L : ℕ) :
    Finset (ResidueChoice S) :=
  (univ : Finset (ResidueChoice S)).filter fun σ =>
    (3 : ℝ) * L ≤
        ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ∧
      ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ≤
        (5 : ℝ) * L

noncomputable def lateFibreOffBandMass (S y T L : ℕ) : ℝ :=
  (lateFibreOffBandSet S y T L).card /
    (Fintype.card (ResidueChoice S) : ℝ)

theorem lateFibreOffBandMass_nonneg (S y T L : ℕ) :
    0 ≤ lateFibreOffBandMass S y T L :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem lateFibreOffBandMass_le_one (S y T L : ℕ) :
    lateFibreOffBandMass S y T L ≤ 1 := by
  have hpos : 0 < (Fintype.card (ResidueChoice S) : ℝ) :=
    Nat.cast_pos.mpr (residueChoice_card_pos S)
  have hsub : lateFibreOffBandSet S y T L ⊆
      (univ : Finset (ResidueChoice S)) := fun _ _ => mem_univ _
  exact (div_le_one hpos).mpr
    (Nat.cast_le.mpr (card_le_card hsub))

theorem lateFibreMeanBandSet_union_offBand (S y T L : ℕ) :
    lateFibreMeanBandSet S y T L ∪ lateFibreOffBandSet S y T L =
      (univ : Finset (ResidueChoice S)) := by
  ext σ
  constructor
  · intro _h
    exact mem_univ σ
  · intro _h
    simp only [mem_union, lateFibreMeanBandSet, lateFibreOffBandSet,
      mem_filter, mem_univ, true_and]
    by_cases h :
      (3 : ℝ) * L ≤
          ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ∧
        ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ≤
          (5 : ℝ) * L
    · exact Or.inl h
    · exact Or.inr h

theorem disjoint_lateFibreMeanBand_offBand (S y T L : ℕ) :
    Disjoint (lateFibreMeanBandSet S y T L) (lateFibreOffBandSet S y T L) := by
  refine disjoint_left.mpr ?_
  intro σ hband hoff
  have hb : (3 : ℝ) * L ≤
        ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ∧
      ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ≤
        (5 : ℝ) * L :=
    (mem_filter.mp hband).2
  have ho :
      ¬ ((3 : ℝ) * L ≤
            ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ∧
          ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ≤
            (5 : ℝ) * L) :=
    (mem_filter.mp hoff).2
  exact ho hb

theorem lateFibreOffBandMass_eq_zero_of_forall_band
    (S y T L : ℕ)
    (h : ∀ σ : ResidueChoice S,
      (3 : ℝ) * L ≤
          ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ∧
        ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ≤
          (5 : ℝ) * L) :
    lateFibreOffBandMass S y T L = 0 := by
  have hemp : lateFibreOffBandSet S y T L = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro σ hσ
    exact (mem_filter.mp hσ).2 (h σ)
  simp [lateFibreOffBandMass, hemp]

theorem actualRootLaw_failureMass_eq_avg
    (S y T L : ℕ) (hTS : T ≤ S) (hSy : S ≤ y) :
    Stopped.failureMass (offsetWindow T) (actualRootLaw y T) L =
      (∑ σ : ResidueChoice S,
          Stopped.failureMass (offsetWindow T)
            (lateRootLaw S y (lateCandidateSet S T σ)) L) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  have hpt :
      (fun U => actualRootLaw y T U) =
        fun U =>
          (∑ σ : ResidueChoice S,
              lateRootLaw S y (lateCandidateSet S T σ) U) /
            (Fintype.card (ResidueChoice S) : ℝ) := by
    funext U
    exact actualRootLaw_eq_avg_lateRootLaw S y T hTS hSy U
  unfold Stopped.failureMass
  rw [hpt, ← sum_div]
  congr 1
  change
      ∑ U ∈ (offsetWindow T).powerset.filter (fun U => U.card < L),
          ∑ σ ∈ (univ : Finset (ResidueChoice S)),
            lateRootLaw S y (lateCandidateSet S T σ) U =
        ∑ σ ∈ (univ : Finset (ResidueChoice S)),
          ∑ U ∈ (offsetWindow T).powerset.filter (fun U => U.card < L),
            lateRootLaw S y (lateCandidateSet S T σ) U
  exact sum_comm

/-- Full-window CRT `failureMass` is `≤ 5/L` plus the mass of fibres
whose mean count is outside `[3L, 5L]`. -/
theorem actualRootLaw_failureMass_le_five_div_add_offBand
    (S y T L : ℕ) (hTS : T ≤ S) (hSy : S ≤ y) (hL : 0 < L) :
    Stopped.failureMass (offsetWindow T) (actualRootLaw y T) L ≤
      (5 : ℝ) / (L : ℝ) + lateFibreOffBandMass S y T L := by
  have hdenpos : 0 < (Fintype.card (ResidueChoice S) : ℝ) :=
    Nat.cast_pos.mpr (residueChoice_card_pos S)
  rw [actualRootLaw_failureMass_eq_avg S y T L hTS hSy]
  have hfib : ∀ σ : ResidueChoice S,
      Stopped.failureMass (offsetWindow T)
          (lateRootLaw S y (lateCandidateSet S T σ)) L =
        Stopped.failureMass (lateCandidateSet S T σ)
          (lateRootLaw S y (lateCandidateSet S T σ)) L :=
    fun σ =>
      lateRootLaw_failureMass_window_eq_fibre S y T
        (lateCandidateSet_subset_Icc S T σ) L
  simp_rw [hfib]
  let fail (σ : ResidueChoice S) : ℝ :=
    Stopped.failureMass (lateCandidateSet S T σ)
      (lateRootLaw S y (lateCandidateSet S T σ)) L
  change
    (∑ σ ∈ (univ : Finset (ResidueChoice S)), fail σ) /
        (Fintype.card (ResidueChoice S) : ℝ) ≤
      (5 : ℝ) / (L : ℝ) + lateFibreOffBandMass S y T L
  have hsum :
      ∑ σ ∈ (univ : Finset (ResidueChoice S)), fail σ =
        ∑ σ ∈ lateFibreMeanBandSet S y T L, fail σ +
          ∑ σ ∈ lateFibreOffBandSet S y T L, fail σ := by
    rw [← lateFibreMeanBandSet_union_offBand S y T L,
      sum_union (disjoint_lateFibreMeanBand_offBand S y T L)]
  have hbandσ : ∀ σ ∈ lateFibreMeanBandSet S y T L,
      fail σ ≤ (5 : ℝ) / (L : ℝ) := by
    intro σ hσ
    have hm := (mem_filter.mp hσ).2
    exact lateRootLaw_failureMass_le_of_meanBand S y
      (lateCandidateSet_subset_Icc S T σ) hTS hSy hL hm.1 hm.2
  have hoffσ : ∀ σ ∈ lateFibreOffBandSet S y T L, fail σ ≤ 1 :=
    fun σ _ => lateRootLaw_failureMass_le_one S y _ L
  have hle :
      ∑ σ ∈ (univ : Finset (ResidueChoice S)), fail σ ≤
        ∑ σ ∈ lateFibreMeanBandSet S y T L, (5 : ℝ) / (L : ℝ) +
          ∑ σ ∈ lateFibreOffBandSet S y T L, (1 : ℝ) := by
    rw [hsum]
    exact add_le_add (sum_le_sum hbandσ) (sum_le_sum hoffσ)
  have hconst :
      ∑ σ ∈ lateFibreMeanBandSet S y T L, (5 : ℝ) / (L : ℝ) +
          ∑ σ ∈ lateFibreOffBandSet S y T L, (1 : ℝ) =
        ((lateFibreMeanBandSet S y T L).card : ℝ) *
            ((5 : ℝ) / (L : ℝ)) +
          ((lateFibreOffBandSet S y T L).card : ℝ) := by
    rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  have hdiv :
      (∑ σ ∈ (univ : Finset (ResidueChoice S)), fail σ) /
          (Fintype.card (ResidueChoice S) : ℝ) ≤
        (((lateFibreMeanBandSet S y T L).card : ℝ) *
              ((5 : ℝ) / (L : ℝ)) +
            ((lateFibreOffBandSet S y T L).card : ℝ)) /
          (Fintype.card (ResidueChoice S) : ℝ) :=
    div_le_div_of_nonneg_right (hconst ▸ hle) (le_of_lt hdenpos)
  have hre :
      (((lateFibreMeanBandSet S y T L).card : ℝ) *
            ((5 : ℝ) / (L : ℝ)) +
          ((lateFibreOffBandSet S y T L).card : ℝ)) /
          (Fintype.card (ResidueChoice S) : ℝ) =
        (((lateFibreMeanBandSet S y T L).card : ℝ) /
              (Fintype.card (ResidueChoice S) : ℝ)) *
            ((5 : ℝ) / (L : ℝ)) +
          ((lateFibreOffBandSet S y T L).card : ℝ) /
            (Fintype.card (ResidueChoice S) : ℝ) := by
    rw [add_div, mul_comm ((lateFibreMeanBandSet S y T L).card : ℝ),
      mul_div_assoc, mul_comm]
  have hble :
      ((lateFibreMeanBandSet S y T L).card : ℝ) /
          (Fintype.card (ResidueChoice S) : ℝ) ≤ 1 := by
    have hsub : lateFibreMeanBandSet S y T L ⊆
        (univ : Finset (ResidueChoice S)) := fun _ _ => mem_univ _
    exact (div_le_one hdenpos).mpr (Nat.cast_le.mpr (card_le_card hsub))
  have hnn5 : 0 ≤ (5 : ℝ) / (L : ℝ) :=
    div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hfive :
      (((lateFibreMeanBandSet S y T L).card : ℝ) /
            (Fintype.card (ResidueChoice S) : ℝ)) *
          ((5 : ℝ) / (L : ℝ)) ≤
        (5 : ℝ) / (L : ℝ) :=
    mul_le_of_le_one_left hnn5 hble
  have hfinal :
      (((lateFibreMeanBandSet S y T L).card : ℝ) /
            (Fintype.card (ResidueChoice S) : ℝ)) *
          ((5 : ℝ) / (L : ℝ)) +
        ((lateFibreOffBandSet S y T L).card : ℝ) /
          (Fintype.card (ResidueChoice S) : ℝ) ≤
        (5 : ℝ) / (L : ℝ) + lateFibreOffBandMass S y T L :=
    add_le_add hfive le_rfl
  rw [hre] at hdiv
  exact hdiv.trans hfinal

theorem actualRootLaw_failureMass_le_five_div_of_forall_band
    (S y T L : ℕ) (hTS : T ≤ S) (hSy : S ≤ y) (hL : 0 < L)
    (hband : ∀ σ : ResidueChoice S,
      (3 : ℝ) * L ≤
          ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ∧
        ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y ≤
          (5 : ℝ) * L) :
    Stopped.failureMass (offsetWindow T) (actualRootLaw y T) L ≤
      (5 : ℝ) / (L : ℝ) := by
  have h0 := lateFibreOffBandMass_eq_zero_of_forall_band S y T L hband
  have hle :=
    actualRootLaw_failureMass_le_five_div_add_offBand S y T L hTS hSy hL
  rw [h0, add_zero] at hle
  exact hle

/-! ### `profileL → ∞` and `5/L → 0` -/

theorem tendsto_profileL_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ => profileL κ X) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun n => ?_
  have h := eventually_nat_le_kappa_log_windowG hκ n
  rw [eventually_atTop] at h
  obtain ⟨X0, hX0⟩ := h
  refine ⟨X0, fun X hX => ?_⟩
  have hlog : (n : ℝ) ≤ κ * Real.log (windowG X) := hX0 X hX
  have hcast : (n : ℝ) ≤ (profileL κ X : ℝ) :=
    hlog.trans (kappa_log_windowG_le_profileL (le_of_lt hκ) X)
  exact Nat.cast_le.mp hcast

theorem tendsto_inv_profileL {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ => (profileL κ X : ℝ)⁻¹) atTop (nhds 0) :=
  (tendsto_natCast_atTop_atTop.comp (tendsto_profileL_atTop hκ)).inv_tendsto_atTop

theorem tendsto_five_div_profileL {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ => (5 : ℝ) / (profileL κ X : ℝ))
      atTop (nhds 0) := by
  have hfun :
      (fun X : ℕ => (5 : ℝ) / (profileL κ X : ℝ)) =
        fun X => (5 : ℝ) * (profileL κ X : ℝ)⁻¹ := by
    funext X
    rw [div_eq_mul_inv]
  rw [hfun]
  exact mul_zero (5 : ℝ) ▸
    (tendsto_const_nhds (x := (5 : ℝ))).mul (tendsto_inv_profileL hκ)

/-! ### Named remaining band input (not an axiom) -/

/-- Every physical S-presieve fibre has exact mean count in `[3L, 5L]`.
Not proved: that needs a candidate-count law, not only fibre moments. -/
def ActualCrtFibreMeanBand (κ : ℝ) : Prop :=
  ∀ᶠ X : ℕ in atTop,
    profileS κ X ≤ sieveCutoff (X : ℝ) ∧
      0 < profileL κ X ∧
        ∀ σ : ResidueChoice (profileS κ X),
          (3 : ℝ) * profileL κ X ≤
              ((lateCandidateSet (profileS κ X) (profileS κ X) σ).card : ℝ) *
                lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ∧
            ((lateCandidateSet (profileS κ X) (profileS κ X) σ).card : ℝ) *
                lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ≤
              (5 : ℝ) * profileL κ X

/-- Off-band fibre mass vanishes, and the averaging hypotheses hold
eventually. Weaker than `ActualCrtFibreMeanBand`. -/
def ActualCrtFibreOffBandVanishes (κ : ℝ) : Prop :=
  (∀ᶠ X : ℕ in atTop,
      profileS κ X ≤ sieveCutoff (X : ℝ) ∧ 0 < profileL κ X) ∧
    Tendsto (fun X : ℕ =>
        lateFibreOffBandMass (profileS κ X) (sieveCutoff (X : ℝ))
          (profileS κ X) (profileL κ X))
      atTop (nhds 0)

theorem actualCrtFibreOffBandVanishes_of_meanBand {κ : ℝ}
    (hband : ActualCrtFibreMeanBand κ) :
    ActualCrtFibreOffBandVanishes κ := by
  refine ⟨?hsy, ?hmass⟩
  · filter_upwards [hband] with X hX
    exact ⟨hX.1, hX.2.1⟩
  · have heq :
        (fun X : ℕ =>
            lateFibreOffBandMass (profileS κ X) (sieveCutoff (X : ℝ))
              (profileS κ X) (profileL κ X)) =ᶠ[atTop]
          fun _ => (0 : ℝ) := by
      filter_upwards [hband] with X hX
      exact lateFibreOffBandMass_eq_zero_of_forall_band
        (profileS κ X) (sieveCutoff (X : ℝ)) (profileS κ X)
        (profileL κ X) hX.2.2
    exact Tendsto.congr' heq.symm tendsto_const_nhds

theorem actualRootLaw_failureMass_le_five_div_add_offBand_profile
    (κ : ℝ) (X : ℕ)
    (hSy : profileS κ X ≤ sieveCutoff (X : ℝ))
    (hL : 0 < profileL κ X) :
    Stopped.failureMass (windowOmega κ X)
        (actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X))
        (profileL κ X) ≤
      (5 : ℝ) / (profileL κ X : ℝ) +
        lateFibreOffBandMass (profileS κ X) (sieveCutoff (X : ℝ))
          (profileS κ X) (profileL κ X) := by
  rw [windowOmega_eq_offsetWindow]
  exact actualRootLaw_failureMass_le_five_div_add_offBand
    (profileS κ X) (sieveCutoff (X : ℝ)) (profileS κ X) (profileL κ X)
    le_rfl hSy hL

/-- Under off-band vanishing, full-window CRT `failureMass → 0`.
The bound is `5/L +` off-band mass; `L → ∞` is unconditional for `κ > 0`. -/
theorem tendsto_actualRootLaw_failureMass_of_offBand
    {κ : ℝ} (hκ : 0 < κ)
    (hband : ActualCrtFibreOffBandVanishes κ) :
    Tendsto (fun X : ℕ =>
        Stopped.failureMass (windowOmega κ X)
          (actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X))
          (profileL κ X))
      atTop (nhds 0) := by
  have hnn : ∀ X : ℕ,
      0 ≤ Stopped.failureMass (windowOmega κ X)
          (actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X))
          (profileL κ X) :=
    fun X => failureMass_nonneg_of_nonneg fun U _ =>
      actualRootLaw_nonneg _ _ _
  have hle :
      ∀ᶠ X : ℕ in atTop,
        Stopped.failureMass (windowOmega κ X)
            (actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X))
            (profileL κ X) ≤
          (5 : ℝ) / (profileL κ X : ℝ) +
            lateFibreOffBandMass (profileS κ X) (sieveCutoff (X : ℝ))
              (profileS κ X) (profileL κ X) := by
    filter_upwards [hband.1] with X hX
    exact actualRootLaw_failureMass_le_five_div_add_offBand_profile
      κ X hX.1 hX.2
  have hupper :
      Tendsto (fun X : ℕ =>
          (5 : ℝ) / (profileL κ X : ℝ) +
            lateFibreOffBandMass (profileS κ X) (sieveCutoff (X : ℝ))
              (profileS κ X) (profileL κ X))
        atTop (nhds 0) :=
    add_zero (0 : ℝ) ▸ (tendsto_five_div_profileL hκ).add hband.2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper (Eventually.of_forall hnn) hle

theorem tendsto_actualRootLaw_failureMass_of_fibreMeanBand
    {κ : ℝ} (hκ : 0 < κ) (hband : ActualCrtFibreMeanBand κ) :
    Tendsto (fun X : ℕ =>
        Stopped.failureMass (windowOmega κ X)
          (actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X))
          (profileL κ X))
      atTop (nhds 0) :=
  tendsto_actualRootLaw_failureMass_of_offBand hκ
    (actualCrtFibreOffBandVanishes_of_meanBand hband)

theorem tendsto_actualRootLaw_failureMass_stdKappa
    {ρ : ℝ} (hρ : 1 < ρ)
    (hband : ActualCrtFibreOffBandVanishes (stdKappa ρ)) :
    Tendsto (fun X : ℕ =>
        Stopped.failureMass (windowOmega (stdKappa ρ) X)
          (actualRootLaw (sieveCutoff (X : ℝ)) (profileS (stdKappa ρ) X))
          (profileL (stdKappa ρ) X))
      atTop (nhds 0) :=
  tendsto_actualRootLaw_failureMass_of_offBand (stdKappa_pos hρ) hband

/-! ### `ModelRemainderVanishes` adapter: probability discharged -/

/-- Nonnegativity and total mass 1 of the actual CRT law are theorems.
`failureMass → 0` and `modelRemainder → 0` remain named inputs:
the former follows from `ActualCrtFibreOffBandVanishes`; the Bonferroni
remainder is not a second-moment statement. -/
theorem modelRemainderVanishes_actualRootLaw (κ d0 : ℝ)
    (hfail : Tendsto (fun X : ℕ =>
        Stopped.failureMass (windowOmega κ X)
          (actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X))
          (profileL κ X))
      atTop (nhds 0))
    (hrem : Tendsto (fun X : ℕ =>
        Stopped.modelRemainder (windowOmega κ X)
          (actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X))
          (profileL κ X) (profileR (profileL κ X) d0))
      atTop (nhds 0)) :
    ModelRemainderVanishes κ d0
      (fun X => actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X)) :=
  ⟨Eventually.of_forall fun X U _ => actualRootLaw_nonneg _ _ _,
    Eventually.of_forall fun X => actualRootLaw_sum_windowOmega κ X,
    hfail, hrem⟩

theorem modelRemainderVanishes_actualRootLaw_of_offBand
    {κ d0 : ℝ} (hκ : 0 < κ)
    (hband : ActualCrtFibreOffBandVanishes κ)
    (hrem : Tendsto (fun X : ℕ =>
        Stopped.modelRemainder (windowOmega κ X)
          (actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X))
          (profileL κ X) (profileR (profileL κ X) d0))
      atTop (nhds 0)) :
    ModelRemainderVanishes κ d0
      (fun X => actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X)) :=
  modelRemainderVanishes_actualRootLaw κ d0
    (tendsto_actualRootLaw_failureMass_of_offBand hκ hband) hrem

theorem modelRemainderVanishes_actualRootLaw_stdKappa
    {ρ d0 : ℝ} (hρ : 1 < ρ)
    (hfail : Tendsto (fun X : ℕ =>
        Stopped.failureMass (windowOmega (stdKappa ρ) X)
          (actualRootLaw (sieveCutoff (X : ℝ)) (profileS (stdKappa ρ) X))
          (profileL (stdKappa ρ) X))
      atTop (nhds 0))
    (hrem : Tendsto (fun X : ℕ =>
        Stopped.modelRemainder (windowOmega (stdKappa ρ) X)
          (actualRootLaw (sieveCutoff (X : ℝ)) (profileS (stdKappa ρ) X))
          (profileL (stdKappa ρ) X)
          (profileR (profileL (stdKappa ρ) X) d0))
      atTop (nhds 0)) :
    ModelRemainderVanishes (stdKappa ρ) d0
      (fun X => actualRootLaw (sieveCutoff (X : ℝ))
        (profileS (stdKappa ρ) X)) :=
  modelRemainderVanishes_actualRootLaw _ _ hfail hrem

end

end PrimeGapNormality.Prime
