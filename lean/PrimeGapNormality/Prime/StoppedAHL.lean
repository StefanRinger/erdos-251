import PrimeGapNormality.Prime.StoppedPrime
import PrimeGapNormality.Prime.BudgetNorm
import PrimeGapNormality.Prime.EndAPI
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic

/-!
# AHL layers/budget control StoppedPrime first-L L1

If EndAPI `ahlLayer` (weighted) or `ahlBudget` is small, and the model
remainder plus HL-inclusion mismatch are small, then StoppedPrime's
`shapeL1 + failureMass` is small. Does not prove `ShortPatternS` for
`nthPrime`. Does not assume `KuperbergConj13`.

Source: `StoppedPrime` finite (5.1)/(1.1); `BudgetNorm` (1.2);
`EndAPI` (eq:ahl); paper (eq:normalizedbudget), `lem:stopped`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Filter
open scoped Topology

set_option maxHeartbeats 800000

noncomputable section

/-! ### Weighted HL-inclusion mismatch (StoppedPrime remainder) -/

/-- Weighted `|M_X/N_X - q_H|` remainder on layers `L ≤ j ≤ r`. -/
def hlModelMismatch (κ : ℝ) (X : ℕ) (ν : Finset ℕ → ℝ) (L r : ℕ) : ℝ :=
  ∑ j ∈ Icc L r,
    ((j - 1).choose (L - 1) : ℝ) *
      ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
        |rootedMainTerm X H / (windowNX X : ℝ) -
          Stopped.inclusionMass (windowOmega κ X) ν H|

theorem hlModelMismatch_nonneg (κ : ℝ) (X : ℕ) (ν : Finset ℕ → ℝ)
    (L r : ℕ) : 0 ≤ hlModelMismatch κ X ν L r :=
  sum_nonneg fun j _ =>
    mul_nonneg (Nat.cast_nonneg ((j - 1).choose (L - 1)))
      (sum_nonneg fun _ _ => abs_nonneg _)

theorem hlModelMismatch_eq_zero {κ : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ}
    (hN : 0 < windowNX X)
    (hq : ∀ H ∈ (windowOmega κ X).powerset,
      Stopped.inclusionMass (windowOmega κ X) ν H =
        rootedMainTerm X H / (windowNX X : ℝ)) :
    hlModelMismatch κ X ν L r = 0 := by
  refine sum_eq_zero fun j _ => ?_
  have h0 :
      ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
          |rootedMainTerm X H / (windowNX X : ℝ) -
            Stopped.inclusionMass (windowOmega κ X) ν H| = 0 := by
    refine sum_eq_zero fun H hH => ?_
    have hHΩ : H ⊆ windowOmega κ X :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hH).1
    rw [hq H (Finset.mem_powerset.mpr hHΩ), sub_self, abs_zero]
  rw [h0, mul_zero]

private theorem abs_neg_one_pow_le (n : ℕ) : |(-1 : ℝ) ^ n| ≤ 1 := by
  rw [abs_pow, abs_neg, abs_one, one_pow]

private theorem two_nonneg : (0 : ℝ) ≤ 2 := by norm_num

private theorem tendsto_const_mul_nhds_zero {α : Type*} {f : α → ℝ}
    {l : Filter α} {c : ℝ} (hf : Tendsto f l (nhds 0)) :
    Tendsto (fun x => c * f x) l (nhds 0) :=
  mul_zero c ▸ (tendsto_const_nhds (x := c) (f := l)).mul hf

private theorem tendsto_add_nhds_zero {α : Type*} {f g : α → ℝ}
    {l : Filter α} (hf : Tendsto f l (nhds 0))
    (hg : Tendsto g l (nhds 0)) :
    Tendsto (fun x => f x + g x) l (nhds 0) :=
  add_zero (0 : ℝ) ▸ hf.add hg

/-! ### Small `ahlLayer` sum implies small L1 -/

/-- Layerwise (1.1): a small weighted `ahlLayer` sum yields small
StoppedPrime first-`L` L1, up to model remainder and HL mismatch. -/
theorem shapeL1_actual_add_failure_le_of_small_ahlLayer
    {κ E : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hN : 0 < windowNX X)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega κ X).powerset, ν U = 1)
    (hE : (1 / (windowNX X : ℝ)) *
        ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L ≤ E) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν L +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X) L ≤
      Stopped.failureMass (windowOmega κ X) ν L +
        2 * Stopped.modelRemainder (windowOmega κ X) ν L r +
        2 * E + 2 * hlModelMismatch κ X ν L r := by
  have hmain :=
    shapeL1_actual_add_failure_le_of_ahlLayer hL hr hpar hN hν hmass
  have hmain' :
      Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν L +
          Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X) L ≤
        Stopped.failureMass (windowOmega κ X) ν L +
          2 * Stopped.modelRemainder (windowOmega κ X) ν L r +
          2 *
            ((1 / (windowNX X : ℝ)) *
                ∑ j ∈ Icc L r,
                  ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L +
              hlModelMismatch κ X ν L r) := by
    unfold hlModelMismatch
    exact hmain
  have hblock :
      (1 / (windowNX X : ℝ)) *
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L +
        hlModelMismatch κ X ν L r ≤
        E + hlModelMismatch κ X ν L r :=
    _root_.add_le_add_left hE (hlModelMismatch κ X ν L r)
  have h2b := mul_le_mul_of_nonneg_left hblock two_nonneg
  have hdist :
      (2 : ℝ) * (E + hlModelMismatch κ X ν L r) =
        2 * E + 2 * hlModelMismatch κ X ν L r :=
    mul_add _ _ _
  rw [hdist] at h2b
  exact hmain'.trans ((_root_.add_le_add_right h2b
      (Stopped.failureMass (windowOmega κ X) ν L +
        2 * Stopped.modelRemainder (windowOmega κ X) ν L r)).trans
    (le_of_eq (add_assoc _ _ _).symm))

/-- Small layers give a small named `ahlBudget`. -/
theorem ahlBudget_le_of_ahlLayer_bound {κ d0 B : ℝ} {X : ℕ}
    (hN : 0 < windowNX X) (hB : 0 ≤ B)
    (hA : ∀ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
      ahlLayer κ X j (profileL κ X) ≤ B) :
    ahlBudget κ d0 X ≤
      (1 / (windowNX X : ℝ)) * B *
        ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
          ((j - 1).choose (profileL κ X - 1) : ℝ) := by
  have hahl := ahlBudget_eq_weighted (κ := κ) (d0 := d0) (X := X)
    (ne_of_gt hN)
  rw [hahl]
  have hNℝ : (0 : ℝ) < (windowNX X : ℝ) := Nat.cast_pos.mpr hN
  have hN0 : (0 : ℝ) ≤ 1 / (windowNX X : ℝ) := one_div_nonneg.mpr hNℝ.le
  have hpt :
      ∀ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
        ((j - 1).choose (profileL κ X - 1) : ℝ) *
            ahlLayer κ X j (profileL κ X) ≤
          ((j - 1).choose (profileL κ X - 1) : ℝ) * B := by
    intro j hj
    exact mul_le_mul_of_nonneg_left (hA j hj)
      (Nat.cast_nonneg ((j - 1).choose (profileL κ X - 1)))
  have hsum := sum_le_sum hpt
  have hfac :
      ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
          ((j - 1).choose (profileL κ X - 1) : ℝ) * B =
        B *
          ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
            ((j - 1).choose (profileL κ X - 1) : ℝ) := by
    have hswap : ∀ j,
        ((j - 1).choose (profileL κ X - 1) : ℝ) * B =
          B * ((j - 1).choose (profileL κ X - 1) : ℝ) :=
      fun j => mul_comm _ _
    simp_rw [hswap]
    rw [← mul_sum]
  have hmul :=
    mul_le_mul_of_nonneg_left (hsum.trans (le_of_eq hfac)) hN0
  have hrhs :
      (1 / (windowNX X : ℝ)) *
          (B *
            ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
              ((j - 1).choose (profileL κ X - 1) : ℝ)) =
        (1 / (windowNX X : ℝ)) * B *
          ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
            ((j - 1).choose (profileL κ X - 1) : ℝ) :=
    (mul_assoc _ _ _).symm
  rwa [hrhs] at hmul

/-! ### Named `ahlBudget` implies small adverse budget and L1 -/

theorem adverseBudget_actual_le_of_ahlBudget
    {κ d0 : ℝ} {X : ℕ} {ν : Finset ℕ → ℝ}
    (hN : 0 < windowNX X) :
    Stopped.adverseBudget (windowOmega κ X) (actualConfigMass κ X) ν
        (profileL κ X) (profileR (profileL κ X) d0) ≤
      ahlBudget κ d0 X +
        hlModelMismatch κ X ν (profileL κ X)
          (profileR (profileL κ X) d0) := by
  have hW :=
    adverseBudget_actual_le_of_ahlLayer (κ := κ) (X := X)
      (L := profileL κ X) (r := profileR (profileL κ X) d0) (ν := ν) hN
  have hahl := ahlBudget_eq_weighted (κ := κ) (d0 := d0) (X := X)
    (ne_of_gt hN)
  unfold hlModelMismatch
  rw [hahl]
  exact hW

/-- Combined finite bound: small `ahlBudget` and small model/HL
mismatch imply small first-`L` shape L1 on the profile. -/
theorem shapeL1_actual_add_failure_le_of_ahlBudget
    {κ d0 : ℝ} {X : ℕ} {ν : Finset ℕ → ℝ}
    (hL : 1 ≤ profileL κ X) (hN : 0 < windowNX X)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega κ X).powerset, ν U = 1) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν
          (profileL κ X) +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
          (profileL κ X) ≤
      Stopped.failureMass (windowOmega κ X) ν (profileL κ X) +
        2 * Stopped.modelRemainder (windowOmega κ X) ν (profileL κ X)
          (profileR (profileL κ X) d0) +
        2 * ahlBudget κ d0 X +
        2 * hlModelMismatch κ X ν (profileL κ X)
          (profileR (profileL κ X) d0) := by
  have hmain :=
    stoppedShapeL1_profile_add_failure_le (d0 := d0) hL hN hν hmass
  have hW :=
    adverseBudget_actual_le_of_ahlBudget (κ := κ) (d0 := d0) (X := X)
      (ν := ν) hN
  have hW2 := mul_le_mul_of_nonneg_left hW two_nonneg
  have hdist :
      (2 : ℝ) *
          (ahlBudget κ d0 X +
            hlModelMismatch κ X ν (profileL κ X)
              (profileR (profileL κ X) d0)) =
        2 * ahlBudget κ d0 X +
          2 * hlModelMismatch κ X ν (profileL κ X)
            (profileR (profileL κ X) d0) :=
    mul_add _ _ _
  rw [hdist] at hW2
  exact hmain.trans ((_root_.add_le_add_right hW2
      (Stopped.failureMass (windowOmega κ X) ν (profileL κ X) +
        2 * Stopped.modelRemainder (windowOmega κ X) ν (profileL κ X)
          (profileR (profileL κ X) d0))).trans
    (le_of_eq (add_assoc _ _ _).symm))

theorem shapeL1_actual_add_failure_le_of_ahlBudget_calibrated
    {κ d0 : ℝ} {X : ℕ} {ν : Finset ℕ → ℝ}
    (hL : 1 ≤ profileL κ X) (hN : 0 < windowNX X)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega κ X).powerset, ν U = 1)
    (hq : ∀ H ∈ (windowOmega κ X).powerset,
      Stopped.inclusionMass (windowOmega κ X) ν H =
        rootedMainTerm X H / (windowNX X : ℝ)) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν
          (profileL κ X) +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
          (profileL κ X) ≤
      Stopped.failureMass (windowOmega κ X) ν (profileL κ X) +
        2 * Stopped.modelRemainder (windowOmega κ X) ν (profileL κ X)
          (profileR (profileL κ X) d0) +
        2 * ahlBudget κ d0 X := by
  have hmain :=
    shapeL1_actual_add_failure_le_of_ahlBudget (κ := κ) (d0 := d0)
      (X := X) (ν := ν) hL hN hν hmass
  have hcal :=
    hlModelMismatch_eq_zero (L := profileL κ X)
      (r := profileR (profileL κ X) d0) hN hq
  rw [hcal, mul_zero, add_zero] at hmain
  exact hmain

theorem shapeL1_actual_add_failure_nonneg
    (κ : ℝ) (X : ℕ) (ν : Finset ℕ → ℝ) :
    0 ≤ Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν
          (profileL κ X) +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
          (profileL κ X) := by
  refine add_nonneg ?_ ?_
  · unfold Stopped.shapeL1
    exact sum_nonneg fun _ _ => abs_nonneg _
  · unfold Stopped.failureMass
    exact sum_nonneg fun U _ => actualConfigMass_nonneg κ X U

/-! ### BudgetNorm relative calibration (paper (1.2)) -/

/-- Inclusion-scale relative (1.2) for one adverse layer. -/
theorem adverseLayer_actual_le_rel
    {κ : ℝ} {X L j : ℕ} {ν : Finset ℕ → ℝ} {Z δ : ℝ}
    (hN : 0 < windowNX X) (hZ : 0 < Z) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ H ∈ (windowOmega κ X).powerset, 0 ≤ rootedMainTerm X H)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hrel : ∀ H ∈ (windowOmega κ X).powerset,
      |Stopped.inclusionMass (windowOmega κ X) ν H -
        rootedMainTerm X H / Z| ≤
          δ * (rootedMainTerm X H / Z)) :
    Stopped.adverseLayer (windowOmega κ X) (actualConfigMass κ X) ν L j ≤
      (1 / (windowNX X : ℝ)) * ahlLayer κ X j L +
        ((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
          Stopped.countMoment (windowOmega κ X) ν j := by
  let Ω := windowOmega κ X
  let I := Ω.powerset.filter (fun H => H.card = j)
  let μ := actualConfigMass κ X
  have hNℝ : (0 : ℝ) < (windowNX X : ℝ) := Nat.cast_pos.mpr hN
  have hw : ∀ H ∈ I, 0 ≤ (1 : ℝ) := fun _ _ => zero_le_one
  have hσ : ∀ H ∈ I, |(-1 : ℝ) ^ (j - L + 1)| ≤ 1 :=
    fun _ _ => abs_neg_one_pow_le _
  have hMI : ∀ H ∈ I, 0 ≤ rootedMainTerm X H := fun H hH =>
    hM H (Finset.mem_filter.mp hH).1
  have hqI : ∀ H ∈ I, 0 ≤ Stopped.inclusionMass Ω ν H := by
    intro H _
    unfold Stopped.inclusionMass
    exact sum_nonneg fun U hU => hν U (Finset.mem_filter.mp hU).1
  have hrelI : ∀ H ∈ I,
      |Stopped.inclusionMass Ω ν H - rootedMainTerm X H / Z| ≤
        δ * (rootedMainTerm X H / Z) := fun H hH =>
    hrel H (Finset.mem_filter.mp hH).1
  have hcore :=
    posPart_budget_rel_le (ι := Finset ℕ) I
      (fun _ => (1 : ℝ))
      (fun H => (rootedTupleCount X H : ℝ))
      (fun H => rootedMainTerm X H)
      (fun H => Stopped.inclusionMass Ω ν H)
      (fun _ => (-1 : ℝ) ^ (j - L + 1))
      (N := (windowNX X : ℝ)) (Z := Z) (δ := δ)
      hNℝ hZ hδ0 hδ1 hw hσ hMI hqI hrelI
  have hLHS :
      Stopped.adverseLayer Ω μ ν L j =
        ∑ H ∈ I,
          (((-1 : ℝ) ^ (j - L + 1)) *
            ((rootedTupleCount X H : ℝ) / (windowNX X : ℝ) -
              Stopped.inclusionMass Ω ν H))⁺ := by
    rw [adverseLayer_eq_posPart]
    refine sum_congr rfl fun H hH => ?_
    have hHΩ : H ⊆ Ω := Finset.mem_powerset.mp (Finset.mem_filter.mp hH).1
    rw [inclusionMass_actualConfigMass_div hN hHΩ]
  have hahl :
      ∑ H ∈ I,
          (((-1 : ℝ) ^ (j - L + 1)) *
            ((rootedTupleCount X H : ℝ) - rootedMainTerm X H))⁺ =
        ahlLayer κ X j L := by
    unfold ahlLayer
    rfl
  have hmom :
      ∑ H ∈ I, Stopped.inclusionMass Ω ν H =
        Stopped.countMoment (windowOmega κ X) ν j :=
    (countMoment_eq_sum_inclusionMass Ω ν j).symm
  rw [hLHS]
  simp only [one_mul, hahl, hmom] at hcore
  exact hcore

theorem adverseBudget_actual_le_rel
    {κ : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ} {Z δ : ℝ}
    (hN : 0 < windowNX X) (hZ : 0 < Z) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ H ∈ (windowOmega κ X).powerset, 0 ≤ rootedMainTerm X H)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hrel : ∀ H ∈ (windowOmega κ X).powerset,
      |Stopped.inclusionMass (windowOmega κ X) ν H -
        rootedMainTerm X H / Z| ≤
          δ * (rootedMainTerm X H / Z)) :
    Stopped.adverseBudget (windowOmega κ X) (actualConfigMass κ X) ν L r ≤
      (1 / (windowNX X : ℝ)) *
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L +
        ((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) *
              Stopped.countMoment (windowOmega κ X) ν j := by
  unfold Stopped.adverseBudget
  have hpt : ∀ j ∈ Icc L r,
      ((j - 1).choose (L - 1) : ℝ) *
          Stopped.adverseLayer (windowOmega κ X) (actualConfigMass κ X)
            ν L j ≤
        ((j - 1).choose (L - 1) : ℝ) *
          ((1 / (windowNX X : ℝ)) * ahlLayer κ X j L +
            ((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
              Stopped.countMoment (windowOmega κ X) ν j) := by
    intro j hj
    have hnn : (0 : ℝ) ≤ ((j - 1).choose (L - 1) : ℝ) :=
      Nat.cast_nonneg ((j - 1).choose (L - 1))
    exact mul_le_mul_of_nonneg_left
      (adverseLayer_actual_le_rel hN hZ hδ0 hδ1 hM hν hrel) hnn
  have hsum := sum_le_sum hpt
  refine hsum.trans (le_of_eq ?_)
  have hsplit :
      ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            ((1 / (windowNX X : ℝ)) * ahlLayer κ X j L +
              ((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
                Stopped.countMoment (windowOmega κ X) ν j) =
        ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) *
              ((1 / (windowNX X : ℝ)) * ahlLayer κ X j L) +
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) *
              (((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
                Stopped.countMoment (windowOmega κ X) ν j) := by
    simp_rw [mul_add]
    rw [sum_add_distrib]
  rw [hsplit]
  have hscale :
      ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            ((1 / (windowNX X : ℝ)) * ahlLayer κ X j L) =
        (1 / (windowNX X : ℝ)) *
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L := by
    have hA : ∀ j,
        ((j - 1).choose (L - 1) : ℝ) *
            ((1 / (windowNX X : ℝ)) * ahlLayer κ X j L) =
          (1 / (windowNX X : ℝ)) *
            (((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L) :=
      fun j => mul_left_comm _ _ _
    simp_rw [hA]
    rw [← mul_sum]
  have hcal :
      ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            (((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
              Stopped.countMoment (windowOmega κ X) ν j) =
        ((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) *
              Stopped.countMoment (windowOmega κ X) ν j := by
    have hA : ∀ j,
        ((j - 1).choose (L - 1) : ℝ) *
            (((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
              Stopped.countMoment (windowOmega κ X) ν j) =
          ((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
            (((j - 1).choose (L - 1) : ℝ) *
              Stopped.countMoment (windowOmega κ X) ν j) :=
      fun j => mul_left_comm _ _ _
    simp_rw [hA]
    rw [← mul_sum]
  rw [hscale, hcal]

theorem adverseBudget_actual_le_rel_of_ahlBudget
    {κ d0 : ℝ} {X : ℕ} {ν : Finset ℕ → ℝ} {Z δ : ℝ}
    (hN : 0 < windowNX X) (hZ : 0 < Z) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ H ∈ (windowOmega κ X).powerset, 0 ≤ rootedMainTerm X H)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hrel : ∀ H ∈ (windowOmega κ X).powerset,
      |Stopped.inclusionMass (windowOmega κ X) ν H -
        rootedMainTerm X H / Z| ≤
          δ * (rootedMainTerm X H / Z)) :
    Stopped.adverseBudget (windowOmega κ X) (actualConfigMass κ X) ν
        (profileL κ X) (profileR (profileL κ X) d0) ≤
      ahlBudget κ d0 X +
        ((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
          ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
            ((j - 1).choose (profileL κ X - 1) : ℝ) *
              Stopped.countMoment (windowOmega κ X) ν j := by
  have hW :=
    adverseBudget_actual_le_rel (κ := κ) (X := X) (L := profileL κ X)
      (r := profileR (profileL κ X) d0) (ν := ν) (Z := Z) (δ := δ)
      hN hZ hδ0 hδ1 hM hν hrel
  have hahl := ahlBudget_eq_weighted (κ := κ) (d0 := d0) (X := X)
    (ne_of_gt hN)
  rwa [← hahl] at hW

theorem shapeL1_actual_add_failure_le_of_ahlBudget_rel
    {κ d0 : ℝ} {X : ℕ} {ν : Finset ℕ → ℝ} {Z δ : ℝ}
    (hL : 1 ≤ profileL κ X) (hN : 0 < windowNX X)
    (hZ : 0 < Z) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega κ X).powerset, ν U = 1)
    (hM : ∀ H ∈ (windowOmega κ X).powerset, 0 ≤ rootedMainTerm X H)
    (hrel : ∀ H ∈ (windowOmega κ X).powerset,
      |Stopped.inclusionMass (windowOmega κ X) ν H -
        rootedMainTerm X H / Z| ≤
          δ * (rootedMainTerm X H / Z)) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν
          (profileL κ X) +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
          (profileL κ X) ≤
      Stopped.failureMass (windowOmega κ X) ν (profileL κ X) +
        2 * Stopped.modelRemainder (windowOmega κ X) ν (profileL κ X)
          (profileR (profileL κ X) d0) +
        2 * ahlBudget κ d0 X +
        2 * (((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
          ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
            ((j - 1).choose (profileL κ X - 1) : ℝ) *
              Stopped.countMoment (windowOmega κ X) ν j) := by
  have hmain :=
    stoppedShapeL1_profile_add_failure_le (d0 := d0) hL hN hν hmass
  have hW :=
    adverseBudget_actual_le_rel_of_ahlBudget (κ := κ) (d0 := d0)
      (X := X) (ν := ν) (Z := Z) (δ := δ) hN hZ hδ0 hδ1 hM hν hrel
  have hW2 := mul_le_mul_of_nonneg_left hW two_nonneg
  have hdist :
      (2 : ℝ) *
          (ahlBudget κ d0 X +
            ((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
              ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
                ((j - 1).choose (profileL κ X - 1) : ℝ) *
                  Stopped.countMoment (windowOmega κ X) ν j) =
        2 * ahlBudget κ d0 X +
          2 * (((|Z / (windowNX X : ℝ) - 1| + δ) / (1 - δ)) *
            ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
              ((j - 1).choose (profileL κ X - 1) : ℝ) *
                Stopped.countMoment (windowOmega κ X) ν j) :=
    mul_add _ _ _
  rw [hdist] at hW2
  exact hmain.trans ((_root_.add_le_add_right hW2
      (Stopped.failureMass (windowOmega κ X) ν (profileL κ X) +
        2 * Stopped.modelRemainder (windowOmega κ X) ν (profileL κ X)
          (profileR (profileL κ X) d0))).trans
    (le_of_eq (add_assoc _ _ _).symm))

/-! ### First-L observations -/

theorem abs_endpointObs_actual_sub_le_of_ahlBudget
    {κ d0 : ℝ} {X : ℕ} {ν : Finset ℕ → ℝ} {phi : List ℕ → ℝ}
    (hL : 1 ≤ profileL κ X) (hN : 0 < windowNX X)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega κ X).powerset, ν U = 1)
    (hφ : ∀ t, |phi t| ≤ 1) :
    |∑ U ∈ (windowOmega κ X).powerset,
          actualConfigMass κ X U *
            endpointObs (profileL κ X) phi U -
        ∑ K ∈ (windowOmega κ X).powerset.filter
            (fun K => K.card = profileL κ X),
          Stopped.shortShapeMass (windowOmega κ X) ν (profileL κ X) K *
            phi (K.sort (· ≤ ·))| ≤
      Stopped.failureMass (windowOmega κ X) ν (profileL κ X) +
        2 * Stopped.modelRemainder (windowOmega κ X) ν (profileL κ X)
          (profileR (profileL κ X) d0) +
        2 * ahlBudget κ d0 X +
        2 * hlModelMismatch κ X ν (profileL κ X)
          (profileR (profileL κ X) d0) := by
  let Ω := windowOmega κ X
  let μ := actualConfigMass κ X
  let L := profileL κ X
  let φ : Finset ℕ → ℝ := fun K => phi (K.sort (· ≤ ·))
  have hφK : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), |φ K| ≤ 1 :=
    fun K _ => hφ _
  have hψ : ∀ U ∈ Ω.powerset, |(0 : ℝ)| ≤ 1 := fun _ _ => by
    rw [abs_zero]
    exact zero_le_one
  have hobs :
      ∑ U ∈ Ω.powerset, μ U * endpointObs L phi U =
        ∑ U ∈ Ω.powerset,
          μ U * (if L ≤ U.card then φ (Stopped.firstL L U) else 0) := by
    refine sum_congr rfl fun U _ => ?_
    rw [endpointObs_eq_stoppedValue, Stopped.stoppedValue]
  have heval :=
    abs_stopped_eval_actual_sub_le (κ := κ) (X := X) (L := L) (ν := ν)
      (φ := φ) (ψ := fun _ => (0 : ℝ)) hN hφK hψ
  have hshape :=
    shapeL1_actual_add_failure_le_of_ahlBudget (d0 := d0) hL hN hν hmass
  rw [hobs]
  exact heval.trans hshape

/-! ### Limit form: `AHL` plus vanishing remainder implies vanishing L1 -/

theorem tendsto_shapeL1_actual_add_failure_of_AHL
    {κ d0 : ℝ} (hAHL : AHL κ d0) (ν : ℕ → Finset ℕ → ℝ)
    (hL : ∀ᶠ X : ℕ in atTop, 1 ≤ profileL κ X)
    (hN : ∀ᶠ X : ℕ in atTop, 0 < windowNX X)
    (hν : ∀ᶠ X : ℕ in atTop,
      ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν X U)
    (hmass : ∀ᶠ X : ℕ in atTop,
      ∑ U ∈ (windowOmega κ X).powerset, ν X U = 1)
    (hfail : Tendsto (fun X : ℕ =>
        Stopped.failureMass (windowOmega κ X) (ν X) (profileL κ X))
      atTop (nhds 0))
    (hR : Tendsto (fun X : ℕ =>
        Stopped.modelRemainder (windowOmega κ X) (ν X)
          (profileL κ X) (profileR (profileL κ X) d0))
      atTop (nhds 0))
    (hcal : Tendsto (fun X : ℕ =>
        hlModelMismatch κ X (ν X) (profileL κ X)
          (profileR (profileL κ X) d0))
      atTop (nhds 0)) :
    Tendsto (fun X : ℕ =>
      Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) (ν X)
          (profileL κ X) +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
          (profileL κ X))
      atTop (nhds 0) := by
  have hAHL' : Tendsto (fun X : ℕ => ahlBudget κ d0 X) atTop (nhds 0) :=
    hAHL
  have h2R := tendsto_const_mul_nhds_zero (c := (2 : ℝ)) hR
  have h2E := tendsto_const_mul_nhds_zero (c := (2 : ℝ)) hAHL'
  have h2M := tendsto_const_mul_nhds_zero (c := (2 : ℝ)) hcal
  have hupper :=
    tendsto_add_nhds_zero
      (tendsto_add_nhds_zero (tendsto_add_nhds_zero hfail h2R) h2E) h2M
  have hle : ∀ᶠ X : ℕ in atTop,
      Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) (ν X)
            (profileL κ X) +
          Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
            (profileL κ X) ≤
        Stopped.failureMass (windowOmega κ X) (ν X) (profileL κ X) +
          2 * Stopped.modelRemainder (windowOmega κ X) (ν X)
            (profileL κ X) (profileR (profileL κ X) d0) +
          2 * ahlBudget κ d0 X +
          2 * hlModelMismatch κ X (ν X) (profileL κ X)
            (profileR (profileL κ X) d0) := by
    filter_upwards [hL, hN, hν, hmass] with X hL' hN' hν' hmass'
    exact shapeL1_actual_add_failure_le_of_ahlBudget (d0 := d0) hL' hN' hν' hmass'
  exact squeeze_zero'
    (Eventually.of_forall fun X =>
      shapeL1_actual_add_failure_nonneg κ X (ν X))
    hle hupper

end

end PrimeGapNormality.Prime
