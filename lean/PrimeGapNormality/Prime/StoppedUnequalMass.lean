import PrimeGapNormality.Prime.Stopped
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite stopped comparison for unequal nonnegative masses

The equal-mass identity behind `stoppedShapeL1_add_failure_le` is
private in `Stopped.lean`. This module re-proves the mass partition
from the public definitions `shortShapeMass`, `failureMass` and
`shapeL1`, keeps the exact deficit `(mass μ − mass ν)`, and restores
the one-sided bound on positive parts by reducing to the existing
equal-mass theorem (mass placed on `∅` is invisible to first-`L`
shapes, nonempty inclusions, and `countEnvelope L r 0`).

Probability laws (total mass 1) recover the old inequality.

Does not change AHL error weights. Does not import `StatisticalPack`.

Source: `rounds/round106/01_gpt_proof_digestion_audit.md` Checkpoint 1, §3;
`rounds/round105/00_grok_repair_priorities.md` F.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime.Stopped

open Finset

set_option maxHeartbeats 800000

variable {α : Type*} [DecidableEq α] [LinearOrder α]

/-! ### Mass partition from public definitions -/

private theorem firstL_mem_Lshapes {Ω U : Finset α} {L : ℕ}
    (hU : U ⊆ Ω) (hLcard : L ≤ U.card) :
    firstL L U ∈ Ω.powerset.filter (fun K => K.card = L) :=
  mem_filter.mpr ⟨mem_powerset.mpr (firstL_subset.trans hU), firstL_card hLcard⟩

/-- Source: `rounds/round106/01_gpt_proof_digestion_audit.md` Checkpoint 1;
`Stopped.shortShapeMass`.
Contract: API
Audit: GREEN -/
theorem sum_shortShapeMass_eq {Ω : Finset α} {μ : Finset α → ℝ} {L : ℕ} :
    ∑ K ∈ Ω.powerset.filter (fun K => K.card = L), shortShapeMass Ω μ L K =
      ∑ U ∈ Ω.powerset.filter (fun U => L ≤ U.card), μ U := by
  simp only [shortShapeMass]
  rw [sum_comm]
  have hpt : ∀ U ∈ Ω.powerset,
      ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          (if L ≤ U.card ∧ firstL L U = K then μ U else 0) =
        if L ≤ U.card then μ U else 0 := by
    intro U hU
    have hUΩ : U ⊆ Ω := mem_powerset.mp hU
    by_cases hcard : L ≤ U.card
    · have hmem := firstL_mem_Lshapes hUΩ hcard
      rw [sum_eq_single (firstL L U)]
      · simp [hcard]
      · intro K _hK hne
        simp [hcard, hne.symm]
      · intro hnot
        exact (hnot hmem).elim
    · simp [hcard]
  rw [sum_congr rfl hpt, sum_filter]

/-- Public form of the private `sum_short_add_failure`.

Source: `rounds/round106/01_gpt_proof_digestion_audit.md` Checkpoint 1;
`Stopped.shortShapeMass`, `Stopped.failureMass`.
Contract: API
Audit: GREEN -/
theorem shortShapeMass_add_failureMass {Ω : Finset α} {μ : Finset α → ℝ}
    {L : ℕ} :
    ∑ K ∈ Ω.powerset.filter (fun K => K.card = L), shortShapeMass Ω μ L K +
        failureMass Ω μ L =
      ∑ U ∈ Ω.powerset, μ U := by
  rw [sum_shortShapeMass_eq, failureMass]
  have h :=
    sum_filter_add_sum_filter_not (s := Ω.powerset) (p := fun U => L ≤ U.card)
      (f := μ)
  have hset :
      Ω.powerset.filter (fun U => ¬ L ≤ U.card) =
        Ω.powerset.filter (fun U => U.card < L) := by
    ext U
    simp
  rwa [hset] at h

private theorem abs_eq_two_max_sub (x : ℝ) : |x| = 2 * max x 0 - x := by
  rcases le_total x 0 with hx | hx
  · rw [abs_of_nonpos hx, max_eq_right hx]
    ring
  · rw [abs_of_nonneg hx, max_eq_left hx]
    ring

/-- Exact finite mass identity, no equal-mass hypothesis.

`|a − b| = 2 [b − a]₊ + (a − b)`, and the first-`L` shapes sum to
`mass − failureMass`.

Source: `rounds/round106/01_gpt_proof_digestion_audit.md` Checkpoint 1.
Contract: API
Audit: GREEN -/
theorem shapeL1_add_failureMass_eq {Ω : Finset α} {μ ν : Finset α → ℝ}
    {L : ℕ} :
    shapeL1 Ω μ ν L + failureMass Ω μ L =
      2 * ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            max (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) 0 +
        failureMass Ω ν L +
        ((∑ U ∈ Ω.powerset, μ U) - (∑ U ∈ Ω.powerset, ν U)) := by
  unfold shapeL1
  have habs : ∀ K,
      |shortShapeMass Ω μ L K - shortShapeMass Ω ν L K| =
        2 * max (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) 0 -
          (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) := by
    intro K
    simpa [abs_sub_comm] using
      abs_eq_two_max_sub (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K)
  rw [sum_congr rfl fun K _ => habs K, sum_sub_distrib, ← mul_sum]
  have hdiff :
      ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) =
        (∑ U ∈ Ω.powerset, ν U - failureMass Ω ν L) -
          (∑ U ∈ Ω.powerset, μ U - failureMass Ω μ L) := by
    rw [sum_sub_distrib]
    have hμ := shortShapeMass_add_failureMass (μ := μ) (Ω := Ω) (L := L)
    have hν := shortShapeMass_add_failureMass (μ := ν) (Ω := Ω) (L := L)
    linarith
  rw [hdiff]
  ring

/-! ### Empty-set mass that equalizes totals without changing shapes -/

private noncomputable def addEmptyMass (μ : Finset α → ℝ) (c : ℝ) :
    Finset α → ℝ :=
  fun U => if U = ∅ then μ ∅ + c else μ U

private theorem empty_mem_powerset (Ω : Finset α) :
    (∅ : Finset α) ∈ Ω.powerset :=
  mem_powerset.mpr (empty_subset _)

private theorem empty_mem_failure {Ω : Finset α} {L : ℕ} (hL : 1 ≤ L) :
    (∅ : Finset α) ∈ Ω.powerset.filter (fun U => U.card < L) := by
  refine mem_filter.mpr ⟨empty_mem_powerset Ω, ?_⟩
  simp only [card_empty]
  exact lt_of_lt_of_le Nat.zero_lt_one hL

private theorem addEmptyMass_eq_add (μ : Finset α → ℝ) (c : ℝ) (U : Finset α) :
    addEmptyMass μ c U = μ U + if U = ∅ then c else 0 := by
  unfold addEmptyMass
  by_cases h : U = ∅ <;> simp [h]

private theorem addEmptyMass_nonneg {Ω : Finset α} {μ : Finset α → ℝ} {c : ℝ}
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U) (hc : 0 ≤ c) :
    ∀ U ∈ Ω.powerset, 0 ≤ addEmptyMass μ c U := by
  intro U hU
  rw [addEmptyMass_eq_add]
  have hc0 : 0 ≤ (if U = ∅ then c else 0) := by
    by_cases h : U = ∅ <;> simp [h, hc]
  exact add_nonneg (hμ U hU) hc0

private theorem sum_addEmptyMass (Ω : Finset α) (μ : Finset α → ℝ) (c : ℝ) :
    ∑ U ∈ Ω.powerset, addEmptyMass μ c U =
      ∑ U ∈ Ω.powerset, μ U + c := by
  rw [sum_congr rfl fun U _ => addEmptyMass_eq_add μ c U]
  rw [sum_add_distrib, sum_ite_eq', if_pos (empty_mem_powerset Ω)]

private theorem add_max_sub_balance (a b : ℝ) :
    a + max (b - a) 0 = b + max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

private theorem card_pos_of_ge_L {U : Finset α} {L : ℕ}
    (hL : 1 ≤ L) (hcard : L ≤ U.card) : U ≠ ∅ :=
  (card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one (le_trans hL hcard))).ne_empty

private theorem shortShapeMass_addEmptyMass {Ω : Finset α} {μ : Finset α → ℝ}
    {L : ℕ} {K : Finset α} {c : ℝ} (hL : 1 ≤ L) :
    shortShapeMass Ω (addEmptyMass μ c) L K = shortShapeMass Ω μ L K := by
  unfold shortShapeMass
  refine sum_congr rfl fun U _hU => ?_
  by_cases hcard : L ≤ U.card
  · have hμU : addEmptyMass μ c U = μ U := by
      rw [addEmptyMass_eq_add, if_neg (card_pos_of_ge_L hL hcard), add_zero]
    by_cases hKeq : firstL L U = K
    · rw [if_pos ⟨hcard, hKeq⟩, if_pos ⟨hcard, hKeq⟩, hμU]
    · rw [if_neg (mt And.right hKeq), if_neg (mt And.right hKeq)]
  · rw [if_neg (mt And.left hcard), if_neg (mt And.left hcard)]

private theorem failureMass_addEmptyMass {Ω : Finset α} {μ : Finset α → ℝ}
    {L : ℕ} {c : ℝ} (hL : 1 ≤ L) :
    failureMass Ω (addEmptyMass μ c) L = failureMass Ω μ L + c := by
  unfold failureMass
  rw [sum_congr rfl fun U _ => addEmptyMass_eq_add μ c U]
  rw [sum_add_distrib, sum_ite_eq', if_pos (empty_mem_failure hL)]

private theorem inclusionMass_addEmptyMass {Ω : Finset α} {μ : Finset α → ℝ}
    {H : Finset α} {c : ℝ} (hH : H.Nonempty) :
    inclusionMass Ω (addEmptyMass μ c) H = inclusionMass Ω μ H := by
  unfold inclusionMass addEmptyMass
  refine sum_congr rfl fun U hU => ?_
  have hHU : H ⊆ U := (mem_filter.mp hU).2
  have hne : U ≠ ∅ := by
    intro hempty
    rw [hempty] at hHU
    obtain ⟨x, hx⟩ := hH
    exact (notMem_empty x) (hHU hx)
  rw [if_neg hne]

private theorem adverseLayer_addEmptyMass {Ω : Finset α} {μ ν : Finset α → ℝ}
    {L j : ℕ} {cμ cν : ℝ} (hj : 1 ≤ j) :
    adverseLayer Ω (addEmptyMass μ cμ) (addEmptyMass ν cν) L j =
      adverseLayer Ω μ ν L j := by
  unfold adverseLayer
  refine sum_congr rfl fun H hH => ?_
  have hcard : H.card = j := (mem_filter.mp hH).2
  have hne : H.Nonempty := by
    have hpos : 0 < H.card := by
      rw [hcard]
      exact lt_of_lt_of_le Nat.zero_lt_one hj
    exact card_pos.mp hpos
  rw [inclusionMass_addEmptyMass hne, inclusionMass_addEmptyMass hne]

private theorem adverseBudget_addEmptyMass {Ω : Finset α} {μ ν : Finset α → ℝ}
    {L r : ℕ} {cμ cν : ℝ} (hL : 1 ≤ L) (_hr : L ≤ r) :
    adverseBudget Ω (addEmptyMass μ cμ) (addEmptyMass ν cν) L r =
      adverseBudget Ω μ ν L r := by
  unfold adverseBudget
  refine sum_congr rfl fun j hj => ?_
  have hjL : 1 ≤ j := by
    have := mem_Icc.mp hj
    exact le_trans hL this.1
  rw [adverseLayer_addEmptyMass hjL]

private theorem countEnvelope_card_zero (L r : ℕ) :
    countEnvelope L r 0 = 0 := by
  unfold countEnvelope
  have hempty : Icc (r + 1) 0 = ∅ :=
    Icc_eq_empty_iff.mpr (Nat.not_succ_le_zero r)
  rw [hempty]
  simp

private theorem modelRemainder_addEmptyMass {Ω : Finset α} {ν : Finset α → ℝ}
    {L r : ℕ} {c : ℝ} :
    modelRemainder Ω (addEmptyMass ν c) L r = modelRemainder Ω ν L r := by
  unfold modelRemainder
  have henv : countEnvelope L r 0 = 0 := countEnvelope_card_zero L r
  have hterm : ∀ U,
      addEmptyMass ν c U * countEnvelope L r U.card =
        ν U * countEnvelope L r U.card +
          if U = ∅ then c * countEnvelope L r 0 else 0 := by
    intro U
    rw [addEmptyMass_eq_add, add_mul]
    by_cases hU : U = ∅ <;> simp [hU]
  rw [sum_congr rfl fun U _ => hterm U, sum_add_distrib, sum_ite_eq',
    if_pos (empty_mem_powerset Ω), henv, mul_zero, add_zero]

/-- One-sided bound on first-`L` positive parts. Same statement as the
private `def_le_budget`, obtained by equalizing totals on `∅` and
applying `stoppedShapeL1_add_failure_le`.

Source: `rounds/round106/01_gpt_proof_digestion_audit.md` §3;
`Stopped.stoppedShapeL1_add_failure_le`.
Contract: API
Audit: GREEN -/
theorem sum_posPart_shortShapeMass_le {Ω : Finset α} {μ ν : Finset α → ℝ}
    {L r : ℕ} (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U) :
    ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        max (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) 0 ≤
      adverseBudget Ω μ ν L r + modelRemainder Ω ν L r := by
  let δμ : ℝ :=
    max ((∑ U ∈ Ω.powerset, ν U) - (∑ U ∈ Ω.powerset, μ U)) 0
  let δν : ℝ :=
    max ((∑ U ∈ Ω.powerset, μ U) - (∑ U ∈ Ω.powerset, ν U)) 0
  let μ' : Finset α → ℝ := addEmptyMass μ δμ
  let ν' : Finset α → ℝ := addEmptyMass ν δν
  have hδμ : 0 ≤ δμ := le_max_right _ _
  have hδν : 0 ≤ δν := le_max_right _ _
  have hμnn : ∀ U ∈ Ω.powerset, 0 ≤ μ' U := by
    dsimp [μ']
    exact addEmptyMass_nonneg hμ hδμ
  have hνnn : ∀ U ∈ Ω.powerset, 0 ≤ ν' U := by
    dsimp [ν']
    exact addEmptyMass_nonneg hν hδν
  have hmass : ∑ U ∈ Ω.powerset, μ' U = ∑ U ∈ Ω.powerset, ν' U := by
    dsimp [μ', ν']
    rw [sum_addEmptyMass, sum_addEmptyMass]
    exact add_max_sub_balance _ _
  have hpub :=
    stoppedShapeL1_add_failure_le (Ω := Ω) (μ := μ') (ν := ν') (L := L)
      (r := r) hL hr hpar hμnn hνnn hmass
  have hid := shapeL1_add_failureMass_eq (Ω := Ω) (μ := μ') (ν := ν') (L := L)
  have hid0 :
      shapeL1 Ω μ' ν' L + failureMass Ω μ' L =
        2 *
            ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
              max (shortShapeMass Ω ν' L K - shortShapeMass Ω μ' L K) 0 +
          failureMass Ω ν' L := by
    linarith [hid, hmass]
  have h2def :
      2 *
          ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            max (shortShapeMass Ω ν' L K - shortShapeMass Ω μ' L K) 0 ≤
        2 * modelRemainder Ω ν' L r + 2 * adverseBudget Ω μ' ν' L r := by
    linarith [hpub, hid0]
  have hshape :
      ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          max (shortShapeMass Ω ν' L K - shortShapeMass Ω μ' L K) 0 =
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          max (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) 0 := by
    refine sum_congr rfl fun K _ => ?_
    dsimp [μ', ν']
    rw [shortShapeMass_addEmptyMass hL, shortShapeMass_addEmptyMass hL]
  have hR : modelRemainder Ω ν' L r = modelRemainder Ω ν L r := by
    dsimp [ν']
    exact modelRemainder_addEmptyMass
  have hW : adverseBudget Ω μ' ν' L r = adverseBudget Ω μ ν L r := by
    dsimp [μ', ν']
    exact adverseBudget_addEmptyMass hL hr
  have hmul :
      (2 : ℝ) *
          ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            max (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) 0 ≤
        (2 : ℝ) * (adverseBudget Ω μ ν L r + modelRemainder Ω ν L r) := by
    rw [hshape, hR, hW] at h2def
    linarith [h2def]
  exact le_of_mul_le_mul_left hmul (by norm_num : (0 : ℝ) < 2)

/-- Finite stopped comparison with possibly unequal total masses.

Source: `rounds/round106/01_gpt_proof_digestion_audit.md` (U1);
`rounds/round105/00_grok_repair_priorities.md` F.
Contract: API
Audit: GREEN -/
theorem stoppedShapeL1_add_failure_le_unequalMass
    {Ω : Finset α} {μ ν : Finset α → ℝ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U) :
    shapeL1 Ω μ ν L + failureMass Ω μ L
      ≤ failureMass Ω ν L
        + 2 * modelRemainder Ω ν L r
        + 2 * adverseBudget Ω μ ν L r
        + |(∑ U ∈ Ω.powerset, μ U) - (∑ U ∈ Ω.powerset, ν U)| := by
  have hid := shapeL1_add_failureMass_eq (Ω := Ω) (μ := μ) (ν := ν) (L := L)
  have hdef :=
    sum_posPart_shortShapeMass_le (Ω := Ω) (μ := μ) (ν := ν) (L := L)
      (r := r) hL hr hpar hμ hν
  have hmass :
      (∑ U ∈ Ω.powerset, μ U) - (∑ U ∈ Ω.powerset, ν U) ≤
        |(∑ U ∈ Ω.powerset, μ U) - (∑ U ∈ Ω.powerset, ν U)| :=
    le_abs_self _
  have h2 :
      2 *
          ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            max (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) 0 ≤
        2 * (adverseBudget Ω μ ν L r + modelRemainder Ω ν L r) :=
    mul_le_mul_of_nonneg_left hdef (by norm_num)
  linarith

/-- Equal total mass recovers `stoppedShapeL1_add_failure_le`.

Source: `rounds/round106/01_gpt_proof_digestion_audit.md` Checkpoint 1.
Contract: API
Audit: GREEN -/
theorem stoppedShapeL1_add_failure_le_of_eqMass
    {Ω : Finset α} {μ ν : Finset α → ℝ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ Ω.powerset, μ U = ∑ U ∈ Ω.powerset, ν U) :
    shapeL1 Ω μ ν L + failureMass Ω μ L
      ≤ failureMass Ω ν L
        + 2 * modelRemainder Ω ν L r
        + 2 * adverseBudget Ω μ ν L r := by
  have h :=
    stoppedShapeL1_add_failure_le_unequalMass (Ω := Ω) (μ := μ) (ν := ν)
      (L := L) (r := r) hL hr hpar hμ hν
  simpa [hmass, sub_self, abs_zero, add_zero] using h

/-- Probability measures (nonnegative, total mass 1) reduce to the old
inequality.

Source: `rounds/round106/01_gpt_proof_digestion_audit.md` Checkpoint 1.
Contract: API
Audit: GREEN -/
theorem stoppedShapeL1_add_failure_le_of_mass_one
    {Ω : Finset α} {μ ν : Finset α → ℝ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U)
    (hμ1 : ∑ U ∈ Ω.powerset, μ U = 1)
    (hν1 : ∑ U ∈ Ω.powerset, ν U = 1) :
    shapeL1 Ω μ ν L + failureMass Ω μ L
      ≤ failureMass Ω ν L
        + 2 * modelRemainder Ω ν L r
        + 2 * adverseBudget Ω μ ν L r :=
  stoppedShapeL1_add_failure_le_of_eqMass hL hr hpar hμ hν
    (hμ1.trans hν1.symm)

end PrimeGapNormality.Prime.Stopped
