import PrimeGapNormality.Prime.Stopped
import PrimeGapNormality.Prime.BudgetNorm
import PrimeGapNormality.Prime.MobiusEndpoint
import PrimeGapNormality.Prime.EndAPI
import PrimeGapNormality.Prime.Hypotheses
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Function
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Prime-window instance of the finite stopped transfer

Wires `Stopped.stoppedShapeL1_add_failure_le` to EndAPI window objects.
`Ω = windowOmega`. The actual configuration mass `actualConfigMass` is
the empirical law of rooted prime patterns; its inclusion masses are
`rootedTupleCount / N_X`. The model `ν` remains a parameter.

Does not prove S, PNT calibration rates, or Kuperberg ⇒ AHL.

Source: `rounds/round99/01_grok_transfer_contract.md` (5.1);
`rounds/round103/07_grok_minimal_budget_small_addendum.md` (1.1);
`rounds/round104/13_gpt_paper_v0_3.tex` `lem:stopped`, (eq:normalizedbudget);
`lean/PrimeGapNormality/Prime/EndAPI.lean`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 800000

/-! ### Bridge between Stopped and MobiusEndpoint -/

/-- Stopped inclusion masses match the endpoint inclusion probabilities. -/
theorem inclusionMass_eq_inclusionProb (Ω : Finset ℕ) (μ : Finset ℕ → ℝ)
    (H : Finset ℕ) :
    Stopped.inclusionMass Ω μ H = inclusionProb Ω μ H := by
  unfold Stopped.inclusionMass inclusionProb
  rw [sum_filter]

/-- Stopped count moments match the endpoint inclusion moments. -/
theorem countMoment_eq_inclusionMoment (Ω : Finset ℕ) (μ : Finset ℕ → ℝ)
    (j : ℕ) :
    Stopped.countMoment Ω μ j = inclusionMoment Ω μ j :=
  rfl

theorem countMoment_eq_sum_inclusionMass (Ω : Finset ℕ) (μ : Finset ℕ → ℝ)
    (j : ℕ) :
    Stopped.countMoment Ω μ j =
      ∑ H ∈ Ω.powerset.filter (fun H => H.card = j),
        Stopped.inclusionMass Ω μ H := by
  rw [countMoment_eq_inclusionMoment, inclusionMoment_eq_sum_inclusionProb]
  exact sum_congr rfl fun H _ => (inclusionMass_eq_inclusionProb Ω μ H).symm

private theorem max_eq_posPart (x : ℝ) : max x 0 = x⁺ := rfl

private theorem abs_neg_one_pow_le (n : ℕ) : |(-1 : ℝ) ^ n| ≤ 1 := by
  rw [abs_pow, abs_neg, abs_one, one_pow]

private theorem take_sort_nodup (L : ℕ) (U : Finset ℕ) :
    ((U.sort (· ≤ ·)).take L).Nodup :=
  (U.sort_nodup (· ≤ ·)).sublist (List.take_sublist L _)

private theorem firstL_sort_take {L : ℕ} {U : Finset ℕ} (_h : L ≤ U.card) :
    (Stopped.firstL L U).sort (· ≤ ·) = (U.sort (· ≤ ·)).take L := by
  have hnd := take_sort_nodup L U
  have hpw : ((U.sort (· ≤ ·)).take L).Pairwise (· ≤ ·) :=
    (pairwise_sort U (· ≤ ·)).take
  exact (List.toFinset_sort (· ≤ ·) hnd).mpr hpw

/-- Endpoint list observation is the Stopped first-`L` value. -/
theorem endpointObs_eq_stoppedValue (L : ℕ) (phi : List ℕ → ℝ)
    (U : Finset ℕ) :
    endpointObs L phi U =
      Stopped.stoppedValue L (fun K => phi (K.sort (· ≤ ·))) U := by
  unfold endpointObs Stopped.stoppedValue
  by_cases h : L ≤ U.card
  · have hnot : ¬ U.card < L := not_lt.mpr h
    rw [if_neg hnot, if_pos h]
    change phi ((U.sort (· ≤ ·)).take L) =
      phi ((Stopped.firstL L U).sort (· ≤ ·))
    rw [firstL_sort_take h]
  · have hlt : U.card < L := Nat.not_le.mp h
    rw [if_pos hlt, if_neg h]

/-! ### Window prime counts -/

private theorem primeCounting_eq_card_range (n : ℕ) :
    Nat.primeCounting n = ((range (n + 1)).filter Nat.Prime).card := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]

private theorem range_sdiff_eq_Ioc (X : ℕ) :
    range (2 * X + 1) \ range (X + 1) = Ioc X (2 * X) := by
  ext n
  simp only [mem_sdiff, mem_range, mem_Ioc]
  constructor
  · intro h
    exact ⟨Nat.succ_le_iff.mp (Nat.not_lt.mp h.2), Nat.lt_succ_iff.mp h.1⟩
  · intro h
    exact ⟨Nat.lt_succ_of_le h.2, Nat.not_lt.mpr (Nat.succ_le_of_lt h.1)⟩

private theorem filter_sdiff_eq {α : Type*} [DecidableEq α] (s t : Finset α)
    (P : α → Prop) [DecidablePred P] :
    (s \ t).filter P = s.filter P \ t.filter P := by
  ext x
  constructor
  · intro hx
    have hstP : x ∈ s \ t ∧ P x := mem_filter.mp hx
    have hst : x ∈ s ∧ x ∉ t := mem_sdiff.mp hstP.1
    exact mem_sdiff.mpr
      ⟨mem_filter.mpr ⟨hst.1, hstP.2⟩,
        fun ht => hst.2 (mem_filter.mp ht).1⟩
  · intro hx
    have hstP : x ∈ s.filter P ∧ x ∉ t.filter P := mem_sdiff.mp hx
    have hsP : x ∈ s ∧ P x := mem_filter.mp hstP.1
    refine mem_filter.mpr
      ⟨mem_sdiff.mpr ⟨hsP.1, fun ht => hstP.2 (mem_filter.mpr ⟨ht, hsP.2⟩)⟩, hsP.2⟩

theorem windowNX_eq_card_primes (X : ℕ) :
    windowNX X = ((Ioc X (2 * X)).filter Nat.Prime).card := by
  unfold windowNX
  rw [primeCounting_eq_card_range, primeCounting_eq_card_range]
  have hsub : (range (X + 1)).filter Nat.Prime ⊆
      (range (2 * X + 1)).filter Nat.Prime := by
    intro n hn
    have hn' := mem_filter.mp hn
    refine mem_filter.mpr ⟨?_, hn'.2⟩
    rw [mem_range] at hn' ⊢
    omega
  rw [← card_sdiff_of_subset hsub, ← filter_sdiff_eq, range_sdiff_eq_Ioc]

/-! ### Actual rooted configuration mass -/

/-- Prime pattern of a root `n` inside `Ω_X`. -/
noncomputable def rootedPattern (κ : ℝ) (X n : ℕ) : Finset ℕ :=
  (windowOmega κ X).filter (fun h => Nat.Prime (n + h))

/-- Unnormalised count of roots with exact window pattern `U`. -/
noncomputable def actualPatternCount (κ : ℝ) (X : ℕ) (U : Finset ℕ) : ℕ :=
  ((Ioc X (2 * X)).filter
      fun n => Nat.Prime n ∧ rootedPattern κ X n = U).card

/-- Empirical configuration mass on subsets of `Ω_X`.

Inclusion masses of this law are `rootedTupleCount / N_X`. -/
noncomputable def actualConfigMass (κ : ℝ) (X : ℕ) (U : Finset ℕ) : ℝ :=
  if windowNX X = 0 then 0
  else (actualPatternCount κ X U : ℝ) / (windowNX X : ℝ)

/-- Paper actual inclusion probability `p_H = C_X(H)/N_X`. -/
noncomputable def actualInclusion (X : ℕ) (H : Finset ℕ) : ℝ :=
  if windowNX X = 0 then 0
  else (rootedTupleCount X H : ℝ) / (windowNX X : ℝ)

theorem actualConfigMass_nonneg (κ : ℝ) (X : ℕ) (U : Finset ℕ) :
    0 ≤ actualConfigMass κ X U := by
  unfold actualConfigMass
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem actualInclusion_eq_div {X : ℕ} (H : Finset ℕ)
    (hN : windowNX X ≠ 0) :
    actualInclusion X H = (rootedTupleCount X H : ℝ) / (windowNX X : ℝ) := by
  unfold actualInclusion
  rw [if_neg hN]

private theorem rootedPattern_mem_powerset (κ : ℝ) (X n : ℕ) :
    rootedPattern κ X n ∈ (windowOmega κ X).powerset :=
  mem_powerset.mpr (filter_subset _ _)

private theorem subset_rootedPattern_iff {κ : ℝ} {X : ℕ} {H : Finset ℕ}
    (hH : H ⊆ windowOmega κ X) (n : ℕ) :
    H ⊆ rootedPattern κ X n ↔ ∀ h ∈ H, Nat.Prime (n + h) := by
  unfold rootedPattern
  constructor
  · intro hsub h hh
    exact (mem_filter.mp (hsub hh)).2
  · intro hp h hh
    exact mem_filter.mpr ⟨hH hh, hp h hh⟩

private theorem filter_pattern_eq (κ : ℝ) (X : ℕ) (U : Finset ℕ) :
    ((Ioc X (2 * X)).filter Nat.Prime).filter
        (fun n => rootedPattern κ X n = U) =
      (Ioc X (2 * X)).filter
        (fun n => Nat.Prime n ∧ rootedPattern κ X n = U) := by
  ext n
  simp only [mem_filter]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

private theorem sum_actualPatternCount (κ : ℝ) (X : ℕ) :
    ∑ U ∈ (windowOmega κ X).powerset, actualPatternCount κ X U =
      windowNX X := by
  rw [windowNX_eq_card_primes]
  have hmem : (((Ioc X (2 * X)).filter Nat.Prime : Set ℕ)).MapsTo
      (rootedPattern κ X) ((windowOmega κ X).powerset : Set (Finset ℕ)) :=
    fun n _ => rootedPattern_mem_powerset κ X n
  have hfiber :=
    card_eq_sum_card_fiberwise (f := rootedPattern κ X)
      (s := (Ioc X (2 * X)).filter Nat.Prime)
      (t := (windowOmega κ X).powerset) hmem
  rw [hfiber]
  refine sum_congr rfl fun U _ => ?_
  unfold actualPatternCount
  rw [filter_pattern_eq]

private theorem sum_actualPatternCount_supset {κ : ℝ} {X : ℕ} {H : Finset ℕ}
    (hH : H ⊆ windowOmega κ X) :
    ∑ U ∈ (windowOmega κ X).powerset.filter (fun U => H ⊆ U),
        actualPatternCount κ X U =
      rootedTupleCount X H := by
  let primes := (Ioc X (2 * X)).filter Nat.Prime
  let s := primes.filter (fun n => H ⊆ rootedPattern κ X n)
  have hs : s.card = rootedTupleCount X H := by
    unfold rootedTupleCount
    congr 1
    ext n
    constructor
    · intro hn
      have hs' := mem_filter.mp hn
      have hp := mem_filter.mp hs'.1
      refine mem_filter.mpr ⟨hp.1, hp.2, ?_⟩
      exact (subset_rootedPattern_iff hH n).mp hs'.2
    · intro hn
      have hr := mem_filter.mp hn
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hr.1, hr.2.1⟩, ?_⟩
      exact (subset_rootedPattern_iff hH n).mpr hr.2.2
  have hmem :
      (s : Set ℕ).MapsTo (rootedPattern κ X)
        ((windowOmega κ X).powerset.filter (fun U => H ⊆ U) :
          Set (Finset ℕ)) := by
    intro n hn
    have hn' := mem_filter.mp hn
    exact mem_filter.mpr ⟨rootedPattern_mem_powerset κ X n, hn'.2⟩
  have hfiber :=
    card_eq_sum_card_fiberwise (f := rootedPattern κ X) (s := s)
      (t := (windowOmega κ X).powerset.filter (fun U => H ⊆ U)) hmem
  rw [← hs, hfiber]
  refine sum_congr rfl fun U hU => ?_
  have hHU : H ⊆ U := (mem_filter.mp hU).2
  unfold actualPatternCount
  congr 1
  ext n
  constructor
  · intro hn
    have hf : n ∈ Ioc X (2 * X) ∧ Nat.Prime n ∧ rootedPattern κ X n = U :=
      mem_filter.mp hn
    have hpat : rootedPattern κ X n = U := hf.2.2
    have hsub : H ⊆ rootedPattern κ X n := by
      rw [hpat]
      exact hHU
    refine mem_filter.mpr ⟨?_, hpat⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hf.1, hf.2.1⟩, hsub⟩
  · intro hn
    have hs' : n ∈ s ∧ rootedPattern κ X n = U := mem_filter.mp hn
    have hp : n ∈ primes ∧ H ⊆ rootedPattern κ X n := mem_filter.mp hs'.1
    have hpr : n ∈ Ioc X (2 * X) ∧ Nat.Prime n := mem_filter.mp hp.1
    exact mem_filter.mpr ⟨hpr.1, hpr.2, hs'.2⟩

/-- Inclusion mass of the empirical law is `C_X(H)/N_X`. -/
theorem inclusionMass_actualConfigMass {κ : ℝ} {X : ℕ} {H : Finset ℕ}
    (hN : 0 < windowNX X) (hH : H ⊆ windowOmega κ X) :
    Stopped.inclusionMass (windowOmega κ X) (actualConfigMass κ X) H =
      actualInclusion X H := by
  have hNz : windowNX X ≠ 0 := ne_of_gt hN
  unfold Stopped.inclusionMass actualInclusion actualConfigMass
  rw [if_neg hNz]
  rw [sum_congr rfl fun U _ => if_neg hNz]
  have hdiv :=
    sum_div ((windowOmega κ X).powerset.filter (fun U => H ⊆ U))
      (fun U => (actualPatternCount κ X U : ℝ)) (windowNX X : ℝ)
  rw [← hdiv, ← Nat.cast_sum, sum_actualPatternCount_supset hH]

theorem inclusionMass_actualConfigMass_div {κ : ℝ} {X : ℕ} {H : Finset ℕ}
    (hN : 0 < windowNX X) (hH : H ⊆ windowOmega κ X) :
    Stopped.inclusionMass (windowOmega κ X) (actualConfigMass κ X) H =
      (rootedTupleCount X H : ℝ) / (windowNX X : ℝ) := by
    rw [inclusionMass_actualConfigMass hN hH,
    actualInclusion_eq_div H (ne_of_gt hN)]

theorem sum_actualConfigMass {κ : ℝ} {X : ℕ} (hN : 0 < windowNX X) :
    ∑ U ∈ (windowOmega κ X).powerset, actualConfigMass κ X U = 1 := by
  have hNz : windowNX X ≠ 0 := ne_of_gt hN
  unfold actualConfigMass
  rw [sum_congr rfl fun U _ => if_neg hNz]
  have hdiv :=
    sum_div (windowOmega κ X).powerset
      (fun U => (actualPatternCount κ X U : ℝ)) (windowNX X : ℝ)
  rw [← hdiv, ← Nat.cast_sum, sum_actualPatternCount]
  exact div_self (Nat.cast_ne_zero.mpr hNz)

/-! ### Profile parity (EndAPI `profileR`) -/

private theorem le_profileR (L : ℕ) (d0 : ℝ) : L ≤ profileR L d0 := by
  dsimp [profileR]
  split_ifs <;> omega

private theorem odd_profileR_sub (L : ℕ) (d0 : ℝ) :
    Odd (profileR L d0 - L) := by
  dsimp [profileR]
  split_ifs with h
  · exact h
  · have heq : max L ⌈d0 * (L : ℝ)⌉₊ + 1 - L =
        max L ⌈d0 * (L : ℝ)⌉₊ - L + 1 := by omega
    rw [heq]
    have heven : Even (max L ⌈d0 * (L : ℝ)⌉₊ - L) :=
      Nat.not_odd_iff_even.mp h
    have hmod : (max L ⌈d0 * (L : ℝ)⌉₊ - L) % 2 = 0 :=
      Nat.even_iff.mp heven
    rw [Nat.odd_iff, Nat.add_mod, hmod, zero_add]

/-! ### Instantiation of the finite stopped kernel -/

/-- Finite (5.1) on the prime window, with actual rooted masses. -/
theorem stoppedShapeL1_actual_add_failure_le
    {κ : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hN : 0 < windowNX X)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega κ X).powerset, ν U = 1) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν L +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X) L ≤
      Stopped.failureMass (windowOmega κ X) ν L +
        2 * Stopped.modelRemainder (windowOmega κ X) ν L r +
        2 * Stopped.adverseBudget (windowOmega κ X)
          (actualConfigMass κ X) ν L r := by
  have hμ : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ actualConfigMass κ X U :=
    fun U _ => actualConfigMass_nonneg κ X U
  have htot : ∑ U ∈ (windowOmega κ X).powerset, actualConfigMass κ X U =
      ∑ U ∈ (windowOmega κ X).powerset, ν U := by
    rw [sum_actualConfigMass hN, hmass]
  exact Stopped.stoppedShapeL1_add_failure_le hL hr hpar hμ hν htot

/-- Same bound with the model remainder replaced by a count moment. -/
theorem stoppedShapeL1_actual_add_failure_moment_le
    {κ : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hN : 0 < windowNX X)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega κ X).powerset, ν U = 1) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν L +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X) L ≤
      Stopped.failureMass (windowOmega κ X) ν L +
        2 * ((r.choose (L - 1) : ℝ) *
          Stopped.countMoment (windowOmega κ X) ν (r + 1)) +
        2 * Stopped.adverseBudget (windowOmega κ X)
          (actualConfigMass κ X) ν L r := by
  have hmain :=
    stoppedShapeL1_actual_add_failure_le hL hr hpar hN hν hmass
  have hR := Stopped.modelRemainder_le (Ω := windowOmega κ X) (ν := ν)
    (L := L) (r := r) hL hr hν
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hR2 :
      2 * Stopped.modelRemainder (windowOmega κ X) ν L r ≤
        2 * ((r.choose (L - 1) : ℝ) *
          Stopped.countMoment (windowOmega κ X) ν (r + 1)) :=
    mul_le_mul_of_nonneg_left hR h2
  linarith [hmain, hR2]

/-- Profile `(L,r)` packaging of the finite kernel. -/
theorem stoppedShapeL1_profile_add_failure_le
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
        2 * Stopped.adverseBudget (windowOmega κ X)
          (actualConfigMass κ X) ν (profileL κ X)
          (profileR (profileL κ X) d0) :=
  stoppedShapeL1_actual_add_failure_le hL (le_profileR _ _)
    (odd_profileR_sub _ _) hN hν hmass

/-! ### First-L observations -/

theorem abs_stopped_eval_actual_sub_le
    {κ : ℝ} {X L : ℕ} {ν : Finset ℕ → ℝ} {φ ψ : Finset ℕ → ℝ}
    (hN : 0 < windowNX X)
    (hφ : ∀ K ∈ (windowOmega κ X).powerset.filter (fun K => K.card = L),
      |φ K| ≤ 1)
    (hψ : ∀ U ∈ (windowOmega κ X).powerset, |ψ U| ≤ 1) :
    |∑ U ∈ (windowOmega κ X).powerset,
          actualConfigMass κ X U *
            (if L ≤ U.card then φ (Stopped.firstL L U) else ψ U) -
        ∑ K ∈ (windowOmega κ X).powerset.filter (fun K => K.card = L),
          Stopped.shortShapeMass (windowOmega κ X) ν L K * φ K| ≤
      Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν L +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X) L :=
  Stopped.abs_stopped_eval_sub_le hφ hψ fun U _ =>
    actualConfigMass_nonneg κ X U

/-- If the adverse budget and model remainder are small, first-`L`
endpoint observations differ by a small L1 amount. -/
theorem abs_endpointObs_actual_sub_le
    {κ : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ} {phi : List ℕ → ℝ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hN : 0 < windowNX X)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega κ X).powerset, ν U = 1)
    (hφ : ∀ t, |phi t| ≤ 1) :
    |∑ U ∈ (windowOmega κ X).powerset,
          actualConfigMass κ X U * endpointObs L phi U -
        ∑ K ∈ (windowOmega κ X).powerset.filter (fun K => K.card = L),
          Stopped.shortShapeMass (windowOmega κ X) ν L K *
            phi (K.sort (· ≤ ·))| ≤
      Stopped.failureMass (windowOmega κ X) ν L +
        2 * Stopped.modelRemainder (windowOmega κ X) ν L r +
        2 * Stopped.adverseBudget (windowOmega κ X)
          (actualConfigMass κ X) ν L r := by
  let Ω := windowOmega κ X
  let μ := actualConfigMass κ X
  let φ : Finset ℕ → ℝ := fun K => phi (K.sort (· ≤ ·))
  have hφK : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), |φ K| ≤ 1 :=
    fun K _ => hφ _
  have hψ : ∀ U ∈ Ω.powerset, |(0 : ℝ)| ≤ 1 := fun _ _ => by norm_num
  have hobs :
      ∑ U ∈ Ω.powerset, μ U * endpointObs L phi U =
        ∑ U ∈ Ω.powerset,
          μ U * (if L ≤ U.card then φ (Stopped.firstL L U) else 0) := by
    refine sum_congr rfl fun U _ => ?_
    rw [endpointObs_eq_stoppedValue, Stopped.stoppedValue]
  have heval :=
    abs_stopped_eval_actual_sub_le (κ := κ) (X := X) (L := L) (ν := ν)
      (φ := φ) (ψ := fun _ => 0) hN hφK hψ
  have hshape :=
    stoppedShapeL1_actual_add_failure_le hL hr hpar hN hν hmass
  rw [hobs]
  exact heval.trans hshape

/-! ### AlternatingStoppedHL versus `ahlLayer` -/

theorem ahlLayer_eq_alternating_sum (κ : ℝ) (X j L : ℕ) :
    ahlLayer κ X j L =
      ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
        max (((-1 : ℝ) ^ (j - L + 1)) *
          ((rootedTupleCount X H : ℝ) - rootedMainTerm X H)) 0 := by
  unfold ahlLayer
  refine sum_congr rfl fun H _ => (max_eq_posPart _).symm

/-- Count-scale (7.2) controls one AHL layer. -/
theorem ahlLayer_le_of_alternatingStoppedHL
    {κ : ℝ} {X L r : ℕ} {ε : ℝ}
    (h : AlternatingStoppedHL (windowOmega κ X)
      (fun H => (rootedTupleCount X H : ℝ))
      (fun H => rootedMainTerm X H) L r ε)
    {j : ℕ} (hjL : L ≤ j) (hjr : j ≤ r) :
    ahlLayer κ X j L ≤
      ε * ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
        rootedMainTerm X H := by
  rw [ahlLayer_eq_alternating_sum]
  exact h j hjL hjr

/-- Inclusion-scale (7.2) is exactly a relative adverse layer. -/
theorem adverseLayer_le_of_alternating_inclusions
    {Ω : Finset ℕ} {μ ν : Finset ℕ → ℝ} {L r : ℕ} {ε : ℝ}
    (hA : AlternatingStoppedHL Ω (Stopped.inclusionMass Ω μ)
      (Stopped.inclusionMass Ω ν) L r ε)
    {j : ℕ} (hj : j ∈ Icc L r) :
    Stopped.adverseLayer Ω μ ν L j ≤ ε * Stopped.countMoment Ω ν j := by
  have ⟨hjL, hjr⟩ := mem_Icc.mp hj
  have h := hA j hjL hjr
  unfold Stopped.adverseLayer
  rwa [countMoment_eq_sum_inclusionMass]

theorem adverseBudget_le_of_alternating_inclusions
    {Ω : Finset ℕ} {μ ν : Finset ℕ → ℝ} {L r : ℕ} {ε : ℝ}
    (hL : 1 ≤ L) (hr : L ≤ r)
    (hA : AlternatingStoppedHL Ω (Stopped.inclusionMass Ω μ)
      (Stopped.inclusionMass Ω ν) L r ε) :
    Stopped.adverseBudget Ω μ ν L r ≤
      ε * ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) * Stopped.countMoment Ω ν j :=
  Stopped.adverseBudget_le_of_layer hL hr fun j hj =>
    adverseLayer_le_of_alternating_inclusions hA hj

/-! ### BudgetNorm: raw AHL layers to Stopped `adverseBudget` -/

theorem adverseLayer_eq_posPart
    {Ω : Finset ℕ} {μ ν : Finset ℕ → ℝ} {L j : ℕ} :
    Stopped.adverseLayer Ω μ ν L j =
      ∑ H ∈ Ω.powerset.filter (fun H => H.card = j),
        (((-1 : ℝ) ^ (j - L + 1)) *
          (Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H))⁺ := by
  unfold Stopped.adverseLayer
  refine sum_congr rfl fun H _ => max_eq_posPart _

/-- Layerwise (1.1): actual `p_H = C_X(H)/N_X` versus model inclusions. -/
theorem adverseLayer_actual_le_normed
    {κ : ℝ} {X L j : ℕ} {ν : Finset ℕ → ℝ} {Z : ℝ}
    (hN : 0 < windowNX X) :
    Stopped.adverseLayer (windowOmega κ X) (actualConfigMass κ X) ν L j ≤
      (1 / (windowNX X : ℝ)) * ahlLayer κ X j L +
        ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
          |rootedMainTerm X H / (windowNX X : ℝ) - rootedMainTerm X H / Z| +
        ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
          |rootedMainTerm X H / Z -
            Stopped.inclusionMass (windowOmega κ X) ν H| := by
  let Ω := windowOmega κ X
  let I := Ω.powerset.filter (fun H => H.card = j)
  let μ := actualConfigMass κ X
  have hNℝ : 0 < (windowNX X : ℝ) := Nat.cast_pos.mpr hN
  have hw : ∀ H ∈ I, 0 ≤ (1 : ℝ) := fun _ _ => zero_le_one
  have hσ : ∀ H ∈ I, |(-1 : ℝ) ^ (j - L + 1)| ≤ 1 :=
    fun _ _ => abs_neg_one_pow_le _
  have hcore :=
    posPart_budget_normed_le (ι := Finset ℕ) I
      (fun _ => (1 : ℝ))
      (fun H => (rootedTupleCount X H : ℝ))
      (fun H => rootedMainTerm X H)
      (fun H => Stopped.inclusionMass Ω ν H)
      (fun _ => (-1 : ℝ) ^ (j - L + 1))
      (N := (windowNX X : ℝ)) (Z := Z) hNℝ hw hσ
  simp only [one_mul] at hcore
  have hLHS :
      Stopped.adverseLayer Ω μ ν L j =
        ∑ H ∈ I,
          (((-1 : ℝ) ^ (j - L + 1)) *
            ((rootedTupleCount X H : ℝ) / (windowNX X : ℝ) -
              Stopped.inclusionMass Ω ν H))⁺ := by
    rw [adverseLayer_eq_posPart]
    refine sum_congr rfl fun H hH => ?_
    have hHΩ : H ⊆ Ω := mem_powerset.mp (mem_filter.mp hH).1
    rw [inclusionMass_actualConfigMass_div hN hHΩ]
  have hahl :
      ∑ H ∈ I,
          (((-1 : ℝ) ^ (j - L + 1)) *
            ((rootedTupleCount X H : ℝ) - rootedMainTerm X H))⁺ =
        ahlLayer κ X j L := by
    unfold ahlLayer
    rfl
  rw [hLHS]
  refine hcore.trans ?_
  rw [hahl]

/-- Weighted (1.1) for the Stopped adverse budget on the prime window. -/
theorem adverseBudget_actual_le_normed
    {κ : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ} {Z : ℝ}
    (hN : 0 < windowNX X) :
    Stopped.adverseBudget (windowOmega κ X) (actualConfigMass κ X) ν L r ≤
      (1 / (windowNX X : ℝ)) *
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L +
        ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
              |rootedMainTerm X H / (windowNX X : ℝ) -
                rootedMainTerm X H / Z| +
        ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
              |rootedMainTerm X H / Z -
                Stopped.inclusionMass (windowOmega κ X) ν H| := by
  unfold Stopped.adverseBudget
  have hpt : ∀ j ∈ Icc L r,
      ((j - 1).choose (L - 1) : ℝ) *
          Stopped.adverseLayer (windowOmega κ X) (actualConfigMass κ X) ν L j ≤
        ((j - 1).choose (L - 1) : ℝ) *
          ((1 / (windowNX X : ℝ)) * ahlLayer κ X j L +
            ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
              |rootedMainTerm X H / (windowNX X : ℝ) -
                rootedMainTerm X H / Z| +
            ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
              |rootedMainTerm X H / Z -
                Stopped.inclusionMass (windowOmega κ X) ν H|) := by
    intro j hj
    have hnn : (0 : ℝ) ≤ ((j - 1).choose (L - 1) : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left (adverseLayer_actual_le_normed hN) hnn
  have hsum := sum_le_sum hpt
  refine hsum.trans ?_
  have hsplit :
      ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            ((1 / (windowNX X : ℝ)) * ahlLayer κ X j L +
              ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
                |rootedMainTerm X H / (windowNX X : ℝ) -
                  rootedMainTerm X H / Z| +
              ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
                |rootedMainTerm X H / Z -
                  Stopped.inclusionMass (windowOmega κ X) ν H|) =
        ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) *
              ((1 / (windowNX X : ℝ)) * ahlLayer κ X j L) +
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) *
              ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
                |rootedMainTerm X H / (windowNX X : ℝ) -
                  rootedMainTerm X H / Z| +
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) *
              ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
                |rootedMainTerm X H / Z -
                  Stopped.inclusionMass (windowOmega κ X) ν H| := by
    simp_rw [mul_add]
    rw [sum_add_distrib, sum_add_distrib]
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
      fun j => by ring
    simp_rw [hA]
    rw [← mul_sum]
  rw [hscale]

/-- No auxiliary `Z`: compare model inclusions to `M_X/N_X`. -/
theorem adverseBudget_actual_le_of_ahlLayer
    {κ : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ}
    (hN : 0 < windowNX X) :
    Stopped.adverseBudget (windowOmega κ X) (actualConfigMass κ X) ν L r ≤
      (1 / (windowNX X : ℝ)) *
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L +
        ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
              |rootedMainTerm X H / (windowNX X : ℝ) -
                Stopped.inclusionMass (windowOmega κ X) ν H| := by
  have h :=
    adverseBudget_actual_le_normed (κ := κ) (X := X) (L := L) (r := r)
      (ν := ν) (Z := (windowNX X : ℝ)) hN
  have hmid :
      ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
              |rootedMainTerm X H / (windowNX X : ℝ) -
                rootedMainTerm X H / (windowNX X : ℝ)| = 0 := by
    refine sum_eq_zero fun j _ => ?_
    have h0 :
        ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
            |rootedMainTerm X H / (windowNX X : ℝ) -
              rootedMainTerm X H / (windowNX X : ℝ)| = 0 := by
      refine sum_eq_zero fun H _ => ?_
      rw [sub_self, abs_zero]
    simp [h0]
  linarith [h, hmid]

theorem ahlBudget_eq_weighted {κ d0 : ℝ} {X : ℕ}
    (hN : windowNX X ≠ 0) :
    ahlBudget κ d0 X =
      (1 / (windowNX X : ℝ)) *
        ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
          ((j - 1).choose (profileL κ X - 1) : ℝ) *
            ahlLayer κ X j (profileL κ X) := by
  unfold ahlBudget
  split_ifs with h
  · exact (hN h).elim
  · rfl

/-- Combined finite bound: small AHL layers and small model/HL mismatch
imply small first-`L` shape L1. -/
theorem shapeL1_actual_add_failure_le_of_ahlLayer
    {κ : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hN : 0 < windowNX X)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega κ X).powerset, ν U = 1) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν L +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X) L ≤
      Stopped.failureMass (windowOmega κ X) ν L +
        2 * Stopped.modelRemainder (windowOmega κ X) ν L r +
        2 *
          ((1 / (windowNX X : ℝ)) *
              ∑ j ∈ Icc L r,
                ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L +
            ∑ j ∈ Icc L r,
              ((j - 1).choose (L - 1) : ℝ) *
                ∑ H ∈ (windowOmega κ X).powerset.filter
                    (fun H => H.card = j),
                  |rootedMainTerm X H / (windowNX X : ℝ) -
                    Stopped.inclusionMass (windowOmega κ X) ν H|) := by
  have hmain :=
    stoppedShapeL1_actual_add_failure_le hL hr hpar hN hν hmass
  have hW := adverseBudget_actual_le_of_ahlLayer (κ := κ) (X := X)
    (L := L) (r := r) (ν := ν) hN
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hW2 := mul_le_mul_of_nonneg_left hW h2
  linarith [hmain, hW2]

/-- Count-scale `AlternatingStoppedHL` plus exact HL-normalised model
inclusions yield a relative adverse budget. -/
theorem adverseBudget_actual_le_of_alternatingStoppedHL
    {κ : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ} {ε : ℝ}
    (hN : 0 < windowNX X) (hε : 0 ≤ ε)
    (hA : AlternatingStoppedHL (windowOmega κ X)
      (fun H => (rootedTupleCount X H : ℝ))
      (fun H => rootedMainTerm X H) L r ε)
    (hq : ∀ H ∈ (windowOmega κ X).powerset,
      Stopped.inclusionMass (windowOmega κ X) ν H =
        rootedMainTerm X H / (windowNX X : ℝ)) :
    Stopped.adverseBudget (windowOmega κ X) (actualConfigMass κ X) ν L r ≤
      (ε / (windowNX X : ℝ)) *
        ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
              rootedMainTerm X H := by
  have hW := adverseBudget_actual_le_of_ahlLayer (κ := κ) (X := X)
    (L := L) (r := r) (ν := ν) hN
  have hcal :
      ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
              |rootedMainTerm X H / (windowNX X : ℝ) -
                Stopped.inclusionMass (windowOmega κ X) ν H| = 0 := by
    refine sum_eq_zero fun j _ => ?_
    have h0 :
        ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
            |rootedMainTerm X H / (windowNX X : ℝ) -
              Stopped.inclusionMass (windowOmega κ X) ν H| = 0 := by
      refine sum_eq_zero fun H hH => ?_
      have hHΩ : H ⊆ windowOmega κ X :=
        mem_powerset.mp (mem_filter.mp hH).1
      rw [hq H (mem_powerset.mpr hHΩ), sub_self, abs_zero]
    simp [h0]
  have hahl : ∀ j ∈ Icc L r,
      ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L ≤
        ((j - 1).choose (L - 1) : ℝ) *
          (ε * ∑ H ∈ (windowOmega κ X).powerset.filter
              (fun H => H.card = j), rootedMainTerm X H) := by
    intro j hj
    have ⟨hjL, hjr⟩ := mem_Icc.mp hj
    have hnn : (0 : ℝ) ≤ ((j - 1).choose (L - 1) : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left
      (ahlLayer_le_of_alternatingStoppedHL hA hjL hjr) hnn
  have hsum := sum_le_sum hahl
  have hfac :
      ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            (ε * ∑ H ∈ (windowOmega κ X).powerset.filter
                (fun H => H.card = j), rootedMainTerm X H) =
        ε * ∑ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) *
            ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
              rootedMainTerm X H := by
    have hA' : ∀ j,
        ((j - 1).choose (L - 1) : ℝ) *
            (ε * ∑ H ∈ (windowOmega κ X).powerset.filter
                (fun H => H.card = j), rootedMainTerm X H) =
          ε * (((j - 1).choose (L - 1) : ℝ) *
            ∑ H ∈ (windowOmega κ X).powerset.filter (fun H => H.card = j),
              rootedMainTerm X H) :=
      fun j => by ring
    simp_rw [hA']
    rw [← mul_sum]
  have hNℝ : 0 < (windowNX X : ℝ) := Nat.cast_pos.mpr hN
  have hscale :
      (1 / (windowNX X : ℝ)) *
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L ≤
        (ε / (windowNX X : ℝ)) *
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) *
              ∑ H ∈ (windowOmega κ X).powerset.filter
                  (fun H => H.card = j),
                rootedMainTerm X H := by
    have hnn : 0 ≤ 1 / (windowNX X : ℝ) := one_div_nonneg.mpr hNℝ.le
    have hmul := mul_le_mul_of_nonneg_left (hsum.trans (le_of_eq hfac)) hnn
    have hrhs :
        (1 / (windowNX X : ℝ)) *
            (ε * ∑ j ∈ Icc L r,
              ((j - 1).choose (L - 1) : ℝ) *
                ∑ H ∈ (windowOmega κ X).powerset.filter
                    (fun H => H.card = j),
                  rootedMainTerm X H) =
          (ε / (windowNX X : ℝ)) *
            ∑ j ∈ Icc L r,
              ((j - 1).choose (L - 1) : ℝ) *
                ∑ H ∈ (windowOmega κ X).powerset.filter
                    (fun H => H.card = j),
                  rootedMainTerm X H := by
      ring
    rwa [hrhs] at hmul
  linarith [hW, hcal, hscale]

theorem shapeL1_actual_add_failure_le_of_alternatingStoppedHL
    {κ : ℝ} {X L r : ℕ} {ν : Finset ℕ → ℝ} {ε : ℝ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hN : 0 < windowNX X) (hε : 0 ≤ ε)
    (hν : ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ (windowOmega κ X).powerset, ν U = 1)
    (hA : AlternatingStoppedHL (windowOmega κ X)
      (fun H => (rootedTupleCount X H : ℝ))
      (fun H => rootedMainTerm X H) L r ε)
    (hq : ∀ H ∈ (windowOmega κ X).powerset,
      Stopped.inclusionMass (windowOmega κ X) ν H =
        rootedMainTerm X H / (windowNX X : ℝ)) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X) ν L +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X) L ≤
      Stopped.failureMass (windowOmega κ X) ν L +
        2 * Stopped.modelRemainder (windowOmega κ X) ν L r +
        2 * ((ε / (windowNX X : ℝ)) *
          ∑ j ∈ Icc L r,
            ((j - 1).choose (L - 1) : ℝ) *
              ∑ H ∈ (windowOmega κ X).powerset.filter
                  (fun H => H.card = j),
                rootedMainTerm X H) := by
  have hmain :=
    stoppedShapeL1_actual_add_failure_le hL hr hpar hN hν hmass
  have hW :=
    adverseBudget_actual_le_of_alternatingStoppedHL hN hε hA hq
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hW2 := mul_le_mul_of_nonneg_left hW h2
  linarith [hmain, hW2]

end PrimeGapNormality.Prime
