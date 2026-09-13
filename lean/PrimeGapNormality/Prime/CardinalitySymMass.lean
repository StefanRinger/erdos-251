import PrimeGapNormality.Prime.ActualRootLaw
import PrimeGapNormality.Prime.CardinalitySymInterface
import PrimeGapNormality.Prime.EulerProd
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# v0.6 — actual late root-law is cardinality-symmetric

Expose the rooted sieve through `S`, fix `A = U_S ∩ [1,T]` with
`T ≤ S`, and retain by the remaining primes `S < p ≤ y`. The target
measure is `actualRootLaw`, not a newly invented model. Candidates in
`A` are **not** claimed independent.

The late fibre is constructed as the remaining-prime product on
`A.powerset` (uniform average over `LateResidueChoice`). Full
identification with the global `actualRootLaw y T` fibre is required:
`actualRootLaw_eq_avg_lateRootLaw` averages `lateRootLaw` over the
`S`-presieve. Do not replace this by an existential `μ`.

`rootedEulerProdNat S y` is paper `ϑ`. Exact first/second/factorial
moments are named contracts (`eq:exactcounts`). Do not import
`Coupling` (name clash on `bernoulliThin`).

Source: `rounds/round108/05_paper_v0_6.tex` `eq:exchangeable`,
`eq:exactcounts`; `06_grok_exact_symmetry_and_st_delta.md` §2.
Contract: API
Audit: GREEN
-/

open Finset
open scoped Classical

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- Paper `ϑ = ∏_{S < p ≤ y} (1 - 1/(p-1))`. -/
noncomputable def lateRetention (S y : ℕ) : ℝ :=
  rootedEulerProdNat S y

/-- Candidates after the `S`-presieve, clipped to `T ≤ S`. -/
noncomputable def lateCandidateSet (S T : ℕ) (σ : ResidueChoice S) :
    Finset ℕ :=
  sieveSurvivorsFin S σ T

/-- Remaining primes `S < p ≤ y`. -/
abbrev latePrimes (S y : ℕ) : Finset ℕ :=
  Nat.primesLE y \ Nat.primesLE S

/-- Remaining sieve primes as a subtype. -/
abbrev LatePrime (S y : ℕ) :=
  {p : ℕ // p ∈ latePrimes S y}

/-- Remaining forbidden residues: one nonzero class modulo each `p > S`. -/
abbrev LateResidueChoice (S y : ℕ) :=
  ∀ p : LatePrime S y, Fin (p.val - 1)

instance (S y : ℕ) : DecidableEq (LatePrime S y) :=
  Subtype.instDecidableEq

instance (S y : ℕ) : Fintype (LatePrime S y) :=
  Finset.fintypeCoeSort (latePrimes S y)

instance (S y : ℕ) (p : LatePrime S y) : Nonempty (Fin (p.val - 1)) := by
  have hp : Nat.Prime p.val :=
    Nat.prime_of_mem_primesLE (sdiff_subset p.property)
  exact Fin.pos_iff_nonempty.mp (Nat.sub_pos_of_lt hp.one_lt)

instance (S y : ℕ) : Fintype (LateResidueChoice S y) :=
  Pi.instFintype

instance (S y : ℕ) : Nonempty (LateResidueChoice S y) :=
  ⟨fun p =>
    ⟨0, Nat.sub_pos_of_lt
      (Nat.prime_of_mem_primesLE (sdiff_subset p.property)).one_lt⟩⟩

instance (y : ℕ) : Nonempty (ResidueChoice y) :=
  ⟨fun p =>
    ⟨0, Nat.sub_pos_of_lt
      (Nat.prime_of_mem_primesLE p.property).one_lt⟩⟩

/-- Survivors in a fixed candidate set under remaining residues. -/
noncomputable def lateSurvivors (S y : ℕ) (A : Finset ℕ)
    (σ : LateResidueChoice S y) : Finset ℕ :=
  A.filter (fun n => ∀ p : LatePrime S y, n % p.val ≠ (σ p).val + 1)

/-- Remaining-prime product mass on subsets of a fixed candidate set.
Not independent Bernoulli coins: each remaining prime hits at most
one candidate when `T ≤ S`. -/
noncomputable def lateProductMass (S y : ℕ) (A E : Finset ℕ) : ℝ :=
  (((univ : Finset (LateResidueChoice S y)).filter
      fun σ => lateSurvivors S y A σ = E).card : ℝ) /
    (((univ : Finset (LateResidueChoice S y)).card : ℝ))

/-- The actual late root-law on a fixed candidate set: remaining-prime
product mass, not an existential stand-in. -/
noncomputable abbrev lateRootLaw (S y : ℕ) (A E : Finset ℕ) : ℝ :=
  lateProductMass S y A E

/-- Paper inclusion factor `∏_{S < p ≤ y} (1 - j/(p-1))`. -/
noncomputable def lateInclusionFactor (S y j : ℕ) : ℝ :=
  ∏ p ∈ latePrimes S y, (1 - (j : ℝ) / ((p : ℝ) - 1))

/-- Exact factorial moments, paper `eq:exactcounts`. Factors
`1 - j/(p-1)` stay nonnegative for `j ≤ M ≤ S ≤ p-1`. For `j > M`
the moment is zero; do not interpret a product with negative factors
as a probability. `Nat.choose 0 0 = 1`, never 0. -/
def ExactCountMoments (S y : ℕ) (A : Finset ℕ) (μ : Finset ℕ → ℝ) : Prop :=
  let M := A.card
  let θ := lateRetention S y
  (∑ E ∈ A.powerset, (E.card : ℝ) * μ E = (M : ℝ) * θ) ∧
    ((∑ E ∈ A.powerset, (E.card : ℝ) ^ 2 * μ E) -
        ((M : ℝ) * θ) ^ 2 ≤ (M : ℝ) * θ) ∧
      (∀ j : ℕ, j ≤ M →
        ∑ E ∈ A.powerset, (Nat.choose E.card j : ℝ) * μ E =
          (Nat.choose M j : ℝ) *
            ∏ p ∈ Nat.primesLE y \ Nat.primesLE S,
              (1 - (j : ℝ) / ((p : ℝ) - 1))) ∧
        ∀ j : ℕ, M < j →
          ∑ E ∈ A.powerset, (Nat.choose E.card j : ℝ) * μ E = 0

/-- Finite Chebyshev count band on late fibres whose mean lies in
`[3L,5L]`. Not the strong exponential grid exception. False on empty
`A` / `T = 0` unless the mean band holds. Instantiates
`μ := lateRootLaw`, not an arbitrary mass. -/
def CountBandException (S y T L : ℕ) : Prop :=
  0 < L →
    ∀ σ : ResidueChoice S,
      let A := lateCandidateSet S T σ
      let μ := lateRootLaw S y A
      let Mθ := (A.card : ℝ) * lateRetention S y
      (3 : ℝ) * L ≤ Mθ → Mθ ≤ (5 : ℝ) * L →
        ∑ E ∈ A.powerset.filter
            (fun E => E.card < 2 * L ∨ 6 * L < E.card), μ E ≤
          (5 : ℝ) / (L : ℝ)

/-! ### Remaining primes and candidate arithmetic -/

private theorem latePrime_gt {S y : ℕ} (p : LatePrime S y) :
    S < p.val := by
  have hp := mem_sdiff.mp p.property
  have hprime : Nat.Prime p.val := Nat.prime_of_mem_primesLE hp.1
  have : ¬ p.val ≤ S := fun hle =>
    hp.2 (Nat.mem_primesLE.mpr ⟨hle, hprime⟩)
  exact Nat.not_le.mp this

private theorem latePrime_prime {S y : ℕ} (p : LatePrime S y) :
    Nat.Prime p.val :=
  Nat.prime_of_mem_primesLE (sdiff_subset p.property)

private theorem latePrime_ge_three {S y : ℕ} (hS : 2 ≤ S)
    {p : ℕ} (hp : p ∈ latePrimes S y) : 3 ≤ p := by
  have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have hnotin : p ∉ Nat.primesLE S := (mem_sdiff.mp hp).2
  have : ¬ p ≤ S := fun hle => hnotin (Nat.mem_primesLE.mpr ⟨hle, hp'⟩)
  omega

theorem lateCandidateSet_subset_Icc (S T : ℕ) (σ : ResidueChoice S) :
    lateCandidateSet S T σ ⊆ Icc 1 T :=
  filter_subset _ _

theorem lateCandidateSet_card_le_T (S T : ℕ) (σ : ResidueChoice S) :
    (lateCandidateSet S T σ).card ≤ T := by
  have h := card_le_card (lateCandidateSet_subset_Icc S T σ)
  have hI : (Icc 1 T).card = T := by
    rw [Nat.card_Icc]
    omega
  exact h.trans_eq hI

private theorem candidate_lt_latePrime {S y T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) {n : ℕ} (hn : n ∈ A)
    (p : LatePrime S y) : n < p.val :=
  Nat.lt_of_le_of_lt ((mem_Icc.mp (hA hn)).2.trans hT) (latePrime_gt p)

private theorem candidate_mem_Icc_pred {S y T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (p : LatePrime S y) :
    A ⊆ Icc 1 (p.val - 1) := by
  intro n hn
  have hnI := mem_Icc.mp (hA hn)
  have hlt := candidate_lt_latePrime hA hT hn p
  exact mem_Icc.mpr ⟨hnI.1, Nat.le_sub_one_of_lt hlt⟩

private theorem lateSurvivors_subset (S y : ℕ) (A : Finset ℕ)
    (σ : LateResidueChoice S y) :
    lateSurvivors S y A σ ⊆ A :=
  filter_subset _ _

private theorem lateChoice_card_pos (S y : ℕ) :
    0 < ((univ : Finset (LateResidueChoice S y)).card : ℝ) :=
  Nat.cast_pos.mpr (card_pos.mpr univ_nonempty)

private theorem lateChoice_card_ne_zero (S y : ℕ) :
    ((univ : Finset (LateResidueChoice S y)).card : ℝ) ≠ 0 :=
  ne_of_gt (lateChoice_card_pos S y)

private theorem lateChoice_card_eq_prod (S y : ℕ) :
    ((univ : Finset (LateResidueChoice S y)).card : ℝ) =
      ∏ p : LatePrime S y, ((p.val - 1 : ℕ) : ℝ) := by
  simp [Fintype.card_pi, Fintype.card_fin]

/-! ### Residue encoding `{1,…,p-1}` -/

private theorem card_filter_val_succ_mem {k : ℕ} (J : Finset ℕ)
    (hJ : J ⊆ Icc 1 k) :
    ((univ : Finset (Fin k)).filter (fun x => x.val + 1 ∈ J)).card = J.card := by
  refine card_nbij (fun x : Fin k => x.val + 1) ?_ ?_ ?_
  · intro x hx
    exact (mem_filter.mp hx).2
  · intro x _hx y _hy hxy
    exact Fin.ext (Nat.add_right_cancel hxy)
  · intro m hm
    have hmI := mem_Icc.mp (hJ hm)
    have hm1 : 1 ≤ m := hmI.1
    have hlt : m - 1 < k := by omega
    refine ⟨⟨m - 1, hlt⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · rw [Nat.sub_add_cancel hm1]
      exact hm
    · exact Nat.sub_add_cancel hm1

private theorem card_filter_val_succ_not_mem {k : ℕ} (J : Finset ℕ)
    (hJ : J ⊆ Icc 1 k) :
    ((univ : Finset (Fin k)).filter (fun x => x.val + 1 ∉ J)).card =
      k - J.card := by
  have hsum :=
    card_filter_add_card_filter_not (s := (univ : Finset (Fin k)))
      (fun x : Fin k => x.val + 1 ∈ J)
  have hmem := card_filter_val_succ_mem (k := k) J hJ
  have huniv : (univ : Finset (Fin k)).card = k := Fintype.card_fin k
  have hle : J.card ≤ k := by
    have hI : (Icc 1 k).card = k := by
      rw [Nat.card_Icc]
      omega
    exact (card_le_card hJ).trans_eq hI
  have hnot :
      ((univ : Finset (Fin k)).filter (fun x => x.val + 1 ∉ J)).card =
        ((univ : Finset (Fin k)).filter (fun x => ¬ x.val + 1 ∈ J)).card :=
    rfl
  omega

private theorem late_filter_eq_piFinset (S y : ℕ) (J : Finset ℕ) :
    ((univ : Finset (LateResidueChoice S y)).filter
        fun σ => ∀ p : LatePrime S y, (σ p).val + 1 ∉ J) =
      Fintype.piFinset fun p : LatePrime S y =>
        (univ : Finset (Fin (p.val - 1))).filter
          fun x => x.val + 1 ∉ J := by
  ext σ
  constructor
  · intro hσ
    rw [Fintype.mem_piFinset]
    intro p
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hσ).2 p⟩
  · intro hσ
    refine mem_filter.mpr ⟨mem_univ _, fun p => ?_⟩
    exact (mem_filter.mp (Fintype.mem_piFinset.mp hσ p)).2

private theorem late_mem_survivors_iff (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (σ : LateResidueChoice S y) {n : ℕ}
    (hn : n ∈ A) :
    n ∈ lateSurvivors S y A σ ↔
      ∀ p : LatePrime S y, (σ p).val + 1 ≠ n := by
  simp only [lateSurvivors, mem_filter, hn, true_and]
  refine forall_congr' fun p => ?_
  rw [Nat.mod_eq_of_lt (candidate_lt_latePrime hA hT hn p), ne_comm]

private theorem late_subset_survivors_iff (S y : ℕ) {T : ℕ} {A H : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hH : H ⊆ A)
    (σ : LateResidueChoice S y) :
    H ⊆ lateSurvivors S y A σ ↔
      ∀ p : LatePrime S y, (σ p).val + 1 ∉ H := by
  constructor
  · intro h p hpH
    have hnA : (σ p).val + 1 ∈ A := hH hpH
    have hsurv : (σ p).val + 1 ∈ lateSurvivors S y A σ := h hpH
    exact (late_mem_survivors_iff S y hA hT σ hnA).mp hsurv p rfl
  · intro h n hnH
    have hnA : n ∈ A := hH hnH
    rw [late_mem_survivors_iff S y hA hT σ hnA]
    intro p heq
    exact h p (heq ▸ hnH)

/-! ### Inclusion probabilities -/

theorem lateInclusionFactor_one (S y : ℕ) :
    lateInclusionFactor S y 1 = lateRetention S y := by
  unfold lateInclusionFactor lateRetention rootedEulerProdNat
  refine prod_congr (s₁ := latePrimes S y) (s₂ := latePrimes S y) rfl
    fun p _hp => ?_
  rw [Nat.cast_one, one_div]

private theorem one_sub_two_mul_le_sq (q : ℝ) :
    1 - 2 * q ≤ (1 - q) ^ 2 := by
  have h : (1 - q) ^ 2 - (1 - 2 * q) = q ^ 2 := by ring
  have : 0 ≤ (1 - q) ^ 2 - (1 - 2 * q) := by
    rw [h]
    exact sq_nonneg q
  linarith

private theorem late_div_cast {p j : ℕ} (hp : 2 ≤ p) (hj : j ≤ p - 1) :
    ((p - 1 - j : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) =
      1 - (j : ℝ) / ((p : ℝ) - 1) := by
  have h1 : 1 ≤ p := le_trans (by decide : (1 : ℕ) ≤ 2) hp
  have hpred : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  have hden : (p : ℝ) - 1 ≠ 0 := by
    rw [← hpred]
    exact Nat.cast_ne_zero.mpr (Nat.sub_ne_zero_of_lt hp)
  rw [Nat.cast_sub hj, hpred]
  exact (one_sub_div hden).symm

private theorem lateInclusion_card (S y : ℕ) {T : ℕ} {A H : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hH : H ⊆ A) :
    (((univ : Finset (LateResidueChoice S y)).filter
          fun σ => H ⊆ lateSurvivors S y A σ).card : ℝ) /
        (((univ : Finset (LateResidueChoice S y)).card : ℝ)) =
      lateInclusionFactor S y H.card := by
  have hiff :
      ((univ : Finset (LateResidueChoice S y)).filter
          fun σ => H ⊆ lateSurvivors S y A σ) =
        (univ.filter fun σ =>
          ∀ p : LatePrime S y, (σ p).val + 1 ∉ H) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    exact late_subset_survivors_iff S y hA hT hH σ
  rw [hiff, late_filter_eq_piFinset]
  have hnum :
      ((Fintype.piFinset fun p : LatePrime S y =>
          (univ : Finset (Fin (p.val - 1))).filter
            fun x => x.val + 1 ∉ H).card : ℝ) =
        ∏ p : LatePrime S y, ((p.val - 1 - H.card : ℕ) : ℝ) := by
    rw [Fintype.card_piFinset, Nat.cast_prod]
    refine prod_congr (s₁ := univ) (s₂ := univ) rfl fun p _ => ?_
    have hIcc := candidate_mem_Icc_pred (S := S) (y := y) hA hT p
    have hHI : H ⊆ Icc 1 (p.val - 1) := hH.trans hIcc
    exact congrArg Nat.cast (card_filter_val_succ_not_mem H hHI)
  have hden := lateChoice_card_eq_prod S y
  have hfac :
      (∏ p : LatePrime S y, ((p.val - 1 - H.card : ℕ) : ℝ)) /
          (∏ p : LatePrime S y, ((p.val - 1 : ℕ) : ℝ)) =
        ∏ p : LatePrime S y,
          (1 - (H.card : ℝ) / ((p.val : ℝ) - 1)) := by
    have hdiv :
        ∀ p : LatePrime S y,
          ((p.val - 1 - H.card : ℕ) : ℝ) / ((p.val - 1 : ℕ) : ℝ) =
            1 - (H.card : ℝ) / ((p.val : ℝ) - 1) := by
      intro p
      have hp2 : 2 ≤ p.val := (latePrime_prime p).two_le
      have hIcc := candidate_mem_Icc_pred (S := S) (y := y) hA hT p
      have hHI : H ⊆ Icc 1 (p.val - 1) := hH.trans hIcc
      have hIcard : (Icc 1 (p.val - 1)).card = p.val - 1 := by
        rw [Nat.card_Icc]
        omega
      have hj : H.card ≤ p.val - 1 := (card_le_card hHI).trans_eq hIcard
      exact late_div_cast hp2 hj
    have hpt :
        (∏ p : LatePrime S y,
            ((p.val - 1 - H.card : ℕ) : ℝ) / ((p.val - 1 : ℕ) : ℝ)) =
          (∏ p : LatePrime S y, ((p.val - 1 - H.card : ℕ) : ℝ)) /
            (∏ p : LatePrime S y, ((p.val - 1 : ℕ) : ℝ)) :=
      prod_div_distrib
        (s := (univ : Finset (LatePrime S y)))
        (fun p : LatePrime S y => ((p.val - 1 - H.card : ℕ) : ℝ))
        (fun p : LatePrime S y => ((p.val - 1 : ℕ) : ℝ))
    rw [← hpt]
    exact Fintype.prod_congr _ _ fun p => hdiv p
  have hcoe :
      ∏ p : LatePrime S y, (1 - (H.card : ℝ) / ((p.val : ℝ) - 1)) =
        lateInclusionFactor S y H.card := by
    unfold lateInclusionFactor
    exact prod_coe_sort (latePrimes S y)
      (fun p : ℕ => 1 - (H.card : ℝ) / ((p : ℝ) - 1))
  rw [hnum, hden, hfac, hcoe]

theorem lateProductMass_nonneg (S y : ℕ) (A E : Finset ℕ) :
    0 ≤ lateProductMass S y A E :=
  div_nonneg (Nat.cast_nonneg _) (le_of_lt (lateChoice_card_pos S y))

theorem lateProductMass_sum (S y : ℕ) (A : Finset ℕ) :
    ∑ E ∈ A.powerset, lateProductMass S y A E = 1 := by
  have hdiv := lateChoice_card_ne_zero S y
  have hmaps :
      ((univ : Finset (LateResidueChoice S y)) : Set (LateResidueChoice S y)).MapsTo
        (lateSurvivors S y A) A.powerset :=
    fun σ _ => mem_powerset.mpr (lateSurvivors_subset S y A σ)
  have hfiber :=
    card_eq_sum_card_fiberwise (f := lateSurvivors S y A)
      (s := (univ : Finset (LateResidueChoice S y))) (t := A.powerset) hmaps
  simp only [lateProductMass]
  rw [← Finset.sum_div, ← Nat.cast_sum, ← hfiber]
  exact div_self hdiv

theorem lateProductMass_superset_sum (S y : ℕ) {T : ℕ} {A H : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hH : H ⊆ A) :
    ∑ E ∈ A.powerset.filter (fun E => H ⊆ E), lateProductMass S y A E =
      lateInclusionFactor S y H.card := by
  have hmaps :
      (((univ : Finset (LateResidueChoice S y)).filter
          fun σ => H ⊆ lateSurvivors S y A σ) :
          Set (LateResidueChoice S y)).MapsTo
        (lateSurvivors S y A)
        (A.powerset.filter (fun E => H ⊆ E)) := by
    intro σ hσ
    have hsub : H ⊆ lateSurvivors S y A σ := (mem_filter.mp hσ).2
    exact mem_filter.mpr
      ⟨mem_powerset.mpr (lateSurvivors_subset S y A σ), hsub⟩
  have hfiber :=
    card_eq_sum_card_fiberwise (f := lateSurvivors S y A)
      (s := (univ : Finset (LateResidueChoice S y)).filter
        fun σ => H ⊆ lateSurvivors S y A σ)
      (t := A.powerset.filter (fun E => H ⊆ E)) hmaps
  have hfibereq :
      (∑ E ∈ A.powerset.filter (fun E => H ⊆ E),
          ((univ : Finset (LateResidueChoice S y)).filter
              fun σ => lateSurvivors S y A σ = E).card) =
        ∑ E ∈ A.powerset.filter (fun E => H ⊆ E),
          (((univ : Finset (LateResidueChoice S y)).filter
              fun σ => H ⊆ lateSurvivors S y A σ).filter
              fun σ => lateSurvivors S y A σ = E).card := by
    refine sum_congr
      (s₁ := A.powerset.filter (fun E => H ⊆ E))
      (s₂ := A.powerset.filter (fun E => H ⊆ E)) rfl fun E hE => ?_
    have hHE : H ⊆ E := (mem_filter.mp hE).2
    refine congrArg Finset.card ?_
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hσeq
      exact ⟨hσeq.symm ▸ hHE, hσeq⟩
    · intro hσ
      exact hσ.2
  simp only [lateProductMass]
  rw [← Finset.sum_div, ← Nat.cast_sum, hfibereq, ← hfiber]
  exact lateInclusion_card S y hA hT hH

/-! ### Factorial moments -/

theorem lateProductMass_choose_moment (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (j : ℕ) :
    ∑ E ∈ A.powerset, (Nat.choose E.card j : ℝ) * lateProductMass S y A E =
      (Nat.choose A.card j : ℝ) * lateInclusionFactor S y j := by
  have hBchoose : ∀ E ∈ A.powerset,
      (Nat.choose E.card j : ℝ) =
        ∑ H ∈ A.powersetCard j, if H ⊆ E then (1 : ℝ) else 0 := by
    intro E hE
    have hEA : E ⊆ A := mem_powerset.mp hE
    have hfilter :
        (A.powersetCard j).filter (fun H => H ⊆ E) = E.powersetCard j := by
      ext H
      simp only [mem_filter, mem_powersetCard]
      constructor
      · intro h
        exact ⟨h.2, h.1.2⟩
      · intro h
        exact ⟨⟨h.1.trans hEA, h.2⟩, h.1⟩
    calc
      (Nat.choose E.card j : ℝ)
          = ∑ H ∈ E.powersetCard j, (1 : ℝ) := by
            simp [sum_const, nsmul_eq_mul, card_powersetCard]
      _ = ∑ H ∈ (A.powersetCard j).filter (fun H => H ⊆ E), (1 : ℝ) := by
            rw [hfilter]
      _ = ∑ H ∈ A.powersetCard j, if H ⊆ E then (1 : ℝ) else 0 := by
            rw [sum_filter]
  have h1 :
      ∑ E ∈ A.powerset, (Nat.choose E.card j : ℝ) * lateProductMass S y A E =
        ∑ E ∈ A.powerset, ∑ H ∈ A.powersetCard j,
          lateProductMass S y A E * (if H ⊆ E then (1 : ℝ) else 0) := by
    refine sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl fun E hE => ?_
    rw [hBchoose E hE, mul_comm, mul_sum]
  have hswap :
      ∑ E ∈ A.powerset, ∑ H ∈ A.powersetCard j,
          lateProductMass S y A E * (if H ⊆ E then (1 : ℝ) else 0)
        = ∑ H ∈ A.powersetCard j,
            ∑ E ∈ A.powerset.filter (fun E => H ⊆ E),
              lateProductMass S y A E := by
    rw [sum_comm]
    refine sum_congr (s₁ := A.powersetCard j) (s₂ := A.powersetCard j) rfl
      fun H _ => ?_
    have :
        ∑ E ∈ A.powerset,
            lateProductMass S y A E * (if H ⊆ E then (1 : ℝ) else 0)
          = ∑ E ∈ A.powerset,
              if H ⊆ E then lateProductMass S y A E else 0 := by
      refine sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl fun E _ => ?_
      simp [mul_ite, mul_one, mul_zero]
    rw [this, ← sum_filter]
  rw [h1, hswap]
  have hH : ∀ H ∈ A.powersetCard j,
      ∑ E ∈ A.powerset.filter (fun E => H ⊆ E), lateProductMass S y A E =
        lateInclusionFactor S y j := by
    intro H hH
    have hHA : H ⊆ A := (mem_powersetCard.mp hH).1
    have hcard : H.card = j := (mem_powersetCard.mp hH).2
    rw [lateProductMass_superset_sum S y hA hT hHA, hcard]
  rw [sum_congr (s₁ := A.powersetCard j) (s₂ := A.powersetCard j) rfl hH,
    sum_const, nsmul_eq_mul, card_powersetCard, mul_comm]

theorem lateProductMass_first_moment (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    ∑ E ∈ A.powerset, (E.card : ℝ) * lateProductMass S y A E =
      (A.card : ℝ) * lateRetention S y := by
  have h := lateProductMass_choose_moment S y hA hT 1
  have hL :
      ∑ E ∈ A.powerset, (Nat.choose E.card 1 : ℝ) * lateProductMass S y A E =
        ∑ E ∈ A.powerset, (E.card : ℝ) * lateProductMass S y A E := by
    refine sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl fun E _ => ?_
    simp [Nat.choose_one_right]
  have hR :
      (Nat.choose A.card 1 : ℝ) * lateInclusionFactor S y 1 =
        (A.card : ℝ) * lateRetention S y := by
    simp [Nat.choose_one_right, lateInclusionFactor_one]
  rw [← hL, h, hR]

private theorem two_mul_choose_two (n : ℕ) :
    (2 : ℝ) * (Nat.choose n 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ n 1, Nat.choose_one_right]
    push_cast
    have hsplit :
        (2 : ℝ) * ((n : ℝ) + (Nat.choose n 2 : ℝ)) =
          (2 : ℝ) * n + (2 : ℝ) * (Nat.choose n 2 : ℝ) := by
      ring
    rw [hsplit, ih]
    ring

private theorem lateRetention_nonneg (S y : ℕ) : 0 ≤ lateRetention S y := by
  unfold lateRetention rootedEulerProdNat
  refine prod_nonneg fun p hp => ?_
  have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp'.two_le
  have hden : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hden)

private theorem lateInclusionFactor_two_le_theta_sq (S y : ℕ)
    (hS : 2 ≤ S) :
    lateInclusionFactor S y 2 ≤ (lateRetention S y) ^ 2 := by
  have hθ :
      (lateRetention S y) ^ 2 =
        ∏ p ∈ latePrimes S y, (1 - (1 : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
    rw [← lateInclusionFactor_one, lateInclusionFactor, ← prod_pow]
    refine prod_congr (s₁ := latePrimes S y) (s₂ := latePrimes S y) rfl
      fun p _ => by rw [Nat.cast_one]
  have hle :
      ∀ p ∈ latePrimes S y,
        1 - (2 : ℝ) / ((p : ℝ) - 1) ≤
          (1 - (1 : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
    intro p _hp
    have h2 : (2 : ℝ) / ((p : ℝ) - 1) =
        2 * ((1 : ℝ) / ((p : ℝ) - 1)) := by
      ring
    rw [h2]
    exact one_sub_two_mul_le_sq (1 / ((p : ℝ) - 1))
  have h0 :
      ∀ p ∈ latePrimes S y, 0 ≤ 1 - (2 : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hp3 : 3 ≤ p := latePrime_ge_three hS hp
    have hp3R : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
    have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hnum : (2 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    exact sub_nonneg.mpr ((div_le_one hden).mpr hnum)
  have hprod := prod_le_prod h0 hle
  calc
    lateInclusionFactor S y 2
        = ∏ p ∈ latePrimes S y, (1 - (2 : ℝ) / ((p : ℝ) - 1)) := rfl
    _ ≤ ∏ p ∈ latePrimes S y, (1 - (1 : ℝ) / ((p : ℝ) - 1)) ^ 2 := hprod
    _ = (lateRetention S y) ^ 2 := hθ.symm

theorem lateProductMass_second_moment_bound (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    (∑ E ∈ A.powerset, (E.card : ℝ) ^ 2 * lateProductMass S y A E) -
        ((A.card : ℝ) * lateRetention S y) ^ 2 ≤
      (A.card : ℝ) * lateRetention S y := by
  set M := A.card
  set θ := lateRetention S y
  set μ := lateProductMass S y A
  have hEN := lateProductMass_first_moment S y hA hT
  have hdecomp :
      ∑ E ∈ A.powerset, (E.card : ℝ) ^ 2 * μ E =
        ∑ E ∈ A.powerset, ((E.card : ℝ) * ((E.card : ℝ) - 1)) * μ E +
          ∑ E ∈ A.powerset, (E.card : ℝ) * μ E := by
    have hpt : ∀ E ∈ A.powerset,
        (E.card : ℝ) ^ 2 * μ E =
          ((E.card : ℝ) * ((E.card : ℝ) - 1)) * μ E + (E.card : ℝ) * μ E := by
      intro E _
      ring
    rw [sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl hpt, sum_add_distrib]
  have hpair :
      ∑ E ∈ A.powerset, ((E.card : ℝ) * ((E.card : ℝ) - 1)) * μ E =
        (2 : ℝ) *
          ∑ E ∈ A.powerset, (Nat.choose E.card 2 : ℝ) * μ E := by
    have hpt : ∀ E ∈ A.powerset,
        ((E.card : ℝ) * ((E.card : ℝ) - 1)) * μ E =
          (2 : ℝ) * ((Nat.choose E.card 2 : ℝ) * μ E) := by
      intro E _
      have hc := two_mul_choose_two E.card
      rw [← hc]
      ring
    rw [sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl hpt, ← mul_sum]
  have hch2 := lateProductMass_choose_moment S y hA hT 2
  rw [hdecomp, hpair, hEN]
  rcases lt_or_ge M 2 with hM | hM
  · have hz : ∀ E ∈ A.powerset, Nat.choose E.card 2 = 0 := by
      intro E hE
      have hle : E.card ≤ M := card_le_card (mem_powerset.mp hE)
      exact Nat.choose_eq_zero_of_lt (lt_of_le_of_lt hle hM)
    have h0 :
        ∑ E ∈ A.powerset, (Nat.choose E.card 2 : ℝ) * μ E = 0 := by
      refine sum_eq_zero fun E hE => ?_
      simp [hz E hE]
    rw [h0, mul_zero, zero_add]
    have hsq0 : 0 ≤ ((M : ℝ) * θ) ^ 2 := sq_nonneg _
    linarith
  · have hATcard : M ≤ T := by
      have : M ≤ (Icc 1 T).card := card_le_card hA
      have hI : (Icc 1 T).card = T := by
        rw [Nat.card_Icc]
        omega
      exact this.trans_eq hI
    have hS : 2 ≤ S := by omega
    have hC : (2 : ℝ) * (Nat.choose M 2 : ℝ) = (M : ℝ) * ((M : ℝ) - 1) :=
      two_mul_choose_two M
    have hpair' :
        (2 : ℝ) * ∑ E ∈ A.powerset, (Nat.choose E.card 2 : ℝ) * μ E =
          (M : ℝ) * ((M : ℝ) - 1) * lateInclusionFactor S y 2 := by
      rw [hch2, ← mul_assoc, hC]
    rw [hpair']
    have hfac := lateInclusionFactor_two_le_theta_sq S y hS
    have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
    have hM1 : 0 ≤ (M : ℝ) - 1 := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hprod :
        (M : ℝ) * ((M : ℝ) - 1) * lateInclusionFactor S y 2 ≤
          (M : ℝ) * ((M : ℝ) - 1) * θ ^ 2 :=
      mul_le_mul_of_nonneg_left hfac (mul_nonneg hM0 hM1)
    have hMM : (M : ℝ) * ((M : ℝ) - 1) * θ ^ 2 ≤ (M : ℝ) * (M : ℝ) * θ ^ 2 := by
      have : (M : ℝ) - 1 ≤ (M : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left this hM0) (sq_nonneg θ)
    have : (M : ℝ) * ((M : ℝ) - 1) * lateInclusionFactor S y 2 ≤
        ((M : ℝ) * θ) ^ 2 := by
      have : (M : ℝ) * (M : ℝ) * θ ^ 2 = ((M : ℝ) * θ) ^ 2 := by ring
      exact hprod.trans (hMM.trans_eq this)
    linarith

/-! ### Möbius inversion ⇒ equal card ⇒ equal mass -/

private theorem sum_powerset_neg_one_real (W : Finset ℕ) :
    ∑ m ∈ W.powerset, (-1 : ℝ) ^ m.card = if W = ∅ then 1 else 0 := by
  have h := sum_powerset_neg_one_pow_card (α := ℕ) (x := W)
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) h
  simpa [Int.cast_sum, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_ite,
    Int.cast_zero] using hcast

private theorem sum_signed_supersets (U J : Finset ℕ) (hJ : J ⊆ U) :
    ∑ H ∈ U.powerset.filter (fun H => J ⊆ H), (-1 : ℝ) ^ (H.card - J.card) =
      if J = U then (1 : ℝ) else 0 := by
  calc
    ∑ H ∈ U.powerset.filter (fun H => J ⊆ H), (-1 : ℝ) ^ (H.card - J.card)
        = ∑ K ∈ (U \ J).powerset, (-1 : ℝ) ^ K.card := by
      refine sum_nbij' (fun H => H \ J) (fun K => J ∪ K) ?_ ?_ ?_ ?_ ?_
      · intro H hH
        have hH' := mem_filter.mp hH
        have hHU : H ⊆ U := mem_powerset.mp hH'.1
        exact mem_powerset.mpr (sdiff_subset_sdiff hHU (Subset.rfl : J ⊆ J))
      · intro K hK
        have hKU : K ⊆ U \ J := mem_powerset.mp hK
        refine mem_filter.mpr ?_
        exact ⟨mem_powerset.mpr (union_subset hJ (hKU.trans sdiff_subset)),
          subset_union_left⟩
      · intro H hH
        have hH' := mem_filter.mp hH
        exact union_sdiff_of_subset hH'.2
      · intro K hK
        have hKU : K ⊆ U \ J := mem_powerset.mp hK
        exact union_sdiff_cancel_left (disjoint_sdiff_self_right.mono_right hKU)
      · intro H hH
        have hH' := mem_filter.mp hH
        rw [card_sdiff_of_subset hH'.2]
    _ = if U \ J = ∅ then (1 : ℝ) else 0 :=
      sum_powerset_neg_one_real (U \ J)
    _ = if J = U then (1 : ℝ) else 0 := by
      refine if_congr ?_ rfl rfl
      rw [sdiff_eq_empty_iff_subset]
      exact ⟨fun h => Subset.antisymm hJ h, fun h => h ▸ Subset.rfl⟩

theorem lateProductMass_eq_signed (S y : ℕ) {T : ℕ} {A E : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hE : E ⊆ A) :
    lateProductMass S y A E =
      ∑ K ∈ A.powerset.filter (fun K => E ⊆ K),
        (-1 : ℝ) ^ (K.card - E.card) * lateInclusionFactor S y K.card := by
  set μ := lateProductMass S y A
  set AE := A.powerset.filter (fun K => E ⊆ K)
  set w : Finset ℕ → ℝ := fun K => (-1 : ℝ) ^ (K.card - E.card)
  have hinc : ∀ K ∈ AE,
      lateInclusionFactor S y K.card =
        ∑ F ∈ A.powerset.filter (fun F => K ⊆ F), μ F := by
    intro K hK
    have hKA : K ⊆ A := mem_powerset.mp (mem_filter.mp hK).1
    exact (lateProductMass_superset_sum S y hA hT hKA).symm
  have hRHS :
      ∑ K ∈ AE, w K * lateInclusionFactor S y K.card =
        ∑ K ∈ AE, ∑ F ∈ A.powerset.filter (fun F => K ⊆ F), w K * μ F := by
    refine sum_congr (s₁ := AE) (s₂ := AE) rfl fun K hK => ?_
    rw [hinc K hK, mul_sum]
  have hite :
      ∑ K ∈ AE, ∑ F ∈ A.powerset.filter (fun F => K ⊆ F), w K * μ F =
        ∑ K ∈ AE, ∑ F ∈ A.powerset,
          if K ⊆ F then w K * μ F else (0 : ℝ) := by
    refine sum_congr (s₁ := AE) (s₂ := AE) rfl fun K _ => ?_
    rw [sum_filter]
  have hswap :
      (∑ K ∈ AE, ∑ F ∈ A.powerset, if K ⊆ F then w K * μ F else (0 : ℝ)) =
        ∑ F ∈ A.powerset, ∑ K ∈ AE, if K ⊆ F then w K * μ F else (0 : ℝ) :=
    sum_comm
  have hfilter :
      (∑ F ∈ A.powerset, ∑ K ∈ AE, if K ⊆ F then w K * μ F else (0 : ℝ)) =
        ∑ F ∈ A.powerset, ∑ K ∈ AE.filter (fun K => K ⊆ F), w K * μ F := by
    refine sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl fun F _ => ?_
    rw [← sum_filter]
  have hmul :
      ∑ F ∈ A.powerset, ∑ K ∈ AE.filter (fun K => K ⊆ F), w K * μ F =
        ∑ F ∈ A.powerset, (∑ K ∈ AE.filter (fun K => K ⊆ F), w K) * μ F := by
    refine sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl fun F _ => ?_
    rw [← sum_mul]
  have hinner : ∀ F ∈ A.powerset,
      ∑ K ∈ AE.filter (fun K => K ⊆ F), w K =
        if F = E then (1 : ℝ) else 0 := by
    intro F hFpow
    by_cases hEF : E ⊆ F
    · have hset : AE.filter (fun K => K ⊆ F) =
          F.powerset.filter (fun K => E ⊆ K) := by
        ext K
        constructor
        · intro hK
          have hfil := mem_filter.mp hK
          have hAE := mem_filter.mp hfil.1
          exact mem_filter.mpr ⟨mem_powerset.mpr hfil.2, hAE.2⟩
        · intro hK
          have hfil := mem_filter.mp hK
          have hKA : K ⊆ A :=
            (mem_powerset.mp hfil.1).trans (mem_powerset.mp hFpow)
          exact mem_filter.mpr
            ⟨mem_filter.mpr ⟨mem_powerset.mpr hKA, hfil.2⟩,
              mem_powerset.mp hfil.1⟩
      rw [hset]
      simp only [w]
      rw [sum_signed_supersets F E hEF]
      simp [eq_comm]
    · have hempty : AE.filter (fun K => K ⊆ F) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro K hK
        have hEK : E ⊆ K := (mem_filter.mp (mem_filter.mp hK).1).2
        have hKF : K ⊆ F := (mem_filter.mp hK).2
        exact hEF (hEK.trans hKF)
      have hFE : F ≠ E := fun h => hEF (h ▸ Subset.rfl)
      simp [hempty, hFE]
  have hsumF :
      ∑ F ∈ A.powerset, (∑ K ∈ AE.filter (fun K => K ⊆ F), w K) * μ F =
        ∑ F ∈ A.powerset, (if F = E then (1 : ℝ) else 0) * μ F := by
    refine sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl fun F hF => ?_
    rw [hinner F hF]
  have hiteE :
      ∑ F ∈ A.powerset, (if F = E then (1 : ℝ) else 0) * μ F =
        μ E := by
    have hpt : ∀ F ∈ A.powerset,
        (if F = E then (1 : ℝ) else 0) * μ F =
          if F = E then μ E else (0 : ℝ) := by
      intro F _
      split_ifs with hFE
      · rw [hFE, one_mul]
      · simp
    rw [sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl hpt]
    exact sum_ite_eq_of_mem' A.powerset E (fun _ => μ E)
      (mem_powerset.mpr hE)
  calc
    μ E = ∑ F ∈ A.powerset, (if F = E then (1 : ℝ) else 0) * μ F := hiteE.symm
    _ = ∑ K ∈ AE, w K * lateInclusionFactor S y K.card := by
      rw [← hsumF, ← hmul, ← hfilter, ← hswap, ← hite, ← hRHS]

theorem lateProductMass_eq_of_card_eq (S y : ℕ) {T : ℕ} {A E F : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hE : E ⊆ A) (hF : F ⊆ A)
    (hc : E.card = F.card) :
    lateProductMass S y A E = lateProductMass S y A F := by
  have hEform := lateProductMass_eq_signed S y hA hT hE
  have hFform := lateProductMass_eq_signed S y hA hT hF
  have hEnb :
      ∑ K ∈ A.powerset.filter (fun K => E ⊆ K),
          (-1 : ℝ) ^ (K.card - E.card) * lateInclusionFactor S y K.card =
        ∑ J ∈ (A \ E).powerset,
          (-1 : ℝ) ^ J.card * lateInclusionFactor S y (E.card + J.card) := by
    refine sum_nbij' (fun K => K \ E) (fun J => E ∪ J) ?_ ?_ ?_ ?_ ?_
    · intro K hK
      have hK' := mem_filter.mp hK
      have hKA : K ⊆ A := mem_powerset.mp hK'.1
      exact mem_powerset.mpr (sdiff_subset_sdiff hKA (Subset.rfl : E ⊆ E))
    · intro J hJ
      have hJA : J ⊆ A \ E := mem_powerset.mp hJ
      refine mem_filter.mpr ⟨mem_powerset.mpr
          (union_subset hE (hJA.trans sdiff_subset)), subset_union_left⟩
    · intro K hK
      exact union_sdiff_of_subset (mem_filter.mp hK).2
    · intro J hJ
      have hJA : J ⊆ A \ E := mem_powerset.mp hJ
      exact union_sdiff_cancel_left (disjoint_sdiff_self_right.mono_right hJA)
    · intro K hK
      have hEK : E ⊆ K := (mem_filter.mp hK).2
      have hcard : K.card - E.card = (K \ E).card := (card_sdiff_of_subset hEK).symm
      have hadd : E.card + (K \ E).card = K.card := by
        rw [card_sdiff_of_subset hEK]
        exact Nat.add_sub_of_le (card_le_card hEK)
      rw [hcard, hadd]
  have hFnb :
      ∑ K ∈ A.powerset.filter (fun K => F ⊆ K),
          (-1 : ℝ) ^ (K.card - F.card) * lateInclusionFactor S y K.card =
        ∑ J ∈ (A \ F).powerset,
          (-1 : ℝ) ^ J.card * lateInclusionFactor S y (F.card + J.card) := by
    refine sum_nbij' (fun K => K \ F) (fun J => F ∪ J) ?_ ?_ ?_ ?_ ?_
    · intro K hK
      have hK' := mem_filter.mp hK
      have hKA : K ⊆ A := mem_powerset.mp hK'.1
      exact mem_powerset.mpr (sdiff_subset_sdiff hKA (Subset.rfl : F ⊆ F))
    · intro J hJ
      have hJA : J ⊆ A \ F := mem_powerset.mp hJ
      refine mem_filter.mpr ⟨mem_powerset.mpr
          (union_subset hF (hJA.trans sdiff_subset)), subset_union_left⟩
    · intro K hK
      exact union_sdiff_of_subset (mem_filter.mp hK).2
    · intro J hJ
      have hJA : J ⊆ A \ F := mem_powerset.mp hJ
      exact union_sdiff_cancel_left (disjoint_sdiff_self_right.mono_right hJA)
    · intro K hK
      have hFK : F ⊆ K := (mem_filter.mp hK).2
      have hcard : K.card - F.card = (K \ F).card := (card_sdiff_of_subset hFK).symm
      have hadd : F.card + (K \ F).card = K.card := by
        rw [card_sdiff_of_subset hFK]
        exact Nat.add_sub_of_le (card_le_card hFK)
      rw [hcard, hadd]
  have hEcard : (A \ E).card = A.card - E.card := card_sdiff_of_subset hE
  have hFcard : (A \ F).card = A.card - F.card := card_sdiff_of_subset hF
  have hEsum :
      ∑ J ∈ (A \ E).powerset,
          (-1 : ℝ) ^ J.card * lateInclusionFactor S y (E.card + J.card) =
        ∑ n ∈ range ((A.card - E.card) + 1),
          (Nat.choose (A.card - E.card) n : ℝ) *
            ((-1 : ℝ) ^ n * lateInclusionFactor S y (E.card + n)) := by
    have h := sum_powerset_apply_card
      (fun n => (-1 : ℝ) ^ n * lateInclusionFactor S y (E.card + n))
      (x := A \ E)
    rw [h, hEcard]
    refine sum_congr (s₁ := range (A.card - E.card + 1))
      (s₂ := range (A.card - E.card + 1)) rfl fun n _ => ?_
    rw [nsmul_eq_mul]
  have hFsum :
      ∑ J ∈ (A \ F).powerset,
          (-1 : ℝ) ^ J.card * lateInclusionFactor S y (F.card + J.card) =
        ∑ n ∈ range ((A.card - F.card) + 1),
          (Nat.choose (A.card - F.card) n : ℝ) *
            ((-1 : ℝ) ^ n * lateInclusionFactor S y (F.card + n)) := by
    have h := sum_powerset_apply_card
      (fun n => (-1 : ℝ) ^ n * lateInclusionFactor S y (F.card + n))
      (x := A \ F)
    rw [h, hFcard]
    refine sum_congr (s₁ := range (A.card - F.card + 1))
      (s₂ := range (A.card - F.card + 1)) rfl fun n _ => ?_
    rw [nsmul_eq_mul]
  rw [hEform, hFform, hEnb, hFnb, hEsum, hFsum, hc]

theorem lateProductMass_cardinalitySymmetric (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    CardinalitySymmetricMass A (lateProductMass S y A) := by
  refine ⟨?h0, lateProductMass_sum S y A, ?hsym⟩
  · intro E _hE
    exact lateProductMass_nonneg S y A E
  · intro E F hE hF hc
    exact lateProductMass_eq_of_card_eq S y hA hT hE hF hc

theorem lateProductMass_choose_eq_zero (S y : ℕ) (A : Finset ℕ) {j : ℕ}
    (hj : A.card < j) :
    ∑ E ∈ A.powerset, (Nat.choose E.card j : ℝ) * lateProductMass S y A E = 0 := by
  refine sum_eq_zero fun E hE => ?_
  have hle : E.card ≤ A.card := card_le_card (mem_powerset.mp hE)
  have hz : Nat.choose E.card j = 0 :=
    Nat.choose_eq_zero_of_lt (lt_of_le_of_lt hle hj)
  simp [hz]

theorem exactCountMoments_lateProductMass (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    ExactCountMoments S y A (lateProductMass S y A) := by
  refine ⟨lateProductMass_first_moment S y hA hT,
    lateProductMass_second_moment_bound S y hA hT, ?hjle, ?hjgt⟩
  · intro j hj
    have h := lateProductMass_choose_moment S y hA hT j
    simpa [lateInclusionFactor, latePrimes] using h
  · intro j hj
    exact lateProductMass_choose_eq_zero S y A hj

theorem lateRootLaw_cardinalitySymmetric (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hSy : S ≤ y) :
    CardinalitySymmetricMass A (lateRootLaw S y A) := by
  simpa [lateRootLaw] using lateProductMass_cardinalitySymmetric S y hA hT

theorem exactCountMoments_lateRootLaw (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hSy : S ≤ y) :
    ExactCountMoments S y A (lateRootLaw S y A) := by
  simpa [lateRootLaw] using exactCountMoments_lateProductMass S y hA hT

/-! ### Glue `ResidueChoice S × LateResidueChoice S y ≃ ResidueChoice y` -/

private theorem primesLE_subset_of_le {S y : ℕ} (hSy : S ≤ y) :
    Nat.primesLE S ⊆ Nat.primesLE y :=
  Nat.primesLE_mono hSy

private def glueResidue (S y : ℕ) (hSy : S ≤ y)
    (σ : ResidueChoice S) (τ : LateResidueChoice S y) : ResidueChoice y :=
  fun p =>
    if h : p.val ∈ Nat.primesLE S then
      σ ⟨p.val, h⟩
    else
      τ ⟨p.val, mem_sdiff.mpr ⟨p.property, h⟩⟩

private def restrictEarly (S y : ℕ) (hSy : S ≤ y)
    (ρ : ResidueChoice y) : ResidueChoice S :=
  fun p => ρ ⟨p.val, primesLE_subset_of_le hSy p.property⟩

private def restrictLate (S y : ℕ) (_hSy : S ≤ y)
    (ρ : ResidueChoice y) : LateResidueChoice S y :=
  fun p => ρ ⟨p.val, sdiff_subset p.property⟩

private def residueGlueEquiv (S y : ℕ) (hSy : S ≤ y) :
    ResidueChoice S × LateResidueChoice S y ≃ ResidueChoice y where
  toFun := fun pair => glueResidue S y hSy pair.1 pair.2
  invFun := fun ρ => (restrictEarly S y hSy ρ, restrictLate S y hSy ρ)
  left_inv := by
    rintro ⟨σ, τ⟩
    refine Prod.ext ?_ ?_
    · funext p
      simp [restrictEarly, glueResidue, p.property]
    · funext q
      have hq : q.val ∉ Nat.primesLE S := (mem_sdiff.mp q.property).2
      simp [restrictLate, glueResidue, hq]
  right_inv := by
    intro ρ
    funext p
    by_cases h : p.val ∈ Nat.primesLE S
    · simp [glueResidue, restrictEarly, h]
    · simp [glueResidue, restrictLate, h]

private theorem residueOfChoice_glue_early {S y : ℕ} (hSy : S ≤ y)
    (σ : ResidueChoice S) (τ : LateResidueChoice S y) {p : ℕ}
    (hp : p ∈ Nat.primesLE S) :
    residueOfChoice y (glueResidue S y hSy σ τ) p =
      residueOfChoice S σ p := by
  have hpY : p ∈ Nat.primesLE y := primesLE_subset_of_le hSy hp
  simp [residueOfChoice, glueResidue, hpY, hp]

private theorem residueOfChoice_glue_late {S y : ℕ} (hSy : S ≤ y)
    (σ : ResidueChoice S) (τ : LateResidueChoice S y) {p : ℕ}
    (hp : p ∈ latePrimes S y) :
    residueOfChoice y (glueResidue S y hSy σ τ) p =
      (τ ⟨p, hp⟩).val + 1 := by
  have hpY : p ∈ Nat.primesLE y := sdiff_subset hp
  have hpS : p ∉ Nat.primesLE S := (mem_sdiff.mp hp).2
  simp [residueOfChoice, glueResidue, hpY, hpS]

private theorem sieveSurvivorsFin_glue (S y T : ℕ) (hSy : S ≤ y)
    (σ : ResidueChoice S) (τ : LateResidueChoice S y) :
    sieveSurvivorsFin y (glueResidue S y hSy σ τ) T =
      lateSurvivors S y (lateCandidateSet S T σ) τ := by
  ext n
  constructor
  · intro hn
    have hnI : n ∈ offsetWindow T := (mem_filter.mp hn).1
    have hsurv := (mem_filter.mp hn).2
    refine mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_filter.mpr ⟨hnI, ?_⟩
      intro p hp
      have hne := hsurv p (primesLE_subset_of_le hSy hp)
      rwa [residueOfChoice_glue_early hSy σ τ hp] at hne
    · intro q
      have hne := hsurv q.val (sdiff_subset q.property)
      rwa [residueOfChoice_glue_late hSy σ τ q.property] at hne
  · intro hn
    have hnA := (mem_filter.mp hn).1
    have hlate := (mem_filter.mp hn).2
    have hnI : n ∈ offsetWindow T := (mem_filter.mp hnA).1
    have hearly := (mem_filter.mp hnA).2
    refine mem_filter.mpr ⟨hnI, ?_⟩
    intro p hp
    by_cases hpS : p ∈ Nat.primesLE S
    · have hne := hearly p hpS
      rwa [residueOfChoice_glue_early hSy σ τ hpS]
    · have hlp : p ∈ latePrimes S y := mem_sdiff.mpr ⟨hp, hpS⟩
      have hne := hlate ⟨p, hlp⟩
      rwa [residueOfChoice_glue_late hSy σ τ hlp]

private theorem card_filter_survivors_sum (S y T : ℕ) (hSy : S ≤ y)
    (U : Finset ℕ) :
    ((univ : Finset (ResidueChoice y)).filter
        fun ρ => sieveSurvivorsFin y ρ T = U).card =
      ∑ σ : ResidueChoice S,
        ((univ : Finset (LateResidueChoice S y)).filter
          fun τ =>
            lateSurvivors S y (lateCandidateSet S T σ) τ = U).card := by
  let e := residueGlueEquiv S y hSy
  have hleft :
      ((univ : Finset (ResidueChoice y)).filter
          fun ρ => sieveSurvivorsFin y ρ T = U).card =
        ((univ : Finset (ResidueChoice S × LateResidueChoice S y)).filter
          fun pair => sieveSurvivorsFin y (e pair) T = U).card := by
    refine card_equiv e.symm ?_
    intro ρ
    simp only [mem_filter, mem_univ, true_and]
    rw [e.apply_symm_apply]
  have hpred :
      ((univ : Finset (ResidueChoice S × LateResidueChoice S y)).filter
          fun pair => sieveSurvivorsFin y (e pair) T = U) =
        univ.filter fun pair =>
          lateSurvivors S y (lateCandidateSet S T pair.1) pair.2 = U := by
    ext pair
    simp only [mem_filter, mem_univ, true_and]
    change sieveSurvivorsFin y (glueResidue S y hSy pair.1 pair.2) T = U ↔ _
    rw [sieveSurvivorsFin_glue S y T hSy pair.1 pair.2]
  rw [hleft, hpred]
  have hcardP :
      ((univ : Finset (ResidueChoice S × LateResidueChoice S y)).filter
          fun pair =>
            lateSurvivors S y (lateCandidateSet S T pair.1) pair.2 =
              U).card =
        ∑ pair : ResidueChoice S × LateResidueChoice S y,
          if lateSurvivors S y (lateCandidateSet S T pair.1) pair.2 = U then
            (1 : ℕ) else 0 := by
    exact (sum_boole (R := ℕ) _ _).symm
  have hcardS :
      ∀ σ : ResidueChoice S,
        ((univ : Finset (LateResidueChoice S y)).filter
            fun τ =>
              lateSurvivors S y (lateCandidateSet S T σ) τ = U).card =
          ∑ τ : LateResidueChoice S y,
            if lateSurvivors S y (lateCandidateSet S T σ) τ = U then
              (1 : ℕ) else 0 := by
    intro σ
    exact (sum_boole (R := ℕ) _ _).symm
  rw [hcardP, Fintype.sum_prod_type]
  refine sum_congr (s₁ := univ) (s₂ := univ) rfl fun σ _ => ?_
  exact (hcardS σ).symm

theorem actualRootLaw_eq_avg_lateRootLaw
    (S y T : ℕ) (hTS : T ≤ S) (hSy : S ≤ y) (U : Finset ℕ) :
    actualRootLaw y T U =
      (∑ σ : ResidueChoice S,
          lateRootLaw S y (lateCandidateSet S T σ) U) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  have hcardY :
      Fintype.card (ResidueChoice y) =
        Fintype.card (ResidueChoice S) *
          Fintype.card (LateResidueChoice S y) := by
    rw [← Fintype.card_congr (residueGlueEquiv S y hSy), Fintype.card_prod]
  have hsum := card_filter_survivors_sum S y T hSy U
  have hdenL :
      ((univ : Finset (LateResidueChoice S y)).card : ℝ) =
        (Fintype.card (LateResidueChoice S y) : ℝ) :=
    rfl
  have havg :
      (∑ σ : ResidueChoice S,
          lateRootLaw S y (lateCandidateSet S T σ) U) /
        (Fintype.card (ResidueChoice S) : ℝ) =
      (((∑ σ : ResidueChoice S,
          ((univ : Finset (LateResidueChoice S y)).filter
            fun τ =>
              lateSurvivors S y (lateCandidateSet S T σ) τ = U).card) : ℕ) : ℝ) /
        ((Fintype.card (ResidueChoice S) : ℝ) *
          (Fintype.card (LateResidueChoice S y) : ℝ)) := by
    simp only [lateRootLaw, lateProductMass, hdenL]
    rw [← Finset.sum_div, div_div, ← Nat.cast_sum]
    congr 1
    ring
  rw [havg, ← hsum, actualRootLaw, hcardY, Nat.cast_mul]


/-! ### Chebyshev count band from `Var N ≤ M ϑ` -/

theorem countBand_of_second_moment {A : Finset ℕ} {μ : Finset ℕ → ℝ}
    {S y L : ℕ} {C : ℝ}
    (hμ : CardinalitySymmetricMass A μ)
    (hMom : ExactCountMoments S y A μ) (hL : 0 < L)
    (hlo : (3 : ℝ) * L ≤ (A.card : ℝ) * lateRetention S y)
    (hhi : (A.card : ℝ) * lateRetention S y ≤ (5 : ℝ) * L)
    (hC : (A.card : ℝ) * lateRetention S y ≤ C * L) :
    ∑ E ∈ A.powerset.filter (fun E => E.card < 2 * L ∨ 6 * L < E.card), μ E ≤
      C / (L : ℝ) := by
  set m := (A.card : ℝ) * lateRetention S y
  have hsum1 : ∑ E ∈ A.powerset, μ E = 1 := hμ.2.1
  have hnonneg : ∀ E ∈ A.powerset, 0 ≤ μ E := hμ.1
  have hEN : ∑ E ∈ A.powerset, (E.card : ℝ) * μ E = m := hMom.1
  have hVar : (∑ E ∈ A.powerset, (E.card : ℝ) ^ 2 * μ E) - m ^ 2 ≤ m := hMom.2.1
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hdev : ∀ E ∈ A.powerset.filter
        (fun E => E.card < 2 * L ∨ 6 * L < E.card),
      (L : ℝ) ≤ |(E.card : ℝ) - m| := by
    intro E hE
    have hbad : E.card < 2 * L ∨ 6 * L < E.card := (mem_filter.mp hE).2
    rcases hbad with hlt | hgt
    · have hX : (E.card : ℝ) < 2 * (L : ℝ) := by
        have : (E.card : ℝ) < ((2 * L : ℕ) : ℝ) := Nat.cast_lt.mpr hlt
        simpa [Nat.cast_mul] using this
      have hXm : (E.card : ℝ) ≤ m := le_trans (le_of_lt hX)
        (le_trans (by linarith : (2 : ℝ) * L ≤ (3 : ℝ) * L) hlo)
      have hgap : (L : ℝ) ≤ m - (E.card : ℝ) := by linarith
      rw [abs_sub_comm]
      rwa [abs_of_nonneg (sub_nonneg.mpr hXm)]
    · have hX : 6 * (L : ℝ) < (E.card : ℝ) := by
        have : ((6 * L : ℕ) : ℝ) < (E.card : ℝ) := Nat.cast_lt.mpr hgt
        simpa [Nat.cast_mul] using this
      have hmX : m ≤ (E.card : ℝ) :=
        le_trans hhi (le_of_lt (lt_trans (by linarith : (5 : ℝ) * L < 6 * (L : ℝ)) hX))
      have hgap : (L : ℝ) ≤ (E.card : ℝ) - m := by linarith
      rwa [abs_of_nonneg (sub_nonneg.mpr hmX)]
  have hexp :
      ∑ E ∈ A.powerset, ((E.card : ℝ) - m) ^ 2 * μ E =
        (∑ E ∈ A.powerset, (E.card : ℝ) ^ 2 * μ E) - m ^ 2 := by
    have hpt : ∀ E ∈ A.powerset,
        ((E.card : ℝ) - m) ^ 2 * μ E =
          (E.card : ℝ) ^ 2 * μ E - 2 * m * ((E.card : ℝ) * μ E) + m ^ 2 * μ E := by
      intro E _
      ring
    rw [sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl hpt, sum_add_distrib,
      sum_sub_distrib]
    have hlin :
        ∑ E ∈ A.powerset, (2 * m * ((E.card : ℝ) * μ E)) =
          2 * m * ∑ E ∈ A.powerset, (E.card : ℝ) * μ E := by
      rw [← mul_sum]
    have hsq :
        ∑ E ∈ A.powerset, m ^ 2 * μ E = m ^ 2 := by
      rw [← mul_sum, hsum1, mul_one]
    rw [hlin, hEN, hsq]
    ring
  have hVar' : ∑ E ∈ A.powerset, ((E.card : ℝ) - m) ^ 2 * μ E ≤ m := by
    rw [hexp]
    exact hVar
  have hbad :
      ((L : ℝ) ^ 2) *
          ∑ E ∈ A.powerset.filter
              (fun E => E.card < 2 * L ∨ 6 * L < E.card), μ E ≤
        ∑ E ∈ A.powerset.filter
            (fun E => E.card < 2 * L ∨ 6 * L < E.card),
          ((E.card : ℝ) - m) ^ 2 * μ E := by
    have hpt : ∀ E ∈ A.powerset.filter
          (fun E => E.card < 2 * L ∨ 6 * L < E.card),
        ((L : ℝ) ^ 2) * μ E ≤ ((E.card : ℝ) - m) ^ 2 * μ E := by
      intro E hE
      have hμ0 : 0 ≤ μ E := hnonneg E (mem_filter.mp hE).1
      have hsqle : (L : ℝ) ^ 2 ≤ ((E.card : ℝ) - m) ^ 2 := by
        have hL0 : 0 ≤ (L : ℝ) := le_of_lt hLpos
        have : |(L : ℝ)| ≤ |(E.card : ℝ) - m| := by
          rw [abs_of_nonneg hL0]
          exact hdev E hE
        exact sq_le_sq.mpr this
      exact mul_le_mul_of_nonneg_right hsqle hμ0
    have hLsq :
        ∑ E ∈ A.powerset.filter
            (fun E => E.card < 2 * L ∨ 6 * L < E.card), ((L : ℝ) ^ 2) * μ E =
          ((L : ℝ) ^ 2) *
            ∑ E ∈ A.powerset.filter
                (fun E => E.card < 2 * L ∨ 6 * L < E.card), μ E := by
      rw [← mul_sum]
    rw [← hLsq]
    exact sum_le_sum hpt
  have hbadle :
      ∑ E ∈ A.powerset.filter
          (fun E => E.card < 2 * L ∨ 6 * L < E.card),
        ((E.card : ℝ) - m) ^ 2 * μ E ≤
        ∑ E ∈ A.powerset, ((E.card : ℝ) - m) ^ 2 * μ E := by
    refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_
    intro E hE _h
    exact mul_nonneg (sq_nonneg _) (hnonneg E hE)
  have ht2 : 0 < (L : ℝ) ^ 2 := sq_pos_of_pos hLpos
  have hP :
      ∑ E ∈ A.powerset.filter (fun E => E.card < 2 * L ∨ 6 * L < E.card), μ E ≤
        m / (L : ℝ) ^ 2 := by
    have hmul : ((L : ℝ) ^ 2) *
        ∑ E ∈ A.powerset.filter
            (fun E => E.card < 2 * L ∨ 6 * L < E.card), μ E ≤ m :=
      hbad.trans (hbadle.trans hVar')
    exact (le_div_iff₀ ht2).mpr (by linarith [hmul])
  have hCL : m / (L : ℝ) ^ 2 ≤ C / (L : ℝ) := by
    have hm0 : 0 ≤ m := mul_nonneg (Nat.cast_nonneg _) (lateRetention_nonneg S y)
    have hnum : m ≤ C * (L : ℝ) := by
      simpa using hC
    have hL2 : 0 < (L : ℝ) ^ 2 := ht2
    have : m / (L : ℝ) ^ 2 ≤ (C * (L : ℝ)) / (L : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    have hsimpl : (C * (L : ℝ)) / (L : ℝ) ^ 2 = C / (L : ℝ) := by
      have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLpos
      field_simp [hLne, pow_two]
    exact this.trans_eq hsimpl
  exact hP.trans hCL

theorem countBandException (S y T L : ℕ) (hT : T ≤ S) :
    CountBandException S y T L := by
  intro hL σ A μ Mθ hlo hhi
  have hμ :
      CardinalitySymmetricMass A μ := by
    simpa [lateRootLaw] using
      lateProductMass_cardinalitySymmetric S y
        (lateCandidateSet_subset_Icc S T σ) hT
  have hMom :
      ExactCountMoments S y A μ := by
    simpa [lateRootLaw] using
      exactCountMoments_lateProductMass S y
        (lateCandidateSet_subset_Icc S T σ) hT
  exact countBand_of_second_moment (C := (5 : ℝ)) hμ hMom hL hlo hhi hhi

end PrimeGapNormality.Prime
