import PrimeGapNormality.Prime.CardinalitySymMass
import PrimeGapNormality.Prime.ActualRootLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nested cutoff comparison: full L1 of `actualRootLaw` (C1)+(C2)

Paper nested cutoffs `2 ≤ y₁ ≤ y₂` and physical window `T ≤ y₁`
(paper `S ≤ y₁`). Write `μ_i` for `actualRootLaw y_i T`. The same
nonzero residues through `y₁` give `U₂ ⊆ U₁`. Retention is

  `Theta = lateRetention y₁ y₂ = rootedEulerProdNat y₁ y₂`.

`M₁` is the mean cardinality `E_{μ₁} |U|`. Full L1-norm (not halved
TV):

  `∑_U |μ₁(U) − μ₂(U)| ≤ 2 M₁ (1 − Theta)`                             (C1)
  `|E_{μ₁} f − E_{μ₂} f| ≤ 2 M₁ (1 − Theta)` for `|f| ≤ 1` (ℂ or ℝ)   (C2)

Finite product / counting on late fibres: Dirac versus
`lateRootLaw` on `A.powerset`, then uniform average via
`actualRootLaw_eq_avg_lateRootLaw` with split `= y₁`. Does **not**
use Bernoulli approximation, `HLMismatchVanishes`, Weyl files, or
`Tendsto 0` of a Dirac HL mismatch.

Does **not** import MixZeta, SingletonLi, ExactRootWindowClose,
RootedCutoffTypicalOsc, ExactLawTypicalSetMassLeOne, WeylOf*,
CrtHLMismatchVanishing, or CrtMixtureTransfer.

**Compiled.**
1. `lateSurvivors ⊆ A`; `lateRootLaw = 0` off `A`.
2. `lateRootLaw S S` is Dirac at `A` (`latePrimes S S = ∅`).
3. Fibre Dirac-versus-late L1 equals `2 (1 − μ A)`.
4. `1 − μ A ≤ E |A \ U|` and `E |A \ U| = |A| (1 − lateRetention)`.
5. Fibre L1 `≤ 2 |A| (1 − Theta)`; window form of the same bound.
6. Mean cardinality identity: `M₁` is the average of
   `lateCandidateSet y₁ T`.
7. Nested `actualRootLaw` L1 ≤ `2 M₁ (1 − Theta)` (C1).
8. Bounded tests (C2), complex and real.

**Not compiled.** (C3) product/integral comparison. (C4) `O(L/G)` or
`M₁ ≤ 12 L`. `HLMismatchVanishes`. Bernoulli approximation.
`hoff` / `hcard`. Kernel close.

**Remaining hyps.** Nested binders `2 ≤ y₁ ≤ y₂` and `T ≤ y₁`.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| fibre Dirac vs `lateRootLaw` L1 `= 2(1−μ A)` | theorem |
| `1−μ A ≤ E\|A\U\| = \|A\|(1−Theta)` | theorem (`T ≤ S`) |
| fibre L1 `≤ 2 \|A\| (1−Theta)` | theorem |
| mixed L1 `≤ 2 M₁ (1−Theta)` (C1) | theorem (`2 ≤ y₁ ≤ y₂`, `T ≤ y₁`) |
| bounded-test mean (C2) | theorem (same binders) |
| `M₁` = average `lateCandidateSet` card | theorem |
| (C3) `1−Theta ≤ 1−R + 1/(y₁−1)` | not claimed |
| (C4) `O(L/G)`, `M₁ ≤ 12 L` | not claimed |
| `HLMismatchVanishes` | not claimed |
| Bernoulli / kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round115/09_grok_mixture_gate_and_cutoff_bridge.md` §2
(C1)(C2); `CardinalitySymMass.actualRootLaw_eq_avg_lateRootLaw`,
`lateProductMass_sum`, `lateProductMass_first_moment`,
`lateRetention`, `lateCandidateSet`.
Contract: API
Audit: GREEN
-/

open Finset
open scoped Classical

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

/-! ### Fibre support -/

/-- `lateSurvivors` is a filter of `A`. Unique name: the copy in
`CardinalitySymMass` is private. -/
theorem crtNestL1_lateSurvivors_subset (S y : ℕ) (A : Finset ℕ)
    (σ : LateResidueChoice S y) : lateSurvivors S y A σ ⊆ A :=
  filter_subset _ _

/-- Off-`A` configurations have late mass `0`. Unique name. -/
theorem crtNestL1_eq_zero_of_not_subset {S y : ℕ} {A E : Finset ℕ}
    (hE : ¬ E ⊆ A) : lateRootLaw S y A E = 0 := by
  have hempty :
      ((univ : Finset (LateResidueChoice S y)).filter
          fun σ => lateSurvivors S y A σ = E) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro σ hσ
    have hE' : lateSurvivors S y A σ = E := (mem_filter.mp hσ).2
    exact hE (hE' ▸ crtNestL1_lateSurvivors_subset S y A σ)
  simp [lateRootLaw, lateProductMass, hempty]

/-! ### Retention in `[0, 1]` -/

/-- Unconditional nonnegativity of `lateRetention`. Unique name. -/
theorem crtNestL1_lateRetention_nonneg (S y : ℕ) :
    0 ≤ lateRetention S y := by
  unfold lateRetention rootedEulerProdNat
  refine prod_nonneg fun p hp => ?_
  have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp'.two_le
  have hden : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hden)

/-- Product of factors in `[0, 1]`. Unique name. -/
theorem crtNestL1_lateRetention_le_one (S y : ℕ) :
    lateRetention S y ≤ 1 := by
  unfold lateRetention rootedEulerProdNat
  refine prod_le_one ?h0 ?h1
  · intro p hp
    have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
    have : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp'.two_le
    have hden : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hden)
  · intro p hp
    have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
    have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp'.two_le
    have hden : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    exact sub_le_self _ (inv_nonneg.mpr hden)

theorem crtNestL1_lateRetention_self (S : ℕ) : lateRetention S S = 1 := by
  unfold lateRetention rootedEulerProdNat
  rw [Finset.sdiff_self, Finset.prod_empty]

/-! ### Empty late primes at `y = S`: Dirac fibre -/

theorem crtNestL1_latePrime_isEmpty (S : ℕ) : IsEmpty (LatePrime S S) :=
  ⟨fun p =>
    have hp := mem_sdiff.mp p.property
    hp.2 hp.1⟩

/-- Remaining sieve is empty, so every late survivor set is `A`. -/
theorem crtNestL1_lateSurvivors_eq_self (S : ℕ) (A : Finset ℕ)
    (σ : LateResidueChoice S S) : lateSurvivors S S A σ = A := by
  unfold lateSurvivors
  refine filter_true_of_mem fun _n _hn p => ?_
  exact (crtNestL1_latePrime_isEmpty S).elim p

/-- `lateRootLaw S S` is Dirac at the candidate set. -/
theorem crtNestL1_lateRootLaw_eq_dirac (S : ℕ) (A E : Finset ℕ) :
    lateRootLaw S S A E = if E = A then 1 else 0 := by
  have hpos :
      ((univ : Finset (LateResidueChoice S S)).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (card_pos.mpr univ_nonempty))
  by_cases hEA : E = A
  · have hfilt :
        ((univ : Finset (LateResidueChoice S S)).filter
            fun σ => lateSurvivors S S A σ = E) =
          univ := by
      rw [hEA]
      exact filter_true_of_mem fun σ _ =>
        crtNestL1_lateSurvivors_eq_self S A σ
    have hmass : lateRootLaw S S A E = 1 := by
      simp only [lateRootLaw, lateProductMass, hfilt]
      exact div_self hpos
    rw [hmass, if_pos hEA]
  · have hempty :
        ((univ : Finset (LateResidueChoice S S)).filter
            fun σ => lateSurvivors S S A σ = E) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro σ hσ
      have hE' : lateSurvivors S S A σ = E := (mem_filter.mp hσ).2
      exact hEA
        (hE'.symm.trans (crtNestL1_lateSurvivors_eq_self S A σ))
    have hmass0 : lateRootLaw S S A E = 0 := by
      simp only [lateRootLaw, lateProductMass, hempty, card_empty,
        Nat.cast_zero, zero_div]
    rw [hmass0, if_neg hEA]

/-! ### Dirac versus a probability on `A.powerset` -/

/-- Full L1 of Dirac_A versus a nonnegative mass summing to `1`. -/
theorem crtNestL1_dirac_tv (S y : ℕ) (A : Finset ℕ) :
    ∑ E ∈ A.powerset,
        |(if E = A then (1 : ℝ) else 0) - lateRootLaw S y A E| =
      2 * (1 - lateRootLaw S y A A) := by
  set μ := lateRootLaw S y A
  have hnn : ∀ E ∈ A.powerset, 0 ≤ μ E := fun E _ =>
    lateProductMass_nonneg S y A E
  have hsum : ∑ E ∈ A.powerset, μ E = 1 := lateProductMass_sum S y A
  have hAmem : A ∈ A.powerset := mem_powerset.mpr Subset.rfl
  have hμle : μ A ≤ 1 := by
    have := single_le_sum hnn hAmem
    rwa [hsum] at this
  have h1μ : 0 ≤ 1 - μ A := sub_nonneg.mpr hμle
  have hpt : ∀ E ∈ A.powerset,
      |(if E = A then (1 : ℝ) else 0) - μ E| =
        if E = A then 1 - μ A else μ E := by
    intro E hE
    by_cases hEA : E = A
    · rw [if_pos hEA, if_pos hEA, hEA, abs_of_nonneg h1μ]
    · rw [if_neg hEA, if_neg hEA, zero_sub, abs_neg,
        abs_of_nonneg (hnn E hE)]
  have hsplit :
      ∑ E ∈ A.powerset, (if E = A then 1 - μ A else μ E) =
        (∑ E ∈ A.powerset, if E = A then 1 - μ A else (0 : ℝ)) +
          ∑ E ∈ A.powerset, if E = A then (0 : ℝ) else μ E := by
    have hpt' : ∀ E ∈ A.powerset,
        (if E = A then 1 - μ A else μ E) =
          (if E = A then 1 - μ A else (0 : ℝ)) +
            (if E = A then (0 : ℝ) else μ E) := by
      intro E _
      split_ifs <;> simp
    rw [sum_congr rfl hpt', sum_add_distrib]
  have hleft :
      ∑ E ∈ A.powerset, (if E = A then 1 - μ A else (0 : ℝ)) =
        1 - μ A :=
    sum_ite_eq_of_mem' A.powerset A (fun _ => 1 - μ A) hAmem
  have hAterm :
      ∑ E ∈ A.powerset, (if E = A then μ E else (0 : ℝ)) = μ A :=
    sum_ite_eq_of_mem' A.powerset A μ hAmem
  have hμsplit :
      ∑ E ∈ A.powerset, (if E = A then μ E else (0 : ℝ)) +
          ∑ E ∈ A.powerset, (if E = A then (0 : ℝ) else μ E) =
        ∑ E ∈ A.powerset, μ E := by
    have hptμ : ∀ E ∈ A.powerset,
        (if E = A then μ E else (0 : ℝ)) +
            (if E = A then (0 : ℝ) else μ E) =
          μ E := by
      intro E _
      split_ifs <;> simp
    rw [← sum_add_distrib]
    exact sum_congr rfl hptμ
  have hright :
      ∑ E ∈ A.powerset, (if E = A then (0 : ℝ) else μ E) =
        1 - μ A := by
    linarith
  rw [sum_congr rfl hpt, hsplit, hleft, hright]
  ring

/-- Strict inclusion of finite sets gives a real gap of at least `1`. -/
theorem crtNestL1_card_gap_ge_one {A E : Finset ℕ}
    (hE : E ∈ A.powerset) (hne : E ≠ A) :
    (1 : ℝ) ≤ (A.card : ℝ) - (E.card : ℝ) := by
  have hss : E ⊂ A :=
    Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hE, hne⟩
  have hlt : E.card < A.card := card_lt_card hss
  have hnat : (1 : ℕ) ≤ A.card - E.card :=
    Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hlt)
  have hcast : ((A.card - E.card : ℕ) : ℝ) =
      (A.card : ℝ) - (E.card : ℝ) :=
    Nat.cast_sub (le_of_lt hlt)
  have : (1 : ℝ) ≤ ((A.card - E.card : ℕ) : ℝ) := by exact_mod_cast hnat
  rwa [hcast] at this

/-- `P(U ≠ A) ≤ E |A \ U|` on the fibre: `U ⊆ A` almost surely. -/
theorem crtNestL1_miss_le_meanGap (S y : ℕ) (A : Finset ℕ) :
    1 - lateRootLaw S y A A ≤
      ∑ E ∈ A.powerset,
        ((A.card : ℝ) - (E.card : ℝ)) * lateRootLaw S y A E := by
  set μ := lateRootLaw S y A
  have hnn : ∀ E ∈ A.powerset, 0 ≤ μ E := fun E _ =>
    lateProductMass_nonneg S y A E
  have hsum : ∑ E ∈ A.powerset, μ E = 1 := lateProductMass_sum S y A
  have hAmem : A ∈ A.powerset := mem_powerset.mpr Subset.rfl
  have hAterm :
      ∑ E ∈ A.powerset, (if E = A then μ E else (0 : ℝ)) = μ A :=
    sum_ite_eq_of_mem' A.powerset A μ hAmem
  have hμsplit :
      ∑ E ∈ A.powerset, (if E = A then μ E else (0 : ℝ)) +
          ∑ E ∈ A.powerset, (if E = A then (0 : ℝ) else μ E) =
        ∑ E ∈ A.powerset, μ E := by
    have hptμ : ∀ E ∈ A.powerset,
        (if E = A then μ E else (0 : ℝ)) +
            (if E = A then (0 : ℝ) else μ E) =
          μ E := by
      intro E _
      split_ifs <;> simp
    rw [← sum_add_distrib]
    exact sum_congr rfl hptμ
  have hmiss :
      ∑ E ∈ A.powerset, (if E = A then (0 : ℝ) else μ E) =
        1 - μ A := by
    linarith
  have hle : ∀ E ∈ A.powerset,
      (if E = A then (0 : ℝ) else μ E) ≤
        ((A.card : ℝ) - (E.card : ℝ)) * μ E := by
    intro E hE
    by_cases hEA : E = A
    · subst hEA
      simp
    · rw [if_neg hEA]
      have := mul_le_mul_of_nonneg_right
        (crtNestL1_card_gap_ge_one hE hEA) (hnn E hE)
      rwa [one_mul] at this
  have hle_sum := sum_le_sum hle
  rw [hmiss] at hle_sum
  exact hle_sum

/-- First-moment identity: `E |A \ U| = |A| (1 − Theta)`. -/
theorem crtNestL1_meanGap_eq (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    ∑ E ∈ A.powerset,
        ((A.card : ℝ) - (E.card : ℝ)) * lateRootLaw S y A E =
      (A.card : ℝ) * (1 - lateRetention S y) := by
  have hsum : ∑ E ∈ A.powerset, lateRootLaw S y A E = 1 :=
    lateProductMass_sum S y A
  have h1 := lateProductMass_first_moment S y hA hT
  have hpt : ∀ E ∈ A.powerset,
      ((A.card : ℝ) - (E.card : ℝ)) * lateRootLaw S y A E =
        (A.card : ℝ) * lateRootLaw S y A E -
          (E.card : ℝ) * lateRootLaw S y A E := by
    intro E _
    ring
  rw [sum_congr rfl hpt, sum_sub_distrib, ← mul_sum, hsum, mul_one, h1]
  ring

/-- Fibre L1 of Dirac versus `lateRootLaw` is at most
`2 |A| (1 − Theta)`. -/
theorem crtNestL1_fibre_massL1_le (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    ∑ E ∈ A.powerset,
        |(if E = A then (1 : ℝ) else 0) - lateRootLaw S y A E| ≤
      2 * (A.card : ℝ) * (1 - lateRetention S y) := by
  have htv := crtNestL1_dirac_tv S y A
  have hmiss := crtNestL1_miss_le_meanGap S y A
  have hgap := crtNestL1_meanGap_eq S y hA hT
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hbound :
      2 * (1 - lateRootLaw S y A A) ≤
        2 * ((A.card : ℝ) * (1 - lateRetention S y)) :=
    mul_le_mul_of_nonneg_left (hmiss.trans_eq hgap) h2
  have hre :
      2 * ((A.card : ℝ) * (1 - lateRetention S y)) =
        2 * (A.card : ℝ) * (1 - lateRetention S y) := by
    ring
  rw [htv]
  exact hbound.trans_eq hre

/-- Window L1 equals fibre L1: mass vanishes off `A`. -/
theorem crtNestL1_fibre_window_massL1_eq (S y : ℕ) {T : ℕ}
    {A : Finset ℕ} (hA : A ⊆ offsetWindow T) :
    ∑ U ∈ (offsetWindow T).powerset,
        |(if U = A then (1 : ℝ) else 0) - lateRootLaw S y A U| =
      ∑ E ∈ A.powerset,
        |(if E = A then (1 : ℝ) else 0) - lateRootLaw S y A E| := by
  have hsub : A.powerset ⊆ (offsetWindow T).powerset :=
    powerset_mono.mpr hA
  let f : Finset ℕ → ℝ := fun U =>
    |(if U = A then (1 : ℝ) else 0) - lateRootLaw S y A U|
  have hvan : ∀ U ∈ (offsetWindow T).powerset, U ∉ A.powerset → f U = 0 := by
    intro U _hU hnot
    have hnotA : ¬ U ⊆ A := fun hUA => hnot (mem_powerset.mpr hUA)
    have hne : U ≠ A := fun h => hnotA (h ▸ Subset.rfl)
    simp only [f]
    rw [if_neg hne, crtNestL1_eq_zero_of_not_subset hnotA, sub_zero,
      abs_zero]
  exact (Finset.sum_subset (s₁ := A.powerset)
      (s₂ := (offsetWindow T).powerset) hsub hvan).symm

theorem crtNestL1_fibre_window_massL1_le (S y : ℕ) {T : ℕ}
    {A : Finset ℕ} (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    ∑ U ∈ (offsetWindow T).powerset,
        |(if U = A then (1 : ℝ) else 0) - lateRootLaw S y A U| ≤
      2 * (A.card : ℝ) * (1 - lateRetention S y) := by
  have hwin : A ⊆ offsetWindow T := hA
  rw [crtNestL1_fibre_window_massL1_eq S y hwin]
  exact crtNestL1_fibre_massL1_le S y hA hT

/-- Nested fibre: Dirac at the split versus later `lateRootLaw`. -/
theorem crtNestL1_nested_fibre_window_massL1_le (S y : ℕ) {T : ℕ}
    {A : Finset ℕ} (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    ∑ U ∈ (offsetWindow T).powerset,
        |lateRootLaw S S A U - lateRootLaw S y A U| ≤
      2 * (A.card : ℝ) * (1 - lateRetention S y) := by
  have hpt : ∀ U ∈ (offsetWindow T).powerset,
      |lateRootLaw S S A U - lateRootLaw S y A U| =
        |(if U = A then (1 : ℝ) else 0) - lateRootLaw S y A U| := by
    intro U _
    rw [crtNestL1_lateRootLaw_eq_dirac]
  rw [sum_congr rfl hpt]
  exact crtNestL1_fibre_window_massL1_le S y hA hT

/-! ### Mean cardinality of `actualRootLaw` at the split -/

/-- `M₁ = E_{μ₁} |U|` equals the average late-candidate cardinality. -/
theorem crtNestL1_meanCard (y T : ℕ) (hT : T ≤ y) :
    ∑ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U =
      (∑ σ ∈ (univ : Finset (ResidueChoice y)),
          ((lateCandidateSet y T σ).card : ℝ)) /
        (Fintype.card (ResidueChoice y) : ℝ) := by
  have hpt :
      ∀ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U =
          (U.card : ℝ) *
            ((∑ σ ∈ (univ : Finset (ResidueChoice y)),
                lateRootLaw y y (lateCandidateSet y T σ) U) /
              (Fintype.card (ResidueChoice y) : ℝ)) := by
    intro U _
    rw [actualRootLaw_eq_avg_lateRootLaw y y T hT le_rfl]
  rw [sum_congr rfl hpt]
  have hdiv : ∀ U ∈ (offsetWindow T).powerset,
      (U.card : ℝ) *
          ((∑ σ ∈ (univ : Finset (ResidueChoice y)),
              lateRootLaw y y (lateCandidateSet y T σ) U) /
            (Fintype.card (ResidueChoice y) : ℝ)) =
        ((U.card : ℝ) *
            ∑ σ ∈ (univ : Finset (ResidueChoice y)),
              lateRootLaw y y (lateCandidateSet y T σ) U) /
          (Fintype.card (ResidueChoice y) : ℝ) := by
    intro U _
    exact (mul_div_assoc (U.card : ℝ)
      (∑ σ ∈ (univ : Finset (ResidueChoice y)),
        lateRootLaw y y (lateCandidateSet y T σ) U)
      (Fintype.card (ResidueChoice y) : ℝ)).symm
  rw [sum_congr rfl hdiv, ← sum_div]
  congr 1
  have hmul :
      ∑ U ∈ (offsetWindow T).powerset,
          (U.card : ℝ) *
            ∑ σ ∈ (univ : Finset (ResidueChoice y)),
              lateRootLaw y y (lateCandidateSet y T σ) U =
        ∑ U ∈ (offsetWindow T).powerset,
          ∑ σ ∈ (univ : Finset (ResidueChoice y)),
            (U.card : ℝ) *
              lateRootLaw y y (lateCandidateSet y T σ) U := by
    refine sum_congr rfl fun U _ => ?_
    rw [mul_sum]
  rw [hmul]
  have hswap :
      ∑ U ∈ (offsetWindow T).powerset,
          ∑ σ ∈ (univ : Finset (ResidueChoice y)),
            (U.card : ℝ) *
              lateRootLaw y y (lateCandidateSet y T σ) U =
        ∑ σ ∈ (univ : Finset (ResidueChoice y)),
          ∑ U ∈ (offsetWindow T).powerset,
            (U.card : ℝ) *
              lateRootLaw y y (lateCandidateSet y T σ) U :=
    sum_comm
  rw [hswap]
  refine sum_congr rfl fun σ _ => ?_
  set A := lateCandidateSet y T σ
  have hwin : A ⊆ offsetWindow T := by
    simpa [offsetWindow] using lateCandidateSet_subset_Icc y T σ
  have hAin : A ∈ (offsetWindow T).powerset := mem_powerset.mpr hwin
  have hptU : ∀ U ∈ (offsetWindow T).powerset,
      (U.card : ℝ) * lateRootLaw y y A U =
        if U = A then (U.card : ℝ) else 0 := by
    intro U _
    rw [crtNestL1_lateRootLaw_eq_dirac]
    split_ifs with hUA
    · rw [mul_one]
    · rw [mul_zero]
  rw [sum_congr rfl hptU,
    sum_ite_eq_of_mem' (offsetWindow T).powerset A
      (fun U => (U.card : ℝ)) hAin]

/-! ### Mixed nested L1 (C1) and bounded tests (C2) -/

/-- Full L1 of nested `actualRootLaw`. Paper (C1). Does **not** claim
`O(L/G)` or `M₁ ≤ 12 L`. -/
theorem crtNestL1_massL1_le (y1 y2 T : ℕ)
    (hy : 2 ≤ y1) (h12 : y1 ≤ y2) (hT : T ≤ y1) :
    ∑ U ∈ (offsetWindow T).powerset,
        |actualRootLaw y1 T U - actualRootLaw y2 T U| ≤
      2 *
        (∑ U ∈ (offsetWindow T).powerset,
            (U.card : ℝ) * actualRootLaw y1 T U) *
        (1 - lateRetention y1 y2) := by
  have hθ0 : 0 ≤ lateRetention y1 y2 := by
    unfold lateRetention
    exact (rootedEulerProdNat_pos hy).le
  have hθ1 : lateRetention y1 y2 ≤ 1 :=
    crtNestL1_lateRetention_le_one y1 y2
  have hNpos : 0 < (Fintype.card (ResidueChoice y1) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  set N := (Fintype.card (ResidueChoice y1) : ℝ)
  set θ := lateRetention y1 y2
  set Ω := (offsetWindow T).powerset
  have hNdef : N = (Fintype.card (ResidueChoice y1) : ℝ) := rfl
  have hdiff : ∀ U,
      actualRootLaw y1 T U - actualRootLaw y2 T U =
        (∑ σ ∈ (univ : Finset (ResidueChoice y1)),
            (lateRootLaw y1 y1 (lateCandidateSet y1 T σ) U -
              lateRootLaw y1 y2 (lateCandidateSet y1 T σ) U)) / N := by
    intro U
    have h1 := actualRootLaw_eq_avg_lateRootLaw y1 y1 T hT le_rfl U
    have h2 := actualRootLaw_eq_avg_lateRootLaw y1 y2 T hT h12 U
    rw [h1, h2, ← hNdef, div_sub_div_same, ← sum_sub_distrib]
  have habsU : ∀ U ∈ Ω,
      |actualRootLaw y1 T U - actualRootLaw y2 T U| ≤
        (∑ σ ∈ (univ : Finset (ResidueChoice y1)),
            |lateRootLaw y1 y1 (lateCandidateSet y1 T σ) U -
              lateRootLaw y1 y2 (lateCandidateSet y1 T σ) U|) / N := by
    intro U _hU
    rw [hdiff U, abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right
      (abs_sum_le_sum_abs
        (fun σ =>
          lateRootLaw y1 y1 (lateCandidateSet y1 T σ) U -
            lateRootLaw y1 y2 (lateCandidateSet y1 T σ) U)
        (univ : Finset (ResidueChoice y1)))
      (le_of_lt hNpos)
  have hsumU := sum_le_sum habsU
  have hdiv :
      ∑ U ∈ Ω,
          (∑ σ ∈ (univ : Finset (ResidueChoice y1)),
              |lateRootLaw y1 y1 (lateCandidateSet y1 T σ) U -
                lateRootLaw y1 y2 (lateCandidateSet y1 T σ) U|) / N =
        (∑ U ∈ Ω,
            ∑ σ ∈ (univ : Finset (ResidueChoice y1)),
              |lateRootLaw y1 y1 (lateCandidateSet y1 T σ) U -
                lateRootLaw y1 y2 (lateCandidateSet y1 T σ) U|) / N := by
    rw [← sum_div]
  have hswap :
      ∑ U ∈ Ω,
          ∑ σ ∈ (univ : Finset (ResidueChoice y1)),
            |lateRootLaw y1 y1 (lateCandidateSet y1 T σ) U -
              lateRootLaw y1 y2 (lateCandidateSet y1 T σ) U| =
        ∑ σ ∈ (univ : Finset (ResidueChoice y1)),
          ∑ U ∈ Ω,
            |lateRootLaw y1 y1 (lateCandidateSet y1 T σ) U -
              lateRootLaw y1 y2 (lateCandidateSet y1 T σ) U| :=
    sum_comm
  have hfib : ∀ σ ∈ (univ : Finset (ResidueChoice y1)),
      ∑ U ∈ Ω,
          |lateRootLaw y1 y1 (lateCandidateSet y1 T σ) U -
            lateRootLaw y1 y2 (lateCandidateSet y1 T σ) U| ≤
        2 * ((lateCandidateSet y1 T σ).card : ℝ) * (1 - θ) :=
    fun σ _ =>
      crtNestL1_nested_fibre_window_massL1_le y1 y2
        (lateCandidateSet_subset_Icc y1 T σ) hT
  have hsumσ := sum_le_sum hfib
  have hfact :
      ∑ σ ∈ (univ : Finset (ResidueChoice y1)),
          2 * ((lateCandidateSet y1 T σ).card : ℝ) * (1 - θ) =
        2 * (1 - θ) *
          ∑ σ ∈ (univ : Finset (ResidueChoice y1)),
            ((lateCandidateSet y1 T σ).card : ℝ) := by
    have hpt : ∀ σ ∈ (univ : Finset (ResidueChoice y1)),
        2 * ((lateCandidateSet y1 T σ).card : ℝ) * (1 - θ) =
          (2 * (1 - θ)) *
            ((lateCandidateSet y1 T σ).card : ℝ) := by
      intro σ _
      ring
    rw [sum_congr rfl hpt, ← mul_sum]
  have hchain :
      ∑ U ∈ Ω, |actualRootLaw y1 T U - actualRootLaw y2 T U| ≤
        (2 * (1 - θ) *
            ∑ σ ∈ (univ : Finset (ResidueChoice y1)),
              ((lateCandidateSet y1 T σ).card : ℝ)) / N := by
    have h1 := hsumU.trans_eq hdiv
    have h2 := h1.trans_eq (by rw [hswap])
    have h3 :=
      div_le_div_of_nonneg_right (hsumσ.trans_eq hfact) (le_of_lt hNpos)
    exact h2.trans h3
  have hM :
      (∑ σ ∈ (univ : Finset (ResidueChoice y1)),
          ((lateCandidateSet y1 T σ).card : ℝ)) / N =
        ∑ U ∈ Ω, (U.card : ℝ) * actualRootLaw y1 T U := by
    have := crtNestL1_meanCard y1 T hT
    simpa [N, Ω] using this.symm
  have hre :
      (2 * (1 - θ) *
          ∑ σ ∈ (univ : Finset (ResidueChoice y1)),
            ((lateCandidateSet y1 T σ).card : ℝ)) / N =
        2 *
          ((∑ σ ∈ (univ : Finset (ResidueChoice y1)),
              ((lateCandidateSet y1 T σ).card : ℝ)) / N) *
          (1 - θ) := by
    calc
      (2 * (1 - θ) *
            ∑ σ ∈ (univ : Finset (ResidueChoice y1)),
              ((lateCandidateSet y1 T σ).card : ℝ)) / N
          = (2 * (1 - θ)) *
              ((∑ σ ∈ (univ : Finset (ResidueChoice y1)),
                  ((lateCandidateSet y1 T σ).card : ℝ)) / N) :=
            mul_div_assoc _ _ _
      _ = 2 *
            ((∑ σ ∈ (univ : Finset (ResidueChoice y1)),
                ((lateCandidateSet y1 T σ).card : ℝ)) / N) *
            (1 - θ) := by
            ring
  have hθ01 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  exact (hchain.trans_eq hre).trans_eq (by rw [hM])

/-- Complex bounded test. Paper (C2). Unique name: not `massL1`. -/
theorem crtNestL1_abs_mean_sub_le (y1 y2 T : ℕ)
    (hy : 2 ≤ y1) (h12 : y1 ≤ y2) (hT : T ≤ y1)
    (F : Finset ℕ → ℂ) (hF : ∀ U, ‖F U‖ ≤ 1) :
    ‖∑ U ∈ (offsetWindow T).powerset,
        ((actualRootLaw y1 T U - actualRootLaw y2 T U : ℝ) : ℂ) *
          F U‖ ≤
      2 *
        (∑ U ∈ (offsetWindow T).powerset,
            (U.card : ℝ) * actualRootLaw y1 T U) *
        (1 - lateRetention y1 y2) := by
  have hL1 := crtNestL1_massL1_le y1 y2 T hy h12 hT
  have hpt : ∀ U ∈ (offsetWindow T).powerset,
      ‖((actualRootLaw y1 T U - actualRootLaw y2 T U : ℝ) : ℂ) *
          F U‖ ≤
        |actualRootLaw y1 T U - actualRootLaw y2 T U| := by
    intro U _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hF U)
  exact (norm_sum_le (offsetWindow T).powerset
      (fun U =>
        ((actualRootLaw y1 T U - actualRootLaw y2 T U : ℝ) : ℂ) *
          F U)).trans
    ((sum_le_sum hpt).trans hL1)

/-- Real bounded test. Paper (C2). -/
theorem crtNestL1_abs_mean_sub_le_real (y1 y2 T : ℕ)
    (hy : 2 ≤ y1) (h12 : y1 ≤ y2) (hT : T ≤ y1)
    (f : Finset ℕ → ℝ) (hf : ∀ U, |f U| ≤ 1) :
    |∑ U ∈ (offsetWindow T).powerset,
        (actualRootLaw y1 T U - actualRootLaw y2 T U) * f U| ≤
      2 *
        (∑ U ∈ (offsetWindow T).powerset,
            (U.card : ℝ) * actualRootLaw y1 T U) *
        (1 - lateRetention y1 y2) := by
  have hL1 := crtNestL1_massL1_le y1 y2 T hy h12 hT
  have hpt : ∀ U ∈ (offsetWindow T).powerset,
      |(actualRootLaw y1 T U - actualRootLaw y2 T U) * f U| ≤
        |actualRootLaw y1 T U - actualRootLaw y2 T U| := by
    intro U _
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hf U)
  exact (abs_sum_le_sum_abs
        (fun U => (actualRootLaw y1 T U - actualRootLaw y2 T U) * f U)
        (offsetWindow T).powerset).trans
    ((sum_le_sum hpt).trans hL1)

end

end PrimeGapNormality.Prime
