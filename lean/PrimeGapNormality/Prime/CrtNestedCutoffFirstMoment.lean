import PrimeGapNormality.Prime.CardinalitySymMass
import PrimeGapNormality.Prime.ModelConcentration
import PrimeGapNormality.Prime.PresieveWindowS
import PrimeGapNormality.Prime.SieveCutoffCal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nested cutoffs: model first moment `M₁` of `actualRootLaw`

Paper `M₁ = E_μ |U|` for `μ = actualRootLaw y T` (cutoff `y`,
physical window `T`, with a split `T ≤ S ≤ y`). This is the mean
cardinality that enters the nested-cutoff L1 bound
`∑ |μ₁ − μ₂| ≤ 2 M₁ (1 − Θ)`. It is **not** a Weyl hypothesis.

The exact identity is the residue average of the late-fibre first
moment `lateProductMass_first_moment` (equivalently
`exactCountMoments_lateRootLaw`) via
`actualRootLaw_eq_avg_lateRootLaw`. Independent Bernoulli thinning
is instantiated only as a **fibre first-moment comparison**
(`bernoulliThin_choose_moment` at `j = 1`); it does not replace `μ`.

`M₁ ≤ 12 L` is the `j = 1` case of the v0.8 model-moment hull. It is
obtained by instantiating `factorialMoment_le_twelve` on the uniform
residue law of the split, with the remaining good-event / exception /
crude `C₁ log S̄` hypotheses kept as binders. Those events are **not**
proved here. Unconditional `M₁ ≤ 12 L` is therefore remaining.

Does **not** import `CrtNestedCutoffL1`, MixZeta, SingletonLi,
ExactRootWindowClose, RootedCutoffTypicalOsc,
ExactLawTypicalSetMassLeOne, WeylOf*, CrtHLMismatchVanishing,
CrtMixtureTransfer, or CrtFailureMassLimit.

Does **not** claim (C4) `O(L/G)`, `HLMismatchVanishes`, `hoff` /
`hcard`, or that the kernel is closed.

**Compiled.**
1. `lateRetention ∈ [0, 1]`; `lateRetention y y = 1`.
2. `actualRootLaw` is a probability on `(offsetWindow T).powerset`.
3. Fibre first moment: `E |U| = |A| θ` on `lateRootLaw`.
4. Window form of the fibre identity (mass vanishes off `A`).
5. Mixed identity: `M₁ =` average of `|A_σ| θ` (`T ≤ S ≤ y`).
6. At the split `S = y`: `M₁` is the average of
   `(lateCandidateSet y T σ).card`.
7. Crude: `M₁ ≤ T` and `M₁ ≤` average `|A|`.
8. Bernoulli versus late first moments agree on a fibre (`j = 1`).
9. `factorialMoment _ _ 1` is the first moment.
10. `M₁ ≤ 12 L` from `factorialMoment_le_twelve` at `j = 1`
    (exception / `6 L` / `C₁ log S̄` remaining).
11. `ModelMomentHull` at `j = 1` from that bound.
12. Physical identity and the same `12 L` wrapper at
    `y = sieveCutoff X`, `T = profileS κ X`.

**Not compiled.** (C4) `O(L/G)`. Unconditional `M₁ ≤ 12 L`
(exception not discharged). (C1) L1. `HLMismatchVanishes`.
`hoff` / `hcard`. Kernel close.

**Remaining hyps.** Binders `T ≤ S ≤ y`. For `12 L`: complementary
mass `≤ ε` of the good event `θ N ≤ 6 L`, crude bound
`θ N ≤ C₁ L log S̄`, and `ε (C₁ log S̄ / 6) ≤ 1`. Physical
`profileS ≤ sieveCutoff` remains as a binder (this leaf does not
import `ProfileSLeSieveCutoff` / `CrtFailureMassLimit`). Kernel not
closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `M₁` = residue average of `\|A\| θ` | theorem (`crtNestFM_meanCard_eq_avg`) |
| `M₁` = average `lateCandidateSet y T` card | theorem (`crtNestFM_meanCard`; `T ≤ y`) |
| `M₁ ≤ T` | theorem (`crtNestFM_meanCard_le_T`) |
| `M₁ ≤` average `\|A\|` | theorem (`θ ≤ 1`) |
| fibre Bernoulli vs late first moments | theorem (comparison, not a law swap) |
| `M₁ ≤ 12 L` | theorem (`crtNestFM_meanCard_le_twelve`; exception / `6 L` / `C₁ log S̄` remaining) |
| `ModelMomentHull` at `j = 1` | theorem (same remaining hyps) |
| unconditional `M₁ ≤ 12 L` | remaining (exception not discharged) |
| (C4) `O(L/G)` | not claimed |
| `HLMismatchVanishes` / `hoff` / `hcard` | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round115/09_grok_mixture_gate_and_cutoff_bridge.md` §3
before `(C4)`; `CardinalitySymMass.lateProductMass_first_moment`,
`actualRootLaw_eq_avg_lateRootLaw`, `lateCandidateSet`;
`ModelConcentration.factorialMoment_le_twelve`;
`PresieveWindowS.ModelMomentHull`,
`factorialMoment_le_twelve_of_six_exception`.
Contract: API
Audit: GREEN
-/

open Finset
open scoped Classical

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

/-! ### Retention in `[0, 1]` -/

/-- Unconditional nonnegativity of `lateRetention`. Unique name. -/
theorem crtNestFM_lateRetention_nonneg (S y : ℕ) :
    0 ≤ lateRetention S y := by
  unfold lateRetention rootedEulerProdNat
  refine prod_nonneg fun p hp => ?_
  have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp'.two_le
  have hden : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hden)

/-- Product of factors in `[0, 1]`. Unique name. -/
theorem crtNestFM_lateRetention_le_one (S y : ℕ) :
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

theorem crtNestFM_lateRetention_self (S : ℕ) : lateRetention S S = 1 := by
  unfold lateRetention rootedEulerProdNat
  rw [Finset.sdiff_self, Finset.prod_empty]

/-! ### `actualRootLaw` is a probability -/

theorem crtNestFM_residueChoice_card_pos (y : ℕ) :
    0 < Fintype.card (ResidueChoice y) :=
  Fintype.card_pos

theorem crtNestFM_residueChoice_card_ne_zero (y : ℕ) :
    (Fintype.card (ResidueChoice y) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr
    (Nat.pos_iff_ne_zero.mp (crtNestFM_residueChoice_card_pos y))

theorem crtNestFM_resUnif_sum (S : ℕ) :
    ∑ σ ∈ (univ : Finset (ResidueChoice S)),
        (1 : ℝ) / (Fintype.card (ResidueChoice S) : ℝ) = 1 := by
  rw [sum_const, nsmul_eq_mul, card_univ]
  exact mul_one_div_cancel (crtNestFM_residueChoice_card_ne_zero S)

theorem crtNestFM_sieveSurvivorsFin_mem_powerset
    (y S : ℕ) (σ : ResidueChoice y) :
    sieveSurvivorsFin y σ S ∈ (offsetWindow S).powerset :=
  mem_powerset.mpr (filter_subset _ _)

theorem crtNestFM_actualRootLaw_nonneg (y S : ℕ) (U : Finset ℕ) :
    0 ≤ actualRootLaw y S U :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Every residue choice lands in the powerset, so the masses
partition `1`. Unique name. -/
theorem crtNestFM_actualRootLaw_sum (y S : ℕ) :
    ∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U = 1 := by
  have hmaps :
      ((univ : Finset (ResidueChoice y)) : Set (ResidueChoice y)).MapsTo
        (fun σ => sieveSurvivorsFin y σ S) (offsetWindow S).powerset :=
    fun σ _ => crtNestFM_sieveSurvivorsFin_mem_powerset y S σ
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
  exact div_self (crtNestFM_residueChoice_card_ne_zero y)

/-! ### Fibre first moment -/

/-- Unique name: the copy in `CardinalitySymMass` is private. -/
theorem crtNestFM_lateSurvivors_subset (S y : ℕ) (A : Finset ℕ)
    (σ : LateResidueChoice S y) : lateSurvivors S y A σ ⊆ A :=
  filter_subset _ _

theorem crtNestFM_lateRootLaw_eq_zero_of_not_subset
    {S y : ℕ} {A E : Finset ℕ} (hE : ¬ E ⊆ A) :
    lateRootLaw S y A E = 0 := by
  have hempty :
      ((univ : Finset (LateResidueChoice S y)).filter
          fun σ => lateSurvivors S y A σ = E) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro σ hσ
    have hE' : lateSurvivors S y A σ = E := (mem_filter.mp hσ).2
    exact hE (hE' ▸ crtNestFM_lateSurvivors_subset S y A σ)
  simp only [lateRootLaw, lateProductMass, hempty, card_empty,
    Nat.cast_zero, zero_div]

/-- Fibre form of `lateProductMass_first_moment`. Remaining: `T ≤ S`. -/
theorem crtNestFM_fibre_first_moment (S y : ℕ) {T : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    ∑ E ∈ A.powerset, (E.card : ℝ) * lateRootLaw S y A E =
      (A.card : ℝ) * lateRetention S y :=
  lateProductMass_first_moment S y hA hT

/-- Window form: late mass vanishes off `A`. Remaining: `T ≤ S`. -/
theorem crtNestFM_fibre_window_first_moment (S y : ℕ) {T : ℕ}
    {A : Finset ℕ} (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    ∑ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * lateRootLaw S y A U =
      (A.card : ℝ) * lateRetention S y := by
  have hwin : A ⊆ offsetWindow T := hA
  have hsub : A.powerset ⊆ (offsetWindow T).powerset :=
    powerset_mono.mpr hwin
  let f : Finset ℕ → ℝ := fun U =>
    (U.card : ℝ) * lateRootLaw S y A U
  have hzero :
      ∑ U ∈ (offsetWindow T).powerset, f U =
        ∑ E ∈ A.powerset, f E :=
    (Finset.sum_subset (s₁ := A.powerset)
        (s₂ := (offsetWindow T).powerset) (f := f) hsub
        fun U _hU hnot => by
      have hnotA : ¬ U ⊆ A := fun hUA => hnot (mem_powerset.mpr hUA)
      simp only [f]
      rw [crtNestFM_lateRootLaw_eq_zero_of_not_subset hnotA, mul_zero]).symm
  simpa [f] using hzero.trans (crtNestFM_fibre_first_moment S y hA hT)

/-! ### Mixed first-moment identity -/

/-- `M₁ =` residue average of `|A_σ| θ`. Remaining: `T ≤ S ≤ y`.
Does **not** name this `crtNestL1_meanCard`. -/
theorem crtNestFM_meanCard_eq_avg (S y T : ℕ) (hTS : T ≤ S) (hSy : S ≤ y) :
    ∑ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U =
      (∑ σ ∈ (univ : Finset (ResidueChoice S)),
          ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  have hpt :
      ∀ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U =
          (U.card : ℝ) *
            ((∑ σ ∈ (univ : Finset (ResidueChoice S)),
                lateRootLaw S y (lateCandidateSet S T σ) U) /
              (Fintype.card (ResidueChoice S) : ℝ)) := by
    intro U _
    rw [actualRootLaw_eq_avg_lateRootLaw S y T hTS hSy]
  rw [sum_congr (s₁ := (offsetWindow T).powerset)
      (s₂ := (offsetWindow T).powerset) rfl hpt]
  have hdiv :
      ∀ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) *
            ((∑ σ ∈ (univ : Finset (ResidueChoice S)),
                lateRootLaw S y (lateCandidateSet S T σ) U) /
              (Fintype.card (ResidueChoice S) : ℝ)) =
          ((U.card : ℝ) *
              ∑ σ ∈ (univ : Finset (ResidueChoice S)),
                lateRootLaw S y (lateCandidateSet S T σ) U) /
            (Fintype.card (ResidueChoice S) : ℝ) := by
    intro U _
    exact (mul_div_assoc (U.card : ℝ)
      (∑ σ ∈ (univ : Finset (ResidueChoice S)),
          lateRootLaw S y (lateCandidateSet S T σ) U)
      (Fintype.card (ResidueChoice S) : ℝ)).symm
  rw [sum_congr (s₁ := (offsetWindow T).powerset)
      (s₂ := (offsetWindow T).powerset) rfl hdiv, ← sum_div]
  congr 1
  have hmul :
      ∑ U ∈ (offsetWindow T).powerset,
          (U.card : ℝ) *
            ∑ σ ∈ (univ : Finset (ResidueChoice S)),
              lateRootLaw S y (lateCandidateSet S T σ) U =
        ∑ U ∈ (offsetWindow T).powerset,
          ∑ σ ∈ (univ : Finset (ResidueChoice S)),
            (U.card : ℝ) *
              lateRootLaw S y (lateCandidateSet S T σ) U := by
    refine sum_congr (s₁ := (offsetWindow T).powerset)
        (s₂ := (offsetWindow T).powerset) rfl fun U _ => ?_
    rw [mul_sum]
  rw [hmul, sum_comm]
  refine sum_congr (s₁ := univ) (s₂ := univ) rfl fun σ _ => ?_
  exact crtNestFM_fibre_window_first_moment S y
    (lateCandidateSet_subset_Icc S T σ) hTS

/-- Same identity with `θ` factored. Remaining: `T ≤ S ≤ y`. -/
theorem crtNestFM_meanCard_eq_theta_avg
    (S y T : ℕ) (hTS : T ≤ S) (hSy : S ≤ y) :
    ∑ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U =
      lateRetention S y *
        ((∑ σ ∈ (univ : Finset (ResidueChoice S)),
            ((lateCandidateSet S T σ).card : ℝ)) /
          (Fintype.card (ResidueChoice S) : ℝ)) := by
  rw [crtNestFM_meanCard_eq_avg S y T hTS hSy]
  have hpt :
      ∀ σ ∈ (univ : Finset (ResidueChoice S)),
        ((lateCandidateSet S T σ).card : ℝ) * lateRetention S y =
          lateRetention S y * (lateCandidateSet S T σ).card := fun σ _ =>
    mul_comm _ _
  rw [sum_congr (s₁ := univ) (s₂ := univ) rfl hpt, ← mul_sum, mul_div_assoc]

/-- Identification with `massPowerMoment` at `j = 1`. Remaining:
`T ≤ S ≤ y`. -/
theorem crtNestFM_meanCard_eq_theta_massPower
    (S y T : ℕ) (hTS : T ≤ S) (hSy : S ≤ y) :
    ∑ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U =
      lateRetention S y *
        massPowerMoment (univ : Finset (ResidueChoice S))
          (fun _ => (1 : ℝ) / (Fintype.card (ResidueChoice S) : ℝ))
          (fun σ => ((lateCandidateSet S T σ).card : ℝ)) 1 := by
  rw [crtNestFM_meanCard_eq_theta_avg S y T hTS hSy]
  congr 1
  unfold massPowerMoment
  have hpt :
      ∀ σ ∈ (univ : Finset (ResidueChoice S)),
        ((1 : ℝ) / (Fintype.card (ResidueChoice S) : ℝ)) *
            (((lateCandidateSet S T σ).card : ℝ) ^ (1 : ℕ)) =
          ((lateCandidateSet S T σ).card : ℝ) /
            (Fintype.card (ResidueChoice S) : ℝ) := by
    intro σ _
    rw [pow_one, mul_comm, mul_one_div]
  rw [sum_congr (s₁ := univ) (s₂ := univ) rfl hpt, sum_div]

/-- Split `S = y`: `M₁` is the average late-candidate cardinality.
Remaining: `T ≤ y`. Unique name: not `crtNestL1_meanCard`. -/
theorem crtNestFM_meanCard (y T : ℕ) (hT : T ≤ y) :
    ∑ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U =
      (∑ σ ∈ (univ : Finset (ResidueChoice y)),
          ((lateCandidateSet y T σ).card : ℝ)) /
        (Fintype.card (ResidueChoice y) : ℝ) := by
  rw [crtNestFM_meanCard_eq_theta_avg y y T hT le_rfl,
    crtNestFM_lateRetention_self, one_mul]

/-! ### Crude bounds (no exception arithmetic) -/

private theorem crtNestFM_offsetWindow_card (T : ℕ) :
    (offsetWindow T).card = T := by
  rw [offsetWindow, Nat.card_Icc, Nat.add_sub_cancel]

/-- `M₁ ≤ T` because every configuration sits in `[1, T]`. -/
theorem crtNestFM_meanCard_le_T (y T : ℕ) :
    ∑ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U ≤ T := by
  have hnn : ∀ U ∈ (offsetWindow T).powerset,
      0 ≤ actualRootLaw y T U := fun U _ =>
    crtNestFM_actualRootLaw_nonneg y T U
  have hsum := crtNestFM_actualRootLaw_sum y T
  have hcard : ∀ U ∈ (offsetWindow T).powerset, (U.card : ℝ) ≤ T := by
    intro U hU
    have hle : U.card ≤ (offsetWindow T).card :=
      card_le_card (mem_powerset.mp hU)
    exact Nat.cast_le.mpr (hle.trans_eq (crtNestFM_offsetWindow_card T))
  have hle :
      ∑ U ∈ (offsetWindow T).powerset,
          (U.card : ℝ) * actualRootLaw y T U ≤
        ∑ U ∈ (offsetWindow T).powerset,
          (T : ℝ) * actualRootLaw y T U :=
    sum_le_sum fun U hU =>
      mul_le_mul_of_nonneg_right (hcard U hU) (hnn U hU)
  have hrhs :
      ∑ U ∈ (offsetWindow T).powerset,
          (T : ℝ) * actualRootLaw y T U = T := by
    rw [← mul_sum, hsum, mul_one]
  exact hle.trans_eq hrhs

/-- `M₁ = E[|A| θ] ≤ E |A|`. Remaining: `T ≤ S ≤ y`. -/
theorem crtNestFM_meanCard_le_avgCard
    (S y T : ℕ) (hTS : T ≤ S) (hSy : S ≤ y) :
    ∑ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U ≤
      (∑ σ ∈ (univ : Finset (ResidueChoice S)),
          ((lateCandidateSet S T σ).card : ℝ)) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  rw [crtNestFM_meanCard_eq_theta_avg S y T hTS hSy]
  have hθle := crtNestFM_lateRetention_le_one S y
  have havg :
      0 ≤
        (∑ σ ∈ (univ : Finset (ResidueChoice S)),
            ((lateCandidateSet S T σ).card : ℝ)) /
          (Fintype.card (ResidueChoice S) : ℝ) :=
    div_nonneg (sum_nonneg fun _σ _ => Nat.cast_nonneg _)
      (le_of_lt (Nat.cast_pos.mpr (crtNestFM_residueChoice_card_pos S)))
  have : lateRetention S y *
        ((∑ σ ∈ (univ : Finset (ResidueChoice S)),
            ((lateCandidateSet S T σ).card : ℝ)) /
          (Fintype.card (ResidueChoice S) : ℝ)) ≤
      (1 : ℝ) *
        ((∑ σ ∈ (univ : Finset (ResidueChoice S)),
            ((lateCandidateSet S T σ).card : ℝ)) /
          (Fintype.card (ResidueChoice S) : ℝ)) :=
    mul_le_mul_of_nonneg_right hθle havg
  rwa [one_mul] at this

/-! ### Bernoulli first-moment comparison (not a replacement of `μ`) -/

/-- On a fixed fibre, independent Bernoulli thinning with retention
`θ` has the same first moment as `lateRootLaw`. This instantiates
`bernoulliThin_choose_moment` at `j = 1`; it does **not** replace
`actualRootLaw` by a Bernoulli mixture. Remaining: `T ≤ S` and
`θ ∈ [0, 1]` (the latter is `crtNestFM_lateRetention_*`). -/
theorem crtNestFM_bernoulli_eq_late_first_moment
    (S y : ℕ) {T : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 T) (hT : T ≤ S) :
    ∑ E ∈ A.powerset, (E.card : ℝ) * lateRootLaw S y A E =
      ∑ B ∈ A.powerset,
        (B.card : ℝ) *
          bernoulliThin A (lateRetention S y)
            (crtNestFM_lateRetention_nonneg S y)
            (crtNestFM_lateRetention_le_one S y) B := by
  rw [crtNestFM_fibre_first_moment S y hA hT]
  have hθ0 := crtNestFM_lateRetention_nonneg S y
  have hθ1 := crtNestFM_lateRetention_le_one S y
  have hB := bernoulliThin_choose_moment A hθ0 hθ1 1
  have hL :
      ∑ B ∈ A.powerset,
          bernoulliThin A (lateRetention S y) hθ0 hθ1 B *
            (Nat.choose B.card 1 : ℝ) =
        ∑ B ∈ A.powerset,
          (B.card : ℝ) *
            bernoulliThin A (lateRetention S y) hθ0 hθ1 B := by
    refine sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl fun B _ => ?_
    rw [Nat.choose_one_right, mul_comm]
  have hR :
      (lateRetention S y) ^ 1 * (Nat.choose A.card 1 : ℝ) =
        (A.card : ℝ) * lateRetention S y := by
    rw [pow_one, Nat.choose_one_right, mul_comm]
  rw [← hL, hB, hR]

/-! ### Factorial moment at `j = 1` is the first moment -/

theorem crtNestFM_factorialMoment_one (A : Finset ℕ) (μ : Finset ℕ → ℝ) :
    factorialMoment A μ 1 = ∑ E ∈ A.powerset, (E.card : ℝ) * μ E := by
  unfold factorialMoment
  refine sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl fun E _ => ?_
  rw [Nat.choose_one_right]

private theorem crtNestFM_cast_factorial_one : (Nat.factorial 1 : ℝ) = 1 := by
  simp [Nat.factorial]

private theorem crtNestFM_twelve_pow_one (L : ℝ) :
    (12 * L) ^ (1 : ℕ) / (Nat.factorial 1 : ℝ) = 12 * L := by
  rw [pow_one, crtNestFM_cast_factorial_one, div_one]

/-! ### `M₁ ≤ 12 L` from the model first-moment hull at `j = 1` -/

/-- v0.8 first-moment band on `actualRootLaw`, by instantiating
`factorialMoment_le_twelve` at `j = 1` on the uniform residue law of
the split. Remaining: complementary mass of `{θ N > 6 L}`, the crude
bound `θ N ≤ C₁ L log S̄`, and `ε (C₁ log S̄ / 6) ≤ 1`. Does **not**
discharge the exception event, and does not claim (C4). -/
theorem crtNestFM_meanCard_le_twelve
    (S y T : ℕ) (hTS : T ≤ S) (hSy : S ≤ y)
    (g : Finset (ResidueChoice S)) {ε C1 logS : ℝ} (L : ℕ)
    (hε : 0 ≤ ε) (hC1 : 0 ≤ C1) (hlog : 0 ≤ logS)
    (hg : g ⊆ (univ : Finset (ResidueChoice S)))
    (hbad :
      ∑ σ ∈ (univ : Finset (ResidueChoice S)) \ g,
          (1 : ℝ) / (Fintype.card (ResidueChoice S) : ℝ) ≤ ε)
    (hgood : ∀ σ ∈ g,
        lateRetention S y * ((lateCandidateSet S T σ).card : ℝ) ≤
          6 * (L : ℝ))
    (hall : ∀ σ ∈ (univ : Finset (ResidueChoice S)),
        lateRetention S y * ((lateCandidateSet S T σ).card : ℝ) ≤
          C1 * (L : ℝ) * logS)
    (hsmall : ε * (C1 * logS / 6) ≤ 1) :
    ∑ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U ≤ 12 * (L : ℝ) := by
  classical
  set μ : ResidueChoice S → ℝ :=
    fun _ => (1 : ℝ) / (Fintype.card (ResidueChoice S) : ℝ)
  set Nfun : ResidueChoice S → ℝ :=
    fun σ => (lateCandidateSet S T σ).card
  set θ := lateRetention S y
  set Q :=
    ∑ U ∈ (offsetWindow T).powerset,
      (U.card : ℝ) * actualRootLaw y T U
  have hθ : 0 ≤ θ := crtNestFM_lateRetention_nonneg S y
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hμ : ∀ σ ∈ (univ : Finset (ResidueChoice S)), 0 ≤ μ σ := fun _ _ =>
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hN : ∀ σ ∈ (univ : Finset (ResidueChoice S)), 0 ≤ Nfun σ :=
    fun _ _ => Nat.cast_nonneg _
  have hμ1 : ∑ σ ∈ (univ : Finset (ResidueChoice S)), μ σ ≤ 1 :=
    (crtNestFM_resUnif_sum S).le
  have hQ :
      Q ≤ θ ^ (1 : ℕ) *
          massPowerMoment (univ : Finset (ResidueChoice S)) μ Nfun 1 /
            (Nat.factorial 1 : ℝ) := by
    have hid := crtNestFM_meanCard_eq_theta_massPower S y T hTS hSy
    rw [pow_one, crtNestFM_cast_factorial_one, div_one]
    exact hid.le
  have hj : 1 ≤ (1 : ℕ) := le_rfl
  have hsmall' : ε * (C1 * logS / 6) ^ (1 : ℕ) ≤ 1 := by rwa [pow_one]
  have h12 :=
    factorialMoment_le_twelve
      (univ : Finset (ResidueChoice S)) g μ Nfun (θ := θ) (ε := ε)
      (L := (L : ℝ)) (C1 := C1) (logS := logS) (Q := Q) 1
      hθ hε hL hC1 hlog hμ hN hμ1 hg hbad hgood hall hQ hj hsmall'
  have hrhs := crtNestFM_twelve_pow_one (L : ℝ)
  exact h12.trans_eq hrhs

/-- `ModelMomentHull` at `j = 1` for the mixed window law, from the
residue-space first-moment band. Same remaining hyps as
`crtNestFM_meanCard_le_twelve`. -/
theorem crtNestFM_modelMomentHull_one
    (S y T : ℕ) (hTS : T ≤ S) (hSy : S ≤ y)
    (g : Finset (ResidueChoice S)) {ε C1 logS : ℝ} (L a : ℕ)
    (hε : 0 ≤ ε) (hC1 : 0 ≤ C1) (hlog : 0 ≤ logS)
    (hg : g ⊆ (univ : Finset (ResidueChoice S)))
    (hbad :
      ∑ σ ∈ (univ : Finset (ResidueChoice S)) \ g,
          (1 : ℝ) / (Fintype.card (ResidueChoice S) : ℝ) ≤ ε)
    (hgood : ∀ σ ∈ g,
        lateRetention S y * ((lateCandidateSet S T σ).card : ℝ) ≤
          6 * (L : ℝ))
    (hall : ∀ σ ∈ (univ : Finset (ResidueChoice S)),
        lateRetention S y * ((lateCandidateSet S T σ).card : ℝ) ≤
          C1 * (L : ℝ) * logS)
    (hsmall : ε * (C1 * logS / 6) ≤ 1) :
    ModelMomentHull (offsetWindow T) (actualRootLaw y T) L a 1 := by
  intro _hj
  have hM :=
    crtNestFM_meanCard_le_twelve S y T hTS hSy g (ε := ε) (C1 := C1)
      (logS := logS) L hε hC1 hlog hg hbad hgood hall hsmall
  rw [crtNestFM_factorialMoment_one, crtNestFM_twelve_pow_one]
  exact hM

/-- Direct `j = 1` wrapper of
`factorialMoment_le_twelve_of_six_exception`. Remaining: the combined
`6 L + ε C₁ L log S̄` bound on the factorial moment, and the smallness
`ε (C₁ log S̄ / 6) ≤ 1`. -/
theorem crtNestFM_hull_one_of_six_exception
    {A : Finset ℕ} {μ : Finset ℕ → ℝ} {L a : ℕ} {ε C1 logS : ℝ}
    (hε : 0 ≤ ε) (hC1 : 0 ≤ C1) (hlog : 0 ≤ logS)
    (hsmall : ε * (C1 * logS / 6) ≤ 1)
    (hval : factorialMoment A μ 1 ≤
      6 * (L : ℝ) + ε * (C1 * (L : ℝ) * logS)) :
    ModelMomentHull A μ L a 1 := by
  refine factorialMoment_le_twelve_of_six_exception (A := A) (μ := μ)
      (L := L) (a := a) (j := 1) (ε := ε) (C1 := C1) (logS := logS)
      (Nat.cast_nonneg _) hε hC1 hlog le_rfl ?hsmall' ?hval'
  · rwa [pow_one]
  · have hrhs :
        ((6 * (L : ℝ)) ^ (1 : ℕ) +
            ε * (C1 * (L : ℝ) * logS) ^ (1 : ℕ)) /
          (Nat.factorial 1 : ℝ) =
        6 * (L : ℝ) + ε * (C1 * (L : ℝ) * logS) := by
      rw [pow_one, pow_one, crtNestFM_cast_factorial_one, div_one]
    exact hval.trans_eq hrhs.symm

/-! ### Physical specialisation (remaining `profileS ≤ sieveCutoff`) -/

/-- Identity (1) at `y = sieveCutoff X`, `T = profileS κ X`.
Remaining: `profileS ≤ sieveCutoff`. Does not claim `12 L`. -/
theorem crtNestFM_meanCard_profile (κ : ℝ) (X : ℕ)
    (hT : profileS κ X ≤ sieveCutoff (X : ℝ)) :
    ∑ U ∈ (offsetWindow (profileS κ X)).powerset,
        (U.card : ℝ) *
          actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X) U =
      (∑ σ ∈ (univ : Finset (ResidueChoice (sieveCutoff (X : ℝ)))),
          ((lateCandidateSet (sieveCutoff (X : ℝ)) (profileS κ X) σ).card :
            ℝ)) /
        (Fintype.card (ResidueChoice (sieveCutoff (X : ℝ))) : ℝ) :=
  crtNestFM_meanCard (sieveCutoff (X : ℝ)) (profileS κ X) hT

/-- Model first-moment band at the physical pair, with the presieve
split `S = profileS`. Remaining: `profileS ≤ sieveCutoff` and the
same exception / `6 L` / `C₁ log S̄` hyps. Does not claim (C4). -/
theorem crtNestFM_meanCard_le_twelve_profile (κ : ℝ) (X : ℕ)
    (hT : profileS κ X ≤ sieveCutoff (X : ℝ))
    (g : Finset (ResidueChoice (profileS κ X))) {ε C1 logS : ℝ}
    (hε : 0 ≤ ε) (hC1 : 0 ≤ C1) (hlog : 0 ≤ logS)
    (hg : g ⊆ (univ : Finset (ResidueChoice (profileS κ X))))
    (hbad :
      ∑ σ ∈ (univ : Finset (ResidueChoice (profileS κ X))) \ g,
          (1 : ℝ) /
            (Fintype.card (ResidueChoice (profileS κ X)) : ℝ) ≤ ε)
    (hgood : ∀ σ ∈ g,
        lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) *
            ((lateCandidateSet (profileS κ X) (profileS κ X) σ).card : ℝ) ≤
          6 * (profileL κ X : ℝ))
    (hall : ∀ σ ∈ (univ : Finset (ResidueChoice (profileS κ X))),
        lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) *
            ((lateCandidateSet (profileS κ X) (profileS κ X) σ).card : ℝ) ≤
          C1 * (profileL κ X : ℝ) * logS)
    (hsmall : ε * (C1 * logS / 6) ≤ 1) :
    ∑ U ∈ (offsetWindow (profileS κ X)).powerset,
        (U.card : ℝ) *
          actualRootLaw (sieveCutoff (X : ℝ)) (profileS κ X) U ≤
      12 * (profileL κ X : ℝ) :=
  crtNestFM_meanCard_le_twelve (profileS κ X) (sieveCutoff (X : ℝ))
    (profileS κ X) le_rfl hT g (ε := ε) (C1 := C1) (logS := logS)
    (profileL κ X) hε hC1 hlog hg hbad hgood hall hsmall

end

end PrimeGapNormality.Prime
