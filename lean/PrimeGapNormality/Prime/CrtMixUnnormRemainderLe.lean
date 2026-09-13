import PrimeGapNormality.Prime.CrtMixUnnormParityClosed
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Mix-Unnorm Stopped remainders: identify and bound, do not vanish

R115/09 M1 after lake-green Mix-Unnorm Stopped. The comparison still
carries `Stopped.failureMass` / `Stopped.modelRemainder` of
`finiteRootMixUnnorm` and `Stopped.adverseBudget`. This leaf records
the mix-side terms as V-weighted averages of `actualRootLaw` Stopped
objects and gives **finite** bounds in already-named quantities.

`failureMass(ν̃)` is at most the unnormalized total mass `mixZeta`,
hence `≤ 1 + |1 − ζ|`. `modelRemainder(ν̃)` is the Bonferroni
envelope times `countMoment(ν̃, r+1)` (`Stopped.modelRemainder_le`).
`adverseBudget` is nonnegative and at most a triangle of count
moments; vanishing that budget is AHL and is **not** claimed.

Does **not** import MixZeta, SingletonLi, ExactRootWindowClose,
RootedCutoffTypicalOsc, WeylOf*, CrtHLMismatchVanishing,
CrtMixtureTransfer, CrtFailureMassLimit, or CrtNestedCutoffL1/Theta/VRatio.

Does **not** claim `MixZetaTendstoOne`, AHL, kernel closed, (C4),
or `HLMismatchVanishes`. Unique names `crtMixUnnormRem_*`.

**Compiled.**
1. Weighted V-average: mix unnorm versus `actualRootLaw` fibres.
2. Mix `failureMass` = V-average of fibre `failureMass` / `N_X`.
3. Mix `failureMass ≤ mixZeta ≤ 1 + |1 − mixZeta|`.
4. Mix `countMoment` / `modelRemainder` are the same averages.
5. `modelRemainder ≤ C(r, L−1) · countMoment(r+1)` (`L ≤ r` from
   `crtMixProf_le_at`).
6. `adverseBudget ≥ 0` and `≤` triangle of count moments (not AHL).
7. Stopped L¹ with mix failure/remainder replaced by those bounds;
   `adverseBudget` remains.

**Not compiled.** Mix `failureMass` / `modelRemainder` / mix
`countMoment(r+1)` vanish. `MixZetaTendstoOne`. AHL.
`HLMismatchVanishes` at Dirac CRT. Kernel close. (C4).

**Remaining.** Vanishing of mix `failureMass` / `modelRemainder` /
`countMoment(r+1)`; `adverseBudget` / AHL; `MixZetaTendstoOne`
(not claimed). Pointwise `1 ≤ profileL` and `0 < windowNX` on the
consumed comparison. Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| mix unnorm is a V-average of `actualRootLaw` | theorem (`crtMixUnnormRem_weighted_eq`) |
| mix `failureMass` = V-average of fibre failure / `N_X` | theorem |
| mix `failureMass ≤ mixZeta` | theorem |
| mix `failureMass ≤ 1 + \|1−ζ\|` | theorem |
| mix `modelRemainder` = V-average of fibre remainder / `N_X` | theorem |
| mix `modelRemainder ≤ C(r,L−1) countMoment(r+1)` | theorem |
| `adverseBudget ≥ 0` | theorem |
| `adverseBudget ≤` triangle of count moments | theorem (not AHL) |
| Stopped L¹ with finite mix fail/rem bounds | theorem |
| mix fail/rem/`countMoment(r+1)` vanish | remaining |
| `adverseBudget` / AHL | remaining |
| `MixZetaTendstoOne` | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `CrtMixUnnormStopped.crtMixUnnorm_stoppedShapeL1_le`;
`CrtMixUnnormParityClosed.crtMixUnnormClosed_stoppedShapeL1_le`;
`Stopped.failureMass`, `Stopped.modelRemainder`, `Stopped.modelRemainder_le`,
`Stopped.adverseBudget`; `ExactRootMix.finiteRootMixUnnorm`;
`rounds/round115/09_grok_mixture_gate_and_cutoff_bridge.md` M1.
Contract: API
Audit: GREEN
-/

open Finset Filter

namespace PrimeGapNormality.Prime

/-! ### Unnormalized mix as a V-weighted fibre average -/

/-- Pulling a test function through `finiteRootMixUnnorm` yields the
V-weighted average of the same pairing against `actualRootLaw`,
divided by `N_X`. Algebraic; does not need `0 < windowNX`. -/
theorem crtMixUnnormRem_weighted_eq (X S : ℕ) (f : Finset ℕ → ℝ) :
    ∑ U ∈ (offsetWindow S).powerset, finiteRootMixUnnorm X S U * f U =
      (∑ t ∈ mixScale X, mixWeightV t *
          ∑ U ∈ (offsetWindow S).powerset,
            actualRootLaw (sieveCutoff (t : ℝ)) S U * f U) /
        (windowNX X : ℝ) := by
  unfold finiteRootMixUnnorm
  have hpt : ∀ U,
      ((∑ t ∈ mixScale X, mixWeightV t *
          actualRootLaw (sieveCutoff (t : ℝ)) S U) / (windowNX X : ℝ)) *
        f U =
      (∑ t ∈ mixScale X, mixWeightV t *
          (actualRootLaw (sieveCutoff (t : ℝ)) S U * f U)) /
        (windowNX X : ℝ) := by
    intro U
    rw [div_mul_eq_mul_div]
    refine congrArg (fun z => z / (windowNX X : ℝ)) ?_
    rw [sum_mul]
    exact sum_congr rfl fun t _ => mul_assoc _ _ _
  rw [sum_congr rfl fun U _ => hpt U]
  rw [← sum_div]
  refine congrArg (fun z => z / (windowNX X : ℝ)) ?_
  rw [sum_comm]
  exact sum_congr rfl fun t _ => (mul_sum _ _ _).symm

/-! ### `mixZeta` scalar, not `MixZetaTendstoOne` -/

theorem crtMixUnnormRem_mixZeta_nonneg (X : ℕ) : 0 ≤ mixZeta X :=
  div_nonneg (mixZ_nonneg X) (Nat.cast_nonneg _)

/-- Finite identity `ζ = 1 + (ζ − 1) ≤ 1 + |1 − ζ|`. Does **not**
claim `ζ → 1`. -/
theorem crtMixUnnormRem_mixZeta_le_one_add_abs (X : ℕ) :
    mixZeta X ≤ (1 : ℝ) + |1 - mixZeta X| := by
  have hsub : mixZeta X - (1 : ℝ) ≤ |mixZeta X - (1 : ℝ)| :=
    le_abs_self _
  have hid : mixZeta X = (1 : ℝ) + (mixZeta X - (1 : ℝ)) := by ring
  have habs : |mixZeta X - (1 : ℝ)| = |(1 : ℝ) - mixZeta X| :=
    abs_sub_comm (mixZeta X) (1 : ℝ)
  calc mixZeta X
      = (1 : ℝ) + (mixZeta X - (1 : ℝ)) := hid
    _ ≤ (1 : ℝ) + |mixZeta X - (1 : ℝ)| :=
      add_le_add (le_refl (1 : ℝ)) hsub
    _ = (1 : ℝ) + |(1 : ℝ) - mixZeta X| := by rw [habs]

/-! ### Mix `failureMass` -/

theorem crtMixUnnormRem_failureMass_eq_indicator
    (Ω : Finset ℕ) (μ : Finset ℕ → ℝ) (L : ℕ) :
    Stopped.failureMass Ω μ L =
      ∑ U ∈ Ω.powerset, μ U * (if U.card < L then (1 : ℝ) else 0) := by
  unfold Stopped.failureMass
  rw [Finset.sum_filter]
  refine sum_congr rfl fun U _ => ?_
  split_ifs with h <;> simp only [mul_one, mul_zero]

/-- Mix failure mass is the V-average of fibre failure masses,
divided by `N_X`. Not a vanishing statement. -/
theorem crtMixUnnormRem_failureMass_eq (X S L : ℕ) :
    Stopped.failureMass (offsetWindow S) (finiteRootMixUnnorm X S) L =
      (∑ t ∈ mixScale X, mixWeightV t *
          Stopped.failureMass (offsetWindow S)
            (actualRootLaw (sieveCutoff (t : ℝ)) S) L) /
        (windowNX X : ℝ) := by
  rw [crtMixUnnormRem_failureMass_eq_indicator,
    crtMixUnnormRem_weighted_eq]
  refine congrArg (fun z => z / (windowNX X : ℝ)) ?_
  refine sum_congr rfl fun t _ => ?_
  rw [← crtMixUnnormRem_failureMass_eq_indicator]

theorem crtMixUnnormRem_failureMass_nonneg (X S L : ℕ) :
    0 ≤ Stopped.failureMass (offsetWindow S) (finiteRootMixUnnorm X S) L :=
  sum_nonneg fun U _hU =>
    crtMixUnnorm_finiteRootMixUnnorm_nonneg X S U

/-- Fibre `actualRootLaw` is a probability, so its failure mass is
at most 1. -/
theorem crtMixUnnormRem_actualRootLaw_failureMass_le_one
    (y S L : ℕ) :
    Stopped.failureMass (offsetWindow S) (actualRootLaw y S) L ≤ 1 := by
  unfold Stopped.failureMass
  exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun U hU _ => crtMixUnnorm_actualRootLaw_nonneg y S U).trans_eq
    (crtMixUnnorm_actualRootLaw_sum y S)

/-- Nonnegative mix masses: failure mass is at most the total
`∑ ν̃ = mixZeta`. -/
theorem crtMixUnnormRem_failureMass_le_mixZeta (X S L : ℕ) :
    Stopped.failureMass (offsetWindow S) (finiteRootMixUnnorm X S) L ≤
      mixZeta X := by
  have hnn : ∀ U ∈ (offsetWindow S).powerset,
      0 ≤ finiteRootMixUnnorm X S U :=
    fun U _ => crtMixUnnorm_finiteRootMixUnnorm_nonneg X S U
  have hsum :
      ∑ U ∈ (offsetWindow S).powerset, finiteRootMixUnnorm X S U =
        mixZeta X := by
    unfold finiteRootMixUnnorm mixZeta
    rw [← sum_div, crtMixUnnorm_sum_num]
  unfold Stopped.failureMass
  exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun U hU _ => hnn U hU).trans_eq hsum

/-- Finite mix-side bound. Vanishing of this mass remains. -/
theorem crtMixUnnormRem_failureMass_le_one_add_abs (X S L : ℕ) :
    Stopped.failureMass (offsetWindow S) (finiteRootMixUnnorm X S) L ≤
      1 + |1 - mixZeta X| :=
  (crtMixUnnormRem_failureMass_le_mixZeta X S L).trans
    (crtMixUnnormRem_mixZeta_le_one_add_abs X)

/-! ### Mix `countMoment` and `modelRemainder` -/

theorem crtMixUnnormRem_countEnvelope_nonneg (L r N : ℕ) :
    0 ≤ Stopped.countEnvelope L r N :=
  sum_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem crtMixUnnormRem_countEnvelope_eq_zero_of_le
    (L r N : ℕ) (hN : N ≤ r) :
    Stopped.countEnvelope L r N = 0 := by
  unfold Stopped.countEnvelope
  have hempty : Icc (r + 1) N = ∅ :=
    Icc_eq_empty_iff.mpr (not_le.mpr (Nat.lt_succ_of_le hN))
  rw [hempty, sum_empty]

/-- Remainder is supported on `{|U| > r}`. Identifies the mix
Bonferroni term; does not send it to 0. -/
theorem crtMixUnnormRem_modelRemainder_eq_highCard
    (Ω : Finset ℕ) (ν : Finset ℕ → ℝ) (L r : ℕ) :
    Stopped.modelRemainder Ω ν L r =
      ∑ U ∈ Ω.powerset.filter (fun U => r < U.card),
        ν U * Stopped.countEnvelope L r U.card := by
  unfold Stopped.modelRemainder
  refine (sum_subset (filter_subset _ _) ?_).symm
  intro U hU hnot
  have hle : U.card ≤ r :=
    not_lt.mp fun hlt => hnot (mem_filter.mpr ⟨hU, hlt⟩)
  rw [crtMixUnnormRem_countEnvelope_eq_zero_of_le L r U.card hle, mul_zero]

theorem crtMixUnnormRem_countMoment_eq (X S j : ℕ) :
    Stopped.countMoment (offsetWindow S) (finiteRootMixUnnorm X S) j =
      (∑ t ∈ mixScale X, mixWeightV t *
          Stopped.countMoment (offsetWindow S)
            (actualRootLaw (sieveCutoff (t : ℝ)) S) j) /
        (windowNX X : ℝ) := by
  unfold Stopped.countMoment
  exact crtMixUnnormRem_weighted_eq X S fun U => (U.card.choose j : ℝ)

theorem crtMixUnnormRem_countMoment_nonneg (X S j : ℕ) :
    0 ≤ Stopped.countMoment (offsetWindow S) (finiteRootMixUnnorm X S) j :=
  sum_nonneg fun U _ =>
    mul_nonneg (crtMixUnnorm_finiteRootMixUnnorm_nonneg X S U)
      (Nat.cast_nonneg _)

theorem crtMixUnnormRem_modelRemainder_eq (X S L r : ℕ) :
    Stopped.modelRemainder (offsetWindow S) (finiteRootMixUnnorm X S) L r =
      (∑ t ∈ mixScale X, mixWeightV t *
          Stopped.modelRemainder (offsetWindow S)
            (actualRootLaw (sieveCutoff (t : ℝ)) S) L r) /
        (windowNX X : ℝ) := by
  unfold Stopped.modelRemainder
  exact crtMixUnnormRem_weighted_eq X S fun U =>
    Stopped.countEnvelope L r U.card

theorem crtMixUnnormRem_modelRemainder_nonneg (X S L r : ℕ) :
    0 ≤ Stopped.modelRemainder (offsetWindow S)
        (finiteRootMixUnnorm X S) L r :=
  sum_nonneg fun U _ =>
    mul_nonneg (crtMixUnnorm_finiteRootMixUnnorm_nonneg X S U)
      (crtMixUnnormRem_countEnvelope_nonneg L r U.card)

/-- Bonferroni envelope bound at the mix, with public `L ≤ r`.
Remaining: vanishing of mix `countMoment(r+1)`. -/
theorem crtMixUnnormRem_modelRemainder_le
    {κ d0 : ℝ} {X : ℕ} (hL : 1 ≤ profileL κ X) :
    Stopped.modelRemainder (windowOmega κ X)
        (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
        (profileR (profileL κ X) d0) ≤
      ((profileR (profileL κ X) d0).choose (profileL κ X - 1) : ℝ) *
        Stopped.countMoment (windowOmega κ X)
          (finiteRootMixUnnorm X (profileS κ X))
          (profileR (profileL κ X) d0 + 1) :=
  Stopped.modelRemainder_le hL (crtMixProf_le_at κ d0 X)
    fun U _ => crtMixUnnorm_finiteRootMixUnnorm_nonneg X _ U

/-! ### `adverseBudget`: named, nonnegative, triangle-bounded; not AHL -/

theorem crtMixUnnormRem_inclusionMass_nonneg
    (Ω : Finset ℕ) (μ : Finset ℕ → ℝ) (H : Finset ℕ)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U) :
    0 ≤ Stopped.inclusionMass Ω μ H :=
  sum_nonneg fun U hU => hμ U (mem_filter.mp hU).1

theorem crtMixUnnormRem_adverseBudget_nonneg
    (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) (L r : ℕ) :
    0 ≤ Stopped.adverseBudget Ω μ ν L r := by
  unfold Stopped.adverseBudget Stopped.adverseLayer
  refine sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) ?_
  exact sum_nonneg fun H _ => le_max_right _ _

/-- Pos-part layer `≤` the two count moments. Triangle inequality,
not a relative AHL layer bound. -/
theorem crtMixUnnormRem_adverseLayer_le_countMoments
    (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) (L j : ℕ)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U) :
    Stopped.adverseLayer Ω μ ν L j ≤
      Stopped.countMoment Ω μ j + Stopped.countMoment Ω ν j := by
  unfold Stopped.adverseLayer
  have hpt : ∀ H ∈ Ω.powerset.filter (fun H => H.card = j),
      max (((-1 : ℝ) ^ (j - L + 1)) *
          (Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H)) 0 ≤
        Stopped.inclusionMass Ω μ H + Stopped.inclusionMass Ω ν H := by
    intro H _hH
    have hμH : 0 ≤ Stopped.inclusionMass Ω μ H :=
      crtMixUnnormRem_inclusionMass_nonneg Ω μ H hμ
    have hνH : 0 ≤ Stopped.inclusionMass Ω ν H :=
      crtMixUnnormRem_inclusionMass_nonneg Ω ν H hν
    have hx :
        max (((-1 : ℝ) ^ (j - L + 1)) *
            (Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H)) 0 ≤
          |((-1 : ℝ) ^ (j - L + 1)) *
            (Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H)| :=
      max_le (le_abs_self _) (abs_nonneg _)
    have hsign :
        |((-1 : ℝ) ^ (j - L + 1)) *
            (Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H)| =
          |Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have htri0 :
        |Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H| ≤
          |Stopped.inclusionMass Ω μ H| + |Stopped.inclusionMass Ω ν H| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    have htri :
        |Stopped.inclusionMass Ω μ H - Stopped.inclusionMass Ω ν H| ≤
          Stopped.inclusionMass Ω μ H + Stopped.inclusionMass Ω ν H := by
      rw [abs_of_nonneg hμH, abs_of_nonneg hνH] at htri0
      exact htri0
    exact hx.trans (hsign.trans_le htri)
  have hsum := sum_le_sum hpt
  have hadd :
      ∑ H ∈ Ω.powerset.filter (fun H => H.card = j),
          (Stopped.inclusionMass Ω μ H + Stopped.inclusionMass Ω ν H) =
        Stopped.countMoment Ω μ j + Stopped.countMoment Ω ν j := by
    rw [sum_add_distrib, countMoment_eq_sum_inclusionMass Ω μ j,
      countMoment_eq_sum_inclusionMass Ω ν j]
  exact hsum.trans_eq hadd

/-- Finite triangle bound on the mix/actual adverse budget.
Does **not** claim AHL or a relative `ε · countMoment` layer. -/
theorem crtMixUnnormRem_adverseBudget_le_countMoments
    {κ d0 : ℝ} {X : ℕ} :
    Stopped.adverseBudget (windowOmega κ X) (actualConfigMass κ X)
        (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
        (profileR (profileL κ X) d0) ≤
      ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d0),
        ((j - 1).choose (profileL κ X - 1) : ℝ) *
          (Stopped.countMoment (windowOmega κ X) (actualConfigMass κ X) j +
            Stopped.countMoment (windowOmega κ X)
              (finiteRootMixUnnorm X (profileS κ X)) j) := by
  unfold Stopped.adverseBudget
  refine sum_le_sum fun j _hj => ?_
  have hnn : (0 : ℝ) ≤ ((j - 1).choose (profileL κ X - 1) : ℝ) :=
    Nat.cast_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hnn
  exact crtMixUnnormRem_adverseLayer_le_countMoments
    (windowOmega κ X) (actualConfigMass κ X)
    (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) j
    (fun U _ => actualConfigMass_nonneg κ X U)
    (fun U _ => crtMixUnnorm_finiteRootMixUnnorm_nonneg X _ U)

/-! ### Consumed Stopped comparison with finite mix fail/rem bounds -/

/-- Mix-Unnorm Stopped L¹ after replacing mix `failureMass` by
`1 + |1−ζ|` and mix `modelRemainder` by the Bonferroni count moment.
`adverseBudget` is kept (AHL remaining). Does **not** claim those
mix terms vanish, nor `MixZetaTendstoOne`, nor kernel close. -/
theorem crtMixUnnormRem_stoppedShapeL1_le
    {κ d0 : ℝ} {X : ℕ}
    (hL : 1 ≤ profileL κ X)
    (hN : 0 < windowNX X) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X)
        (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) +
      Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
        (profileL κ X) ≤
      1 + 2 * |1 - mixZeta X| +
        2 * (((profileR (profileL κ X) d0).choose (profileL κ X - 1) : ℝ) *
          Stopped.countMoment (windowOmega κ X)
            (finiteRootMixUnnorm X (profileS κ X))
            (profileR (profileL κ X) d0 + 1)) +
        2 * Stopped.adverseBudget (windowOmega κ X)
          (actualConfigMass κ X)
          (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
          (profileR (profileL κ X) d0) := by
  have hmain :=
    crtMixUnnormClosed_stoppedShapeL1_le (κ := κ) (d0 := d0) hL hN
  have hfail :
      Stopped.failureMass (windowOmega κ X)
          (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) ≤
        1 + |1 - mixZeta X| :=
    crtMixUnnormRem_failureMass_le_one_add_abs X (profileS κ X)
      (profileL κ X)
  have hrem := crtMixUnnormRem_modelRemainder_le (κ := κ) (d0 := d0) hL
  have hstep :
      Stopped.failureMass (windowOmega κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) +
          2 * Stopped.modelRemainder (windowOmega κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) +
          2 * Stopped.adverseBudget (windowOmega κ X)
            (actualConfigMass κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) +
          |1 - mixZeta X| ≤
        1 + |1 - mixZeta X| +
          2 * Stopped.modelRemainder (windowOmega κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) +
          2 * Stopped.adverseBudget (windowOmega κ X)
            (actualConfigMass κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) +
          |1 - mixZeta X| :=
    add_le_add
      (add_le_add
        (add_le_add hfail
          (le_refl
            (2 *
              Stopped.modelRemainder (windowOmega κ X)
                (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
                (profileR (profileL κ X) d0))))
        (le_refl
          (2 *
            Stopped.adverseBudget (windowOmega κ X)
              (actualConfigMass κ X)
              (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
              (profileR (profileL κ X) d0))))
      (le_refl |1 - mixZeta X|)
  have hring :
      1 + |1 - mixZeta X| +
          2 * Stopped.modelRemainder (windowOmega κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) +
          2 * Stopped.adverseBudget (windowOmega κ X)
            (actualConfigMass κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) +
          |1 - mixZeta X| =
        1 + 2 * |1 - mixZeta X| +
          2 * Stopped.modelRemainder (windowOmega κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) +
          2 * Stopped.adverseBudget (windowOmega κ X)
            (actualConfigMass κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) := by
    ring
  have hbonf :
      1 + 2 * |1 - mixZeta X| +
          2 * Stopped.modelRemainder (windowOmega κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) +
          2 * Stopped.adverseBudget (windowOmega κ X)
            (actualConfigMass κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) ≤
        1 + 2 * |1 - mixZeta X| +
          2 * (((profileR (profileL κ X) d0).choose (profileL κ X - 1) : ℝ) *
            Stopped.countMoment (windowOmega κ X)
              (finiteRootMixUnnorm X (profileS κ X))
              (profileR (profileL κ X) d0 + 1)) +
          2 * Stopped.adverseBudget (windowOmega κ X)
            (actualConfigMass κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) :=
    add_le_add
      (add_le_add (le_refl (1 + 2 * |1 - mixZeta X|))
        (mul_le_mul_of_nonneg_left hrem (by norm_num : (0 : ℝ) ≤ 2)))
      (le_refl _)
  exact hmain.trans (hstep.trans (hring.trans_le hbonf))

/-- Eventual form (`0 < κ`). `1 ≤ profileL` is a theorem; remaining
binder is eventual `0 < windowNX`. Mix vanish / AHL / MixZeta are
not claimed. -/
theorem crtMixUnnormRem_eventually
    {κ d0 : ℝ} (hκ : 0 < κ)
    (hN : ∀ᶠ X : ℕ in atTop, 0 < windowNX X) :
    ∀ᶠ X : ℕ in atTop,
      Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X)
          (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
          (profileL κ X) ≤
        1 + 2 * |1 - mixZeta X| +
          2 * (((profileR (profileL κ X) d0).choose (profileL κ X - 1) : ℝ) *
            Stopped.countMoment (windowOmega κ X)
              (finiteRootMixUnnorm X (profileS κ X))
              (profileR (profileL κ X) d0 + 1)) +
          2 * Stopped.adverseBudget (windowOmega κ X)
            (actualConfigMass κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) := by
  filter_upwards [eventually_one_le_profileL hκ, hN] with X hL hNX
  exact crtMixUnnormRem_stoppedShapeL1_le (κ := κ) (d0 := d0) hL hNX

end PrimeGapNormality.Prime
