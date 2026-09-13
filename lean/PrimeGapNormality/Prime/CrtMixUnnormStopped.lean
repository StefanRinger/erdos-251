import PrimeGapNormality.Prime.ExactRootMix
import PrimeGapNormality.Prime.StoppedPrime
import PrimeGapNormality.Prime.StoppedUnequalMass
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card

/-!
# Unnormalized V-mix as Stopped input; `|Z/N−1|` paid additively

R115/09 M1. The Stopped comparison is instantiated at the
unnormalized V-weighted mix `finiteRootMixUnnorm`, not at a
Bernoulli law and not at the Dirac CRT cutoff. After the finite
unequal-mass kernel, the scalar `|ζ_X − 1| = |Z_X/N_X − 1|` enters
**additively**. It is not multiplied by `exp(C L)`.

`windowOmega κ X` is definitionally `offsetWindow (profileS κ X)`
(`EndAPI.Icc` vs `ActualRootLaw.Icc`). The fibrewise card-sum for
`actualRootLaw` is copied under unique names; this leaf imports
neither `CrtMixtureTransfer` nor `CrtFailureMassLimit` (same public
theorem names) and neither `CrtHLMismatchVanishing` nor `MixZeta`.

This does **not** close `HLMismatchVanishes` at Dirac CRT. It does
**not** close AHL. Remaining: `modelRemainder` / `failureMass` of
the mix, `adverseBudget` / AHL, and `MixZetaTendstoOne` (not
claimed; lives in `MixZeta.lean` under `MixPrimeCountingAsymp`).

Does **not** import MixZeta, SingletonLi, ExactRootWindowClose,
RootedCutoffTypicalOsc, WeylOf*, or CrtHLMismatchVanishing.

**Compiled.**
1. `actualRootLaw` nonnegative (`card/card ≥ 0`).
2. `actualRootLaw` sums to 1 on `(offsetWindow S).powerset`.
3. `finiteRootMixUnnorm` nonnegative (`mixWeightV_nonneg`,
   `windowNX ≥ 0`).
4. If `0 < windowNX X`, the unnormalized mix sums to `mixZeta X`.
5. If `mixZ X ≠ 0`, the normalized mix sums to 1.
6. Stopped unequal-mass comparison: `shapeL1 + failureMass(actual)
   ≤ failureMass(unnorm) + 2 modelRemainder(unnorm) + 2 adverseBudget
   + |1 − mixZeta X|`.

**Not compiled.** `MixZetaTendstoOne`. `HLMismatchVanishes` at
Dirac CRT. AHL. Vanishing of mix `modelRemainder` / `failureMass`.
Kernel close.

**Remaining.** Mix `modelRemainder` / `failureMass`;
`adverseBudget` / AHL; `MixZetaTendstoOne` (not claimed).

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `actualRootLaw` nonnegative | theorem (`crtMixUnnorm_actualRootLaw_nonneg`) |
| `actualRootLaw` sums to 1 | theorem (`crtMixUnnorm_actualRootLaw_sum`) |
| `finiteRootMixUnnorm` nonnegative | theorem (`crtMixUnnorm_finiteRootMixUnnorm_nonneg`) |
| `∑ finiteRootMixUnnorm = mixZeta` | theorem (`crtMixUnnorm_sum`; `0 < windowNX`) |
| `∑ finiteRootMix = 1` | theorem (`crtMixUnnorm_finiteRootMix_sum`; `mixZ ≠ 0`) |
| Stopped L¹ + failure vs unnorm + additive `|1−ζ|` | theorem (`crtMixUnnorm_stoppedShapeL1_le`) |
| `|Z/N−1|` paid additively, not `× exp(C L)` | theorem (same) |
| `1 ≤ L`, `L ≤ r`, `Odd (r−L)` | remaining binders (profile parity is private in `StoppedPrime`; `profileR_ge` lives in `KuperbergAHL`, not imported) |
| mix `failureMass` / `modelRemainder` vanish | remaining |
| `adverseBudget` / AHL | remaining |
| `MixZetaTendstoOne` | not claimed (`MixZeta.lean` / `MixPrimeCountingAsymp`) |
| `HLMismatchVanishes` at Dirac CRT | remaining; not a goal of this leaf |
| AHL | remaining; not a goal of this leaf |

Does not claim the kernel is closed.

Source: `rounds/round115/09_grok_mixture_gate_and_cutoff_bridge.md` M1;
`ExactRootMix` (unnormalized `ν̃` as Stopped input);
`Stopped.stoppedShapeL1_add_failure_le_unequalMass`;
`StoppedPrime.actualConfigMass`, `sum_actualConfigMass`.
Contract: API
Audit: GREEN
-/

open Finset
open scoped Classical

namespace PrimeGapNormality.Prime

/-! ### Probability of `actualRootLaw` (unique copies; no CRT-leaf import) -/

/-- Residue space is nonempty: each prime `p ≤ y` has a nonzero
residue slot `Fin (p − 1)`. -/
theorem crtMixUnnorm_residueChoice_card_pos (y : ℕ) :
    0 < Fintype.card (ResidueChoice y) := by
  letI : Nonempty (ResidueChoice y) :=
    ⟨fun p =>
      ⟨0, Nat.sub_pos_of_lt
        (Nat.prime_of_mem_primesLE p.property).one_lt⟩⟩
  exact Fintype.card_pos

theorem crtMixUnnorm_residueChoice_card_ne_zero (y : ℕ) :
    (Fintype.card (ResidueChoice y) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr
    (Nat.pos_iff_ne_zero.mp (crtMixUnnorm_residueChoice_card_pos y))

theorem crtMixUnnorm_sieveSurvivorsFin_mem_powerset
    (y S : ℕ) (σ : ResidueChoice y) :
    sieveSurvivorsFin y σ S ∈ (offsetWindow S).powerset :=
  mem_powerset.mpr (filter_subset _ _)

/-- Nonnegativity from the definition `card / card`. Unique copy:
not `crtHL_actualRootLaw_nonneg`. -/
theorem crtMixUnnorm_actualRootLaw_nonneg (y S : ℕ) (U : Finset ℕ) :
    0 ≤ actualRootLaw y S U :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Fibrewise card-sum: every residue choice lands in the powerset,
so the masses partition 1. Copied from `CrtMixtureTransfer` /
`CrtFailureMassLimit` under a unique name; neither file is imported. -/
theorem crtMixUnnorm_actualRootLaw_sum (y S : ℕ) :
    ∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U = 1 := by
  have hmaps :
      ((univ : Finset (ResidueChoice y)) : Set (ResidueChoice y)).MapsTo
        (fun σ => sieveSurvivorsFin y σ S) (offsetWindow S).powerset :=
    fun σ _ => crtMixUnnorm_sieveSurvivorsFin_mem_powerset y S σ
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
  exact div_self (crtMixUnnorm_residueChoice_card_ne_zero y)

/-- `EndAPI.windowOmega` is definitionally the offset window. -/
theorem crtMixUnnorm_windowOmega_eq_offsetWindow (κ : ℝ) (X : ℕ) :
    windowOmega κ X = offsetWindow (profileS κ X) :=
  rfl

/-! ### Unnormalized and normalized mix masses -/

/-- Numerator of both `finiteRootMixUnnorm` and `finiteRootMix`
sums to `Z_X`, because each `actualRootLaw(y_t)` is a probability. -/
theorem crtMixUnnorm_sum_num (X S : ℕ) :
    ∑ U ∈ (offsetWindow S).powerset,
        ∑ t ∈ mixScale X, mixWeightV t *
          actualRootLaw (sieveCutoff (t : ℝ)) S U =
      mixZ X := by
  rw [sum_comm]
  have hpt : ∀ t ∈ mixScale X,
      ∑ U ∈ (offsetWindow S).powerset,
          mixWeightV t * actualRootLaw (sieveCutoff (t : ℝ)) S U =
        mixWeightV t := fun t _ => by
    rw [← mul_sum, crtMixUnnorm_actualRootLaw_sum, mul_one]
  rw [sum_congr rfl hpt]
  rfl

/-- Unnormalized mix is nonnegative: `V(y_t) ≥ 0` and `N_X ≥ 0`. -/
theorem crtMixUnnorm_finiteRootMixUnnorm_nonneg
    (X S : ℕ) (U : Finset ℕ) :
    0 ≤ finiteRootMixUnnorm X S U := by
  unfold finiteRootMixUnnorm
  refine div_nonneg (sum_nonneg fun t _ => mul_nonneg
      (mixWeightV_nonneg t)
      (crtMixUnnorm_actualRootLaw_nonneg _ _ _)) ?_
  exact Nat.cast_nonneg _

/-- Each fibre sums to 1, so the unnormalized mix totals `ζ_X = Z_X/N_X`.
The identity is the Stopped mass of `ν̃`; `|ζ−1|` is paid later,
additively. -/
theorem crtMixUnnorm_sum (X S : ℕ) (_hN : 0 < windowNX X) :
    ∑ U ∈ (offsetWindow S).powerset, finiteRootMixUnnorm X S U =
      mixZeta X := by
  unfold finiteRootMixUnnorm mixZeta
  rw [← sum_div, crtMixUnnorm_sum_num]

/-- Normalized mix is a probability whenever `Z_X ≠ 0`.
(`mixScale` may be empty at `X = 0`, so `mixZ = 0` is possible.) -/
theorem crtMixUnnorm_finiteRootMix_sum (X S : ℕ) (hZ : mixZ X ≠ 0) :
    ∑ U ∈ (offsetWindow S).powerset, finiteRootMix X S U = 1 := by
  unfold finiteRootMix
  rw [← sum_div, crtMixUnnorm_sum_num]
  exact div_self hZ

/-! ### Stopped unequal-mass instance

Does **not** close `HLMismatchVanishes` at Dirac CRT. Does **not**
close AHL. The additive `|1 − mixZeta X|` is exactly `|Z_X/N_X − 1|`
and is not multiplied by `exp(C L)`. Remaining after this leaf:
mix `modelRemainder` / `failureMass`, `adverseBudget` / AHL, and
`MixZetaTendstoOne` (not claimed). -/

/-- Finite stopped comparison of the empirical configuration mass
against the unnormalized V-mix. Profile parity (`L ≤ r` and
`Odd (r − L)`) is kept as a binder: the matching lemmas in
`StoppedPrime` are private, and this leaf does not import
`KuperbergAHL`. -/
theorem crtMixUnnorm_stoppedShapeL1_le
    {κ d0 : ℝ} {X : ℕ}
    (hL : 1 ≤ profileL κ X)
    (hr : profileL κ X ≤ profileR (profileL κ X) d0)
    (hpar : Odd (profileR (profileL κ X) d0 - profileL κ X))
    (hN : 0 < windowNX X) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X)
        (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) +
      Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
        (profileL κ X) ≤
      Stopped.failureMass (windowOmega κ X)
          (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) +
        2 * Stopped.modelRemainder (windowOmega κ X)
          (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
          (profileR (profileL κ X) d0) +
        2 * Stopped.adverseBudget (windowOmega κ X)
          (actualConfigMass κ X)
          (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
          (profileR (profileL κ X) d0) +
        |1 - mixZeta X| := by
  have hμ :
      ∀ U ∈ (windowOmega κ X).powerset, 0 ≤ actualConfigMass κ X U :=
    fun U _ => actualConfigMass_nonneg κ X U
  have hν :
      ∀ U ∈ (windowOmega κ X).powerset,
        0 ≤ finiteRootMixUnnorm X (profileS κ X) U :=
    fun U _ => crtMixUnnorm_finiteRootMixUnnorm_nonneg X _ U
  have hmain :=
    Stopped.stoppedShapeL1_add_failure_le_unequalMass
      (Ω := windowOmega κ X) (μ := actualConfigMass κ X)
      (ν := finiteRootMixUnnorm X (profileS κ X))
      (L := profileL κ X) (r := profileR (profileL κ X) d0)
      hL hr hpar hμ hν
  have hμsum :
      ∑ U ∈ (windowOmega κ X).powerset, actualConfigMass κ X U = 1 :=
    sum_actualConfigMass hN
  have hνsum :
      ∑ U ∈ (windowOmega κ X).powerset,
          finiteRootMixUnnorm X (profileS κ X) U =
        mixZeta X := by
    rw [crtMixUnnorm_windowOmega_eq_offsetWindow]
    exact crtMixUnnorm_sum X (profileS κ X) hN
  rw [hμsum, hνsum] at hmain
  exact hmain

end PrimeGapNormality.Prime
