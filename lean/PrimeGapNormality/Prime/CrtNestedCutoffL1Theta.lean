import PrimeGapNormality.Prime.CrtNestedCutoffC1C3
import PrimeGapNormality.Prime.CrtNestedCutoffL1
import PrimeGapNormality.Prime.CrtNestedCutoffTheta
import PrimeGapNormality.Prime.CrtNestedCutoffVRatio
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

/-!
# Nested cutoffs: L1 instantiated at (C3), so `1 − Θ` is not a binder

Paper (C1) `∑ |μ₁ − μ₂| ≤ 2 M₁ (1 − Θ)` is
`crtNestL1_massL1_le`. Paper (C3)
`1 − Θ ≤ 1 − R + 1/(y₁ − 1)` is `crtNestTh_one_sub_le`.
This leaf multiplies them on the **same** mean card `M₁` as L1
(the window average of `|U|` under `actualRootLaw y₁ T`; see
`crtNestL1_meanCard` / the RHS mean in `crtNestL1_massL1_le`).
The remaining scalar is `1 − R + 1/(y₁ − 1)`, not a `1 − Θ`
binder.

`μ_i = actualRootLaw y_i T`. Finite nested-cutoff hypotheses
`2 ≤ y₁`, `y₁ ≤ y₂`, `T ≤ y₁` remain. Does **not** invent a new
`M₁` definition.

Optional mixScale/eventual form uses lake-green
`crtNestVR_one_sub_le_of`: `1 − R ≤ log 2 / log X + 1/y(t)`.
That is **not** `O(L/G)` and does **not** claim `M₁ ≤ 12 L`.

Does **not** import MixZeta, SingletonLi, FirstMoment,
ExceptionMass, CrudeMoment, C4Shape, MixUnnorm*,
ExactRootWindowClose, RootedCutoffTypicalOsc, WeylOf*,
CrtHLMismatchVanishing, CrtMixtureTransfer, CrtFailureMassLimit,
ExactLawTypicalSetMassLeOne, or KuperbergAHL.

Does **not** claim (C4) `O(L/G)`, unconditional `12 L`, `hoff` /
`hcard`, kernel close.

**Compiled.**
1. `actualRootLaw ≥ 0`; hence `M₁ ≥ 0`.
2. `0 ≤ 1 − Θ` from `lateRetention ≤ 1`.
3. Instantiated scale: `2 M (1 − Θ) ≤ 2 M (1 − R + 1/(y₁ − 1))`
   at the theorem `crtNestTh_one_sub_le` (no (C3) binder).
4. Nested `actualRootLaw` L1 ≤ `2 M₁ (1 − R + 1/(y₁ − 1))` (C1
   at (C3)).
5. Bounded tests (C2), complex and real, same scalar.
6. If also `1 − R ≤ δ` then L1 ≤ `2 M₁ (δ + 1/(y₁ − 1))`.
7. Pointwise `e¹⁶ ≤ X`, `X < t ≤ 2X`, and mixScale/eventual:
   L1 ≤ `2 M₁ (log 2 / log X + 1/y(t) + 1/(y(X) − 1))`.

**Not compiled.** (C4) `O(L/G)`. `M₁ ≤ 12 L`.
`HLMismatchVanishes`. Kernel close.

**Remaining hyps.** Nested binders `2 ≤ y₁ ≤ y₂` and `T ≤ y₁`.
Pointwise `Real.exp 16 ≤ X` for the jump (eventual discharges
the size of `X`). `M₁ ≤ 12 L` remaining, not claimed. Kernel
not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `0 ≤ M₁` | theorem (`crtNestL1Th_meanCard_nonneg`) |
| `0 ≤ 1−Θ` | theorem (not a consumer binder) |
| `2 M (1−Θ) ≤ 2 M (1−R+1/(y₁−1))` | theorem ((C3) no longer a binder) |
| mixed L1 ≤ `2 M₁ (1−R+1/(y₁−1))` | theorem (`2 ≤ y₁ ≤ y₂`, `T ≤ y₁`) |
| bounded-test mean (C2) | theorem (same binders, `|f| ≤ 1`) |
| `1−Θ` as a binder | disappeared |
| `1−R ≤ log 2/log X + 1/y(t)` on mixScale | theorem (pointwise `e¹⁶ ≤ X`) |
| `M₁ ≤ 12 L` | remaining (not claimed) |
| (C4) `O(L/G)` | not claimed |
| `HLMismatchVanishes` / kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round115/09_grok_mixture_gate_and_cutoff_bridge.md` §3;
`CrtNestedCutoffL1.crtNestL1_massL1_le`,
`CrtNestedCutoffTheta.crtNestTh_one_sub_le`,
`CrtNestedCutoffC1C3.crtNestC13_le`,
`CrtNestedCutoffVRatio.crtNestVR_one_sub_le_of`.
Contract: API
Audit: GREEN
-/

open Filter Finset

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Nonnegativity of `M₁` and `1 − Θ` -/

/-- Mass of `actualRootLaw` is a ratio of cardinals. Unique name:
forbidden files also prove this. -/
theorem crtNestL1Th_actualRootLaw_nonneg (y T : ℕ) (U : Finset ℕ) :
    0 ≤ actualRootLaw y T U :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Same mean card as `crtNestL1_massL1_le` / `crtNestL1_meanCard`.
Does **not** introduce a new `M₁` definition. -/
theorem crtNestL1Th_meanCard_nonneg (y T : ℕ) :
    0 ≤ ∑ U ∈ (offsetWindow T).powerset,
        (U.card : ℝ) * actualRootLaw y T U :=
  sum_nonneg fun U _ =>
    mul_nonneg (Nat.cast_nonneg _) (crtNestL1Th_actualRootLaw_nonneg y T U)

/-- `Θ = lateRetention y₁ y₂ ≤ 1`. Unique name. -/
theorem crtNestL1Th_one_sub_theta_nonneg (y1 y2 : ℕ) :
    0 ≤ 1 - lateRetention y1 y2 :=
  sub_nonneg.mpr (crtNestL1_lateRetention_le_one y1 y2)

/-! ### Instantiated `(C3)` scale: `1 − Θ` leaves the binder list -/

/-- Instantiated scale at the theorem `crtNestTh_one_sub_le`.
The (C3) comparison is no longer a binder. Remaining: `0 ≤ M` and
`2 ≤ y1 ≤ y2`. Does **not** claim (C1) or (C4). -/
theorem crtNestL1Th_two_mul_one_sub {M : ℝ} {y1 y2 : ℕ} (hM : 0 ≤ M)
    (hy1 : 2 ≤ y1) (hy12 : y1 ≤ y2) :
    (2 : ℝ) * M * (1 - lateRetention y1 y2) ≤
      2 * M *
        (1 - eulerProdNat y2 / eulerProdNat y1 + 1 / ((y1 : ℝ) - 1)) :=
  crtNestC13_two_mul_one_sub hM (crtNestL1Th_one_sub_theta_nonneg y1 y2)
    (crtNestTh_one_sub_le hy1 hy12)

/-! ### Mixed nested L1 (C1) at (C3) -/

/-- Full L1 of nested `actualRootLaw`, with (C3) instantiated.
Paper (C1) then (C3). The scalar `1 − Θ` is not a binder.
Does **not** claim `O(L/G)` or `M₁ ≤ 12 L`. Remaining:
`2 ≤ y1`, `y1 ≤ y2`, `T ≤ y1`. -/
theorem crtNestL1Th_massL1_le (y1 y2 T : ℕ)
    (hy : 2 ≤ y1) (h12 : y1 ≤ y2) (hT : T ≤ y1) :
    ∑ U ∈ (offsetWindow T).powerset,
        |actualRootLaw y1 T U - actualRootLaw y2 T U| ≤
      2 *
        (∑ U ∈ (offsetWindow T).powerset,
            (U.card : ℝ) * actualRootLaw y1 T U) *
        (1 - eulerProdNat y2 / eulerProdNat y1 + 1 / ((y1 : ℝ) - 1)) :=
  crtNestC13_le (crtNestL1Th_meanCard_nonneg y1 T)
    (crtNestL1Th_one_sub_theta_nonneg y1 y2)
    (crtNestL1_massL1_le y1 y2 T hy h12 hT)
    (crtNestTh_one_sub_le hy h12)

/-- Complex bounded test. Paper (C2) at (C3). Extra hyp: `|F| ≤ 1`. -/
theorem crtNestL1Th_abs_mean_sub_le (y1 y2 T : ℕ)
    (hy : 2 ≤ y1) (h12 : y1 ≤ y2) (hT : T ≤ y1)
    (F : Finset ℕ → ℂ) (hF : ∀ U, ‖F U‖ ≤ 1) :
    ‖∑ U ∈ (offsetWindow T).powerset,
        ((actualRootLaw y1 T U - actualRootLaw y2 T U : ℝ) : ℂ) *
          F U‖ ≤
      2 *
        (∑ U ∈ (offsetWindow T).powerset,
            (U.card : ℝ) * actualRootLaw y1 T U) *
        (1 - eulerProdNat y2 / eulerProdNat y1 + 1 / ((y1 : ℝ) - 1)) :=
  crtNestC13_le (crtNestL1Th_meanCard_nonneg y1 T)
    (crtNestL1Th_one_sub_theta_nonneg y1 y2)
    (crtNestL1_abs_mean_sub_le y1 y2 T hy h12 hT F hF)
    (crtNestTh_one_sub_le hy h12)

/-- Real bounded test. Paper (C2) at (C3). Extra hyp: `|f| ≤ 1`. -/
theorem crtNestL1Th_abs_mean_sub_le_real (y1 y2 T : ℕ)
    (hy : 2 ≤ y1) (h12 : y1 ≤ y2) (hT : T ≤ y1)
    (f : Finset ℕ → ℝ) (hf : ∀ U, |f U| ≤ 1) :
    |∑ U ∈ (offsetWindow T).powerset,
        (actualRootLaw y1 T U - actualRootLaw y2 T U) * f U| ≤
      2 *
        (∑ U ∈ (offsetWindow T).powerset,
            (U.card : ℝ) * actualRootLaw y1 T U) *
        (1 - eulerProdNat y2 / eulerProdNat y1 + 1 / ((y1 : ℝ) - 1)) :=
  crtNestC13_le (crtNestL1Th_meanCard_nonneg y1 T)
    (crtNestL1Th_one_sub_theta_nonneg y1 y2)
    (crtNestL1_abs_mean_sub_le_real y1 y2 T hy h12 hT f hf)
    (crtNestTh_one_sub_le hy h12)

/-! ### Replace `1 − R` by any larger `δ` -/

/-- If also `1 − R ≤ δ` then L1 ≤ `2 M₁ (δ + 1/(y₁ − 1))`. Remaining:
`2 ≤ y1 ≤ y2`, `T ≤ y1`, and `1 − R ≤ δ`. Does **not** claim
`O(L/G)`. -/
theorem crtNestL1Th_massL1_le_of_one_sub (y1 y2 T : ℕ) {δ : ℝ}
    (hy : 2 ≤ y1) (h12 : y1 ≤ y2) (hT : T ≤ y1)
    (hδ : 1 - eulerProdNat y2 / eulerProdNat y1 ≤ δ) :
    ∑ U ∈ (offsetWindow T).powerset,
        |actualRootLaw y1 T U - actualRootLaw y2 T U| ≤
      2 *
        (∑ U ∈ (offsetWindow T).powerset,
            (U.card : ℝ) * actualRootLaw y1 T U) *
        (δ + 1 / ((y1 : ℝ) - 1)) :=
  (crtNestL1Th_massL1_le y1 y2 T hy h12 hT).trans
    (crtNestC13_two_mul_mono (crtNestL1Th_meanCard_nonneg y1 T)
      ((crtNestL1Th_one_sub_theta_nonneg y1 y2).trans
        (crtNestTh_one_sub_le hy h12))
      (add_le_add hδ (le_refl (1 / ((y1 : ℝ) - 1)))))

/-! ### Jump `1 − R` at calibrated cutoffs (not `(C4)`) -/

private theorem crtNestL1Th_one_lt_of_exp_sixteen_le {t : ℝ}
    (ht : Real.exp 16 ≤ t) : 1 < t :=
  lt_of_lt_of_le
    (lt_trans (by norm_num : (1 : ℝ) < 2)
      (lt_trans Real.exp_one_gt_two
        (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16))))
    ht

private theorem crtNestL1Th_two_le_sieveCutoff {X : ℝ}
    (hX : Real.exp 16 ≤ X) : 2 ≤ sieveCutoff X :=
  (sieveCutoff_spec (crtNestL1Th_one_lt_of_exp_sixteen_le hX)).1.two_le

private theorem crtNestL1Th_sieveCutoff_le {X t : ℝ}
    (hX : Real.exp 16 ≤ X) (hXt : X < t) :
    sieveCutoff X ≤ sieveCutoff t :=
  crtNestVR_sieveCutoff_mono (crtNestL1Th_one_lt_of_exp_sixteen_le hX) hXt

private theorem crtNestL1Th_mem_Ioc {X t : ℕ} (ht : t ∈ mixScale X) :
    (X : ℝ) < t ∧ (t : ℝ) ≤ 2 * (X : ℝ) := by
  have h := mem_Ioc.mp (by simpa [mixScale] using ht)
  refine ⟨Nat.cast_lt.mpr h.1, ?_⟩
  have hle : (t : ℝ) ≤ ((2 * X : ℕ) : ℝ) := Nat.cast_le.mpr h.2
  simpa [Nat.cast_mul, Nat.cast_ofNat] using hle

/-- Paper: nested L1 ≤ `2 M₁ (log 2 / log X + 1/y(t) + 1/(y(X) − 1))`
for `e¹⁶ ≤ X` and `X < t ≤ 2X`. Remaining: `T ≤ y(X)`. Does **not**
claim `O(L/G)` or `M₁ ≤ 12 L`. -/
theorem crtNestL1Th_massL1_le_of {X t : ℝ} (T : ℕ)
    (hX : Real.exp 16 ≤ X) (hXt : X < t) (ht2 : t ≤ 2 * X)
    (hT : T ≤ sieveCutoff X) :
    ∑ U ∈ (offsetWindow T).powerset,
        |actualRootLaw (sieveCutoff X) T U -
          actualRootLaw (sieveCutoff t) T U| ≤
      2 *
        (∑ U ∈ (offsetWindow T).powerset,
            (U.card : ℝ) * actualRootLaw (sieveCutoff X) T U) *
        (Real.log 2 / Real.log X + (sieveCutoff t : ℝ)⁻¹ +
          1 / ((sieveCutoff X : ℝ) - 1)) :=
  crtNestL1Th_massL1_le_of_one_sub (sieveCutoff X) (sieveCutoff t) T
    (crtNestL1Th_two_le_sieveCutoff hX)
    (crtNestL1Th_sieveCutoff_le hX hXt) hT
    (crtNestVR_one_sub_le_of hX hXt ht2)

/-- Same bound on `t ∈ mixScale X = Ioc X (2X)`. Remaining:
`T ≤ y(X)` and `Real.exp 16 ≤ (X : ℝ)`. Does **not** claim
`O(L/G)` or `M₁ ≤ 12 L`. -/
theorem crtNestL1Th_massL1_le_mixScale {X t T : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) (ht : t ∈ mixScale X)
    (hT : T ≤ sieveCutoff (X : ℝ)) :
    ∑ U ∈ (offsetWindow T).powerset,
        |actualRootLaw (sieveCutoff (X : ℝ)) T U -
          actualRootLaw (sieveCutoff (t : ℝ)) T U| ≤
      2 *
        (∑ U ∈ (offsetWindow T).powerset,
            (U.card : ℝ) *
              actualRootLaw (sieveCutoff (X : ℝ)) T U) *
        (Real.log 2 / Real.log (X : ℝ) + (sieveCutoff (t : ℝ) : ℝ)⁻¹ +
          1 / ((sieveCutoff (X : ℝ) : ℝ) - 1)) :=
  crtNestL1Th_massL1_le_of_one_sub
    (sieveCutoff (X : ℝ)) (sieveCutoff (t : ℝ)) T
    (crtNestL1Th_two_le_sieveCutoff hX)
    (crtNestL1Th_sieveCutoff_le hX (crtNestL1Th_mem_Ioc ht).1) hT
    (crtNestVR_one_sub_le_mixScale hX ht)

/-! ### Eventual form -/

/-- Eventual nested L1 ≤ `2 M₁ (log 2 / log X + 1/y(t) + 1/(y(X) − 1))`
on the mix support `Ioc X (2X)`. Remaining: `T ≤ y(X)` (size of `X`
is eventual). Does **not** claim
`∑ |μ_{y(t)} − μ_{y(X)}| = O(L/G)` or `M₁ ≤ 12 L`. -/
theorem crtNestL1Th_massL1_le_atTop :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ Ioc X (2 * X),
      ∀ T : ℕ, T ≤ sieveCutoff (X : ℝ) →
        ∑ U ∈ (offsetWindow T).powerset,
            |actualRootLaw (sieveCutoff (X : ℝ)) T U -
              actualRootLaw (sieveCutoff (t : ℝ)) T U| ≤
          2 *
            (∑ U ∈ (offsetWindow T).powerset,
                (U.card : ℝ) *
                  actualRootLaw (sieveCutoff (X : ℝ)) T U) *
            (Real.log 2 / Real.log (X : ℝ) +
              (sieveCutoff (t : ℝ) : ℝ)⁻¹ +
              1 / ((sieveCutoff (X : ℝ) : ℝ) - 1)) := by
  filter_upwards [crtNestVR_eventually_exp_sixteen] with X hX
  intro t ht T hT
  exact crtNestL1Th_massL1_le_mixScale hX (by simpa [mixScale] using ht) hT

end

end PrimeGapNormality.Prime
