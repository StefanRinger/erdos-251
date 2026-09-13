import PrimeGapNormality.Prime.EndAPI
import PrimeGapNormality.Prime.KuperbergClose
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# SmallWindow AHL adapter (`S_small = ⌊(6/5) L G⌋`)

Paper v0.14 uses one window `S_small = ⌊(6/5) L G⌋` for geometry,
moments and AHL. Public EndAPI stays the factor-4 large path:

  `profileS = ⌊4 L G⌋`, `windowOmega = Icc 1 profileS`,
  `ahlLayer` / `ahlBudget` / `AHL` = AHL_large.

This leaf is the named SmallWindow adapter. Same `profileL`, same
`r = profileR L d0`, same signs and binomial weights
`(j-1).choose (L-1)`. The small layer sums the same nonnegative
positive parts over `Icc 1 S_small ⊆ windowOmega`, so
`E_small(X) ≤ E_large(X)` pointwise and `AHL → ahlSmall_AHL`.
The reverse is **not** claimed.

The floor formula is the same as `SieveCirc`, but **SieveCirc is
not imported** (that module sits in the lake queue).

Does **not** rewrite EndAPI. Does **not** claim that a compiled
AHL_large Weyl/Mix closer already proves the paper end theorem
under only `ahlSmall_AHL`. No inner/outer stop, no re-expansion,
no `30/L`, no (C4), no kernel, no PrimeCountingNormalization. Does **not**
import MixZeta or SingletonLi.

**Compiled.**
1. `ahlSmall_window = ⌊((6:ℝ)/5) * profileL κ X * windowG X⌋₊`.
2. `1 ≤ windowG`, hence `0 ≤ windowG`; `(6/5) ≤ 4`;
   `ahlSmall_window ≤ profileS`.
3. `ahlSmall_omega = Icc 1 ahlSmall_window ⊆ windowOmega`.
4. `ahlSmall_layer` = `ahlLayer` summed over `ahlSmall_omega`.
5. Pointwise `ahlSmall_layer ≤ ahlLayer` (dropped summands are
   nonnegative positive parts).
6. Same weights ⇒ `ahlSmall_budget ≤ ahlBudget`.
7. `AHL κ d0 → ahlSmall_AHL κ d0` (Tendsto squeeze). Reverse not
   claimed.
8. Existing `kuperberg_implies_AHL` composes to
   `KuperbergConj13 → ahlSmall_AHL` (old stronger path).

**Not compiled.** `ahlSmall_AHL → AHL`. Weyl/Mix end theorems
under only `ahlSmall_AHL`. Inner vs outer stop. Re-expansion.
`30/L`. (C4). Kernel close. PrimeCountingNormalization. Identification
with `SieveCirc` (formula duplicated, module not imported).

**Remaining hyps.** None for `ahlSmall_window ≤ profileS` or the
pointwise layer/budget comparison (`windowG ≥ 1` is a theorem;
`profileL : ℕ`). `AHL → ahlSmall_AHL` takes `AHL`. The Kuperberg
path still needs `KuperbergConj13`, `0 < κ` and `0 < d0`, same as
`kuperberg_implies_AHL`. Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `ahlSmall_window = ⌊(6/5) L G⌋` | definition |
| `ahlSmall_window ≤ profileS` | theorem (`windowG ≥ 1`) |
| `ahlSmall_omega ⊆ windowOmega` | theorem |
| `ahlSmall_layer ≤ ahlLayer` | theorem (nonneg summands) |
| `ahlSmall_budget ≤ ahlBudget` | theorem |
| `AHL → ahlSmall_AHL` | theorem (Tendsto) |
| `ahlSmall_AHL → AHL` | not claimed |
| `KuperbergConj13 → ahlSmall_AHL` | theorem (compose AHL_large) |
| Weyl/Mix closer under only `ahlSmall_AHL` | not claimed |
| inner/outer stop, `30/L`, (C4), kernel | not claimed |

AHL vs AHLSmall: `AHL` remains AHL_large on `windowOmega`.
`ahlSmall_AHL` is the paper `S_small` budget. Large implies small;
small does not imply large; an AHL_large closer is not a paper
closer under only `ahlSmall_AHL`.

Does not claim the kernel is closed.

Source: `rounds/round118/17_grok_single_window_delta.md`;
v0.14 SHA-256
`dae6dead578de461821da4e0b005897e0272e207d61466a8c0cbbf7f492ffcf6`;
`EndAPI.profileL`, `EndAPI.windowG`, `EndAPI.profileS`,
`EndAPI.windowOmega`, `EndAPI.ahlLayer`, `EndAPI.ahlBudget`,
`EndAPI.AHL`; `KuperbergClose.kuperberg_implies_AHL`.
Contract: API
-/

namespace PrimeGapNormality.Prime

open Finset Filter
open scoped Topology

noncomputable section

/-! ### Small window `S_small = ⌊(6/5) L G⌋` -/

/-- Paper `S_small = ⌊(6/5) L G⌋`. Uses existing `profileL` and
`windowG`; does not rewrite `profileS`. -/
def ahlSmall_window (κ : ℝ) (X : ℕ) : ℕ :=
  ⌊((6 : ℝ) / 5) * (profileL κ X : ℝ) * windowG X⌋₊

/-- Unfolding. -/
theorem ahlSmall_window_eq (κ : ℝ) (X : ℕ) :
    ahlSmall_window κ X =
      ⌊((6 : ℝ) / 5) * (profileL κ X : ℝ) * windowG X⌋₊ :=
  rfl

/-! ### Nonnegative factors -/

/-- Floor at `1` in `windowG`. -/
theorem ahlSmall_windowG_one_le (X : ℕ) : (1 : ℝ) ≤ windowG X :=
  le_max_right _ _

/-- `windowG` is nonnegative. -/
theorem ahlSmall_windowG_nonneg (X : ℕ) : (0 : ℝ) ≤ windowG X :=
  le_trans (by norm_num : (0 : ℝ) ≤ 1) (ahlSmall_windowG_one_le X)

/-- Coefficient `(6:ℝ)/5` is nonnegative. -/
theorem ahlSmall_six_div_five_nonneg : (0 : ℝ) ≤ (6 : ℝ) / 5 :=
  div_nonneg (by norm_num) (by norm_num)

/-- Floor argument of `ahlSmall_window` is nonnegative. -/
theorem ahlSmall_arg_nonneg (κ : ℝ) (X : ℕ) :
    (0 : ℝ) ≤ ((6 : ℝ) / 5) * (profileL κ X : ℝ) * windowG X :=
  mul_nonneg
    (mul_nonneg ahlSmall_six_div_five_nonneg (Nat.cast_nonneg _))
    (ahlSmall_windowG_nonneg X)

/-! ### Coefficient comparison `(6/5) ≤ 4` -/

/-- `(6:ℝ)/5 ≤ 4`. -/
theorem ahlSmall_six_div_five_le_four : (6 : ℝ) / 5 ≤ 4 := by
  have hpos : (0 : ℝ) < 5 := by norm_num
  exact (div_le_iff₀ hpos).mpr (by norm_num : (6 : ℝ) ≤ (4 : ℝ) * 5)

/-- `(6/5) L G ≤ 4 L G` for a natural `L` and nonnegative `G`. -/
theorem ahlSmall_six_div_five_mul_le {L : ℕ} {G : ℝ} (hG : 0 ≤ G) :
    ((6 : ℝ) / 5) * (L : ℝ) * G ≤ (4 : ℝ) * (L : ℝ) * G := by
  have hLG : (0 : ℝ) ≤ (L : ℝ) * G :=
    mul_nonneg (Nat.cast_nonneg L) hG
  have hmul :
      ((6 : ℝ) / 5) * ((L : ℝ) * G) ≤ (4 : ℝ) * ((L : ℝ) * G) :=
    mul_le_mul_of_nonneg_right ahlSmall_six_div_five_le_four hLG
  calc
    ((6 : ℝ) / 5) * (L : ℝ) * G
        = ((6 : ℝ) / 5) * ((L : ℝ) * G) := mul_assoc _ _ _
    _ ≤ (4 : ℝ) * ((L : ℝ) * G) := hmul
    _ = (4 : ℝ) * (L : ℝ) * G := (mul_assoc _ _ _).symm

/-- Same comparison at `L = profileL κ X` and `G = windowG X`.
Remaining: `0 ≤ windowG X`. -/
theorem ahlSmall_arg_le_profileS_arg {κ : ℝ} {X : ℕ}
    (hG : 0 ≤ windowG X) :
    ((6 : ℝ) / 5) * (profileL κ X : ℝ) * windowG X ≤
      (4 : ℝ) * (profileL κ X : ℝ) * windowG X :=
  ahlSmall_six_div_five_mul_le hG

/-! ### Floor comparison `S_small ≤ profileS` -/

/-- Small window is at most the public `profileS` as soon as
`windowG` is nonnegative. `profileL` is a `ℕ`. -/
theorem ahlSmall_window_le_profileS_of {κ : ℝ} {X : ℕ}
    (hG : 0 ≤ windowG X) :
    ahlSmall_window κ X ≤ profileS κ X := by
  unfold ahlSmall_window profileS
  exact Nat.floor_le_floor (ahlSmall_arg_le_profileS_arg hG)

/-- Unconditional form: `1 ≤ windowG X` supplies nonnegativity.
`0 ≤ κ` is not required. -/
theorem ahlSmall_window_le_profileS (κ : ℝ) (X : ℕ) :
    ahlSmall_window κ X ≤ profileS κ X :=
  ahlSmall_window_le_profileS_of (ahlSmall_windowG_nonneg X)

/-! ### Small search window `Icc 1 S_small` -/

/-- Paper window `{1, …, S_small}`. -/
def ahlSmall_omega (κ : ℝ) (X : ℕ) : Finset ℕ :=
  Icc 1 (ahlSmall_window κ X)

/-- Unfolding. -/
theorem ahlSmall_omega_eq (κ : ℝ) (X : ℕ) :
    ahlSmall_omega κ X = Icc 1 (ahlSmall_window κ X) :=
  rfl

/-- `Icc 1 S_small ⊆ Icc 1 profileS`. -/
theorem ahlSmall_omega_subset_windowOmega (κ : ℝ) (X : ℕ) :
    ahlSmall_omega κ X ⊆ windowOmega κ X := by
  unfold ahlSmall_omega windowOmega
  exact Icc_subset_Icc_right (ahlSmall_window_le_profileS κ X)

/-- Card-`j` subsets of the small window sit inside the large
layer index set. -/
theorem ahlSmall_powerset_filter_subset (κ : ℝ) (X j : ℕ) :
    (ahlSmall_omega κ X).powerset.filter (fun H => H.card = j) ⊆
      (windowOmega κ X).powerset.filter (fun H => H.card = j) :=
  filter_subset_filter (fun H => H.card = j)
    (powerset_mono.mpr (ahlSmall_omega_subset_windowOmega κ X))

/-! ### Small AHL layer -/

/-- One layer of the small-window positive-part budget. Same
sign `(-1)^(j-L+1)` as `ahlLayer`; sum over `ahlSmall_omega`. -/
def ahlSmall_layer (κ : ℝ) (X j L : ℕ) : ℝ :=
  ∑ H ∈ (ahlSmall_omega κ X).powerset.filter fun H => H.card = j,
    (((-1 : ℝ) ^ (j - L + 1)) *
      ((rootedTupleCount X H : ℝ) - rootedMainTerm X H))⁺

/-- Positive parts. -/
theorem ahlSmall_layer_nonneg (κ : ℝ) (X j L : ℕ) :
    0 ≤ ahlSmall_layer κ X j L := by
  unfold ahlSmall_layer
  exact sum_nonneg fun _ _ => posPart_nonneg _

/-- Dropping nonnegative positive parts cannot raise the layer. -/
theorem ahlSmall_layer_le_ahlLayer (κ : ℝ) (X j L : ℕ) :
    ahlSmall_layer κ X j L ≤ ahlLayer κ X j L := by
  unfold ahlSmall_layer ahlLayer
  exact sum_le_sum_of_subset_of_nonneg
    (ahlSmall_powerset_filter_subset κ X j)
    fun _ _ _ => posPart_nonneg _

/-! ### Small aggregated budget (`r = profileR` unchanged) -/

/-- Paper `ℰ` on `S_small`, same `L` and `r = profileR L d0`. -/
def ahlSmall_budget (κ d0 : ℝ) (X : ℕ) : ℝ :=
  let L := profileL κ X
  let r := profileR L d0
  if windowNX X = 0 then 1
  else
    (1 / (windowNX X : ℝ)) *
      ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) *
        ahlSmall_layer κ X j L

/-- Sentinel `1` or a sum of nonnegative terms. -/
theorem ahlSmall_budget_nonneg (κ d0 : ℝ) (X : ℕ) :
    0 ≤ ahlSmall_budget κ d0 X := by
  unfold ahlSmall_budget
  split_ifs
  · exact zero_le_one
  · refine mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _)) ?_
    exact sum_nonneg fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (ahlSmall_layer_nonneg κ X j _)

/-- Same `profileL`, same `profileR`, same binomial weights.
Pointwise `E_small ≤ E_large`. -/
theorem ahlSmall_budget_le_ahlBudget (κ d0 : ℝ) (X : ℕ) :
    ahlSmall_budget κ d0 X ≤ ahlBudget κ d0 X := by
  unfold ahlSmall_budget ahlBudget
  split_ifs
  · exact le_rfl
  · refine mul_le_mul_of_nonneg_left ?_
      (div_nonneg zero_le_one (Nat.cast_nonneg _))
    refine sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left
        (ahlSmall_layer_le_ahlLayer κ X j (profileL κ X))
        (Nat.cast_nonneg _)

/-! ### `AHL` (large) implies `ahlSmall_AHL`; reverse not claimed -/

/-- Aggregated one-sided hypothesis on the paper window `S_small`.
This is **not** `AHL` (AHL_large). -/
def ahlSmall_AHL (κ d0 : ℝ) : Prop :=
  Tendsto (fun X : ℕ => ahlSmall_budget κ d0 X) atTop (nhds 0)

/-- `0 ≤ ahlSmall_budget ≤ ahlBudget` and `AHL` squeeze.
Does **not** claim the reverse. -/
theorem ahlSmall_AHL_of_AHL {κ d0 : ℝ} (hAHL : AHL κ d0) :
    ahlSmall_AHL κ d0 :=
  squeeze_zero (ahlSmall_budget_nonneg κ d0)
    (ahlSmall_budget_le_ahlBudget κ d0) hAHL

/-- Old stronger path: Kuperberg → AHL_large → `ahlSmall_AHL`.
Remaining: `KuperbergConj13`, `0 < κ`, `0 < d0`. Does **not**
claim that an AHL_large Weyl/Mix closer already proves the paper
end theorem under only `ahlSmall_AHL`. -/
theorem ahlSmall_AHL_of_KuperbergConj13 (hK : KuperbergConj13)
    {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    ahlSmall_AHL κ d0 :=
  ahlSmall_AHL_of_AHL (kuperberg_implies_AHL hK hκ hd0)

end

end PrimeGapNormality.Prime
