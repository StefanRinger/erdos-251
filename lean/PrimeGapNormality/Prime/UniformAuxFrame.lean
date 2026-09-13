import PrimeGapNormality.Prime.SubsetSpacing
import PrimeGapNormality.Prime.CompleteFrameMass
import PrimeGapNormality.Prime.SlotResample
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

/-!
# Uniform auxiliary frames: exact `n` versus `n−1` slot sum

Paper v0.16, positive-frame mean. For a positive finite `A ⊂ ℕ` with
`M = |A|`, exact layer `n` (`1 ≤ n ≤ M`; paper `n ≥ L`), and Lean rank
`j` with `j + 1 < n` (paper `1 ≤ j < L`, already `j + 1 < L` in
`SubsetSpacing`):

* `U` uniform among the `n`-subsets of `A`;
* `F` uniform among **all** `(n−1)`-subsets;
* `W_F` the insertion slot of the `j`-th **positive** point
  (`openSlot`; `A ∩ W_F`).

For a general test `f : Finset ℕ → ℝ` (paper: nonnegative),

    `E[f(U)] = n/(M−n+1) · E_F Σ_{u ∈ A ∩ W_F} f(F ∪ {u})`.

Equivalent binomial form
`C(M, n−1) / C(M, n) = n / (M−n+1)`. Empty slots are allowed in the
auxiliary measure; **no division by slot cardinality**. This is **not**
the claim that fixed-rank deletion yields uniform frames: the original
weights still contain `|A ∩ W_F|`.

Local public bijection: insert/erase of the `j`-th point on the exact
layers `n` and `n−1`. Does **not** call the private
`generic_preimage_sum_eq_geL` in `SubsetSpacing`. Does **not** apply
`GenericFrameMassEqGeL` to `μ · f` (`μ · f` is not cardinality-symmetric
in general). Exact cardinality, not the incomplete-frame sum `≥ L`.

Unique names `auxFrame_`. Does not import MixZeta, SingletonLi, AHLSmall,
Kernel, (C4), `EndAPI.profileS`, Selberg domination, Fourier square,
the `8^r` hull, relative presieve raster, rank→location, or slot-cut.

**Compiled.**
1. `n · C(M, n) = (M−n+1) · C(M, n−1)` (`1 ≤ n ≤ M`).
2. Quotient `C(M, n−1) / C(M, n) = n / (M−n+1)`.
3. Coefficient `n/(M−n+1) · 1/C(M, n−1) = 1/C(M, n)`.
4. Layer cards `#(powersetCard A n) = C(M, n)`.
5. Weighted bijection: `Σ_U f(U) = Σ_F Σ_{u ∈ openSlot} f(insert u F)`.
6. Uniform Finset mean identity, no slot-size division.
7. Nonnegativity of the mean when `0 ≤ f`.

**Not compiled.** Selberg domination. Fourier square. `8^r` hull.
Kernel. (C4). MixZeta. SingletonLi. AHLSmall. `EndAPI.profileS`.
Relative presieve raster. Rank→physical location. Slot-cut. Inverse
slot moments. ε-limit. Joint AC of the original fixed-rank frame
measure. The claim that remaining frames are uniform.

**Remaining hyps.** `1 ≤ n ≤ |A|`, `j + 1 < n`, positivity `∀ x ∈ A,
0 < x` (open-slot sentinel `0`), and `0 ≤ f` on the mean-nonnegativity
lemma. Paper `n ≥ L` and `j + 1 < L` imply `j + 1 < n`. Kernel not
closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| binomial product identity | theorem (`auxFrame_choose_mul`) |
| binomial quotient | theorem (`auxFrame_choose_ratio`) |
| mean coefficient | theorem (`auxFrame_choose_coeff`) |
| exact-layer preimage bijection | theorem (`auxFrame_preimage_sum`) |
| uniform mean identity | theorem (`auxFrame_uniformMean_eq`) |
| remaining frames themselves uniform | not claimed |
| `GenericFrameMassEqGeL` on `μ · f` | not used |
| Selberg / Fourier / `8^r` / kernel / (C4) | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round119/19_grok_v016_positive_frames_delta.md`;
paper `17_paper_v0_16.tex`
SHA-256 `86d4589af0a05aed4230a4f27625bfe85128b5cf70dbf976a64e3e7dd80c209d`.
`SubsetSpacing` GREEN (do not edit). Rank convention:
paper `1 ≤ j < L` is Lean `j + 1 < L`.
Contract: API
-/

open Finset

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

/-! ### Binomial identities `n · C(M,n) = (M−n+1) · C(M,n−1)` -/

theorem auxFrame_choose_mul {M n : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    n * M.choose n = (M - n + 1) * M.choose (n - 1) := by
  have h := Nat.choose_succ_right_eq M (n - 1)
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hsub : M - (n - 1) = M - n + 1 := tsub_tsub_assoc hnM hn
  rw [hn1, hsub] at h
  rw [Nat.mul_comm n, Nat.mul_comm (M - n + 1)]
  exact h

theorem auxFrame_cast_sub {M n : ℕ} (hnM : n ≤ M) :
    ((M - n + 1 : ℕ) : ℝ) = (M : ℝ) - n + 1 := by
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hnM]

theorem auxFrame_choose_ne_zero {M n : ℕ} (hnM : n ≤ M) :
    (M.choose n : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.choose_pos hnM).ne'

theorem auxFrame_choose_pred_ne_zero {M n : ℕ} (hnM : n ≤ M) :
    (M.choose (n - 1) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.choose_pos (le_trans (Nat.sub_le n 1) hnM)).ne'

theorem auxFrame_sub_ne_zero {M n : ℕ} (hnM : n ≤ M) :
    (M : ℝ) - n + 1 ≠ 0 := by
  rw [← auxFrame_cast_sub hnM]
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)

theorem auxFrame_choose_mul_real {M n : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    (n : ℝ) * (M.choose n : ℝ) =
      ((M : ℝ) - n + 1) * (M.choose (n - 1) : ℝ) := by
  have h := congrArg (fun k : ℕ => (k : ℝ)) (auxFrame_choose_mul hn hnM)
  simp only [Nat.cast_mul] at h
  rwa [auxFrame_cast_sub hnM] at h

/-- Paper equivalent: `C(M, n−1) / C(M, n) = n / (M−n+1)`. -/
theorem auxFrame_choose_ratio {M n : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    (M.choose (n - 1) : ℝ) / (M.choose n : ℝ) =
      (n : ℝ) / ((M : ℝ) - n + 1) := by
  refine (div_eq_div_iff (auxFrame_choose_ne_zero hnM)
      (auxFrame_sub_ne_zero hnM)).mpr ?_
  have h := auxFrame_choose_mul_real hn hnM
  calc
    (M.choose (n - 1) : ℝ) * ((M : ℝ) - n + 1)
        = ((M : ℝ) - n + 1) * (M.choose (n - 1) : ℝ) :=
          mul_comm (M.choose (n - 1) : ℝ) _
    _ = (n : ℝ) * (M.choose n : ℝ) := h.symm

/-- Coefficient in the uniform-mean identity. -/
theorem auxFrame_choose_coeff {M n : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    (n : ℝ) / ((M : ℝ) - n + 1) * (1 / (M.choose (n - 1) : ℝ)) =
      1 / (M.choose n : ℝ) := by
  have hpred := auxFrame_choose_pred_ne_zero hnM
  calc
    (n : ℝ) / ((M : ℝ) - n + 1) * (1 / (M.choose (n - 1) : ℝ))
        = (M.choose (n - 1) : ℝ) / (M.choose n : ℝ) *
            (1 / (M.choose (n - 1) : ℝ)) := by
          rw [auxFrame_choose_ratio hn hnM]
    _ = (M.choose (n - 1) : ℝ) * (M.choose n : ℝ)⁻¹ *
          (M.choose (n - 1) : ℝ)⁻¹ := by
        rw [div_eq_mul_inv, one_div]
    _ = (M.choose n : ℝ)⁻¹ := by
      rw [mul_comm (M.choose (n - 1) : ℝ), mul_assoc,
        mul_inv_cancel₀ hpred, mul_one]
    _ = 1 / (M.choose n : ℝ) := (one_div _).symm

theorem auxFrame_powersetCard_card (A : Finset ℕ) (n : ℕ) :
    (A.powersetCard n).card = A.card.choose n :=
  card_powersetCard _ _

/-! ### Slot insert sum (no division by `|A ∩ W_F|`) -/

/-- Inner paper sum `Σ_{u ∈ A ∩ W_F} f(F ∪ {u})`. Empty slot is `0`. -/
def auxFrame_slotInsertSum (A : Finset ℕ) (j : ℕ) (f : Finset ℕ → ℝ)
    (F : Finset ℕ) : ℝ :=
  ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j, f (insert u F)

/-- Uniform mean of `f` on the exact `n`-layer. Empty layer is `0`
(`a / 0 = 0` in `ℝ`). -/
def auxFrame_uniformMean (A : Finset ℕ) (n : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  (∑ U ∈ A.powersetCard n, f U) / (A.card.choose n : ℝ)

theorem auxFrame_slotInsertSum_nonneg {A : Finset ℕ} {j : ℕ}
    {f : Finset ℕ → ℝ} (hf : ∀ U, 0 ≤ f U) (F : Finset ℕ) :
    0 ≤ auxFrame_slotInsertSum A j f F :=
  sum_nonneg fun _ _ => hf _

theorem auxFrame_uniformMean_nonneg {A : Finset ℕ} {n : ℕ}
    {f : Finset ℕ → ℝ} (hf : ∀ U, 0 ≤ f U) :
    0 ≤ auxFrame_uniformMean A n f :=
  div_nonneg (sum_nonneg fun _ _ => hf _) (Nat.cast_nonneg _)

/-! ### Exact-layer insert/erase bijection -/

theorem auxFrame_j_lt {n j : ℕ} {B : Finset ℕ} (hj : j + 1 < n)
    (hB : B.card = n) : j < B.card := by
  rw [hB]
  exact Nat.lt_of_succ_lt hj

theorem auxFrame_mem_erase {A B : Finset ℕ} {n j : ℕ} (hBA : B ⊆ A)
    (hB : B.card = n) (hj : j + 1 < n) :
    B.erase (deletedOf B j) ∈ A.powersetCard (n - 1) := by
  have hjB : j < B.card := auxFrame_j_lt hj hB
  have huB : deletedOf B j ∈ B := deletedOf_mem hjB
  refine mem_powersetCard.mpr ⟨(erase_subset _ B).trans hBA, ?_⟩
  rw [card_erase_of_mem huB, hB]

theorem auxFrame_mem_openSlot_erase {A B : Finset ℕ} {j : ℕ}
    (hBA : B ⊆ A) (hpos : ∀ x ∈ A, 0 < x) (hj : j + 1 < B.card) :
    deletedOf B j ∈
      openSlot A ((B.erase (deletedOf B j)).sort (· ≤ ·)) j := by
  have hu := mem_openSlot_of_remainingFrame hBA hpos hj
  rw [← deletedOf_eq_getElem (Nat.lt_of_succ_lt hj)] at hu
  rwa [remainingFrame_eq_erase_sort (Nat.lt_of_succ_lt hj)] at hu

theorem auxFrame_mem_insert {A F : Finset ℕ} {n j u : ℕ} (hn : 1 ≤ n)
    (hFA : F ⊆ A) (hF : F.card = n - 1)
    (hu : u ∈ openSlot A (F.sort (· ≤ ·)) j) :
    insert u F ∈ A.powersetCard n := by
  have huA : u ∈ A := (mem_openSlot.mp hu).1
  have hcard : (insert u F).card = F.card + 1 :=
    card_insert_of_notMem (not_mem_of_mem_openSlot_sort hu)
  refine mem_powersetCard.mpr ⟨insert_subset huA hFA, ?_⟩
  rw [hcard, hF, Nat.sub_add_cancel hn]

/-- Weighted exact-layer bijection for an arbitrary test `f`.
Insert of a slot point / erase of the `j`-th order statistic. -/
theorem auxFrame_preimage_sum {A : Finset ℕ} {n j : ℕ} (f : Finset ℕ → ℝ)
    (hn : 1 ≤ n) (hj : j + 1 < n) (hpos : ∀ x ∈ A, 0 < x) :
    ∑ F ∈ A.powersetCard (n - 1),
        ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j, f (insert u F) =
      ∑ B ∈ A.powersetCard n, f B := by
  set frames := A.powersetCard (n - 1)
  rw [sum_sigma' (s := frames)
    (t := fun F => openSlot A (F.sort (· ≤ ·)) j)
    (f := fun F u => f (insert u F))]
  refine sum_bij'
      (fun p _ => insert p.2 p.1)
      (fun B _ => ⟨B.erase (deletedOf B j), deletedOf B j⟩)
      ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hF := (mem_sigma.mp hp).1
    have hu := (mem_sigma.mp hp).2
    have hFm := mem_powersetCard.mp hF
    exact auxFrame_mem_insert hn hFm.1 hFm.2 hu
  · intro B hB
    have hBm := mem_powersetCard.mp hB
    have hj1 : j + 1 < B.card := by
      rw [hBm.2]
      exact hj
    refine mem_sigma.mpr ⟨?_, ?_⟩
    · exact auxFrame_mem_erase hBm.1 hBm.2 hj
    · exact auxFrame_mem_openSlot_erase hBm.1 hpos hj1
  · intro p hp
    have hu := (mem_sigma.mp hp).2
    have hdel : deletedOf (insert p.2 p.1) j = p.2 :=
      insert_sort_deletedOf_eq hu
    simp [hdel, erase_insert (not_mem_of_mem_openSlot_sort hu)]
  · intro B hB
    have hBm := mem_powersetCard.mp hB
    have hjB : j < B.card := auxFrame_j_lt hj hBm.2
    exact insert_erase (deletedOf_mem hjB)
  · intro p _hp
    rfl

theorem auxFrame_preimage_sum_slot {A : Finset ℕ} {n j : ℕ}
    (f : Finset ℕ → ℝ) (hn : 1 ≤ n) (hj : j + 1 < n)
    (hpos : ∀ x ∈ A, 0 < x) :
    ∑ F ∈ A.powersetCard (n - 1), auxFrame_slotInsertSum A j f F =
      ∑ B ∈ A.powersetCard n, f B :=
  auxFrame_preimage_sum f hn hj hpos

/-! ### Uniform Finset mean -/

/-- Exact uniform mean of `f` on `n`-subsets equals the paper auxiliary
frame mean: coefficient `n/(M−n+1)` times the uniform mean of the
**undivided** slot insert sum on `(n−1)`-subsets. Empty slots contribute
`0`; original fixed-rank weights `|A ∩ W_F|` are not renormalised. -/
theorem auxFrame_uniformMean_eq {A : Finset ℕ} {n j : ℕ} (f : Finset ℕ → ℝ)
    (hn : 1 ≤ n) (hnM : n ≤ A.card) (hj : j + 1 < n)
    (hpos : ∀ x ∈ A, 0 < x) (_hf : ∀ U, 0 ≤ f U) :
    auxFrame_uniformMean A n f =
      (n : ℝ) / ((A.card : ℝ) - n + 1) *
        (1 / (A.card.choose (n - 1) : ℝ)) *
        ∑ F ∈ A.powersetCard (n - 1), auxFrame_slotInsertSum A j f F := by
  unfold auxFrame_uniformMean auxFrame_slotInsertSum
  rw [auxFrame_preimage_sum f hn hj hpos,
    auxFrame_choose_coeff hn hnM, div_eq_mul_one_div, mul_comm]

/-- Expanded form matching the paper display
`E[f(U)] = n/(M−n+1) · E_F Σ_u f(F ∪ {u})`. -/
theorem auxFrame_uniformMean_eq_sum {A : Finset ℕ} {n j : ℕ}
    (f : Finset ℕ → ℝ) (hn : 1 ≤ n) (hnM : n ≤ A.card) (hj : j + 1 < n)
    (hpos : ∀ x ∈ A, 0 < x) (hf : ∀ U, 0 ≤ f U) :
    (∑ U ∈ A.powersetCard n, f U) / (A.card.choose n : ℝ) =
      (n : ℝ) / ((A.card : ℝ) - n + 1) *
        (1 / (A.card.choose (n - 1) : ℝ)) *
        ∑ F ∈ A.powersetCard (n - 1),
          ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j, f (insert u F) := by
  simpa [auxFrame_uniformMean, auxFrame_slotInsertSum] using
    auxFrame_uniformMean_eq f hn hnM hj hpos hf

end

end PrimeGapNormality.Prime
