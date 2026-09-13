import PrimeGapNormality.Prime.SubsetSpacing
import Init.Data.List.Nat.TakeDrop
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort

/-!
# Uniform random deletion: n-extensions and inner gap merge

Paper v0.16 §2 last paragraph (after the uniform auxiliary-frame
identity, which lives on the separate leaf `UniformAuxFrame` and is
not touched here): each `(n−1)`-set in an `M`-carrier has exactly
`M−n+1` one-point n-extensions, and deleting an inner point merges
neighbouring gaps by `g'_i ≤ g_i + g_(i+1)`.

This leaf is only those two finite identities. Order statistics and
gaps are imported from GREEN `SubsetSpacing` (`orderStat`,
`subsetGap`); `SubsetSpacing` is not edited.

Does **not** compile an AC bound, `8^r`, Selberg, Fourier, a kernel,
MixZeta, SingletonLi, `GenericFrameMassEqGeL` on `μ·f`, EndAPI, or
AHLSmall. Unique names `auxDel_`.

**Compiled.**
1. If `F ⊆ A`, `F.card = n−1`, `1 ≤ n ≤ A.card` and `A.card = M`,
   then `#(A \ F) = M − n + 1`.
2. After erasing an inner order statistic `Y_{i+1}`, the new gap at
   rank `i` equals `g_i + g_{i+1}`, hence is `≤` that sum.

**Not compiled.** AC cluster. `8^r` hull. Selberg integration.
Fourier square. Kernel close. MixZeta. SingletonLi.
`GenericFrameMassEqGeL` on `μ·f`. EndAPI. AHLSmall. The uniform
auxiliary-frame mass identity (`UniformAuxFrame`).

**Remaining hyps.** `1 ≤ n ≤ |A|` and `F ⊆ A` of card `n−1` for the
extension count. Inner index `0 < i` and `i+1 < |E|` for the gap
merge. Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `#(A \ F) = M − n + 1` | theorem (`auxDel_extension_card`) |
| inner deletion `g'_i = g_i + g_{i+1}` | theorem (`auxDel_gap_eq_neighbor_sum`) |
| inner deletion `g'_i ≤ g_i + g_{i+1}` | theorem (`auxDel_gap_le_neighbor_sum`) |
| AC / `8^r` / Selberg / Fourier / kernel | not claimed |
| MixZeta / SingletonLi / EndAPI / AHLSmall | not claimed |
| `GenericFrameMassEqGeL` on `μ·f` | not claimed |
| uniform aux-frame identity | not claimed (`UniformAuxFrame`) |

Does not claim the kernel is closed.

Source: `rounds/round119/19_grok_v016_positive_frames_delta.md` §2
last paragraph; v0.16 paper, uniform random deletion.
Contract: API
-/

open Finset

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### n-extensions of an `(n−1)`-subset -/

/-- `M − (n−1) = M − n + 1` once `1 ≤ n ≤ M`. -/
theorem auxDel_nat_sub_pred_eq {M n : ℕ} (hn0 : 1 ≤ n) (hn : n ≤ M) :
    M - (n - 1) = M - n + 1 := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn0
  have hsucc : M + 1 - (n - 1 + 1) = M - (n - 1) :=
    Nat.succ_sub_succ_eq_sub M (n - 1)
  have hcomm : M + 1 - n = M - n + 1 := Nat.sub_add_comm hn
  calc
    M - (n - 1) = M + 1 - (n - 1 + 1) := hsucc.symm
    _ = M + 1 - n := by rw [hn1]
    _ = M - n + 1 := hcomm

/-- Each `(n−1)`-subset `F ⊆ A` has exactly `M − n + 1` one-point
n-extensions: the unused carrier points `A \ F`. -/
theorem auxDel_extension_card {A F : Finset ℕ} {n M : ℕ}
    (hM : A.card = M) (hF : F ⊆ A) (hFn : F.card = n - 1)
    (hn0 : 1 ≤ n) (hn : n ≤ A.card) :
    (A \ F).card = M - n + 1 := by
  have hnM : n ≤ M := by rw [← hM]; exact hn
  have hs : (A \ F).card = M - F.card := by
    rw [← hM]
    exact card_sdiff_of_subset hF
  rw [hs, hFn]
  exact auxDel_nat_sub_pred_eq hn0 hnM

/-! ### Sorted list after erasing an order statistic -/

theorem auxDel_orderStat_mem {E : Finset ℕ} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ E.card) : orderStat E k ∈ E := by
  have hget := orderStat_pos_eq_sort hk0 hk
  have hlen : (E.sort (· ≤ ·)).length = E.card := length_sort _
  have hk' : k - 1 < (E.sort (· ≤ ·)).length := by
    rw [hlen]
    exact Nat.lt_of_lt_of_le (Nat.sub_lt hk0 Nat.zero_lt_one) hk
  have hmem : (E.sort (· ≤ ·))[k - 1]'hk' ∈ E.sort (· ≤ ·) :=
    List.getElem_mem hk'
  rw [hget]
  exact (mem_sort (· ≤ ·)).mp hmem

theorem auxDel_getElem_eraseIdx_pred {l : List ℕ} {i : ℕ}
    (hi : i < l.length) (hi0 : 0 < i)
    (h : i - 1 < (l.eraseIdx i).length) :
    (l.eraseIdx i)[i - 1] = l[i - 1] := by
  have heq : l.eraseIdx i = l.take i ++ l.drop (i + 1) :=
    List.eraseIdx_eq_take_drop_succ l i
  have hlenTake : (l.take i).length = i :=
    List.length_take_of_le (Nat.le_of_lt hi)
  have hj : i - 1 < (l.take i).length := by
    rw [hlenTake]
    exact Nat.sub_lt hi0 Nat.zero_lt_one
  have hj' : i - 1 < i := Nat.sub_lt hi0 Nat.zero_lt_one
  have hiPred : i - 1 < l.length := Nat.lt_trans hj' hi
  rw [List.getElem_eq_iff]
  rw [heq, List.getElem?_append_left hj, List.getElem?_take, if_pos hj']
  exact (List.getElem_eq_iff hiPred).mp rfl

theorem auxDel_getElem_eraseIdx_at {l : List ℕ} {i : ℕ}
    (hi : i < l.length) (hi1 : i + 1 < l.length)
    (h : i < (l.eraseIdx i).length) :
    (l.eraseIdx i)[i] = l[i + 1] := by
  have heq : l.eraseIdx i = l.take i ++ l.drop (i + 1) :=
    List.eraseIdx_eq_take_drop_succ l i
  have hlenTake : (l.take i).length = i :=
    List.length_take_of_le (Nat.le_of_lt hi)
  have hle : (l.take i).length ≤ i := Nat.le_of_eq hlenTake
  have hidx : i - (l.take i).length = 0 := by
    rw [hlenTake, Nat.sub_self]
  rw [List.getElem_eq_iff]
  rw [heq, List.getElem?_append_right hle, hidx, List.getElem?_drop]
  exact (List.getElem_eq_iff hi1).mp rfl

theorem auxDel_mem_eraseIdx_iff {E : Finset ℕ} {i a : ℕ}
    (hi : i < E.card) :
    a ∈ (E.sort (· ≤ ·)).eraseIdx i ↔
      a ∈ E.erase (orderStat E (i + 1)) := by
  set l := E.sort (· ≤ ·)
  have hlen : l.length = E.card := length_sort _
  have hi' : i < l.length := by rw [hlen]; exact hi
  have hy : orderStat E (i + 1) = l[i]'hi' :=
    orderStat_succ_eq_sort hi
  have hnd : l.Nodup := sort_nodup (s := E) (r := (· ≤ ·))
  have hdrop : l.drop i = l[i]'hi' :: l.drop (i + 1) :=
    List.drop_eq_getElem_cons hi'
  have happNd : (l.take i ++ l.drop i).Nodup := by
    rw [List.take_append_drop]
    exact hnd
  have hdisj : ∀ x ∈ l.take i, ∀ z ∈ l.drop i, x ≠ z :=
    (List.nodup_append.mp happNd).2.2
  have hyDrop : l[i]'hi' ∈ l.drop i := by
    rw [hdrop]
    exact List.mem_cons_self
  have hyNotTake : l[i]'hi' ∉ l.take i := fun ht =>
    (hdisj _ ht _ hyDrop rfl)
  have hyNotTail : l[i]'hi' ∉ l.drop (i + 1) := by
    have hndDrop : (l.drop i).Nodup :=
      hnd.sublist (List.drop_sublist i l)
    have hndCons : (l[i]'hi' :: l.drop (i + 1)).Nodup := by
      rw [← hdrop]
      exact hndDrop
    exact (List.nodup_cons.mp hndCons).1
  constructor
  · intro ha
    rw [List.eraseIdx_eq_take_drop_succ, List.mem_append] at ha
    rw [hy]
    refine mem_erase.mpr ⟨?_, (mem_sort (· ≤ ·)).mp ?_⟩
    · intro hay
      rcases ha with htake | htl
      · exact hyNotTake (hay ▸ htake)
      · exact hyNotTail (hay ▸ htl)
    · rcases ha with htake | htl
      · exact List.take_subset i l htake
      · exact List.drop_subset (i + 1) l htl
  · intro ha
    rw [hy] at ha
    have hae := mem_erase.mp ha
    have hal : a ∈ l := (mem_sort (· ≤ ·)).mpr hae.2
    have hl : l = l.take i ++ l[i]'hi' :: l.drop (i + 1) := by
      calc
        l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
        _ = l.take i ++ l[i]'hi' :: l.drop (i + 1) := by rw [hdrop]
    have hmem : a ∈ l.take i ++ l[i]'hi' :: l.drop (i + 1) := by
      rw [← hl]
      exact hal
    rw [List.eraseIdx_eq_take_drop_succ, List.mem_append]
    rw [List.mem_append, List.mem_cons] at hmem
    rcases hmem with htake | hy' | htl
    · exact Or.inl htake
    · exact (hae.1 hy').elim
    · exact Or.inr htl

theorem auxDel_sort_erase {E : Finset ℕ} {i : ℕ} (hi : i < E.card) :
    ((E.erase (orderStat E (i + 1))).sort (· ≤ ·)) =
      (E.sort (· ≤ ·)).eraseIdx i := by
  refine
    (sortedLT_sort (E.erase (orderStat E (i + 1)))).eq_of_mem_iff
      ((sortedLT_sort E).pairwise.eraseIdx i).sortedLT ?_
  intro a
  rw [mem_sort]
  exact (auxDel_mem_eraseIdx_iff hi).symm

/-! ### Order statistics after inner deletion -/

theorem auxDel_erase_card {E : Finset ℕ} {i : ℕ} (hi : i < E.card) :
    (E.erase (orderStat E (i + 1))).card = E.card - 1 := by
  have hmem : orderStat E (i + 1) ∈ E :=
    auxDel_orderStat_mem (Nat.succ_pos i) (Nat.succ_le_of_lt hi)
  exact card_erase_of_mem hmem

theorem auxDel_orderStat_erase_self {E : Finset ℕ} {i : ℕ}
    (hi0 : 0 < i) (hi : i + 1 < E.card) :
    orderStat (E.erase (orderStat E (i + 1))) i = orderStat E i := by
  have hiE : i < E.card := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hcard : (E.erase (orderStat E (i + 1))).card = E.card - 1 :=
    auxDel_erase_card hiE
  have hiLe : i ≤ (E.erase (orderStat E (i + 1))).card := by
    rw [hcard]
    exact Nat.le_of_lt (Nat.lt_sub_of_add_lt hi)
  have hget :=
    orderStat_pos_eq_sort (E := E.erase (orderStat E (i + 1))) hi0 hiLe
  have hgetE := orderStat_pos_eq_sort (E := E) hi0 (Nat.le_of_lt hiE)
  have hsort := auxDel_sort_erase (E := E) (i := i) hiE
  have hlen : (E.sort (· ≤ ·)).length = E.card := length_sort _
  have hiL : i < (E.sort (· ≤ ·)).length := by rw [hlen]; exact hiE
  have hpredLen :
      i - 1 <
        ((E.erase (orderStat E (i + 1))).sort (· ≤ ·)).length := by
    rw [length_sort, hcard]
    exact Nat.pred_lt_pred (Nat.ne_of_gt hi0) hiE
  have hpred :
      i - 1 < ((E.sort (· ≤ ·)).eraseIdx i).length := by
    rw [← hsort]
    exact hpredLen
  have hidx :=
    auxDel_getElem_eraseIdx_pred (l := E.sort (· ≤ ·)) hiL hi0 hpred
  calc
    orderStat (E.erase (orderStat E (i + 1))) i =
        ((E.erase (orderStat E (i + 1))).sort (· ≤ ·))[i - 1]'hpredLen :=
      hget
    _ = ((E.sort (· ≤ ·)).eraseIdx i)[i - 1]'(hsort ▸ hpredLen) :=
      List.getElem_of_eq hsort hpredLen
    _ = (E.sort (· ≤ ·))[i - 1] := hidx
    _ = orderStat E i := hgetE.symm

theorem auxDel_orderStat_erase_succ {E : Finset ℕ} {i : ℕ}
    (hi : i + 1 < E.card) :
    orderStat (E.erase (orderStat E (i + 1))) (i + 1) =
      orderStat E (i + 2) := by
  have hiE : i < E.card := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hcard : (E.erase (orderStat E (i + 1))).card = E.card - 1 :=
    auxDel_erase_card hiE
  have hi' : i < (E.erase (orderStat E (i + 1))).card := by
    rw [hcard]
    exact Nat.lt_sub_of_add_lt hi
  have hget :=
    orderStat_succ_eq_sort (E := E.erase (orderStat E (i + 1))) hi'
  have hgetE := orderStat_succ_eq_sort (E := E) (i := i + 1) hi
  have hsort := auxDel_sort_erase (E := E) (i := i) hiE
  have hlen : (E.sort (· ≤ ·)).length = E.card := length_sort _
  have hiL : i < (E.sort (· ≤ ·)).length := by rw [hlen]; exact hiE
  have hi1L : i + 1 < (E.sort (· ≤ ·)).length := by rw [hlen]; exact hi
  have hidxLen :
      i < ((E.erase (orderStat E (i + 1))).sort (· ≤ ·)).length := by
    rw [length_sort]
    exact hi'
  have hidxErase : i < ((E.sort (· ≤ ·)).eraseIdx i).length :=
    hsort ▸ hidxLen
  have hidx :=
    auxDel_getElem_eraseIdx_at (l := E.sort (· ≤ ·)) hiL hi1L hidxErase
  calc
    orderStat (E.erase (orderStat E (i + 1))) (i + 1) =
        ((E.erase (orderStat E (i + 1))).sort (· ≤ ·))[i]'hidxLen :=
      hget
    _ = ((E.sort (· ≤ ·)).eraseIdx i)[i]'(hsort ▸ hidxLen) :=
      List.getElem_of_eq hsort hidxLen
    _ = (E.sort (· ≤ ·))[i + 1] := hidx
    _ = orderStat E (i + 2) := hgetE.symm

theorem auxDel_orderStat_le_succ {E : Finset ℕ} {k : ℕ}
    (hk : k < E.card) :
    orderStat E k ≤ orderStat E (k + 1) := by
  have hsorted := sortedLT_sort E
  have hlen : (E.sort (· ≤ ·)).length = E.card := length_sort _
  have hk' : k < (E.sort (· ≤ ·)).length := by rw [hlen]; exact hk
  rw [orderStat_succ_eq_sort hk]
  by_cases hk0 : k = 0
  · subst hk0
    simp [orderStat]
  · have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
    have hget := orderStat_pos_eq_sort hk0' (Nat.le_of_lt hk)
    have hpred : k - 1 < (E.sort (· ≤ ·)).length := by
      rw [hlen]
      exact Nat.lt_trans (Nat.sub_lt hk0' Nat.zero_lt_one) hk
    have hlt :=
      hsorted.getElem_lt_getElem_of_lt (hi := hpred) (hj := hk')
        (Nat.sub_lt hk0' Nat.zero_lt_one)
    simpa [hget] using Nat.le_of_lt hlt

/-- If `a ≤ b ≤ c` then `c − a = (b − a) + (c − b)` in `ℕ`. -/
theorem auxDel_tsub_add {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    c - a = b - a + (c - b) := by
  calc
    c - a = c - b + b - a := by rw [Nat.sub_add_cancel hbc]
    _ = c - b + (b - a) := Nat.add_sub_assoc hab (c - b)
    _ = b - a + (c - b) := Nat.add_comm _ _

/-! ### Inner gap merge `g'_i ≤ g_i + g_(i+1)` -/

/-- Deleting the inner point `Y_{i+1}` merges the two neighbouring
gaps with equality. Adjacent ranks add; they do not overshoot. -/
theorem auxDel_gap_eq_neighbor_sum {E : Finset ℕ} {i : ℕ}
    (hi0 : 0 < i) (hi : i + 1 < E.card) :
    subsetGap (E.erase (orderStat E (i + 1))) i =
      subsetGap E i + subsetGap E (i + 1) := by
  have hiE : i < E.card := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hleft := auxDel_orderStat_erase_self hi0 hi
  have hright := auxDel_orderStat_erase_succ hi
  have hle₁ : orderStat E i ≤ orderStat E (i + 1) :=
    auxDel_orderStat_le_succ hiE
  have hle₂ : orderStat E (i + 1) ≤ orderStat E (i + 2) :=
    auxDel_orderStat_le_succ hi
  unfold subsetGap
  rw [hleft, hright]
  exact auxDel_tsub_add hle₁ hle₂

/-- Pointwise coupling after inner deletion:
`g'_i ≤ g_i + g_(i+1)`. -/
theorem auxDel_gap_le_neighbor_sum {E : Finset ℕ} {i : ℕ}
    (hi0 : 0 < i) (hi : i + 1 < E.card) :
    subsetGap (E.erase (orderStat E (i + 1))) i ≤
      subsetGap E i + subsetGap E (i + 1) :=
  Nat.le_of_eq (auxDel_gap_eq_neighbor_sum hi0 hi)

end

end PrimeGapNormality.Prime
