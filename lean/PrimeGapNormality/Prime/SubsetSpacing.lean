import PrimeGapNormality.Prime.CardinalitySymInterface
import PrimeGapNormality.Prime.CompleteFrameMass
import PrimeGapNormality.Prime.SlotResample
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# v0.6 — uniform subset spacings and generic frame weights

Uniform n-subsets of `{1,…,M}`: ordered ranks `Y_0 = 0 < Y_1 < ⋯ < Y_n`,
gaps `D_i = Y_{i+1} - Y_i`. Paper `eq:subsetspacing`. Do not replace
the rooted first gap or the last needed rank by a sentinel zero hole.
`n = 0` is not used in a spacing lemma. For `q > M` the binomial
numerator saturates at 0 because `n ≥ 1`.

Generic frame masses reuse the existing deletion/insertion bijection
in `CompleteFrameMass` with an arbitrary weight `μ`. Bernoulli is the
special case already proved. Rank convention: paper `1 ≤ j < L` is
Lean `j + 1 < L`. Sum over **all** complete frames, not only
`|F| = L-1`.

Do not import `ActualRootLaw` (name clash on `bernoulliThin`).

Source: `rounds/round108/05_paper_v0_6.tex` `eq:subsetspacing` and
complete frames; `06_grok_exact_symmetry_and_st_delta.md` §2.3–§3.
Contract: API
Audit: GREEN
-/

open Finset

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- Rank universe `{1,…,M}`. -/
def rankUniverse (M : ℕ) : Finset ℕ :=
  Icc 1 M

/-- Uniform n-subsets of `{1,…,M}`. -/
def uniformNSubsets (M n : ℕ) : Finset (Finset ℕ) :=
  (rankUniverse M).powerset.filter (fun E => E.card = n)

/-- Order statistic with `Y_0 = 0`. For `i ≥ 1`, `Y_i` is the
`(i-1)`-st entry of the increasing sort. -/
noncomputable def orderStat (E : Finset ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 0
  else if h : i - 1 < E.card then
    (E.sort (· ≤ ·))[i - 1]'(by simpa [length_sort] using h)
  else 0

/-- Rank gap `D_i = Y_{i+1} - Y_i` for `0 ≤ i < n`. -/
noncomputable def subsetGap (E : Finset ℕ) (i : ℕ) : ℕ :=
  orderStat E (i + 1) - orderStat E i

/-- `Pr(D_i > q)` under the uniform n-subset law. Empty family has
mass 0 (no `0/0`). -/
noncomputable def subsetSpacingProbGt (M n i q : ℕ) : ℝ :=
  let s := uniformNSubsets M n
  if s.card = 0 then 0
  else ((s.filter (fun E => q < subsetGap E i)).card : ℝ) / (s.card : ℝ)

/-- Occupancy-weighted frame mass for a cardinality-symmetric law:
`|openSlot| * p_{|F|+1} / binom(M, |F|+1)`. Empty slot is 0. -/
noncomputable def genericFrameMass (A : Finset ℕ) (μ : Finset ℕ → ℝ)
    (F : Finset ℕ) (j : ℕ) : ℝ :=
  ((openSlot A (F.sort (· ≤ ·)) j).card : ℝ) *
    uniformLayerWeight A μ (F.card + 1)

/-- Subtract `q` from every point strictly after the `i`-th order
statistic; points at or before the threshold are unchanged. -/
def compressAfter (t q x : ℕ) : ℕ :=
  if x ≤ t then x else x - q

/-- Inverse of `compressAfter`. -/
def expandAfter (t q x : ℕ) : ℕ :=
  if x ≤ t then x else x + q

/-! ### Uniform n-subsets and order statistics -/

theorem rankUniverse_card (M : ℕ) : (rankUniverse M).card = M := by
  simp [rankUniverse, Nat.card_Icc]

theorem uniformNSubsets_eq_powersetCard (M n : ℕ) :
    uniformNSubsets M n = (rankUniverse M).powersetCard n :=
  (powersetCard_eq_filter).symm

theorem uniformNSubsets_card (M n : ℕ) :
    (uniformNSubsets M n).card = Nat.choose M n := by
  rw [uniformNSubsets_eq_powersetCard, card_powersetCard, rankUniverse_card]

theorem mem_uniformNSubsets {M n : ℕ} {E : Finset ℕ} :
    E ∈ uniformNSubsets M n ↔ E ⊆ rankUniverse M ∧ E.card = n := by
  simp [uniformNSubsets, mem_filter, mem_powerset]

theorem mem_rankUniverse {M x : ℕ} :
    x ∈ rankUniverse M ↔ 1 ≤ x ∧ x ≤ M :=
  mem_Icc

theorem orderStat_zero (E : Finset ℕ) : orderStat E 0 = 0 :=
  rfl

theorem orderStat_pos_eq_sort {E : Finset ℕ} {i : ℕ} (hi0 : 0 < i)
    (hi : i ≤ E.card) :
    orderStat E i =
      (E.sort (· ≤ ·))[i - 1]'(by
        rw [length_sort]
        omega) := by
  unfold orderStat
  rw [if_neg (Nat.ne_of_gt hi0), dif_pos (by omega)]

theorem orderStat_succ_eq_sort {E : Finset ℕ} {i : ℕ} (hi : i < E.card) :
    orderStat E (i + 1) =
      (E.sort (· ≤ ·))[i]'(by simpa [length_sort] using hi) := by
  have hi0 : 0 < i + 1 := Nat.succ_pos i
  have hle : i + 1 ≤ E.card := Nat.succ_le_of_lt hi
  simpa [Nat.add_sub_cancel] using orderStat_pos_eq_sort hi0 hle

theorem subsetGap_eq_sort_sub {E : Finset ℕ} {i : ℕ} (hi : i < E.card) :
    subsetGap E i =
      (E.sort (· ≤ ·))[i]'(by simpa [length_sort] using hi) -
        orderStat E i := by
  unfold subsetGap
  rw [orderStat_succ_eq_sort hi]

theorem pos_of_mem_rankUniverse {M x : ℕ} (hx : x ∈ rankUniverse M) :
    0 < x :=
  Nat.succ_le_iff.mp (mem_rankUniverse.mp hx).1

theorem pos_of_subset_rankUniverse {M : ℕ} {E : Finset ℕ}
    (hE : E ⊆ rankUniverse M) {x : ℕ} (hx : x ∈ E) : 0 < x :=
  pos_of_mem_rankUniverse (hE hx)

theorem lt_sort_get_orderStat {E : Finset ℕ} {i : ℕ} (hi : i < E.card)
    (hpos : ∀ x ∈ E, 0 < x) :
    orderStat E i <
      (E.sort (· ≤ ·))[i]'(by simpa [length_sort] using hi) := by
  have hlen : (E.sort (· ≤ ·)).length = E.card := length_sort _
  have hi' : i < (E.sort (· ≤ ·)).length := by simpa [hlen] using hi
  have hsorted : (E.sort (· ≤ ·)).SortedLT := sortedLT_sort E
  by_cases hi0 : i = 0
  · subst hi0
    simp [orderStat]
    exact hpos _ ((mem_sort (· ≤ ·)).mp (List.getElem_mem hi'))
  · have hi0' : 0 < i := Nat.pos_of_ne_zero hi0
    have ht := orderStat_pos_eq_sort hi0' (Nat.le_of_lt hi)
    have hidx : i - 1 < i := Nat.sub_lt hi0' Nat.zero_lt_one
    have hi1 : i - 1 < (E.sort (· ≤ ·)).length := by omega
    have hlt := (hsorted.getElem_lt_getElem_iff (hi := hi1) (hj := hi')).mpr hidx
    simpa [ht] using hlt

theorem take_le_orderStat {E : Finset ℕ} {i : ℕ} (hi : i < E.card) :
    ∀ x ∈ (E.sort (· ≤ ·)).take i, x ≤ orderStat E i := by
  intro x hx
  set l := E.sort (· ≤ ·)
  have hlen : l.length = E.card := length_sort _
  obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp hx
  have hklt : k < i := (Nat.lt_min.mp hk).1
  have hklen : k < l.length := (Nat.lt_min.mp hk).2
  have hsorted : l.SortedLT := sortedLT_sort E
  by_cases hi0 : i = 0
  · subst hi0
    exact (Nat.not_lt_zero k hklt).elim
  · have hi0' : 0 < i := Nat.pos_of_ne_zero hi0
    have ht := orderStat_pos_eq_sort hi0' (Nat.le_of_lt hi)
    have hki : k ≤ i - 1 := by omega
    have hi1 : i - 1 < l.length := by omega
    have hle := (hsorted.getElem_le_getElem_iff (hi := hklen) (hj := hi1)).mpr hki
    simpa [l, ht] using hle

theorem drop_gt_orderStat {E : Finset ℕ} {i : ℕ} (hi : i < E.card)
    (hpos : ∀ x ∈ E, 0 < x) :
    ∀ x ∈ (E.sort (· ≤ ·)).drop i, orderStat E i < x := by
  intro x hx
  set l := E.sort (· ≤ ·)
  have hlen : l.length = E.card := length_sort _
  obtain ⟨k, hk, rfl⟩ := List.mem_drop_iff_getElem.mp hx
  have hklen : i + k < l.length := by
    have hmin : min i l.length = i := Nat.min_eq_left (by omega)
    omega
  have hsorted : l.SortedLT := sortedLT_sort E
  have hi' : i < l.length := by simpa [hlen] using hi
  have hlt_next := lt_sort_get_orderStat hi hpos
  have hle : l[i]'hi' ≤ l[i + k]'hklen :=
    (hsorted.getElem_le_getElem_iff (hi := hi') (hj := hklen)).mpr (Nat.le_add_right i k)
  exact lt_of_lt_of_le hlt_next hle

theorem lt_add_q_sort_get {E : Finset ℕ} {i q : ℕ} (hi : i < E.card)
    (hpos : ∀ x ∈ E, 0 < x) (hg : q < subsetGap E i) :
    orderStat E i + q <
      (E.sort (· ≤ ·))[i]'(by simpa [length_sort] using hi) := by
  have hgap := subsetGap_eq_sort_sub (E := E) (i := i) hi
  have hlt := lt_sort_get_orderStat (E := E) (i := i) hi hpos
  have hle : orderStat E i ≤
      (E.sort (· ≤ ·))[i]'(by simpa [length_sort] using hi) :=
    Nat.le_of_lt hlt
  have hg' : q <
      (E.sort (· ≤ ·))[i]'(by simpa [length_sort] using hi) - orderStat E i := by
    simpa [hgap] using hg
  have h := Nat.add_lt_add_right hg' (orderStat E i)
  have hsub := Nat.sub_add_cancel hle
  have hcomm :
      q + orderStat E i <
        (E.sort (· ≤ ·))[i]'(by simpa [length_sort] using hi) -
            orderStat E i + orderStat E i := h
  simpa [Nat.add_comm, hsub] using hcomm

private theorem mem_drop_of_gt_orderStat {E : Finset ℕ} {i x : ℕ}
    (hi : i < E.card) (hx : x ∈ E) (hgt : orderStat E i < x) :
    x ∈ (E.sort (· ≤ ·)).drop i := by
  have hxL : x ∈ E.sort (· ≤ ·) := (mem_sort (· ≤ ·)).mpr hx
  have hsplit :
      x ∈ (E.sort (· ≤ ·)).take i ++ (E.sort (· ≤ ·)).drop i := by
    simpa [List.take_append_drop] using hxL
  exact (List.mem_append.mp hsplit).resolve_left fun htake =>
    (not_le_of_gt hgt) (take_le_orderStat hi x htake)

private theorem add_q_lt_of_mem_drop {E : Finset ℕ} {i q x : ℕ}
    (hi : i < E.card) (hpos : ∀ z ∈ E, 0 < z) (hg : q < subsetGap E i)
    (hx : x ∈ (E.sort (· ≤ ·)).drop i) :
    orderStat E i + q < x := by
  have hnext := lt_add_q_sort_get hi hpos hg
  have hlen : (E.sort (· ≤ ·)).length = E.card := length_sort _
  obtain ⟨k, hk, rfl⟩ := List.mem_drop_iff_getElem.mp hx
  have hklen : i + k < (E.sort (· ≤ ·)).length := by
    have : min i (E.sort (· ≤ ·)).length = i := Nat.min_eq_left (by omega)
    omega
  have hsorted : (E.sort (· ≤ ·)).SortedLT := sortedLT_sort E
  have hi' : i < (E.sort (· ≤ ·)).length := by simpa [hlen] using hi
  have hle :=
    (hsorted.getElem_le_getElem_iff (hi := hi') (hj := hklen)).mpr
      (Nat.le_add_right i k)
  exact lt_of_lt_of_le hnext hle

/-! ### Compression / expansion on a gap -/

private theorem map_compress_eq_take_drop {E : Finset ℕ} {i q : ℕ}
    (hi : i < E.card) (hpos : ∀ x ∈ E, 0 < x) :
    (E.sort (· ≤ ·)).map (compressAfter (orderStat E i) q) =
      (E.sort (· ≤ ·)).take i ++
        ((E.sort (· ≤ ·)).drop i).map (fun x => x - q) := by
  set l := E.sort (· ≤ ·)
  have ht : l.take i ++ l.drop i = l := List.take_append_drop i l
  nth_rw 1 [← ht]
  rw [List.map_append]
  congr 1
  · refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
    intro x hx
    have hxle := take_le_orderStat hi x hx
    simp [compressAfter, hxle]
  · refine List.map_congr_left ?_
    intro x hx
    have hxgt := drop_gt_orderStat hi hpos x hx
    have hnot : ¬ x ≤ orderStat E i := Nat.not_le.mpr hxgt
    simp [compressAfter, hnot]

private theorem map_expand_eq_take_drop {F : Finset ℕ} {i q : ℕ}
    (hi : i < F.card) (hpos : ∀ x ∈ F, 0 < x) :
    (F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q) =
      (F.sort (· ≤ ·)).take i ++
        ((F.sort (· ≤ ·)).drop i).map (fun x => x + q) := by
  set l := F.sort (· ≤ ·)
  have ht : l.take i ++ l.drop i = l := List.take_append_drop i l
  nth_rw 1 [← ht]
  rw [List.map_append]
  congr 1
  · refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
    intro x hx
    have hxle := take_le_orderStat hi x hx
    simp [expandAfter, hxle]
  · refine List.map_congr_left ?_
    intro x hx
    have hxgt := drop_gt_orderStat hi hpos x hx
    have hnot : ¬ x ≤ orderStat F i := Nat.not_le.mpr hxgt
    simp [expandAfter, hnot]

private theorem q_le_drop_of_gap {E : Finset ℕ} {i q : ℕ} (hi : i < E.card)
    (hpos : ∀ x ∈ E, 0 < x) (hg : q < subsetGap E i)
    {x : ℕ} (hx : x ∈ (E.sort (· ≤ ·)).drop i) : q ≤ x := by
  have := add_q_lt_of_mem_drop hi hpos hg hx
  omega

private theorem pairwise_shift_sub {E : Finset ℕ} {i q : ℕ} (hi : i < E.card)
    (hpos : ∀ x ∈ E, 0 < x) (hg : q < subsetGap E i) :
    ((E.sort (· ≤ ·)).map (compressAfter (orderStat E i) q)).Pairwise
      (· < ·) := by
  rw [map_compress_eq_take_drop hi hpos, List.pairwise_append]
  set l := E.sort (· ≤ ·)
  have hpw : l.Pairwise (· < ·) := sort_pairwise_lt E
  refine ⟨List.Pairwise.take (l := l) (i := i) hpw, ?_, ?_⟩
  · have hdrop := List.Pairwise.drop (l := l) (i := i) hpw
    rw [List.pairwise_iff_getElem] at hdrop ⊢
    intro a b ha hb hab
    have ha' : a < (l.drop i).length := by simpa using ha
    have hb' : b < (l.drop i).length := by simpa using hb
    have hlt : (l.drop i)[a]'ha' < (l.drop i)[b]'hb' := hdrop a b ha' hb' hab
    have hqa : q ≤ (l.drop i)[a]'ha' :=
      q_le_drop_of_gap hi hpos hg (List.getElem_mem ha')
    have hqb : q ≤ (l.drop i)[b]'hb' :=
      q_le_drop_of_gap hi hpos hg (List.getElem_mem hb')
    have : (l.drop i)[a]'ha' - q < (l.drop i)[b]'hb' - q :=
      Nat.sub_lt_sub_right hqa hlt
    simpa using this
  · intro a ha b hb
    have hale := take_le_orderStat hi a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
    have htq := add_q_lt_of_mem_drop hi hpos hg ht
    omega

private theorem pairwise_shift_add {F : Finset ℕ} {i q : ℕ} (hi : i < F.card)
    (hpos : ∀ x ∈ F, 0 < x) :
    ((F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q)).Pairwise
      (· < ·) := by
  rw [map_expand_eq_take_drop hi hpos, List.pairwise_append]
  set l := F.sort (· ≤ ·)
  have hpw : l.Pairwise (· < ·) := sort_pairwise_lt F
  refine ⟨List.Pairwise.take (l := l) (i := i) hpw, ?_, ?_⟩
  · have hdrop := List.Pairwise.drop (l := l) (i := i) hpw
    rw [List.pairwise_iff_getElem] at hdrop ⊢
    intro a b ha hb hab
    have ha' : a < (l.drop i).length := by simpa using ha
    have hb' : b < (l.drop i).length := by simpa using hb
    have hlt : (l.drop i)[a]'ha' < (l.drop i)[b]'hb' := hdrop a b ha' hb' hab
    simpa using Nat.add_lt_add_right hlt q
  · intro a ha b hb
    obtain ⟨t, ht, hb'⟩ := List.mem_map.mp hb
    have hale := take_le_orderStat hi a ha
    have hbgt := drop_gt_orderStat hi hpos t ht
    have : a < t + q := by omega
    simpa [hb'] using this

private theorem compress_injOn {E : Finset ℕ} {i q : ℕ} (hi : i < E.card)
    (hpos : ∀ x ∈ E, 0 < x) (hg : q < subsetGap E i) :
    Set.InjOn (compressAfter (orderStat E i) q) (E : Set ℕ) := by
  intro x hx y hy hxy
  set t := orderStat E i
  wlog hle : x ≤ y generalizing x y
  · exact Eq.symm
      (this (x := y) (y := x) hy hx hxy.symm (le_of_not_ge hle))
  have hxE : x ∈ E := hx
  have hyE : y ∈ E := hy
  by_cases hy_le : y ≤ t
  · have hx_le : x ≤ t := le_trans hle hy_le
    simpa [compressAfter, hx_le, hy_le] using hxy
  · have hygt : t < y := Nat.not_le.mp hy_le
    have hydrop := mem_drop_of_gt_orderStat hi hyE hygt
    have hyq := add_q_lt_of_mem_drop hi hpos hg hydrop
    by_cases hx_le : x ≤ t
    · have hx' : compressAfter t q x = x := by simp [compressAfter, hx_le]
      have hy' : compressAfter t q y = y - q := by simp [compressAfter, hy_le]
      have heq : x = y - q := by simpa [hx', hy'] using hxy
      omega
    · have hxgt : t < x := Nat.not_le.mp hx_le
      have hx' : compressAfter t q x = x - q := by simp [compressAfter, hx_le]
      have hy' : compressAfter t q y = y - q := by simp [compressAfter, hy_le]
      have heq : x - q = y - q := by simpa [hx', hy'] using hxy
      have hxdrop := mem_drop_of_gt_orderStat hi hxE hxgt
      have hxq := q_le_drop_of_gap hi hpos hg hxdrop
      omega

private theorem expand_injOn {F : Finset ℕ} {i q : ℕ} (hi : i < F.card)
    (hpos : ∀ x ∈ F, 0 < x) :
    Set.InjOn (expandAfter (orderStat F i) q) (F : Set ℕ) := by
  intro x hx y hy hxy
  set t := orderStat F i
  wlog hle : x ≤ y generalizing x y
  · exact Eq.symm
      (this (x := y) (y := x) hy hx hxy.symm (le_of_not_ge hle))
  by_cases hy_le : y ≤ t
  · have hx_le : x ≤ t := le_trans hle hy_le
    simpa [expandAfter, hx_le, hy_le] using hxy
  · have hygt : t < y := Nat.not_le.mp hy_le
    by_cases hx_le : x ≤ t
    · have : x = y + q := by
        simpa [expandAfter, hx_le, hy_le] using hxy
      omega
    · have : x + q = y + q := by
        simpa [expandAfter, hx_le, hy_le] using hxy
      omega

private theorem mem_map_compress {E : Finset ℕ} {i q y : ℕ}
    (hi : i < E.card) (hpos : ∀ x ∈ E, 0 < x) :
    y ∈ (E.sort (· ≤ ·)).map (compressAfter (orderStat E i) q) ↔
      y ∈ E.image (compressAfter (orderStat E i) q) := by
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact mem_image.mpr ⟨x, (mem_sort (· ≤ ·)).mp hx, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact List.mem_map.mpr ⟨x, (mem_sort (· ≤ ·)).mpr hx, rfl⟩

private theorem mem_map_expand {F : Finset ℕ} {i q y : ℕ}
    (hi : i < F.card) (hpos : ∀ x ∈ F, 0 < x) :
    y ∈ (F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q) ↔
      y ∈ F.image (expandAfter (orderStat F i) q) := by
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact mem_image.mpr ⟨x, (mem_sort (· ≤ ·)).mp hx, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact List.mem_map.mpr ⟨x, (mem_sort (· ≤ ·)).mpr hx, rfl⟩

private theorem sort_image_compress {E : Finset ℕ} {i q : ℕ} (hi : i < E.card)
    (hpos : ∀ x ∈ E, 0 < x) (hg : q < subsetGap E i) :
    (E.image (compressAfter (orderStat E i) q)).sort (· ≤ ·) =
      (E.sort (· ≤ ·)).map (compressAfter (orderStat E i) q) := by
  set l := (E.sort (· ≤ ·)).map (compressAfter (orderStat E i) q)
  have hpw := pairwise_shift_sub hi hpos hg
  have hsorted_l : l.SortedLT := hpw.sortedLT
  have hsorted_s :
      ((E.image (compressAfter (orderStat E i) q)).sort (· ≤ ·)).SortedLT :=
    sortedLT_sort _
  refine hsorted_s.eq_of_mem_iff hsorted_l ?_
  intro y
  rw [mem_sort, mem_map_compress hi hpos]

private theorem sort_image_expand {F : Finset ℕ} {i q : ℕ} (hi : i < F.card)
    (hpos : ∀ x ∈ F, 0 < x) :
    (F.image (expandAfter (orderStat F i) q)).sort (· ≤ ·) =
      (F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q) := by
  set l := (F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q)
  have hpw := pairwise_shift_add (q := q) hi hpos
  have hsorted_l : l.SortedLT := hpw.sortedLT
  have hsorted_s :
      ((F.image (expandAfter (orderStat F i) q)).sort (· ≤ ·)).SortedLT :=
    sortedLT_sort _
  refine hsorted_s.eq_of_mem_iff hsorted_l ?_
  intro y
  rw [mem_sort, mem_map_expand hi hpos]

private theorem orderStat_image_compress {E : Finset ℕ} {i q : ℕ}
    (hi : i < E.card) (hpos : ∀ x ∈ E, 0 < x) (hg : q < subsetGap E i) :
    orderStat (E.image (compressAfter (orderStat E i) q)) i =
      orderStat E i := by
  have hinj := compress_injOn hi hpos hg
  have hcard : (E.image (compressAfter (orderStat E i) q)).card = E.card :=
    card_image_of_injOn hinj
  have hi' : i < (E.image (compressAfter (orderStat E i) q)).card := by
    simpa [hcard] using hi
  have hsort := sort_image_compress hi hpos hg
  by_cases hi0 : i = 0
  · subst hi0
    simp [orderStat]
  · have hi0' : 0 < i := Nat.pos_of_ne_zero hi0
    have hle : i ≤ (E.image (compressAfter (orderStat E i) q)).card :=
      Nat.le_of_lt hi'
    have hget := orderStat_pos_eq_sort (E := E.image (compressAfter (orderStat E i) q))
      hi0' hle
    have hlenE : (E.sort (· ≤ ·)).length = E.card := length_sort _
    have hk : i - 1 < (E.sort (· ≤ ·)).length := by omega
    have hmaplen :
        ((E.sort (· ≤ ·)).map (compressAfter (orderStat E i) q)).length =
          E.card := by
      simp [hlenE]
    have hk' : i - 1 <
        ((E.sort (· ≤ ·)).map (compressAfter (orderStat E i) q)).length := by
      omega
    have hxle : (E.sort (· ≤ ·))[i - 1]'hk ≤ orderStat E i := by
      have htake : (E.sort (· ≤ ·))[i - 1]'hk ∈ (E.sort (· ≤ ·)).take i :=
        List.mem_take_iff_getElem.mpr ⟨i - 1, by omega, rfl⟩
      exact take_le_orderStat hi _ htake
    have hcomp :
        compressAfter (orderStat E i) q ((E.sort (· ≤ ·))[i - 1]'hk) =
          (E.sort (· ≤ ·))[i - 1]'hk := by
      simp [compressAfter, hxle]
    have horig := orderStat_pos_eq_sort hi0' (Nat.le_of_lt hi)
    have hmapget :
        ((E.sort (· ≤ ·)).map (compressAfter (orderStat E i) q))[i - 1]'hk' =
          compressAfter (orderStat E i) q ((E.sort (· ≤ ·))[i - 1]'hk) := by
      simp [List.getElem_map]
    have hwant :
        ((E.sort (· ≤ ·)).map (compressAfter (orderStat E i) q))[i - 1]'hk' =
          orderStat E i := by
      simpa [hmapget, hcomp] using horig.symm
    rw [hget]
    exact (List.getElem_of_eq hsort (by
        simp [length_sort, hcard]
        omega)).trans hwant

private theorem orderStat_image_expand {F : Finset ℕ} {i q : ℕ}
    (hi : i < F.card) (hpos : ∀ x ∈ F, 0 < x) :
    orderStat (F.image (expandAfter (orderStat F i) q)) i =
      orderStat F i := by
  have hinj := expand_injOn (q := q) hi hpos
  have hcard : (F.image (expandAfter (orderStat F i) q)).card = F.card :=
    card_image_of_injOn hinj
  have hi' : i < (F.image (expandAfter (orderStat F i) q)).card := by
    simpa [hcard] using hi
  have hsort := sort_image_expand (q := q) hi hpos
  by_cases hi0 : i = 0
  · subst hi0
    simp [orderStat]
  · have hi0' : 0 < i := Nat.pos_of_ne_zero hi0
    have hle : i ≤ (F.image (expandAfter (orderStat F i) q)).card :=
      Nat.le_of_lt hi'
    have hget := orderStat_pos_eq_sort (E := F.image (expandAfter (orderStat F i) q))
      hi0' hle
    have hlenF : (F.sort (· ≤ ·)).length = F.card := length_sort _
    have hk : i - 1 < (F.sort (· ≤ ·)).length := by omega
    have hxle : (F.sort (· ≤ ·))[i - 1]'hk ≤ orderStat F i := by
      have htake : (F.sort (· ≤ ·))[i - 1]'hk ∈ (F.sort (· ≤ ·)).take i :=
        List.mem_take_iff_getElem.mpr ⟨i - 1, by omega, rfl⟩
      exact take_le_orderStat hi _ htake
    have hcomp :
        expandAfter (orderStat F i) q ((F.sort (· ≤ ·))[i - 1]'hk) =
          (F.sort (· ≤ ·))[i - 1]'hk := by
      simp [expandAfter, hxle]
    have horig := orderStat_pos_eq_sort hi0' (Nat.le_of_lt hi)
    have hmaplen :
        ((F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q)).length = F.card := by
      simp [hlenF]
    have hk' : i - 1 <
        ((F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q)).length := by
      omega
    have hmapget :
        ((F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q))[i - 1]'hk' =
          expandAfter (orderStat F i) q ((F.sort (· ≤ ·))[i - 1]'hk) := by
      simp [List.getElem_map]
    have hwant :
        ((F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q))[i - 1]'hk' =
          orderStat F i := by
      simpa [hmapget, hcomp] using horig.symm
    rw [hget]
    exact (List.getElem_of_eq hsort (by
        simp [length_sort, hcard]
        omega)).trans hwant

private theorem compressAfter_expandAfter {t q x : ℕ} :
    compressAfter t q (expandAfter t q x) = x := by
  unfold compressAfter expandAfter
  split_ifs <;> omega

private theorem expandAfter_compressAfter_of_gap {E : Finset ℕ} {i q x : ℕ}
    (hi : i < E.card) (hpos : ∀ x ∈ E, 0 < x) (hg : q < subsetGap E i)
    (hx : x ∈ E) :
    expandAfter (orderStat E i) q (compressAfter (orderStat E i) q x) = x := by
  set t := orderStat E i
  unfold expandAfter compressAfter
  by_cases hxle : x ≤ t
  · simp [hxle]
  · have hxgt : t < x := Nat.not_le.mp hxle
    have hxdrop := mem_drop_of_gt_orderStat hi hx hxgt
    have hnext := add_q_lt_of_mem_drop hi hpos hg hxdrop
    have hxq : q ≤ x := by omega
    have hnot : ¬ x - q ≤ t := by omega
    simp [hxle, hnot, Nat.sub_add_cancel hxq]

private theorem compress_subset_rankUniverse {E : Finset ℕ} {M i q : ℕ}
    (hE : E ⊆ rankUniverse M) (hi : i < E.card) (hg : q < subsetGap E i) :
    E.image (compressAfter (orderStat E i) q) ⊆ rankUniverse (M - q) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  have hxR := mem_rankUniverse.mp (hE hx)
  have hpos : ∀ z ∈ E, 0 < z := fun z hz => pos_of_subset_rankUniverse hE hz
  have hnext := lt_add_q_sort_get hi hpos hg
  set t := orderStat E i
  by_cases hxle : x ≤ t
  · have hyx : compressAfter t q x = x := by simp [compressAfter, hxle]
    rw [hyx]
    refine mem_rankUniverse.mpr ⟨hxR.1, ?_⟩
    have hlen : (E.sort (· ≤ ·)).length = E.card := length_sort _
    have hi' : i < (E.sort (· ≤ ·)).length := by simpa [hlen] using hi
    have hmax : (E.sort (· ≤ ·))[i]'hi' ≤ M := by
      have hmem : (E.sort (· ≤ ·))[i]'hi' ∈ E :=
        (mem_sort (· ≤ ·)).mp (List.getElem_mem _)
      exact (mem_rankUniverse.mp (hE hmem)).2
    have htq : t + q < (E.sort (· ≤ ·))[i]'hi' := hnext
    omega
  · have hxgt : t < x := Nat.not_le.mp hxle
    have hyx : compressAfter t q x = x - q := by simp [compressAfter, hxle]
    rw [hyx]
    have hxdrop := mem_drop_of_gt_orderStat hi hx hxgt
    have htq := add_q_lt_of_mem_drop hi hpos hg hxdrop
    have hxq : q ≤ x := by omega
    have hge1 : 1 ≤ x - q := by omega
    have hleM : x - q ≤ M - q := by omega
    exact mem_rankUniverse.mpr ⟨hge1, hleM⟩

private theorem expand_subset_rankUniverse {F : Finset ℕ} {M i q : ℕ}
    (hF : F ⊆ rankUniverse (M - q)) :
    F.image (expandAfter (orderStat F i) q) ⊆ rankUniverse M := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  have hxR := mem_rankUniverse.mp (hF hx)
  by_cases hxle : x ≤ orderStat F i
  · have : expandAfter (orderStat F i) q x = x := by simp [expandAfter, hxle]
    rw [this]
    exact mem_rankUniverse.mpr ⟨hxR.1, hxR.2.trans (Nat.sub_le M q)⟩
  · have : expandAfter (orderStat F i) q x = x + q := by simp [expandAfter, hxle]
    rw [this]
    refine mem_rankUniverse.mpr ⟨Nat.le_trans hxR.1 (Nat.le_add_right x q), ?_⟩
    omega

private theorem subsetGap_image_expand {F : Finset ℕ} {i q : ℕ}
    (hi : i < F.card) (hpos : ∀ x ∈ F, 0 < x) :
    q < subsetGap (F.image (expandAfter (orderStat F i) q)) i := by
  have hinj := expand_injOn (q := q) hi hpos
  have hcard : (F.image (expandAfter (orderStat F i) q)).card = F.card :=
    card_image_of_injOn hinj
  have hi' : i < (F.image (expandAfter (orderStat F i) q)).card := by
    simpa [hcard] using hi
  have hsort := sort_image_expand (q := q) hi hpos
  have hmap := map_expand_eq_take_drop (q := q) hi hpos
  have ht := orderStat_image_expand (q := q) hi hpos
  have hgap := subsetGap_eq_sort_sub (E := F.image (expandAfter (orderStat F i) q)) hi'
  have hlenF : (F.sort (· ≤ ·)).length = F.card := length_sort _
  have hiF : i < (F.sort (· ≤ ·)).length := by simpa [hlenF] using hi
  have hlen_map :
      ((F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q)).length = F.card := by
    simp [hlenF]
  have hi_map : i <
      ((F.sort (· ≤ ·)).map (expandAfter (orderStat F i) q)).length := by
    omega
  have hget :
      ((F.image (expandAfter (orderStat F i) q)).sort (· ≤ ·))[i]'(by
          simpa [length_sort, hcard] using hi') =
        (F.sort (· ≤ ·))[i]'hiF + q := by
    have htake_len : ((F.sort (· ≤ ·)).take i).length = i := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    have hidx : i - ((F.sort (· ≤ ·)).take i).length = 0 := by
      rw [htake_len, Nat.sub_self]
    have hdrop_pos : 0 < ((F.sort (· ≤ ·)).drop i).length := by
      rw [List.length_drop, hlenF]
      omega
    set dropMap : List ℕ :=
      ((F.sort (· ≤ ·)).drop i).map (fun x => x + q)
    have hidx_lt : i - ((F.sort (· ≤ ·)).take i).length < dropMap.length := by
      simpa [dropMap, List.length_map, List.length_drop, hlenF, htake_len, hidx]
        using hdrop_pos
    have hmap0 : dropMap[0]'(by simpa [dropMap, List.length_map] using hdrop_pos) =
        (F.sort (· ≤ ·))[i]'hiF + q := by
      simp [dropMap, List.getElem_map, List.getElem_drop]
    have happ :
        ((F.sort (· ≤ ·)).take i ++ dropMap)[i]'(by
            simp [dropMap, htake_len, List.length_map, List.length_drop, hlenF]
            omega) =
          dropMap[i - ((F.sort (· ≤ ·)).take i).length]'hidx_lt :=
      List.getElem_append_right (by
        simpa [htake_len] using (Nat.le_refl i))
    have hidx_get :
        dropMap[i - ((F.sort (· ≤ ·)).take i).length]'hidx_lt =
          dropMap[0]'(by simpa [dropMap, List.length_map] using hdrop_pos) :=
      getElem_congr_idx hidx
    exact
      (List.getElem_of_eq hsort (by simpa [length_sort, hcard] using hi')).trans
        ((List.getElem_of_eq hmap hi_map).trans (happ.trans (hidx_get.trans hmap0)))
  have hlt0 := lt_sort_get_orderStat hi hpos
  have : q <
      ((F.image (expandAfter (orderStat F i) q)).sort (· ≤ ·))[i]'(by
          simpa [length_sort, hcard] using hi') -
        orderStat (F.image (expandAfter (orderStat F i) q)) i := by
    rw [hget, ht]
    omega
  simpa [hgap] using this

private theorem compress_mem_uniform {M n i q : ℕ} {E : Finset ℕ}
    (hE : E ∈ uniformNSubsets M n) (hi : i < n) (hg : q < subsetGap E i) :
    E.image (compressAfter (orderStat E i) q) ∈ uniformNSubsets (M - q) n := by
  have hE' := mem_uniformNSubsets.mp hE
  have hpos : ∀ x ∈ E, 0 < x := fun x hx => pos_of_subset_rankUniverse hE'.1 hx
  have hiE : i < E.card := by simpa [hE'.2] using hi
  have hsub := compress_subset_rankUniverse hE'.1 hiE hg
  have hinj := compress_injOn hiE hpos hg
  have hcard : (E.image (compressAfter (orderStat E i) q)).card = n := by
    simpa [hE'.2] using card_image_of_injOn hinj
  exact mem_uniformNSubsets.mpr ⟨hsub, hcard⟩

private theorem expand_mem_filter {M n i q : ℕ} {F : Finset ℕ}
    (hF : F ∈ uniformNSubsets (M - q) n) (hn : 1 ≤ n) (hi : i < n) :
    F.image (expandAfter (orderStat F i) q) ∈
      (uniformNSubsets M n).filter (fun E => q < subsetGap E i) := by
  have hF' := mem_uniformNSubsets.mp hF
  have hpos : ∀ x ∈ F, 0 < x := fun x hx => pos_of_subset_rankUniverse hF'.1 hx
  have hiF : i < F.card := by simpa [hF'.2] using hi
  have hsub := expand_subset_rankUniverse (M := M) (i := i) (q := q) hF'.1
  have hinj := expand_injOn (q := q) hiF hpos
  have hcard : (F.image (expandAfter (orderStat F i) q)).card = n := by
    simpa [hF'.2] using card_image_of_injOn hinj
  have hmem : F.image (expandAfter (orderStat F i) q) ∈ uniformNSubsets M n :=
    mem_uniformNSubsets.mpr ⟨hsub, hcard⟩
  have hgap := subsetGap_image_expand (q := q) hiF hpos
  exact mem_filter.mpr ⟨hmem, hgap⟩

private theorem expand_compress {M n i q : ℕ} {E : Finset ℕ}
    (hE : E ∈ uniformNSubsets M n) (hi : i < n) (hg : q < subsetGap E i) :
    (E.image (compressAfter (orderStat E i) q)).image
        (expandAfter (orderStat (E.image (compressAfter (orderStat E i) q)) i) q) =
      E := by
  have hE' := mem_uniformNSubsets.mp hE
  have hpos : ∀ x ∈ E, 0 < x := fun x hx => pos_of_subset_rankUniverse hE'.1 hx
  have hiE : i < E.card := by simpa [hE'.2] using hi
  have ht := orderStat_image_compress hiE hpos hg
  rw [ht]
  have hpt : ∀ x ∈ E,
      expandAfter (orderStat E i) q (compressAfter (orderStat E i) q x) = x :=
    fun x hx => expandAfter_compressAfter_of_gap hiE hpos hg hx
  rw [image_image]
  refine (image_congr (g := (id : ℕ → ℕ)) ?_).trans ?_
  · intro x hx
    simp only [Function.comp_apply, id_eq]
    exact hpt x hx
  · simp [Finset.image_id]

private theorem compress_expand {M n i q : ℕ} {F : Finset ℕ}
    (hF : F ∈ uniformNSubsets (M - q) n) (hi : i < n) :
    (F.image (expandAfter (orderStat F i) q)).image
        (compressAfter (orderStat (F.image (expandAfter (orderStat F i) q)) i) q) =
      F := by
  have hF' := mem_uniformNSubsets.mp hF
  have hpos : ∀ x ∈ F, 0 < x := fun x hx => pos_of_subset_rankUniverse hF'.1 hx
  have hiF : i < F.card := by simpa [hF'.2] using hi
  have ht := orderStat_image_expand (q := q) hiF hpos
  rw [ht]
  have hpt : ∀ x ∈ F,
      compressAfter (orderStat F i) q (expandAfter (orderStat F i) q x) = x :=
    fun x _ => compressAfter_expandAfter
  rw [image_image]
  refine (image_congr (g := (id : ℕ → ℕ)) ?_).trans ?_
  · intro x hx
    simp only [Function.comp_apply, id_eq]
    exact hpt x hx
  · simp [Finset.image_id]

private theorem filter_gap_card (M n i q : ℕ) (hn : 1 ≤ n) (hnM : n ≤ M)
    (hi : i < n) :
    ((uniformNSubsets M n).filter (fun E => q < subsetGap E i)).card =
      Nat.choose (M - q) n := by
  refine Eq.trans ?_ (uniformNSubsets_card (M - q) n)
  refine card_bij'
      (fun E _ => E.image (compressAfter (orderStat E i) q))
      (fun F _ => F.image (expandAfter (orderStat F i) q))
      ?_ ?_ ?_ ?_
  · intro E hE
    have hg := (mem_filter.mp hE).2
    exact compress_mem_uniform (mem_filter.mp hE).1 hi hg
  · intro F hF
    exact expand_mem_filter hF hn hi
  · intro E hE
    exact expand_compress (mem_filter.mp hE).1 hi (mem_filter.mp hE).2
  · intro F hF
    exact compress_expand hF hi

/-- Paper identity: `Pr(D_i > q) = binom(M-q, n) / binom(M, n)`. -/
theorem SubsetSpacingIdentity (M n i q : ℕ) :
    1 ≤ n → n ≤ M → i < n →
      subsetSpacingProbGt M n i q =
        (Nat.choose (M - q) n : ℝ) / (Nat.choose M n : ℝ) := by
  intro hn hnM hi
  unfold subsetSpacingProbGt
  have hscard : (uniformNSubsets M n).card = Nat.choose M n :=
    uniformNSubsets_card M n
  have hpos : (uniformNSubsets M n).card ≠ 0 := by
    rw [hscard]
    exact (Nat.choose_pos hnM).ne'
  simp [hpos]
  rw [filter_gap_card M n i q hn hnM hi, hscard]

/-! ### Exponential and short tails -/

private theorem choose_pred_div_choose {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    (Nat.choose (N - 1) k : ℝ) / (Nat.choose N k : ℝ) =
      ((N - k : ℕ) : ℝ) / (N : ℝ) := by
  have hch : (Nat.choose N k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hk)
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hmul := Nat.choose_mul_succ_eq (N - 1) k
  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN)
  rw [hN1] at hmul
  have hcast :
      (Nat.choose (N - 1) k : ℝ) * (N : ℝ) =
        (Nat.choose N k : ℝ) * ((N - k : ℕ) : ℝ) := by
    exact_mod_cast hmul
  rw [div_eq_div_iff hch hN0]
  exact hcast.trans (mul_comm _ _)

private theorem choose_ratio_le_pow {M n q : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    (Nat.choose (M - q) n : ℝ) / (Nat.choose M n : ℝ) ≤
      (((M : ℝ) - n) / M) ^ q := by
  have hM : 0 < M := Nat.lt_of_lt_of_le hn hnM
  induction q with
  | zero =>
    have hne : (Nat.choose M n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hnM)
    simp [div_self hne]
  | succ q ih =>
    by_cases hle : n ≤ M - (q + 1)
    · have hle' : n ≤ M - q := by omega
      have hMq : 0 < M - q := by omega
      have hstep :
          (Nat.choose (M - (q + 1)) n : ℝ) / (Nat.choose (M - q) n : ℝ) =
            ((M - q - n : ℕ) : ℝ) / ((M - q : ℕ) : ℝ) := by
        simpa [Nat.sub_sub] using
          choose_pred_div_choose (N := M - q) (k := n) hMq hle'
      have hsplit :
          (Nat.choose (M - (q + 1)) n : ℝ) / (Nat.choose M n : ℝ) =
            ((Nat.choose (M - (q + 1)) n : ℝ) / (Nat.choose (M - q) n : ℝ)) *
              ((Nat.choose (M - q) n : ℝ) / (Nat.choose M n : ℝ)) := by
        have hmid : (Nat.choose (M - q) n : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hle')
        field_simp [hmid]
      have hMn : ((M - n : ℕ) : ℝ) = (M : ℝ) - n := Nat.cast_sub hnM
      have hfac :
          ((M - q - n : ℕ) : ℝ) / ((M - q : ℕ) : ℝ) ≤
            ((M - n : ℕ) : ℝ) / (M : ℝ) := by
        have hnat : (M - q - n) * M ≤ (M - n) * (M - q) := by
          have hleft : (M - q - n) * M = (M - q) * M - n * M :=
            Nat.sub_mul (M - q) n M
          have h3 : n * (M - q) ≤ n * M :=
            Nat.mul_le_mul_left n (Nat.sub_le M q)
          have h4 : (M - q) * M - n * M ≤ (M - q) * M - n * (M - q) :=
            Nat.sub_le_sub_left h3 ((M - q) * M)
          have hcomm : (M - q) * M = M * (M - q) := Nat.mul_comm (M - q) M
          have hright : (M - q) * M - n * (M - q) = (M - n) * (M - q) := by
            rw [hcomm]
            exact (Nat.sub_mul M n (M - q)).symm
          exact hleft.trans_le (h4.trans (le_of_eq hright))
        have hMqR : (0 : ℝ) < (M - q : ℕ) := Nat.cast_pos.mpr hMq
        have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
        rw [div_le_div_iff₀ hMqR hMR]
        exact_mod_cast hnat
      rw [hsplit, hstep]
      have hbound :=
        mul_le_mul hfac ih
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      have hpow :
          ((M - n : ℕ) : ℝ) / (M : ℝ) * (((M : ℝ) - n) / M) ^ q =
            (((M : ℝ) - n) / M) ^ (q + 1) := by
        rw [hMn, mul_comm, pow_succ]
      exact hbound.trans_eq hpow
    · have hz : Nat.choose (M - (q + 1)) n = 0 :=
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hle)
      have : (Nat.choose (M - (q + 1)) n : ℝ) / (Nat.choose M n : ℝ) = 0 := by
        rw [hz, Nat.cast_zero, zero_div]
      rw [this]
      exact pow_nonneg (div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hnM))
        (Nat.cast_nonneg _)) _

/-- Exponential tail `≤ exp(-n q / M)`. -/
theorem SubsetSpacingExpTail (M n i q : ℕ) :
    1 ≤ n → n ≤ M → i < n →
      subsetSpacingProbGt M n i q ≤ Real.exp (-(n : ℝ) * q / M) := by
  intro hn hnM hi
  rw [SubsetSpacingIdentity M n i q hn hnM hi]
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hn hnM)
  have hratio := choose_ratio_le_pow (M := M) (n := n) (q := q) hn hnM
  have hx : ((M : ℝ) - n) / M = 1 - (n : ℝ) / M := by
    rw [sub_div, div_self hM.ne']
  have hpow :
      (((M : ℝ) - n) / M) ^ q ≤ Real.exp (-(n : ℝ) / M) ^ q := by
    rw [hx]
    have hle :=
      pow_le_pow_left₀
        (sub_nonneg.mpr ((div_le_one hM).mpr (Nat.cast_le.mpr hnM)))
        (Real.one_sub_le_exp_neg ((n : ℝ) / M)) q
    have harg :
        Real.exp (-((n : ℝ) / M)) ^ q = Real.exp (-(n : ℝ) / M) ^ q := by
      rw [← neg_div]
    exact hle.trans_eq harg
  have hexp : Real.exp (-(n : ℝ) / M) ^ q = Real.exp (-(n : ℝ) * q / M) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact hratio.trans (hpow.trans_eq hexp)

private theorem choose_sub_le {M n q : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    Nat.choose M n - Nat.choose (M - q) n ≤ q * Nat.choose (M - 1) (n - 1) := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    have hmono : Nat.choose (M - (q + 1)) n ≤ Nat.choose (M - q) n :=
      Nat.choose_le_choose n (Nat.sub_le_sub_left (Nat.le_succ q) M)
    have hmono' : Nat.choose (M - q) n ≤ Nat.choose M n :=
      Nat.choose_le_choose n (Nat.sub_le M q)
    have htel :
        Nat.choose M n - Nat.choose (M - (q + 1)) n =
          (Nat.choose M n - Nat.choose (M - q) n) +
            (Nat.choose (M - q) n - Nat.choose (M - (q + 1)) n) :=
      (Nat.sub_add_sub_cancel hmono' hmono).symm
    have hstep : Nat.choose (M - q) n - Nat.choose (M - (q + 1)) n ≤
        Nat.choose (M - 1) (n - 1) := by
      by_cases hMq : M - q = 0
      · have : M - (q + 1) = 0 := by omega
        simp [hMq, this]
      · have hN : 0 < M - q := Nat.pos_of_ne_zero hMq
        have hn0 : 0 < n := Nat.succ_le_iff.mp hn
        have hpascal :
            Nat.choose (M - q) n =
              Nat.choose (M - q - 1) (n - 1) + Nat.choose (M - q - 1) n :=
          Nat.choose_eq_choose_pred_add hN hn0
        have : Nat.choose (M - q) n - Nat.choose (M - q - 1) n =
            Nat.choose (M - q - 1) (n - 1) := by
          rw [hpascal, Nat.add_sub_cancel_right]
        have hrew : M - (q + 1) = M - q - 1 := (Nat.sub_sub M q 1).symm
        rw [hrew, this]
        exact Nat.choose_le_choose (n - 1) (by omega)
    have : q * Nat.choose (M - 1) (n - 1) + Nat.choose (M - 1) (n - 1) =
        (q + 1) * Nat.choose (M - 1) (n - 1) :=
      (Nat.succ_mul q (Nat.choose (M - 1) (n - 1))).symm
    calc
      Nat.choose M n - Nat.choose (M - (q + 1)) n
          = (Nat.choose M n - Nat.choose (M - q) n) +
              (Nat.choose (M - q) n - Nat.choose (M - (q + 1)) n) := htel
      _ ≤ q * Nat.choose (M - 1) (n - 1) + Nat.choose (M - 1) (n - 1) :=
        Nat.add_le_add ih hstep
      _ = (q + 1) * Nat.choose (M - 1) (n - 1) := this

private theorem choose_pred_div_eq {M n : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    (Nat.choose (M - 1) (n - 1) : ℝ) / (Nat.choose M n : ℝ) =
      (n : ℝ) / M := by
  have hM : 0 < M := Nat.lt_of_lt_of_le hn hnM
  have hch : (Nat.choose M n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hnM)
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hmulN :
      M * Nat.choose (M - 1) (n - 1) = Nat.choose M n * n := by
    have := Nat.add_one_mul_choose_eq (M - 1) (n - 1)
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hM),
      Nat.sub_add_cancel hn] using this
  have hcast :
      (M : ℝ) * (Nat.choose (M - 1) (n - 1) : ℝ) =
        (Nat.choose M n : ℝ) * (n : ℝ) := by
    exact_mod_cast hmulN
  rw [div_eq_div_iff hch hM0, mul_comm (n : ℝ),
    mul_comm (Nat.choose (M - 1) (n - 1) : ℝ)]
  exact hcast

/-- Short bound `Pr(D_i ≤ q) ≤ n q / M`. -/
theorem SubsetSpacingShort (M n i q : ℕ) :
    1 ≤ n → n ≤ M → i < n →
      1 - subsetSpacingProbGt M n i q ≤ (n : ℝ) * q / M := by
  intro hn hnM hi
  rw [SubsetSpacingIdentity M n i q hn hnM hi]
  have hM : 0 < M := Nat.lt_of_lt_of_le hn hnM
  have hch : (Nat.choose M n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hnM)
  have hle : Nat.choose (M - q) n ≤ Nat.choose M n :=
    Nat.choose_le_choose n (Nat.sub_le M q)
  have hsub :
      1 - (Nat.choose (M - q) n : ℝ) / (Nat.choose M n : ℝ) =
        ((Nat.choose M n - Nat.choose (M - q) n : ℕ) : ℝ) /
          (Nat.choose M n : ℝ) := by
    have hcast :
        ((Nat.choose M n - Nat.choose (M - q) n : ℕ) : ℝ) =
          (Nat.choose M n : ℝ) - (Nat.choose (M - q) n : ℝ) :=
      Nat.cast_sub hle
    rw [hcast, sub_div, div_self (a := (Nat.choose M n : ℝ)) hch]
  rw [hsub]
  have hnat := choose_sub_le (M := M) (n := n) (q := q) hn hnM
  have hnum :
      ((Nat.choose M n - Nat.choose (M - q) n : ℕ) : ℝ) ≤
        (q : ℝ) * (Nat.choose (M - 1) (n - 1) : ℝ) := by
    exact_mod_cast hnat
  have hdiv :
      ((Nat.choose M n - Nat.choose (M - q) n : ℕ) : ℝ) /
          (Nat.choose M n : ℝ) ≤
        (q : ℝ) * (Nat.choose (M - 1) (n - 1) : ℝ) / (Nat.choose M n : ℝ) :=
    div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)
  have hrat := choose_pred_div_eq (M := M) (n := n) hn hnM
  have hrew :
      (q : ℝ) * (Nat.choose (M - 1) (n - 1) : ℝ) / (Nat.choose M n : ℝ) =
        (n : ℝ) * q / M := by
    calc
      (q : ℝ) * (Nat.choose (M - 1) (n - 1) : ℝ) / (Nat.choose M n : ℝ)
          = (q : ℝ) *
              ((Nat.choose (M - 1) (n - 1) : ℝ) / (Nat.choose M n : ℝ)) := by
            rw [mul_div_assoc]
      _ = (q : ℝ) * ((n : ℝ) / M) := by rw [hrat]
      _ = (q : ℝ) * (n : ℝ) / M := by rw [mul_div_assoc]
      _ = (n : ℝ) * q / M := by rw [mul_comm (q : ℝ)]
  exact hdiv.trans_eq hrew

/-! ### Physical gap majorized by a deterministic rank threshold -/

/-- Occupancy of a physical interval of length `H`, uniformly in the
start `t`. Instantiate from a good relative grid. Apply this bound
*before* `SubsetSpacingIdentity`; do not condition on a random start. -/
def PhysicalWindowOccupancyLe (A : Finset ℕ) (S' H q : ℕ) : Prop :=
  ∀ t : ℕ, t ≤ S' → (A ∩ Ioc t (t + H)).card ≤ q

/-- A physical interval that stays inside the aligned span is bounded
below by a deterministic rank count. Empty if the interval exits `S'`. -/
def PhysicalWindowOccupancyGe (A : Finset ℕ) (S' H q : ℕ) : Prop :=
  ∀ t : ℕ, t + H < S' → q ≤ (A ∩ Ioc t (t + H)).card

theorem Ioo_subset_Ioc_of_right_le {a b c : ℕ} (h : b ≤ c) :
    Ioo a b ⊆ Ioc a c := by
  intro x hx
  have hx' := mem_Ioo.mp hx
  exact mem_Ioc.mpr ⟨hx'.1, (Nat.le_of_lt hx'.2).trans h⟩

/-- A physical gap of length at most `H` is contained in the occupancy
window of length `H` at the same start. Rank-gap bounds are applied only
after this comparison. -/
theorem physical_short_gap_occupancy_le {A E : Finset ℕ} {i H : ℕ}
    (_hEA : E ⊆ A) (_hi : i < E.card) (hshort : subsetGap E i ≤ H) :
    (A ∩ Ioo (orderStat E i) (orderStat E (i + 1))).card ≤
      (A ∩ Ioc (orderStat E i) (orderStat E i + H)).card := by
  have hle : orderStat E (i + 1) ≤ orderStat E i + H :=
    (Nat.sub_le_iff_le_add').mp hshort
  have hsub : Ioo (orderStat E i) (orderStat E (i + 1)) ⊆
      Ioc (orderStat E i) (orderStat E i + H) :=
    Ioo_subset_Ioc_of_right_le hle
  exact card_le_card (inter_subset_inter_left hsub)

/-- Combine a uniform physical-window occupancy bound with a short
physical gap. The resulting rank count is then ready for
`SubsetSpacingIdentity`. -/
theorem physical_short_gap_rankCount_le {A E : Finset ℕ} {S' H q i : ℕ}
    (hmaj : PhysicalWindowOccupancyLe A S' H q) (hEA : E ⊆ A)
    (hi : i < E.card) (hstart : orderStat E i ≤ S')
    (hshort : subsetGap E i ≤ H) :
    (A ∩ Ioo (orderStat E i) (orderStat E (i + 1))).card ≤ q :=
  (physical_short_gap_occupancy_le hEA hi hshort).trans (hmaj _ hstart)

/-! ### Generic complete-frame masses -/

private theorem j_lt_of_geL {L j : ℕ} {B : Finset ℕ}
    (hj : j + 1 < L) (hB : L ≤ B.card) : j < B.card :=
  Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt hj) hB

private theorem mem_completeFrames_erase {A B : Finset ℕ} {L j : ℕ}
    (hBA : B ⊆ A) (hB : L ≤ B.card) (hj : j + 1 < L) :
    B.erase (deletedOf B j) ∈
      A.powerset.filter (fun F => L - 1 ≤ F.card) := by
  have hjB : j < B.card := j_lt_of_geL hj hB
  have huB : deletedOf B j ∈ B := deletedOf_mem hjB
  refine mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset _ B).trans hBA), ?_⟩
  rw [card_erase_of_mem huB]
  exact Nat.sub_le_sub_right hB 1

private theorem mem_openSlot_erase {A B : Finset ℕ} {j : ℕ}
    (hBA : B ⊆ A) (hpos : ∀ x ∈ A, 0 < x) (hj : j + 1 < B.card) :
    deletedOf B j ∈
      openSlot A ((B.erase (deletedOf B j)).sort (· ≤ ·)) j := by
  have hu := mem_openSlot_of_remainingFrame hBA hpos hj
  rw [← deletedOf_eq_getElem (Nat.lt_of_succ_lt hj)] at hu
  rwa [remainingFrame_eq_erase_sort (Nat.lt_of_succ_lt hj)] at hu

private theorem mem_geL_insert {A F : Finset ℕ} {L j u : ℕ}
    (hL : 2 ≤ L) (hFA : F ⊆ A) (hF : L - 1 ≤ F.card)
    (hu : u ∈ openSlot A (F.sort (· ≤ ·)) j) :
    insert u F ∈ A.powerset.filter (fun B => L ≤ B.card) := by
  have huA : u ∈ A := (mem_openSlot.mp hu).1
  have hBA : insert u F ⊆ A := insert_subset huA hFA
  have hcard : (insert u F).card = F.card + 1 :=
    card_insert_of_notMem (not_mem_of_mem_openSlot_sort hu)
  have hL1 : 1 ≤ L := Nat.le_of_succ_le hL
  have hge : L ≤ (insert u F).card := by
    rw [hcard]
    have := Nat.succ_le_succ hF
    simpa [Nat.sub_add_cancel hL1] using this
  exact mem_filter.mpr ⟨mem_powerset.mpr hBA, hge⟩

theorem mu_eq_uniformLayerWeight {A : Finset ℕ} {μ : Finset ℕ → ℝ}
    (hμ : CardinalitySymmetricMass A μ) {E : Finset ℕ} (hEA : E ⊆ A) :
    μ E = uniformLayerWeight A μ E.card := by
  set n := E.card
  have hn : n ≤ A.card := card_le_card hEA
  have hch : 0 < Nat.choose A.card n := Nat.choose_pos hn
  unfold uniformLayerWeight
  rw [dif_pos ⟨hn, hch⟩]
  set s := A.powerset.filter (fun F => F.card = n)
  have hs : ∀ F ∈ s, μ F = μ E := by
    intro F hF
    have hFA : F ⊆ A := mem_powerset.mp (mem_filter.mp hF).1
    have hcard : F.card = n := (mem_filter.mp hF).2
    exact hμ.2.2 F E hFA hEA hcard
  have hsum : cardinalityLayer A μ n = (Nat.choose A.card n : ℝ) * μ E := by
    unfold cardinalityLayer
    rw [sum_congr (s₁ := s) (s₂ := s) rfl hs, sum_const, nsmul_eq_mul]
    have hscard : s.card = Nat.choose A.card n := by
      rw [show s = A.powersetCard n from (powersetCard_eq_filter).symm,
        card_powersetCard]
    rw [hscard]
  rw [hsum]
  have hne : (Nat.choose A.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hch.ne'
  exact (mul_div_cancel_left₀ (μ E) hne).symm

theorem genericFrameMass_eq_openSlot_sum {A : Finset ℕ} {μ : Finset ℕ → ℝ}
    (hμ : CardinalitySymmetricMass A μ) {F : Finset ℕ} {j : ℕ}
    (hFA : F ⊆ A) :
    genericFrameMass A μ F j =
      ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j, μ (insert u F) := by
  unfold genericFrameMass
  have hterm : ∀ u ∈ openSlot A (F.sort (· ≤ ·)) j,
      μ (insert u F) = uniformLayerWeight A μ (F.card + 1) := by
    intro u hu
    have huA : u ∈ A := (mem_openSlot.mp hu).1
    have hins : insert u F ⊆ A := insert_subset huA hFA
    have hcard : (insert u F).card = F.card + 1 :=
      card_insert_of_notMem (not_mem_of_mem_openSlot_sort hu)
    rw [mu_eq_uniformLayerWeight hμ hins, hcard]
  rw [sum_congr (s₁ := openSlot A (F.sort (· ≤ ·)) j)
    (s₂ := openSlot A (F.sort (· ≤ ·)) j) rfl hterm, sum_const, nsmul_eq_mul]

private theorem generic_preimage_sum_eq_geL {A : Finset ℕ} {μ : Finset ℕ → ℝ}
    {L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L) (hpos : ∀ x ∈ A, 0 < x) :
    ∑ F ∈ A.powerset.filter (fun F => L - 1 ≤ F.card),
        ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j,
          μ (insertAt (F.sort (· ≤ ·)) j u).toFinset =
      ∑ B ∈ A.powerset.filter (fun B => L ≤ B.card), μ B := by
  set frames := A.powerset.filter (fun F => L - 1 ≤ F.card)
  rw [sum_sigma' (s := frames)
    (t := fun F => openSlot A (F.sort (· ≤ ·)) j)
    (f := fun F u => μ (insertAt (F.sort (· ≤ ·)) j u).toFinset)]
  refine sum_bij'
      (fun p _ => insert p.2 p.1)
      (fun B _ => ⟨B.erase (deletedOf B j), deletedOf B j⟩)
      ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hF := (mem_sigma.mp hp).1
    have hu := (mem_sigma.mp hp).2
    have hFcard : L - 1 ≤ p.1.card := (mem_filter.mp hF).2
    have hFA : p.1 ⊆ A := mem_powerset.mp (mem_filter.mp hF).1
    exact mem_geL_insert hL hFA hFcard hu
  · intro B hB
    have hBcard : L ≤ B.card := (mem_filter.mp hB).2
    have hBA : B ⊆ A := mem_powerset.mp (mem_filter.mp hB).1
    have hj1 : j + 1 < B.card := Nat.lt_of_lt_of_le hj hBcard
    refine mem_sigma.mpr ⟨?_, ?_⟩
    · exact mem_completeFrames_erase hBA hBcard hj
    · exact mem_openSlot_erase hBA hpos hj1
  · intro p hp
    have hu := (mem_sigma.mp hp).2
    have hdel : deletedOf (insert p.2 p.1) j = p.2 :=
      insert_sort_deletedOf_eq hu
    simp [hdel, erase_insert (not_mem_of_mem_openSlot_sort hu)]
  · intro B hB
    have hBcard : L ≤ B.card := (mem_filter.mp hB).2
    have hjB : j < B.card := j_lt_of_geL hj hBcard
    exact insert_erase (deletedOf_mem hjB)
  · intro p hp
    have hu := (mem_sigma.mp hp).2
    have hjF : j < (p.1.sort (· ≤ ·)).length :=
      lt_length_of_mem_deletionSlot (mem_openSlot.mp hu).2.2
    have hjle : j ≤ (p.1.sort (· ≤ ·)).length := Nat.le_of_lt hjF
    rw [insertAt_toFinset hjle, sort_toFinset]

/-- Geometric preimage identity for an arbitrary weight, then
cardinality symmetry to factor the slot cardinality. Sums to
`Pr(N ≥ L)`. -/
theorem GenericFrameMassEqGeL (A : Finset ℕ) (μ : Finset ℕ → ℝ)
    (L j : ℕ) :
    CardinalitySymmetricMass A μ →
      2 ≤ L → j + 1 < L → (∀ x ∈ A, 0 < x) →
        ∑ F ∈ A.powerset.filter (fun F => L - 1 ≤ F.card),
            genericFrameMass A μ F j =
          ∑ B ∈ A.powerset.filter (fun B => L ≤ B.card), μ B := by
  intro hμ hL hj hpos
  set frames := A.powerset.filter (fun F => L - 1 ≤ F.card)
  have hpt : ∀ F ∈ frames,
      genericFrameMass A μ F j =
        ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j, μ (insert u F) := by
    intro F hF
    have hFA : F ⊆ A := mem_powerset.mp (mem_filter.mp hF).1
    exact genericFrameMass_eq_openSlot_sum hμ hFA
  rw [sum_congr (s₁ := frames) (s₂ := frames) rfl hpt]
  have hpt' : ∀ F ∈ frames,
      ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j, μ (insert u F) =
        ∑ u ∈ openSlot A (F.sort (· ≤ ·)) j,
          μ (insertAt (F.sort (· ≤ ·)) j u).toFinset := by
    intro F hF
    refine sum_congr (s₁ := openSlot A (F.sort (· ≤ ·)) j)
      (s₂ := openSlot A (F.sort (· ≤ ·)) j) rfl ?_
    intro u hu
    have hjF : j < (F.sort (· ≤ ·)).length :=
      lt_length_of_mem_deletionSlot (mem_openSlot.mp hu).2.2
    have hjle : j ≤ (F.sort (· ≤ ·)).length := Nat.le_of_lt hjF
    rw [insertAt_toFinset hjle, sort_toFinset]
  rw [sum_congr (s₁ := frames) (s₂ := frames) rfl hpt']
  exact generic_preimage_sum_eq_geL hL hj hpos

end PrimeGapNormality.Prime
