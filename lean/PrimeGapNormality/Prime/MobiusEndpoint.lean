import PrimeGapNormality.Prime.MobiusTV
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Endpoint Möbius coefficients, remainder, and high-order transfer

Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §§2–4;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §4.B.
Contract: combinatorial remainder
Audit: GREEN

Finite combinatorics only. No PNT, no normality corollary, no RestrictedUHL
axiom. The maps `A` and `Q` are explicit parameters/hypotheses.
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 800000

/-! ### Endpoint observable -/

/-- `f(U)=0` if `|U|<L`, else `phi` of the increasing first `L` points.

Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §2;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §4.B.
Contract: combinatorial remainder
Audit: GREEN -/
noncomputable def endpointObs (L : ℕ) (phi : List ℕ → ℝ) (U : Finset ℕ) : ℝ :=
  if U.card < L then 0 else phi ((U.sort (· ≤ ·)).take L)

/-- Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §2.
Contract: combinatorial remainder
Audit: GREEN -/
theorem abs_endpointObs_le (L : ℕ) (phi : List ℕ → ℝ) (U : Finset ℕ)
    (hφ : ∀ t, |phi t| ≤ 1) :
    |endpointObs L phi U| ≤ 1 := by
  unfold endpointObs
  split_ifs
  · simp
  · exact hφ _

/-- Binomial moment `E μ[C(N,j)]`.

Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §4.
Contract: combinatorial remainder
Audit: GREEN -/
noncomputable def inclusionMoment (V : Finset ℕ) (μ : Finset ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ U ∈ V.powerset, μ U * (U.card.choose j : ℝ)

/-- Inclusion probability `p_H = ∑_{H ⊆ U} μ(U)` on the powerset of `V`.

Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §4.
Contract: combinatorial remainder
Audit: GREEN -/
noncomputable def inclusionProb (V : Finset ℕ) (μ : Finset ℕ → ℝ) (H : Finset ℕ) : ℝ :=
  ∑ U ∈ V.powerset, if H ⊆ U then μ U else 0

/-- Summed absolute inclusion discrepancies of order `j`.

Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §4.
Contract: combinatorial remainder
Audit: GREEN -/
noncomputable def summedAbsDelta (V : Finset ℕ) (μ ν : Finset ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ H ∈ V.powerset.filter (fun H => H.card = j),
    |inclusionProb V μ H - inclusionProb V ν H|

/-! ### Sorted unions and points below a coordinate -/

private theorem card_pos_of_one_le_card {L : ℕ} {s : Finset ℕ}
    (hL : 1 ≤ L) (hs : L ≤ s.card) : s.Nonempty :=
  card_pos.mp (lt_of_lt_of_le hL hs)

private theorem sort_union_of_forall_lt (A B : Finset ℕ)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    (A ∪ B).sort (· ≤ ·) = A.sort (· ≤ ·) ++ B.sort (· ≤ ·) := by
  have hA : (A.sort (· ≤ ·)).SortedLT := sortedLT_sort A
  have hB : (B.sort (· ≤ ·)).SortedLT := sortedLT_sort B
  have hcross : ∀ x ∈ A.sort (· ≤ ·), ∀ y ∈ B.sort (· ≤ ·), x < y := by
    intro x hx y hy
    exact hAB x ((mem_sort (· ≤ ·)).mp hx) y ((mem_sort (· ≤ ·)).mp hy)
  have hpw : (A.sort (· ≤ ·) ++ B.sort (· ≤ ·)).Pairwise (· < ·) :=
    List.pairwise_append.mpr ⟨hA.pairwise, hB.pairwise, hcross⟩
  have hL : (A.sort (· ≤ ·) ++ B.sort (· ≤ ·)).SortedLT := hpw.sortedLT
  have hR : ((A ∪ B).sort (· ≤ ·)).SortedLT := sortedLT_sort _
  refine hR.eq_of_mem_iff hL ?_
  intro z
  simp [mem_sort, mem_union, List.mem_append]

private theorem sort_insert_gt {J : Finset ℕ} {x : ℕ}
    (h : ∀ y ∈ J, y < x) :
    (insert x J).sort (· ≤ ·) = J.sort (· ≤ ·) ++ [x] := by
  have hx : x ∉ J := fun hy => lt_irrefl x (h x hy)
  have hunion : insert x J = J ∪ {x} := by
    rw [insert_eq, union_comm]
  rw [hunion, sort_union_of_forall_lt J {x} (fun a ha b hb => by
    simp only [mem_singleton] at hb
    subst b
    exact h a ha), sort_singleton]

private theorem le_max_self {H : Finset ℕ} (hHne : H.Nonempty) :
    ∀ y ∈ H, y ≤ H.max' hHne :=
  (max'_le_iff (s := H) (H := hHne)).mp le_rfl

private theorem notMem_of_forall_lt {G : Finset ℕ} {x : ℕ}
    (hG : ∀ y ∈ G, y < x) : x ∉ G :=
  fun hx => lt_irrefl x (hG x hx)

private theorem max'_insert_gt {G : Finset ℕ} {x : ℕ}
    (hG : ∀ y ∈ G, y < x) :
    (insert x G).max' (insert_nonempty x G) = x := by
  apply le_antisymm
  · rw [max'_le_iff]
    intro y hy
    rcases mem_insert.mp hy with rfl | hyG
    · exact le_rfl
    · exact (hG y hyG).le
  · exact le_max' _ x (mem_insert_self x G)

/-! ### Signed binomial tail -/

private theorem sum_powerset_neg_one_real (W : Finset ℕ) :
    ∑ S ∈ W.powerset, (-1 : ℝ) ^ S.card = if W = ∅ then (1 : ℝ) else 0 := by
  have h := sum_powerset_neg_one_pow_card (α := ℕ) (x := W)
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) h
  simpa [Int.cast_sum, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_ite,
    Int.cast_zero] using hcast

private theorem sum_range_signed_choose {n k : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ range (k + 1), (-1 : ℝ) ^ i * (n.choose i : ℝ) =
      (-1 : ℝ) ^ k * ((n - 1).choose k : ℝ) := by
  have hz := Int.alternating_sum_range_choose_eq_choose (n := n - 1) (m := k)
  have hn' : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
  rw [← hn'] at hz
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hz
  simpa [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast] using hcast

private theorem sum_Icc_signed_choose_high {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∑ q ∈ Icc k n, (-1 : ℝ) ^ q * (n.choose q : ℝ) =
      (-1 : ℝ) ^ k * ((n - 1).choose (k - 1) : ℝ) := by
  rcases le_or_gt k n with hkn | hkn
  · have hfull_z := Int.alternating_sum_range_choose_of_ne (n := n)
      (Nat.one_le_iff_ne_zero.mp hn)
    have hfull : ∑ q ∈ range (n + 1), (-1 : ℝ) ^ q * (n.choose q : ℝ) = 0 := by
      have hcast := congrArg (fun z : ℤ => (z : ℝ)) hfull_z
      simpa [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, Int.cast_zero] using hcast
    have hlow :
        ∑ q ∈ range k, (-1 : ℝ) ^ q * (n.choose q : ℝ) =
          (-1 : ℝ) ^ (k - 1) * ((n - 1).choose (k - 1) : ℝ) := by
      have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
      rw [hk']
      exact sum_range_signed_choose hn
    have hdisj : Disjoint (range k) (Icc k n) :=
      disjoint_left.mpr fun a ha hb =>
        (mem_range.mp ha).not_ge (mem_Icc.mp hb).1
    have hunion : range k ∪ Icc k n = range (n + 1) := by
      ext q
      simp only [mem_union, mem_range, mem_Icc, Nat.lt_succ_iff]
      constructor
      · intro h
        rcases h with hlt | hI
        · exact Nat.le_trans (Nat.le_of_lt hlt) hkn
        · exact hI.2
      · intro hq
        rcases lt_or_ge q k with hlt | hge
        · exact Or.inl hlt
        · exact Or.inr ⟨hge, hq⟩
    have hsplit :
        ∑ q ∈ range (n + 1), (-1 : ℝ) ^ q * (n.choose q : ℝ) =
          ∑ q ∈ range k, (-1 : ℝ) ^ q * (n.choose q : ℝ) +
            ∑ q ∈ Icc k n, (-1 : ℝ) ^ q * (n.choose q : ℝ) := by
      rw [← hunion, sum_union hdisj]
    have hhigh :
        ∑ q ∈ Icc k n, (-1 : ℝ) ^ q * (n.choose q : ℝ) =
          -∑ q ∈ range k, (-1 : ℝ) ^ q * (n.choose q : ℝ) := by
      linarith
    have hneg : -((-1 : ℝ) ^ (k - 1)) = (-1 : ℝ) ^ k := by
      rw [← neg_one_mul, mul_comm, ← pow_succ, Nat.sub_add_cancel hk]
    rw [hhigh, hlow, ← neg_mul, hneg]
  · have hempty : Icc k n = ∅ := Icc_eq_empty_of_lt hkn
    have hch : (n - 1).choose (k - 1) = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.lt_of_succ_le (by omega))
    simp [hempty, hch]

private theorem sum_signed_high_powerset {W : Finset ℕ} {k : ℕ}
    (hn : 1 ≤ W.card) (hk : 1 ≤ k) :
    ∑ S ∈ W.powerset.filter (fun S => k ≤ S.card), (-1 : ℝ) ^ S.card =
      (-1 : ℝ) ^ k * ((W.card - 1).choose (k - 1) : ℝ) := by
  let n := W.card
  have hbi :
      W.powerset.filter (fun S => k ≤ S.card) =
        (Icc k n).biUnion (fun q => W.powersetCard q) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_Icc, mem_powersetCard]
    constructor
    · intro h
      exact ⟨S.card, ⟨h.2, card_le_card h.1⟩, ⟨h.1, rfl⟩⟩
    · intro ⟨q, hq, hS⟩
      exact ⟨hS.1, hS.2 ▸ hq.1⟩
  have hdisj : Set.PairwiseDisjoint (Icc k n : Set ℕ) (fun q => W.powersetCard q) := by
    intro a _ b _ hab
    refine disjoint_left.mpr ?_
    intro S hSa hSb
    exact hab ((mem_powersetCard.mp hSa).2.symm.trans (mem_powersetCard.mp hSb).2)
  rw [hbi, sum_biUnion hdisj]
  have hterm :
      ∑ q ∈ Icc k n, ∑ S ∈ W.powersetCard q, (-1 : ℝ) ^ S.card =
        ∑ q ∈ Icc k n, (-1 : ℝ) ^ q * (n.choose q : ℝ) := by
    refine sum_congr rfl fun q _ => ?_
    have hconst : ∀ S ∈ W.powersetCard q, (-1 : ℝ) ^ S.card = (-1 : ℝ) ^ q := by
      intro S hS
      rw [(mem_powersetCard.mp hS).2]
    rw [sum_congr rfl hconst, sum_const, card_powersetCard, nsmul_eq_mul]
    simp [n, mul_comm]
  rw [hterm]
  exact sum_Icc_signed_choose_high hn hk

/-! ### Binomial comparison and hockey-stick -/

private theorem choose_endpoint_mul_le {n L r : ℕ}
    (_hL : 1 ≤ L) (hr : L ≤ r) (hn : r ≤ n) :
    n.choose (L - 1) * (n - L).choose (r - L) ≤
      r.choose (L - 1) * n.choose r := by
  have hLr : L - 1 ≤ r := (Nat.sub_le L 1).trans hr
  have hmul := Nat.choose_mul (n := n) (k := r) (s := L - 1) hLr
  have hsub : n - (L - 1) = n - L + 1 := by omega
  have hrL : r - (L - 1) = r - L + 1 := by omega
  rw [hsub, hrL] at hmul
  have hsmall : (n - L).choose (r - L) ≤ (n - L + 1).choose (r - L + 1) := by
    set m := n - L
    set kk := r - L
    have hkpos : 0 < kk + 1 := Nat.succ_pos _
    have hid := Nat.add_one_mul_choose_eq m kk
    have hle : kk + 1 ≤ m + 1 := by omega
    have hmul' : m.choose kk * (kk + 1) ≤ m.choose kk * (m + 1) :=
      Nat.mul_le_mul_left _ hle
    have hid' : m.choose kk * (m + 1) = (m + 1).choose (kk + 1) * (kk + 1) := by
      rw [Nat.mul_comm, hid]
    have h2 : m.choose kk * (kk + 1) ≤ (m + 1).choose (kk + 1) * (kk + 1) := by
      rwa [hid'] at hmul'
    exact Nat.le_of_mul_le_mul_right h2 hkpos
  have hleft :
      n.choose (L - 1) * (n - L).choose (r - L) ≤
        n.choose (L - 1) * (n - L + 1).choose (r - L + 1) :=
    Nat.mul_le_mul_left _ hsmall
  calc
    n.choose (L - 1) * (n - L).choose (r - L)
        ≤ n.choose (L - 1) * (n - L + 1).choose (r - L + 1) := hleft
    _ = n.choose r * r.choose (L - 1) := hmul.symm
    _ = r.choose (L - 1) * n.choose r := Nat.mul_comm _ _

private theorem sum_below_choose (U : Finset ℕ) (r : ℕ) :
    ∑ x ∈ U, ((U.filter (fun y => y < x)).card.choose r : ℝ) =
      (U.card.choose (r + 1) : ℝ) := by
  induction U using Finset.induction_on_max with
  | empty =>
    simp
  | insert a s hlt ih =>
    have ha : a ∉ s := notMem_of_forall_lt hlt
    rw [sum_insert ha]
    have hbelow_a : (insert a s).filter (fun y => y < a) = s := by
      ext y
      simp only [mem_filter, mem_insert]
      constructor
      · intro h
        rcases h.1 with rfl | hy
        · exact (lt_irrefl y h.2).elim
        · exact hy
      · intro hy
        exact ⟨Or.inr hy, hlt y hy⟩
    have hbelow_s : ∀ x ∈ s,
        (insert a s).filter (fun y => y < x) = s.filter (fun y => y < x) := by
      intro x hx
      ext y
      simp only [mem_filter, mem_insert]
      constructor
      · intro h
        rcases h.1 with rfl | hy
        · exact absurd h.2 (not_lt.mpr (hlt x hx).le)
        · exact ⟨hy, h.2⟩
      · intro h
        exact ⟨Or.inr h.1, h.2⟩
    rw [hbelow_a]
    have hsum :
        ∑ x ∈ s, (((insert a s).filter (fun y => y < x)).card.choose r : ℝ) =
          ∑ x ∈ s, ((s.filter (fun y => y < x)).card.choose r : ℝ) :=
      sum_congr rfl fun x hx => by rw [hbelow_s x hx]
    rw [hsum, ih, card_insert_of_notMem ha, Nat.choose_succ_succ', Nat.cast_add]

private theorem sum_Icc_add {L r : ℕ} (h : L ≤ r) (f : ℕ → ℝ) :
    ∑ j ∈ Icc L r, f j = ∑ m ∈ range (r - L + 1), f (L + m) := by
  refine sum_nbij' (fun j => j - L) (fun m => L + m) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hjr := mem_Icc.mp hj
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.sub_le_sub_right hjr.2 L
  · intro m hm
    have hm' : m ≤ r - L := Nat.lt_succ_iff.mp (mem_range.mp hm)
    refine mem_Icc.mpr ⟨Nat.le_add_right L m, ?_⟩
    have : L + m ≤ L + (r - L) := Nat.add_le_add_left hm' L
    exact this.trans (by omega)
  · intro j hj
    exact Nat.add_sub_cancel' (mem_Icc.mp hj).1
  · intro m _
    exact Nat.add_sub_cancel_left L m
  · intro j hj
    rw [Nat.add_sub_cancel' (mem_Icc.mp hj).1]

/-! ### Lemma 2.1: endpoint Möbius identity -/

/-- Source: `rounds/round98/03_gpt_observable_transfer_descent.md` Lemma 2.1.
Contract: combinatorial remainder
Audit: GREEN -/
theorem mobiusCoeff_endpoint_eq_zero (L : ℕ) (phi : List ℕ → ℝ) (H : Finset ℕ)
    (hH : H.card < L) :
    mobiusCoeff (endpointObs L phi) H = 0 := by
  unfold mobiusCoeff endpointObs
  refine sum_eq_zero fun J hJ => ?_
  have hJle : J.card ≤ H.card := card_le_card (mem_powerset.mp hJ)
  have : J.card < L := lt_of_le_of_lt hJle hH
  simp [this]

private theorem endpointObs_insert_gt {L : ℕ} {phi : List ℕ → ℝ} {J : Finset ℕ}
    {x : ℕ} (hL : 1 ≤ L) (hlt : ∀ y ∈ J, y < x) :
    endpointObs L phi (insert x J) - endpointObs L phi J =
      if J.card = L - 1 then
        phi ((insert x J).sort (· ≤ ·))
      else 0 := by
  have hx : x ∉ J := notMem_of_forall_lt hlt
  have hcard : (insert x J).card = J.card + 1 := card_insert_of_notMem hx
  have hsort := sort_insert_gt hlt
  have hlenJ : (J.sort (· ≤ ·)).length = J.card := length_sort _
  rcases lt_trichotomy J.card (L - 1) with hltJ | hEq | hgt
  · have hJlt : J.card < L := lt_of_lt_of_le hltJ (Nat.sub_le L 1)
    have hIns : (insert x J).card < L := by
      rw [hcard]
      omega
    simp [endpointObs, hJlt, hIns, hltJ.ne]
  · have hJlt : J.card < L := by
      rw [hEq]
      exact Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hL) Nat.zero_lt_one
    have hIns : ¬ (insert x J).card < L := by
      rw [hcard, hEq]
      omega
    have hlen : (insert x J).card = L := by
      rw [hcard, hEq, Nat.sub_add_cancel hL]
    have htake :
        ((insert x J).sort (· ≤ ·)).take L = (insert x J).sort (· ≤ ·) := by
      have hls : ((insert x J).sort (· ≤ ·)).length = L := by
        rw [length_sort, hlen]
      rw [← hls, List.take_length]
    unfold endpointObs
    rw [if_neg hIns, if_pos hJlt, sub_zero, htake, if_pos hEq]
  · have hJge : L ≤ J.card := by omega
    have hJnot : ¬ J.card < L := not_lt.mpr hJge
    have hIns : ¬ (insert x J).card < L := by
      rw [hcard]
      omega
    have htake :
        ((insert x J).sort (· ≤ ·)).take L = (J.sort (· ≤ ·)).take L := by
      rw [hsort]
      exact List.take_append_of_le_length (by simpa [hlenJ] using hJge)
    simp [endpointObs, hJnot, hIns, htake, hgt.ne.symm]

/-- Source: `rounds/round98/03_gpt_observable_transfer_descent.md` Lemma 2.1 (2.1).
Contract: combinatorial remainder
Audit: GREEN -/
theorem mobiusCoeff_endpoint (L : ℕ) (phi : List ℕ → ℝ) (H : Finset ℕ)
    (hL : 1 ≤ L) (hH : L ≤ H.card) :
    mobiusCoeff (endpointObs L phi) H =
      (-1 : ℝ) ^ (H.card - L) *
        ∑ J ∈ (H.erase (H.max' (card_pos_of_one_le_card hL hH))).powersetCard (L - 1),
          phi ((insert (H.max' (card_pos_of_one_le_card hL hH)) J).sort (· ≤ ·)) := by
  have hHne : H.Nonempty := card_pos_of_one_le_card hL hH
  set x := H.max' hHne
  have hx : x ∈ H := max'_mem _ _
  have hle_max := le_max_self hHne
  have hHins : H = insert x (H.erase x) := (insert_erase hx).symm
  have hxnot : x ∉ H.erase x := notMem_erase x H
  have hcard_erase : (H.erase x).card = H.card - 1 := card_erase_of_mem hx
  have hpos : 1 ≤ H.card := hL.trans hH
  unfold mobiusCoeff
  rw [hHins, sum_powerset_insert hxnot]
  have hlt_erase : ∀ y ∈ H.erase x, y < x := fun y hy =>
    lt_of_le_of_ne (hle_max y (mem_of_mem_erase hy)) (ne_of_mem_erase hy)
  have hdiff :
      ∑ J ∈ (H.erase x).powerset,
          ((-1 : ℝ) ^ ((insert x (H.erase x)).card - J.card) * endpointObs L phi J +
            (-1 : ℝ) ^ ((insert x (H.erase x)).card - (insert x J).card) *
              endpointObs L phi (insert x J)) =
        ∑ J ∈ (H.erase x).powerset,
          (-1 : ℝ) ^ (H.card - 1 - J.card) *
            (endpointObs L phi (insert x J) - endpointObs L phi J) := by
    refine sum_congr rfl fun J hJ => ?_
    have hJsub : J ⊆ H.erase x := mem_powerset.mp hJ
    have hxJ : x ∉ J := fun hy => hxnot (hJsub hy)
    have hJc : J.card ≤ H.card - 1 := by
      rw [← hcard_erase]
      exact card_le_card hJsub
    have hHcard : (insert x (H.erase x)).card = H.card := by
      rw [insert_erase hx]
    have hinsc : (insert x J).card = J.card + 1 := card_insert_of_notMem hxJ
    have hpow1 : (insert x (H.erase x)).card - J.card = H.card - 1 - J.card + 1 := by
      omega
    have hpow2 : (insert x (H.erase x)).card - (insert x J).card = H.card - 1 - J.card := by
      omega
    rw [hHcard] at hpow1 hpow2 ⊢
    have h1 : (-1 : ℝ) ^ (H.card - J.card) =
        -((-1 : ℝ) ^ (H.card - 1 - J.card)) := by
      rw [hpow1, pow_succ, mul_neg_one]
    have h2 : (-1 : ℝ) ^ (H.card - (insert x J).card) =
        (-1 : ℝ) ^ (H.card - 1 - J.card) := by
      rw [hpow2]
    rw [h1, h2]
    ring
  rw [← sum_add_distrib]
  rw [hdiff]
  have honly :
      ∑ J ∈ (H.erase x).powerset,
          (-1 : ℝ) ^ (H.card - 1 - J.card) *
            (endpointObs L phi (insert x J) - endpointObs L phi J) =
        ∑ J ∈ (H.erase x).powersetCard (L - 1),
          (-1 : ℝ) ^ (H.card - L) * phi ((insert x J).sort (· ≤ ·)) := by
    have hsplit :=
      (sum_filter_add_sum_filter_not (s := (H.erase x).powerset)
        (p := fun J => J.card = L - 1)
        (f := fun J =>
          (-1 : ℝ) ^ (H.card - 1 - J.card) *
            (endpointObs L phi (insert x J) - endpointObs L phi J))).symm
    have hpos :
        ∑ J ∈ (H.erase x).powerset.filter (fun J => J.card = L - 1),
            (-1 : ℝ) ^ (H.card - 1 - J.card) *
              (endpointObs L phi (insert x J) - endpointObs L phi J) =
          ∑ J ∈ (H.erase x).powersetCard (L - 1),
            (-1 : ℝ) ^ (H.card - L) * phi ((insert x J).sort (· ≤ ·)) := by
      have hfilt :
          (H.erase x).powerset.filter (fun J => J.card = L - 1) =
            (H.erase x).powersetCard (L - 1) := by
        simp [powersetCard_eq_filter]
      rw [hfilt]
      refine sum_congr rfl fun J hJ => ?_
      have hJc : J.card = L - 1 := (mem_powersetCard.mp hJ).2
      have hJsub : J ⊆ H.erase x := (mem_powersetCard.mp hJ).1
      have hlt : ∀ y ∈ J, y < x := fun y hy => hlt_erase y (hJsub hy)
      have hsub := endpointObs_insert_gt (L := L) (phi := phi) (J := J) (x := x) hL hlt
      rw [hsub, if_pos hJc]
      have hsign : H.card - 1 - J.card = H.card - L := by omega
      rw [hsign]
    have hneg :
        ∑ J ∈ (H.erase x).powerset.filter (fun J => ¬ J.card = L - 1),
            (-1 : ℝ) ^ (H.card - 1 - J.card) *
              (endpointObs L phi (insert x J) - endpointObs L phi J) = 0 := by
      refine sum_eq_zero fun J hJ => ?_
      have hJsub : J ⊆ H.erase x := mem_powerset.mp (mem_filter.mp hJ).1
      have hne : J.card ≠ L - 1 := (mem_filter.mp hJ).2
      have hlt : ∀ y ∈ J, y < x := fun y hy => hlt_erase y (hJsub hy)
      have hsub := endpointObs_insert_gt (L := L) (phi := phi) (J := J) (x := x) hL hlt
      rw [hsub, if_neg hne, mul_zero]
    have hsum := hsplit
    rw [hpos, hneg, add_zero] at hsum
    exact hsum
  rw [honly, mul_sum, erase_insert hxnot]
  refine sum_congr rfl fun J _ => ?_
  have hcardH : (insert x (H.erase x)).card = H.card := by
    rw [insert_erase hx]
  rw [hcardH, mul_comm]

/-- Source: `rounds/round98/03_gpt_observable_transfer_descent.md` Lemma 2.1 (2.2).
Contract: combinatorial remainder
Audit: GREEN -/
theorem abs_mobiusCoeff_endpoint_le (L : ℕ) (phi : List ℕ → ℝ) (H : Finset ℕ)
    (hL : 1 ≤ L) (hφ : ∀ t, |phi t| ≤ 1) :
    |mobiusCoeff (endpointObs L phi) H| ≤ ((H.card - 1).choose (L - 1) : ℝ) := by
  rcases lt_or_ge H.card L with hlt | hH
  · rw [mobiusCoeff_endpoint_eq_zero L phi H hlt, abs_zero]
    exact Nat.cast_nonneg _
  · have hHne := card_pos_of_one_le_card hL hH
    rw [mobiusCoeff_endpoint L phi H hL hH, abs_mul, abs_neg_one_pow, one_mul]
    have hbound :=
      calc
        |∑ J ∈ (H.erase (H.max' hHne)).powersetCard (L - 1),
            phi ((insert (H.max' hHne) J).sort (· ≤ ·))|
            ≤ ∑ J ∈ (H.erase (H.max' hHne)).powersetCard (L - 1),
                |phi ((insert (H.max' hHne) J).sort (· ≤ ·))| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ J ∈ (H.erase (H.max' hHne)).powersetCard (L - 1), (1 : ℝ) :=
          sum_le_sum fun _ _ => hφ _
        _ = ((H.erase (H.max' hHne)).card.choose (L - 1) : ℝ) := by
          simp [sum_const, card_powersetCard, nsmul_eq_mul]
        _ = ((H.card - 1).choose (L - 1) : ℝ) := by
          rw [card_erase_of_mem (max'_mem _ _)]
    exact hbound

/-! ### Lemma 3.1: specialized truncation remainder -/

private theorem endpoint_sub_truncPoly (L : ℕ) (phi : List ℕ → ℝ) (r : ℕ)
    (U : Finset ℕ) :
    endpointObs L phi U - truncPoly (endpointObs L phi) r U =
      ∑ H ∈ U.powerset.filter (fun H => r < H.card),
        mobiusCoeff (endpointObs L phi) H := by
  have hfull := sum_mobiusCoeff (endpointObs L phi) U
  have hdisj :
      Disjoint (U.powerset.filter (fun H => H.card ≤ r))
        (U.powerset.filter (fun H => r < H.card)) :=
    disjoint_left.mpr fun H hH hH' =>
      (Nat.not_lt.mpr (mem_filter.mp hH).2) (mem_filter.mp hH').2
  have hunion :
      U.powerset.filter (fun H => H.card ≤ r) ∪
          U.powerset.filter (fun H => r < H.card) = U.powerset := by
    ext H
    simp only [mem_union, mem_filter, mem_powerset]
    constructor
    · intro h
      rcases h with h | h <;> exact h.1
    · intro hU
      rcases le_or_gt H.card r with hle | hgt
      · exact Or.inl ⟨hU, hle⟩
      · exact Or.inr ⟨hU, hgt⟩
  have hsum :=
    sum_union (s₁ := U.powerset.filter (fun H => H.card ≤ r))
      (s₂ := U.powerset.filter (fun H => r < H.card))
      (f := mobiusCoeff (endpointObs L phi)) hdisj
  have :
      truncPoly (endpointObs L phi) r U +
        ∑ H ∈ U.powerset.filter (fun H => r < H.card),
          mobiusCoeff (endpointObs L phi) H =
        endpointObs L phi U := by
    rw [truncPoly, ← hsum, hunion, hfull]
  linarith

private theorem erase_eq_below {H : Finset ℕ} (hHne : H.Nonempty) :
    H.erase (H.max' hHne) = H.filter (fun y => y < H.max' hHne) := by
  ext y
  simp only [mem_erase, mem_filter]
  constructor
  · intro h
    exact ⟨h.2, lt_of_le_of_ne (le_max_self hHne y h.2) h.1⟩
  · intro h
    exact ⟨ne_of_lt h.2, h.1⟩

private theorem high_card_eq_biUnion {U : Finset ℕ} {r : ℕ} :
    U.powerset.filter (fun H => r < H.card) =
      U.biUnion fun x =>
        ((U.filter (fun y => y < x)).powerset.filter (fun G => r ≤ G.card)).image
          (insert x) := by
  ext H
  constructor
  · intro hH
    obtain ⟨hHU, hcard⟩ := mem_filter.mp hH
    have hHne : H.Nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le r) hcard)
    set x := H.max' hHne
    have hxU : x ∈ U := mem_powerset.mp hHU (max'_mem _ _)
    have hG : H.erase x ⊆ U.filter (fun y => y < x) := by
      intro y hy
      have hyH : y ∈ H := mem_of_mem_erase hy
      have hyx : y ≠ x := ne_of_mem_erase hy
      exact mem_filter.mpr ⟨mem_powerset.mp hHU hyH,
        lt_of_le_of_ne (le_max_self hHne y hyH) hyx⟩
    have hGcard : r ≤ (H.erase x).card := by
      rw [card_erase_of_mem (max'_mem _ _)]
      omega
    refine mem_biUnion.mpr ⟨x, hxU, mem_image.mpr
      ⟨H.erase x, mem_filter.mpr ⟨mem_powerset.mpr hG, hGcard⟩, insert_erase (max'_mem _ _)⟩⟩
  · intro hH
    obtain ⟨x, hxU, hIm⟩ := mem_biUnion.mp hH
    obtain ⟨G, hG, rfl⟩ := mem_image.mp hIm
    have hGbel : G ⊆ U.filter (fun y => y < x) := mem_powerset.mp (mem_filter.mp hG).1
    have hGcard : r ≤ G.card := (mem_filter.mp hG).2
    have hlt : ∀ y ∈ G, y < x := fun y hy => (mem_filter.mp (hGbel hy)).2
    have hxG : x ∉ G := notMem_of_forall_lt hlt
    have hsub : insert x G ⊆ U :=
      insert_subset hxU (hGbel.trans (fun t ht => (mem_filter.mp ht).1))
    have hcard : r < (insert x G).card := by
      rw [card_insert_of_notMem hxG]
      omega
    exact mem_filter.mpr ⟨mem_powerset.mpr hsub, hcard⟩

private theorem high_card_pairwise {U : Finset ℕ} {r : ℕ} :
    Set.PairwiseDisjoint (U : Set ℕ) fun x =>
      ((U.filter (fun y => y < x)).powerset.filter (fun G => r ≤ G.card)).image
        (insert x) := by
  intro x hx x' hx' hne
  refine disjoint_left.mpr ?_
  intro H hH hH'
  obtain ⟨G, hG, rfl⟩ := mem_image.mp hH
  obtain ⟨G', hG', hEq⟩ := mem_image.mp hH'
  have hlt : ∀ y ∈ G, y < x := fun y hy =>
    (mem_filter.mp ((mem_powerset.mp (mem_filter.mp hG).1) hy)).2
  have hlt' : ∀ y ∈ G', y < x' := fun y hy =>
    (mem_filter.mp ((mem_powerset.mp (mem_filter.mp hG').1) hy)).2
  have hmax : x = x' := by
    apply le_antisymm
    · have hxmem : x ∈ insert x' G' := hEq ▸ mem_insert_self x G
      rcases mem_insert.mp hxmem with hxx | hxG'
      · exact le_of_eq hxx
      · exact (hlt' x hxG').le
    · have hx'mem : x' ∈ insert x G := hEq.symm ▸ mem_insert_self x' G'
      rcases mem_insert.mp hx'mem with hxx | hxG
      · exact le_of_eq hxx
      · exact (hlt x' hxG).le
  exact hne hmax

private theorem disjoint_of_sdiff_subset {J S B : Finset ℕ}
    (hS : S ⊆ B \ J) : Disjoint J S :=
  disjoint_left.mpr fun _ haJ haS => (mem_sdiff.mp (hS haS)).2 haJ

private theorem filter_supset_eq_image {B J : Finset ℕ} {r L : ℕ}
    (hJ : J ⊆ B) (hJc : J.card = L - 1) (hL : 1 ≤ L) (_hr : L ≤ r) :
    B.powerset.filter (fun G => r ≤ G.card ∧ J ⊆ G) =
      ((B \ J).powerset.filter (fun S => r - L + 1 ≤ S.card)).image
        (fun S => J ∪ S) := by
  ext G
  constructor
  · intro hG
    have hG' := mem_filter.mp hG
    have hGB : G ⊆ B := mem_powerset.mp hG'.1
    have hcard : r ≤ G.card := hG'.2.1
    have hJG : J ⊆ G := hG'.2.2
    have hdisj : Disjoint J (G \ J) := disjoint_sdiff
    have hGeq : G = J ∪ (G \ J) := (union_sdiff_of_subset hJG).symm
    have hScard : r - L + 1 ≤ (G \ J).card := by
      have : G.card = (L - 1) + (G \ J).card := by
        rw [← hJc, ← card_union_of_disjoint hdisj, union_sdiff_of_subset hJG]
      omega
    exact mem_image.mpr ⟨G \ J,
      mem_filter.mpr ⟨mem_powerset.mpr (sdiff_subset_sdiff hGB Subset.rfl), hScard⟩,
      hGeq.symm⟩
  · intro hG
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hG
    have hSB : S ⊆ B \ J := mem_powerset.mp (mem_filter.mp hS).1
    have hScard : r - L + 1 ≤ S.card := (mem_filter.mp hS).2
    have hdisj := disjoint_of_sdiff_subset hSB
    have hGB : J ∪ S ⊆ B := union_subset hJ (hSB.trans sdiff_subset)
    have hcard : r ≤ (J ∪ S).card := by
      rw [card_union_of_disjoint hdisj, hJc]
      omega
    exact mem_filter.mpr ⟨mem_powerset.mpr hGB, ⟨hcard, subset_union_left⟩⟩

private theorem sum_high_insert_eq (L r : ℕ) (phi : List ℕ → ℝ) (U : Finset ℕ)
    (x : ℕ) (hL : 1 ≤ L) (hr : L ≤ r) :
    ∑ G ∈ (U.filter (fun y => y < x)).powerset.filter (fun G => r ≤ G.card),
        mobiusCoeff (endpointObs L phi) (insert x G) =
      ∑ J ∈ (U.filter (fun y => y < x)).powersetCard (L - 1),
        phi ((insert x J).sort (· ≤ ·)) *
          ∑ S ∈ ((U.filter (fun y => y < x)) \ J).powerset.filter
              (fun S => r - L + 1 ≤ S.card),
            (-1 : ℝ) ^ S.card := by
  set B := U.filter (fun y => y < x)
  have hEqG :
      ∑ G ∈ B.powerset.filter (fun G => r ≤ G.card),
          mobiusCoeff (endpointObs L phi) (insert x G) =
        ∑ G ∈ B.powerset.filter (fun G => r ≤ G.card),
          ∑ J ∈ G.powersetCard (L - 1),
            (-1 : ℝ) ^ (G.card + 1 - L) *
              phi ((insert x J).sort (· ≤ ·)) := by
    refine sum_congr rfl fun G hG => ?_
    have hGbel : G ⊆ B := mem_powerset.mp (mem_filter.mp hG).1
    have hGcard : r ≤ G.card := (mem_filter.mp hG).2
    have hlt : ∀ y ∈ G, y < x := fun y hy => (mem_filter.mp (hGbel hy)).2
    have hxG : x ∉ G := notMem_of_forall_lt hlt
    have hHcard : L ≤ (insert x G).card := by
      rw [card_insert_of_notMem hxG]
      omega
    have hmax := max'_insert_gt hlt
    have hmax' : (insert x G).max' (card_pos_of_one_le_card hL hHcard) = x := by
      convert hmax
    rw [mobiusCoeff_endpoint L phi (insert x G) hL hHcard, hmax', erase_insert hxG,
      card_insert_of_notMem hxG, mul_sum]
  rw [hEqG]
  have hcomm :=
    sum_comm' (s := B.powerset.filter (fun G => r ≤ G.card))
      (t := fun G => G.powersetCard (L - 1))
      (t' := B.powersetCard (L - 1))
      (s' := fun J => B.powerset.filter (fun G => r ≤ G.card ∧ J ⊆ G))
      (h := by
        intro G J
        constructor
        · intro h
          have hG := mem_filter.mp h.1
          have hJ := mem_powersetCard.mp h.2
          exact ⟨mem_filter.mpr ⟨hG.1, ⟨hG.2, hJ.1⟩⟩,
            mem_powersetCard.mpr ⟨hJ.1.trans (mem_powerset.mp hG.1), hJ.2⟩⟩
        · intro h
          have hG := mem_filter.mp h.1
          have hJ := mem_powersetCard.mp h.2
          exact ⟨mem_filter.mpr ⟨hG.1, hG.2.1⟩, mem_powersetCard.mpr ⟨hG.2.2, hJ.2⟩⟩)
      (f := fun G J =>
        (-1 : ℝ) ^ (G.card + 1 - L) * phi ((insert x J).sort (· ≤ ·)))
  rw [hcomm]
  refine sum_congr rfl fun J hJ => ?_
  have hJB : J ⊆ B := (mem_powersetCard.mp hJ).1
  have hJc : J.card = L - 1 := (mem_powersetCard.mp hJ).2
  rw [filter_supset_eq_image hJB hJc hL hr]
  have hinj : Set.InjOn (fun S => J ∪ S)
      (↑((B \ J).powerset.filter (fun S => r - L + 1 ≤ S.card)) : Set (Finset ℕ)) := by
    intro S hS S' hS' hEq
    have hdisj := disjoint_of_sdiff_subset (mem_powerset.mp (mem_filter.mp hS).1)
    have hdisj' := disjoint_of_sdiff_subset (mem_powerset.mp (mem_filter.mp hS').1)
    have hEq' : J ∪ S = J ∪ S' := hEq
    calc
      S = (J ∪ S) \ J := (union_sdiff_cancel_left hdisj).symm
      _ = (J ∪ S') \ J := by rw [hEq']
      _ = S' := union_sdiff_cancel_left hdisj'
  rw [sum_image hinj]
  have hterm :
      ∀ S ∈ (B \ J).powerset.filter (fun S => r - L + 1 ≤ S.card),
        (-1 : ℝ) ^ ((J ∪ S).card + 1 - L) * phi ((insert x J).sort (· ≤ ·)) =
          phi ((insert x J).sort (· ≤ ·)) * (-1 : ℝ) ^ S.card := by
    intro S hS
    have hSB : S ⊆ B \ J := mem_powerset.mp (mem_filter.mp hS).1
    have hdisj := disjoint_of_sdiff_subset hSB
    have hGcard : (J ∪ S).card = (L - 1) + S.card := by
      rw [card_union_of_disjoint hdisj, hJc]
    have hsign : (-1 : ℝ) ^ ((J ∪ S).card + 1 - L) = (-1 : ℝ) ^ S.card := by
      have : (L - 1) + S.card + 1 - L = S.card := by omega
      rw [hGcard, this]
    rw [hsign]
    ring
  rw [sum_congr rfl hterm, mul_sum]

private theorem abs_sum_high_insert_le (L r : ℕ) (phi : List ℕ → ℝ) (U : Finset ℕ)
    (x : ℕ) (hφ : ∀ t, |phi t| ≤ 1) (hL : 1 ≤ L) (hr : L ≤ r)
    (hB : r ≤ (U.filter (fun y => y < x)).card) :
    |∑ G ∈ (U.filter (fun y => y < x)).powerset.filter (fun G => r ≤ G.card),
        mobiusCoeff (endpointObs L phi) (insert x G)| ≤
      ((U.filter (fun y => y < x)).card.choose (L - 1) : ℝ) *
        (((U.filter (fun y => y < x)).card - L).choose (r - L) : ℝ) := by
  set B := U.filter (fun y => y < x)
  rw [sum_high_insert_eq L r phi U x hL hr]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hk : 1 ≤ r - L + 1 := Nat.succ_pos _
  have hpt :
      ∀ J ∈ B.powersetCard (L - 1),
        |phi ((insert x J).sort (· ≤ ·)) *
            ∑ S ∈ (B \ J).powerset.filter (fun S => r - L + 1 ≤ S.card),
              (-1 : ℝ) ^ S.card| ≤
          ((B.card - L).choose (r - L) : ℝ) := by
    intro J hJ
    have hJB : J ⊆ B := (mem_powersetCard.mp hJ).1
    have hJc : J.card = L - 1 := (mem_powersetCard.mp hJ).2
    have hWcard : (B \ J).card = B.card - (L - 1) := by
      rw [card_sdiff_of_subset hJB, hJc]
    have hWpos : 1 ≤ (B \ J).card := by omega
    have hsigned := sum_signed_high_powerset (W := B \ J) (k := r - L + 1) hWpos hk
    have hpred : (B \ J).card - 1 = B.card - L := by omega
    have hkk : r - L + 1 - 1 = r - L := Nat.add_sub_cancel _ _
    have hphi : |phi ((insert x J).sort (· ≤ ·))| ≤ 1 := hφ _
    rw [abs_mul]
    have hmul :=
      mul_le_of_le_one_left
        (abs_nonneg
          (∑ S ∈ (B \ J).powerset.filter (fun S => r - L + 1 ≤ S.card),
            (-1 : ℝ) ^ S.card))
        hphi
    refine hmul.trans ?_
    rw [hsigned, abs_mul, abs_neg_one_pow, one_mul, hkk, hpred,
      abs_of_nonneg (Nat.cast_nonneg _)]
  have hsum := sum_le_sum hpt
  have hcnt :
      ∑ J ∈ B.powersetCard (L - 1), ((B.card - L).choose (r - L) : ℝ) =
        (B.card.choose (L - 1) : ℝ) * ((B.card - L).choose (r - L) : ℝ) := by
    simp [sum_const, card_powersetCard, nsmul_eq_mul]
  exact hsum.trans (le_of_eq hcnt)

/-- Source: `rounds/round98/03_gpt_observable_transfer_descent.md` Lemma 3.1.
Contract: combinatorial remainder
Audit: GREEN -/
theorem truncPoly_endpoint_remainder (L : ℕ) (phi : List ℕ → ℝ) {r : ℕ}
    {U : Finset ℕ} (hφ : ∀ t, |phi t| ≤ 1) (hL : 1 ≤ L) (hr : L ≤ r) :
    |endpointObs L phi U - truncPoly (endpointObs L phi) r U| ≤
      (r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ) := by
  rcases le_or_gt U.card r with hN | hN
  · have hf : ∀ s, |endpointObs L phi s| ≤ 1 := fun s => abs_endpointObs_le L phi s hφ
    have heq := truncPoly_eq_of_card_le (endpointObs L phi) hf hN
    have hch : U.card.choose (r + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.succ_le_succ hN)
    simp [heq, hch]
  · have hdiff := endpoint_sub_truncPoly L phi r U
    rw [hdiff, high_card_eq_biUnion, sum_biUnion high_card_pairwise]
    have hinj : ∀ x ∈ U,
        Set.InjOn (insert x)
          (↑((U.filter (fun y => y < x)).powerset.filter (fun G => r ≤ G.card)) :
            Set (Finset ℕ)) := by
      intro x _ G hG G' hG' hEq
      have hlt : ∀ y ∈ G, y < x := fun y hy =>
        (mem_filter.mp ((mem_powerset.mp (mem_filter.mp hG).1) hy)).2
      have hlt' : ∀ y ∈ G', y < x := fun y hy =>
        (mem_filter.mp ((mem_powerset.mp (mem_filter.mp hG').1) hy)).2
      have hxG : x ∉ G := notMem_of_forall_lt hlt
      have hxG' : x ∉ G' := notMem_of_forall_lt hlt'
      have hEq' : insert x G = insert x G' := hEq
      calc
        G = (insert x G).erase x := (erase_insert hxG).symm
        _ = (insert x G').erase x := by rw [hEq']
        _ = G' := erase_insert hxG'
    have hrewrite :
        ∑ x ∈ U, ∑ H ∈ ((U.filter (fun y => y < x)).powerset.filter
            (fun G => r ≤ G.card)).image (insert x),
            mobiusCoeff (endpointObs L phi) H =
          ∑ x ∈ U, ∑ G ∈ (U.filter (fun y => y < x)).powerset.filter
              (fun G => r ≤ G.card),
              mobiusCoeff (endpointObs L phi) (insert x G) := by
      refine sum_congr rfl fun x hx => sum_image (hinj x hx)
    rw [hrewrite]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hsplit :=
      (sum_filter_add_sum_filter_not (s := U)
        (p := fun x => r ≤ (U.filter (fun y => y < x)).card)
        (f := fun x =>
          |∑ G ∈ (U.filter (fun y => y < x)).powerset.filter (fun G => r ≤ G.card),
              mobiusCoeff (endpointObs L phi) (insert x G)|)).symm
    have hlow :
        ∑ x ∈ U.filter (fun x => ¬ r ≤ (U.filter (fun y => y < x)).card),
            |∑ G ∈ (U.filter (fun y => y < x)).powerset.filter
                (fun G => r ≤ G.card),
                mobiusCoeff (endpointObs L phi) (insert x G)| = 0 := by
      refine sum_eq_zero fun x hx => ?_
      have hlt : (U.filter (fun y => y < x)).card < r :=
        lt_of_not_ge (mem_filter.mp hx).2
      have hempty :
          (U.filter (fun y => y < x)).powerset.filter (fun G => r ≤ G.card) = ∅ := by
        ext G
        simp only [mem_filter, mem_powerset, notMem_empty, iff_false, not_and]
        intro hGB hcard
        exact (not_le.mpr ((card_le_card hGB).trans_lt hlt)) hcard
      simp [hempty]
    have hpos :
        ∑ x ∈ U.filter (fun x => r ≤ (U.filter (fun y => y < x)).card),
            |∑ G ∈ (U.filter (fun y => y < x)).powerset.filter
                (fun G => r ≤ G.card),
                mobiusCoeff (endpointObs L phi) (insert x G)| ≤
          ∑ x ∈ U.filter (fun x => r ≤ (U.filter (fun y => y < x)).card),
            ((U.filter (fun y => y < x)).card.choose (L - 1) : ℝ) *
              (((U.filter (fun y => y < x)).card - L).choose (r - L) : ℝ) :=
      sum_le_sum fun x hx =>
        abs_sum_high_insert_le L r phi U x hφ hL hr (mem_filter.mp hx).2
    have hsumU :
        ∑ x ∈ U, |∑ G ∈ (U.filter (fun y => y < x)).powerset.filter
            (fun G => r ≤ G.card),
            mobiusCoeff (endpointObs L phi) (insert x G)| =
          ∑ x ∈ U.filter (fun x => r ≤ (U.filter (fun y => y < x)).card),
            |∑ G ∈ (U.filter (fun y => y < x)).powerset.filter
                (fun G => r ≤ G.card),
                mobiusCoeff (endpointObs L phi) (insert x G)| := by
      rw [hsplit, hlow, add_zero]
    rw [hsumU]
    refine hpos.trans ?_
    have hpt :
        ∀ x ∈ U.filter (fun x => r ≤ (U.filter (fun y => y < x)).card),
          ((U.filter (fun y => y < x)).card.choose (L - 1) : ℝ) *
              (((U.filter (fun y => y < x)).card - L).choose (r - L) : ℝ) ≤
            (r.choose (L - 1) : ℝ) *
              ((U.filter (fun y => y < x)).card.choose r : ℝ) := by
      intro x hx
      exact_mod_cast choose_endpoint_mul_le hL hr (mem_filter.mp hx).2
    have h1 := sum_le_sum hpt
    have hsubset :
        U.filter (fun x => r ≤ (U.filter (fun y => y < x)).card) ⊆ U :=
      fun t ht => (mem_filter.mp ht).1
    have hnonneg :
        ∀ x ∈ U, x ∉ U.filter (fun x => r ≤ (U.filter (fun y => y < x)).card) →
          0 ≤ (r.choose (L - 1) : ℝ) *
            ((U.filter (fun y => y < x)).card.choose r : ℝ) := fun _ _ _ => by
      positivity
    have h2 := sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    have hfactor :
        ∑ x ∈ U, (r.choose (L - 1) : ℝ) *
            ((U.filter (fun y => y < x)).card.choose r : ℝ) =
          (r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ) := by
      rw [← mul_sum, sum_below_choose]
    exact (h1.trans h2).trans (le_of_eq hfactor)

/-! ### Inclusion moments and transfer -/

private theorem filter_card_subset_eq {V U : Finset ℕ} {j : ℕ}
    (hU : U ⊆ V) :
    (V.powerset.filter (fun H => H.card = j)).filter (fun H => H ⊆ U) =
      U.powersetCard j := by
  ext H
  simp only [mem_filter, mem_powerset, mem_powersetCard]
  constructor
  · intro h
    exact ⟨h.2, h.1.2⟩
  · intro h
    exact ⟨⟨h.1.trans hU, h.2⟩, h.1⟩

/-- Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §4.
Contract: combinatorial remainder
Audit: GREEN -/
theorem inclusionMoment_eq_sum_inclusionProb (V : Finset ℕ) (μ : Finset ℕ → ℝ)
    (j : ℕ) :
    inclusionMoment V μ j =
      ∑ H ∈ V.powerset.filter (fun H => H.card = j), inclusionProb V μ H := by
  have hinner :
      ∀ U ∈ V.powerset,
        μ U * (U.card.choose j : ℝ) =
          ∑ H ∈ V.powerset.filter (fun H => H.card = j),
            (if H ⊆ U then μ U else (0 : ℝ)) := by
    intro U hU
    have hUsub : U ⊆ V := mem_powerset.mp hU
    calc
      μ U * (U.card.choose j : ℝ)
          = ∑ H ∈ U.powersetCard j, μ U := by
            rw [sum_const, card_powersetCard, nsmul_eq_mul, mul_comm]
      _ = ∑ H ∈ (V.powerset.filter (fun H => H.card = j)).filter (fun H => H ⊆ U),
            μ U := by
        rw [← filter_card_subset_eq hUsub]
      _ = ∑ H ∈ V.powerset.filter (fun H => H.card = j),
            (if H ⊆ U then μ U else (0 : ℝ)) :=
        sum_filter (s := V.powerset.filter (fun H => H.card = j))
          (p := fun H => H ⊆ U) (f := fun _ => μ U)
  unfold inclusionMoment
  have hswap :
      ∑ U ∈ V.powerset,
          ∑ H ∈ V.powerset.filter (fun H => H.card = j),
            (if H ⊆ U then μ U else (0 : ℝ)) =
        ∑ H ∈ V.powerset.filter (fun H => H.card = j),
          ∑ U ∈ V.powerset, (if H ⊆ U then μ U else (0 : ℝ)) :=
    sum_comm
  calc
    ∑ U ∈ V.powerset, μ U * (U.card.choose j : ℝ)
        = ∑ U ∈ V.powerset,
            ∑ H ∈ V.powerset.filter (fun H => H.card = j),
              (if H ⊆ U then μ U else (0 : ℝ)) :=
      sum_congr rfl hinner
    _ = ∑ H ∈ V.powerset.filter (fun H => H.card = j),
          ∑ U ∈ V.powerset, (if H ⊆ U then μ U else (0 : ℝ)) := hswap
    _ = ∑ H ∈ V.powerset.filter (fun H => H.card = j), inclusionProb V μ H := rfl

private theorem inclusionMoment_le_add (V : Finset ℕ) (μ ν : Finset ℕ → ℝ)
    (j : ℕ) :
    inclusionMoment V μ j ≤
      summedAbsDelta V μ ν j + inclusionMoment V ν j := by
  rw [inclusionMoment_eq_sum_inclusionProb, inclusionMoment_eq_sum_inclusionProb]
  have hpt :
      ∀ H ∈ V.powerset.filter (fun H => H.card = j),
        inclusionProb V μ H ≤
          |inclusionProb V μ H - inclusionProb V ν H| + inclusionProb V ν H := by
    intro H _
    linarith [le_abs_self (inclusionProb V μ H - inclusionProb V ν H)]
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  rfl

private theorem filter_le_subset_eq {V U : Finset ℕ} {r : ℕ}
    (hU : U ⊆ V) :
    (V.powerset.filter (fun H => H.card ≤ r)).filter (fun H => H ⊆ U) =
      U.powerset.filter (fun H => H.card ≤ r) := by
  ext H
  simp only [mem_filter, mem_powerset]
  constructor
  · intro h
    exact ⟨h.2, h.1.2⟩
  · intro h
    exact ⟨⟨h.1.trans hU, h.2⟩, h.1⟩

private theorem sum_sub_truncPoly_eq (V : Finset ℕ) (μ ν : Finset ℕ → ℝ)
    (L r : ℕ) (phi : List ℕ → ℝ) :
    ∑ U ∈ V.powerset, (μ U - ν U) * truncPoly (endpointObs L phi) r U =
      ∑ H ∈ V.powerset.filter (fun H => H.card ≤ r),
        mobiusCoeff (endpointObs L phi) H *
          (inclusionProb V μ H - inclusionProb V ν H) := by
  have hinner :
      ∀ U ∈ V.powerset,
        (μ U - ν U) * truncPoly (endpointObs L phi) r U =
          ∑ H ∈ V.powerset.filter (fun H => H.card ≤ r),
            (if H ⊆ U then (μ U - ν U) * mobiusCoeff (endpointObs L phi) H
              else (0 : ℝ)) := by
    intro U hU
    have hUsub : U ⊆ V := mem_powerset.mp hU
    unfold truncPoly
    rw [mul_sum]
    calc
      ∑ H ∈ U.powerset.filter (fun H => H.card ≤ r),
          (μ U - ν U) * mobiusCoeff (endpointObs L phi) H
          = ∑ H ∈ (V.powerset.filter (fun H => H.card ≤ r)).filter (fun H => H ⊆ U),
              (μ U - ν U) * mobiusCoeff (endpointObs L phi) H := by
        rw [← filter_le_subset_eq hUsub]
      _ = ∑ H ∈ V.powerset.filter (fun H => H.card ≤ r),
            (if H ⊆ U then (μ U - ν U) * mobiusCoeff (endpointObs L phi) H
              else (0 : ℝ)) :=
        sum_filter (s := V.powerset.filter (fun H => H.card ≤ r))
          (p := fun H => H ⊆ U)
          (f := fun H => (μ U - ν U) * mobiusCoeff (endpointObs L phi) H)
  have hswap :
      ∑ U ∈ V.powerset,
          ∑ H ∈ V.powerset.filter (fun H => H.card ≤ r),
            (if H ⊆ U then (μ U - ν U) * mobiusCoeff (endpointObs L phi) H
              else (0 : ℝ)) =
        ∑ H ∈ V.powerset.filter (fun H => H.card ≤ r),
          ∑ U ∈ V.powerset,
            (if H ⊆ U then (μ U - ν U) * mobiusCoeff (endpointObs L phi) H
              else (0 : ℝ)) :=
    sum_comm
  rw [sum_congr rfl hinner, hswap]
  refine sum_congr rfl fun H _ => ?_
  have hconst :
      ∑ U ∈ V.powerset,
          (if H ⊆ U then (μ U - ν U) * mobiusCoeff (endpointObs L phi) H
            else (0 : ℝ)) =
        mobiusCoeff (endpointObs L phi) H *
          ∑ U ∈ V.powerset, (if H ⊆ U then μ U - ν U else (0 : ℝ)) := by
    have h1 :=
      sum_filter (s := V.powerset) (p := fun U => H ⊆ U)
        (f := fun U => (μ U - ν U) * mobiusCoeff (endpointObs L phi) H)
    have h2 :=
      sum_filter (s := V.powerset) (p := fun U => H ⊆ U)
        (f := fun U => μ U - ν U)
    have hterm :
        ∀ U ∈ V.powerset.filter (fun U => H ⊆ U),
          (μ U - ν U) * mobiusCoeff (endpointObs L phi) H =
            mobiusCoeff (endpointObs L phi) H * (μ U - ν U) :=
      fun _ _ => mul_comm _ _
    calc
      ∑ U ∈ V.powerset,
            (if H ⊆ U then (μ U - ν U) * mobiusCoeff (endpointObs L phi) H
              else (0 : ℝ))
          = ∑ U ∈ V.powerset.filter (fun U => H ⊆ U),
              (μ U - ν U) * mobiusCoeff (endpointObs L phi) H :=
        h1.symm
      _ = ∑ U ∈ V.powerset.filter (fun U => H ⊆ U),
            mobiusCoeff (endpointObs L phi) H * (μ U - ν U) :=
        sum_congr rfl hterm
      _ = mobiusCoeff (endpointObs L phi) H *
            ∑ U ∈ V.powerset.filter (fun U => H ⊆ U), (μ U - ν U) :=
        (mul_sum _ _ _).symm
      _ = mobiusCoeff (endpointObs L phi) H *
            ∑ U ∈ V.powerset, (if H ⊆ U then μ U - ν U else (0 : ℝ)) := by
        rw [h2]
  have hinc :
      ∑ U ∈ V.powerset, (if H ⊆ U then μ U - ν U else (0 : ℝ)) =
        inclusionProb V μ H - inclusionProb V ν H := by
    unfold inclusionProb
    have hterm :
        ∀ U ∈ V.powerset,
          (if H ⊆ U then μ U - ν U else (0 : ℝ)) =
            (if H ⊆ U then μ U else (0 : ℝ)) -
              (if H ⊆ U then ν U else (0 : ℝ)) := by
      intro U _
      split_ifs <;> ring
    rw [sum_congr rfl hterm, sum_sub_distrib]
  rw [hconst, hinc]

/-- Möbius expansion of the endpoint transfer, stronger than (4.2).

Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §4.
Contract: combinatorial remainder
Audit: GREEN -/
theorem endpoint_transfer_moments (V : Finset ℕ) (μ ν : Finset ℕ → ℝ)
    (L r : ℕ) (phi : List ℕ → ℝ)
    (hμ0 : ∀ U ∈ V.powerset, 0 ≤ μ U) (hν0 : ∀ U ∈ V.powerset, 0 ≤ ν U)
    (_hμ1 : ∑ U ∈ V.powerset, μ U = 1)
    (_hν1 : ∑ U ∈ V.powerset, ν U = 1)
    (hφ : ∀ t, |phi t| ≤ 1) (hL : 1 ≤ L) (hr : L ≤ r) :
    |∑ U ∈ V.powerset, (μ U - ν U) * endpointObs L phi U| ≤
      ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * summedAbsDelta V μ ν j +
        (r.choose (L - 1) : ℝ) *
          (inclusionMoment V μ (r + 1) + inclusionMoment V ν (r + 1)) := by
  have hpt : ∀ U,
      (μ U - ν U) * endpointObs L phi U =
        (μ U - ν U) * truncPoly (endpointObs L phi) r U +
          (μ U - ν U) *
            (endpointObs L phi U - truncPoly (endpointObs L phi) r U) :=
    fun _ => by ring
  rw [sum_congr rfl (fun U _ => hpt U), sum_add_distrib]
  have hpoly :
      |∑ U ∈ V.powerset, (μ U - ν U) * truncPoly (endpointObs L phi) r U| ≤
        ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * summedAbsDelta V μ ν j := by
    rw [sum_sub_truncPoly_eq]
    have hsplit :=
      (sum_filter_add_sum_filter_not
        (s := V.powerset.filter (fun H => H.card ≤ r))
        (p := fun H => L ≤ H.card)
        (f := fun H =>
          mobiusCoeff (endpointObs L phi) H *
            (inclusionProb V μ H - inclusionProb V ν H))).symm
    have hlow :
        ∑ H ∈ (V.powerset.filter (fun H => H.card ≤ r)).filter
            (fun H => ¬ L ≤ H.card),
            mobiusCoeff (endpointObs L phi) H *
              (inclusionProb V μ H - inclusionProb V ν H) = 0 := by
      refine sum_eq_zero fun H hH => ?_
      have : H.card < L := lt_of_not_ge (mem_filter.mp hH).2
      simp [mobiusCoeff_endpoint_eq_zero L phi H this]
    have hfilt :
        (V.powerset.filter (fun H => H.card ≤ r)).filter (fun H => L ≤ H.card) =
          V.powerset.filter (fun H => L ≤ H.card ∧ H.card ≤ r) := by
      ext H
      simp only [mem_filter, mem_powerset]
      constructor
      · intro h
        exact ⟨h.1.1, ⟨h.2, h.1.2⟩⟩
      · intro h
        exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩
    rw [hsplit, hlow, add_zero, hfilt]
    have hbi :
        V.powerset.filter (fun H => L ≤ H.card ∧ H.card ≤ r) =
          (Icc L r).biUnion fun j => V.powerset.filter (fun H => H.card = j) := by
      ext H
      simp only [mem_filter, mem_biUnion, mem_Icc, mem_powerset]
      constructor
      · intro h
        exact ⟨H.card, ⟨h.2.1, h.2.2⟩, ⟨h.1, rfl⟩⟩
      · intro ⟨j, hj, hH⟩
        exact ⟨hH.1, hH.2 ▸ hj.1, hH.2 ▸ hj.2⟩
    have hdisj :
        Set.PairwiseDisjoint (Icc L r : Set ℕ)
          (fun j => V.powerset.filter (fun H => H.card = j)) := by
      intro a _ b _ hab
      refine disjoint_left.mpr ?_
      intro H hHa hHb
      exact hab ((mem_filter.mp hHa).2.symm.trans (mem_filter.mp hHb).2)
    rw [hbi, sum_biUnion hdisj]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine sum_le_sum fun j hj => ?_
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hpt :
        ∀ H ∈ V.powerset.filter (fun H => H.card = j),
          |mobiusCoeff (endpointObs L phi) H *
              (inclusionProb V μ H - inclusionProb V ν H)| ≤
            ((j - 1).choose (L - 1) : ℝ) *
              |inclusionProb V μ H - inclusionProb V ν H| := by
      intro H hH
      have hcard : H.card = j := (mem_filter.mp hH).2
      have hge : L ≤ H.card := by
        have := mem_Icc.mp hj
        omega
      have hle := abs_mobiusCoeff_endpoint_le L phi H hL hφ
      rw [hcard] at hle
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    have hsum := sum_le_sum hpt
    have hfactor :
        ∑ H ∈ V.powerset.filter (fun H => H.card = j),
            ((j - 1).choose (L - 1) : ℝ) *
              |inclusionProb V μ H - inclusionProb V ν H| =
          ((j - 1).choose (L - 1) : ℝ) * summedAbsDelta V μ ν j := by
      rw [← mul_sum]
      rfl
    exact hsum.trans (le_of_eq hfactor)
  have hrem :
      |∑ U ∈ V.powerset, (μ U - ν U) *
          (endpointObs L phi U - truncPoly (endpointObs L phi) r U)| ≤
        (r.choose (L - 1) : ℝ) *
          (inclusionMoment V μ (r + 1) + inclusionMoment V ν (r + 1)) := by
    have habs :=
      abs_sum_le_sum_abs (s := V.powerset)
        (fun U => (μ U - ν U) *
          (endpointObs L phi U - truncPoly (endpointObs L phi) r U))
    refine habs.trans ?_
    have hptU : ∀ U ∈ V.powerset,
        |(μ U - ν U) *
            (endpointObs L phi U - truncPoly (endpointObs L phi) r U)| ≤
          μ U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) +
            ν U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) := by
      intro U hU
      have hremU := truncPoly_endpoint_remainder L phi hφ hL hr (U := U)
      have hμ : 0 ≤ μ U := hμ0 U hU
      have hν : 0 ≤ ν U := hν0 U hU
      have habsμν : |μ U - ν U| ≤ μ U + ν U := by
        have := abs_add_le (μ U) (-ν U)
        rw [abs_neg] at this
        rw [abs_of_nonneg hμ, abs_of_nonneg hν] at this
        exact this
      have hmul :
          |(μ U - ν U) *
              (endpointObs L phi U - truncPoly (endpointObs L phi) r U)| ≤
            |μ U - ν U| *
              |endpointObs L phi U - truncPoly (endpointObs L phi) r U| :=
        le_of_eq (abs_mul _ _)
      have h1 :
          |μ U - ν U| * |endpointObs L phi U - truncPoly (endpointObs L phi) r U| ≤
            |μ U - ν U| * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left hremU (abs_nonneg _)
      have h2 :
          |μ U - ν U| * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) ≤
            (μ U + ν U) * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_right habsμν (by positivity)
      have h3 :
          (μ U + ν U) * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) =
            μ U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) +
              ν U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) := by
        ring
      exact (hmul.trans h1).trans (h2.trans (le_of_eq h3))
    refine (sum_le_sum hptU).trans ?_
    have hμs :
        ∑ U ∈ V.powerset,
            μ U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) =
          (r.choose (L - 1) : ℝ) * inclusionMoment V μ (r + 1) := by
      simp only [inclusionMoment]
      have hterm :
          ∀ U ∈ V.powerset,
            μ U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) =
              (r.choose (L - 1) : ℝ) * (μ U * (U.card.choose (r + 1) : ℝ)) :=
        fun U _ => mul_left_comm _ _ _
      rw [sum_congr rfl hterm, ← mul_sum]
    have hνs :
        ∑ U ∈ V.powerset,
            ν U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) =
          (r.choose (L - 1) : ℝ) * inclusionMoment V ν (r + 1) := by
      simp only [inclusionMoment]
      have hterm :
          ∀ U ∈ V.powerset,
            ν U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) =
              (r.choose (L - 1) : ℝ) * (ν U * (U.card.choose (r + 1) : ℝ)) :=
        fun U _ => mul_left_comm _ _ _
      rw [sum_congr rfl hterm, ← mul_sum]
    rw [sum_add_distrib, hμs, hνs]
    exact le_of_eq (by ring)
  refine (abs_add_le _ _).trans (add_le_add hpoly hrem)

/-- Transfer bound (4.2) with the `2 Q_{r+1} + A_{r+1}` packaging.

Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §4 (4.2).
Contract: combinatorial remainder
Audit: GREEN -/
theorem endpoint_transfer (V : Finset ℕ) (μ ν : Finset ℕ → ℝ)
    (L r : ℕ) (phi : List ℕ → ℝ)
    (hμ0 : ∀ U ∈ V.powerset, 0 ≤ μ U) (hν0 : ∀ U ∈ V.powerset, 0 ≤ ν U)
    (hμ1 : ∑ U ∈ V.powerset, μ U = 1)
    (hν1 : ∑ U ∈ V.powerset, ν U = 1)
    (hφ : ∀ t, |phi t| ≤ 1) (hL : 1 ≤ L) (hr : L ≤ r) :
    |∑ U ∈ V.powerset, (μ U - ν U) * endpointObs L phi U| ≤
      ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * summedAbsDelta V μ ν j +
        (r.choose (L - 1) : ℝ) *
          (2 * inclusionMoment V ν (r + 1) + summedAbsDelta V μ ν (r + 1)) := by
  have hmom :=
    endpoint_transfer_moments V μ ν L r phi hμ0 hν0 hμ1 hν1 hφ hL hr
  have hle := inclusionMoment_le_add V μ ν (r + 1)
  have hadd :
      inclusionMoment V μ (r + 1) + inclusionMoment V ν (r + 1) ≤
        2 * inclusionMoment V ν (r + 1) + summedAbsDelta V μ ν (r + 1) := by
    calc
      inclusionMoment V μ (r + 1) + inclusionMoment V ν (r + 1)
          ≤ (summedAbsDelta V μ ν (r + 1) + inclusionMoment V ν (r + 1)) +
              inclusionMoment V ν (r + 1) :=
        add_le_add hle le_rfl
      _ = 2 * inclusionMoment V ν (r + 1) + summedAbsDelta V μ ν (r + 1) := by
        ring
  refine hmom.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_left hadd (Nat.cast_nonneg _)

/-! ### Poisson tail (4.5) and relative-mean corollary -/

private theorem choose_pred_div_factorial_le {L j : ℕ} {lam : ℝ}
    (hL : 1 ≤ L) (hj : L ≤ j) (hlam : 0 ≤ lam) :
    ((j - 1).choose (L - 1) : ℝ) * lam ^ j / (j.factorial : ℝ) ≤
      (lam ^ L / (L.factorial : ℝ)) *
        (lam ^ (j - L) / ((j - L).factorial : ℝ)) := by
  have hle : L - 1 ≤ j - 1 := Nat.sub_le_sub_right hj 1
  have hsub : j - 1 - (L - 1) = j - L := by omega
  have hid := Nat.choose_mul_factorial_mul_factorial hle
  rw [hsub] at hid
  have hLfac : L.factorial = L * (L - 1).factorial :=
    (Nat.mul_factorial_pred (Nat.one_le_iff_ne_zero.mp hL)).symm
  have hjfac : j.factorial = j * (j - 1).factorial :=
    (Nat.mul_factorial_pred (Nat.one_le_iff_ne_zero.mp (hL.trans hj))).symm
  have hnat :
      (j - 1).choose (L - 1) * L.factorial * (j - L).factorial ≤ j.factorial := by
    calc
      (j - 1).choose (L - 1) * L.factorial * (j - L).factorial
          = (j - 1).choose (L - 1) * (L * (L - 1).factorial) * (j - L).factorial := by
            rw [hLfac]
      _ = ((j - 1).choose (L - 1) * (L - 1).factorial * (j - L).factorial) * L := by
            ac_rfl
      _ = (j - 1).factorial * L := by rw [hid]
      _ ≤ (j - 1).factorial * j := Nat.mul_le_mul_left _ hj
      _ = j.factorial := by rw [Nat.mul_comm, hjfac]
  have hposj : (0 : ℝ) < (j.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos j
  have hposL : (0 : ℝ) < (L.factorial : ℝ) * ((j - L).factorial : ℝ) := by
    exact_mod_cast mul_pos (Nat.factorial_pos L) (Nat.factorial_pos (j - L))
  have hfrac :
      ((j - 1).choose (L - 1) : ℝ) / (j.factorial : ℝ) ≤
        1 / ((L.factorial : ℝ) * ((j - L).factorial : ℝ)) := by
    rw [div_le_iff₀ hposj, one_div, mul_comm, ← div_eq_mul_inv, le_div_iff₀ hposL]
    exact_mod_cast (by simpa [mul_assoc] using hnat)
  have hpow0 : 0 ≤ lam ^ j := pow_nonneg hlam _
  have hpow : lam ^ j = lam ^ L * lam ^ (j - L) := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  have hLHS :
      ((j - 1).choose (L - 1) : ℝ) * lam ^ j / (j.factorial : ℝ) =
        lam ^ j * (((j - 1).choose (L - 1) : ℝ) / (j.factorial : ℝ)) := by
    ring
  have hRHS :
      (lam ^ L / (L.factorial : ℝ)) *
          (lam ^ (j - L) / ((j - L).factorial : ℝ)) =
        lam ^ j * (1 / ((L.factorial : ℝ) * ((j - L).factorial : ℝ))) := by
    rw [hpow]
    ring
  rw [hLHS, hRHS]
  exact mul_le_mul_of_nonneg_left hfrac hpow0

/-- Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §4 (4.5).
Contract: combinatorial remainder
Audit: GREEN -/
theorem endpointPoisson_le_exp (L : ℕ) (lam : ℝ) (r : ℕ)
    (hL : 1 ≤ L) (hlam : 0 ≤ lam) :
    ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * lam ^ j / (j.factorial : ℝ) ≤
      Real.exp lam * lam ^ L / (L.factorial : ℝ) := by
  rcases lt_or_ge r L with hlt | hle
  · simp [Icc_eq_empty_of_lt hlt]
    positivity
  · rw [sum_Icc_add hle]
    have hterm :
        ∀ m ∈ range (r - L + 1),
          ((L + m - 1).choose (L - 1) : ℝ) * lam ^ (L + m) / ((L + m).factorial : ℝ) ≤
            (lam ^ L / (L.factorial : ℝ)) *
              (lam ^ m / (m.factorial : ℝ)) := by
      intro m _
      have hj : L ≤ L + m := Nat.le_add_right _ _
      have h := choose_pred_div_factorial_le hL hj hlam
      have : L + m - L = m := Nat.add_sub_cancel_left L m
      simpa [this] using h
    have hsum := sum_le_sum hterm
    have hfac :
        ∑ m ∈ range (r - L + 1),
            (lam ^ L / (L.factorial : ℝ)) * (lam ^ m / (m.factorial : ℝ)) =
          (lam ^ L / (L.factorial : ℝ)) *
            ∑ m ∈ range (r - L + 1), lam ^ m / (m.factorial : ℝ) := by
      rw [← mul_sum]
    have hexp :
        ∑ m ∈ range (r - L + 1), lam ^ m / (m.factorial : ℝ) ≤ Real.exp lam := by
      simpa [Nat.factorial] using Real.sum_le_exp_of_nonneg hlam (r - L + 1)
    have hnonneg : 0 ≤ lam ^ L / (L.factorial : ℝ) := by positivity
    have hmul :
        (lam ^ L / (L.factorial : ℝ)) *
            ∑ m ∈ range (r - L + 1), lam ^ m / (m.factorial : ℝ) ≤
          (lam ^ L / (L.factorial : ℝ)) * Real.exp lam :=
      mul_le_mul_of_nonneg_left hexp hnonneg
    have hswap : (lam ^ L / (L.factorial : ℝ)) * Real.exp lam =
        Real.exp lam * lam ^ L / (L.factorial : ℝ) := by ring
    exact (hsum.trans (le_of_eq hfac)).trans (hmul.trans (le_of_eq hswap))

/-- Relative-mean corollary: `A_j ≤ ε Q_j` and `Q_j ≤ lam^j/j!`.

Source: `rounds/round98/03_gpt_observable_transfer_descent.md` §4 (4.3)–(4.5).
Contract: combinatorial remainder
Audit: GREEN -/
theorem endpoint_transfer_relative (V : Finset ℕ) (μ ν : Finset ℕ → ℝ)
    (L r : ℕ) (phi : List ℕ → ℝ) (ε lam : ℝ)
    (hμ0 : ∀ U ∈ V.powerset, 0 ≤ μ U) (hν0 : ∀ U ∈ V.powerset, 0 ≤ ν U)
    (hμ1 : ∑ U ∈ V.powerset, μ U = 1)
    (hν1 : ∑ U ∈ V.powerset, ν U = 1)
    (hφ : ∀ t, |phi t| ≤ 1) (hL : 1 ≤ L) (hr : L ≤ r)
    (hε : 0 ≤ ε) (hlam : 0 ≤ lam)
    (hA : ∀ j, L ≤ j → j ≤ r + 1 →
      summedAbsDelta V μ ν j ≤ ε * inclusionMoment V ν j)
    (hQ : ∀ j, L ≤ j → j ≤ r + 1 →
      inclusionMoment V ν j ≤ lam ^ j / (j.factorial : ℝ)) :
    |∑ U ∈ V.powerset, (μ U - ν U) * endpointObs L phi U| ≤
      ε * (Real.exp lam * lam ^ L / (L.factorial : ℝ)) +
        (2 + ε) * (r.choose (L - 1) : ℝ) * lam ^ (r + 1) / ((r + 1).factorial : ℝ) := by
  have htr := endpoint_transfer V μ ν L r phi hμ0 hν0 hμ1 hν1 hφ hL hr
  have hband :
      ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * summedAbsDelta V μ ν j ≤
        ε * ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) *
          lam ^ j / (j.factorial : ℝ) := by
    have hpt :
        ∀ j ∈ Icc L r,
          ((j - 1).choose (L - 1) : ℝ) * summedAbsDelta V μ ν j ≤
            ε * (((j - 1).choose (L - 1) : ℝ) *
              lam ^ j / (j.factorial : ℝ)) := by
      intro j hj
      have hjr := mem_Icc.mp hj
      have hAj := hA j hjr.1 (hjr.2.trans (Nat.le_succ r))
      have hQj := hQ j hjr.1 (hjr.2.trans (Nat.le_succ r))
      have hch : 0 ≤ ((j - 1).choose (L - 1) : ℝ) := Nat.cast_nonneg _
      have h1 : ((j - 1).choose (L - 1) : ℝ) * summedAbsDelta V μ ν j ≤
          ((j - 1).choose (L - 1) : ℝ) * (ε * inclusionMoment V ν j) :=
        mul_le_mul_of_nonneg_left hAj hch
      have h2 : ((j - 1).choose (L - 1) : ℝ) * (ε * inclusionMoment V ν j) ≤
          ((j - 1).choose (L - 1) : ℝ) * (ε * (lam ^ j / (j.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQj hε) hch
      have h3 :
          ((j - 1).choose (L - 1) : ℝ) * (ε * (lam ^ j / (j.factorial : ℝ))) =
            ε * (((j - 1).choose (L - 1) : ℝ) * lam ^ j / (j.factorial : ℝ)) := by
        ring
      exact h1.trans (h2.trans (le_of_eq h3))
    have hsum := sum_le_sum hpt
    have hfac :
        ∑ j ∈ Icc L r,
            ε * (((j - 1).choose (L - 1) : ℝ) * lam ^ j / (j.factorial : ℝ)) =
          ε * ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) *
            lam ^ j / (j.factorial : ℝ) := by
      rw [← mul_sum]
    exact hsum.trans (le_of_eq hfac)
  have hPoi := endpointPoisson_le_exp L lam r hL hlam
  have hfirst :
      ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * summedAbsDelta V μ ν j ≤
        ε * (Real.exp lam * lam ^ L / (L.factorial : ℝ)) :=
    hband.trans (mul_le_mul_of_nonneg_left hPoi hε)
  have hrest :
      (r.choose (L - 1) : ℝ) *
          (2 * inclusionMoment V ν (r + 1) + summedAbsDelta V μ ν (r + 1)) ≤
        (2 + ε) * (r.choose (L - 1) : ℝ) * lam ^ (r + 1) /
          ((r + 1).factorial : ℝ) := by
    have hAr := hA (r + 1) (hr.trans (Nat.le_succ r)) le_rfl
    have hQr := hQ (r + 1) (hr.trans (Nat.le_succ r)) le_rfl
    have hch : 0 ≤ (r.choose (L - 1) : ℝ) := Nat.cast_nonneg _
    have hQnon : 0 ≤ inclusionMoment V ν (r + 1) :=
      sum_nonneg fun U hU => mul_nonneg (hν0 U hU) (Nat.cast_nonneg _)
    have hcomb :
        2 * inclusionMoment V ν (r + 1) + summedAbsDelta V μ ν (r + 1) ≤
          (2 + ε) * inclusionMoment V ν (r + 1) := by
      have : summedAbsDelta V μ ν (r + 1) ≤ ε * inclusionMoment V ν (r + 1) := hAr
      have h2 : 2 * inclusionMoment V ν (r + 1) + ε * inclusionMoment V ν (r + 1) =
          (2 + ε) * inclusionMoment V ν (r + 1) := by ring
      exact (add_le_add le_rfl this).trans (le_of_eq h2)
    have hQb :
        (2 + ε) * inclusionMoment V ν (r + 1) ≤
          (2 + ε) * (lam ^ (r + 1) / ((r + 1).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hQr (add_nonneg (by positivity) hε)
    have h1 :
        (r.choose (L - 1) : ℝ) *
            (2 * inclusionMoment V ν (r + 1) + summedAbsDelta V μ ν (r + 1)) ≤
          (r.choose (L - 1) : ℝ) * ((2 + ε) * inclusionMoment V ν (r + 1)) :=
      mul_le_mul_of_nonneg_left hcomb hch
    have h2 :
        (r.choose (L - 1) : ℝ) * ((2 + ε) * inclusionMoment V ν (r + 1)) ≤
          (r.choose (L - 1) : ℝ) *
            ((2 + ε) * (lam ^ (r + 1) / ((r + 1).factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left hQb hch
    have h3 :
        (r.choose (L - 1) : ℝ) *
            ((2 + ε) * (lam ^ (r + 1) / ((r + 1).factorial : ℝ))) =
          (2 + ε) * (r.choose (L - 1) : ℝ) * lam ^ (r + 1) /
            ((r + 1).factorial : ℝ) := by
      ring
    exact h1.trans (h2.trans (le_of_eq h3))
  exact htr.trans (add_le_add hfirst hrest)

end PrimeGapNormality.Prime
