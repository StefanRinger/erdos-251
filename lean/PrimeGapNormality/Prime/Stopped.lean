import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite one-sided stopped first-L transfer

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN

Finite ordered first-L shapes, truncated Janossy masses, model remainder,
and the one-sided inequality (5.1). Nested namespace so this
`shortShapeMass` does not collide with `PrimeGapNormality.Prime.shortShapeMass`.
No primes, no PNT, no actual order-`(r+1)` moment on `μ`.
-/

namespace PrimeGapNormality.Prime.Stopped

open Finset

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

variable {α : Type*} [DecidableEq α] [LinearOrder α]

/-! ### Contract definitions -/

/-- First `L` elements of `U` in increasing order.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def firstL (L : ℕ) (U : Finset α) : Finset α :=
  ((U.sort (· ≤ ·)).take L).toFinset

/-- Inclusion mass `∑_{H ⊆ U} μ U` on the powerset of `Ω`.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def inclusionMass (Ω : Finset α) (μ : Finset α → ℝ) (H : Finset α) : ℝ :=
  ∑ U ∈ Ω.powerset.filter (fun U => H ⊆ U), μ U

/-- Short first-L shape mass.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def shortShapeMass (Ω : Finset α) (μ : Finset α → ℝ) (L : ℕ) (K : Finset α) : ℝ :=
  ∑ U ∈ Ω.powerset, if L ≤ U.card ∧ firstL L U = K then μ U else 0

/-- Mass of configurations with fewer than `L` points.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def failureMass (Ω : Finset α) (μ : Finset α → ℝ) (L : ℕ) : ℝ :=
  ∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U

/-- ℓ¹ distance of short first-L shape masses.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def shapeL1 (Ω : Finset α) (μ ν : Finset α → ℝ) (L : ℕ) : ℝ :=
  ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
    |shortShapeMass Ω μ L K - shortShapeMass Ω ν L K|

/-- Binomial count moment `∑ μ(U) C(|U|, j)`.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def countMoment (Ω : Finset α) (ν : Finset α → ℝ) (j : ℕ) : ℝ :=
  ∑ U ∈ Ω.powerset, ν U * (U.card.choose j : ℝ)

/-- Points of `Ω` strictly before `max K` and outside `K`.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def beforeOutside (Ω K : Finset α) (hK : K.Nonempty) : Finset α :=
  Ω.filter (fun x => x < K.max' hK ∧ x ∉ K)

/-- Truncated Janossy mass. May be negative. Does not call `max` on empty.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def janossyTrunc (Ω : Finset α) (μ : Finset α → ℝ) (L r : ℕ)
    (K : Finset α) : ℝ :=
  if hK : K.Nonempty then
    ∑ D ∈ (beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L),
      (-1 : ℝ) ^ D.card * inclusionMass Ω μ (K ∪ D)
  else
    0

/-- Exact positive counting envelope `R_(L,r)(N)`.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def countEnvelope (L r N : ℕ) : ℝ :=
  ∑ t ∈ Icc (r + 1) N,
    (Nat.choose (t - 1) (L - 1) : ℝ) * (Nat.choose (t - L - 1) (r - L) : ℝ)

/-- Model remainder `E_ν R_(L,r)(|U|)`.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def modelRemainder (Ω : Finset α) (ν : Finset α → ℝ) (L r : ℕ) : ℝ :=
  ∑ U ∈ Ω.powerset, ν U * countEnvelope L r U.card

/-- Adverse inclusion layer of order `j`.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def adverseLayer (Ω : Finset α) (μ ν : Finset α → ℝ) (L j : ℕ) : ℝ :=
  ∑ H ∈ Ω.powerset.filter (fun H => H.card = j),
    max (((-1 : ℝ) ^ (j - L + 1)) * (inclusionMass Ω μ H - inclusionMass Ω ν H)) 0

/-- Weighted adverse budget `W`.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def adverseBudget (Ω : Finset α) (μ ν : Finset α → ℝ) (L r : ℕ) : ℝ :=
  ∑ j ∈ Icc L r, (Nat.choose (j - 1) (L - 1) : ℝ) * adverseLayer Ω μ ν L j

/-- Stopped observable: `φ` of the first `L` points, else `0`.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
noncomputable def stoppedValue (L : ℕ) (φ : Finset α → ℝ) (U : Finset α) : ℝ :=
  if L ≤ U.card then φ (firstL L U) else 0

/-! ### First-L combinatorics -/

private theorem take_sort_nodup (L : ℕ) (U : Finset α) :
    ((U.sort (· ≤ ·)).take L).Nodup :=
  (U.sort_nodup (· ≤ ·)).sublist (List.take_sublist L _)

private theorem firstL_sort {L : ℕ} {U : Finset α} (_h : L ≤ U.card) :
    (firstL L U).sort (· ≤ ·) = (U.sort (· ≤ ·)).take L := by
  have hnd := take_sort_nodup L U
  have hpw : ((U.sort (· ≤ ·)).take L).Pairwise (· ≤ ·) :=
    (pairwise_sort U (· ≤ ·)).take
  exact (List.toFinset_sort (· ≤ ·) hnd).mpr hpw

/-- Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem firstL_card {L : ℕ} {U : Finset α} (h : L ≤ U.card) :
    (firstL L U).card = L := by
  rw [firstL, List.toFinset_card_of_nodup (take_sort_nodup L U), List.length_take,
    length_sort, min_eq_left h]

/-- Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem firstL_subset {L : ℕ} {U : Finset α} : firstL L U ⊆ U := by
  intro y hy
  have : y ∈ (U.sort (· ≤ ·)).take L := List.mem_toFinset.mp hy
  exact (mem_sort (· ≤ ·)).mp (List.mem_of_mem_take this)

private theorem nonempty_of_card_ge {L : ℕ} {s : Finset α}
    (hL : 1 ≤ L) (hs : L ≤ s.card) : s.Nonempty :=
  card_pos.mp (lt_of_lt_of_le hL hs)

private theorem firstL_nonempty {L : ℕ} {U : Finset α} (hL : 1 ≤ L) (hU : L ≤ U.card) :
    (firstL L U).Nonempty :=
  nonempty_of_card_ge hL (by rw [firstL_card hU])

private theorem firstL_max_eq_sort {L : ℕ} {U : Finset α} (hL : 1 ≤ L) (hU : L ≤ U.card) :
    (firstL L U).max' (firstL_nonempty hL hU) =
      (U.sort (· ≤ ·))[L - 1]'(by
        rw [length_sort]
        have : 0 < L := hL
        omega) := by
  have htake := firstL_sort hU
  have hlenTake : ((U.sort (· ≤ ·)).take L).length = L := by
    rw [List.length_take, length_sort, min_eq_left hU]
  have hmax := max'_eq_sorted_last (s := firstL L U) (h := firstL_nonempty hL hU)
  have hlenK : ((firstL L U).sort (· ≤ ·)).length = L := by
    rw [length_sort, firstL_card hU]
  have hgetK :
      ((firstL L U).sort (· ≤ ·))[((firstL L U).sort (· ≤ ·)).length - 1]'
          (by simpa using Nat.sub_lt (card_pos.mpr (firstL_nonempty hL hU)) Nat.zero_lt_one) =
        ((firstL L U).sort (· ≤ ·))[L - 1]'(by rw [hlenK]; omega) := by
    simp [hlenK]
  have hgetTake :
      ((firstL L U).sort (· ≤ ·))[L - 1]'(by rw [hlenK]; omega) =
        ((U.sort (· ≤ ·)).take L)[L - 1]'(by rw [hlenTake]; omega) := by
    simp [htake]
  have hgetU :
      ((U.sort (· ≤ ·)).take L)[L - 1]'(by rw [hlenTake]; omega) =
        (U.sort (· ≤ ·))[L - 1]'(by rw [length_sort]; omega) :=
    List.getElem_take
  exact (hmax.trans hgetK).trans (hgetTake.trans hgetU)

private theorem firstL_void {L : ℕ} {U : Finset α} (hL : 1 ≤ L) (hU : L ≤ U.card) :
    ∀ x ∈ U, x < (firstL L U).max' (firstL_nonempty hL hU) → x ∈ firstL L U := by
  intro x hxU hxlt
  set l := U.sort (· ≤ ·)
  have hxmax := firstL_max_eq_sort hL hU
  rw [hxmax] at hxlt
  have hxl : x ∈ l := (mem_sort (· ≤ ·)).mpr hxU
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hxl
  have hlen : l.length = U.card := length_sort _
  have hLt : L - 1 < l.length := by
    rw [hlen]; have : 0 < L := hL; omega
  have hsorted : List.SortedLT l := sortedLT_sort U
  have hjL : j < L := by
    have hcmp := hsorted.getElem_lt_getElem_iff (i := j) (j := L - 1) (hi := hj) (hj := hLt)
    have : j < L - 1 := hcmp.mp hxlt
    omega
  have : l[j] ∈ l.take L :=
    (List.mem_take_iff_getElem).mpr ⟨j, Nat.lt_min.mpr ⟨hjL, hj⟩, rfl⟩
  exact List.mem_toFinset.mpr this

private theorem pred_ssubset {U : Finset α} {z : α} (hz : z ∈ U) :
    U.filter (fun x => x < z) ⊂ U := by
  refine ssubset_of_subset_of_ne (filter_subset _ _) ?_
  intro heq
  have hz' : z ∈ U.filter (fun x => x < z) := by
    rw [heq]
    exact hz
  simp at hz'

private theorem pred_card_lt {U : Finset α} {z : α} (hz : z ∈ U) :
    (U.filter (fun x => x < z)).card < U.card :=
  card_lt_card (pred_ssubset hz)

private theorem below_card_sort_get (U : Finset α) {i : ℕ} (hi : i < U.card) :
    (U.filter (fun y =>
        y < (U.sort (· ≤ ·))[i]'(by simpa [length_sort] using hi))).card = i := by
  set l := U.sort (· ≤ ·)
  have hlen : l.length = U.card := length_sort _
  have hi' : i < l.length := by simpa [l, hlen] using hi
  have hsorted : List.SortedLT l := sortedLT_sort U
  have heq :
      U.filter (fun y => y < l[i]'hi') = (l.take i).toFinset := by
    ext y
    constructor
    · intro hy
      have hy' := mem_filter.mp hy
      have hym : y ∈ l := (mem_sort (· ≤ ·)).mpr hy'.1
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hym
      have hjlt : j < i :=
        (hsorted.getElem_lt_getElem_iff (i := j) (j := i) (hi := hj) (hj := hi')).mp hy'.2
      exact List.mem_toFinset.mpr
        ((List.mem_take_iff_getElem).mpr ⟨j, Nat.lt_min.mpr ⟨hjlt, hj⟩, rfl⟩)
    · intro hy
      have hym := List.mem_toFinset.mp hy
      obtain ⟨j, hjmin, rfl⟩ := List.mem_take_iff_getElem.mp hym
      have hjlt : j < i := (Nat.lt_min.mp hjmin).1
      have hjlen : j < l.length := (Nat.lt_min.mp hjmin).2
      have hyU : l[j] ∈ U := (mem_sort (· ≤ ·)).mp (List.getElem_mem _)
      have hylt : l[j] < l[i]'hi' :=
        (hsorted.getElem_lt_getElem_iff (i := j) (j := i) (hi := hjlen) (hj := hi')).mpr hjlt
      exact mem_filter.mpr ⟨hyU, hylt⟩
  rw [heq, List.toFinset_card_of_nodup]
  · rw [List.length_take, hlen, min_eq_left (le_of_lt hi)]
  · exact (U.sort_nodup _).sublist (List.take_sublist i l)

private theorem pred_card_lt_of_mem_firstL {L : ℕ} {U : Finset α} {y : α}
    (hU : L ≤ U.card) (hy : y ∈ firstL L U) :
    (U.filter (fun x => x < y)).card < L := by
  set l := U.sort (· ≤ ·)
  have hyL : y ∈ l.take L := List.mem_toFinset.mp hy
  obtain ⟨j, hjmin, rfl⟩ := List.mem_take_iff_getElem.mp hyL
  have hjL : j < L := (Nat.lt_min.mp hjmin).1
  have hjlen : j < l.length := (Nat.lt_min.mp hjmin).2
  have hi : j < U.card := by simpa [l, length_sort] using hjlen
  have hcard := below_card_sort_get U hi
  have hfilt :
      U.filter (fun x => x < l[j]) =
        U.filter (fun y => y < (U.sort (· ≤ ·))[j]'(by simpa [length_sort] using hi)) := by
    simp [l]
  rw [hfilt, hcard]
  exact hjL

/-- Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem firstL_eq_iff {L : ℕ} {U K : Finset α} (hK : K.Nonempty)
    (hL : 1 ≤ L) (hU : L ≤ U.card) :
    firstL L U = K ↔
      K ⊆ U ∧ K.card = L ∧ ∀ x ∈ U, x < K.max' hK → x ∈ K := by
  constructor
  · intro h
    refine ⟨h ▸ firstL_subset, h ▸ firstL_card hU, ?_⟩
    intro x hxU hxlt
    have hmax : (firstL L U).max' (firstL_nonempty hL hU) = K.max' hK := by
      refine le_antisymm ?_ ?_
      · exact (max'_le_iff (firstL L U) (firstL_nonempty hL hU)).mpr (fun y hy =>
          (max'_le_iff K hK).mp le_rfl y (h ▸ hy))
      · exact (max'_le_iff K hK).mpr (fun y hy =>
          (max'_le_iff (firstL L U) (firstL_nonempty hL hU)).mp le_rfl y
            (h.symm ▸ hy))
    have hxlt' : x < (firstL L U).max' (firstL_nonempty hL hU) := by
      rwa [hmax]
    exact h ▸ firstL_void hL hU x hxU hxlt'
  · intro ⟨hsub, hcard, hvoid⟩
    refine eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      by_cases hlt : y < K.max' hK
      · exact hvoid y (firstL_subset hy) hlt
      · have hyU : y ∈ U := firstL_subset hy
        have hle : K.max' hK ≤ y := le_of_not_gt hlt
        by_cases heq : y = K.max' hK
        · exact heq ▸ max'_mem K hK
        · have hzlt : K.max' hK < y := lt_of_le_of_ne hle (Ne.symm heq)
          have hpred : K ⊆ U.filter (fun x => x < y) := by
            intro k hk
            exact mem_filter.mpr ⟨hsub hk, (le_max' K k hk).trans_lt hzlt⟩
          have hleK : L ≤ (U.filter (fun x => x < y)).card :=
            hcard ▸ card_le_card hpred
          have hltK : (U.filter (fun x => x < y)).card < L :=
            pred_card_lt_of_mem_firstL hU hy
          exact (hltK.not_ge hleK).elim
    · rw [firstL_card hU, hcard]

private theorem firstL_eq_of_void {L : ℕ} {U K : Finset α} (hK : K.Nonempty)
    (hL : 1 ≤ L) (hcard : K.card = L) (hsub : K ⊆ U)
    (hvoid : ∀ x ∈ U, x < K.max' hK → x ∈ K) :
    firstL L U = K := by
  have hU : L ≤ U.card := hcard ▸ card_le_card hsub
  exact (firstL_eq_iff hK hL hU).mpr ⟨hsub, hcard, hvoid⟩

private theorem void_of_firstL_eq {L : ℕ} {U K : Finset α} (hK : K.Nonempty)
    (hL : 1 ≤ L) (hU : L ≤ U.card) (h : firstL L U = K) :
    ∀ x ∈ U, x < K.max' hK → x ∈ K :=
  ((firstL_eq_iff hK hL hU).mp h).2.2

private theorem pred_eq_void {U K : Finset α} (hK : K.Nonempty) :
    U.filter (fun x => x < K.max' hK ∧ x ∉ K) =
      U.filter (fun x => x < K.max' hK) \ K := by
  ext x
  constructor
  · intro hx
    have hx' := mem_filter.mp hx
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨hx'.1, hx'.2.1⟩, hx'.2.2⟩
  · intro hx
    have hx' := mem_sdiff.mp hx
    have hxF := mem_filter.mp hx'.1
    exact mem_filter.mpr ⟨hxF.1, hxF.2, hx'.2⟩

private theorem firstL_eq_iff_pred {L : ℕ} {U K : Finset α} (hK : K.Nonempty)
    (hL : 1 ≤ L) (hcard : K.card = L) (hsub : K ⊆ U) :
    firstL L U = K ↔ U.filter (fun x => x < K.max' hK ∧ x ∉ K) = ∅ := by
  have hU : L ≤ U.card := hcard ▸ card_le_card hsub
  constructor
  · intro h
    refine eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    have hx' := mem_filter.mp hx
    exact hx'.2.2 (((firstL_eq_iff hK hL hU).mp h).2.2 x hx'.1 hx'.2.1)
  · intro hempty
    refine firstL_eq_of_void hK hL hcard hsub ?_
    intro x hxU hlt
    by_contra hxK
    have : x ∈ U.filter (fun y => y < K.max' hK ∧ y ∉ K) :=
      mem_filter.mpr ⟨hxU, hlt, hxK⟩
    exact (eq_empty_iff_forall_notMem.mp hempty) _ this

/-! ### Alternating binomial sums -/

/-- Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem sum_range_signed_choose {m s : ℕ} (hm : 1 ≤ m) :
    ∑ i ∈ range (s + 1), (-1 : ℝ) ^ i * (m.choose i : ℝ) =
      (-1 : ℝ) ^ s * ((m - 1).choose s : ℝ) := by
  have hz := Int.alternating_sum_range_choose_eq_choose (n := m - 1) (m := s)
  have hn' : m = m - 1 + 1 := (Nat.sub_add_cancel hm).symm
  rw [← hn'] at hz
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hz
  simpa [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast] using hcast

/-- Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem sum_range_signed_choose_zero (s : ℕ) :
    ∑ i ∈ range (s + 1), (-1 : ℝ) ^ i * ((0 : ℕ).choose i : ℝ) = 1 := by
  have hterm : ∀ i ∈ range (s + 1),
      (-1 : ℝ) ^ i * ((0 : ℕ).choose i : ℝ) = if i = 0 then (1 : ℝ) else 0 := by
    intro i hi
    cases i with
    | zero => simp
    | succ k => simp [Nat.choose_eq_zero_of_lt (Nat.succ_pos k)]
  rw [sum_congr rfl hterm, sum_ite_eq']
  simp [mem_range]

private noncomputable def truncSigned (m s : ℕ) : ℝ :=
  ∑ i ∈ range (s + 1), (-1 : ℝ) ^ i * (m.choose i : ℝ)

private theorem truncSigned_zero (s : ℕ) : truncSigned 0 s = 1 :=
  sum_range_signed_choose_zero s

private theorem truncSigned_of_pos {m s : ℕ} (hm : 1 ≤ m) :
    truncSigned m s = (-1 : ℝ) ^ s * ((m - 1).choose s : ℝ) :=
  sum_range_signed_choose hm

private theorem truncSigned_le_indicator {m s : ℕ} (hpar : Odd s) :
    truncSigned m s ≤ if m = 0 then (1 : ℝ) else 0 := by
  cases m with
  | zero => simp [truncSigned_zero]
  | succ m =>
    have hm : 1 ≤ m.succ := Nat.succ_le_succ (Nat.zero_le _)
    rw [truncSigned_of_pos hm, Odd.neg_one_pow hpar]
    simp

private theorem truncSigned_eq_neg_choose {m s : ℕ} (hm : 1 ≤ m) (hpar : Odd s) :
    truncSigned m s = -((m - 1).choose s : ℝ) := by
  rw [truncSigned_of_pos hm, Odd.neg_one_pow hpar, neg_mul, one_mul]

/-! ### Truncated signed powerset sums -/

private theorem powerset_trunc_eq_biUnion {W : Finset α} {s : ℕ} :
    W.powerset.filter (fun D => D.card ≤ s) =
      (range (s + 1)).biUnion (fun i => W.powersetCard i) := by
  ext D
  simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
  constructor
  · intro h
    exact ⟨D.card, Nat.lt_succ_iff.mpr h.2, h.1, rfl⟩
  · intro ⟨i, hi, hW, hcard⟩
    exact ⟨hW, hcard ▸ Nat.lt_succ_iff.mp hi⟩

private theorem pairwiseDisjoint_powersetCard (W : Finset α) (I : Finset ℕ) :
    (I : Set ℕ).PairwiseDisjoint (fun i => W.powersetCard i) := by
  intro a _ b _ hab
  refine disjoint_left.mpr ?_
  intro S hSa hSb
  exact hab ((mem_powersetCard.mp hSa).2.symm.trans (mem_powersetCard.mp hSb).2)

private theorem sum_trunc_powerset (W : Finset α) (s : ℕ) :
    ∑ D ∈ W.powerset.filter (fun D => D.card ≤ s), (-1 : ℝ) ^ D.card =
      truncSigned W.card s := by
  rw [powerset_trunc_eq_biUnion, sum_biUnion (pairwiseDisjoint_powersetCard W _),
    truncSigned]
  refine sum_congr rfl fun i _ => ?_
  have hconst : ∀ D ∈ W.powersetCard i, (-1 : ℝ) ^ D.card = (-1 : ℝ) ^ i := by
    intro D hD
    rw [(mem_powersetCard.mp hD).2]
  rw [sum_congr rfl hconst, sum_const, card_powersetCard, nsmul_eq_mul]
  ring

/-! ### Endpoint multiplicity -/

private theorem max_eq_iff_mem {K H : Finset α} (hK : K.Nonempty) (hH : H.Nonempty)
    (hKH : K ⊆ H) :
    K.max' hK = H.max' hH ↔ H.max' hH ∈ K := by
  constructor
  · intro h
    rw [← h]
    exact max'_mem K hK
  · intro hz
    exact le_antisymm (max'_subset hK hKH) (le_max' K _ hz)

/-- A set of card `j` contains exactly `C(j-1, L-1)` subsets `K` of card `L`
with `max K = max H`.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem endpoint_multiplicity {H : Finset α} {L : ℕ}
    (hH : H.Nonempty) (hL : 1 ≤ L) (hle : L ≤ H.card) :
    (H.powerset.filter (fun K => K.card = L ∧ H.max' hH ∈ K)).card =
      (H.card - 1).choose (L - 1) := by
  set z := H.max' hH
  have hzH : {z} ⊆ H := singleton_subset_iff.mpr (max'_mem _ _)
  have h1 : ({z} : Finset α).card ≤ L := by simp [hL]
  have hfilter :
      H.powerset.filter (fun K => K.card = L ∧ z ∈ K) =
        (H.powersetCard L).filter (fun K => {z} ⊆ K) := by
    ext K
    constructor
    · intro h
      have h' := mem_filter.mp h
      exact mem_filter.mpr
        ⟨mem_powersetCard.mpr ⟨mem_powerset.mp h'.1, h'.2.1⟩,
          singleton_subset_iff.mpr h'.2.2⟩
    · intro h
      have h' := mem_filter.mp h
      have hpc := mem_powersetCard.mp h'.1
      exact mem_filter.mpr ⟨mem_powerset.mpr hpc.1, hpc.2, singleton_subset_iff.mp h'.2⟩
  rw [hfilter, card_filter_powersetCard_subset {z} H L hzH h1]
  simp

/-! ### Janossy expansion -/

private theorem beforeOutside_inter {Ω U K : Finset α} (hK : K.Nonempty) (hU : U ⊆ Ω) :
    U ∩ beforeOutside Ω K hK = U.filter (fun x => x < K.max' hK ∧ x ∉ K) := by
  ext x
  constructor
  · intro hx
    have hxI := mem_inter.mp hx
    have hxB := mem_filter.mp hxI.2
    exact mem_filter.mpr ⟨hxI.1, hxB.2.1, hxB.2.2⟩
  · intro hx
    have hxF := mem_filter.mp hx
    exact mem_inter.mpr ⟨hxF.1, mem_filter.mpr ⟨hU hxF.1, hxF.2.1, hxF.2.2⟩⟩

private theorem truncDs_eq_inter {Ω U K : Finset α} {L r : ℕ} (hK : K.Nonempty)
    (hU : U ⊆ Ω) (hKU : K ⊆ U) :
    (beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L ∧ D ⊆ U) =
      (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).powerset.filter
        (fun D => D.card ≤ r - L) := by
  ext D
  simp only [mem_filter, mem_powerset]
  constructor
  · intro ⟨hDB, hcard, hDU⟩
    have hD : D ⊆ U.filter (fun x => x < K.max' hK ∧ x ∉ K) := by
      intro x hx
      have hxB := hDB hx
      have hxU := hDU hx
      have hxB' := mem_filter.mp hxB
      exact mem_filter.mpr ⟨hxU, hxB'.2.1, hxB'.2.2⟩
    exact ⟨hD, hcard⟩
  · intro ⟨hD, hcard⟩
    have hDU : D ⊆ U := (hD.trans (filter_subset _ _))
    have hDB : D ⊆ beforeOutside Ω K hK := by
      intro x hx
      have hxF := mem_filter.mp (hD hx)
      exact mem_filter.mpr ⟨hU hxF.1, hxF.2.1, hxF.2.2⟩
    exact ⟨hDB, hcard, hDU⟩

private theorem union_subset_iff_of_le {K D U : Finset α} :
    K ∪ D ⊆ U ↔ K ⊆ U ∧ D ⊆ U :=
  union_subset_iff

private theorem janossyTrunc_eq_sum {Ω : Finset α} {μ : Finset α → ℝ} {L r : ℕ}
    {K : Finset α} (hK : K.Nonempty) :
    janossyTrunc Ω μ L r K =
      ∑ U ∈ Ω.powerset,
        μ U * (if K ⊆ U then truncSigned
            (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0) := by
  unfold janossyTrunc
  rw [dif_pos hK]
  have hswap :
      ∑ D ∈ (beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L),
          (-1 : ℝ) ^ D.card * inclusionMass Ω μ (K ∪ D) =
        ∑ U ∈ Ω.powerset, μ U *
          ∑ D ∈ (beforeOutside Ω K hK).powerset.filter
              (fun D => D.card ≤ r - L ∧ K ∪ D ⊆ U),
            (-1 : ℝ) ^ D.card := by
    simp only [inclusionMass]
    have hite :
        ∑ D ∈ (beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L),
            (-1 : ℝ) ^ D.card *
              ∑ U ∈ Ω.powerset.filter (fun U => K ∪ D ⊆ U), μ U =
          ∑ D ∈ (beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L),
            ∑ U ∈ Ω.powerset,
              if K ∪ D ⊆ U then (-1 : ℝ) ^ D.card * μ U else 0 := by
      refine sum_congr rfl fun D _ => ?_
      rw [sum_filter, mul_sum]
      refine sum_congr rfl fun U _ => ?_
      split_ifs with h
      · ring
      · simp
    rw [hite, sum_comm]
    refine sum_congr rfl fun U _ => ?_
    have hfact :
        ∑ D ∈ (beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L),
            (if K ∪ D ⊆ U then (-1 : ℝ) ^ D.card * μ U else 0) =
          μ U * ∑ D ∈ (beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L),
            (if K ∪ D ⊆ U then (-1 : ℝ) ^ D.card else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun D _ => ?_
      split_ifs <;> ring
    rw [hfact]
    refine congrArg (fun z => μ U * z) ?_
    have heq :
        (beforeOutside Ω K hK).powerset.filter
            (fun D => D.card ≤ r - L ∧ K ∪ D ⊆ U) =
          ((beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L)).filter
            (fun D => K ∪ D ⊆ U) := by
      ext D
      simp only [mem_filter, and_assoc]
    rw [heq]
    exact (sum_filter (p := fun D => K ∪ D ⊆ U)
      (f := fun D => (-1 : ℝ) ^ D.card)).symm
  rw [hswap]
  refine sum_congr rfl fun U hU => ?_
  have hUΩ : U ⊆ Ω := mem_powerset.mp hU
  by_cases hKU : K ⊆ U
  · simp only [hKU, ite_true]
    have hfilter :
        (beforeOutside Ω K hK).powerset.filter
            (fun D => D.card ≤ r - L ∧ K ∪ D ⊆ U) =
          (beforeOutside Ω K hK).powerset.filter
            (fun D => D.card ≤ r - L ∧ D ⊆ U) := by
      ext D
      simp [mem_filter, union_subset_iff, hKU]
    rw [hfilter, truncDs_eq_inter (Ω := Ω) (U := U) (K := K) (L := L) (r := r) hK hUΩ hKU,
      sum_trunc_powerset]
  · simp only [hKU, ite_false, mul_zero]
    have hzero :
        ∑ D ∈ (beforeOutside Ω K hK).powerset.filter
            (fun D => D.card ≤ r - L ∧ K ∪ D ⊆ U),
          (-1 : ℝ) ^ D.card = 0 := by
      refine sum_eq_zero fun D hD => ?_
      have hDU := (mem_filter.mp hD).2.2
      have : K ⊆ U := (subset_union_left.trans hDU)
      exact (hKU this).elim
    simp [hzero]

private theorem shortShapeMass_eq_sum {Ω : Finset α} {μ : Finset α → ℝ} {L : ℕ}
    {K : Finset α} :
    shortShapeMass Ω μ L K =
      ∑ U ∈ Ω.powerset, μ U * (if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) := by
  unfold shortShapeMass
  refine sum_congr rfl fun U _ => ?_
  split_ifs <;> simp

private theorem indicator_eq_pred {Ω U K : Finset α} {L : ℕ}
    (hK : K.Nonempty) (hL : 1 ≤ L) (hcard : K.card = L) (hUΩ : U ⊆ Ω) :
    (if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) =
      if K ⊆ U ∧ U.filter (fun x => x < K.max' hK ∧ x ∉ K) = ∅ then (1 : ℝ) else 0 := by
  by_cases hKU : K ⊆ U
  · have hU : L ≤ U.card := hcard ▸ card_le_card hKU
    have hiff := firstL_eq_iff_pred hK hL hcard hKU
    simp [hKU, hU, hiff]
  · have hne : firstL L U ≠ K := by
      intro h
      exact hKU (h ▸ firstL_subset)
    simp [hKU, hne]

private theorem trunc_le_indicator_config {Ω U K : Finset α} {L r : ℕ}
    (hK : K.Nonempty) (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hcard : K.card = L) (hUΩ : U ⊆ Ω) :
    (if K ⊆ U then truncSigned
        (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0) ≤
      if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0 := by
  by_cases hKU : K ⊆ U
  · have hUcard : L ≤ U.card := hcard ▸ card_le_card hKU
    have hiff := firstL_eq_iff_pred hK hL hcard hKU
    set m := (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card
    have hle := truncSigned_le_indicator (m := m) (s := r - L) hpar
    by_cases hm0 : m = 0
    · have hempty : U.filter (fun x => x < K.max' hK ∧ x ∉ K) = ∅ :=
        card_eq_zero.mp hm0
      have hfirst : firstL L U = K := hiff.mpr hempty
      simp [hKU, hUcard, hfirst, hm0, truncSigned_zero]
    · have hne : firstL L U ≠ K := by
        intro h
        exact hm0 (card_eq_zero.mpr (hiff.mp h))
      have htr : truncSigned m (r - L) ≤ 0 := by
        simpa [hm0] using hle
      simp [hKU, hUcard, hne, htr]
  · have hne : firstL L U ≠ K := by
      intro h
      exact hKU (h ▸ firstL_subset)
    simp [hKU, hne]

/-- Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` Lemma 4.1;
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem janossyTrunc_le_shortShapeMass {Ω : Finset α} {μ : Finset α → ℝ} {L r : ℕ}
    {K : Finset α}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L)) (hcard : K.card = L)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U) :
    janossyTrunc Ω μ L r K ≤ shortShapeMass Ω μ L K := by
  have hK : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
  rw [janossyTrunc_eq_sum hK, shortShapeMass_eq_sum]
  refine sum_le_sum fun U hU => ?_
  have hUΩ : U ⊆ Ω := mem_powerset.mp hU
  have hμU : 0 ≤ μ U := hμ U hU
  have hpt := trunc_le_indicator_config (Ω := Ω) hK hL hr hpar hcard hUΩ
  exact mul_le_mul_of_nonneg_left hpt hμU

/-! ### Residual identity on one configuration -/

private theorem sort_union_of_forall_lt {A₀ B : Finset α}
    (hAB0 : ∀ a ∈ A₀, ∀ b ∈ B, a < b) :
    (A₀ ∪ B).sort (· ≤ ·) = A₀.sort (· ≤ ·) ++ B.sort (· ≤ ·) := by
  suffices ∀ A, (∀ a ∈ A, ∀ b ∈ B, a < b) →
      (A ∪ B).sort (· ≤ ·) = A.sort (· ≤ ·) ++ B.sort (· ≤ ·) by
    exact this A₀ hAB0
  intro A
  refine Finset.strongInductionOn A (fun A ih hAB => ?_)
  rcases eq_empty_or_nonempty A with hA | hA
  · simp [hA]
  · set a := A.min' hA
    have ha : a ∈ A := min'_mem _ _
    have hinsertA : A = insert a (A.erase a) := (insert_erase ha).symm
    have hunion : A ∪ B = insert a ((A.erase a) ∪ B) := by
      conv_lhs => rw [hinsertA]
      exact insert_union a (A.erase a) B
    have ha_not_B : a ∉ B := by
      intro hab
      exact (lt_irrefl a) (hAB a ha a hab)
    have ha_not_rest : a ∉ A.erase a ∪ B := by
      simp [ha_not_B]
    have hle_rest : ∀ z ∈ A.erase a ∪ B, a ≤ z := by
      intro z hz
      rw [mem_union] at hz
      rcases hz with hz | hz
      · exact min'_le A z (mem_of_mem_erase hz)
      · exact (hAB a ha z hz).le
    have hleA : ∀ z ∈ A.erase a, a ≤ z := fun z hz =>
      min'_le A z (mem_of_mem_erase hz)
    have ha_not_erase : a ∉ A.erase a := notMem_erase _ _
    have hAsort : A.sort (· ≤ ·) = a :: (A.erase a).sort (· ≤ ·) := by
      conv_lhs => rw [hinsertA]
      exact sort_insert (· ≤ ·) hleA ha_not_erase
    rw [hunion, sort_insert (· ≤ ·) hle_rest ha_not_rest, hAsort]
    have ih' := ih (A.erase a) (erase_ssubset ha)
      (fun z hz b hb => hAB z (mem_of_mem_erase hz) b hb)
    rw [ih', List.cons_append]

private theorem below_eq_union (U : Finset α) (x : α) :
    U = U.filter (fun y => y < x) ∪ U.filter (fun y => x ≤ y) := by
  ext y
  simp only [mem_union, mem_filter]
  constructor
  · intro hy
    rcases lt_or_ge y x with hlt | hge
    · exact Or.inl ⟨hy, hlt⟩
    · exact Or.inr ⟨hy, hge⟩
  · intro h
    rcases h with h | h <;> exact h.1

private theorem below_disjoint (U : Finset α) (x : α) :
    Disjoint (U.filter (fun y => y < x)) (U.filter (fun y => x ≤ y)) :=
  disjoint_left.mpr fun a ha hb =>
    ((mem_filter.mp ha).2).not_ge (mem_filter.mp hb).2

private theorem sort_get_below_card (U : Finset α) {x : α} (hx : x ∈ U) :
    (U.sort (· ≤ ·))[(U.filter (fun y => y < x)).card]'(by
        simpa [length_sort] using pred_card_lt hx) = x := by
  set A := U.filter (fun y => y < x)
  set B := U.filter (fun y => x ≤ y)
  have hU : U = A ∪ B := below_eq_union U x
  have hdisj : Disjoint A B := below_disjoint U x
  have hltAB : ∀ a ∈ A, ∀ b ∈ B, a < b := fun a ha b hb =>
    (mem_filter.mp ha).2.trans_le (mem_filter.mp hb).2
  have hsort : (A ∪ B).sort (· ≤ ·) = A.sort (· ≤ ·) ++ B.sort (· ≤ ·) :=
    sort_union_of_forall_lt hltAB
  have hBne : B.Nonempty := ⟨x, mem_filter.mpr ⟨hx, le_rfl⟩⟩
  have hmin : B.min' hBne = x := by
    refine le_antisymm (min'_le B x (mem_filter.mpr ⟨hx, le_rfl⟩)) ?_
    exact le_min' B hBne x fun y hy => (mem_filter.mp hy).2
  have hlenA : (A.sort (· ≤ ·)).length = A.card := length_sort _
  have hi : A.card < U.card := pred_card_lt hx
  have hidx : A.card < (A ∪ B).card := by
    rw [← hU]
    exact hi
  have hget :
      ((A ∪ B).sort (· ≤ ·))[A.card]'(by simpa [length_sort] using hidx) =
        (B.sort (· ≤ ·))[0]'(by simpa [length_sort] using card_pos.mpr hBne) := by
    simp [hsort, hlenA]
  have hUsort : (U.sort (· ≤ ·))[A.card]'(by simpa [length_sort] using hi) =
      ((A ∪ B).sort (· ≤ ·))[A.card]'(by simpa [length_sort] using hidx) := by
    simp [hU]
  have hmin0 :
      (B.sort (· ≤ ·))[0]'(by simpa [length_sort] using card_pos.mpr hBne) =
        B.min' hBne :=
    (min'_eq_sorted_zero (s := B) (h := hBne)).symm
  rw [hUsort, hget, hmin0, hmin]

private theorem sum_by_pred_card (U : Finset α) (f : ℕ → ℝ) :
    ∑ z ∈ U, f (U.filter (fun x => x < z)).card =
      ∑ i ∈ range U.card, f i := by
  refine sum_bij'
    (fun z _ => (U.filter (fun x => x < z)).card)
    (fun i hi => (U.sort (· ≤ ·))[i]'(by simpa [length_sort] using mem_range.mp hi))
    ?_ ?_ ?_ ?_ ?_
  · intro z hz
    exact mem_range.mpr (pred_card_lt hz)
  · intro i hi
    exact (mem_sort (· ≤ ·)).mp (List.getElem_mem _)
  · intro z hz
    exact sort_get_below_card U hz
  · intro i hi
    exact below_card_sort_get U (mem_range.mp hi)
  · intro _ _
    rfl

private theorem sum_shapes_by_max {U : Finset α} {L : ℕ} (hL : 1 ≤ L)
    (f : Finset α → ℝ) :
    ∑ K ∈ U.powerset.filter (fun K => K.card = L), f K =
      ∑ z ∈ U, ∑ J ∈ (U.filter (fun x => x < z)).powerset.filter
          (fun J => J.card = L - 1), f (insert z J) := by
  rw [sum_sigma' (f := fun z J => f (insert z J))]
  refine sum_bij'
    (fun K hKmem =>
      ⟨K.max' (card_pos.mp (by
          have := (mem_filter.mp hKmem).2
          omega)),
        K.erase (K.max' (card_pos.mp (by
          have := (mem_filter.mp hKmem).2
          omega)))⟩)
    (fun p _ => insert p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro K hKmem
    have hKp := mem_filter.mp hKmem
    have hKU : K ⊆ U := mem_powerset.mp hKp.1
    have hcard : K.card = L := hKp.2
    have hKne : K.Nonempty := card_pos.mp (by omega)
    have hz : K.max' hKne ∈ U := hKU (max'_mem _ _)
    have hJ : K.erase (K.max' hKne) ∈
        (U.filter (fun x => x < K.max' hKne)).powerset.filter
          (fun J => J.card = L - 1) := by
      refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_⟩
      · intro x hx
        have hxK : x ∈ K := mem_of_mem_erase hx
        have hle : x ≤ K.max' hKne :=
          (max'_le_iff (s := K) (H := hKne)).mp le_rfl x hxK
        have hne : x ≠ K.max' hKne :=
          ne_of_mem_of_not_mem hx (notMem_erase _ _)
        exact mem_filter.mpr ⟨hKU hxK, lt_of_le_of_ne hle hne⟩
      · rw [card_erase_of_mem (max'_mem K hKne), hcard]
    exact mem_sigma.mpr ⟨hz, hJ⟩
  · intro p hp
    have hp' := mem_sigma.mp hp
    have hz : p.1 ∈ U := hp'.1
    have hJ := mem_filter.mp hp'.2
    have hJpred : p.2 ⊆ U.filter (fun x => x < p.1) := mem_powerset.mp hJ.1
    have hcardJ : p.2.card = L - 1 := hJ.2
    have hzJ : p.1 ∉ p.2 := by
      intro h
      exact (lt_irrefl p.1) (mem_filter.mp (hJpred h)).2
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_⟩
    · intro x hx
      rw [mem_insert] at hx
      rcases hx with rfl | hx
      · exact hz
      · exact (mem_filter.mp (hJpred hx)).1
    · rw [card_insert_of_notMem hzJ, hcardJ]
      omega
  · intro K hKmem
    have hKp := mem_filter.mp hKmem
    have hcard : K.card = L := hKp.2
    have hKne : K.Nonempty := card_pos.mp (by omega)
    simp [insert_erase (max'_mem K hKne)]
  · intro p hp
    have hp' := mem_sigma.mp hp
    have hJ := mem_filter.mp hp'.2
    have hJpred : p.2 ⊆ U.filter (fun x => x < p.1) := mem_powerset.mp hJ.1
    have hlt : ∀ x ∈ p.2, x < p.1 := fun x hx => (mem_filter.mp (hJpred hx)).2
    have hne : (insert p.1 p.2).Nonempty := insert_nonempty _ _
    have hmax : (insert p.1 p.2).max' hne = p.1 := by
      apply le_antisymm
      · exact max'_le _ _ _ fun x hx => by
          rw [mem_insert] at hx
          rcases hx with rfl | hx
          · exact le_rfl
          · exact (hlt x hx).le
      · exact le_max' _ _ (mem_insert_self _ _)
    have hzJ : p.1 ∉ p.2 := by
      intro h
      exact (lt_irrefl p.1) (hlt p.1 h)
    simp [hmax, erase_insert hzJ]
  · intro K hKmem
    have hKp := mem_filter.mp hKmem
    have hcard : K.card = L := hKp.2
    have hKne : K.Nonempty := card_pos.mp (by omega)
    simp [insert_erase (max'_mem K hKne)]

private theorem m_of_insert {U : Finset α} {z : α} {L : ℕ} {Jset : Finset α}
    (hz : z ∈ U) (hJ : Jset ⊆ U.filter (fun x => x < z))
    (hJcard : Jset.card = L - 1) (hL : 1 ≤ L)
    (hle : L - 1 ≤ (U.filter (fun x => x < z)).card) :
    (U.filter (fun x => x < (insert z Jset).max' (insert_nonempty z Jset)
        ∧ x ∉ insert z Jset)).card =
      (U.filter (fun x => x < z)).card - (L - 1) := by
  have hne : (insert z Jset).Nonempty := insert_nonempty _ _
  have hltJ : ∀ x ∈ Jset, x < z := fun x hx => (mem_filter.mp (hJ hx)).2
  have hmax : (insert z Jset).max' hne = z := by
    apply le_antisymm
    · exact max'_le _ _ _ fun x hx => by
        rw [mem_insert] at hx
        rcases hx with rfl | hx
        · exact le_rfl
        · exact (hltJ x hx).le
    · exact le_max' _ _ (mem_insert_self _ _)
  have hdisj : Disjoint Jset ({z} : Finset α) :=
    disjoint_left.mpr fun x hxJ hxz =>
      (lt_irrefl x) ((mem_singleton.mp hxz) ▸ hltJ x hxJ)
  have heq :
      U.filter (fun x => x < z ∧ x ∉ insert z Jset) =
        U.filter (fun x => x < z) \ Jset := by
    ext x
    constructor
    · intro hx
      have hx' := mem_filter.mp hx
      have hnot : x ≠ z ∧ x ∉ Jset := by
        simpa [mem_insert, not_or] using hx'.2.2
      exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨hx'.1, hx'.2.1⟩, hnot.2⟩
    · intro hx
      have hx' := mem_sdiff.mp hx
      have hxF := mem_filter.mp hx'.1
      have hnot : x ∉ insert z Jset := by
        simp [mem_insert, hx'.2, ne_of_lt hxF.2]
      exact mem_filter.mpr ⟨hxF.1, hxF.2, hnot⟩
  rw [hmax, heq, card_sdiff_of_subset hJ, hJcard]

private theorem shapes_subset {Ω U : Finset α} {L : ℕ} (hU : U ⊆ Ω) :
    U.powerset.filter (fun K => K.card = L) ⊆
      Ω.powerset.filter (fun K => K.card = L) := by
  intro K hK
  have hK' := mem_filter.mp hK
  exact mem_filter.mpr ⟨mem_powerset.mpr ((mem_powerset.mp hK'.1).trans hU), hK'.2⟩

private theorem residual_term {Ω U K : Finset α} {L r : ℕ}
    (hK : K.Nonempty) (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hcard : K.card = L) (hUΩ : U ⊆ Ω) :
    (if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) -
        (if K ⊆ U then truncSigned
          (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0) =
      if K ⊆ U then
        (if (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card = 0 then (0 : ℝ)
          else (Nat.choose
            ((U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card - 1) (r - L) : ℝ))
      else 0 := by
  by_cases hKU : K ⊆ U
  · have hUcard : L ≤ U.card := hcard ▸ card_le_card hKU
    have hiff := firstL_eq_iff_pred hK hL hcard hKU
    set m := (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card
    by_cases hm0 : m = 0
    · have hempty : U.filter (fun x => x < K.max' hK ∧ x ∉ K) = ∅ :=
        card_eq_zero.mp hm0
      have hfirst : firstL L U = K := hiff.mpr hempty
      simp [hKU, hUcard, hfirst, hm0, truncSigned_zero]
    · have hne : firstL L U ≠ K := by
        intro h
        exact hm0 (card_eq_zero.mpr (hiff.mp h))
      have hmpos : 1 ≤ m := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hm0)
      have htr := truncSigned_eq_neg_choose hmpos hpar
      simp [hKU, hUcard, hne, hm0, htr]
  · have hne : firstL L U ≠ K := by
      intro h
      exact hKU (h ▸ firstL_subset)
    simp [hKU, hne]

private theorem config_residual_eq_envelope {Ω U : Finset α} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L)) (hUΩ : U ⊆ Ω) :
    ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        ((if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) -
          (if hK : K.Nonempty then
            (if K ⊆ U then truncSigned
              (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0)
           else 0)) =
      countEnvelope L r U.card := by
  by_cases hUcard : L ≤ U.card
  · have hrest :
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            ((if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) -
              (if hK : K.Nonempty then
                (if K ⊆ U then truncSigned
                  (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0)
               else 0)) =
          ∑ K ∈ U.powerset.filter (fun K => K.card = L),
            (if hK : K.Nonempty then
              (if (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card = 0 then (0 : ℝ)
                else (Nat.choose
                  ((U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card - 1)
                    (r - L) : ℝ))
             else 0) := by
      have hzero_out :
          ∑ K ∈ (Ω.powerset.filter (fun K => K.card = L)) \
              (U.powerset.filter (fun K => K.card = L)),
              ((if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) -
                (if hK : K.Nonempty then
                  (if K ⊆ U then truncSigned
                    (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0)
                 else 0)) = 0 := by
        refine sum_eq_zero fun K hK => ?_
        have hKΩ := mem_sdiff.mp hK
        have hnot : K ∉ U.powerset.filter (fun K => K.card = L) := hKΩ.2
        have hmem := mem_filter.mp hKΩ.1
        have hcard : K.card = L := hmem.2
        have hKne : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
        have hnotU : ¬ K ⊆ U := by
          intro hKU
          exact hnot (mem_filter.mpr ⟨mem_powerset.mpr hKU, hcard⟩)
        have hne : firstL L U ≠ K := by
          intro h
          exact hnotU (h ▸ firstL_subset)
        simp [hUcard, hne, hnotU, hKne]
      have hUsum :
          ∑ K ∈ U.powerset.filter (fun K => K.card = L),
              ((if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) -
                (if hK : K.Nonempty then
                  (if K ⊆ U then truncSigned
                    (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0)
                 else 0)) =
            ∑ K ∈ U.powerset.filter (fun K => K.card = L),
              (if hK : K.Nonempty then
                (if (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card = 0 then (0 : ℝ)
                  else (Nat.choose
                    ((U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card - 1)
                      (r - L) : ℝ))
               else 0) := by
        refine sum_congr rfl fun K hK => ?_
        have hmem := mem_filter.mp hK
        have hKU : K ⊆ U := mem_powerset.mp hmem.1
        have hcard : K.card = L := hmem.2
        have hKne : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
        simpa [hKne, hKU] using
          residual_term (Ω := Ω) hKne hL hr hpar hcard hUΩ
      have hΩsum :
          ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
              ((if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) -
                (if hK : K.Nonempty then
                  (if K ⊆ U then truncSigned
                    (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0)
                 else 0)) =
            ∑ K ∈ U.powerset.filter (fun K => K.card = L),
                ((if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) -
                  (if hK : K.Nonempty then
                    (if K ⊆ U then truncSigned
                      (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0)
                   else 0)) := by
        have hunion :
            Ω.powerset.filter (fun K => K.card = L) =
              (U.powerset.filter (fun K => K.card = L)) ∪
                ((Ω.powerset.filter (fun K => K.card = L)) \
                  (U.powerset.filter (fun K => K.card = L))) :=
          (union_sdiff_of_subset (shapes_subset (L := L) hUΩ)).symm
        rw [hunion, sum_union (disjoint_sdiff)]
        simp [hzero_out]
      exact hΩsum.trans hUsum
    rw [hrest, sum_shapes_by_max hL]
    have hfiber' :
        ∑ z ∈ U, ∑ J ∈ (U.filter (fun x => x < z)).powerset.filter
            (fun J => J.card = L - 1),
          (if hK : (insert z J).Nonempty then
            (if (U.filter (fun x => x < (insert z J).max' hK ∧ x ∉ insert z J)).card = 0
              then (0 : ℝ)
              else (Nat.choose
                ((U.filter (fun x => x < (insert z J).max' hK ∧ x ∉ insert z J)).card - 1)
                  (r - L) : ℝ))
           else 0) =
          ∑ i ∈ range U.card,
            (Nat.choose i (L - 1) : ℝ) *
              (if i + 1 ≤ L then 0 else (Nat.choose (i - L) (r - L) : ℝ)) := by
      -- Use the closed form per fibre, then reindex by predecessor cardinality.
      have hclosed :
          ∑ z ∈ U, ∑ J ∈ (U.filter (fun x => x < z)).powerset.filter
              (fun J => J.card = L - 1),
            (if hK : (insert z J).Nonempty then
              (if (U.filter (fun x => x < (insert z J).max' hK ∧ x ∉ insert z J)).card = 0
                then (0 : ℝ)
                else (Nat.choose
                  ((U.filter (fun x => x < (insert z J).max' hK ∧ x ∉ insert z J)).card - 1)
                    (r - L) : ℝ))
             else 0) =
            ∑ z ∈ U,
              (Nat.choose (U.filter (fun x => x < z)).card (L - 1) : ℝ) *
                (if (U.filter (fun x => x < z)).card + 1 ≤ L then 0
                  else (Nat.choose ((U.filter (fun x => x < z)).card - L) (r - L) : ℝ)) := by
        refine sum_congr rfl fun z hz => ?_
        set pred := U.filter (fun x => x < z)
        have hterm : ∀ J ∈ pred.powerset.filter (fun J => J.card = L - 1),
            (if hK : (insert z J).Nonempty then
              (if (U.filter (fun x => x < (insert z J).max' hK ∧ x ∉ insert z J)).card = 0
                then (0 : ℝ)
                else (Nat.choose
                  ((U.filter (fun x => x < (insert z J).max' hK ∧ x ∉ insert z J)).card - 1)
                    (r - L) : ℝ))
             else 0) =
              if pred.card + 1 ≤ L then (0 : ℝ)
                else (Nat.choose (pred.card - L) (r - L) : ℝ) := by
          intro J hJ
          have hJ' := mem_filter.mp hJ
          have hJsub : J ⊆ pred := mem_powerset.mp hJ'.1
          have hJcard : J.card = L - 1 := hJ'.2
          have hKne : (insert z J).Nonempty := insert_nonempty _ _
          have hleJ : L - 1 ≤ pred.card := hJcard ▸ card_le_card hJsub
          have hm := m_of_insert (U := U) (z := z) (Jset := J) (L := L)
            hz hJsub hJcard hL hleJ
          simp only [dif_pos hKne]
          have hm' :
              (U.filter (fun x => x < (insert z J).max' hKne ∧ x ∉ insert z J)).card =
                pred.card - (L - 1) := by
            simpa [pred] using hm
          rw [hm']
          by_cases hsmall : pred.card + 1 ≤ L
          · have hm0 : pred.card - (L - 1) = 0 := by omega
            rw [if_pos hm0, if_pos hsmall]
          · have hsub : (pred.card - (L - 1)) - 1 = pred.card - L := by omega
            have hmne : pred.card - (L - 1) ≠ 0 := by omega
            rw [if_neg hmne, if_neg hsmall, hsub]
        have hconst := sum_congr rfl hterm
        rw [hconst, sum_const]
        have hpc :
            (pred.powerset.filter (fun J => J.card = L - 1)).card =
              pred.card.choose (L - 1) := by
          rw [← powersetCard_eq_filter, card_powersetCard]
        rw [hpc, nsmul_eq_mul]
      rw [hclosed]
      exact sum_by_pred_card U fun i =>
        (Nat.choose i (L - 1) : ℝ) *
          (if i + 1 ≤ L then 0 else (Nat.choose (i - L) (r - L) : ℝ))
    rw [hfiber']
    -- Convert the rank sum into `countEnvelope`.
    have henv :
        ∑ i ∈ range U.card,
            (Nat.choose i (L - 1) : ℝ) *
              (if i + 1 ≤ L then 0 else (Nat.choose (i - L) (r - L) : ℝ)) =
          countEnvelope L r U.card := by
      unfold countEnvelope
      have hsplit :
          ∑ i ∈ range U.card,
              (Nat.choose i (L - 1) : ℝ) *
                (if i + 1 ≤ L then 0 else (Nat.choose (i - L) (r - L) : ℝ)) =
            ∑ i ∈ (range U.card).filter (fun i => L < i + 1),
              (Nat.choose i (L - 1) : ℝ) * (Nat.choose (i - L) (r - L) : ℝ) := by
        have hterm' : ∀ i ∈ range U.card,
            (Nat.choose i (L - 1) : ℝ) *
              (if i + 1 ≤ L then 0 else (Nat.choose (i - L) (r - L) : ℝ)) =
              if L < i + 1 then
                (Nat.choose i (L - 1) : ℝ) * (Nat.choose (i - L) (r - L) : ℝ)
              else 0 := by
          intro i _
          by_cases h : i + 1 ≤ L
          · have : ¬ L < i + 1 := by omega
            simp [h, this]
          · have : L < i + 1 := by omega
            simp [h, this]
        rw [sum_congr rfl hterm', ← sum_filter]
      rw [hsplit]
      have hIcc :
          (range U.card).filter (fun i => L < i + 1) = Icc L (U.card - 1) := by
        ext i
        simp only [mem_filter, mem_range, mem_Icc]
        constructor
        · intro ⟨hi, hL'⟩
          exact ⟨by omega, Nat.le_pred_of_lt hi⟩
        · intro ⟨hLi, hi⟩
          have hpos : 0 < U.card := lt_of_lt_of_le hL (hUcard)
          refine ⟨?_, by omega⟩
          have : U.card - 1 + 1 = U.card := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
          omega
      rw [hIcc]
      -- Restrict to `i ≥ r` where the second binomial is possibly nonzero,
      -- then shift `t = i + 1`.
      have hzero :
          ∑ i ∈ Icc L (U.card - 1),
              (Nat.choose i (L - 1) : ℝ) * (Nat.choose (i - L) (r - L) : ℝ) =
            ∑ i ∈ Icc r (U.card - 1),
              (Nat.choose i (L - 1) : ℝ) * (Nat.choose (i - L) (r - L) : ℝ) := by
        by_cases hbig : r ≤ U.card - 1
        · have hdisj : Disjoint (Icc L (r - 1)) (Icc r (U.card - 1)) :=
            disjoint_left.mpr fun a ha1 ha2 => by
              have := mem_Icc.mp ha1
              have := mem_Icc.mp ha2
              omega
          have hunion :
              Icc L (U.card - 1) = Icc L (r - 1) ∪ Icc r (U.card - 1) := by
            ext i
            simp only [mem_union, mem_Icc]
            omega
          have hlow :
              ∑ i ∈ Icc L (r - 1),
                  (Nat.choose i (L - 1) : ℝ) * (Nat.choose (i - L) (r - L) : ℝ) = 0 := by
            refine sum_eq_zero fun i hi => ?_
            have hi' := mem_Icc.mp hi
            have : i - L < r - L := by omega
            simp [Nat.choose_eq_zero_of_lt this]
          rw [hunion, sum_union hdisj, hlow, zero_add]
        · have hhigh : Icc r (U.card - 1) = ∅ := by
            rw [Finset.Icc_eq_empty_iff]
            omega
          have hlow :
              ∑ i ∈ Icc L (U.card - 1),
                  (Nat.choose i (L - 1) : ℝ) * (Nat.choose (i - L) (r - L) : ℝ) = 0 := by
            refine sum_eq_zero fun i hi => ?_
            have hi' := mem_Icc.mp hi
            have : i - L < r - L := by omega
            simp [Nat.choose_eq_zero_of_lt this]
          simp [hhigh, hlow]
      rw [hzero]
      have hshift :
          ∑ i ∈ Icc r (U.card - 1),
              (Nat.choose i (L - 1) : ℝ) * (Nat.choose (i - L) (r - L) : ℝ) =
            ∑ t ∈ Icc (r + 1) U.card,
              (Nat.choose (t - 1) (L - 1) : ℝ) *
                (Nat.choose (t - L - 1) (r - L) : ℝ) := by
        refine sum_nbij' (fun i => i + 1) (fun t => t - 1) ?_ ?_ ?_ ?_ ?_
        · intro i hi
          have hi' := mem_Icc.mp hi
          refine mem_Icc.mpr ⟨by omega, ?_⟩
          have hpos : 0 < U.card := lt_of_lt_of_le hL hUcard
          have : U.card - 1 + 1 = U.card := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
          omega
        · intro t ht
          have ht' := mem_Icc.mp ht
          refine mem_Icc.mpr ⟨by omega, by omega⟩
        · intro i _
          simp
        · intro t ht
          have ht' := mem_Icc.mp ht
          omega
        · intro i hi
          have hi' := mem_Icc.mp hi
          have h1 : i + 1 - 1 = i := by omega
          have h2 : i + 1 - L - 1 = i - L := by omega
          simp [h1, h2]
      exact hshift
    exact henv
  · -- `|U| < L`: both sides vanish.
    have hleft :
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            ((if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) -
              (if hK : K.Nonempty then
                (if K ⊆ U then truncSigned
                  (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0)
               else 0)) = 0 := by
      refine sum_eq_zero fun K hK => ?_
      have hmem := mem_filter.mp hK
      have hcard : K.card = L := hmem.2
      have hKne : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
      have hnot : ¬ K ⊆ U := by
        intro hKU
        exact hUcard (hcard ▸ card_le_card hKU)
      have hne : firstL L U ≠ K := by
        intro h
        exact hnot (h ▸ firstL_subset)
      simp [hUcard, hne, hnot, hKne]
    have henv0 : countEnvelope L r U.card = 0 := by
      unfold countEnvelope
      have : Icc (r + 1) U.card = ∅ := by
        rw [Finset.Icc_eq_empty_iff]
        omega
      simp [this]
    simp [hleft, henv0]

/-- Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (4.3);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem modelRemainder_eq_shapeResidual {Ω : Finset α} {ν : Finset α → ℝ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L)) :
    modelRemainder Ω ν L r
      = ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          (shortShapeMass Ω ν L K - janossyTrunc Ω ν L r K) := by
  unfold modelRemainder
  have hpt : ∀ U ∈ Ω.powerset,
      ν U * countEnvelope L r U.card =
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          ν U * ((if L ≤ U.card ∧ firstL L U = K then (1 : ℝ) else 0) -
            (if hK : K.Nonempty then
              (if K ⊆ U then truncSigned
                (U.filter (fun x => x < K.max' hK ∧ x ∉ K)).card (r - L) else 0)
             else 0)) := by
    intro U hU
    have hUΩ : U ⊆ Ω := mem_powerset.mp hU
    have hres := config_residual_eq_envelope (Ω := Ω) (U := U) hL hr hpar hUΩ
    rw [← hres, mul_sum]
  rw [sum_congr rfl hpt, sum_comm]
  refine sum_congr rfl fun K hK => ?_
  have hmem := mem_filter.mp hK
  have hcard : K.card = L := hmem.2
  have hKne : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
  rw [shortShapeMass_eq_sum, janossyTrunc_eq_sum hKne, ← sum_sub_distrib]
  refine sum_congr rfl fun U _ => ?_
  simp [hKne, mul_sub, mul_ite, mul_one]

/-! ### Envelope bound and model remainder inequality -/

private theorem choose_envelope_mul {t L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (ht : r + 1 ≤ t) :
    (t - 1).choose (L - 1) * (t - L - 1).choose (r - L) * (t - L) =
      r.choose (L - 1) * (t - 1).choose r * (r - L + 1) := by
  have hsk : L - 1 ≤ r := le_trans (Nat.sub_le L 1) hr
  have hmul := Nat.choose_mul (n := t - 1) (k := r) (s := L - 1) hsk
  have hsub : t - 1 - (L - 1) = t - L := by omega
  have hrL : r - (L - 1) = r - L + 1 := by omega
  rw [hsub, hrL] at hmul
  have hid := Nat.add_one_mul_choose_eq (t - L - 1) (r - L)
  have hn : t - L - 1 + 1 = t - L := by omega
  rw [hn] at hid
  calc
    (t - 1).choose (L - 1) * (t - L - 1).choose (r - L) * (t - L)
        = (t - 1).choose (L - 1) * ((t - L - 1).choose (r - L) * (t - L)) := by ring
    _ = (t - 1).choose (L - 1) * ((t - L).choose (r - L + 1) * (r - L + 1)) := by
          have hswap :
              (t - L - 1).choose (r - L) * (t - L) =
                (t - L).choose (r - L + 1) * (r - L + 1) := by
            rw [Nat.mul_comm, hid]
          rw [hswap]
    _ = ((t - 1).choose (L - 1) * (t - L).choose (r - L + 1)) * (r - L + 1) := by ring
    _ = ((t - 1).choose r * r.choose (L - 1)) * (r - L + 1) := by
          rw [← hmul]
    _ = r.choose (L - 1) * (t - 1).choose r * (r - L + 1) := by ring

private theorem choose_envelope_le {t L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (ht : r + 1 ≤ t) :
    (t - 1).choose (L - 1) * (t - L - 1).choose (r - L) ≤
      r.choose (L - 1) * (t - 1).choose r := by
  have hpos : 0 < t - L := by omega
  have hmul := choose_envelope_mul hL hr ht
  have hfac : r - L + 1 ≤ t - L := by omega
  have hle :
      r.choose (L - 1) * (t - 1).choose r * (r - L + 1) ≤
        r.choose (L - 1) * (t - 1).choose r * (t - L) :=
    Nat.mul_le_mul_left _ hfac
  have : (t - 1).choose (L - 1) * (t - L - 1).choose (r - L) * (t - L) ≤
      r.choose (L - 1) * (t - 1).choose r * (t - L) := by
    rwa [hmul]
  exact Nat.le_of_mul_le_mul_right this hpos

private theorem sum_choose_shift (r N : ℕ) :
    ∑ t ∈ Icc (r + 1) N, ((t - 1).choose r : ℝ) = (N.choose (r + 1) : ℝ) := by
  by_cases h : r + 1 ≤ N
  · have hmap :
        ∑ t ∈ Icc (r + 1) N, ((t - 1).choose r : ℝ) =
          ∑ i ∈ Icc r (N - 1), (i.choose r : ℝ) := by
      refine sum_nbij' (fun t => t - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
      · intro t ht
        have := mem_Icc.mp ht
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro i hi
        have := mem_Icc.mp hi
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro t ht
        have := mem_Icc.mp ht
        omega
      · intro i _
        omega
      · intro _ _
        rfl
    rw [hmap]
    have hnat := Nat.sum_Icc_choose (n := N - 1) (k := r)
    have hN : N - 1 + 1 = N := Nat.sub_add_cancel (by omega)
    exact_mod_cast (by rw [hN] at hnat; exact hnat)
  · have hempty : Icc (r + 1) N = ∅ := by
      exact Finset.Icc_eq_empty_iff.mpr h
    rw [hempty, sum_empty]
    have : N.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.not_le.mp h)
    simp [this]

private theorem countEnvelope_le (L r N : ℕ) (hL : 1 ≤ L) (hr : L ≤ r) :
    countEnvelope L r N ≤ (r.choose (L - 1) : ℝ) * (N.choose (r + 1) : ℝ) := by
  unfold countEnvelope
  have hpt : ∀ t ∈ Icc (r + 1) N,
      (Nat.choose (t - 1) (L - 1) : ℝ) * (Nat.choose (t - L - 1) (r - L) : ℝ) ≤
        (r.choose (L - 1) : ℝ) * ((t - 1).choose r : ℝ) := by
    intro t ht
    have ht' : r + 1 ≤ t := (mem_Icc.mp ht).1
    exact_mod_cast choose_envelope_le hL hr ht'
  calc
    ∑ t ∈ Icc (r + 1) N,
          (Nat.choose (t - 1) (L - 1) : ℝ) * (Nat.choose (t - L - 1) (r - L) : ℝ)
        ≤ ∑ t ∈ Icc (r + 1) N,
            (r.choose (L - 1) : ℝ) * ((t - 1).choose r : ℝ) :=
      sum_le_sum hpt
    _ = (r.choose (L - 1) : ℝ) * ∑ t ∈ Icc (r + 1) N, ((t - 1).choose r : ℝ) := by
          rw [← mul_sum]
    _ = (r.choose (L - 1) : ℝ) * (N.choose (r + 1) : ℝ) := by
          rw [sum_choose_shift]

/-- Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (4.4) (5.2);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem modelRemainder_le {Ω : Finset α} {ν : Finset α → ℝ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U) :
    modelRemainder Ω ν L r
      ≤ (r.choose (L - 1) : ℝ) * countMoment Ω ν (r + 1) := by
  unfold modelRemainder countMoment
  have hpt : ∀ U ∈ Ω.powerset,
      ν U * countEnvelope L r U.card ≤
        ν U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) := by
    intro U hU
    exact mul_le_mul_of_nonneg_left (countEnvelope_le L r U.card hL hr) (hν U hU)
  calc
    ∑ U ∈ Ω.powerset, ν U * countEnvelope L r U.card
        ≤ ∑ U ∈ Ω.powerset,
            ν U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) :=
      sum_le_sum hpt
    _ = (r.choose (L - 1) : ℝ) *
          ∑ U ∈ Ω.powerset, ν U * (U.card.choose (r + 1) : ℝ) := by
      have hfactor : ∀ U ∈ Ω.powerset,
          ν U * ((r.choose (L - 1) : ℝ) * (U.card.choose (r + 1) : ℝ)) =
            (r.choose (L - 1) : ℝ) * (ν U * (U.card.choose (r + 1) : ℝ)) := by
        intro U _
        rw [mul_left_comm]
      rw [sum_congr rfl hfactor, ← mul_sum]

/-! ### Mass partition and deficit algebra -/

private theorem firstL_mem_shapes {Ω U : Finset α} {L : ℕ}
    (hU : U ⊆ Ω) (hLcard : L ≤ U.card) :
    firstL L U ∈ Ω.powerset.filter (fun K => K.card = L) :=
  mem_filter.mpr ⟨mem_powerset.mpr (firstL_subset.trans hU), firstL_card hLcard⟩

private theorem sum_shortShapeMass {Ω : Finset α} {μ : Finset α → ℝ} {L : ℕ} :
    ∑ K ∈ Ω.powerset.filter (fun K => K.card = L), shortShapeMass Ω μ L K =
      ∑ U ∈ Ω.powerset.filter (fun U => L ≤ U.card), μ U := by
  simp only [shortShapeMass]
  rw [sum_comm]
  have hpt : ∀ U ∈ Ω.powerset,
      ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          (if L ≤ U.card ∧ firstL L U = K then μ U else 0) =
        if L ≤ U.card then μ U else 0 := by
    intro U hU
    have hUΩ : U ⊆ Ω := mem_powerset.mp hU
    by_cases hcard : L ≤ U.card
    · have hmem := firstL_mem_shapes hUΩ hcard
      rw [sum_eq_single (firstL L U)]
      · simp [hcard]
      · intro K hK hne
        simp [hcard, hne.symm]
      · intro hnot
        exact (hnot hmem).elim
    · simp [hcard]
  rw [sum_congr rfl hpt, sum_filter]

private theorem sum_short_add_failure {Ω : Finset α} {μ : Finset α → ℝ} {L : ℕ} :
    ∑ K ∈ Ω.powerset.filter (fun K => K.card = L), shortShapeMass Ω μ L K +
        failureMass Ω μ L =
      ∑ U ∈ Ω.powerset, μ U := by
  rw [sum_shortShapeMass, failureMass]
  have h :=
    sum_filter_add_sum_filter_not (s := Ω.powerset) (p := fun U => L ≤ U.card) (f := μ)
  have hset :
      Ω.powerset.filter (fun U => ¬ L ≤ U.card) =
        Ω.powerset.filter (fun U => U.card < L) := by
    ext U
    simp [Nat.not_le]
  rwa [hset] at h

private theorem abs_eq_two_max_sub (x : ℝ) : |x| = 2 * max x 0 - x := by
  rcases le_total x 0 with hx | hx
  · rw [abs_of_nonpos hx, max_eq_right hx]
    ring
  · rw [abs_of_nonneg hx, max_eq_left hx]
    ring

private theorem shapeL1_eq_two_def {Ω : Finset α} {μ ν : Finset α → ℝ} {L : ℕ}
    (hmass : ∑ U ∈ Ω.powerset, μ U = ∑ U ∈ Ω.powerset, ν U) :
    shapeL1 Ω μ ν L + failureMass Ω μ L =
      2 * ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            max (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) 0 +
        failureMass Ω ν L := by
  unfold shapeL1
  have habs : ∀ K,
      |shortShapeMass Ω μ L K - shortShapeMass Ω ν L K| =
        2 * max (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) 0 -
          (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) := by
    intro K
    simpa [abs_sub_comm] using
      abs_eq_two_max_sub (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K)
  rw [sum_congr rfl fun K _ => habs K, sum_sub_distrib, ← mul_sum]
  have hdiff :
      ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) =
        (∑ U ∈ Ω.powerset, ν U - failureMass Ω ν L) -
          (∑ U ∈ Ω.powerset, μ U - failureMass Ω μ L) := by
    rw [sum_sub_distrib]
    have hμ := sum_short_add_failure (μ := μ) (Ω := Ω) (L := L)
    have hν := sum_short_add_failure (μ := ν) (Ω := Ω) (L := L)
    linarith
  rw [hdiff, hmass]
  ring

/-! ### Adverse reindexing -/

private noncomputable def truncDs (Ω : Finset α) (L r : ℕ) (K : Finset α) :
    Finset (Finset α) :=
  if hK : K.Nonempty then
    (beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L)
  else
    ∅

private theorem truncDs_eq {Ω : Finset α} {L r : ℕ} {K : Finset α} (hK : K.Nonempty) :
    truncDs Ω L r K =
      (beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L) := by
  simp [truncDs, hK]

private theorem pos_sum_le_sum_pos {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    max (∑ i ∈ s, f i) 0 ≤ ∑ i ∈ s, max (f i) 0 := by
  have h1 : ∑ i ∈ s, f i ≤ ∑ i ∈ s, max (f i) 0 :=
    sum_le_sum fun _ _ => le_max_left _ _
  have h2 : 0 ≤ ∑ i ∈ s, max (f i) 0 :=
    sum_nonneg fun _ _ => le_max_right _ _
  exact max_le h1 h2

private theorem disjoint_beforeOutside {Ω K : Finset α} (hK : K.Nonempty) :
    Disjoint K (beforeOutside Ω K hK) :=
  disjoint_left.mpr fun x hxK hxB => (mem_filter.mp hxB).2.2 hxK

private theorem card_union_trunc {Ω K D : Finset α} {L : ℕ} (hK : K.Nonempty)
    (hcard : K.card = L) (hD : D ⊆ beforeOutside Ω K hK) :
    (K ∪ D).card = L + D.card := by
  have hdisj : Disjoint K D :=
    (disjoint_beforeOutside (Ω := Ω) hK).mono_right hD
  rw [card_union_of_disjoint hdisj, hcard]

private theorem trunc_pair_maps {Ω : Finset α} {L r : ℕ} {K D : Finset α}
    (hL : 1 ≤ L) (hr : L ≤ r) (hKmem : K ∈ Ω.powerset.filter (fun K => K.card = L))
    (hD : D ∈ truncDs Ω L r K) :
    K ∪ D ∈ Ω.powerset.filter (fun H => L ≤ H.card ∧ H.card ≤ r) := by
  have hK' := mem_filter.mp hKmem
  have hKΩ : K ⊆ Ω := mem_powerset.mp hK'.1
  have hcard : K.card = L := hK'.2
  have hKne : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
  have hD' : D ∈ (beforeOutside Ω K hKne).powerset.filter (fun D => D.card ≤ r - L) := by
    simpa [truncDs, hKne] using hD
  have hDB : D ⊆ beforeOutside Ω K hKne := mem_powerset.mp (mem_filter.mp hD').1
  have hDΩ : D ⊆ Ω := hDB.trans (filter_subset _ _)
  have hcardD : D.card ≤ r - L := (mem_filter.mp hD').2
  have hunion : K ∪ D ⊆ Ω := union_subset hKΩ hDΩ
  have hcardU : (K ∪ D).card = L + D.card := card_union_trunc hKne hcard hDB
  refine mem_filter.mpr ⟨mem_powerset.mpr hunion, ?_, ?_⟩
  · omega
  · omega

private theorem fiber_card_eq' {Ω H : Finset α} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hHΩ : H ⊆ Ω) (hHne : H.Nonempty)
    (hLo : L ≤ H.card) (hHi : H.card ≤ r) :
    (((Ω.powerset.filter (fun K => K.card = L)).sigma (fun K => truncDs Ω L r K)).filter
        (fun p => p.1 ∪ p.2 = H)).card =
      (H.card - 1).choose (L - 1) := by
  set z := H.max' hHne
  let s :=
    ((Ω.powerset.filter (fun K => K.card = L)).sigma (fun K => truncDs Ω L r K)).filter
      (fun p => p.1 ∪ p.2 = H)
  let t := H.powerset.filter (fun K => K.card = L ∧ z ∈ K)
  have hcardt : t.card = (H.card - 1).choose (L - 1) :=
    endpoint_multiplicity hHne hL hLo
  refine Eq.trans ?_ hcardt
  refine Finset.card_nbij'
    (i := fun p : Σ _ : Finset α, Finset α => p.1)
    (j := fun K : Finset α => (⟨K, H \ K⟩ : Σ _ : Finset α, Finset α))
    ?_ ?_ ?_ ?_
  · intro p hp
    have hp' := mem_filter.mp hp
    have hσ := mem_sigma.mp hp'.1
    have hK' := mem_filter.mp hσ.1
    have hKΩ : p.1 ⊆ Ω := mem_powerset.mp hK'.1
    have hcard : p.1.card = L := hK'.2
    have hKne : p.1.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
    have hD : p.2 ∈ truncDs Ω L r p.1 := hσ.2
    have hD' : p.2 ∈ (beforeOutside Ω p.1 hKne).powerset.filter
        (fun D => D.card ≤ r - L) := by
      simpa [truncDs, hKne] using hD
    have hDB : p.2 ⊆ beforeOutside Ω p.1 hKne :=
      mem_powerset.mp (mem_filter.mp hD').1
    have hEq : p.1 ∪ p.2 = H := hp'.2
    have hKsub : p.1 ⊆ H := by
      rw [← hEq]
      exact subset_union_left
    have hmax : p.1.max' hKne = z := by
      have hHmax : ∀ x ∈ p.2, x < p.1.max' hKne := fun x hx =>
        (mem_filter.mp (hDB hx)).2.1
      have hunion_ne : (p.1 ∪ p.2).Nonempty := by
        rw [hEq]
        exact hHne
      have hle : (p.1 ∪ p.2).max' hunion_ne ≤ p.1.max' hKne :=
        max'_le _ _ _ fun x hx => by
          rw [mem_union] at hx
          rcases hx with hx | hx
          · exact le_max' _ _ hx
          · exact (hHmax x hx).le
      have hge : p.1.max' hKne ≤ (p.1 ∪ p.2).max' hunion_ne :=
        le_max' _ _ (mem_union_left _ (max'_mem _ _))
      have hEqmax : (p.1 ∪ p.2).max' hunion_ne = z := by
        simp [hEq, z]
      exact le_antisymm (hEqmax ▸ hge) (hEqmax ▸ hle)
    have hzK : z ∈ p.1 := by
      have := max'_mem p.1 hKne
      simpa [hmax] using this
    exact mem_filter.mpr ⟨mem_powerset.mpr hKsub, hcard, hzK⟩
  · intro K hK
    have hK' := mem_filter.mp hK
    have hKH : K ⊆ H := mem_powerset.mp hK'.1
    have hcard : K.card = L := hK'.2.1
    have hzK : z ∈ K := hK'.2.2
    have hKne : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
    have hKΩ : K ⊆ Ω := hKH.trans hHΩ
    have hKmem : K ∈ Ω.powerset.filter (fun K => K.card = L) :=
      mem_filter.mpr ⟨mem_powerset.mpr hKΩ, hcard⟩
    have hDsub : H \ K ⊆ beforeOutside Ω K hKne := by
      intro x hx
      have hx' := mem_sdiff.mp hx
      have hxH : x ∈ H := hx'.1
      have hxK : x ∉ K := hx'.2
      have hlt : x < K.max' hKne := by
        have hxle : x ≤ H.max' hHne := le_max' _ _ hxH
        have hmax : K.max' hKne = z :=
          (max_eq_iff_mem hKne hHne hKH).mpr hzK
        have hne : x ≠ z := by
          intro hxz
          exact hxK (hxz ▸ hzK)
        have hxle' : x ≤ K.max' hKne := by
          simpa [hmax] using hxle
        have hneK : x ≠ K.max' hKne := by
          simpa [hmax] using hne
        exact lt_of_le_of_ne hxle' hneK
      exact mem_filter.mpr ⟨hHΩ hxH, hlt, hxK⟩
    have hDcard : (H \ K).card ≤ r - L := by
      have hdisj : Disjoint K (H \ K) := disjoint_sdiff
      have : (K ∪ (H \ K)).card = H.card := by
        rw [union_sdiff_of_subset hKH]
      have : K.card + (H \ K).card = H.card := by
        rwa [card_union_of_disjoint hdisj] at this
      omega
    have hDmem : H \ K ∈ truncDs Ω L r K := by
      simp [truncDs, hKne, mem_filter, mem_powerset, hDsub, hDcard]
    have hσ : (⟨K, H \ K⟩ : Σ _ : Finset α, Finset α) ∈
        (Ω.powerset.filter (fun K => K.card = L)).sigma (fun K => truncDs Ω L r K) :=
      mem_sigma.mpr ⟨hKmem, hDmem⟩
    have hEq : K ∪ (H \ K) = H := union_sdiff_of_subset hKH
    exact mem_filter.mpr ⟨hσ, hEq⟩
  · intro p hp
    have hp' := mem_filter.mp hp
    have hEq : p.1 ∪ p.2 = H := hp'.2
    have hσ := mem_sigma.mp hp'.1
    have hK' := mem_filter.mp hσ.1
    have hcard : p.1.card = L := hK'.2
    have hKne : p.1.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
    have hD : p.2 ∈ truncDs Ω L r p.1 := hσ.2
    have hD' : p.2 ∈ (beforeOutside Ω p.1 hKne).powerset.filter
        (fun D => D.card ≤ r - L) := by
      simpa [truncDs, hKne] using hD
    have hDB : p.2 ⊆ beforeOutside Ω p.1 hKne :=
      mem_powerset.mp (mem_filter.mp hD').1
    have hdisj : Disjoint p.1 p.2 :=
      (disjoint_beforeOutside (Ω := Ω) hKne).mono_right hDB
    have : p.2 = H \ p.1 := by
      rw [← hEq, union_sdiff_cancel_left hdisj]
    exact Sigma.ext rfl (by rw [this])
  · intro K hK
    rfl

private theorem signed_inc (Ω : Finset α) (μ ν : Finset α → ℝ) (L : ℕ) (H : Finset α) :
    (-1 : ℝ) ^ (H.card - L) * (inclusionMass Ω ν H - inclusionMass Ω μ H) =
      (-1 : ℝ) ^ (H.card - L + 1) * (inclusionMass Ω μ H - inclusionMass Ω ν H) := by
  have : (-1 : ℝ) ^ (H.card - L + 1) = -((-1 : ℝ) ^ (H.card - L)) := by
    rw [pow_succ]
    ring
  rw [this]
  ring

private theorem janossy_diff_eq {Ω : Finset α} {μ ν : Finset α → ℝ} {L r : ℕ}
    {K : Finset α} (hK : K.Nonempty) :
    janossyTrunc Ω ν L r K - janossyTrunc Ω μ L r K =
      ∑ D ∈ truncDs Ω L r K,
        (-1 : ℝ) ^ D.card *
          (inclusionMass Ω ν (K ∪ D) - inclusionMass Ω μ (K ∪ D)) := by
  unfold janossyTrunc truncDs
  rw [dif_pos hK, dif_pos hK, dif_pos hK]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun D _ => ?_
  ring

private theorem sum_pospart_janossy_le {Ω : Finset α} {μ ν : Finset α → ℝ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) :
    ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        max (janossyTrunc Ω ν L r K - janossyTrunc Ω μ L r K) 0 ≤
      adverseBudget Ω μ ν L r := by
  let shapes := Ω.powerset.filter (fun K => K.card = L)
  let s := shapes.sigma (fun K => truncDs Ω L r K)
  let t := Ω.powerset.filter (fun H => L ≤ H.card ∧ H.card ≤ r)
  have hmaps : ∀ p ∈ s, p.1 ∪ p.2 ∈ t := by
    intro p hp
    have hσ := mem_sigma.mp hp
    exact trunc_pair_maps hL hr hσ.1 hσ.2
  have hKsum :
      ∑ K ∈ shapes, max (janossyTrunc Ω ν L r K - janossyTrunc Ω μ L r K) 0 ≤
        ∑ K ∈ shapes, ∑ D ∈ truncDs Ω L r K,
          max ((-1 : ℝ) ^ D.card *
            (inclusionMass Ω ν (K ∪ D) - inclusionMass Ω μ (K ∪ D))) 0 := by
    refine sum_le_sum fun K hK => ?_
    have hmem := mem_filter.mp hK
    have hcard : K.card = L := hmem.2
    have hKne : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
    have hdiff := janossy_diff_eq (Ω := Ω) (μ := μ) (ν := ν) (L := L) (r := r) hKne
    have : truncDs Ω L r K =
        (beforeOutside Ω K hKne).powerset.filter (fun D => D.card ≤ r - L) :=
      truncDs_eq hKne
    rw [hdiff]
    exact pos_sum_le_sum_pos _ _
  have hsigma :
      ∑ K ∈ shapes, ∑ D ∈ truncDs Ω L r K,
          max ((-1 : ℝ) ^ D.card *
            (inclusionMass Ω ν (K ∪ D) - inclusionMass Ω μ (K ∪ D))) 0 =
        ∑ p ∈ s,
          max ((-1 : ℝ) ^ p.2.card *
            (inclusionMass Ω ν (p.1 ∪ p.2) - inclusionMass Ω μ (p.1 ∪ p.2))) 0 := by
    rw [sum_sigma']
  refine le_trans hKsum ?_
  rw [hsigma]
  have hfiber :=
    (sum_fiberwise_of_maps_to' (s := s) (t := t) (g := fun p => p.1 ∪ p.2) hmaps
      (fun H =>
        max ((-1 : ℝ) ^ (H.card - L) *
          (inclusionMass Ω ν H - inclusionMass Ω μ H)) 0)).symm
  have hrewrite :
      ∑ p ∈ s,
          max ((-1 : ℝ) ^ p.2.card *
            (inclusionMass Ω ν (p.1 ∪ p.2) - inclusionMass Ω μ (p.1 ∪ p.2))) 0 =
        ∑ p ∈ s,
          max ((-1 : ℝ) ^ ((p.1 ∪ p.2).card - L) *
            (inclusionMass Ω ν (p.1 ∪ p.2) - inclusionMass Ω μ (p.1 ∪ p.2))) 0 := by
    refine sum_congr rfl fun p hp => ?_
    have hσ := mem_sigma.mp hp
    have hK' := mem_filter.mp hσ.1
    have hcard : p.1.card = L := hK'.2
    have hKne : p.1.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
    have hD : p.2 ∈ truncDs Ω L r p.1 := hσ.2
    have hD' : p.2 ∈ (beforeOutside Ω p.1 hKne).powerset.filter
        (fun D => D.card ≤ r - L) := by
      simpa [truncDs, hKne] using hD
    have hDB : p.2 ⊆ beforeOutside Ω p.1 hKne :=
      mem_powerset.mp (mem_filter.mp hD').1
    have hcu : (p.1 ∪ p.2).card = L + p.2.card :=
      card_union_trunc hKne hcard hDB
    have : (p.1 ∪ p.2).card - L = p.2.card := by omega
    simp [this]
  rw [hrewrite, hfiber]
  have hconst :
      ∑ H ∈ t,
          ∑ _p ∈ s.filter (fun p => p.1 ∪ p.2 = H),
            max ((-1 : ℝ) ^ (H.card - L) *
              (inclusionMass Ω ν H - inclusionMass Ω μ H)) 0 =
        ∑ H ∈ t,
          ((s.filter (fun p => p.1 ∪ p.2 = H)).card : ℝ) *
            max ((-1 : ℝ) ^ (H.card - L) *
              (inclusionMass Ω ν H - inclusionMass Ω μ H)) 0 := by
    refine sum_congr rfl fun H _ => ?_
    rw [sum_const, nsmul_eq_mul]
  rw [hconst]
  have hcard :
      ∑ H ∈ t,
          ((s.filter (fun p => p.1 ∪ p.2 = H)).card : ℝ) *
            max ((-1 : ℝ) ^ (H.card - L) *
              (inclusionMass Ω ν H - inclusionMass Ω μ H)) 0 =
        ∑ H ∈ t,
          (Nat.choose (H.card - 1) (L - 1) : ℝ) *
            max ((-1 : ℝ) ^ (H.card - L + 1) *
              (inclusionMass Ω μ H - inclusionMass Ω ν H)) 0 := by
    refine sum_congr rfl fun H hH => ?_
    have hH' := mem_filter.mp hH
    have hHΩ : H ⊆ Ω := mem_powerset.mp hH'.1
    have ⟨hLo, hHi⟩ := hH'.2
    have hHne : H.Nonempty := nonempty_of_card_ge hL hLo
    have hc := fiber_card_eq' (Ω := Ω) (H := H) (L := L) (r := r)
      hL hr hHΩ hHne hLo hHi
    have hsign := signed_inc Ω μ ν L H
    rw [hc]
    refine congrArg (fun z => (Nat.choose (H.card - 1) (L - 1) : ℝ) * z) ?_
    refine congrArg (fun z => max z 0) hsign
  rw [hcard]
  unfold adverseBudget adverseLayer
  have hgroup :
      ∑ H ∈ t,
          (Nat.choose (H.card - 1) (L - 1) : ℝ) *
            max ((-1 : ℝ) ^ (H.card - L + 1) *
              (inclusionMass Ω μ H - inclusionMass Ω ν H)) 0 =
        ∑ j ∈ Icc L r, (Nat.choose (j - 1) (L - 1) : ℝ) *
          ∑ H ∈ Ω.powerset.filter (fun H => H.card = j),
            max ((-1 : ℝ) ^ (j - L + 1) *
              (inclusionMass Ω μ H - inclusionMass Ω ν H)) 0 := by
    have ht :
        t = (Icc L r).biUnion (fun j => Ω.powerset.filter (fun H => H.card = j)) := by
      ext H
      simp only [mem_biUnion, mem_Icc, mem_filter, mem_powerset, t]
      constructor
      · intro h
        exact ⟨H.card, h.2, h.1, rfl⟩
      · intro ⟨j, hj, hH, hcard⟩
        exact ⟨hH, hcard ▸ hj.1, hcard ▸ hj.2⟩
    have hdisj :
        (Icc L r : Set ℕ).PairwiseDisjoint
          (fun j => Ω.powerset.filter (fun H => H.card = j)) := by
      intro a _ b _ hab
      refine disjoint_left.mpr ?_
      intro H hHa hHb
      exact hab ((mem_filter.mp hHa).2.symm.trans (mem_filter.mp hHb).2)
    rw [ht, sum_biUnion hdisj]
    refine sum_congr rfl fun j hj => ?_
    have hsum :
        ∑ H ∈ Ω.powerset.filter (fun H => H.card = j),
            (Nat.choose (H.card - 1) (L - 1) : ℝ) *
              max ((-1 : ℝ) ^ (H.card - L + 1) *
                (inclusionMass Ω μ H - inclusionMass Ω ν H)) 0 =
          ∑ H ∈ Ω.powerset.filter (fun H => H.card = j),
            (Nat.choose (j - 1) (L - 1) : ℝ) *
              max ((-1 : ℝ) ^ (j - L + 1) *
                (inclusionMass Ω μ H - inclusionMass Ω ν H)) 0 := by
      refine sum_congr rfl fun H hH => ?_
      have hcard : H.card = j := (mem_filter.mp hH).2
      simp [hcard]
    rw [hsum, ← mul_sum]
  exact le_of_eq hgroup

private theorem pospart_le_of_le {a b c : ℝ} (h : a ≤ b + c) (hc : 0 ≤ c) :
    max a 0 ≤ max b 0 + c :=
  max_le (h.trans (add_le_add (le_max_left b 0) le_rfl))
    (add_nonneg (le_max_right b 0) hc)

private theorem def_le_budget {Ω : Finset α} {μ ν : Finset α → ℝ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U) :
    ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        max (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) 0 ≤
      adverseBudget Ω μ ν L r + modelRemainder Ω ν L r := by
  have hpt : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L),
      max (shortShapeMass Ω ν L K - shortShapeMass Ω μ L K) 0 ≤
        max (janossyTrunc Ω ν L r K - janossyTrunc Ω μ L r K) 0 +
          (shortShapeMass Ω ν L K - janossyTrunc Ω ν L r K) := by
    intro K hK
    have hcard : K.card = L := (mem_filter.mp hK).2
    have hJμ := janossyTrunc_le_shortShapeMass (Ω := Ω) (μ := μ) (K := K)
      hL hr hpar hcard hμ
    have hJν := janossyTrunc_le_shortShapeMass (Ω := Ω) (μ := ν) (K := K)
      hL hr hpar hcard hν
    have hle :
        shortShapeMass Ω ν L K - shortShapeMass Ω μ L K ≤
          (janossyTrunc Ω ν L r K - janossyTrunc Ω μ L r K) +
            (shortShapeMass Ω ν L K - janossyTrunc Ω ν L r K) := by
      linarith
    exact pospart_le_of_le hle (sub_nonneg.mpr hJν)
  have hsum := sum_le_sum hpt
  have hsplit :
      ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          (max (janossyTrunc Ω ν L r K - janossyTrunc Ω μ L r K) 0 +
            (shortShapeMass Ω ν L K - janossyTrunc Ω ν L r K)) =
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            max (janossyTrunc Ω ν L r K - janossyTrunc Ω μ L r K) 0 +
          ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            (shortShapeMass Ω ν L K - janossyTrunc Ω ν L r K) :=
    sum_add_distrib
  have hR := modelRemainder_eq_shapeResidual (Ω := Ω) (ν := ν) (L := L) (r := r)
    hL hr hpar
  have hW := sum_pospart_janossy_le (Ω := Ω) (μ := μ) (ν := ν) (L := L) (r := r) hL hr
  linarith

/-- Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem stoppedShapeL1_add_failure_le {Ω : Finset α} {μ ν : Finset α → ℝ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L))
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U)
    (hmass : ∑ U ∈ Ω.powerset, μ U = ∑ U ∈ Ω.powerset, ν U) :
    shapeL1 Ω μ ν L + failureMass Ω μ L
      ≤ failureMass Ω ν L
        + 2 * modelRemainder Ω ν L r
        + 2 * adverseBudget Ω μ ν L r := by
  have hid := shapeL1_eq_two_def (Ω := Ω) (μ := μ) (ν := ν) (L := L) hmass
  have hdef := def_le_budget (Ω := Ω) (μ := μ) (ν := ν) (L := L) (r := r)
    hL hr hpar hμ hν
  linarith

/-- Relative layer bound implies a relative adverse budget.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem adverseBudget_le_of_layer {Ω : Finset α} {μ ν : Finset α → ℝ} {L r : ℕ}
    {ε : ℝ} (hL : 1 ≤ L) (hr : L ≤ r)
    (hA : ∀ j ∈ Icc L r, adverseLayer Ω μ ν L j ≤ ε * countMoment Ω ν j) :
    adverseBudget Ω μ ν L r
      ≤ ε * ∑ j ∈ Icc L r,
          (Nat.choose (j - 1) (L - 1) : ℝ) * countMoment Ω ν j := by
  unfold adverseBudget
  have hpt : ∀ j ∈ Icc L r,
      (Nat.choose (j - 1) (L - 1) : ℝ) * adverseLayer Ω μ ν L j ≤
        (Nat.choose (j - 1) (L - 1) : ℝ) * (ε * countMoment Ω ν j) := by
    intro j hj
    have hnn : (0 : ℝ) ≤ (Nat.choose (j - 1) (L - 1) : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left (hA j hj) hnn
  calc
    ∑ j ∈ Icc L r, (Nat.choose (j - 1) (L - 1) : ℝ) * adverseLayer Ω μ ν L j
        ≤ ∑ j ∈ Icc L r,
            (Nat.choose (j - 1) (L - 1) : ℝ) * (ε * countMoment Ω ν j) :=
      sum_le_sum hpt
    _ = ε * ∑ j ∈ Icc L r,
          (Nat.choose (j - 1) (L - 1) : ℝ) * countMoment Ω ν j := by
      refine Eq.trans (sum_congr rfl fun j _ => mul_left_comm _ ε _) ?_
      rw [← mul_sum]

/-- Mean of a bounded stopped observable differs from the model shape mean
by at most `shapeL1 + failureMass μ`.

Source: `rounds/round99/01_gpt_transfer_final_push_and_lean.md` (5.1);
`rounds/round99/01_grok_transfer_contract.md`;
`rounds/round99/06_gpt_transfer_independent_audit.md`.
Contract: API
Audit: GREEN -/
theorem abs_stopped_eval_sub_le {Ω : Finset α} {μ ν : Finset α → ℝ} {L : ℕ}
    {φ ψ : Finset α → ℝ}
    (hφ : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), |φ K| ≤ 1)
    (hψ : ∀ U ∈ Ω.powerset, |ψ U| ≤ 1)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U) :
    |∑ U ∈ Ω.powerset, μ U *
          (if L ≤ U.card then φ (firstL L U) else ψ U) -
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          shortShapeMass Ω ν L K * φ K| ≤
      shapeL1 Ω μ ν L + failureMass Ω μ L := by
  have hgood :
      ∑ U ∈ Ω.powerset.filter (fun U => L ≤ U.card), μ U * φ (firstL L U) =
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          shortShapeMass Ω μ L K * φ K := by
    have hpt : ∀ U ∈ Ω.powerset,
        (if L ≤ U.card then μ U * φ (firstL L U) else 0) =
          ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            (if L ≤ U.card ∧ firstL L U = K then μ U * φ K else 0) := by
      intro U hU
      have hUΩ : U ⊆ Ω := mem_powerset.mp hU
      by_cases hcard : L ≤ U.card
      · have hmem := firstL_mem_shapes hUΩ hcard
        rw [sum_eq_single (firstL L U)]
        · simp [hcard]
        · intro K hK hne
          simp [hcard, hne.symm]
        · intro hnot
          exact (hnot hmem).elim
      · simp [hcard]
    have : ∑ U ∈ Ω.powerset, (if L ≤ U.card then μ U * φ (firstL L U) else 0) =
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          shortShapeMass Ω μ L K * φ K := by
      rw [sum_congr rfl hpt, sum_comm]
      refine sum_congr rfl fun K hK => ?_
      unfold shortShapeMass
      have hfact : ∀ U,
          (if L ≤ U.card ∧ firstL L U = K then μ U * φ K else 0) =
            (if L ≤ U.card ∧ firstL L U = K then μ U else 0) * φ K := by
        intro U
        split_ifs <;> ring
      rw [sum_congr rfl fun U _ => hfact U, sum_mul]
    rw [← this, sum_filter]
  have hsplit :
      ∑ U ∈ Ω.powerset, μ U * (if L ≤ U.card then φ (firstL L U) else ψ U) =
        ∑ U ∈ Ω.powerset.filter (fun U => L ≤ U.card), μ U * φ (firstL L U) +
          ∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U * ψ U := by
    have h := sum_filter_add_sum_filter_not (s := Ω.powerset)
      (p := fun U => L ≤ U.card)
      (f := fun U => μ U * (if L ≤ U.card then φ (firstL L U) else ψ U))
    have hgood' :
        ∑ U ∈ Ω.powerset.filter (fun U => L ≤ U.card),
            μ U * (if L ≤ U.card then φ (firstL L U) else ψ U) =
          ∑ U ∈ Ω.powerset.filter (fun U => L ≤ U.card), μ U * φ (firstL L U) := by
      refine sum_congr rfl fun U hU => ?_
      have := (mem_filter.mp hU).2
      simp [this]
    have hbad' :
        ∑ U ∈ Ω.powerset.filter (fun U => ¬ L ≤ U.card),
            μ U * (if L ≤ U.card then φ (firstL L U) else ψ U) =
          ∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U * ψ U := by
      have hset : Ω.powerset.filter (fun U => ¬ L ≤ U.card) =
          Ω.powerset.filter (fun U => U.card < L) := by
        ext U
        simp [Nat.not_le]
      rw [hset]
      refine sum_congr rfl fun U hU => ?_
      have := (mem_filter.mp hU).2
      have : ¬ L ≤ U.card := Nat.not_le.mpr this
      simp [this]
    linarith
  rw [hsplit, hgood]
  have hdiff :
      ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            shortShapeMass Ω μ L K * φ K +
          ∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U * ψ U -
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          shortShapeMass Ω ν L K * φ K =
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            (shortShapeMass Ω μ L K - shortShapeMass Ω ν L K) * φ K +
          ∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U * ψ U := by
    have hsub :
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
              shortShapeMass Ω μ L K * φ K -
            ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
              shortShapeMass Ω ν L K * φ K =
          ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            (shortShapeMass Ω μ L K - shortShapeMass Ω ν L K) * φ K := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun K _ => ?_
      ring
    linarith
  rw [hdiff]
  have h1 :
      |∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          (shortShapeMass Ω μ L K - shortShapeMass Ω ν L K) * φ K| ≤
        shapeL1 Ω μ ν L := by
    unfold shapeL1
    calc
      |∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            (shortShapeMass Ω μ L K - shortShapeMass Ω ν L K) * φ K|
          ≤ ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
              |(shortShapeMass Ω μ L K - shortShapeMass Ω ν L K) * φ K| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            |shortShapeMass Ω μ L K - shortShapeMass Ω ν L K| * |φ K| := by
            refine sum_congr rfl fun K _ => abs_mul _ _
      _ ≤ ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            |shortShapeMass Ω μ L K - shortShapeMass Ω ν L K| * 1 :=
          sum_le_sum fun K hK =>
            mul_le_mul_of_nonneg_left (hφ K hK) (abs_nonneg _)
      _ = ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
            |shortShapeMass Ω μ L K - shortShapeMass Ω ν L K| := by
            simp
  have h2 :
      |∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U * ψ U| ≤
        failureMass Ω μ L := by
    unfold failureMass
    calc
      |∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U * ψ U|
          ≤ ∑ U ∈ Ω.powerset.filter (fun U => U.card < L), |μ U * ψ U| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U * |ψ U| := by
            refine sum_congr rfl fun U hU => ?_
            have hμU := hμ U (mem_filter.mp hU).1
            rw [abs_mul, abs_of_nonneg hμU]
      _ ≤ ∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U * 1 :=
          sum_le_sum fun U hU =>
            mul_le_mul_of_nonneg_left (hψ U (mem_filter.mp hU).1)
              (hμ U (mem_filter.mp hU).1)
      _ = ∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U := by simp
  calc
    |∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          (shortShapeMass Ω μ L K - shortShapeMass Ω ν L K) * φ K +
        ∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U * ψ U|
        ≤ |∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
              (shortShapeMass Ω μ L K - shortShapeMass Ω ν L K) * φ K| +
          |∑ U ∈ Ω.powerset.filter (fun U => U.card < L), μ U * ψ U| :=
      abs_add_le _ _
    _ ≤ shapeL1 Ω μ ν L + failureMass Ω μ L := add_le_add h1 h2

end PrimeGapNormality.Prime.Stopped
