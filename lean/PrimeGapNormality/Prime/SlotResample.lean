import PrimeGapNormality.Prime.Merge
import PrimeGapNormality.Prime.RankDelete
import PrimeGapNormality.Prime.Coupling
import PrimeGapNormality.Prime.GapPolynomialPhase
import PrimeGapNormality.Prime.Fourier
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bernoulli slot resampling at a deleted interior rank

Delete the interior rank-`j` survivor `u`, hold the remaining strictly
increasing frame `F` fixed, and average `e(phase)` over the open slot
`(a,c) ∩ A`. Independent Bernoulli masses of `insertAt F j u` are
constant on the slot (paper (6.2)), so the deleted point is uniform on
`A ∩ (left,right)`. The model phase sum then factors as the common
frame weight times the frozen character times the slot sum of
`e(freeGapPolyPhase)`.

Lean ranks are 0-based: paper `1 ≤ j < L` is `j + 1 < L`. Root `0` is
the phase origin, not an element of `A`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` complete frames and
(eq:freephase); `rounds/round97/02_gpt_khl_normality_extension.md`
(6.1)–(6.2); `lean/PRIME_NORMALITY.md` RankDelete.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Polynomial

set_option maxHeartbeats 800000

/-! ### Slot, frame weight, frozen phase -/

/-- Candidates in the open deletion slot `(left,right) ∩ A`. Paper
`A ∩ W_F` with `W_F = (a,c)`.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` (6.1).
Contract: API
Audit: GREEN -/
def openSlot (A : Finset ℕ) (F : List ℕ) (j : ℕ) : Finset ℕ :=
  A.filter (fun u => (deletionSlot F j).1 < u ∧ u < (deletionSlot F j).2)

/-- Common Bernoulli mass of every preimage `F ∪ {u}` of a remaining
frame `F`. Paper (6.2): `ρ^{|F|+1}(1-ρ)^{|A|-|F|-1}`.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` (6.2);
`RankDelete.frame_bernoulli_weight_const`.
Contract: API
Audit: GREEN -/
noncomputable def frameBernoulliWeight (A : Finset ℕ) (ρ : ℝ) (F : Finset ℕ) : ℝ :=
  ρ ^ (F.card + 1) * (1 - ρ) ^ (A.card - F.card - 1)

/-- `u`-independent remainder of the truncated gap-polynomial phase:
`Φ_L(insertAt F j u) = frozen + freeGapPolyPhase(u)`. The dummy
insertion value `0` is algebraic, not a slot point.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:freephase);
`GapPolynomialPhase.finiteGapPolyPhase_sub_insertAt`.
Contract: API
Audit: GREEN -/
noncomputable def frozenGapPolyPhase (P : ℝ[X]) (b L j : ℕ) (F : List ℕ) : ℝ :=
  finiteGapPolyPhase P b L (insertAt F j 0) -
    freeGapPolyPhase P b j (deletionSlot F j).1 (0 : ℕ) (deletionSlot F j).2

/-- Uniform average of a complex test on a finite slot. The empty slot
uses the field convention `0/0 = 0`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` complete frames.
Contract: API
Audit: GREEN -/
noncomputable def slotAverage (s : Finset ℕ) (f : ℕ → ℂ) : ℂ :=
  (∑ u ∈ s, f u) / (s.card : ℂ)

/-! ### Circle character (local; `e` lives in Fourier) -/

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

/-! ### Slot arithmetic -/

theorem mem_openSlot {A : Finset ℕ} {F : List ℕ} {j u : ℕ} :
    u ∈ openSlot A F j ↔
      u ∈ A ∧ (deletionSlot F j).1 < u ∧ u < (deletionSlot F j).2 :=
  mem_filter

/-- A point of the open slot forces the right neighbour to exist, hence
`j < F.length`. -/
theorem lt_length_of_mem_deletionSlot {F : List ℕ} {j u : ℕ}
    (hu : u < (deletionSlot F j).2) : j < F.length := by
  by_contra h
  have hge : F.length ≤ j := Nat.le_of_not_gt h
  have hnone : F[j]? = none := getElem?_neg F j (Nat.not_lt.mpr hge)
  have hright : (deletionSlot F j).2 = 0 := by
    unfold deletionSlot
    simp [List.getD_eq_getElem?_getD, hnone]
  exact Nat.not_lt_zero u (hright ▸ hu)

/-- An open-slot point is not a surviving frame site. Merge analogue:
`not_mem_of_mem_mergeSlot`. -/
theorem not_mem_of_mem_deletionSlot {F : List ℕ} {j u : ℕ}
    (hF : F.Pairwise (· < ·))
    (hu : (deletionSlot F j).1 < u ∧ u < (deletionSlot F j).2) :
    u ∉ F := by
  intro hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  have hj : j < F.length := lt_length_of_mem_deletionSlot hu.2
  have hright : (deletionSlot F j).2 = F[j] := deletionSlot_right_eq hj
  have hpw := List.pairwise_iff_getElem.mp hF
  by_cases hij : i < j
  · have hjpos : 0 < j := Nat.zero_lt_of_lt hij
    have hjF : j - 1 < F.length := by omega
    have hleft : (deletionSlot F j).1 = F[j - 1] :=
      deletionSlot_left_eq_of_pos hjpos hjF
    have hi_le : i ≤ j - 1 := by omega
    rcases Nat.lt_or_eq_of_le hi_le with hlt | heq
    · have hlt' : F[i] < F[j - 1] := hpw i (j - 1) hi hjF hlt
      have hgt : F[j - 1] < F[i] := by simpa [hleft] using hu.1
      exact lt_irrefl _ (lt_trans hlt' hgt)
    · have h1 : F[j - 1] < F[i] := by simpa [hleft] using hu.1
      subst heq
      exact lt_irrefl (F[j - 1]) h1
  · have hji : j ≤ i := by omega
    rcases Nat.lt_or_eq_of_le hji with hlt | heq
    · have hlt' : F[j] < F[i] := hpw j i hj hi hlt
      have hgt : F[i] < F[j] := by simpa [hright] using hu.2
      exact lt_irrefl _ (lt_trans hgt hlt')
    · have h2 : F[i] < F[j] := by simpa [hright] using hu.2
      subst heq
      exact lt_irrefl _ h2

theorem not_mem_toFinset_of_mem_deletionSlot {F : List ℕ} {j u : ℕ}
    (hF : F.Pairwise (· < ·))
    (hu : (deletionSlot F j).1 < u ∧ u < (deletionSlot F j).2) :
    u ∉ F.toFinset := by
  simpa [List.mem_toFinset] using not_mem_of_mem_deletionSlot hF hu

theorem mem_insertAt {F : List ℕ} {j u x : ℕ} (hj : j ≤ F.length) :
    x ∈ insertAt F j u ↔ x = u ∨ x ∈ F := by
  simpa [insertAt] using List.mem_insertIdx (a := x) (b := u) hj

theorem insertAt_toFinset {F : List ℕ} {j u : ℕ} (hj : j ≤ F.length) :
    (insertAt F j u).toFinset = insert u F.toFinset := by
  ext x
  simp only [List.mem_toFinset, mem_insert]
  exact mem_insertAt hj

theorem insertAt_eq_take_drop {F : List ℕ} {j u : ℕ} (hj : j ≤ F.length) :
    insertAt F j u = F.take j ++ u :: F.drop j := by
  induction F generalizing j with
  | nil =>
    cases j with
    | zero => simp [insertAt]
    | succ j =>
      rw [List.length_nil] at hj
      exact absurd hj (Nat.not_succ_le_zero j)
  | cons a F ih =>
    cases j with
    | zero => simp [insertAt]
    | succ j =>
      have hj' : j ≤ F.length := by
        simp only [List.length_cons] at hj
        omega
      have ih' := ih hj'
      rw [insertAt] at ih'
      rw [insertAt, List.insertIdx_succ_cons, List.take_succ_cons,
        List.drop_succ_cons, List.cons_append, ih']

/-- Converse of `deletion_preimage`: reinsertion in the open slot restores
a strictly increasing list. -/
theorem insertAt_pairwise_of_mem_slot {F : List ℕ} {j u : ℕ}
    (hF : F.Pairwise (· < ·))
    (hu : (deletionSlot F j).1 < u ∧ u < (deletionSlot F j).2) :
    (insertAt F j u).Pairwise (· < ·) := by
  have hj : j < F.length := lt_length_of_mem_deletionSlot hu.2
  have hjle : j ≤ F.length := Nat.le_of_lt hj
  have hright : (deletionSlot F j).2 = F[j] := deletionSlot_right_eq hj
  have huR : u < F[j] := by simpa [hright] using hu.2
  have hpw := List.pairwise_iff_getElem.mp hF
  rw [insertAt_eq_take_drop hjle, List.pairwise_append]
  refine ⟨List.Pairwise.take (l := F) (i := j) hF, ?_, ?_⟩
  · rw [List.pairwise_cons]
    refine ⟨?_, List.Pairwise.drop (l := F) (i := j) hF⟩
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_drop_iff_getElem.mp hx
    have hjt : j ≤ j + t := Nat.le_add_right j t
    rcases Nat.lt_or_eq_of_le hjt with hlt | heq
    · exact lt_trans huR (hpw j (j + t) hj (by omega) hlt)
    · have ht0 : t = 0 := by omega
      simpa [ht0] using huR
  · intro a ha b hb
    have hjpos : 0 < j := by
      cases j with
      | zero => simp at ha
      | succ _ => exact Nat.succ_pos _
    rcases List.mem_cons.mp hb with rfl | hbdrop
    · obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp ha
      have hkj : k < j := by
        have hmin : min j F.length = j := Nat.min_eq_left hjle
        omega
      have hleft : (deletionSlot F j).1 = F[j - 1] :=
        deletionSlot_left_eq_of_pos hjpos (by omega)
      have hk_le : k ≤ j - 1 := by omega
      rcases Nat.lt_or_eq_of_le hk_le with hlt | heq
      · exact lt_trans (hpw k (j - 1) (by omega) (by omega) hlt)
          (by simpa [hleft] using hu.1)
      · simpa [heq, hleft] using hu.1
    · obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp ha
      obtain ⟨t, ht, rfl⟩ := List.mem_drop_iff_getElem.mp hbdrop
      have hkj : k < j := by
        have hmin : min j F.length = j := Nat.min_eq_left hjle
        omega
      exact hpw k (j + t) (by omega) (by omega) (by omega)

/-! ### Constant Bernoulli weights (6.2) -/

theorem frameBernoulliWeight_pos {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (F : Finset ℕ) : 0 < frameBernoulliWeight A ρ F :=
  mul_pos (pow_pos hρ0 _) (pow_pos (sub_pos.mpr hρ1) _)

theorem frameBernoulliWeight_eq_length {A : Finset ℕ} {ρ : ℝ} {F : List ℕ}
    (hF : F.Pairwise (· < ·)) :
    frameBernoulliWeight A ρ F.toFinset =
      ρ ^ (F.length + 1) * (1 - ρ) ^ (A.card - F.length - 1) := by
  have hcard : F.toFinset.card = F.length :=
    List.toFinset_card_of_nodup (pairwise_nodup_lt hF)
  simp [frameBernoulliWeight, hcard]

/-- The Bernoulli mass of `insertAt F j u` is the paper frame weight
(6.2), independent of the slot point `u`. -/
theorem insertAt_bernoulliThin_eq {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {F : List ℕ} {j u : ℕ} (hF : F.Pairwise (· < ·))
    (hFA : F.toFinset ⊆ A) (hu : u ∈ openSlot A F j) :
    bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset =
      frameBernoulliWeight A ρ F.toFinset := by
  have huA : u ∈ A := (mem_openSlot.mp hu).1
  have hus : (deletionSlot F j).1 < u ∧ u < (deletionSlot F j).2 :=
    (mem_openSlot.mp hu).2
  have hj : j < F.length := lt_length_of_mem_deletionSlot hus.2
  have hjle : j ≤ F.length := Nat.le_of_lt hj
  have huF : u ∉ F.toFinset := not_mem_toFinset_of_mem_deletionSlot hF hus
  have hB : (insertAt F j u).toFinset ⊆ A := by
    rw [insertAt_toFinset hjle]
    exact insert_subset huA hFA
  have huin : u ∈ (insertAt F j u).toFinset := by
    rw [insertAt_toFinset hjle]
    exact mem_insert_self u _
  have herase : (insertAt F j u).toFinset.erase u = F.toFinset := by
    rw [insertAt_toFinset hjle, erase_insert huF]
  rw [frameBernoulliWeight]
  exact frame_bernoulli_weight_const hρ0 hρ1 hB huin herase

/-- Slot constancy: every reinsertion of the deleted rank has the same
Bernoulli mass. -/
theorem insertAt_bernoulliThin_eq_slot {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {F : List ℕ} {j u u' : ℕ} (hF : F.Pairwise (· < ·))
    (hFA : F.toFinset ⊆ A) (hu : u ∈ openSlot A F j)
    (hu' : u' ∈ openSlot A F j) :
    bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset =
      bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u').toFinset := by
  rw [insertAt_bernoulliThin_eq hρ0 hρ1 hF hFA hu,
    insertAt_bernoulliThin_eq hρ0 hρ1 hF hFA hu']

theorem openSlot_bernoulliThin_sum {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {F : List ℕ} {j : ℕ} (hF : F.Pairwise (· < ·))
    (hFA : F.toFinset ⊆ A) :
    ∑ u ∈ openSlot A F j,
        bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset =
      (openSlot A F j).card * frameBernoulliWeight A ρ F.toFinset := by
  have hterm : ∀ u ∈ openSlot A F j,
      bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset =
        frameBernoulliWeight A ρ F.toFinset :=
    fun u hu => insertAt_bernoulliThin_eq hρ0 hρ1 hF hFA hu
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]

/-- Conditional law of the deleted point given the remaining frame: the
Bernoulli masses are proportional to `1` on `A ∩ (left,right)`, hence
uniform after normalisation.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` (6.1)–(6.2);
`rounds/round104/13_gpt_paper_v0_3.tex` complete frames.
Contract: API
Audit: GREEN -/
theorem deleted_point_uniform_on_slot {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {F : List ℕ} {j u : ℕ} (hF : F.Pairwise (· < ·))
    (hFA : F.toFinset ⊆ A) (hu : u ∈ openSlot A F j) :
    bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset /
        ∑ v ∈ openSlot A F j,
          bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j v).toFinset =
      (1 : ℝ) / (openSlot A F j).card := by
  set s := openSlot A F j
  set w := frameBernoulliWeight A ρ F.toFinset
  have hwu : bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset = w :=
    insertAt_bernoulliThin_eq hρ0 hρ1 hF hFA hu
  have hsum :
      ∑ v ∈ s, bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j v).toFinset =
        (s.card : ℝ) * w :=
    openSlot_bernoulliThin_sum hρ0 hρ1 hF hFA
  have hw0 : w ≠ 0 := (frameBernoulliWeight_pos hρ0 hρ1 F.toFinset).ne'
  have hc : (s.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (card_pos.mpr ⟨u, hu⟩))
  rw [hwu, hsum]
  field_simp [hw0, hc]

/-! ### Phase split and model averages -/

/-- The truncated polynomial phase splits as frozen frame plus the two
summand free phase. Algebraic in `u`; the dummy `0` need not lie in the
slot.

Source: `GapPolynomialPhase.finiteGapPolyPhase_sub_insertAt`.
Contract: API
Audit: GREEN -/
theorem finiteGapPolyPhase_eq_add_free {b L j : ℕ} (hL : 2 ≤ L)
    (hj : j + 1 < L) (P : ℝ[X]) (F : List ℕ) (u : ℕ)
    (hlen : L - 1 ≤ F.length) :
    finiteGapPolyPhase P b L (insertAt F j u) =
      frozenGapPolyPhase P b L j F +
        freeGapPolyPhase P b j (deletionSlot F j).1 u (deletionSlot F j).2 := by
  unfold frozenGapPolyPhase
  have h :=
    finiteGapPolyPhase_sub_insertAt (B := b) hL hj P F u (0 : ℕ) hlen
  linarith [h]

/-- The frozen remainder does not depend on the comparison point. -/
theorem frozenGapPolyPhase_eq_sub {b L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L)
    (P : ℝ[X]) (F : List ℕ) (u : ℕ) (hlen : L - 1 ≤ F.length) :
    frozenGapPolyPhase P b L j F =
      finiteGapPolyPhase P b L (insertAt F j u) -
        freeGapPolyPhase P b j (deletionSlot F j).1 u (deletionSlot F j).2 := by
  have h := finiteGapPolyPhase_eq_add_free (b := b) hL hj P F u hlen
  linarith [h]

theorem e_finiteGapPolyPhase_eq_mul_e_free {b L j : ℕ} (hL : 2 ≤ L)
    (hj : j + 1 < L) (P : ℝ[X]) (F : List ℕ) (u : ℕ)
    (hlen : L - 1 ≤ F.length) :
    e (finiteGapPolyPhase P b L (insertAt F j u)) =
      e (frozenGapPolyPhase P b L j F) *
        e (freeGapPolyPhase P b j (deletionSlot F j).1 u
            (deletionSlot F j).2) := by
  rw [finiteGapPolyPhase_eq_add_free (b := b) hL hj P F u hlen, e_add]

theorem slot_e_polyPhase_sum {b L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L)
    (P : ℝ[X]) (F : List ℕ) (A : Finset ℕ) (hlen : L - 1 ≤ F.length) :
    ∑ u ∈ openSlot A F j, e (finiteGapPolyPhase P b L (insertAt F j u)) =
      e (frozenGapPolyPhase P b L j F) *
        ∑ u ∈ openSlot A F j,
          e (freeGapPolyPhase P b j (deletionSlot F j).1 u
              (deletionSlot F j).2) := by
  have hterm : ∀ u ∈ openSlot A F j,
      e (finiteGapPolyPhase P b L (insertAt F j u)) =
        e (frozenGapPolyPhase P b L j F) *
          e (freeGapPolyPhase P b j (deletionSlot F j).1 u
              (deletionSlot F j).2) :=
    fun u _ => e_finiteGapPolyPhase_eq_mul_e_free (b := b) hL hj P F u hlen
  rw [sum_congr rfl hterm, ← mul_sum]

/-- Constant Bernoulli weights pull out of any slot sum. -/
theorem openSlot_bernoulli_mul_sum {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {F : List ℕ} {j : ℕ} (hF : F.Pairwise (· < ·))
    (hFA : F.toFinset ⊆ A) (f : ℕ → ℂ) :
    ∑ u ∈ openSlot A F j,
        (bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset : ℂ) *
          f u =
      (frameBernoulliWeight A ρ F.toFinset : ℂ) *
        ∑ u ∈ openSlot A F j, f u := by
  have hterm : ∀ u ∈ openSlot A F j,
      (bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset : ℂ) * f u =
        (frameBernoulliWeight A ρ F.toFinset : ℂ) * f u := by
    intro u hu
    rw [insertAt_bernoulliThin_eq hρ0 hρ1 hF hFA hu]
  rw [sum_congr rfl hterm, ← mul_sum]

/-- Unnormalised model phase average: common frame weight times the
frozen character times the slot sum of `e(freeGapPolyPhase)`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:freephase) and
complete frames; (6.2).
Contract: API
Audit: GREEN -/
theorem model_phase_average_factor {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {b L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L) (P : ℝ[X])
    {F : List ℕ} (hF : F.Pairwise (· < ·)) (hFA : F.toFinset ⊆ A)
    (hlen : L - 1 ≤ F.length) :
    ∑ u ∈ openSlot A F j,
        (bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset : ℂ) *
          e (finiteGapPolyPhase P b L (insertAt F j u)) =
      (frameBernoulliWeight A ρ F.toFinset : ℂ) *
        e (frozenGapPolyPhase P b L j F) *
          ∑ u ∈ openSlot A F j,
            e (freeGapPolyPhase P b j (deletionSlot F j).1 u
                (deletionSlot F j).2) := by
  rw [openSlot_bernoulli_mul_sum hρ0 hρ1 hF hFA
      (fun u => e (finiteGapPolyPhase P b L (insertAt F j u))),
    slot_e_polyPhase_sum hL hj P F A hlen, mul_assoc]

theorem slotAverage_e_polyPhase {b L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L)
    (P : ℝ[X]) (F : List ℕ) (A : Finset ℕ) (hlen : L - 1 ≤ F.length) :
    slotAverage (openSlot A F j) (fun u =>
        e (finiteGapPolyPhase P b L (insertAt F j u))) =
      e (frozenGapPolyPhase P b L j F) *
        slotAverage (openSlot A F j) (fun u =>
          e (freeGapPolyPhase P b j (deletionSlot F j).1 u
              (deletionSlot F j).2)) := by
  unfold slotAverage
  rw [slot_e_polyPhase_sum hL hj P F A hlen, mul_div_assoc]

/-- Conditional model mean of `e(Φ_L)` given the frame equals the
uniform slot average of `e(freeGapPolyPhase)`, times the frozen
character. Uses uniformity of the deleted point.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` complete frames.
Contract: API
Audit: GREEN -/
theorem model_phase_condAvg_eq_slotAvg {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {b L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L) (P : ℝ[X])
    {F : List ℕ} (hF : F.Pairwise (· < ·)) (hFA : F.toFinset ⊆ A)
    (hlen : L - 1 ≤ F.length) (hne : (openSlot A F j).Nonempty) :
    (∑ u ∈ openSlot A F j,
          (bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset : ℂ) *
            e (finiteGapPolyPhase P b L (insertAt F j u))) /
        ∑ u ∈ openSlot A F j,
          (bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset : ℂ) =
      e (frozenGapPolyPhase P b L j F) *
        slotAverage (openSlot A F j) (fun u =>
          e (freeGapPolyPhase P b j (deletionSlot F j).1 u
              (deletionSlot F j).2)) := by
  set s := openSlot A F j
  set w := frameBernoulliWeight A ρ F.toFinset
  have hw0ℝ : w ≠ 0 := (frameBernoulliWeight_pos hρ0 hρ1 F.toFinset).ne'
  have hw0 : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw0ℝ
  have hc : (s.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (card_pos.mpr hne))
  have hsumw :
      ∑ u ∈ s,
          (bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset : ℂ) =
        (s.card : ℂ) * (w : ℂ) := by
    have hR := openSlot_bernoulliThin_sum (A := A) (ρ := ρ) hρ0 hρ1 (F := F)
      (j := j) hF hFA
    have hcast :
        ((∑ u ∈ s,
            bernoulliThin A ρ hρ0.le hρ1.le
              (insertAt F j u).toFinset : ℝ) : ℂ) =
          ∑ u ∈ s,
            (bernoulliThin A ρ hρ0.le hρ1.le
              (insertAt F j u).toFinset : ℂ) :=
      Complex.ofReal_sum s fun u =>
        bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset
    rw [← hcast, hR, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [model_phase_average_factor hρ0 hρ1 hL hj P hF hFA hlen, hsumw]
  unfold slotAverage
  change
      ((w : ℂ) * e (frozenGapPolyPhase P b L j F) *
          ∑ u ∈ s,
            e (freeGapPolyPhase P b j (deletionSlot F j).1 u
                (deletionSlot F j).2)) /
        ((s.card : ℂ) * (w : ℂ)) =
      e (frozenGapPolyPhase P b L j F) *
        ((∑ u ∈ s,
            e (freeGapPolyPhase P b j (deletionSlot F j).1 u
                (deletionSlot F j).2)) /
          (s.card : ℂ))
  have hden : (s.card : ℂ) * (w : ℂ) ≠ 0 := mul_ne_zero hc hw0
  rw [← mul_div_assoc, div_eq_div_iff hden hc]
  ring

/-! ### Linear gap-phase specialisation (`P = X`) -/

theorem finiteGapPhase_eq_add_free {b L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L)
    (F : List ℕ) (u : ℕ) (hlen : L - 1 ≤ F.length) :
    finiteGapPhase b L (insertAt F j u) =
      frozenGapPolyPhase X b L j F +
        freeGapPolyPhase X b j (deletionSlot F j).1 u (deletionSlot F j).2 := by
  simpa [finiteGapPolyPhase_X] using
    finiteGapPolyPhase_eq_add_free (P := X) hL hj F u hlen

theorem model_gapPhase_average_factor {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {b L j : ℕ} (hL : 2 ≤ L) (hj : j + 1 < L) {F : List ℕ}
    (hF : F.Pairwise (· < ·)) (hFA : F.toFinset ⊆ A)
    (hlen : L - 1 ≤ F.length) :
    ∑ u ∈ openSlot A F j,
        (bernoulliThin A ρ hρ0.le hρ1.le (insertAt F j u).toFinset : ℂ) *
          e (finiteGapPhase b L (insertAt F j u)) =
      (frameBernoulliWeight A ρ F.toFinset : ℂ) *
        e (frozenGapPolyPhase X b L j F) *
          ∑ u ∈ openSlot A F j,
            e (freeGapPolyPhase X b j (deletionSlot F j).1 u
                (deletionSlot F j).2) := by
  simpa [finiteGapPolyPhase_X] using
    model_phase_average_factor (P := X) hρ0 hρ1 hL hj hF hFA hlen

end PrimeGapNormality.Prime
