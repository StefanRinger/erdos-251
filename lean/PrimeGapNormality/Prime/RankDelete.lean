import PrimeGapNormality.Prime.Coupling
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact rank deletion in the Bernoulli model

Finite identities only: open deletion slot, constant Bernoulli frame
weights, linear dependence of the truncated gap phase on the deleted
rank, and finite Abel with the terminal correction. No Weyl assembly,
no public normality end theorem.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` §6 (6.1)–(6.3)
and finite Abel in §13; certificate
`rounds/round97/02_gpt_khl_normality_extension_certificate.py`;
`lean/PRIME_NORMALITY.md` RankDelete.
Contract: API
Audit: GREEN

Lean ranks are 0-based. Paper rank `j` with `1 ≤ j < L` is Lean `j`
with `j + 1 < L`. Root `0` is the phase origin only, not an element of
`A`. Frames are strictly increasing lists; `Finset.sort` uses `· ≤ ·`.
-/

namespace PrimeGapNormality.Prime

open Finset
open Classical

set_option maxHeartbeats 800000

/-! ### Slot, insertion, and phase points -/

/-- Open slot in which the deleted rank-`j` point must lie.
Left is the root `0` when `j = 0`, otherwise the previous surviving
point; right is the next surviving point.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` (6.1);
`lean/PRIME_NORMALITY.md` RankDelete.
Contract: API
Audit: GREEN -/
def deletionSlot (F : List ℕ) (j : ℕ) : ℕ × ℕ :=
  (if j = 0 then 0 else F.getD (j - 1) 0, F.getD j 0)

/-- Insert the deleted rank-`j` value into the surviving frame.

Source: `lean/PRIME_NORMALITY.md` RankDelete (`insertAt`).
Contract: API
Audit: GREEN -/
def insertAt (F : List ℕ) (j u : ℕ) : List ℕ :=
  F.insertIdx j u

/-- Phase sample: `x₀ = 0`, then the entries of `xs`.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` §6.
Contract: API
Audit: GREEN -/
def phasePoint (xs : List ℕ) (k : ℕ) : ℕ :=
  if k = 0 then 0 else xs.getD (k - 1) 0

/-- Finite gap phase `H_L(x) = ∑_{k=1}^{L} (x_k - x_{k-1}) / b^k`
with `x₀ = 0` and `x₁,…,x_L` the first `L` entries of `xs`.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` (6.3);
`lean/PRIME_NORMALITY.md` RankDelete.
Contract: API
Audit: GREEN -/
noncomputable def finiteGapPhase (b L : ℕ) (xs : List ℕ) : ℝ :=
  ∑ k ∈ range L,
    ((phasePoint xs (k + 1) : ℝ) - (phasePoint xs k : ℝ)) / (b : ℝ) ^ (k + 1)

/-- Integer numerator `∑_{k=1}^{L} (x_k - x_{k-1}) b^{L-k}` from the
certificate.

Source: `rounds/round97/02_gpt_khl_normality_extension_certificate.py`
`interior_phase_coefficient`.
Contract: API
Audit: GREEN -/
def finiteGapPhaseNumerator (b L : ℕ) (xs : List ℕ) : ℤ :=
  ∑ k ∈ range L,
    ((phasePoint xs (k + 1) : ℤ) - (phasePoint xs k : ℤ)) *
      (b : ℤ) ^ (L - (k + 1))

/-! ### Slot arithmetic -/

private theorem getD_eq_get {l : List ℕ} {n : ℕ} (hn : n < l.length) :
    l.getD n 0 = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]

theorem deletionSlot_left_zero (F : List ℕ) : (deletionSlot F 0).1 = 0 := by
  rfl

theorem deletionSlot_right_eq {F : List ℕ} {j : ℕ} (hj : j < F.length) :
    (deletionSlot F j).2 = F[j] :=
  getD_eq_get hj

theorem deletionSlot_left_eq_of_pos {F : List ℕ} {j : ℕ} (hj : 0 < j)
    (hjF : j - 1 < F.length) :
    (deletionSlot F j).1 = F[j - 1] := by
  unfold deletionSlot
  simp [Nat.ne_of_gt hj]
  exact getD_eq_get hjF

theorem j_lt_frame_length {L j : ℕ} {F : List ℕ}
    (hj : j + 1 < L) (hlen : L - 1 ≤ F.length) : j < F.length := by
  omega

private theorem pairwise_getElem_lt {F : List ℕ} (hF : F.Pairwise (· < ·)) {i k : ℕ}
    (hi : i < F.length) (hk : k < F.length) (hik : i < k) : F[i] < F[k] :=
  (List.pairwise_iff_getElem.mp hF) i k hi hk hik

private theorem base_cast_ne_zero {b : ℕ} (hb : 2 ≤ b) : (b : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

/-! ### Insertion getElem and one-sided preimage -/

theorem insertAt_length {F : List ℕ} {j u : ℕ} (hj : j ≤ F.length) :
    (insertAt F j u).length = F.length + 1 :=
  List.length_insertIdx_of_le_length hj u

/-- If the restored list is strictly increasing, then `u` lies in the
open deletion slot. Paper (6.1), one direction.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` (6.1).
Contract: API
Audit: GREEN -/
theorem deletion_preimage {F : List ℕ} {j u : ℕ} (hj : j < F.length)
    (hP : (insertAt F j u).Pairwise (· < ·))
    (h0 : 0 < u ∨ 0 < j) :
    (deletionSlot F j).1 < u ∧ u < (deletionSlot F j).2 := by
  have hlen : (insertAt F j u).length = F.length + 1 :=
    insertAt_length (Nat.le_of_lt hj)
  have hi : j < (insertAt F j u).length := by
    rw [hlen]
    exact Nat.lt_succ_of_lt hj
  have hi1 : j + 1 < (insertAt F j u).length := by
    rw [hlen]
    exact Nat.succ_lt_succ hj
  have hself : (insertAt F j u)[j] = u := by
    have hsome : (insertAt F j u)[j]? = some u := by
      simp [insertAt, List.getElem?_insertIdx_self, Nat.le_of_lt hj]
    have ⟨_, heq⟩ := List.getElem?_eq_some_iff.mp hsome
    exact heq
  have hnext : (insertAt F j u)[j + 1] = F[j] := by
    have hsome : (insertAt F j u)[j + 1]? = some F[j] := by
        simp [insertAt, List.getElem?_insertIdx_of_gt (Nat.lt_succ_self j),
          List.getElem?_eq_getElem hj]
    have ⟨_, heq⟩ := List.getElem?_eq_some_iff.mp hsome
    exact heq
  have hlt : (insertAt F j u)[j] < (insertAt F j u)[j + 1] :=
    pairwise_getElem_lt hP hi hi1 (Nat.lt_succ_self j)
  have hright : u < (deletionSlot F j).2 := by
    simpa [hself, hnext, deletionSlot_right_eq hj] using hlt
  refine ⟨?_, hright⟩
  by_cases hj0 : j = 0
  · simp [deletionSlot, hj0]
    cases h0 with
    | inl hu => exact hu
    | inr hjpos => cases hj0; omega
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hiL : j - 1 < (insertAt F j u).length := by
      rw [hlen]
      exact Nat.lt_trans (Nat.sub_lt hjpos Nat.zero_lt_one) (Nat.lt_succ_of_lt hj)
    have hprev : (insertAt F j u)[j - 1] = F[j - 1] := by
      have hjF : j - 1 < F.length := Nat.lt_of_le_of_lt (Nat.sub_le j 1) hj
      have hsome : (insertAt F j u)[j - 1]? = some F[j - 1] := by
        simp [insertAt, List.getElem?_insertIdx_of_lt (Nat.sub_lt hjpos Nat.zero_lt_one),
          List.getElem?_eq_getElem hjF]
      have ⟨_, heq⟩ := List.getElem?_eq_some_iff.mp hsome
      exact heq
    have hltL : (insertAt F j u)[j - 1] < (insertAt F j u)[j] :=
      pairwise_getElem_lt hP hiL hi (Nat.sub_lt hjpos Nat.zero_lt_one)
    have hleft : (deletionSlot F j).1 = F[j - 1] :=
      deletionSlot_left_eq_of_pos hjpos
        (Nat.lt_of_le_of_lt (Nat.sub_le j 1) hj)
    simpa [hprev, hself, hleft] using hltL

/-! ### Phase points of insertion -/

theorem phasePoint_insertAt_of_le {F : List ℕ} {j u k : ℕ} (hk : k ≤ j) :
    phasePoint (insertAt F j u) k = phasePoint F k := by
  by_cases h0 : k = 0
  · simp [phasePoint, h0]
  · have hkj : k - 1 < j := by omega
    simp [phasePoint, insertAt, h0, List.getD_eq_getElem?_getD,
      List.getElem?_insertIdx_of_lt hkj]

theorem phasePoint_insertAt_succ {F : List ℕ} {j u : ℕ} (hj : j ≤ F.length) :
    phasePoint (insertAt F j u) (j + 1) = u := by
  simp [phasePoint, insertAt, List.getD_eq_getElem?_getD,
    List.getElem?_insertIdx_self, hj]

theorem phasePoint_insertAt_of_gt {F : List ℕ} {j u k : ℕ} (hk : j + 1 < k) :
    phasePoint (insertAt F j u) k = F.getD (k - 2) 0 := by
  have hk0 : k ≠ 0 := by omega
  have hgt : j < k - 1 := by omega
  simp [phasePoint, insertAt, hk0, List.getD_eq_getElem?_getD,
    List.getElem?_insertIdx_of_gt hgt, Nat.sub_sub]

theorem phasePoint_insertAt_left {F : List ℕ} {j u : ℕ} :
    phasePoint (insertAt F j u) j = (deletionSlot F j).1 := by
  by_cases h0 : j = 0
  · simp [phasePoint, deletionSlot, h0]
  · rw [phasePoint_insertAt_of_le (k := j) (j := j) (u := u) le_rfl]
    simp [phasePoint, deletionSlot, h0]

theorem phasePoint_insertAt_right {F : List ℕ} {j u : ℕ} :
    phasePoint (insertAt F j u) (j + 2) = (deletionSlot F j).2 := by
  have hk : j + 1 < j + 2 := by omega
  simp [phasePoint_insertAt_of_gt (F := F) (j := j) (u := u) hk, deletionSlot]

/-! ### Constant Bernoulli weights (6.2) -/

theorem frame_bernoulli_weight_const {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {F B : Finset ℕ} {u : ℕ} (hB : B ⊆ A) (hu : u ∈ B)
    (hF : B.erase u = F) :
    bernoulliThin A ρ hρ0.le hρ1.le B =
      ρ ^ (F.card + 1) * (1 - ρ) ^ (A.card - F.card - 1) := by
  have hcardB : F.card + 1 = B.card := by
    have hpos : 1 ≤ B.card := Nat.succ_le_of_lt (card_pos.mpr ⟨u, hu⟩)
    have herase : F.card = B.card - 1 := by
      rw [← hF, card_erase_of_mem hu]
    omega
  have hcardA : A.card - F.card - 1 = A.card - B.card := by
    rw [Nat.sub_sub, hcardB]
  rw [bernoulliThin_eq A hρ0.le hρ1.le hB, hcardB, hcardA]

theorem frame_bernoulli_weight_eq {A : Finset ℕ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {F B B' : Finset ℕ} {u u' : ℕ}
    (hB : B ⊆ A) (hB' : B' ⊆ A) (hu : u ∈ B) (hu' : u' ∈ B')
    (hF : B.erase u = F) (hF' : B'.erase u' = F) :
    bernoulliThin A ρ hρ0.le hρ1.le B =
      bernoulliThin A ρ hρ0.le hρ1.le B' := by
  rw [frame_bernoulli_weight_const hρ0 hρ1 hB hu hF,
    frame_bernoulli_weight_const hρ0 hρ1 hB' hu' hF']

/-! ### Linear phase coefficient (6.3) -/

theorem gap_summand_diff_insertAt {b L j : ℕ} (hL : 2 ≤ L)
    (hj : j + 1 < L) (F : List ℕ) (u u' : ℕ) (hlen : L - 1 ≤ F.length)
    {k : ℕ} (hk : k ∈ range L) :
    (((phasePoint (insertAt F j u) (k + 1) : ℝ) - phasePoint (insertAt F j u) k) -
        ((phasePoint (insertAt F j u') (k + 1) : ℝ) - phasePoint (insertAt F j u') k)) /
        (b : ℝ) ^ (k + 1) =
      if k = j then ((u : ℝ) - u') / (b : ℝ) ^ (j + 1)
      else if k = j + 1 then ((u' : ℝ) - u) / (b : ℝ) ^ (j + 2)
      else 0 := by
  have hjF : j < F.length := j_lt_frame_length hj hlen
  have hjle : j ≤ F.length := Nat.le_of_lt hjF
  have := hL
  have := mem_range.mp hk
  by_cases hkj : k = j
  · subst hkj
    simp [phasePoint_insertAt_succ hjle, phasePoint_insertAt_left]
  · by_cases hkj1 : k = j + 1
    · subst hkj1
      simp [phasePoint_insertAt_succ hjle, phasePoint_insertAt_right]
    · have hne : k ≠ j := hkj
      have hne1 : k ≠ j + 1 := hkj1
      have hdiff :
          (phasePoint (insertAt F j u) (k + 1) : ℝ) - phasePoint (insertAt F j u) k =
            (phasePoint (insertAt F j u') (k + 1) : ℝ) - phasePoint (insertAt F j u') k := by
        by_cases hlt : k < j
        · have hk1 : k + 1 ≤ j := by omega
          have hk0 : k ≤ j := by omega
          simp [phasePoint_insertAt_of_le hk1, phasePoint_insertAt_of_le hk0]
        · have hgt : j + 1 < k := by omega
          have hgt1 : j + 1 < k + 1 := by omega
          simp [phasePoint_insertAt_of_gt hgt1, phasePoint_insertAt_of_gt hgt]
      simp [hne, hne1, hdiff]

/-- Moving the deleted rank changes `H_L` by
`(b-1)(u-u')/b^{j+2}`. Paper (6.3) uses 1-based rank `j_paper = j+1`,
so the coefficient `b^{-j_paper-1}` is Lean `b^{-(j+2)}`. Certificate:
integer coefficient `(b-1) b^{L-rank-1}` with 1-based `rank`.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` (6.3);
certificate `interior_phase_coefficient`.
Contract: API
Audit: GREEN -/
theorem phase_linear_in_deleted {b L j : ℕ} (hb : 2 ≤ b) (hL : 2 ≤ L)
    (hj : j + 1 < L) (F : List ℕ) (u u' : ℕ) (hlen : L - 1 ≤ F.length) :
    finiteGapPhase b L (insertAt F j u) - finiteGapPhase b L (insertAt F j u') =
      ((b : ℝ) - 1) * ((u : ℝ) - u') / (b : ℝ) ^ (j + 2) := by
  have hb0 := base_cast_ne_zero hb
  unfold finiteGapPhase
  rw [← sum_sub_distrib]
  simp_rw [← sub_div]
  have hterm :
      ∑ k ∈ range L,
          (((phasePoint (insertAt F j u) (k + 1) : ℝ) - phasePoint (insertAt F j u) k) -
              ((phasePoint (insertAt F j u') (k + 1) : ℝ) - phasePoint (insertAt F j u') k)) /
              (b : ℝ) ^ (k + 1) =
        ∑ k ∈ range L,
          (if k = j then ((u : ℝ) - u') / (b : ℝ) ^ (j + 1)
          else if k = j + 1 then ((u' : ℝ) - u) / (b : ℝ) ^ (j + 2)
          else 0) :=
    sum_congr rfl fun k hk => gap_summand_diff_insertAt hL hj F u u' hlen hk
  rw [hterm]
  have hjL : j < L := Nat.lt_of_succ_lt hj
  have hj1L : j + 1 < L := hj
  have hsub : ({j, j + 1} : Finset ℕ) ⊆ range L := by
    intro x hx
    simp only [mem_insert, mem_singleton, mem_range] at hx ⊢
    rcases hx with rfl | rfl
    · exact hjL
    · exact hj1L
  have hne : j ≠ j + 1 := Nat.ne_of_lt (Nat.lt_succ_self j)
  have hzero :
      ∀ k ∈ range L \ {j, j + 1},
        (if k = j then ((u : ℝ) - u') / (b : ℝ) ^ (j + 1)
        else if k = j + 1 then ((u' : ℝ) - u) / (b : ℝ) ^ (j + 2)
        else 0) = 0 := by
    intro k hk
    simp only [mem_sdiff, mem_insert, mem_singleton] at hk
    have hkj : k ≠ j := fun h => hk.2 (Or.inl h)
    have hkj1 : k ≠ j + 1 := fun h => hk.2 (Or.inr h)
    simp [hkj, hkj1]
  have hpair :
      ∑ k ∈ ({j, j + 1} : Finset ℕ),
          (if k = j then ((u : ℝ) - u') / (b : ℝ) ^ (j + 1)
          else if k = j + 1 then ((u' : ℝ) - u) / (b : ℝ) ^ (j + 2)
          else 0) =
        ((u : ℝ) - u') / (b : ℝ) ^ (j + 1) + ((u' : ℝ) - u) / (b : ℝ) ^ (j + 2) := by
    rw [sum_pair hne]
    simp
  have hsplit := sum_sdiff (s₁ := ({j, j + 1} : Finset ℕ)) (s₂ := range L)
    (f := fun k =>
      if k = j then ((u : ℝ) - u') / (b : ℝ) ^ (j + 1)
      else if k = j + 1 then ((u' : ℝ) - u) / (b : ℝ) ^ (j + 2)
      else 0)
    hsub
  rw [← hsplit, sum_eq_zero hzero, zero_add, hpair]
  have hpow : (b : ℝ) ^ (j + 2) = (b : ℝ) ^ (j + 1) * b := by
    rw [pow_succ]
  field_simp [hb0, hpow]
  ring

/-! ### Finite Abel with terminal correction (§13) -/

/-- Finite Abel identity, terminal remainder retained. Indices are
0-based: Lean `a 0` is the first sample.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` §13;
certificate `finite_abel_with_terminal_correction`;
`lean/PRIME_NORMALITY.md` RankDelete.
Contract: API
Audit: GREEN -/
theorem finite_abel_terminal {b : ℕ} (hb : 2 ≤ b) (a : ℕ → ℕ) (n : ℕ)
    (hn : 1 ≤ n) :
    ((b : ℝ) - 1) * ∑ i ∈ range n, (a i : ℝ) / (b : ℝ) ^ (i + 1) =
      (a 0 : ℝ) +
        ∑ i ∈ range (n - 1), ((a (i + 1) : ℝ) - a i) / (b : ℝ) ^ (i + 1) -
          (a (n - 1) : ℝ) / (b : ℝ) ^ n := by
  have hb0 := base_cast_ne_zero hb
  have hterm (i : ℕ) :
      ((b : ℝ) - 1) * ((a i : ℝ) / (b : ℝ) ^ (i + 1)) =
        (a i : ℝ) / (b : ℝ) ^ i - (a i : ℝ) / (b : ℝ) ^ (i + 1) := by
    have hpow : (b : ℝ) ^ (i + 1) = (b : ℝ) ^ i * b := pow_succ (b : ℝ) i
    have hbpow : (b : ℝ) ^ i ≠ 0 := pow_ne_zero i hb0
    field_simp [hb0, hbpow, hpow]
    ring
  have hsplit :
      ((b : ℝ) - 1) * ∑ i ∈ range n, (a i : ℝ) / (b : ℝ) ^ (i + 1) =
        ∑ i ∈ range n, (a i : ℝ) / (b : ℝ) ^ i -
          ∑ i ∈ range n, (a i : ℝ) / (b : ℝ) ^ (i + 1) := by
    rw [mul_sum (range n) (fun i => (a i : ℝ) / (b : ℝ) ^ (i + 1)) ((b : ℝ) - 1)]
    simp_rw [hterm]
    rw [sum_sub_distrib]
  have hnrew : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
  have hhead :
      ∑ i ∈ range n, (a i : ℝ) / (b : ℝ) ^ i =
        (a 0 : ℝ) + ∑ i ∈ range (n - 1), (a (i + 1) : ℝ) / (b : ℝ) ^ (i + 1) := by
    conv_lhs => rw [hnrew]
    rw [sum_range_succ' (fun i => (a i : ℝ) / (b : ℝ) ^ i) (n - 1)]
    simp [pow_zero, add_comm]
  have htail :
      ∑ i ∈ range n, (a i : ℝ) / (b : ℝ) ^ (i + 1) =
        ∑ i ∈ range (n - 1), (a i : ℝ) / (b : ℝ) ^ (i + 1) +
          (a (n - 1) : ℝ) / (b : ℝ) ^ n := by
    conv_lhs => rw [hnrew]
    rw [sum_range_succ (fun i => (a i : ℝ) / (b : ℝ) ^ (i + 1)) (n - 1)]
    rw [Nat.sub_add_cancel hn]
  have hcomb :
      ∑ i ∈ range (n - 1), (a (i + 1) : ℝ) / (b : ℝ) ^ (i + 1) -
          ∑ i ∈ range (n - 1), (a i : ℝ) / (b : ℝ) ^ (i + 1) =
        ∑ i ∈ range (n - 1), ((a (i + 1) : ℝ) - a i) / (b : ℝ) ^ (i + 1) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => (sub_div _ _ _).symm
  rw [hsplit, hhead, htail]
  have hrearr :
      (a 0 : ℝ) + ∑ i ∈ range (n - 1), (a (i + 1) : ℝ) / (b : ℝ) ^ (i + 1) -
          (∑ i ∈ range (n - 1), (a i : ℝ) / (b : ℝ) ^ (i + 1) +
            (a (n - 1) : ℝ) / (b : ℝ) ^ n) =
        (a 0 : ℝ) +
          (∑ i ∈ range (n - 1), (a (i + 1) : ℝ) / (b : ℝ) ^ (i + 1) -
            ∑ i ∈ range (n - 1), (a i : ℝ) / (b : ℝ) ^ (i + 1)) -
          (a (n - 1) : ℝ) / (b : ℝ) ^ n := by
    ring
  rw [hrearr, hcomb]

end PrimeGapNormality.Prime
