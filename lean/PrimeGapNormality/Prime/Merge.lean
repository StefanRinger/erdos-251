import PrimeGapNormality.Prime.Coupling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact central Bernoulli merge, all outer voids

Root `0` is fixed and is not a candidate. A short frame
`F = (x_1 < ⋯ < x_{2K})` has `n_F = |A ∩ [1, x_{2K}]|` including every
outer void before the endpoint. Points after the endpoint are integrated
out (factor `1`). The open merge slot is `W_F = (x_{K-1}, x_K)` with
`1 ≤ K`. The identity does not require the whole window to have only
`2K` survivors.

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (22)–(23);
`rounds/round97/01_gpt_khl_merger_independent_audit.md` (A26)–(A27);
certificate `rounds/round96/01_gpt_standard_hl_gap_merger_certificate.py`
`bernoulli_shapes`; `lean/PRIME_SIGNATURES.md` Merge.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 400000

/-! ### Frame endpoint, prefix count, open slot -/

/-- Endpoint `x_{2K}` of a short frame. Empty default `0`. -/
def frameEndpoint (F : List ℕ) : ℕ :=
  F.getD (F.length - 1) 0

/-- Candidates in `[1, x_{2K}]`. Outer voids stay in this count. -/
def framePrefix (A : Finset ℕ) (F : List ℕ) : Finset ℕ :=
  A.filter (fun n => 0 < n ∧ n ≤ frameEndpoint F)

/-- `n_F = |A ∩ [1, x_{2K}]|`. -/
def framePrefixCount (A : Finset ℕ) (F : List ℕ) : ℕ :=
  (framePrefix A F).card

/-- Candidates strictly after the endpoint. Integrated out of the mass. -/
def frameSuffix (A : Finset ℕ) (F : List ℕ) : Finset ℕ :=
  A.filter (fun n => frameEndpoint F < n)

/-- Open central merge slot `W_F = (x_{K-1}, x_K)`.

Root `x_0 = 0` is fixed. Lean index `K-1` is paper rank `K`.
Requires `1 ≤ K`. -/
def mergeSlot {K : ℕ} (_hK : 1 ≤ K) (F : List ℕ) : ℕ × ℕ :=
  (if 1 < K then F.getD (K - 2) 0 else 0, F.getD (K - 1) 0)

/-- `W_F` with `K` recovered as `F.length / 2`. -/
def mergeSlotOf (F : List ℕ) : ℕ × ℕ :=
  let K := F.length / 2
  (if 1 < K then F.getD (K - 2) 0 else 0, F.getD (K - 1) 0)

/-- Supported short frame: length `2K`, strictly increasing, contained
in `A`, strictly after the root. Consecutive first-`2K` survival is
encoded by the void factor `(1-ρ)^{n_F-2K}`, not by a global
`|A| = 2K` restriction. -/
def IsSupportedShortFrame (A : Finset ℕ) (K : ℕ) (F : List ℕ) : Prop :=
  F.length = 2 * K ∧ F.Pairwise (· < ·) ∧ F.toFinset ⊆ A ∧ ∀ x ∈ F, 0 < x

instance instDecidableIsSupportedShortFrame (A : Finset ℕ) (K : ℕ)
    (F : List ℕ) : Decidable (IsSupportedShortFrame A K F) := by
  dsimp [IsSupportedShortFrame]
  infer_instance

/-! ### Shape masses (R96 (22)–(23), R97 (A26)–(A27)) -/

/-- Short consecutive-shape mass `ρ^{2K}(1-ρ)^{n_F-2K}` on a supported
frame, else `0`. Suffix points after the endpoint are omitted (factor
`1`). -/
noncomputable def shortShapeMass (A : Finset ℕ) (ρ : ℝ) (F : List ℕ) : ℝ :=
  if IsSupportedShortFrame A (F.length / 2) F ∧ 1 ≤ F.length / 2 then
    ρ ^ F.length * (1 - ρ) ^ (framePrefixCount A F - F.length)
  else
    0

/-- Long-shape mass of `F ∪ {u}`: one extra survivor in `W_F`, same
endpoint, so exponent `n_F-(2K+1)`. -/
noncomputable def longShapeMass (A : Finset ℕ) (ρ : ℝ) (F : List ℕ)
    (u : ℕ) : ℝ :=
  if IsSupportedShortFrame A (F.length / 2) F ∧ 1 ≤ F.length / 2 ∧
      (mergeSlotOf F).1 < u ∧ u < (mergeSlotOf F).2 ∧ u ∈ A then
    ρ ^ (F.length + 1) * (1 - ρ) ^ (framePrefixCount A F - F.length - 1)
  else
    0

/-- Sum of long-shape masses over `u ∈ A ∩ W_F`. -/
noncomputable def longMergedMass (A : Finset ℕ) (ρ : ℝ) (F : List ℕ) : ℝ :=
  ∑ u ∈ A.filter (fun u =>
      (mergeSlotOf F).1 < u ∧ u < (mergeSlotOf F).2),
    longShapeMass A ρ F u

/-! ### Slot and frame arithmetic -/

theorem pairwise_getElem_lt {F : List ℕ} (hF : F.Pairwise (· < ·)) {i k : ℕ}
    (hi : i < F.length) (hk : k < F.length) (hik : i < k) : F[i] < F[k] :=
  (List.pairwise_iff_getElem.mp hF) i k hi hk hik

theorem pairwise_nodup_lt {F : List ℕ} (hF : F.Pairwise (· < ·)) : F.Nodup :=
  hF.imp (fun h => ne_of_lt h)

theorem getD_eq_getElem_nat {F : List ℕ} {i : ℕ} (hi : i < F.length) :
    F.getD i 0 = F[i] := by
  rw [List.getD_eq_getElem?_getD, getElem?_pos F i hi]
  rfl

theorem two_mul_div_two (K : ℕ) : 2 * K / 2 = K := by
  rw [Nat.mul_comm]
  exact Nat.mul_div_left K (Nat.succ_pos 1)

theorem frameEndpoint_eq_getElem {F : List ℕ} (hpos : 0 < F.length) :
    frameEndpoint F = F[F.length - 1]'(Nat.sub_one_lt_of_lt hpos) :=
  getD_eq_getElem_nat (Nat.sub_one_lt_of_lt hpos)

theorem le_frameEndpoint_of_mem {F : List ℕ} (hF : F.Pairwise (· < ·))
    {x : ℕ} (hx : x ∈ F) : x ≤ frameEndpoint F := by
  have hpos : 0 < F.length := List.length_pos_of_mem hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hlast : frameEndpoint F = F[F.length - 1]'(by omega) :=
    frameEndpoint_eq_getElem hpos
  have hile : i ≤ F.length - 1 := by omega
  rw [hlast]
  rcases Nat.lt_or_eq_of_le hile with hlt | heq
  · exact Nat.le_of_lt (pairwise_getElem_lt hF hi (by omega) hlt)
  · simp [heq]

theorem mergeSlotOf_eq {K : ℕ} (hK : 1 ≤ K) {F : List ℕ}
    (hlen : F.length = 2 * K) : mergeSlotOf F = mergeSlot hK F := by
  have hdiv : F.length / 2 = K := by rw [hlen, two_mul_div_two]
  simp [mergeSlotOf, mergeSlot, hdiv]

theorem mergeSlot_right_eq {K : ℕ} (hK : 1 ≤ K) {F : List ℕ}
    (hlen : F.length = 2 * K) :
    (mergeSlot hK F).2 = F[K - 1]'(by omega) := by
  unfold mergeSlot
  exact getD_eq_getElem_nat (show K - 1 < F.length by omega)

theorem mergeSlot_left_eq_pos {K : ℕ} (hK : 1 ≤ K) (hK2 : 1 < K)
    {F : List ℕ} (hlen : F.length = 2 * K) :
    (mergeSlot hK F).1 = F[K - 2]'(by omega) := by
  unfold mergeSlot
  simp [hK2]
  exact getD_eq_getElem_nat (show K - 2 < F.length by omega)

theorem mergeSlot_left_eq_one {F : List ℕ} :
    (mergeSlot (Nat.le_refl 1) F).1 = 0 := by
  simp [mergeSlot]

/-- A point in the open slot is not a frame site. -/
theorem not_mem_of_mem_mergeSlot {K : ℕ} (hK : 1 ≤ K) {F : List ℕ}
    (hlen : F.length = 2 * K) (hF : F.Pairwise (· < ·)) {u : ℕ}
    (hu : (mergeSlot hK F).1 < u ∧ u < (mergeSlot hK F).2) :
    u ∉ F := by
  intro hmem
  obtain ⟨i, hi, huF⟩ := List.mem_iff_getElem.mp hmem
  have hright : (mergeSlot hK F).2 = F[K - 1]'(by omega) :=
    mergeSlot_right_eq hK hlen
  by_cases hij : i < K - 1
  · have hK2 : 1 < K := by omega
    have hleft : (mergeSlot hK F).1 = F[K - 2]'(by omega) :=
      mergeSlot_left_eq_pos hK hK2 hlen
    have hi_le : i ≤ K - 2 := by omega
    rcases Nat.lt_or_eq_of_le hi_le with hlt | heq
    · have hlt' : F[i] < F[K - 2]'(by omega) :=
        pairwise_getElem_lt hF hi (by omega) hlt
      have : F[K - 2]'(by omega) < F[i] := by
        simpa [hleft, huF] using hu.1
      exact lt_irrefl _ (lt_trans hlt' this)
    · have : F[i] < u := by simpa [heq, hleft] using hu.1
      rw [huF] at this
      exact lt_irrefl _ this
  · have hji : K - 1 ≤ i := by omega
    rcases Nat.lt_or_eq_of_le hji with hlt | heq
    · have hlt' : F[K - 1]'(by omega) < F[i] :=
        pairwise_getElem_lt hF (by omega) hi hlt
      have : F[i] < F[K - 1]'(by omega) := by
        simpa [hright, huF] using hu.2
      exact lt_irrefl _ (lt_trans this hlt')
    · have : u < F[i] := by simpa [heq, hright] using hu.2
      rw [← huF] at this
      exact lt_irrefl _ this

theorem framePrefixCount_ge {K : ℕ} {A : Finset ℕ} {F : List ℕ}
    (hK : 1 ≤ K) (hF : IsSupportedShortFrame A K F) :
    2 * K ≤ framePrefixCount A F := by
  obtain ⟨hlen, hpair, hsub, hpos⟩ := hF
  have := hK
  have hnodup : F.Nodup := pairwise_nodup_lt hpair
  have hcard : F.toFinset.card = F.length := List.toFinset_card_of_nodup hnodup
  have hsubset : F.toFinset ⊆ framePrefix A F := by
    intro x hx
    have hxF : x ∈ F := List.mem_toFinset.mp hx
    exact mem_filter.mpr ⟨hsub hx, hpos x hxF, le_frameEndpoint_of_mem hpair hxF⟩
  have hle := card_le_card hsubset
  simpa [framePrefixCount, hcard, hlen] using hle

theorem framePrefixCount_ge_succ {K : ℕ} {A : Finset ℕ} {F : List ℕ}
    (hK : 1 ≤ K) (hF : IsSupportedShortFrame A K F) {u : ℕ} (huA : u ∈ A)
    (hu : (mergeSlot hK F).1 < u ∧ u < (mergeSlot hK F).2) :
    2 * K + 1 ≤ framePrefixCount A F := by
  obtain ⟨hlen, hpair, hsub, hpos⟩ := hF
  have huF : u ∉ F := not_mem_of_mem_mergeSlot hK hlen hpair hu
  have huFt : u ∉ F.toFinset := by simpa [List.mem_toFinset] using huF
  have hupos : 0 < u := Nat.zero_lt_of_lt hu.1
  have hright : (mergeSlot hK F).2 = F[K - 1]'(by omega) :=
    mergeSlot_right_eq hK hlen
  have hule : u ≤ frameEndpoint F := by
    have hposF : 0 < F.length := by omega
    have hend : frameEndpoint F = F[F.length - 1]'(by omega) :=
      frameEndpoint_eq_getElem hposF
    have hrt_lt_end : F[K - 1]'(by omega) < F[F.length - 1]'(by omega) :=
      pairwise_getElem_lt hpair (by omega) (by omega) (by omega)
    have : u < frameEndpoint F := by
      rw [hend]
      exact lt_trans (by simpa [hright] using hu.2) hrt_lt_end
    exact Nat.le_of_lt this
  have huin : u ∈ framePrefix A F :=
    mem_filter.mpr ⟨huA, hupos, hule⟩
  have hnodup : F.Nodup := pairwise_nodup_lt hpair
  have hcard : F.toFinset.card = F.length := List.toFinset_card_of_nodup hnodup
  have hsubset : insert u F.toFinset ⊆ framePrefix A F := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hxF
    · exact huin
    · have hxFl : x ∈ F := List.mem_toFinset.mp hxF
      exact mem_filter.mpr ⟨hsub hxF, hpos x hxFl, le_frameEndpoint_of_mem hpair hxFl⟩
  have hcardins : (insert u F.toFinset).card = F.toFinset.card + 1 :=
    card_insert_of_notMem huFt
  have hle := card_le_card hsubset
  have : 2 * K + 1 ≤ (insert u F.toFinset).card := by
    omega
  exact le_trans this hle

/-! ### Unfolding supported masses -/

theorem shortShapeMass_eq {K : ℕ} {A : Finset ℕ} {ρ : ℝ} {F : List ℕ}
    (hK : 1 ≤ K) (hF : IsSupportedShortFrame A K F) :
    shortShapeMass A ρ F =
      ρ ^ (2 * K) * (1 - ρ) ^ (framePrefixCount A F - 2 * K) := by
  have hlen : F.length = 2 * K := hF.1
  have hdiv : F.length / 2 = K := by rw [hlen, two_mul_div_two]
  have hsup : IsSupportedShortFrame A (F.length / 2) F := by
    simpa [hdiv] using hF
  unfold shortShapeMass
  rw [if_pos ⟨hsup, by omega⟩, hlen]

theorem longShapeMass_eq {K : ℕ} {A : Finset ℕ} {ρ : ℝ} {F : List ℕ}
    (hK : 1 ≤ K) (hF : IsSupportedShortFrame A K F) {u : ℕ} (huA : u ∈ A)
    (hu : (mergeSlot hK F).1 < u ∧ u < (mergeSlot hK F).2) :
    longShapeMass A ρ F u =
      ρ ^ (2 * K + 1) * (1 - ρ) ^ (framePrefixCount A F - (2 * K + 1)) := by
  have hlen : F.length = 2 * K := hF.1
  have hdiv : F.length / 2 = K := by rw [hlen, two_mul_div_two]
  have hslot : mergeSlotOf F = mergeSlot hK F := mergeSlotOf_eq hK hlen
  have hsup : IsSupportedShortFrame A (F.length / 2) F := by
    simpa [hdiv] using hF
  unfold longShapeMass
  have hcond :
      IsSupportedShortFrame A (F.length / 2) F ∧ 1 ≤ F.length / 2 ∧
        (mergeSlotOf F).1 < u ∧ u < (mergeSlotOf F).2 ∧ u ∈ A :=
    ⟨hsup, by omega, by simpa [hslot] using hu.1, by simpa [hslot] using hu.2, huA⟩
  rw [if_pos hcond]
  have hpow : F.length + 1 = 2 * K + 1 := by omega
  have hexp : framePrefixCount A F - F.length - 1 =
      framePrefixCount A F - (2 * K + 1) := by
    rw [Nat.sub_sub, hlen]
  rw [hpow, hexp]

/-! ### Exact merge identity -/

/-- Empty slot: no long preimage. R96 (23), R97 (A27). -/
theorem merge_identity_empty_slot (A : Finset ℕ) (ρ : ℝ) (F : List ℕ)
    (hW : A.filter (fun u =>
        (mergeSlotOf F).1 < u ∧ u < (mergeSlotOf F).2) = ∅) :
    longMergedMass A ρ F = 0 := by
  simp [longMergedMass, hW]

/-- Exact central identity including every outer void in `n_F`.
Points after the endpoint are integrated out. R96 (23), R97 (A27). -/
theorem merge_identity {K : ℕ} {A : Finset ℕ} {ρ : ℝ} {F : List ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hK : 1 ≤ K)
    (hF : IsSupportedShortFrame A K F) :
    longMergedMass A ρ F
      = (A.filter (fun u =>
            (mergeSlot hK F).1 < u ∧ u < (mergeSlot hK F).2)).card *
          (ρ / (1 - ρ)) * shortShapeMass A ρ F := by
  let _ := hρ
  have hlen : F.length = 2 * K := hF.1
  have hslot : mergeSlotOf F = mergeSlot hK F := mergeSlotOf_eq hK hlen
  have hfilter :
      A.filter (fun u => (mergeSlotOf F).1 < u ∧ u < (mergeSlotOf F).2) =
        A.filter (fun u =>
          (mergeSlot hK F).1 < u ∧ u < (mergeSlot hK F).2) := by
    simp [hslot]
  unfold longMergedMass
  rw [hfilter, shortShapeMass_eq hK hF]
  set s := A.filter (fun u =>
      (mergeSlot hK F).1 < u ∧ u < (mergeSlot hK F).2)
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs, sum_empty]
    simp
  · obtain ⟨u0, hu0⟩ := hs
    have hu0A : u0 ∈ A := (mem_filter.mp hu0).1
    have hu0s : (mergeSlot hK F).1 < u0 ∧ u0 < (mergeSlot hK F).2 :=
      (mem_filter.mp hu0).2
    have hge := framePrefixCount_ge_succ hK hF hu0A hu0s
    have hterm : ∀ u ∈ s,
        longShapeMass A ρ F u =
          ρ ^ (2 * K + 1) *
            (1 - ρ) ^ (framePrefixCount A F - (2 * K + 1)) := by
      intro u hu
      have huA : u ∈ A := (mem_filter.mp hu).1
      have hus : (mergeSlot hK F).1 < u ∧ u < (mergeSlot hK F).2 :=
        (mem_filter.mp hu).2
      exact longShapeMass_eq hK hF huA hus
    rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
    set n := framePrefixCount A F
    have hn : n - 2 * K = n - (2 * K + 1) + 1 := by omega
    have h1ρ : (1 - ρ) ≠ 0 := by linarith
    have hpow : (1 - ρ) ^ (n - 2 * K) =
        (1 - ρ) ^ (n - (2 * K + 1)) * (1 - ρ) := by
      rw [hn, pow_succ]
    have hρpow : ρ ^ (2 * K + 1) = ρ ^ (2 * K) * ρ := pow_succ _ _
    have hmul :
        ρ ^ (2 * K + 1) * (1 - ρ) ^ (n - (2 * K + 1))
          = (ρ / (1 - ρ)) * (ρ ^ (2 * K) * (1 - ρ) ^ (n - 2 * K)) := by
      rw [hρpow, hpow]
      field_simp [h1ρ]
    rw [hmul]
    ring

end PrimeGapNormality.Prime
