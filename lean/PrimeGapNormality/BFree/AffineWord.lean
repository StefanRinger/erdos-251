import PrimeGapNormality.BFree.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact finite affine flip over the reals

Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 3.2 (3.3);
`rounds/round92/05_grok_positive_carry_update.md` §3.A.
Contract: C3 finite kernel
Audit: GREEN

The recursion is `C_{j+1} = b^(u_j) C_j - Q` with real states. Natural
subtraction truncated at zero is not used. A later visit count is the
sum of the word after the flipped time.
-/

namespace PrimeGapNormality.BFree

open Finset

/-- One affine carry step over `ℝ`. -/
def affineStep (b Q : ℝ) (u : ℕ) (C : ℝ) : ℝ :=
  b ^ u * C - Q

/-- Iterate `affineStep` along a visit word. Time `0` is the initial state. -/
def affinePath (b Q : ℝ) (u : ℕ → ℕ) (C0 : ℝ) : ℕ → ℝ
  | 0 => C0
  | n + 1 => affineStep b Q (u n) (affinePath b Q u C0 n)

theorem affinePath_zero (b Q : ℝ) (u : ℕ → ℕ) (C0 : ℝ) :
    affinePath b Q u C0 0 = C0 :=
  rfl

theorem affinePath_succ (b Q : ℝ) (u : ℕ → ℕ) (C0 : ℝ) (n : ℕ) :
    affinePath b Q u C0 (n + 1) = affineStep b Q (u n) (affinePath b Q u C0 n) :=
  rfl

theorem affineStep_same_map (b Q : ℝ) (u : ℕ) (C D : ℝ) :
    affineStep b Q u C - affineStep b Q u D = b ^ u * (C - D) := by
  simp [affineStep]
  ring

theorem affineStep_flip (b Q C : ℝ) :
    affineStep b Q 1 C - affineStep b Q 0 C = (b - 1) * C := by
  simp [affineStep, pow_one, pow_zero]
  ring

/-- Visits strictly after time `k` and strictly before time `n`. -/
def laterVisits (u : ℕ → ℕ) (k n : ℕ) : ℕ :=
  ∑ j ∈ range n, if k < j then u j else 0

theorem laterVisits_zero (u : ℕ → ℕ) (k : ℕ) : laterVisits u k 0 = 0 := by
  simp [laterVisits]

theorem laterVisits_succ (u : ℕ → ℕ) (k n : ℕ) :
    laterVisits u k (n + 1) =
      laterVisits u k n + if k < n then u n else 0 := by
  simp [laterVisits, sum_range_succ]

theorem laterVisits_of_le (u : ℕ → ℕ) {k n : ℕ} (hn : n ≤ k) :
    laterVisits u k n = 0 := by
  refine sum_eq_zero fun j hj => ?_
  have hjn : j < n := mem_range.mp hj
  have : ¬ k < j := fun hkj => (hjn.trans_le hn).not_gt hkj
  simp [this]

theorem affinePath_congr_word (b Q : ℝ) {u v : ℕ → ℕ} (C0 : ℝ) {n : ℕ}
    (h : ∀ j < n, u j = v j) :
    affinePath b Q u C0 n = affinePath b Q v C0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpref : ∀ j < n, u j = v j := fun j hj => h j (Nat.lt_succ_of_lt hj)
    rw [affinePath_succ, affinePath_succ, ih hpref, h n (Nat.lt_succ_self n)]

/-- Exact terminal gap after a single extra visit at time `k`.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (3.3).
Contract: C3
Audit: GREEN -/
theorem affine_flip_diff (b Q : ℝ) (uPlus uMinus : ℕ → ℕ) (C0 : ℝ) {H k : ℕ}
    (hk : k < H) (hagree : ∀ j < H, j ≠ k → uPlus j = uMinus j)
    (hplus : uPlus k = 1) (hminus : uMinus k = 0) :
    affinePath b Q uPlus C0 H - affinePath b Q uMinus C0 H =
      (b - 1) * affinePath b Q uPlus C0 k * b ^ laterVisits uPlus k H := by
  have hpref : ∀ j < k, uPlus j = uMinus j :=
    fun j hj => hagree j (hj.trans hk) (ne_of_lt hj)
  have hCeq : affinePath b Q uPlus C0 k = affinePath b Q uMinus C0 k :=
    affinePath_congr_word b Q C0 hpref
  have hgen : ∀ n, k + 1 ≤ n → n ≤ H →
      affinePath b Q uPlus C0 n - affinePath b Q uMinus C0 n =
        (b - 1) * affinePath b Q uPlus C0 k * b ^ laterVisits uPlus k n := by
    intro n hkn
    induction n, hkn using Nat.le_induction with
    | base =>
      intro _
      have hL : laterVisits uPlus k (k + 1) = 0 := by
        rw [laterVisits_succ, laterVisits_of_le (hn := le_rfl)]
        simp
      rw [affinePath_succ, affinePath_succ, hplus, hminus, hCeq, affineStep_flip,
        hL, pow_zero, mul_one]
    | succ n hkn ih =>
      intro hnH
      have ih' := ih (Nat.le_of_succ_le hnH)
      have hnlt : n < H := Nat.lt_of_succ_le hnH
      have hnk : k < n := Nat.lt_of_succ_le hkn
      have hsame : uPlus n = uMinus n :=
        hagree n hnlt (ne_of_gt hnk)
      rw [affinePath_succ, affinePath_succ, hsame, affineStep_same_map, ih',
        laterVisits_succ, if_pos hnk, pow_add, hsame]
      ring
  exact hgen H (Nat.succ_le_of_lt hk) le_rfl

/-- The flipped path cannot close if the common pre-flip state is positive.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (3.3);
`rounds/round92/05_grok_positive_carry_update.md` §3.A.
Contract: C3
Audit: GREEN -/
theorem affine_flip_diff_pos (b Q : ℝ) (uPlus uMinus : ℕ → ℕ) (C0 : ℝ) {H k : ℕ}
    (hb : (1 : ℝ) < b) (hC : 0 < affinePath b Q uPlus C0 k)
    (hk : k < H) (hagree : ∀ j < H, j ≠ k → uPlus j = uMinus j)
    (hplus : uPlus k = 1) (hminus : uMinus k = 0) :
    affinePath b Q uMinus C0 H < affinePath b Q uPlus C0 H := by
  have hdiff := affine_flip_diff b Q uPlus uMinus C0 hk hagree hplus hminus
  have hpos : 0 < (b - 1) * affinePath b Q uPlus C0 k *
      b ^ laterVisits uPlus k H := by
    have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
    exact mul_pos (mul_pos (sub_pos.mpr hb) hC) (pow_pos hb0 _)
  linarith

end PrimeGapNormality.BFree
