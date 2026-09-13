import PrimeGapNormality.Prime.RankDelete
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite one-gap polynomial phase

Phase `∑_{k=1}^{L} P(x_k - x_{k-1}) B^{-k}` with real (not `ℕ`)
differences. Distinct from `finiteFPhase`, which uses
`P(x_k) - P(x_{k-1})`.

Interior 0-based index `j` with `j + 1 < L` has free phase
`B^{-(j+1)} P(u-a) + B^{-(j+2)} P(c-u)`. Paper index `1 ≤ j < L`
uses exponents `j` and `j+1`; Lean adds one.

Leading coefficient at degree `R ≥ 1`:
`a_R B^{-(j+1)} (1 + (-1)^R / B)`, never cancelled for `B ≥ 2`.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` §5;
`rounds/round103/03_grok_gap_polynomial_implementation_update.md` P1.A.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Classical
open Finset Polynomial

set_option maxHeartbeats 800000

/-- Real gap `x_{k+1} - x_k` (casts before subtracting).

Source: `rounds/round103/03_grok_gap_polynomial_implementation_update.md` P1.A.
Contract: API
Audit: GREEN -/
noncomputable def realGap (xs : List ℕ) (k : ℕ) : ℝ :=
  (phasePoint xs (k + 1) : ℝ) - (phasePoint xs k : ℝ)

/-- Finite one-gap polynomial phase.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` (U_P trunc).
Contract: API
Audit: GREEN -/
noncomputable def finiteGapPolyPhase (P : ℝ[X]) (B L : ℕ) (xs : List ℕ) : ℝ :=
  ∑ k ∈ range L, eval (realGap xs k) P / (B : ℝ) ^ (k + 1)

/-- Free two-summand phase at Lean deletion index `j`.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` (5.1).
Contract: API
Audit: GREEN -/
noncomputable def freeGapPolyPhase (P : ℝ[X]) (B j : ℕ) (a u c : ℝ) : ℝ :=
  eval (u - a) P / (B : ℝ) ^ (j + 1) + eval (c - u) P / (B : ℝ) ^ (j + 2)

/-- Polynomial in the free slot `u`.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` (5.1).
Contract: API
Audit: GREEN -/
noncomputable def freeGapPolyPoly (P : ℝ[X]) (B j : ℕ) (a c : ℝ) : ℝ[X] :=
  C ((B : ℝ) ^ (j + 1))⁻¹ * P.comp (X - C a) +
    C ((B : ℝ) ^ (j + 2))⁻¹ * P.comp (C c - X)

private theorem base_cast_ne_zero {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

theorem finiteGapPolyPhase_X (B L : ℕ) (xs : List ℕ) :
    finiteGapPolyPhase X B L xs = finiteGapPhase B L xs := by
  unfold finiteGapPolyPhase finiteGapPhase realGap
  refine sum_congr rfl fun k _ => ?_
  rw [eval_X]

theorem freeGapPolyPhase_eval (P : ℝ[X]) (B j : ℕ) (a u c : ℝ) :
    eval u (freeGapPolyPoly P B j a c) = freeGapPolyPhase P B j a u c := by
  unfold freeGapPolyPoly freeGapPolyPhase
  simp [eval_add, eval_mul, eval_C, eval_comp, eval_sub, eval_X, div_eq_inv_mul]

theorem freeGapPolyPhase_X_sq (B j : ℕ) (a u c : ℝ) :
    freeGapPolyPhase (X ^ 2) B j a u c =
      (u - a) ^ 2 / (B : ℝ) ^ (j + 1) + (c - u) ^ 2 / (B : ℝ) ^ (j + 2) := by
  unfold freeGapPolyPhase
  simp [eval_pow, eval_X]

/-- Algebraic second difference of the quadratic free phase.
Equals `2 h² B^{-(j+1)} (1 + 1/B)`, independent of anchors.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` (5.3).
Contract: API
Audit: GREEN -/
theorem freeGapPolyPhase_X_sq_secondDiff {B j : ℕ} (hB : 2 ≤ B)
    (a c u h : ℝ) :
    freeGapPolyPhase (X ^ 2) B j a (u + h) c
      - 2 * freeGapPolyPhase (X ^ 2) B j a u c
      + freeGapPolyPhase (X ^ 2) B j a (u - h) c
      = 2 * h ^ 2 * ((B : ℝ) ^ (j + 1))⁻¹ * (1 + 1 / B) := by
  have hb0 := base_cast_ne_zero hB
  simp only [freeGapPolyPhase_X_sq]
  have hpow : (B : ℝ) ^ (j + 2) = (B : ℝ) ^ (j + 1) * B := pow_succ _ _
  have hbpow : (B : ℝ) ^ (j + 1) ≠ 0 := pow_ne_zero _ hb0
  field_simp [hb0, hbpow, hpow]
  ring

private theorem natDegree_C_sub_X (c : ℝ) : natDegree (C c - X) = 1 := by
  rw [← neg_sub, natDegree_neg, natDegree_X_sub_C]

private theorem leadingCoeff_C_sub_X (c : ℝ) : leadingCoeff (C c - X) = -1 := by
  rw [← neg_sub, leadingCoeff_neg, leadingCoeff_X_sub_C]

private theorem one_add_neg_one_pow_div_ne_zero {B R : ℕ} (hB : 2 ≤ B) :
    1 + (-1 : ℝ) ^ R / B ≠ 0 := by
  have hb0 := base_cast_ne_zero hB
  have hB1 : (B : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < B := (Nat.one_lt_cast).mpr (lt_of_lt_of_le (by decide : 1 < 2) hB)
    exact sub_ne_zero.mpr this.ne'
  have hBp1 : (B : ℝ) + 1 ≠ 0 := by
    have : (0 : ℝ) < (B : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num)
    exact this.ne'
  by_cases hEven : Even R
  · have h1 : (-1 : ℝ) ^ R = 1 := Even.neg_one_pow hEven
    rw [h1]
    have : 1 + (1 : ℝ) / B = (B + 1) / B := by field_simp [hb0]
    rw [this]
    exact div_ne_zero hBp1 hb0
  · have hOdd : Odd R := Nat.not_even_iff_odd.mp hEven
    have h1 : (-1 : ℝ) ^ R = -1 := Odd.neg_one_pow hOdd
    rw [h1]
    have : 1 + (-1 : ℝ) / B = (B - 1) / B := by
      field_simp [hb0]
      ring
    rw [this]
    exact div_ne_zero hB1 hb0

/-- Leading coefficient (5.2) at Lean index `j`. Never zero for `B ≥ 2`
and `1 ≤ natDegree P`.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` (5.2).
Contract: API
Audit: GREEN -/
theorem freeGapPolyPoly_leadingCoeff (P : ℝ[X]) {B j : ℕ} (hB : 2 ≤ B)
    (hR : 1 ≤ natDegree P) (a c : ℝ) :
    leadingCoeff (freeGapPolyPoly P B j a c)
      = leadingCoeff P * ((B : ℝ) ^ (j + 1))⁻¹
        * (1 + (-1 : ℝ) ^ natDegree P / B) := by
  have hb0 := base_cast_ne_zero hB
  have hP0 : P ≠ 0 := ne_zero_of_natDegree_gt (Nat.succ_le_iff.mp hR)
  have hdegLin1 : natDegree (X - C a) ≠ 0 := by
    rw [natDegree_X_sub_C]
    exact one_ne_zero
  have hdegLin2 : natDegree (C c - X) ≠ 0 := by
    rw [natDegree_C_sub_X]
    exact one_ne_zero
  have hdeg1 : natDegree (P.comp (X - C a)) = natDegree P := by
    rw [natDegree_comp, natDegree_X_sub_C, mul_one]
  have hdeg2 : natDegree (P.comp (C c - X)) = natDegree P := by
    rw [natDegree_comp, natDegree_C_sub_X, mul_one]
  have hlc1 : leadingCoeff (P.comp (X - C a)) = leadingCoeff P := by
    rw [leadingCoeff_comp hdegLin1, leadingCoeff_X_sub_C, one_pow, mul_one]
  have hlc2 : leadingCoeff (P.comp (C c - X))
      = leadingCoeff P * (-1 : ℝ) ^ natDegree P := by
    rw [leadingCoeff_comp hdegLin2, leadingCoeff_C_sub_X]
  have hα0 : ((B : ℝ) ^ (j + 1))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hb0)
  have hβ0 : ((B : ℝ) ^ (j + 2))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hb0)
  have hlcP : leadingCoeff P ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  have hneg1 : (-1 : ℝ) ≠ 0 := by norm_num
  have hlcC1 :
      leadingCoeff (C ((B : ℝ) ^ (j + 1))⁻¹ * P.comp (X - C a))
        = ((B : ℝ) ^ (j + 1))⁻¹ * leadingCoeff P := by
    have hmul :
        leadingCoeff (C ((B : ℝ) ^ (j + 1))⁻¹) *
          leadingCoeff (P.comp (X - C a)) ≠ 0 := by
      rw [leadingCoeff_C, hlc1]
      exact mul_ne_zero hα0 hlcP
    rw [leadingCoeff_mul' hmul, leadingCoeff_C, hlc1]
  have hlcC2 :
      leadingCoeff (C ((B : ℝ) ^ (j + 2))⁻¹ * P.comp (C c - X))
        = ((B : ℝ) ^ (j + 2))⁻¹ * (leadingCoeff P * (-1 : ℝ) ^ natDegree P) := by
    have hmul :
        leadingCoeff (C ((B : ℝ) ^ (j + 2))⁻¹) *
          leadingCoeff (P.comp (C c - X)) ≠ 0 := by
      rw [leadingCoeff_C, hlc2]
      exact mul_ne_zero hβ0 (mul_ne_zero hlcP (pow_ne_zero _ hneg1))
    rw [leadingCoeff_mul' hmul, leadingCoeff_C, hlc2]
  have hpow : (B : ℝ) ^ (j + 2) = (B : ℝ) ^ (j + 1) * B := pow_succ _ _
  have hsumLead :
      leadingCoeff (C ((B : ℝ) ^ (j + 1))⁻¹ * P.comp (X - C a))
        + leadingCoeff (C ((B : ℝ) ^ (j + 2))⁻¹ * P.comp (C c - X))
        = leadingCoeff P * ((B : ℝ) ^ (j + 1))⁻¹
          * (1 + (-1 : ℝ) ^ natDegree P / B) := by
    rw [hlcC1, hlcC2, hpow]
    have hbpow : (B : ℝ) ^ (j + 1) ≠ 0 := pow_ne_zero _ hb0
    field_simp [hb0, hbpow]
  have hne :
      leadingCoeff (C ((B : ℝ) ^ (j + 1))⁻¹ * P.comp (X - C a))
        + leadingCoeff (C ((B : ℝ) ^ (j + 2))⁻¹ * P.comp (C c - X)) ≠ 0 := by
    rw [hsumLead]
    exact mul_ne_zero (mul_ne_zero hlcP hα0)
      (one_add_neg_one_pow_div_ne_zero (R := natDegree P) hB)
  have hp : C ((B : ℝ) ^ (j + 1))⁻¹ * P.comp (X - C a) ≠ 0 :=
    leadingCoeff_ne_zero.mp (by
      rw [hlcC1]
      exact mul_ne_zero hα0 hlcP)
  have hq : C ((B : ℝ) ^ (j + 2))⁻¹ * P.comp (C c - X) ≠ 0 :=
    leadingCoeff_ne_zero.mp (by
      rw [hlcC2]
      exact mul_ne_zero hβ0 (mul_ne_zero hlcP (pow_ne_zero _ hneg1)))
  have hdegEq :
      degree (C ((B : ℝ) ^ (j + 1))⁻¹ * P.comp (X - C a)) =
        degree (C ((B : ℝ) ^ (j + 2))⁻¹ * P.comp (C c - X)) := by
    have hnat :
        natDegree (C ((B : ℝ) ^ (j + 1))⁻¹ * P.comp (X - C a)) =
          natDegree (C ((B : ℝ) ^ (j + 2))⁻¹ * P.comp (C c - X)) := by
      rw [natDegree_C_mul hα0, natDegree_C_mul hβ0, hdeg1, hdeg2]
    rw [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_inj, hnat]
  unfold freeGapPolyPoly
  rw [leadingCoeff_add_of_degree_eq hdegEq hne, hsumLead]

theorem gapPoly_summand_diff_insertAt {B L j : ℕ} (hL : 2 ≤ L)
    (hj : j + 1 < L) (P : ℝ[X]) (F : List ℕ) (u u' : ℕ)
    (hlen : L - 1 ≤ F.length) {k : ℕ} (hk : k ∈ range L) :
    (eval (realGap (insertAt F j u) k) P -
        eval (realGap (insertAt F j u') k) P) / (B : ℝ) ^ (k + 1) =
      if k = j then
        (eval ((u : ℝ) - (deletionSlot F j).1) P -
          eval ((u' : ℝ) - (deletionSlot F j).1) P) / (B : ℝ) ^ (j + 1)
      else if k = j + 1 then
        (eval ((deletionSlot F j).2 - (u : ℝ)) P -
          eval ((deletionSlot F j).2 - (u' : ℝ)) P) / (B : ℝ) ^ (j + 2)
      else 0 := by
  have hjF : j < F.length := j_lt_frame_length hj hlen
  have hjle : j ≤ F.length := Nat.le_of_lt hjF
  have := hL
  have := mem_range.mp hk
  by_cases hkj : k = j
  · subst hkj
    simp [realGap, phasePoint_insertAt_succ hjle, phasePoint_insertAt_left,
      sub_div]
  · by_cases hkj1 : k = j + 1
    · subst hkj1
      simp [realGap, phasePoint_insertAt_succ hjle, phasePoint_insertAt_right,
        sub_div]
    · have hdiff :
          realGap (insertAt F j u) k = realGap (insertAt F j u') k := by
        unfold realGap
        by_cases hlt : k < j
        · have hk1 : k + 1 ≤ j := by omega
          have hk0 : k ≤ j := by omega
          simp [phasePoint_insertAt_of_le hk1, phasePoint_insertAt_of_le hk0]
        · have hgt : j + 1 < k := by omega
          have hgt1 : j + 1 < k + 1 := by omega
          simp [phasePoint_insertAt_of_gt hgt1, phasePoint_insertAt_of_gt hgt]
      simp [hkj, hkj1, hdiff, sub_self, zero_div]

/-- Two-summand identity: moving the deleted rank changes only the
free phase `ψ(u)`.

Source: `rounds/round103/03_grok_gap_polynomial_implementation_update.md` P1.A.
Contract: API
Audit: GREEN -/
theorem finiteGapPolyPhase_sub_insertAt {B L j : ℕ} (hL : 2 ≤ L)
    (hj : j + 1 < L) (P : ℝ[X]) (F : List ℕ) (u u' : ℕ)
    (hlen : L - 1 ≤ F.length) :
    finiteGapPolyPhase P B L (insertAt F j u)
      - finiteGapPolyPhase P B L (insertAt F j u') =
      freeGapPolyPhase P B j (deletionSlot F j).1 u (deletionSlot F j).2
        - freeGapPolyPhase P B j (deletionSlot F j).1 u' (deletionSlot F j).2 := by
  unfold finiteGapPolyPhase
  rw [← sum_sub_distrib]
  simp_rw [← sub_div]
  have hterm :
      ∑ k ∈ range L,
          (eval (realGap (insertAt F j u) k) P -
              eval (realGap (insertAt F j u') k) P) / (B : ℝ) ^ (k + 1) =
        ∑ k ∈ range L,
          (if k = j then
            (eval ((u : ℝ) - (deletionSlot F j).1) P -
              eval ((u' : ℝ) - (deletionSlot F j).1) P) / (B : ℝ) ^ (j + 1)
          else if k = j + 1 then
            (eval ((deletionSlot F j).2 - (u : ℝ)) P -
              eval ((deletionSlot F j).2 - (u' : ℝ)) P) / (B : ℝ) ^ (j + 2)
          else 0) :=
    sum_congr rfl fun k hk =>
      gapPoly_summand_diff_insertAt hL hj P F u u' hlen hk
  rw [hterm]
  have hsub : ({j, j + 1} : Finset ℕ) ⊆ range L := by
    intro x hx
    simp only [mem_insert, mem_singleton, mem_range] at hx ⊢
    omega
  have hne : j ≠ j + 1 := by omega
  have hzero :
      ∀ k ∈ range L \ {j, j + 1},
        (if k = j then
          (eval ((u : ℝ) - (deletionSlot F j).1) P -
            eval ((u' : ℝ) - (deletionSlot F j).1) P) / (B : ℝ) ^ (j + 1)
        else if k = j + 1 then
          (eval ((deletionSlot F j).2 - (u : ℝ)) P -
            eval ((deletionSlot F j).2 - (u' : ℝ)) P) / (B : ℝ) ^ (j + 2)
        else 0) = 0 := by
    intro k hk
    simp only [mem_sdiff, mem_insert, mem_singleton] at hk
    have hkj : k ≠ j := fun h => hk.2 (Or.inl h)
    have hkj1 : k ≠ j + 1 := fun h => hk.2 (Or.inr h)
    simp [hkj, hkj1]
  have hpair :
      ∑ k ∈ ({j, j + 1} : Finset ℕ),
          (if k = j then
            (eval ((u : ℝ) - (deletionSlot F j).1) P -
              eval ((u' : ℝ) - (deletionSlot F j).1) P) / (B : ℝ) ^ (j + 1)
          else if k = j + 1 then
            (eval ((deletionSlot F j).2 - (u : ℝ)) P -
              eval ((deletionSlot F j).2 - (u' : ℝ)) P) / (B : ℝ) ^ (j + 2)
          else 0) =
        (eval ((u : ℝ) - (deletionSlot F j).1) P -
            eval ((u' : ℝ) - (deletionSlot F j).1) P) / (B : ℝ) ^ (j + 1)
          + (eval ((deletionSlot F j).2 - (u : ℝ)) P -
              eval ((deletionSlot F j).2 - (u' : ℝ)) P) / (B : ℝ) ^ (j + 2) := by
    rw [sum_pair hne]
    simp
  have hsplit := sum_sdiff (s₁ := ({j, j + 1} : Finset ℕ)) (s₂ := range L)
    (f := fun k =>
      if k = j then
        (eval ((u : ℝ) - (deletionSlot F j).1) P -
          eval ((u' : ℝ) - (deletionSlot F j).1) P) / (B : ℝ) ^ (j + 1)
      else if k = j + 1 then
        (eval ((deletionSlot F j).2 - (u : ℝ)) P -
          eval ((deletionSlot F j).2 - (u' : ℝ)) P) / (B : ℝ) ^ (j + 2)
      else 0)
    hsub
  rw [← hsplit, sum_eq_zero hzero, zero_add, hpair]
  unfold freeGapPolyPhase
  ring

/-- Degree-1 regression recovers the linear rank-deletion identity.

Source: `rounds/round103/03_grok_gap_polynomial_implementation_update.md` P1.A.
Contract: API
Audit: GREEN -/
theorem finiteGapPolyPhase_X_sub_insertAt {B L j : ℕ} (hB : 2 ≤ B)
    (hL : 2 ≤ L) (hj : j + 1 < L) (F : List ℕ) (u u' : ℕ)
    (hlen : L - 1 ≤ F.length) :
    finiteGapPolyPhase X B L (insertAt F j u)
      - finiteGapPolyPhase X B L (insertAt F j u') =
      ((B : ℝ) - 1) * ((u : ℝ) - u') / (B : ℝ) ^ (j + 2) := by
  simpa [finiteGapPolyPhase_X] using
    phase_linear_in_deleted hB hL hj F u u' hlen

end PrimeGapNormality.Prime
