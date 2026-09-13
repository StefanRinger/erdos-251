import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Truncated subset Möbius remainder

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (8);
`rounds/round97/01_gpt_khl_merger_independent_audit.md` (A10);
`lean/PRIME_SIGNATURES.md` MobiusTV.
Contract: combinatorial remainder
Audit: GREEN

Boolean-lattice inversion on `Finset α`. No primes, no KHL. The window-TV
lemma with moment/`G` packaging is omitted this wave.
-/

namespace PrimeGapNormality.Prime

open Finset

/-! ### Binomial comparison (R97 (A10)) -/

/-- `binom n j ≤ binom n (r+1) * binom (r+1) j` for `j ≤ r` and `r+1 ≤ n`.

Source: `rounds/round97/01_gpt_khl_merger_independent_audit.md` (A10);
`lean/PRIME_SIGNATURES.md` MobiusTV.
Contract: combinatorial remainder
Audit: GREEN -/
theorem choose_le_choose_mul {n j r : ℕ} (hj : j ≤ r) (hr : r + 1 ≤ n) :
    n.choose j ≤ n.choose (r + 1) * (r + 1).choose j := by
  have hj' : j ≤ r + 1 := Nat.le_succ_of_le hj
  have hpos : 0 < (n - j).choose (r + 1 - j) :=
    Nat.choose_pos (Nat.sub_le_sub_right hr j)
  have hmul : n.choose j * 1 ≤ n.choose j * (n - j).choose (r + 1 - j) :=
    Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hpos)
  rw [Nat.mul_one, ← Nat.choose_mul hj'] at hmul
  exact hmul

/-! ### Coefficients and truncated polynomial -/

/-- Möbius coefficient `a_H` of a bounded set function.

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (8);
`rounds/round97/01_gpt_khl_merger_independent_audit.md` (A10);
`lean/PRIME_SIGNATURES.md` MobiusTV.
Contract: combinatorial remainder
Audit: GREEN -/
noncomputable def mobiusCoeff {α : Type*} (f : Finset α → ℝ) (H : Finset α) : ℝ :=
  ∑ J ∈ H.powerset, (-1 : ℝ) ^ (H.card - J.card) * f J

/-- Degree-`r` truncated Möbius polynomial `P_r f(U)`.

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (8);
`rounds/round97/01_gpt_khl_merger_independent_audit.md` (A10);
`lean/PRIME_SIGNATURES.md` MobiusTV.
Contract: combinatorial remainder
Audit: GREEN -/
noncomputable def truncPoly {α : Type*} (f : Finset α → ℝ) (r : ℕ) (U : Finset α) : ℝ :=
  ∑ H ∈ U.powerset.filter (fun H => H.card ≤ r), mobiusCoeff f H

/-- Source: `lean/PRIME_SIGNATURES.md` MobiusTV.
Contract: combinatorial remainder
Audit: GREEN -/
theorem abs_mobiusCoeff_le {α : Type*} (f : Finset α → ℝ) (H : Finset α)
    (hf : ∀ s, |f s| ≤ 1) :
    |mobiusCoeff f H| ≤ 2 ^ H.card := by
  calc
    |mobiusCoeff f H|
        ≤ ∑ J ∈ H.powerset, |(-1 : ℝ) ^ (H.card - J.card) * f J| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ J ∈ H.powerset, |f J| := by
      refine sum_congr rfl fun J _ => ?_
      rw [abs_mul, abs_neg_one_pow, one_mul]
    _ ≤ ∑ J ∈ H.powerset, (1 : ℝ) :=
      sum_le_sum fun J _ => hf J
    _ = (H.powerset.card : ℝ) := by
      simp [sum_const]
    _ = (2 : ℝ) ^ H.card := by
      rw [card_powerset, Nat.cast_pow]
      simp

private theorem sum_powerset_neg_one {α : Type*} [DecidableEq α] (x : Finset α) :
    ∑ m ∈ x.powerset, (-1 : ℝ) ^ m.card = if x = ∅ then 1 else 0 := by
  rw [sum_powerset_apply_card]
  simp only [nsmul_eq_mul]
  have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.alternating_sum_range_choose (n := x.card))
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_ite,
    Int.cast_zero] at h
  rw [if_congr card_eq_zero rfl rfl] at h
  refine Eq.trans ?_ h
  refine sum_congr rfl fun m _ => ?_
  rw [mul_comm]
  norm_cast

private theorem sum_signed_supersets {α : Type*} [DecidableEq α]
    (U J : Finset α) (hJ : J ⊆ U) :
    ∑ H ∈ U.powerset.filter (fun H => J ⊆ H), (-1 : ℝ) ^ (H.card - J.card) =
      if J = U then (1 : ℝ) else 0 := by
  calc
    ∑ H ∈ U.powerset.filter (fun H => J ⊆ H), (-1 : ℝ) ^ (H.card - J.card)
        = ∑ K ∈ (U \ J).powerset, (-1 : ℝ) ^ K.card := by
      refine sum_nbij' (fun H => H \ J) (fun K => J ∪ K) ?_ ?_ ?_ ?_ ?_
      · intro H hH
        have hH' := mem_filter.mp hH
        have hHU : H ⊆ U := mem_powerset.mp hH'.1
        exact mem_powerset.mpr (sdiff_subset_sdiff hHU (Subset.rfl : J ⊆ J))
      · intro K hK
        have hKU : K ⊆ U \ J := mem_powerset.mp hK
        refine mem_filter.mpr ?_
        exact ⟨mem_powerset.mpr (union_subset hJ (hKU.trans sdiff_subset)), subset_union_left⟩
      · intro H hH
        have hH' := mem_filter.mp hH
        exact union_sdiff_of_subset hH'.2
      · intro K hK
        have hKU : K ⊆ U \ J := mem_powerset.mp hK
        exact union_sdiff_cancel_left (disjoint_sdiff_self_right.mono_right hKU)
      · intro H hH
        have hH' := mem_filter.mp hH
        rw [card_sdiff_of_subset hH'.2]
    _ = if U \ J = ∅ then (1 : ℝ) else 0 :=
      sum_powerset_neg_one (U \ J)
    _ = if J = U then (1 : ℝ) else 0 := by
      refine if_congr ?_ rfl rfl
      rw [sdiff_eq_empty_iff_subset]
      exact ⟨fun h => Subset.antisymm hJ h, fun h => h ▸ Subset.rfl⟩

private theorem sum_comm_nested_powerset {α : Type*} [DecidableEq α] (U : Finset α)
    (g : Finset α → Finset α → ℝ) :
    ∑ H ∈ U.powerset, ∑ J ∈ H.powerset, g H J =
      ∑ J ∈ U.powerset, ∑ H ∈ U.powerset.filter (fun H => J ⊆ H), g H J := by
  refine sum_comm' ?_
  intro H J
  constructor
  · intro h
    have hHU : H ⊆ U := mem_powerset.mp h.1
    have hJH : J ⊆ H := mem_powerset.mp h.2
    refine ⟨mem_filter.mpr ⟨h.1, hJH⟩, mem_powerset.mpr (hJH.trans hHU)⟩
  · intro h
    have hH := mem_filter.mp h.1
    exact ⟨hH.1, mem_powerset.mpr hH.2⟩

/-- Full Möbius inversion on the boolean lattice: `∑_{H ⊆ U} a_H = f(U)`.

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (8);
`rounds/round97/01_gpt_khl_merger_independent_audit.md` (A10).
Contract: combinatorial remainder
Audit: GREEN -/
theorem sum_mobiusCoeff {α : Type*} [DecidableEq α] (f : Finset α → ℝ) (U : Finset α) :
    ∑ H ∈ U.powerset, mobiusCoeff f H = f U := by
  simp only [mobiusCoeff]
  rw [sum_comm_nested_powerset]
  have hfac :
      ∑ J ∈ U.powerset,
          ∑ H ∈ U.powerset.filter (fun H => J ⊆ H),
            (-1 : ℝ) ^ (H.card - J.card) * f J =
        ∑ J ∈ U.powerset,
          f J * ∑ H ∈ U.powerset.filter (fun H => J ⊆ H),
            (-1 : ℝ) ^ (H.card - J.card) := by
    refine sum_congr rfl fun J _ => ?_
    simp_rw [mul_comm _ (f J)]
    exact (mul_sum _ _ _).symm
  rw [hfac]
  have hinter :
      ∑ J ∈ U.powerset,
          f J * ∑ H ∈ U.powerset.filter (fun H => J ⊆ H),
            (-1 : ℝ) ^ (H.card - J.card) =
        ∑ J ∈ U.powerset, f J * (if J = U then (1 : ℝ) else 0) := by
    refine sum_congr rfl fun J hJ => ?_
    rw [sum_signed_supersets U J (mem_powerset.mp hJ)]
  rw [hinter]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_powerset_self, ite_true]

/-- Source: `lean/PRIME_SIGNATURES.md` MobiusTV.
Contract: combinatorial remainder
Audit: GREEN -/
theorem truncPoly_eq_of_card_le {α : Type*} [DecidableEq α] (f : Finset α → ℝ) {r : ℕ}
    {U : Finset α} (hf : ∀ s, |f s| ≤ 1) (hr : U.card ≤ r) :
    truncPoly f r U = f U := by
  have _ := hf
  have hfilt : U.powerset.filter (fun H => H.card ≤ r) = U.powerset := by
    refine filter_eq_self.mpr ?_
    intro H hH
    exact (card_le_card (mem_powerset.mp hH)).trans hr
  rw [truncPoly, hfilt, sum_mobiusCoeff]

private theorem sum_two_pow_choose (n : ℕ) :
    ∑ j ∈ range (n + 1), (2 : ℝ) ^ j * (n.choose j : ℝ) = (3 : ℝ) ^ n := by
  have h := add_pow (2 : ℝ) (1 : ℝ) n
  have h3 : (2 : ℝ) + 1 = 3 := by norm_num
  calc
    ∑ j ∈ range (n + 1), (2 : ℝ) ^ j * (n.choose j : ℝ)
        = ∑ j ∈ range (n + 1), (2 : ℝ) ^ j * (1 : ℝ) ^ (n - j) * (n.choose j : ℝ) := by
      refine sum_congr rfl fun j _ => ?_
      simp [one_pow]
    _ = ((2 : ℝ) + 1) ^ n := h.symm
    _ = (3 : ℝ) ^ n := by rw [h3]

private theorem range_filter_le_eq {n r : ℕ} (hr : r < n) :
    (range (n + 1)).filter (fun j => j ≤ r) = range (r + 1) := by
  ext j
  simp only [mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · intro h
    exact h.2
  · intro hj
    exact ⟨le_trans hj (Nat.le_of_lt hr), hj⟩

private theorem sum_two_pow_card_filter {α : Type*} (U : Finset α) {r : ℕ}
    (hr : r < U.card) :
    ∑ H ∈ U.powerset.filter (fun H => H.card ≤ r), (2 : ℝ) ^ H.card =
      ∑ j ∈ range (r + 1), (U.card.choose j : ℝ) * (2 : ℝ) ^ j := by
  have hcard :=
    (sum_powerset_apply_card (f := fun n => if n ≤ r then (2 : ℝ) ^ n else 0)
      (x := U)).symm
  rw [sum_filter, ← hcard]
  simp only [nsmul_eq_mul]
  have hite :
      ∀ j, (U.card.choose j : ℝ) * (if j ≤ r then (2 : ℝ) ^ j else 0) =
        if j ≤ r then (U.card.choose j : ℝ) * (2 : ℝ) ^ j else 0 := by
    intro j
    split_ifs <;> ring
  simp_rw [hite]
  rw [← sum_filter, range_filter_le_eq hr]

private theorem sum_two_pow_choose_le {n r : ℕ} (hr : r + 1 ≤ n) :
    ∑ j ∈ range (r + 1), (2 : ℝ) ^ j * (n.choose j : ℝ) ≤
      (3 : ℝ) ^ (r + 1) * (n.choose (r + 1) : ℝ) := by
  have hterm :
      ∀ j ∈ range (r + 1),
        (2 : ℝ) ^ j * (n.choose j : ℝ) ≤
          (n.choose (r + 1) : ℝ) * ((2 : ℝ) ^ j * ((r + 1).choose j : ℝ)) := by
    intro j hj
    have hjr : j ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hch : (n.choose j : ℝ) ≤ (n.choose (r + 1) : ℝ) * ((r + 1).choose j : ℝ) := by
      have := choose_le_choose_mul hjr hr
      exact_mod_cast this
    have h2 : 0 ≤ (2 : ℝ) ^ j := by positivity
    calc
      (2 : ℝ) ^ j * (n.choose j : ℝ)
          ≤ (2 : ℝ) ^ j * ((n.choose (r + 1) : ℝ) * ((r + 1).choose j : ℝ)) :=
        mul_le_mul_of_nonneg_left hch h2
      _ = (n.choose (r + 1) : ℝ) * ((2 : ℝ) ^ j * ((r + 1).choose j : ℝ)) := by
        ring
  have hsum := sum_le_sum hterm
  have hfactor :
      ∑ j ∈ range (r + 1),
          (n.choose (r + 1) : ℝ) * ((2 : ℝ) ^ j * ((r + 1).choose j : ℝ)) =
        (n.choose (r + 1) : ℝ) *
          ∑ j ∈ range (r + 1), (2 : ℝ) ^ j * ((r + 1).choose j : ℝ) := by
    rw [← mul_sum]
  have hsub : range (r + 1) ⊆ range (r + 2) :=
    range_subset_range.mpr (Nat.le_succ (r + 1))
  have hnonneg :
      ∀ j ∈ range (r + 2), j ∉ range (r + 1) →
        0 ≤ (2 : ℝ) ^ j * ((r + 1).choose j : ℝ) := by
    intro j _ _
    positivity
  have hpartial :
      ∑ j ∈ range (r + 1), (2 : ℝ) ^ j * ((r + 1).choose j : ℝ) ≤
        ∑ j ∈ range (r + 2), (2 : ℝ) ^ j * ((r + 1).choose j : ℝ) :=
    sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hfull :
      ∑ j ∈ range (r + 2), (2 : ℝ) ^ j * ((r + 1).choose j : ℝ) = (3 : ℝ) ^ (r + 1) :=
    sum_two_pow_choose (r + 1)
  calc
    ∑ j ∈ range (r + 1), (2 : ℝ) ^ j * (n.choose j : ℝ)
        ≤ ∑ j ∈ range (r + 1),
            (n.choose (r + 1) : ℝ) * ((2 : ℝ) ^ j * ((r + 1).choose j : ℝ)) :=
      hsum
    _ = (n.choose (r + 1) : ℝ) *
          ∑ j ∈ range (r + 1), (2 : ℝ) ^ j * ((r + 1).choose j : ℝ) :=
      hfactor
    _ ≤ (n.choose (r + 1) : ℝ) *
          ∑ j ∈ range (r + 2), (2 : ℝ) ^ j * ((r + 1).choose j : ℝ) :=
      mul_le_mul_of_nonneg_left hpartial (Nat.cast_nonneg _)
    _ = (n.choose (r + 1) : ℝ) * (3 : ℝ) ^ (r + 1) := by
      rw [hfull]
    _ = (3 : ℝ) ^ (r + 1) * (n.choose (r + 1) : ℝ) := by
      rw [mul_comm]

/-- Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (8);
`rounds/round97/01_gpt_khl_merger_independent_audit.md` (A10);
`lean/PRIME_SIGNATURES.md` MobiusTV.
Contract: combinatorial remainder
Audit: GREEN -/
theorem truncPoly_remainder {α : Type*} (f : Finset α → ℝ) {r : ℕ} {U : Finset α}
    (hf : ∀ s, |f s| ≤ 1) (hr : r < U.card) :
    |f U - truncPoly f r U| ≤ (1 + 3 ^ (r + 1)) * U.card.choose (r + 1) := by
  have htrunc :
      |truncPoly f r U| ≤
        ∑ H ∈ U.powerset.filter (fun H => H.card ≤ r), (2 : ℝ) ^ H.card := by
    calc
      |truncPoly f r U|
          ≤ ∑ H ∈ U.powerset.filter (fun H => H.card ≤ r), |mobiusCoeff f H| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ H ∈ U.powerset.filter (fun H => H.card ≤ r), (2 : ℝ) ^ H.card :=
        sum_le_sum fun H _ => abs_mobiusCoeff_le f H hf
  have hsum := sum_two_pow_card_filter U hr
  have hbin :
      ∑ j ∈ range (r + 1), (2 : ℝ) ^ j * (U.card.choose j : ℝ) ≤
        (3 : ℝ) ^ (r + 1) * (U.card.choose (r + 1) : ℝ) :=
    sum_two_pow_choose_le (Nat.succ_le_of_lt hr)
  have hC : (1 : ℝ) ≤ (U.card.choose (r + 1) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.choose_pos (Nat.succ_le_of_lt hr)))
  have hswap :
      ∑ j ∈ range (r + 1), (U.card.choose j : ℝ) * (2 : ℝ) ^ j =
        ∑ j ∈ range (r + 1), (2 : ℝ) ^ j * (U.card.choose j : ℝ) :=
    sum_congr rfl fun j _ => mul_comm _ _
  have hpoly :
      |truncPoly f r U| ≤ (3 : ℝ) ^ (r + 1) * (U.card.choose (r + 1) : ℝ) := by
    calc
      |truncPoly f r U|
          ≤ ∑ H ∈ U.powerset.filter (fun H => H.card ≤ r), (2 : ℝ) ^ H.card :=
        htrunc
      _ = ∑ j ∈ range (r + 1), (U.card.choose j : ℝ) * (2 : ℝ) ^ j :=
        hsum
      _ = ∑ j ∈ range (r + 1), (2 : ℝ) ^ j * (U.card.choose j : ℝ) :=
        hswap
      _ ≤ (3 : ℝ) ^ (r + 1) * (U.card.choose (r + 1) : ℝ) :=
        hbin
  have hfU : |f U| ≤ 1 := hf U
  have hadd :
      (1 : ℝ) + (3 : ℝ) ^ (r + 1) * (U.card.choose (r + 1) : ℝ) ≤
        (1 + (3 : ℝ) ^ (r + 1)) * (U.card.choose (r + 1) : ℝ) := by
    calc
      (1 : ℝ) + (3 : ℝ) ^ (r + 1) * (U.card.choose (r + 1) : ℝ)
          ≤ (U.card.choose (r + 1) : ℝ) +
              (3 : ℝ) ^ (r + 1) * (U.card.choose (r + 1) : ℝ) := by
        linarith
      _ = (1 + (3 : ℝ) ^ (r + 1)) * (U.card.choose (r + 1) : ℝ) := by
        ring
  calc
    |f U - truncPoly f r U|
        ≤ |f U| + |truncPoly f r U| := by
      rw [sub_eq_add_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
    _ ≤ (1 : ℝ) + (3 : ℝ) ^ (r + 1) * (U.card.choose (r + 1) : ℝ) :=
      add_le_add hfU hpoly
    _ ≤ (1 + (3 : ℝ) ^ (r + 1)) * (U.card.choose (r + 1) : ℝ) :=
      hadd

end PrimeGapNormality.Prime
