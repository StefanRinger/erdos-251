import PrimeGapNormality.Prime.PeriodicKernel
import PrimeGapNormality.Prime.Independence
import PrimeGapNormality.Prime.JointWeyl
import PrimeGapNormality.Prime.JointLift
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Index passage: residue, dyadic, and density-one Cesàro lifts

Paper v0.3 `lem:progression` and the surrounding index passage in
“From local means to the common orbit” / rational coefficients:

* vanishing residue-class Cesàro means of a bounded character imply
  the full Cesàro mean (interleaving);
* vanishing means on dyadic index blocks `(M,2M]` imply the full
  Cesàro mean (backward dyadic decomposition);
* vanishing on a density-one set of indices implies the full mean;
* `JointWeyl` on the common clock `B^k` implies base-`B` Weyl, as a
  residue-block form complementary to `Components.weylCriterion_of_pow`.

The opposite residue restriction (full Weyl ⇒ arithmetic progressions)
is `PeriodicKernel.commonClock_centeredLift`; this module uses that
lemma as the paper’s positive progression statement and does not
repeat its `F_H` argument. Scalar Wall remains
`Independence.weylCriterion_of_mul`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` Lemma `lem:progression`,
subsection “From local means to the common orbit”, last paragraph of
“Rational coefficients and position series”.
Contract: API
Audit: GREEN
-/

open Finset
open Filter (Tendsto atTop)
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 2000000

/-! ### Circle-character bound -/

private theorem two_pi_I_mul (x : ℝ) :
    (2 * Real.pi * Complex.I * (x : ℂ) : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) := by
  simp [mul_comm, mul_left_comm, Complex.ofReal_mul]

private theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [two_pi_I_mul, Complex.norm_exp_I_mul_ofReal]

private theorem cesaro_norm_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (N : ℕ) :
    ‖(∑ n ∈ range N, a n) / N‖ ≤ 1 := by
  by_cases hN : N = 0
  · subst hN
    simp
  · have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    rw [norm_div]
    have hNn : ‖(N : ℂ)‖ = N := by simp
    rw [hNn]
    have hsum : ‖∑ n ∈ range N, a n‖ ≤ N := by
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∑ n ∈ range N, ‖a n‖ ≤ ∑ n ∈ range N, (1 : ℝ) :=
        sum_le_sum fun _ _ => ha _
      have hcard : (∑ n ∈ range N, (1 : ℝ)) = N := by simp [sum_const]
      exact h1.trans_eq hcard
    exact (div_le_one hpos).mpr hsum

/-! ### Residue-class splitting -/

private theorem sum_range_mul_block (a : ℕ → ℂ) (k Q : ℕ) :
    ∑ n ∈ range (k * Q), a n =
      ∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    have hsplit :
        ∑ n ∈ range (k * (Q + 1)), a n =
          ∑ n ∈ range (k * Q), a n + ∑ r ∈ range k, a (k * Q + r) := by
      rw [Nat.mul_succ, sum_range_add]
    rw [hsplit, ih]
    have hadd :
        ∑ r ∈ range k, ∑ m ∈ range (Q + 1), a (k * m + r) =
          ∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r) +
            ∑ r ∈ range k, a (k * Q + r) := by
      simp_rw [sum_range_succ]
      rw [sum_add_distrib]
    rw [hadd]

private theorem sum_range_mod_split (a : ℕ → ℂ) (k N : ℕ) :
    ∑ n ∈ range N, a n =
      ∑ r ∈ range k, ∑ m ∈ range (N / k), a (k * m + r) +
        ∑ r ∈ range (N % k), a (k * (N / k) + r) := by
  have hN : k * (N / k) + N % k = N := Nat.div_add_mod N k
  nth_rw 1 [← hN]
  rw [sum_range_add, sum_range_mul_block]

/-- Cesàro means along every residue class `n ≡ r (mod k)` of a
unimodular sequence imply the full Cesàro mean. Paper interleaving of
the `k` residue sequences.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` rational coefficients
(interleaving); complementary consumer for
`Components.weylCriterion_of_pow`.
Contract: API
Audit: GREEN -/
theorem tendsto_cesaro_of_residueClasses {k : ℕ} (hk : 0 < k) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (hres : ∀ r < k, Tendsto (fun M : ℕ =>
      (∑ m ∈ range M, a (k * m + r)) / M) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, a n) / N) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hEv :
      ∀ᶠ M in atTop, ∀ r ∈ range k,
        dist ((∑ m ∈ range M, a (k * m + r)) / M) 0 < ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro r hr
    exact (hres r (mem_range.mp hr)).eventually (Metric.ball_mem_nhds 0 hε2)
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp hEv
  obtain ⟨Nbound, hNbound⟩ := exists_nat_gt ((2 * (k : ℝ)) / ε)
  filter_upwards [Filter.eventually_ge_atTop (max (k * M0) (Nbound + 1))] with N hNge
  have hN1 : 1 ≤ N :=
    (Nat.succ_le_succ (Nat.zero_le Nbound)).trans (le_trans (le_max_right _ _) hNge)
  have hNpos : 0 < N := Nat.succ_le_iff.mp hN1
  have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hNk : k * M0 ≤ N := le_trans (le_max_left _ _) hNge
  have hQle : M0 ≤ N / k := by
    have : k * M0 / k ≤ N / k := Nat.div_le_div_right hNk
    rwa [Nat.mul_div_cancel_left M0 hk] at this
  have hNgt : Nbound + 1 ≤ N := le_trans (le_max_right _ _) hNge
  have hkN : (k : ℝ) / N < ε / 2 := by
    have hgt : (2 * (k : ℝ)) / ε < N :=
      hNbound.trans (Nat.cast_lt.mpr (Nat.lt_of_succ_le hNgt))
    have hmul : 2 * (k : ℝ) < ε * N := by
      have := (div_lt_iff₀ hε).mp hgt
      linarith
    rw [div_lt_div_iff₀ hNposR (by norm_num : (0 : ℝ) < 2)]
    linarith
  let Q : ℕ := N / k
  let R : ℕ := N % k
  have hQN : (Q : ℝ) / N ≤ 1 / k := by
    by_cases hQ0 : Q = 0
    · have : (Q : ℝ) / N = 0 := by simp [hQ0]
      rw [this]
      exact div_nonneg (by norm_num) hkR.le
    · have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ0)
      have hNeq : (N : ℝ) = (k : ℝ) * Q + (R : ℝ) := by
        exact_mod_cast (Nat.div_add_mod N k).symm
      have hge : (k : ℝ) * Q ≤ N := by
        have : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
        linarith
      have hle : (Q : ℝ) / N ≤ (Q : ℝ) / ((k : ℝ) * Q) :=
        div_le_div_of_nonneg_left hQpos.le (mul_pos hkR hQpos) hge
      have hsimp : (Q : ℝ) / ((k : ℝ) * Q) = 1 / k := by
        field_simp [hQpos.ne', hkR.ne']
      exact hle.trans_eq hsimp
  have hinner : ∀ r ∈ range k,
      ‖∑ m ∈ range Q, a (k * m + r)‖ ≤ (Q : ℝ) * (ε / 2) := by
    intro r hr
    by_cases hQ0 : Q = 0
    · simp [hQ0]
    · have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ0)
      have havg : ‖(∑ m ∈ range Q, a (k * m + r)) / Q‖ < ε / 2 := by
        simpa [dist_zero_right] using hM0 Q hQle r hr
      have hnorm :
          ‖∑ m ∈ range Q, a (k * m + r)‖ =
            (Q : ℝ) * ‖(∑ m ∈ range Q, a (k * m + r)) / Q‖ := by
        have hdiv := norm_div (∑ m ∈ range Q, a (k * m + r)) (Q : ℂ)
        have hQn : ‖(Q : ℂ)‖ = (Q : ℝ) := by simp
        rw [hdiv, hQn]
        exact (mul_div_cancel₀ _ hQpos.ne').symm
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left havg.le hQpos.le
  have hmain :
      ‖∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)‖ ≤
        (k : ℝ) * (Q : ℝ) * (ε / 2) := by
    have hle :=
      (norm_sum_le (range k) fun r => ∑ m ∈ range Q, a (k * m + r)).trans
        (sum_le_sum hinner)
    have hsumc :
        ∑ r ∈ range k, (Q : ℝ) * (ε / 2) = (k : ℝ) * (Q : ℝ) * (ε / 2) := by
      rw [sum_const, card_range, nsmul_eq_mul]
      ring
    exact hle.trans_eq hsumc
  have hrem : ‖∑ r ∈ range R, a (k * Q + r)‖ ≤ k := by
    have hsum1 : ∑ r ∈ range R, (1 : ℝ) = (R : ℝ) := by
      simp [sum_const, nsmul_eq_mul, card_range]
    have hle :=
      (norm_sum_le (range R) fun r => a (k * Q + r)).trans
        ((sum_le_sum fun _ _ => ha _).trans_eq hsum1)
    have hRle : (R : ℝ) ≤ k := (Nat.cast_lt.mpr (Nat.mod_lt N hk)).le
    exact hle.trans hRle
  have havgbound : ‖(∑ n ∈ range N, a n) / N‖ < ε := by
    have hdecomp :
        (∑ n ∈ range N, a n) / N =
          ((∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)) +
            ∑ r ∈ range R, a (k * Q + r)) / N := by
      change (∑ n ∈ range N, a n) / N =
          ((∑ r ∈ range k, ∑ m ∈ range (N / k), a (k * m + r)) +
            ∑ r ∈ range (N % k), a (k * (N / k) + r)) / N
      rw [sum_range_mod_split]
    rw [hdecomp, norm_div]
    have hNnorm : ‖(N : ℂ)‖ = N := by simp
    rw [hNnorm]
    have htri :
        ‖(∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)) +
            ∑ r ∈ range R, a (k * Q + r)‖ / N ≤
          ‖∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)‖ / N +
            ‖∑ r ∈ range R, a (k * Q + r)‖ / N := by
      have := div_le_div_of_nonneg_right
        (norm_add_le (∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r))
          (∑ r ∈ range R, a (k * Q + r))) (Nat.cast_nonneg N)
      simpa [add_div] using this
    have hmainN :
        ‖∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)‖ / N ≤ ε / 2 := by
      have hle :
          ‖∑ r ∈ range k, ∑ m ∈ range Q, a (k * m + r)‖ / N ≤
            ((k : ℝ) * (Q : ℝ) * (ε / 2)) / N :=
        div_le_div_of_nonneg_right hmain (Nat.cast_nonneg N)
      have hrew : ((k : ℝ) * (Q : ℝ) * (ε / 2)) / N =
          (k : ℝ) * ((Q : ℝ) / N) * (ε / 2) := by
        ring
      have hscale :
          (k : ℝ) * ((Q : ℝ) / N) * (ε / 2) ≤
            (k : ℝ) * (1 / k) * (ε / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQN (Nat.cast_nonneg k))
          (div_nonneg hε.le (by norm_num))
      have hcancel : (k : ℝ) * (1 / k) * (ε / 2) = ε / 2 := by
        field_simp [hkR.ne']
      exact (hle.trans_eq hrew).trans (hscale.trans_eq hcancel)
    have hremN : ‖∑ r ∈ range R, a (k * Q + r)‖ / N < ε / 2 :=
      lt_of_le_of_lt (div_le_div_of_nonneg_right hrem (Nat.cast_nonneg N)) hkN
    have hεsplit : ε / 2 + ε / 2 = ε := add_halves ε
    exact lt_of_le_of_lt htri (hεsplit ▸ add_lt_add_of_le_of_lt hmainN hremN)
  simpa [dist_zero_right] using havgbound

/-! ### Dyadic index blocks -/

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n :=
      Nat.succ_le_iff.mpr (pow_pos (by norm_num : (0 : ℕ) < 2) n)
    have hsum : n + 1 ≤ 2 ^ n + 2 ^ n := by omega
    have htwo : 2 ^ n + 2 ^ n = 2 ^ n * 2 := by ring
    rw [pow_succ]
    exact hsum.trans_eq htwo

private theorem sum_inv_two_succ (q : ℕ) :
    ∑ j ∈ range q, (1 : ℝ) / (2 : ℝ) ^ (j + 1)
      = 1 - (1 : ℝ) / (2 : ℝ) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_range_succ, ih]
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hp : (2 : ℝ) ^ q ≠ 0 := pow_ne_zero q h2
    have hpow : (2 : ℝ) ^ (q + 1) = (2 : ℝ) ^ q * 2 := pow_succ _ _
    have :
        (1 : ℝ) - 1 / (2 : ℝ) ^ q + 1 / (2 : ℝ) ^ (q + 1)
          = 1 - 1 / (2 : ℝ) ^ (q + 1) := by
      rw [hpow]
      field_simp [h2, hp]
      ring
    exact this

private theorem range_union_Ico {m n : ℕ} (h : m ≤ n) :
    range m ∪ Ico m n = range n := by
  ext x
  simp only [mem_union, mem_range, mem_Ico]
  omega

private theorem disjoint_range_Ico (m n : ℕ) :
    Disjoint (range m) (Ico m n) := by
  refine disjoint_left.mpr ?_
  intro x hx hx2
  simp only [mem_range, mem_Ico] at hx hx2
  omega

private theorem sum_range_split_Ico (a : ℕ → ℂ) {m n : ℕ} (h : m ≤ n) :
    ∑ x ∈ range n, a x = ∑ x ∈ range m, a x + ∑ x ∈ Ico m n, a x := by
  rw [← sum_union (disjoint_range_Ico m n), range_union_Ico h]

private theorem sum_range_dyadic_split (a : ℕ → ℂ) (N q : ℕ) :
    ∑ n ∈ range N, a n =
      ∑ n ∈ range (N / 2 ^ q), a n +
        ∑ j ∈ range q, ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hle : N / 2 ^ (q + 1) ≤ N / 2 ^ q :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2)
        (Nat.le_succ q)) (pow_pos (by norm_num : (0 : ℕ) < 2) q)
    calc
      ∑ n ∈ range N, a n
          = ∑ n ∈ range (N / 2 ^ q), a n +
              ∑ j ∈ range q, ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n :=
        ih
      _ = (∑ n ∈ range (N / 2 ^ (q + 1)), a n +
            ∑ n ∈ Ico (N / 2 ^ (q + 1)) (N / 2 ^ q), a n) +
            ∑ j ∈ range q, ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n := by
        rw [sum_range_split_Ico a hle]
      _ = ∑ n ∈ range (N / 2 ^ (q + 1)), a n +
            (∑ j ∈ range q, ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n +
              ∑ n ∈ Ico (N / 2 ^ (q + 1)) (N / 2 ^ q), a n) := by
        abel
      _ = ∑ n ∈ range (N / 2 ^ (q + 1)), a n +
            ∑ j ∈ range (q + 1), ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n := by
        rw [sum_range_succ]

private theorem Ico_insert_left {M : ℕ} (hM : 0 < M) :
    Ico M (2 * M) = insert M (Ico (M + 1) (2 * M)) := by
  ext n
  simp only [mem_insert, mem_Ico]
  constructor
  · intro h
    rcases eq_or_lt_of_le h.1 with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨Nat.succ_le_iff.mpr hlt, h.2⟩
  · rintro (rfl | h)
    · exact ⟨le_rfl, by omega⟩
    · exact ⟨le_trans (Nat.le_succ M) h.1, h.2⟩

private theorem Ioc_insert_right {M : ℕ} (hM : 0 < M) :
    Ioc M (2 * M) = insert (2 * M) (Ico (M + 1) (2 * M)) := by
  ext n
  simp only [mem_insert, mem_Ioc, mem_Ico]
  constructor
  · intro h
    rcases eq_or_lt_of_le h.2 with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨Nat.succ_le_iff.mpr h.1, hlt⟩
  · rintro (rfl | h)
    · exact ⟨by omega, le_rfl⟩
    · exact ⟨Nat.succ_le_iff.mp h.1, h.2.le⟩

private theorem dyadic_Ioc_sub_Ico (a : ℕ → ℂ) {M : ℕ} (hM : 0 < M) :
    ∑ n ∈ Ioc M (2 * M), a n - ∑ n ∈ Ico M (2 * M), a n =
      a (2 * M) - a M := by
  have hMnot : M ∉ Ico (M + 1) (2 * M) := by
    simp [mem_Ico]
  have h2Mnot : 2 * M ∉ Ico (M + 1) (2 * M) := by
    simp [mem_Ico]
  rw [Ico_insert_left hM, Ioc_insert_right hM, sum_insert hMnot, sum_insert h2Mnot]
  abel

private theorem tendsto_div_two_pow_atTop (k : ℕ) :
    Tendsto (fun N : ℕ => N / 2 ^ k) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun M => ?_
  refine ⟨M * 2 ^ k, fun N hN => ?_⟩
  have hk : 0 < 2 ^ k := pow_pos (by norm_num : (0 : ℕ) < 2) k
  exact (Nat.le_div_iff_mul_le hk).mpr hN

private theorem tendsto_Ioc_iff_Ico (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    Tendsto (fun M : ℕ => (∑ n ∈ Ioc M (2 * M), a n) / M) atTop (𝓝 0) ↔
      Tendsto (fun M : ℕ => (∑ n ∈ Ico M (2 * M), a n) / M) atTop (𝓝 0) := by
  have hbd :
      Tendsto (fun M : ℕ => (a (2 * M) - a M) / M) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [Filter.eventually_ge_atTop 1,
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually
        (Metric.ball_mem_nhds (0 : ℝ) hε)] with M hM1 h2M
    have hsub : ‖a (2 * M) - a M‖ ≤ (2 : ℝ) := by
      have hle :=
        (norm_sub_le (a (2 * M)) (a M)).trans (add_le_add (ha _) (ha _))
      have h11 : (1 : ℝ) + 1 = 2 := by norm_num
      exact hle.trans_eq h11
    have hle : ‖(a (2 * M) - a M) / M‖ ≤ (2 : ℝ) / M := by
      rw [norm_div]
      have hMn : ‖(M : ℂ)‖ = M := by simp
      rw [hMn]
      exact div_le_div_of_nonneg_right hsub (Nat.cast_nonneg M)
    have hnn : 0 ≤ (2 : ℝ) / M :=
      div_nonneg (by norm_num) (Nat.cast_nonneg M)
    have h2lt : (2 : ℝ) / M < ε := by
      have hdist : dist ((2 : ℝ) / M) 0 < ε := h2M
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hdist
      exact hdist
    simpa [dist_zero_right] using lt_of_le_of_lt hle h2lt
  have heq :
      (fun M : ℕ =>
        (∑ n ∈ Ioc M (2 * M), a n) / M
          - (∑ n ∈ Ico M (2 * M), a n) / M) =ᶠ[atTop]
        fun M => (a (2 * M) - a M) / M := by
    filter_upwards [Filter.eventually_ge_atTop 1] with M hM
    have hMpos : 0 < M := Nat.succ_le_iff.mp hM
    rw [← sub_div, dyadic_Ioc_sub_Ico a hMpos]
  have hdiff :
      Tendsto (fun M : ℕ =>
        (∑ n ∈ Ioc M (2 * M), a n) / M
          - (∑ n ∈ Ico M (2 * M), a n) / M) atTop (𝓝 0) :=
    Filter.Tendsto.congr' heq.symm hbd
  constructor
  · intro hIoc
    have h := hIoc.sub hdiff
    have heq' :
        (fun M : ℕ =>
          (∑ n ∈ Ioc M (2 * M), a n) / M
            - ((∑ n ∈ Ioc M (2 * M), a n) / M
              - (∑ n ∈ Ico M (2 * M), a n) / M)) =
          fun M => (∑ n ∈ Ico M (2 * M), a n) / M := by
      funext M
      abel
    rw [heq'] at h
    simpa using h
  · intro hIco
    have h := hIco.add hdiff
    have heq' :
        (fun M : ℕ =>
          (∑ n ∈ Ico M (2 * M), a n) / M
            + ((∑ n ∈ Ioc M (2 * M), a n) / M
              - (∑ n ∈ Ico M (2 * M), a n) / M)) =
          fun M => (∑ n ∈ Ioc M (2 * M), a n) / M := by
      funext M
      abel
    rw [heq'] at h
    simpa using h

private theorem Ico_div_two_sub (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (K : ℕ) :
    ‖(∑ n ∈ Ico (K / 2) K, a n)
        - ∑ n ∈ Ico (K / 2) (2 * (K / 2)), a n‖ ≤ 1 := by
  have hK : K = 2 * (K / 2) + K % 2 := (Nat.div_add_mod K 2).symm
  have hrem : K % 2 = 0 ∨ K % 2 = 1 := by
    have : K % 2 < 2 := Nat.mod_lt K (by norm_num)
    omega
  rcases hrem with h0 | h1
  · have heq : 2 * (K / 2) = K := by omega
    rw [heq]
    simp
  · have heq : K = 2 * (K / 2) + 1 := by omega
    have hMle : K / 2 ≤ 2 * (K / 2) :=
      Nat.le_mul_of_pos_left (K / 2) (by norm_num : (0 : ℕ) < 2)
    have hinsert :
        Ico (K / 2) K = insert (2 * (K / 2)) (Ico (K / 2) (2 * (K / 2))) := by
      ext n
      simp only [mem_insert, mem_Ico]
      constructor
      · intro h
        have hn : K / 2 ≤ n ∧ n < K := h
        have hn2 : n < 2 * (K / 2) + 1 := by
          rw [← heq]
          exact hn.2
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hn2) with hlt | rfl
        · exact Or.inr ⟨hn.1, hlt⟩
        · exact Or.inl rfl
      · rintro (rfl | h)
        · exact ⟨hMle, by omega⟩
        · exact ⟨h.1, lt_trans h.2 (by omega)⟩
    have hnot : 2 * (K / 2) ∉ Ico (K / 2) (2 * (K / 2)) := by
      simp [mem_Ico]
    rw [hinsert, sum_insert hnot]
    have hcancel :
        a (2 * (K / 2)) + ∑ n ∈ Ico (K / 2) (2 * (K / 2)), a n
          - ∑ n ∈ Ico (K / 2) (2 * (K / 2)), a n =
          a (2 * (K / 2)) := by
      abel
    rw [hcancel]
    exact ha _

/-- Vanishing means on dyadic index blocks `Ioc M (2M) = (M,2M] ∩ ℕ`
imply the full Cesàro mean, for unimodular sequences. Paper: peel
`q` doubling blocks above `N/2^q`, then `N → ∞` and `q → ∞`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:globalroot) and the
dyadic index passage after it.
Contract: API
Audit: GREEN -/
theorem tendsto_cesaro_of_dyadicBlocks (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (hdy : Tendsto (fun M : ℕ =>
      (∑ n ∈ Ioc M (2 * M), a n) / M) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, a n) / N) atTop (𝓝 0) := by
  have hIco : Tendsto (fun M : ℕ =>
      (∑ n ∈ Ico M (2 * M), a n) / M) atTop (𝓝 0) :=
    (tendsto_Ioc_iff_Ico a ha).mp hdy
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  by_cases hε1 : 1 < ε
  · filter_upwards [Filter.eventually_ge_atTop 1] with N _hN
    simpa [dist_zero_right] using lt_of_le_of_lt (cesaro_norm_le a ha N) hε1
  · obtain ⟨q0, hq0⟩ := exists_nat_gt (4 / ε)
    let q : ℕ := q0
    have hqpow : (4 : ℝ) / ε < (2 : ℝ) ^ q := by
      have hle : (q0 : ℝ) ≤ (2 : ℝ) ^ q0 := by
        have hnat := nat_le_two_pow q0
        have hcast : ((2 ^ q0 : ℕ) : ℝ) = (2 : ℝ) ^ q0 := Nat.cast_pow _ _
        exact (Nat.cast_le.mpr hnat).trans_eq hcast
      exact hq0.trans_le hle
    have hqε : (1 : ℝ) / (2 : ℝ) ^ q < ε / 4 := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ q := pow_pos (by norm_num) _
      have hεsq : 0 < ε := hε
      rw [div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 4)]
      have := (div_lt_iff₀ hεsq).mp hqpow
      linarith
    have hEv :
        ∀ᶠ N : ℕ in atTop, ∀ j ∈ range q,
          dist
            ((∑ n ∈ Ico (N / 2 ^ (j + 1) : ℕ) (2 * (N / 2 ^ (j + 1) : ℕ)), a n) /
              (N / 2 ^ (j + 1) : ℕ))
            (0 : ℂ) < ε / 2 := by
      rw [Filter.eventually_all_finset]
      intro j _hj
      exact (hIco.comp (tendsto_div_two_pow_atTop (j + 1))).eventually
        (Metric.ball_mem_nhds (0 : ℂ) (half_pos hε))
    obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp hEv
    obtain ⟨Nbound, hNbound⟩ := exists_nat_gt ((4 * (q : ℝ)) / ε)
    filter_upwards [Filter.eventually_ge_atTop
      (max (max (2 ^ q) (M0 * 2 ^ q)) (Nbound + 1))] with N hNge
    have hNpow : 2 ^ q ≤ N :=
      le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hNge)
    have hNM0 : M0 * 2 ^ q ≤ N :=
      le_trans (le_max_right (2 ^ q) (M0 * 2 ^ q))
        (le_trans (le_max_left _ _) hNge)
    have hNgt : Nbound + 1 ≤ N := le_trans (le_max_right _ _) hNge
    have hNpos : 0 < N :=
      lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 2) q) hNpow
    have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
    have h2q : 0 < 2 ^ q := pow_pos (by norm_num : (0 : ℕ) < 2) q
    have hqN : (q : ℝ) / N < ε / 4 := by
      have hgt : (4 * (q : ℝ)) / ε < N :=
        hNbound.trans (Nat.cast_lt.mpr (Nat.lt_of_succ_le hNgt))
      have hmul : 4 * (q : ℝ) < ε * N := by
        have := (div_lt_iff₀ hε).mp hgt
        linarith
      rw [div_lt_div_iff₀ hNposR (by norm_num : (0 : ℝ) < 4)]
      linarith
    have hprefix :
        ‖(∑ n ∈ range (N / 2 ^ q), a n) / N‖ ≤ (1 : ℝ) / (2 : ℝ) ^ q := by
      have hcard : ‖∑ n ∈ range (N / 2 ^ q), a n‖ ≤ (N / 2 ^ q : ℕ) := by
        refine (norm_sum_le _ _).trans ?_
        have h1 : ∑ n ∈ range (N / 2 ^ q), ‖a n‖ ≤
            ∑ n ∈ range (N / 2 ^ q), (1 : ℝ) :=
          sum_le_sum fun _ _ => ha _
        have hc : (∑ n ∈ range (N / 2 ^ q), (1 : ℝ)) = (N / 2 ^ q : ℕ) := by
          simp [sum_const]
        exact h1.trans_eq hc
      have h2R : (0 : ℝ) < (2 : ℝ) ^ q := pow_pos (by norm_num) _
      have hcast : ((2 ^ q : ℕ) : ℝ) = (2 : ℝ) ^ q := Nat.cast_pow _ _
      have hleM : ((N / 2 ^ q : ℕ) : ℝ) * (2 : ℝ) ^ q ≤ N := by
        have := Nat.mul_div_le N (2 ^ q)
        have hcast' : (((2 ^ q) * (N / 2 ^ q) : ℕ) : ℝ) ≤ N :=
          Nat.cast_le.mpr this
        rw [Nat.cast_mul, hcast, mul_comm] at hcast'
        exact hcast'
      have hMle : ((N / 2 ^ q : ℕ) : ℝ) ≤ (N : ℝ) / (2 : ℝ) ^ q :=
        (le_div_iff₀ h2R).mpr hleM
      rw [norm_div]
      have hNn : ‖(N : ℂ)‖ = N := by simp
      rw [hNn]
      have h1 : ‖∑ n ∈ range (N / 2 ^ q), a n‖ / N ≤
          ((N / 2 ^ q : ℕ) : ℝ) / N :=
        div_le_div_of_nonneg_right hcard (Nat.cast_nonneg N)
      have h2 : ((N / 2 ^ q : ℕ) : ℝ) / N ≤
          ((N : ℝ) / (2 : ℝ) ^ q) / N :=
        div_le_div_of_nonneg_right hMle (Nat.cast_nonneg N)
      have h3 : ((N : ℝ) / (2 : ℝ) ^ q) / N = 1 / (2 : ℝ) ^ q := by
        field_simp [hNposR.ne', h2R.ne']
      exact h1.trans (h2.trans_eq h3)
    have hblocks :
        ‖(∑ j ∈ range q,
            ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n) / N‖ ≤
          ε / 2 + (q : ℝ) / N := by
      have hpt : ∀ j ∈ range q,
          ‖∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n‖ ≤
            (N / 2 ^ (j + 1) : ℕ) * (ε / 2) + 1 := by
        intro j hj
        have hjq : j < q := mem_range.mp hj
        have hle_exp : j + 1 ≤ q := Nat.succ_le_of_lt hjq
        have hMge' : N / 2 ^ q ≤ N / 2 ^ (j + 1) :=
          Nat.div_le_div_left
            (Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hle_exp)
            (pow_pos (by norm_num : (0 : ℕ) < 2) (j + 1))
        have hMpos : 0 < N / 2 ^ (j + 1) :=
          lt_of_lt_of_le (Nat.div_pos hNpow h2q) hMge'
        let M : ℕ := N / 2 ^ (j + 1)
        let K : ℕ := N / 2 ^ j
        have hMK : M = K / 2 := by
          dsimp [M, K]
          have hdiv : N / 2 ^ (j + 1) = N / (2 ^ j * 2) := by
            rw [pow_succ]
          rw [hdiv, ← Nat.div_div_eq_div_mul]
        have hdiff := Ico_div_two_sub a ha K
        have hrew : Ico (K / 2) (2 * (K / 2)) = Ico M (2 * M) := by
          rw [← hMK]
        rw [hrew, ← hMK] at hdiff
        have hN_ge_M0 : M0 ≤ N := by
          have hmul : M0 ≤ M0 * 2 ^ q := Nat.le_mul_of_pos_right M0 h2q
          exact le_trans hmul hNM0
        have havg : ‖(∑ n ∈ Ico M (2 * M), a n) / M‖ < ε / 2 := by
          have hdist := hM0 N hN_ge_M0 j hj
          simpa [dist_zero_right] using hdist
        have hnorm :
            ‖∑ n ∈ Ico M (2 * M), a n‖ =
              (M : ℝ) * ‖(∑ n ∈ Ico M (2 * M), a n) / M‖ := by
          have hdiv := norm_div (∑ n ∈ Ico M (2 * M), a n) (M : ℂ)
          have hMn : ‖(M : ℂ)‖ = (M : ℝ) := by simp
          rw [hdiv, hMn]
          exact (mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr
            (Nat.pos_iff_ne_zero.mp hMpos))).symm
        have hdiff' :
            ‖(∑ n ∈ Ico M K, a n) - ∑ n ∈ Ico M (2 * M), a n‖ ≤ 1 :=
          hdiff
        have hblock :
            ‖∑ n ∈ Ico M K, a n‖ ≤ ‖∑ n ∈ Ico M (2 * M), a n‖ + 1 := by
          have hx :=
            norm_add_le
              ((∑ n ∈ Ico M K, a n) - ∑ n ∈ Ico M (2 * M), a n)
              (∑ n ∈ Ico M (2 * M), a n)
          have hdecomp :
              ((∑ n ∈ Ico M K, a n) - ∑ n ∈ Ico M (2 * M), a n) +
                  ∑ n ∈ Ico M (2 * M), a n =
                ∑ n ∈ Ico M K, a n := by
            abel
          rw [hdecomp] at hx
          calc
            ‖∑ n ∈ Ico M K, a n‖
                ≤ ‖(∑ n ∈ Ico M K, a n) - ∑ n ∈ Ico M (2 * M), a n‖ +
                    ‖∑ n ∈ Ico M (2 * M), a n‖ :=
              hx
            _ ≤ 1 + ‖∑ n ∈ Ico M (2 * M), a n‖ :=
              add_le_add hdiff' le_rfl
            _ = ‖∑ n ∈ Ico M (2 * M), a n‖ + 1 :=
              add_comm _ _
        have hIcoBd : ‖∑ n ∈ Ico M (2 * M), a n‖ ≤ (M : ℝ) * (ε / 2) := by
          rw [hnorm]
          exact mul_le_mul_of_nonneg_left havg.le (Nat.cast_nonneg _)
        exact hblock.trans (add_le_add hIcoBd le_rfl)
      have hsum :=
        (norm_sum_le (range q) fun j =>
          ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n).trans
          (sum_le_sum hpt)
      have hfact :
          ∑ j ∈ range q, ((N / 2 ^ (j + 1) : ℕ) * (ε / 2) + 1) =
            (∑ j ∈ range q, ((N / 2 ^ (j + 1) : ℕ) : ℝ) * (ε / 2)) + q := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
      have hscale :
          (∑ j ∈ range q, ((N / 2 ^ (j + 1) : ℕ) : ℝ) * (ε / 2)) / N ≤ ε / 2 := by
        have hterm : ∀ j ∈ range q,
            ((N / 2 ^ (j + 1) : ℕ) : ℝ) * (ε / 2) / N ≤
              ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) * (ε / 2) := by
          intro j _hj
          have h2R : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
          have hcast : ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) :=
            Nat.cast_pow _ _
          have hleM : ((N / 2 ^ (j + 1) : ℕ) : ℝ) * (2 : ℝ) ^ (j + 1) ≤ N := by
            have := Nat.mul_div_le N (2 ^ (j + 1))
            have hcast' : (((2 ^ (j + 1)) * (N / 2 ^ (j + 1)) : ℕ) : ℝ) ≤ N :=
              Nat.cast_le.mpr this
            rw [Nat.cast_mul, hcast, mul_comm] at hcast'
            exact hcast'
          have hMle : ((N / 2 ^ (j + 1) : ℕ) : ℝ) ≤
              (N : ℝ) / (2 : ℝ) ^ (j + 1) :=
            (le_div_iff₀ h2R).mpr hleM
          have hleft :
              ((N / 2 ^ (j + 1) : ℕ) : ℝ) * (ε / 2) / N =
                (((N / 2 ^ (j + 1) : ℕ) : ℝ) / N) * (ε / 2) := by
            ring
          have hmid : ((N / 2 ^ (j + 1) : ℕ) : ℝ) / N ≤
              (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by
            have hstep : ((N / 2 ^ (j + 1) : ℕ) : ℝ) / N ≤
                ((N : ℝ) / (2 : ℝ) ^ (j + 1)) / N :=
              div_le_div_of_nonneg_right hMle (Nat.cast_nonneg N)
            have hsimp : ((N : ℝ) / (2 : ℝ) ^ (j + 1)) / N =
                1 / (2 : ℝ) ^ (j + 1) := by
              field_simp [hNposR.ne', h2R.ne']
            exact hstep.trans_eq hsimp
          have : (((N / 2 ^ (j + 1) : ℕ) : ℝ) / N) * (ε / 2) ≤
              (1 / (2 : ℝ) ^ (j + 1)) * (ε / 2) :=
            mul_le_mul_of_nonneg_right hmid
              (div_nonneg hε.le (by norm_num : (0 : ℝ) ≤ 2))
          exact hleft.trans_le this
        have hsumt :
            (∑ j ∈ range q, ((N / 2 ^ (j + 1) : ℕ) : ℝ) * (ε / 2)) / N ≤
              ∑ j ∈ range q, ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) * (ε / 2) := by
          have hswap :
              (∑ j ∈ range q, ((N / 2 ^ (j + 1) : ℕ) : ℝ) * (ε / 2)) / N =
                ∑ j ∈ range q,
                  ((N / 2 ^ (j + 1) : ℕ) : ℝ) * (ε / 2) / N := by
            simp_rw [div_eq_mul_inv, sum_mul]
          rw [hswap]
          exact sum_le_sum hterm
        have hgeom :
            ∑ j ∈ range q, ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) * (ε / 2) ≤ ε / 2 := by
          have hfact :
              ∑ j ∈ range q, ((1 : ℝ) / (2 : ℝ) ^ (j + 1)) * (ε / 2) =
                (∑ j ∈ range q, (1 : ℝ) / (2 : ℝ) ^ (j + 1)) * (ε / 2) := by
            simp_rw [mul_comm _ (ε / 2), ← mul_sum]
          rw [hfact, sum_inv_two_succ]
          have hle : 1 - (1 : ℝ) / (2 : ℝ) ^ q ≤ 1 := by
            have : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ q :=
              div_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
            linarith
          have hmul :=
            mul_le_mul_of_nonneg_right hle
              (div_nonneg hε.le (by norm_num : (0 : ℝ) ≤ 2))
          rwa [one_mul] at hmul
        exact hsumt.trans hgeom
      rw [norm_div]
      have hNn : ‖(N : ℂ)‖ = N := by simp
      rw [hNn]
      have hsumN :
          ‖∑ j ∈ range q, ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n‖ / N ≤
            (∑ j ∈ range q, ((N / 2 ^ (j + 1) : ℕ) * (ε / 2) + 1)) / N :=
        div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
      have hrew :
          (∑ j ∈ range q, ((N / 2 ^ (j + 1) : ℕ) * (ε / 2) + 1)) / N =
            (∑ j ∈ range q, ((N / 2 ^ (j + 1) : ℕ) : ℝ) * (ε / 2)) / N +
              (q : ℝ) / N := by
        rw [hfact, add_div]
      exact (hsumN.trans_eq hrew).trans (add_le_add hscale le_rfl)
    have hdecomp := sum_range_dyadic_split a N q
    have havg : ‖(∑ n ∈ range N, a n) / N‖ < ε := by
      have hsplit :
          (∑ n ∈ range N, a n) / N =
            (∑ n ∈ range (N / 2 ^ q), a n) / N +
              (∑ j ∈ range q,
                ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n) / N := by
        rw [hdecomp, add_div]
      rw [hsplit]
      have htri :=
        norm_add_le ((∑ n ∈ range (N / 2 ^ q), a n) / N)
          ((∑ j ∈ range q,
            ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n) / N)
      have hpre : ‖(∑ n ∈ range (N / 2 ^ q), a n) / N‖ < ε / 4 :=
        lt_of_le_of_lt hprefix hqε
      have hblk : ‖(∑ j ∈ range q,
            ∑ n ∈ Ico (N / 2 ^ (j + 1)) (N / 2 ^ j), a n) / N‖ <
          ε / 2 + ε / 4 :=
        lt_of_le_of_lt hblocks (by linarith [hqN])
      have : ε / 4 + (ε / 2 + ε / 4) = ε := by ring
      exact htri.trans_lt ((add_lt_add hpre hblk).trans_eq this)
    simpa [dist_zero_right] using havg

/-! ### Density-one index sets -/

/-- Vanishing of `(∑_{n ∈ S_N} a_n)/N` on subsets `S_N ⊆ {0,…,N-1}` of
density one implies the full Cesàro mean. Complement mass tends to
zero; unimodular characters cost at most that mass.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` index passage
(density-one remainder after dyadic blocks).
Contract: API
Audit: GREEN -/
theorem tendsto_cesaro_of_densityOne (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (S : ℕ → Finset ℕ) (hS : ∀ N, S N ⊆ range N)
    (hden : Tendsto (fun N : ℕ => ((S N).card : ℝ) / N) atTop (𝓝 1))
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ S N, a n) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, a n) / N) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hone : Tendsto (fun N : ℕ => (N : ℝ) / N) atTop (𝓝 1) := by
    have heq : (fun N : ℕ => (N : ℝ) / N) =ᶠ[atTop] fun _ => (1 : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hN0 : (N : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.succ_le_iff.mp hN).ne'
      exact div_self hN0
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  have hcomp : Tendsto (fun N : ℕ => ((N : ℝ) - (S N).card) / N) atTop (𝓝 0) := by
    have heq :
        (fun N : ℕ => ((N : ℝ) - (S N).card) / N) =
          fun N : ℕ => (N : ℝ) / N - ((S N).card : ℝ) / N := by
      funext N
      exact sub_div _ _ _
    rw [heq]
    have hsub := hone.sub hden
    simpa using hsub
  filter_upwards [Filter.eventually_ge_atTop 1,
    hmean.eventually (Metric.ball_mem_nhds 0 (half_pos hε)),
    hcomp.eventually (Metric.ball_mem_nhds 0 (half_pos hε))] with
    N _hN1 hSclose hCclose
  have hsplit :
      ∑ n ∈ range N, a n = ∑ n ∈ S N, a n + ∑ n ∈ range N \ S N, a n := by
    have hdisj : Disjoint (S N) (range N \ S N) := disjoint_sdiff
    have hunion : S N ∪ (range N \ S N) = range N :=
      union_sdiff_of_subset (hS N)
    rw [← sum_union hdisj, hunion]
  have hcompBd : ‖(∑ n ∈ range N \ S N, a n) / N‖ < ε / 2 := by
    have hcard : ((range N \ S N).card : ℝ) = (N : ℝ) - (S N).card := by
      have hle : (S N).card ≤ N :=
        (card_le_card (hS N)).trans_eq (by simp)
      rw [card_sdiff_of_subset (hS N), card_range, Nat.cast_sub hle]
    have hsum : ‖∑ n ∈ range N \ S N, a n‖ ≤ ((range N \ S N).card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∑ n ∈ range N \ S N, ‖a n‖ ≤ ∑ n ∈ range N \ S N, (1 : ℝ) :=
        sum_le_sum fun _ _ => ha _
      have hc : (∑ n ∈ range N \ S N, (1 : ℝ)) = (range N \ S N).card := by
        simp [sum_const]
      exact h1.trans_eq hc
    rw [norm_div]
    have hNn : ‖(N : ℂ)‖ = N := by simp
    rw [hNn]
    have hle : ‖∑ n ∈ range N \ S N, a n‖ / N ≤
        ((N : ℝ) - (S N).card) / N := by
      rw [← hcard]
      exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
    have hnn : 0 ≤ ((N : ℝ) - (S N).card) / N := by
      have hle' : (S N).card ≤ N :=
        (card_le_card (hS N)).trans_eq (by simp)
      exact div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hle')) (Nat.cast_nonneg N)
    have hlt : ((N : ℝ) - (S N).card) / N < ε / 2 := by
      have hdist : dist (((N : ℝ) - (S N).card) / N) 0 < ε / 2 := hCclose
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hdist
      exact hdist
    exact lt_of_le_of_lt hle hlt
  have hSbd : ‖(∑ n ∈ S N, a n) / N‖ < ε / 2 := by
    simpa [dist_zero_right] using hSclose
  have havg : ‖(∑ n ∈ range N, a n) / N‖ < ε := by
    rw [hsplit, add_div]
    have htri :=
      (norm_add_le ((∑ n ∈ S N, a n) / N)
        ((∑ n ∈ range N \ S N, a n) / N)).trans_lt (add_lt_add hSbd hcompBd)
    have : ε / 2 + ε / 2 = ε := add_halves ε
    rwa [this] at htri
  simpa [dist_zero_right] using havg

/-- Restricted averages `(∑_{S_N} a_n)/|S_N|` on a density-one family
still lift to the full Cesàro mean.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` index passage.
Contract: API
Audit: GREEN -/
theorem tendsto_cesaro_of_densityOne_avg (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (S : ℕ → Finset ℕ) (hS : ∀ N, S N ⊆ range N)
    (hden : Tendsto (fun N : ℕ => ((S N).card : ℝ) / N) atTop (𝓝 1))
    (hmean : Tendsto (fun N : ℕ =>
      (∑ n ∈ S N, a n) / (S N).card) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, a n) / N) atTop (𝓝 0) := by
  have hNmean : Tendsto (fun N : ℕ => (∑ n ∈ S N, a n) / N) atTop (𝓝 0) := by
    have heq :
        (fun N : ℕ => (∑ n ∈ S N, a n) / N) =ᶠ[atTop]
          fun N =>
            ((∑ n ∈ S N, a n) / (S N).card) * (((S N).card : ℂ) / N) := by
      filter_upwards [Filter.eventually_ge_atTop 1,
        (hden.eventually (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)))]
        with N hN1 hdenN
      have hNpos : 0 < N := Nat.succ_le_iff.mp hN1
      have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
      have hcardpos : 0 < (S N).card := by
        have habs : |((S N).card : ℝ) / N - 1| < 1 / 2 := by
          simpa [Real.dist_eq] using hdenN
        have hgt : (1 : ℝ) / 2 < ((S N).card : ℝ) / N := by
          have hle : 1 - ((S N).card : ℝ) / N ≤ |((S N).card : ℝ) / N - 1| := by
            rw [abs_sub_comm]
            exact le_abs_self _
          linarith
        have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
        exact Nat.cast_pos.mp ((div_pos_iff_of_pos_right hNposR).mp
          (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hgt))
      have hc0 : ((S N).card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hcardpos.ne'
      field_simp [hN0, hc0]
    have hcardC : Tendsto (fun N : ℕ => ((S N).card : ℂ) / N) atTop (𝓝 (1 : ℂ)) := by
      have hfun :
          (fun N : ℕ => ((S N).card : ℂ) / N) =
            fun N => Complex.ofReal (((S N).card : ℝ) / N) := by
        funext N
        calc
          ((S N).card : ℂ) / N
              = (((S N).card : ℝ) : ℂ) / ((N : ℝ) : ℂ) := by
                rw [Complex.ofReal_natCast, Complex.ofReal_natCast]
          _ = Complex.ofReal (((S N).card : ℝ) / N) :=
                (Complex.ofReal_div _ _).symm
      rw [hfun]
      have h1 : ((1 : ℝ) : ℂ) = (1 : ℂ) := Complex.ofReal_one
      exact h1 ▸ Filter.tendsto_ofReal_iff.mpr hden
    have hprod : Tendsto (fun N : ℕ =>
        ((∑ n ∈ S N, a n) / (S N).card) * (((S N).card : ℂ) / N)) atTop (𝓝 0) := by
      have hmul := hmean.mul hcardC
      simpa [zero_mul] using hmul
    exact Filter.Tendsto.congr' heq.symm hprod
  exact tendsto_cesaro_of_densityOne a ha S hS hden hNmean

/-! ### Sequence Weyl and the paper progression lemma -/

/-- Residue-class `SequenceWeyl` on every class modulo `k` implies
full `SequenceWeyl`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` interleaving.
Contract: API
Audit: GREEN -/
theorem sequenceWeyl_of_residueClasses {I : Type*} [Fintype I] [DecidableEq I]
    {k : ℕ} (hk : 0 < k) {θ : ℕ → I → ℝ}
    (hres : ∀ r < k, SequenceWeyl (fun m i => θ (k * m + r) i)) :
    SequenceWeyl θ := by
  intro t ht
  let a : ℕ → ℂ := fun n => e (∑ i : I, (t i : ℝ) * θ n i)
  have ha : ∀ n, ‖a n‖ ≤ 1 := fun n => (norm_e _).le
  have hr : ∀ r < k, Tendsto (fun M : ℕ =>
      (∑ m ∈ range M, a (k * m + r)) / M) atTop (𝓝 0) :=
    fun r hr => hres r hr t ht
  simpa [a] using tendsto_cesaro_of_residueClasses hk a ha hr

/-- Dyadic-block `SequenceWeyl` means imply full `SequenceWeyl`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` dyadic index passage.
Contract: API
Audit: GREEN -/
theorem sequenceWeyl_of_dyadicBlocks {I : Type*} [Fintype I] [DecidableEq I]
    {θ : ℕ → I → ℝ}
    (hdy : ∀ t : I → ℤ, (∃ i, t i ≠ 0) →
      Tendsto (fun M : ℕ =>
        (∑ n ∈ Ioc M (2 * M), e (∑ i : I, (t i : ℝ) * θ n i)) / M)
        atTop (𝓝 0)) :
    SequenceWeyl θ := by
  intro t ht
  exact tendsto_cesaro_of_dyadicBlocks _
    (fun _ => (norm_e _).le) (hdy t ht)

/-- Paper `lem:progression` with `q = 1`: integer covariance
`θ_(n+s) - C θ_n ∈ ℤ^I` and vanishing integer Fourier means imply
`SequenceWeyl` along every residue class. Lean residues are `0`-based
(`a < s`); the paper writes `1 ≤ a ≤ s`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` Lemma `lem:progression`;
`PeriodicKernel.commonClock_centeredLift`.
Contract: API
Audit: GREEN -/
theorem positiveProgression_sequenceWeyl {I : Type*} [Fintype I] [DecidableEq I]
    {C s : ℕ} {θ : ℕ → I → ℝ}
    (hC : 2 ≤ C) (hs : 0 < s)
    (hcov : IntegerShiftCov C s θ)
    (hW : SequenceWeyl θ)
    {a : ℕ} (ha : a < s) :
    SequenceWeyl (fun n i => θ (a + s * n) i) := by
  have hq : (0 : ℕ) < 1 := Nat.succ_pos 0
  have hdiv : (1 : ℤ) ∣ ((C : ℤ) - 1) := one_dvd _
  have hW1 : SequenceWeyl (fun n i => ((1 : ℕ) : ℝ) * θ n i) := by
    intro t ht
    have hfun :
        (fun N : ℕ =>
          (∑ n ∈ range N,
            e (∑ i : I, (t i : ℝ) * (((1 : ℕ) : ℝ) * θ n i))) / N) =
          fun N =>
            (∑ n ∈ range N, e (∑ i : I, (t i : ℝ) * θ n i)) / N := by
      funext N
      congr 1
      refine sum_congr rfl fun n _ => ?_
      congr 1
      refine sum_congr rfl fun i _ => ?_
      ring
    rw [hfun]
    exact hW t ht
  exact commonClock_centeredLift hC hs hq hdiv hcov hW1 ha

/-! ### Joint Weyl: dyadic blocks and clock-power interleaving -/

/-- Dyadic-block joint means imply `JointWeyl`. Complementary to the
`range N` definition; used for the paper’s `(M,2M]` index blocks.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:globalroot).
Contract: API
Audit: GREEN -/
theorem jointWeyl_of_dyadicBlocks {I : Type*} [Fintype I] [DecidableEq I]
    {b : I → ℕ} {θ : I → ℝ}
    (h : ∀ t : I → ℤ, (∃ i, t i ≠ 0) →
      Tendsto (fun M : ℕ =>
        (∑ n ∈ Ioc M (2 * M),
          e (∑ i : I, (t i : ℝ) * (b i : ℝ) ^ n * θ i)) / M)
        atTop (𝓝 0)) :
    JointWeyl b θ := by
  intro t ht
  exact tendsto_cesaro_of_dyadicBlocks _
    (fun _ => (norm_e _).le) (h t ht)

/-- Dyadic-block scalar Weyl means imply `weylCriterion`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` dyadic index passage.
Contract: API
Audit: GREEN -/
theorem weylCriterion_of_dyadicBlocks {B : ℕ} {θ : ℝ}
    (h : ∀ τ : ℤ, τ ≠ 0 →
      Tendsto (fun M : ℕ =>
        (∑ n ∈ Ioc M (2 * M), e ((τ : ℝ) * (B : ℝ) ^ n * θ)) / M)
        atTop (𝓝 0)) :
    weylCriterion B θ :=
  fun τ hτ => tendsto_cesaro_of_dyadicBlocks _
    (fun _ => (norm_e _).le) (h τ hτ)

/-- `JointWeyl` on `Unit` is `weylCriterion`. Inverse of
`jointWeyl_of_weylCriterion`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` Weyl packaging.
Contract: API
Audit: GREEN -/
theorem weylCriterion_of_jointWeyl {b : ℕ} {θ : ℝ}
    (h : JointWeyl (fun _ : Unit => b) (fun _ => θ)) :
    weylCriterion b θ := by
  intro τ hτ
  have ht : ∃ i : Unit, (fun _ : Unit => τ) i ≠ 0 := ⟨default, hτ⟩
  have hfun :
      (fun N : ℕ =>
        (∑ n ∈ range N, e ((τ : ℝ) * (b : ℝ) ^ n * θ)) / N) =
        fun N =>
          (∑ n ∈ range N,
            e (∑ i : Unit,
              ((fun _ : Unit => τ) i : ℝ) * (b : ℝ) ^ n * θ)) / N := by
    funext N
    congr 1
    refine sum_congr rfl fun n _ => ?_
    have hsum :
        ∑ i : Unit, ((fun _ : Unit => τ) i : ℝ) * (b : ℝ) ^ n * θ =
          (τ : ℝ) * (b : ℝ) ^ n * θ :=
      Fintype.sum_unique _
    rw [hsum]
  rw [hfun]
  exact h (fun _ => τ) ht

private theorem joint_pow_residue_phase {I : Type*} [Fintype I]
    (t : I → ℤ) (B k r m : ℕ) (θ : I → ℝ) :
    ∑ i, (t i : ℝ) * (B : ℝ) ^ (k * m + r) * θ i =
      ∑ i, ((t i * ((B ^ r : ℕ) : ℤ) : ℤ) : ℝ) *
        ((B ^ k : ℕ) : ℝ) ^ m * θ i := by
  refine sum_congr rfl fun i _ => ?_
  have hpow : (B : ℝ) ^ (k * m + r) = ((B : ℝ) ^ k) ^ m * (B : ℝ) ^ r := by
    rw [pow_add, pow_mul]
  have hk : ((B ^ k : ℕ) : ℝ) = (B : ℝ) ^ k := Nat.cast_pow B k
  have hr : ((B ^ r : ℕ) : ℝ) = (B : ℝ) ^ r := Nat.cast_pow B r
  have hτ : ((t i * ((B ^ r : ℕ) : ℤ) : ℤ) : ℝ) =
      (t i : ℝ) * (B ^ r : ℕ) := by
    rw [Int.cast_mul, Int.cast_natCast]
  rw [hpow, hk, hτ, hr]
  ring

/-- `JointWeyl` on the common clock `C = B^k` implies `JointWeyl` on
base `B`, by interleaving the `k` residue sequences
`B^r (B^k)^N θ`. Complementary block form of
`Components.weylCriterion_of_pow` (scalar packaging).

Source: `rounds/round104/13_gpt_paper_v0_3.tex` last paragraph of
rational coefficients.
Contract: API
Audit: GREEN -/
theorem jointWeyl_of_clockPow {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) {θ : I → ℝ}
    (h : JointWeyl (fun _ : I => B ^ k) θ) :
    JointWeyl (fun _ : I => B) θ := by
  intro t ht
  have hkpos : 0 < k := Nat.succ_le_iff.mp hk
  let a : ℕ → ℂ := fun n => e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * θ i)
  have ha : ∀ n, ‖a n‖ ≤ 1 := fun n => (norm_e _).le
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hB
  have hres : ∀ r < k, Tendsto (fun M : ℕ =>
      (∑ m ∈ range M, a (k * m + r)) / M) atTop (𝓝 0) := by
    intro r _hr
    have ht' : ∃ i, t i * ((B ^ r : ℕ) : ℤ) ≠ 0 := by
      obtain ⟨i, hi⟩ := ht
      exact ⟨i, mul_ne_zero hi (Int.natCast_ne_zero.mpr
        (pow_ne_zero r hBpos.ne'))⟩
    have hmode := h (fun i => t i * ((B ^ r : ℕ) : ℤ)) ht'
    refine Tendsto.congr (fun M => ?_) hmode
    congr 1
    refine sum_congr rfl fun m _ => congrArg e ?_
    exact (joint_pow_residue_phase t B k r m θ).symm
  simpa [a] using tendsto_cesaro_of_residueClasses hkpos a ha hres

/-- `JointWeyl` on clock `B^k` implies scalar `weylCriterion B`.
Does not duplicate `Components.weylCriterion_of_pow`: the hypothesis is
joint rather than scalar `B^k`-Weyl.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` rational coefficients
(interleaving).
Contract: API
Audit: GREEN -/
theorem weylCriterion_of_jointWeyl_clockPow {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) {θ : ℝ}
    (h : JointWeyl (fun _ : Unit => B ^ k) (fun _ => θ)) :
    weylCriterion B θ :=
  weylCriterion_of_jointWeyl (jointWeyl_of_clockPow hB hk h)

/-- Nonzero rational combinations of a `B^k`-jointly Weyl family are
Weyl-normal to base `B`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` rational coefficients;
`JointWeyl.weylCriterion_linearCombination` and residue interleaving.
Contract: API
Audit: GREEN -/
theorem weylCriterion_linearCombination_clockPow {I : Type*} [Fintype I]
    [DecidableEq I] {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) {θ : I → ℝ}
    {q : I → ℚ}
    (h : JointWeyl (fun _ : I => B ^ k) θ) (hq : ∃ i, q i ≠ 0) :
    weylCriterion B (∑ i, (q i : ℝ) * θ i) :=
  weylCriterion_linearCombination hB (jointWeyl_of_clockPow hB hk h) hq

end PrimeGapNormality.Prime
