import PrimeGapNormality.Prime.Config
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite deletion versus independent Bernoulli coupling

Root-Palm uses `q = 1/(p-1)`, not `1/p`. Finite deletion on `m`
candidates: categorical (at most one deletion) versus independent
Bernoulli-`q` deletions. No Janossy renormalisation, no primes, no PNT.

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (12)–(13);
`rounds/round97/01_gpt_khl_merger_independent_audit.md` (A13)–(A14);
`lean/PRIME_SIGNATURES.md` Coupling.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 400000

/-- Independent Bernoulli-`q` mass of one specific `k`-set among `m`
candidates.

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (12);
`lean/PRIME_SIGNATURES.md` Coupling.
Contract: API
Audit: GREEN -/
noncomputable def independentDeleteMass (m : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  q ^ k * (1 - q) ^ (m - k)

/-- Categorical (at most one) deletion mass of a `k`-set among `m`
candidates: empty mass `1 - m*q`, each singleton mass `q`, and zero on
`k ≥ 2`.

Source: `rounds/round97/01_gpt_khl_merger_independent_audit.md` (A13);
`lean/PRIME_SIGNATURES.md` Coupling.
Contract: API
Audit: GREEN -/
noncomputable def categoricalDeleteMass (m : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 - (m : ℝ) * q
  else if k = 1 then q
  else 0

/-- Independent Bernoulli thinning of a candidate set `A`: mass of a
subset `B` is `ρ^|B| * (1-ρ)^(|A|-|B|)` when `B ⊆ A`, else zero.

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (11), (22);
`lean/PRIME_SIGNATURES.md` Coupling.
Contract: API
Audit: GREEN -/
noncomputable def bernoulliThin (A : Finset ℕ) (ρ : ℝ)
    (_hρ0 : 0 ≤ ρ) (_hρ1 : ρ ≤ 1) (B : Finset ℕ) : ℝ :=
  if B ⊆ A then ρ ^ B.card * (1 - ρ) ^ (A.card - B.card) else 0

/-! ### Pointwise deletion masses -/

theorem independentDeleteMass_zero (m : ℕ) (q : ℝ) :
    independentDeleteMass m q 0 = (1 - q) ^ m := by
  simp [independentDeleteMass]

theorem independentDeleteMass_one (m : ℕ) (q : ℝ) :
    independentDeleteMass m q 1 = q * (1 - q) ^ (m - 1) := by
  simp [independentDeleteMass]

theorem independentDeleteMass_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (m k : ℕ) : 0 ≤ independentDeleteMass m q k :=
  mul_nonneg (pow_nonneg hq0 k) (pow_nonneg (sub_nonneg.mpr hq1) (m - k))

theorem categoricalDeleteMass_zero (m : ℕ) (q : ℝ) :
    categoricalDeleteMass m q 0 = 1 - (m : ℝ) * q :=
  rfl

theorem categoricalDeleteMass_one (m : ℕ) (q : ℝ) :
    categoricalDeleteMass m q 1 = q := by
  simp [categoricalDeleteMass]

theorem categoricalDeleteMass_of_two_le (m : ℕ) (q : ℝ) {k : ℕ}
    (hk : 2 ≤ k) : categoricalDeleteMass m q k = 0 := by
  unfold categoricalDeleteMass
  split_ifs with h0 h1
  · omega
  · omega
  · rfl

/-- Binomial theorem: the independent deletion masses sum to one.

Source: `lean/PRIME_MATHLIB.md` binomials.
Contract: API
Audit: GREEN -/
theorem independentDeleteMass_weighted_sum (m : ℕ) (q : ℝ) :
    ∑ k ∈ range (m + 1), (m.choose k : ℝ) * independentDeleteMass m q k = 1 := by
  simp only [independentDeleteMass]
  have hsum :
      ∑ k ∈ range (m + 1), (m.choose k : ℝ) * (q ^ k * (1 - q) ^ (m - k))
        = ∑ k ∈ range (m + 1), q ^ k * (1 - q) ^ (m - k) * (m.choose k : ℝ) := by
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [hsum]
  have hbin := add_pow (R := ℝ) q (1 - q) m
  have hcast :
      ∑ k ∈ range (m + 1), q ^ k * (1 - q) ^ (m - k) * (m.choose k : ℝ)
        = ∑ k ∈ range (m + 1), q ^ k * (1 - q) ^ (m - k) * (m.choose k) := by
    refine sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  rw [hcast, ← hbin, add_sub_cancel, one_pow]

/-! ### Bernoulli: `1 - (1-q)^n ≤ n q` -/

theorem one_sub_pow_le {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    1 - (1 - q) ^ n ≤ (n : ℝ) * q := by
  have hB : 1 + (n : ℝ) * (-q) ≤ (1 - q) ^ n := by
    simpa [sub_eq_add_neg] using
      one_add_mul_le_pow (a := -q) (by linarith : (-2 : ℝ) ≤ -q) n
  have hring : 1 + (n : ℝ) * (-q) = 1 - (n : ℝ) * q := by ring
  have hB' : 1 - (n : ℝ) * q ≤ (1 - q) ^ n := by rwa [hring] at hB
  linarith

/-! ### Exact TV identity (R97 (A13)) -/

theorem mem_two_of_mem_sdiff_zero_one {m k : ℕ}
    (hk : k ∈ range (m + 1) \ {0, 1}) : 2 ≤ k := by
  simp only [mem_sdiff, mem_insert, mem_singleton, mem_range] at hk
  omega

theorem pair_zero_one_subset_range {m : ℕ} (hm : 0 < m) :
    ({0, 1} : Finset ℕ) ⊆ range (m + 1) := by
  intro x hx
  simp only [mem_insert, mem_singleton, mem_range] at hx ⊢
  rcases hx with rfl | rfl
  · exact Nat.succ_pos m
  · exact Nat.succ_lt_succ hm

/-- Half-TV between categorical and independent deletion, summed over
cardinality with binomial multiplicity.

Source: `rounds/round96/01_gpt_standard_hl_gap_merger_certificate.py`
`categorical_vs_bernoulli`; R97 (A13).
Contract: API
Audit: GREEN -/
noncomputable def categoricalVsIndependentTV (m : ℕ) (q : ℝ) : ℝ :=
  (∑ k ∈ range (m + 1),
      (m.choose k : ℝ) *
        |categoricalDeleteMass m q k - independentDeleteMass m q k|) / 2

theorem categoricalVsIndependentTV_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (m : ℕ) :
    categoricalVsIndependentTV m q
      = (m : ℝ) * q * (1 - (1 - q) ^ (m - 1)) := by
  unfold categoricalVsIndependentTV
  cases m with
  | zero =>
    simp [categoricalDeleteMass, independentDeleteMass, range_one, sum_singleton]
  | succ n =>
    set m := n + 1
    have hm : 0 < m := Nat.succ_pos n
    have h01 := pair_zero_one_subset_range hm
    have hind := independentDeleteMass_weighted_sum m q
    have hnon : ∀ k : ℕ, 0 ≤ independentDeleteMass m q k :=
      fun k => independentDeleteMass_nonneg hq0 hq1 m k
    have hqle : 0 ≤ 1 - q := sub_nonneg.mpr hq1
    have hpowle : (1 - q) ^ (m - 1) ≤ 1 :=
      pow_le_one₀ hqle (sub_le_self (1 : ℝ) hq0)
    have hind0 : independentDeleteMass m q 0 = (1 - q) ^ m := independentDeleteMass_zero m q
    have hind1 : independentDeleteMass m q 1 = q * (1 - q) ^ (m - 1) :=
      independentDeleteMass_one m q
    have hcat0 : categoricalDeleteMass m q 0 = 1 - (m : ℝ) * q := rfl
    have hcat1 : categoricalDeleteMass m q 1 = q := categoricalDeleteMass_one m q
    have hB0 : 1 - (m : ℝ) * q ≤ (1 - q) ^ m := by
      have hPow : 1 + (m : ℝ) * (-q) ≤ (1 - q) ^ m := by
        simpa [sub_eq_add_neg] using
          one_add_mul_le_pow (a := -q) (by linarith : (-2 : ℝ) ≤ -q) m
      have hring : 1 + (m : ℝ) * (-q) = 1 - (m : ℝ) * q := by ring
      rwa [hring] at hPow
    have habs0 :
        |categoricalDeleteMass m q 0 - independentDeleteMass m q 0|
          = (1 - q) ^ m - (1 - (m : ℝ) * q) := by
      rw [hcat0, hind0, abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hB0)
    have habs1 :
        |categoricalDeleteMass m q 1 - independentDeleteMass m q 1|
          = q * (1 - (1 - q) ^ (m - 1)) := by
      rw [hcat1, hind1]
      have : q * (1 - q) ^ (m - 1) ≤ q := by
        have := mul_le_mul_of_nonneg_left hpowle hq0
        simpa using this
      have hdiff : 0 ≤ q - q * (1 - q) ^ (m - 1) := sub_nonneg.mpr this
      rw [abs_of_nonneg hdiff]
      ring
    let f : ℕ → ℝ := fun k =>
      (m.choose k : ℝ) * |categoricalDeleteMass m q k - independentDeleteMass m q k|
    have htail :
        ∀ k ∈ range (m + 1) \ {0, 1},
          f k = (m.choose k : ℝ) * independentDeleteMass m q k := by
      intro k hk
      have hk2 : 2 ≤ k := mem_two_of_mem_sdiff_zero_one hk
      simp only [f]
      rw [categoricalDeleteMass_of_two_le m q hk2, zero_sub, abs_neg,
        abs_of_nonneg (hnon k)]
    have hsumf :
        ∑ k ∈ range (m + 1), f k
          = f 0 + f 1 + ∑ k ∈ range (m + 1) \ {0, 1}, f k := by
      rw [← sum_sdiff h01, sum_pair (by decide : (0 : ℕ) ≠ 1)]
      ring
    have hsumind :
        ∑ k ∈ range (m + 1) \ {0, 1},
            (m.choose k : ℝ) * independentDeleteMass m q k
          = 1 - (1 - q) ^ m - (m : ℝ) * q * (1 - q) ^ (m - 1) := by
      have hpair :
          ∑ k ∈ ({0, 1} : Finset ℕ),
              (m.choose k : ℝ) * independentDeleteMass m q k
            = (1 - q) ^ m + (m : ℝ) * q * (1 - q) ^ (m - 1) := by
        rw [sum_pair (by decide : (0 : ℕ) ≠ 1), Nat.choose_zero_right,
          Nat.choose_one_right, hind0, hind1]
        simp
        ring
      have hsplit :=
        (sum_sdiff h01 :
          ∑ k ∈ range (m + 1) \ {0, 1},
              (m.choose k : ℝ) * independentDeleteMass m q k
            + ∑ k ∈ ({0, 1} : Finset ℕ),
              (m.choose k : ℝ) * independentDeleteMass m q k
            = ∑ k ∈ range (m + 1),
              (m.choose k : ℝ) * independentDeleteMass m q k)
      linarith
    have hf0 : f 0 = (1 - q) ^ m - (1 - (m : ℝ) * q) := by
      change (m.choose 0 : ℝ) *
          |categoricalDeleteMass m q 0 - independentDeleteMass m q 0| = _
      simp [Nat.choose_zero_right, habs0]
    have hf1 : f 1 = (m : ℝ) * q * (1 - (1 - q) ^ (m - 1)) := by
      change (m.choose 1 : ℝ) *
          |categoricalDeleteMass m q 1 - independentDeleteMass m q 1| = _
      simp [Nat.choose_one_right, habs1]
      ring
    have hftail :
        ∑ k ∈ range (m + 1) \ {0, 1}, f k
          = 1 - (1 - q) ^ m - (m : ℝ) * q * (1 - q) ^ (m - 1) := by
      rw [sum_congr rfl htail]
      exact hsumind
    have hL1 : ∑ k ∈ range (m + 1), f k
        = 2 * ((m : ℝ) * q * (1 - (1 - q) ^ (m - 1))) := by
      rw [hsumf, hf0, hf1, hftail]
      ring
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    rw [div_eq_iff h2, hL1]
    ring

/-- Exact finite TV between categorical and independent deletion.

Source: `rounds/round97/01_gpt_khl_merger_independent_audit.md` (A13);
certificate `categorical_vs_bernoulli`.
Contract: API
Audit: GREEN -/
theorem categorical_tv_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ)
    (_hm : (m : ℝ) * q ≤ 1) :
    (∑ k ∈ range (m + 1),
        (m.choose k : ℝ) *
          |categoricalDeleteMass m q k - independentDeleteMass m q k|) / 2
      = (m : ℝ) * q * (1 - (1 - q) ^ (m - 1)) :=
  categoricalVsIndependentTV_eq hq0 hq1 m

/-- Quadratic TV bound. For `m = 0` the right-hand side is zero by
`ℕ`-subtraction.

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (12);
`rounds/round97/01_gpt_khl_merger_independent_audit.md` (A13).
Contract: API
Audit: GREEN -/
theorem categorical_tv_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    (∑ k ∈ range (m + 1),
        (m.choose k : ℝ) *
          |categoricalDeleteMass m q k - independentDeleteMass m q k|) / 2
      ≤ (m : ℝ) * (m - 1 : ℕ) * q ^ 2 := by
  have heq := categoricalVsIndependentTV_eq hq0 hq1 m
  unfold categoricalVsIndependentTV at heq
  rw [heq]
  have hpow := one_sub_pow_le hq0 hq1 (m - 1)
  have hmq : 0 ≤ (m : ℝ) * q := mul_nonneg (Nat.cast_nonneg m) hq0
  have hbound :
      (m : ℝ) * q * (1 - (1 - q) ^ (m - 1))
        ≤ (m : ℝ) * q * ((m - 1 : ℕ) * q) :=
    mul_le_mul_of_nonneg_left hpow hmq
  have hring :
      (m : ℝ) * q * ((m - 1 : ℕ) * q) = (m : ℝ) * (m - 1 : ℕ) * q ^ 2 := by
    ring
  exact hbound.trans (le_of_eq hring)

/-! ### Bernoulli thinning -/

theorem bernoulliThin_eq (A : Finset ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {B : Finset ℕ} (hBA : B ⊆ A) :
    bernoulliThin A ρ hρ0 hρ1 B = ρ ^ B.card * (1 - ρ) ^ (A.card - B.card) :=
  if_pos hBA

theorem bernoulliThin_eq_zero (A : Finset ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {B : Finset ℕ} (hBA : ¬ B ⊆ A) :
    bernoulliThin A ρ hρ0 hρ1 B = 0 :=
  if_neg hBA

theorem bernoulliThin_nonneg (A : Finset ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (B : Finset ℕ) : 0 ≤ bernoulliThin A ρ hρ0 hρ1 B := by
  unfold bernoulliThin
  split_ifs
  · exact mul_nonneg (pow_nonneg hρ0 _) (pow_nonneg (sub_nonneg.mpr hρ1) _)
  · exact le_rfl

/-- Thinning masses on the powerset of `A` sum to one.

Source: `lean/PRIME_MATHLIB.md` products of masses.
Contract: API
Audit: GREEN -/
theorem bernoulliThin_sum (A : Finset ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∑ B ∈ A.powerset, bernoulliThin A ρ hρ0 hρ1 B = 1 := by
  have hprod := prod_add (fun _ : ℕ => ρ) (fun _ => 1 - ρ) A
  have h1 : ∏ _i ∈ A, (ρ + (1 - ρ)) = (1 : ℝ) := by
    have hρ : ∀ i ∈ A, ρ + (1 - ρ) = (1 : ℝ) := fun _ _ => by ring
    rw [prod_congr rfl hρ]
    exact prod_const_one
  rw [h1] at hprod
  rw [hprod]
  refine sum_congr rfl fun B hB => ?_
  have hBA : B ⊆ A := mem_powerset.mp hB
  rw [bernoulliThin_eq A hρ0 hρ1 hBA, prod_const, prod_const,
    card_sdiff_of_subset hBA]

/-! ### Product coupling -/

theorem tvHalf_nonneg {ι : Type*} (s : Finset ι) (μ ν : ι → ℝ) : 0 ≤ tvHalf s μ ν :=
  div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

/-- Two-factor product coupling: TV of a product of independent discrete
masses is at most the sum of the coordinate TVs.

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` (13);
`rounds/round97/01_gpt_khl_merger_independent_audit.md` (A14);
`lean/PRIME_MATHLIB.md` missing (5).
Contract: API
Audit: GREEN -/
theorem tvHalf_mul_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ μ' : α → ℝ) (ν ν' : β → ℝ)
    (hν0 : ∀ b ∈ t, 0 ≤ ν b) (hμ'0 : ∀ a ∈ s, 0 ≤ μ' a)
    (hν1 : ∑ b ∈ t, ν b = 1) (hμ'1 : ∑ a ∈ s, μ' a = 1) :
    tvHalf (s ×ˢ t) (fun p => μ p.1 * ν p.2) (fun p => μ' p.1 * ν' p.2)
      ≤ tvHalf s μ μ' + tvHalf t ν ν' := by
  unfold tvHalf
  rw [sum_product]
  have hsplit : ∀ a ∈ s, ∀ b ∈ t,
      |μ a * ν b - μ' a * ν' b|
        ≤ |μ a - μ' a| * ν b + μ' a * |ν b - ν' b| := by
    intro a ha b hb
    have hb0 := hν0 b hb
    have ha0 := hμ'0 a ha
    have hrew : μ a * ν b - μ' a * ν' b
        = (μ a - μ' a) * ν b + μ' a * (ν b - ν' b) := by ring
    rw [hrew]
    calc
      |(μ a - μ' a) * ν b + μ' a * (ν b - ν' b)|
          ≤ |(μ a - μ' a) * ν b| + |μ' a * (ν b - ν' b)| := abs_add_le _ _
      _ = |μ a - μ' a| * |ν b| + |μ' a| * |ν b - ν' b| := by
            rw [abs_mul, abs_mul]
      _ = |μ a - μ' a| * ν b + μ' a * |ν b - ν' b| := by
            rw [abs_of_nonneg hb0, abs_of_nonneg ha0]
  have hsum :
      ∑ a ∈ s, ∑ b ∈ t, |μ a * ν b - μ' a * ν' b|
        ≤ ∑ a ∈ s, ∑ b ∈ t,
            (|μ a - μ' a| * ν b + μ' a * |ν b - ν' b|) := by
    refine sum_le_sum fun a ha => sum_le_sum fun b hb => hsplit a ha b hb
  have hsimp :
      ∑ a ∈ s, ∑ b ∈ t, (|μ a - μ' a| * ν b + μ' a * |ν b - ν' b|)
        = ∑ a ∈ s, |μ a - μ' a| + ∑ b ∈ t, |ν b - ν' b| := by
    simp only [sum_add_distrib]
    have h1 :
        ∑ a ∈ s, ∑ b ∈ t, |μ a - μ' a| * ν b = ∑ a ∈ s, |μ a - μ' a| := by
      simp only [← mul_sum]
      simp [hν1]
    have h2 :
        ∑ a ∈ s, ∑ b ∈ t, μ' a * |ν b - ν' b|
          = ∑ b ∈ t, |ν b - ν' b| := by
      have hswap :
          ∑ a ∈ s, ∑ b ∈ t, μ' a * |ν b - ν' b|
            = ∑ a ∈ s, μ' a * ∑ b ∈ t, |ν b - ν' b| := by
        refine sum_congr rfl fun a ha => ?_
        rw [← Finset.mul_sum]
      rw [hswap, ← Finset.sum_mul, hμ'1, one_mul]
    rw [h1, h2]
  have hden : (0 : ℝ) ≤ 2 := by norm_num
  have hmain := div_le_div_of_nonneg_right hsum hden
  calc
    (∑ a ∈ s, ∑ b ∈ t, |μ a * ν b - μ' a * ν' b|) / 2
        ≤ (∑ a ∈ s, ∑ b ∈ t,
            (|μ a - μ' a| * ν b + μ' a * |ν b - ν' b|)) / 2 := hmain
    _ = (∑ a ∈ s, |μ a - μ' a| + ∑ b ∈ t, |ν b - ν' b|) / 2 := by rw [hsimp]
    _ = (∑ a ∈ s, |μ a - μ' a|) / 2 + (∑ b ∈ t, |ν b - ν' b|) / 2 := by ring

/-- Sum of per-coordinate deletion TVs over a Finset of independent
deletions, bounded by the paper's quadratic budget (A14).

Source: `rounds/round97/01_gpt_khl_merger_independent_audit.md` (A14).
Contract: API
Audit: GREEN -/
theorem sum_categorical_tv_le {ι : Type*} (s : Finset ι) (m : ℕ)
    {q : ι → ℝ} (hq0 : ∀ i ∈ s, 0 ≤ q i) (hq1 : ∀ i ∈ s, q i ≤ 1) :
    ∑ i ∈ s, categoricalVsIndependentTV m (q i)
      ≤ ∑ i ∈ s, (m : ℝ) * (m - 1 : ℕ) * q i ^ 2 := by
  refine sum_le_sum fun i hi => ?_
  simpa [categoricalVsIndependentTV] using categorical_tv_le (hq0 i hi) (hq1 i hi) m

end PrimeGapNormality.Prime
