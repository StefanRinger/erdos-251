import PrimeGapNormality.Prime.EndAPI
import PrimeGapNormality.Prime.PrimeSeries
import PrimeGapNormality.Prime.TailMass
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Condition T for primes (paper v0.3 after `lem:tailmass`)

Paper: `Avg_{n ∈ I_X} T_ρ(n+L) ≤ F_ρ(v+L+1) / m_X ≪_ρ G`, with
`I_X = {n : X < p_n ≤ 2X}`, `m_X = |I_X|`, `v` last index, `L = O(log G)`,
`G = log X`.

This module compiles the T-ready comparison for genuine primes, not S
and not normality.

1. Polynomial mass: `nthPrime_le_succ_sq` and geometric sums give
   `F_ρ(N) = O_ρ(N^2)`.
2. If `I_X ⊆ {u,…,v}` and `m_X > 0`, the average of
   `gapTail ρ primeGap (n+L)` is `≤ F_ρ(v+L+1) / m_X`.
3. Bertrand gives `m_X ≥ 1` for `X > 0`. Mathlib Chebyshev supplies
   `π(x) ≪ x / log x` and `π(x) ≫ x / log x` separately, but the leading
   constants `log 4 = 2 log 2` cancel on a dyadic interval, so they do
   **not** prove `m_X ≫ X / log X`. Closing `≪_ρ G` still needs that
   PNT density (and the paper's `p_n ≪ n log n` in place of `N^2`).

Source: `rounds/round104/13_gpt_paper_v0_3.tex` after `lem:tailmass`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 800000

private theorem rho_pos {ρ : ℝ} (hρ : 1 < ρ) : 0 < ρ :=
  lt_trans (by norm_num) hρ

private theorem rho_ne_zero {ρ : ℝ} (hρ : 1 < ρ) : ρ ≠ 0 :=
  (rho_pos hρ).ne'

private theorem rho_sub_one_pos {ρ : ℝ} (hρ : 1 < ρ) : 0 < ρ - 1 :=
  sub_pos.mpr hρ

private theorem rho_sub_one_ne_zero {ρ : ℝ} (hρ : 1 < ρ) : ρ - 1 ≠ 0 :=
  (rho_sub_one_pos hρ).ne'

private theorem inv_rho_nonneg {ρ : ℝ} (hρ : 1 < ρ) : 0 ≤ ρ⁻¹ :=
  inv_nonneg.mpr (rho_pos hρ).le

private theorem inv_rho_lt_one {ρ : ℝ} (hρ : 1 < ρ) : ρ⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ hρ

private theorem inv_rho_norm_lt_one {ρ : ℝ} (hρ : 1 < ρ) : ‖ρ⁻¹‖ < 1 := by
  rw [norm_inv, Real.norm_eq_abs, abs_of_pos (rho_pos hρ)]
  exact inv_rho_lt_one hρ

private theorem add_sq_le_two_mul_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  have hdiff : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring
  have hsum : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
  rw [hdiff] at h
  rw [hsum]
  linarith

private theorem two_mul_choose_two (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    have hdiv : 2 ∣ (n + 1) * n := by
      simpa [Nat.mul_comm] using Nat.two_dvd_mul_add_one n
    rw [Nat.choose_two_right, Nat.succ_sub_one, Nat.mul_div_cancel' hdiv]

private theorem nat_sq_le_choose_two (j : ℕ) :
    (j : ℝ) ^ 2 ≤ 2 * ((j + 2).choose 2 : ℝ) := by
  have hN : j * j ≤ (j + 2) * (j + 1) := by
    have heq : (j + 2) * (j + 1) = j * j + 3 * j + 2 := by ring
    rw [heq]
    exact Nat.le_add_right (j * j) (3 * j + 2)
  have hch : 2 * (j + 2).choose 2 = (j + 2) * (j + 1) := by
    simpa using two_mul_choose_two (j + 2)
  calc
    (j : ℝ) ^ 2 = ((j * j : ℕ) : ℝ) := by simp [sq, Nat.cast_mul]
    _ ≤ (((j + 2) * (j + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hN
    _ = ((2 * (j + 2).choose 2 : ℕ) : ℝ) := by rw [← hch]
    _ = 2 * ((j + 2).choose 2 : ℝ) := by simp [Nat.cast_mul]

private theorem div_pow_succ {ρ : ℝ} (hρ : 1 < ρ) (A : ℝ) (j : ℕ) :
    A / ρ ^ (j + 1) = (A / ρ) * ρ⁻¹ ^ j := by
  have h0 := rho_ne_zero hρ
  rw [pow_succ, div_mul_eq_div_div, div_eq_mul_inv, inv_pow]
  field_simp [h0]

private theorem one_sub_inv_rho {ρ : ℝ} (hρ : 1 < ρ) :
    (1 : ℝ) - ρ⁻¹ = (ρ - 1) / ρ := by
  have h0 := rho_ne_zero hρ
  rw [inv_eq_one_div]
  field_simp [h0]

private theorem tsum_geometric_inv_rho {ρ : ℝ} (hρ : 1 < ρ) :
    ∑' j : ℕ, ρ⁻¹ ^ j = ρ / (ρ - 1) := by
  have hsum := tsum_geometric_of_lt_one (inv_rho_nonneg hρ) (inv_rho_lt_one hρ)
  rw [hsum, one_sub_inv_rho hρ, inv_div]

private theorem tsum_sq_geometric_le {ρ : ℝ} (hρ : 1 < ρ) :
    ∑' j : ℕ, (j : ℝ) ^ 2 * ρ⁻¹ ^ j ≤ 2 * (ρ / (ρ - 1)) ^ 3 := by
  have hr := inv_rho_norm_lt_one hρ
  have hr0 := inv_rho_nonneg hρ
  have hch := tsum_choose_mul_geometric_of_norm_lt_one (k := 2) (r := ρ⁻¹) hr
  have hf : Summable fun j : ℕ => (j : ℝ) ^ 2 * ρ⁻¹ ^ j :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  have hg : Summable fun j : ℕ =>
      (2 : ℝ) * (((j + 2).choose 2 : ℝ) * ρ⁻¹ ^ j) :=
    (summable_choose_mul_geometric_of_norm_lt_one (k := 2) (r := ρ⁻¹) hr).mul_left 2
  have hterm : ∀ j : ℕ,
      (j : ℝ) ^ 2 * ρ⁻¹ ^ j ≤
        (2 : ℝ) * (((j + 2).choose 2 : ℝ) * ρ⁻¹ ^ j) := fun j => by
    have := mul_le_mul_of_nonneg_right (nat_sq_le_choose_two j) (pow_nonneg hr0 j)
    simpa [mul_assoc] using this
  have hle := hf.tsum_le_tsum hterm hg
  have htsum :
      ∑' j : ℕ, (2 : ℝ) * (((j + 2).choose 2 : ℝ) * ρ⁻¹ ^ j) =
        2 * (ρ / (ρ - 1)) ^ 3 := by
    rw [tsum_mul_left, hch]
    have hinv : 1 / (1 - ρ⁻¹) ^ (2 + 1) = (ρ / (ρ - 1)) ^ 3 := by
      rw [one_sub_inv_rho hρ, show (2 : ℕ) + 1 = 3 from rfl, div_pow, one_div,
        inv_div, div_pow]
    rw [hinv]
  exact hle.trans (le_of_eq htsum)

/-- Explicit `O_ρ(1)` factor in `F_ρ(N) ≤ C(ρ) (N+1)^2`. -/
noncomputable def posMassPolyCoeff (ρ : ℝ) : ℝ :=
  144 * (2 / (ρ - 1) + 4 * ρ ^ 2 / (ρ - 1) ^ 3)

theorem posMassPolyCoeff_nonneg {ρ : ℝ} (hρ : 1 < ρ) : 0 ≤ posMassPolyCoeff ρ := by
  have hpos := rho_sub_one_pos hρ
  unfold posMassPolyCoeff
  positivity

private theorem one_le_succ_sq (N : ℕ) : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N))
  exact one_le_pow₀ h1

private theorem nthPrime_div_pow_le_poly {ρ : ℝ} (hρ : 1 < ρ) (N j : ℕ) :
    (nthPrime (N + j) : ℝ) / ρ ^ (j + 1) ≤
      (144 / ρ) *
        ((2 * ((N + 1 : ℕ) : ℝ) ^ 2 + 2 * (j : ℝ) ^ 2) * ρ⁻¹ ^ j) := by
  have hbound : (nthPrime (N + j) : ℝ) ≤ 144 * ((N + j + 1 : ℕ) : ℝ) ^ 2 := by
    have := nthPrime_le_succ_sq (N + j)
    have hcast :
        ((144 * (N + j + 1) ^ 2 : ℕ) : ℝ) =
          144 * ((N + j + 1 : ℕ) : ℝ) ^ 2 := by
      simp [Nat.cast_mul, Nat.cast_pow]
    exact (Nat.cast_le.mpr this).trans_eq hcast
  have hidx : ((N + j + 1 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) + (j : ℝ) := by
    simp [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
  have hsqb :
      ((N + j + 1 : ℕ) : ℝ) ^ 2 ≤
        2 * ((N + 1 : ℕ) : ℝ) ^ 2 + 2 * (j : ℝ) ^ 2 := by
    rw [hidx]
    exact add_sq_le_two_mul_sq _ _
  have hnum :
      144 * ((N + j + 1 : ℕ) : ℝ) ^ 2 ≤
        144 * (2 * ((N + 1 : ℕ) : ℝ) ^ 2 + 2 * (j : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hsqb (by norm_num : (0 : ℝ) ≤ 144)
  have hle :=
    div_le_div_of_nonneg_right (hbound.trans hnum)
      (pow_nonneg (rho_pos hρ).le (j + 1))
  have hrew :
      144 * (2 * ((N + 1 : ℕ) : ℝ) ^ 2 + 2 * (j : ℝ) ^ 2) / ρ ^ (j + 1) =
        (144 / ρ) *
          ((2 * ((N + 1 : ℕ) : ℝ) ^ 2 + 2 * (j : ℝ) ^ 2) * ρ⁻¹ ^ j) := by
    rw [div_pow_succ hρ]
    ring
  exact hle.trans_eq hrew

/-- Polynomial Chebyshev inversion plus geometric moments:
`F_ρ(N) = O_ρ(N^2)`. Paper uses `p_n ≪ n log(2n)` for `O_ρ(N log N)`. -/
theorem posMass_nthPrime_le {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) :
    posMass ρ (fun k => (nthPrime k : ℝ)) N ≤
      posMassPolyCoeff ρ * ((N + 1 : ℕ) : ℝ) ^ 2 := by
  set r : ℝ := ρ⁻¹
  have hr0 : 0 ≤ r := inv_rho_nonneg hρ
  have hr : ‖r‖ < 1 := inv_rho_norm_lt_one hρ
  have hgeo : Summable fun j : ℕ => r ^ j :=
    summable_geometric_of_lt_one hr0 (inv_rho_lt_one hρ)
  have hsq : Summable fun j : ℕ => (j : ℝ) ^ 2 * r ^ j :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  set sN : ℝ := ((N + 1 : ℕ) : ℝ)
  have hdom :
      Summable fun j : ℕ =>
        (144 / ρ) * ((2 * sN ^ 2 + 2 * (j : ℝ) ^ 2) * r ^ j) := by
    have hconst : Summable fun j : ℕ => (2 * sN ^ 2 : ℝ) * r ^ j :=
      hgeo.mul_left (2 * sN ^ 2)
    have hsq' : Summable fun j : ℕ => (2 : ℝ) * ((j : ℝ) ^ 2 * r ^ j) :=
      hsq.mul_left 2
    have hfun :
        (fun j : ℕ => (2 * sN ^ 2 + 2 * (j : ℝ) ^ 2) * r ^ j) =
          fun j : ℕ => (2 * sN ^ 2) * r ^ j + 2 * ((j : ℝ) ^ 2 * r ^ j) := by
      funext j
      ring
    have hadd : Summable fun j : ℕ =>
        (2 * sN ^ 2 + 2 * (j : ℝ) ^ 2) * r ^ j := by
      simpa [hfun] using hconst.add hsq'
    exact hadd.mul_left (144 / ρ)
  have hterm : ∀ j : ℕ,
      (nthPrime (N + j) : ℝ) / ρ ^ (j + 1) ≤
        (144 / ρ) * ((2 * sN ^ 2 + 2 * (j : ℝ) ^ 2) * r ^ j) := by
    intro j
    simpa [sN, r] using nthPrime_div_pow_le_poly hρ N j
  have hf : Summable fun j : ℕ =>
      (nthPrime (N + j) : ℝ) / ρ ^ (j + 1) :=
    Summable.of_nonneg_of_le
      (fun j => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (rho_pos hρ).le (j + 1)))
      hterm hdom
  have hle := hf.tsum_le_tsum hterm hdom
  have htsum :
      ∑' j : ℕ, (144 / ρ) * ((2 * sN ^ 2 + 2 * (j : ℝ) ^ 2) * r ^ j) =
        (144 / ρ) *
          (2 * sN ^ 2 * ∑' j : ℕ, r ^ j + 2 * ∑' j : ℕ, (j : ℝ) ^ 2 * r ^ j) := by
    have hfun :
        (fun j : ℕ => (144 / ρ) * ((2 * sN ^ 2 + 2 * (j : ℝ) ^ 2) * r ^ j)) =
          fun j : ℕ =>
            (144 / ρ) *
              ((2 * sN ^ 2) * r ^ j + 2 * ((j : ℝ) ^ 2 * r ^ j)) := by
      funext j
      ring
    rw [hfun, tsum_mul_left]
    rw [Summable.tsum_add (hgeo.mul_left (2 * sN ^ 2)) (hsq.mul_left 2),
      tsum_mul_left, tsum_mul_left]
  have hgeo_eq : ∑' j : ℕ, r ^ j = ρ / (ρ - 1) := by
    simpa [r] using tsum_geometric_inv_rho hρ
  have hsq_le : ∑' j : ℕ, (j : ℝ) ^ 2 * r ^ j ≤ 2 * (ρ / (ρ - 1)) ^ 3 := by
    simpa [r] using tsum_sq_geometric_le hρ
  have hmass : posMass ρ (fun k => (nthPrime k : ℝ)) N ≤
      (144 / ρ) *
        (2 * sN ^ 2 * (ρ / (ρ - 1)) + 2 * (2 * (ρ / (ρ - 1)) ^ 3)) := by
    refine hle.trans ?_
    rw [htsum, hgeo_eq]
    refine mul_le_mul_of_nonneg_left ?_
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 144) (rho_pos hρ).le)
    exact add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left hsq_le (by positivity : (0 : ℝ) ≤ 2))
  have hsimp :
      (144 / ρ) *
          (2 * sN ^ 2 * (ρ / (ρ - 1)) + 2 * (2 * (ρ / (ρ - 1)) ^ 3)) =
        144 * (2 * sN ^ 2 / (ρ - 1) + 4 * ρ ^ 2 / (ρ - 1) ^ 3) := by
    have hρ0 := rho_ne_zero hρ
    have hd := rho_sub_one_ne_zero hρ
    have hpow : (ρ / (ρ - 1)) ^ 3 = ρ ^ 3 / (ρ - 1) ^ 3 := by
      rw [div_pow]
    rw [hpow]
    field_simp [hρ0, hd]
    ring
  have hC :
      144 * (2 * sN ^ 2 / (ρ - 1) + 4 * ρ ^ 2 / (ρ - 1) ^ 3) ≤
        posMassPolyCoeff ρ * sN ^ 2 := by
    unfold posMassPolyCoeff
    have h1 := one_le_succ_sq N
    have hsec : 4 * ρ ^ 2 / (ρ - 1) ^ 3 ≤
        (4 * ρ ^ 2 / (ρ - 1) ^ 3) * sN ^ 2 :=
      le_mul_of_one_le_right (by positivity) h1
    have hinner :
        2 * sN ^ 2 / (ρ - 1) + 4 * ρ ^ 2 / (ρ - 1) ^ 3 ≤
          (2 / (ρ - 1) + 4 * ρ ^ 2 / (ρ - 1) ^ 3) * sN ^ 2 := by
      have hL : 2 * sN ^ 2 / (ρ - 1) = 2 / (ρ - 1) * sN ^ 2 := by ring
      rw [hL, add_mul]
      exact add_le_add (le_refl _) hsec
    have hassoc :
        144 * ((2 / (ρ - 1) + 4 * ρ ^ 2 / (ρ - 1) ^ 3) * sN ^ 2) =
          (144 * (2 / (ρ - 1) + 4 * ρ ^ 2 / (ρ - 1) ^ 3)) * sN ^ 2 := by
      ring
    exact (mul_le_mul_of_nonneg_left hinner (by norm_num : (0 : ℝ) ≤ 144)).trans_eq
      hassoc
  exact hmass.trans (hsimp.trans_le hC)

/-! ### Index block `I_X` -/

/-- Paper `I_X = {n : X < p_n ≤ 2X}`. Lean `nthPrime 0 = 2` is paper `p_1`. -/
noncomputable def primeIndexBlock (X : ℕ) : Finset ℕ :=
  (range (Nat.primeCounting (2 * X))).filter fun n => X < nthPrime n

theorem mem_primeIndexBlock_iff {X n : ℕ} :
    n ∈ primeIndexBlock X ↔ X < nthPrime n ∧ nthPrime n ≤ 2 * X := by
  unfold primeIndexBlock
  rw [mem_filter, mem_range]
  constructor
  · intro h
    refine ⟨h.2, ?_⟩
    exact (nthPrime_le_iff_succ_le_pi n (2 * X)).2 (Nat.succ_le_of_lt h.1)
  · intro h
    refine ⟨?_, h.1⟩
    exact Nat.lt_of_succ_le ((nthPrime_le_iff_succ_le_pi n (2 * X)).1 h.2)

theorem primeIndexBlock_eq_Ico (X : ℕ) :
    primeIndexBlock X =
      Ico (Nat.primeCounting X) (Nat.primeCounting (2 * X)) := by
  ext n
  rw [mem_primeIndexBlock_iff, mem_Ico]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have : ¬ nthPrime n ≤ X := not_le.mpr h.1
      rw [nthPrime_le_iff_succ_le_pi, not_le] at this
      exact Nat.lt_succ_iff.mp this
    · exact Nat.lt_of_succ_le ((nthPrime_le_iff_succ_le_pi n (2 * X)).1 h.2)
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← not_le, nthPrime_le_iff_succ_le_pi, not_le]
      exact Nat.lt_succ_of_le h.1
    · exact (nthPrime_le_iff_succ_le_pi n (2 * X)).2 (Nat.succ_le_of_lt h.2)

theorem card_primeIndexBlock_eq_windowNX (X : ℕ) :
    (primeIndexBlock X).card = windowNX X := by
  rw [primeIndexBlock_eq_Ico, Nat.card_Ico, windowNX]

/-- Bertrand: a prime in `(X, 2X]` exists for `X > 0`, so `m_X ≥ 1`.
This is not `m_X ≫ X / log X`. -/
theorem card_primeIndexBlock_pos {X : ℕ} (hX : 0 < X) :
    0 < (primeIndexBlock X).card := by
  rw [card_primeIndexBlock_eq_windowNX]
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul X (ne_of_gt hX)
  have hsub : Nat.primesLE X ⊆ Nat.primesLE (2 * X) :=
    Nat.primesLE_mono (by omega : X ≤ 2 * X)
  have hpX : p ∉ Nat.primesLE X := by
    simp [Nat.mem_primesLE, hp, not_le.mpr hlt]
  have hp2 : p ∈ Nat.primesLE (2 * X) := Nat.mem_primesLE.mpr ⟨hle, hp⟩
  have hss : Nat.primesLE X ⊂ Nat.primesLE (2 * X) := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨hsub, ?_⟩
    intro heq
    exact hpX (heq.symm ▸ hp2)
  have hcard := card_lt_card hss
  rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hcard
  exact Nat.sub_pos_of_lt hcard

theorem le_of_mem_primeIndexBlock {X n : ℕ} (hn : n ∈ primeIndexBlock X) :
    n ≤ Nat.primeCounting (2 * X) - 1 := by
  have hnlt : n < Nat.primeCounting (2 * X) :=
    (mem_Ico.mp ((primeIndexBlock_eq_Ico X) ▸ hn)).2
  exact Nat.le_pred_of_lt hnlt

/-! ### Average of `T_ρ(n+L)` on an index interval -/

/-- Shifted tails on any `s` with indices `≤ v` sit under `F_ρ(v+L+1)`. -/
theorem sum_primeGapTail_of_le_le_posMass {ρ : ℝ} (hρ : 1 < ρ)
    {v L : ℕ} {s : Finset ℕ} (hs : ∀ n ∈ s, n ≤ v) :
    ∑ n ∈ s, gapTail ρ (fun k => (primeGap k : ℝ)) (n + L) ≤
      posMass ρ (fun k => (nthPrime k : ℝ)) (v + L + 1) := by
  let t : Finset ℕ := s.image (fun n => n + L)
  have hinj : Set.InjOn (fun n : ℕ => n + L) (s : Set ℕ) := by
    intro a _ha b _hb h
    exact Nat.add_right_cancel h
  have ht : t ⊆ range (v + L + 1) := by
    intro i hi
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.add_le_add_right (hs n hn) L))
  have hsum := sum_primeGapTail_le_posMass hρ (n := 0) (J := v + L + 1) t ht
  have himage :
      ∑ i ∈ t, gapTail ρ (fun k => (primeGap k : ℝ)) i =
        ∑ n ∈ s, gapTail ρ (fun k => (primeGap k : ℝ)) (n + L) :=
    sum_image hinj
  have hsum' :
      ∑ i ∈ t, gapTail ρ (fun k => (primeGap k : ℝ)) i ≤
        posMass ρ (fun k => (nthPrime k : ℝ)) (v + L + 1) := by
    simpa using hsum
  exact himage.symm.trans_le hsum'

/-- Paper display after `lem:tailmass`: the block average is
`≤ F_ρ(v+L+1) / m_X` whenever `I ⊆ {u,…,v}` and `m_X > 0`. -/
theorem avg_primeGapTail_le_posMass_div {ρ : ℝ} (hρ : 1 < ρ)
    {u v L : ℕ} {s : Finset ℕ} (hs : s ⊆ Icc u v) (_hm : 0 < s.card) :
    (∑ n ∈ s, gapTail ρ (fun k => (primeGap k : ℝ)) (n + L)) / (s.card : ℝ) ≤
      posMass ρ (fun k => (nthPrime k : ℝ)) (v + L + 1) / (s.card : ℝ) := by
  have hle : ∀ n ∈ s, n ≤ v := fun n hn => (mem_Icc.mp (hs hn)).2
  have hsum := sum_primeGapTail_of_le_le_posMass (L := L) hρ hle
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

private theorem primeCounting_two_mul_add_shift {X L : ℕ}
    (hπ : 1 ≤ Nat.primeCounting (2 * X)) :
    Nat.primeCounting (2 * X) - 1 + L + 1 = Nat.primeCounting (2 * X) + L := by
  omega

/-- Condition T on the genuine prime index block, with `m_X` kept as a
positivity hypothesis (supplied by Bertrand for `X > 0`). -/
theorem conditionT_prime {ρ : ℝ} (hρ : 1 < ρ) (X L : ℕ)
    (hm : 0 < (primeIndexBlock X).card) :
    (∑ n ∈ primeIndexBlock X,
          gapTail ρ (fun k => (primeGap k : ℝ)) (n + L)) /
        ((primeIndexBlock X).card : ℝ) ≤
      posMass ρ (fun k => (nthPrime k : ℝ))
          (Nat.primeCounting (2 * X) + L) /
        ((primeIndexBlock X).card : ℝ) := by
  have hπ : 1 ≤ Nat.primeCounting (2 * X) := by
    have hlt : Nat.primeCounting X < Nat.primeCounting (2 * X) := by
      have hpos : 0 < windowNX X := by
        rwa [card_primeIndexBlock_eq_windowNX] at hm
      exact tsub_pos_iff_lt.mp hpos
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hlt)
  have hs : primeIndexBlock X ⊆
      Icc (Nat.primeCounting X) (Nat.primeCounting (2 * X) - 1) := by
    intro n hn
    rw [mem_Icc]
    have hIco := mem_Ico.mp ((primeIndexBlock_eq_Ico X) ▸ hn)
    exact ⟨hIco.1, Nat.le_pred_of_lt hIco.2⟩
  have havg :=
    avg_primeGapTail_le_posMass_div hρ (u := Nat.primeCounting X)
      (v := Nat.primeCounting (2 * X) - 1) (L := L) hs hm
  simpa [primeCounting_two_mul_add_shift hπ] using havg

/-- Polynomial form of T: the average is `O_ρ((v+L)^2 / m_X)`, not yet
`O_ρ(G)`. -/
theorem conditionT_prime_poly {ρ : ℝ} (hρ : 1 < ρ) (X L : ℕ)
    (hm : 0 < (primeIndexBlock X).card) :
    (∑ n ∈ primeIndexBlock X,
          gapTail ρ (fun k => (primeGap k : ℝ)) (n + L)) /
        ((primeIndexBlock X).card : ℝ) ≤
      posMassPolyCoeff ρ *
          ((Nat.primeCounting (2 * X) + L + 1 : ℕ) : ℝ) ^ 2 /
        ((primeIndexBlock X).card : ℝ) := by
  have hT := conditionT_prime hρ X L hm
  have hF := posMass_nthPrime_le hρ (Nat.primeCounting (2 * X) + L)
  have hden : 0 ≤ ((primeIndexBlock X).card : ℝ) := Nat.cast_nonneg _
  have hdiv :
      posMass ρ (fun k => (nthPrime k : ℝ)) (Nat.primeCounting (2 * X) + L) /
          ((primeIndexBlock X).card : ℝ) ≤
        posMassPolyCoeff ρ *
            ((Nat.primeCounting (2 * X) + L + 1 : ℕ) : ℝ) ^ 2 /
          ((primeIndexBlock X).card : ℝ) :=
    div_le_div_of_nonneg_right hF hden
  exact hT.trans hdiv

/-! ### Chebyshev density: upper bound yes, dyadic lower bound no -/

/-- Explicit Chebyshev upper bound `π(n) ≪ n / log n`. -/
theorem primeCounting_le_log4_div {n : ℕ} (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤
      Real.log 4 * (n : ℝ) / Real.log (Real.sqrt n) + Real.sqrt n := by
  have hx : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hπ := Chebyshev.pi_le_log4_mul_div hx
  have hfloor : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  simpa [hfloor] using hπ

/-- Dyadic count is at most `π(2X)`, hence `O(X / log X)` from above. -/
theorem windowNX_le_chebyshev_upper {X : ℕ} (hX : 1 ≤ X) :
    (windowNX X : ℝ) ≤
      Real.log 4 * (2 * X : ℝ) / Real.log (Real.sqrt (2 * X : ℝ)) +
        Real.sqrt (2 * X : ℝ) := by
  have h2 : 2 ≤ 2 * X := by omega
  have hπ := primeCounting_le_log4_div h2
  have hcast : ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := by simp
  have hle : (windowNX X : ℝ) ≤ (Nat.primeCounting (2 * X) : ℝ) :=
    Nat.cast_le.mpr (Nat.sub_le _ _)
  rw [hcast] at hπ
  exact hle.trans hπ

/-- Witness that Chebyshev's leading constants cancel dyadically:
the lower estimate for `π(2X)` does not exceed the upper estimate for
`π(X)`. Their difference is therefore not a positive multiple of
`X / log X`. -/
theorem chebyshev_dyadic_estimates_le {X : ℕ} (hX : 2 ≤ X) :
    ((2 * X : ℝ) * Real.log 2 - Real.log ((2 * X + 1 : ℕ) : ℝ)) /
        Real.log (2 * X : ℝ) ≤
      Real.log 4 * (X : ℝ) / Real.log (Real.sqrt X) + Real.sqrt X := by
  have hx : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hX)
  have hXpos : (0 : ℝ) < X := lt_trans (by norm_num) hx
  have h2le : (2 : ℝ) ≤ 2 * (X : ℝ) := by
    have : (1 : ℝ) ≤ X := le_of_lt hx
    have hmul := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2)
    simpa using hmul
  have h2X : (1 : ℝ) < 2 * (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h2le
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hx
  have hlog2X : 0 < Real.log (2 * (X : ℝ)) := Real.log_pos h2X
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast2X : (2 * X : ℝ) = 2 * (X : ℝ) := by simp
  have hnum_le :
      (2 * X : ℝ) * Real.log 2 - Real.log ((2 * X + 1 : ℕ) : ℝ) ≤
        (2 * X : ℝ) * Real.log 2 := by
    have hlog : 0 ≤ Real.log ((2 * X + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * X + 1))
    linarith
  have hLHS :
      ((2 * X : ℝ) * Real.log 2 - Real.log ((2 * X + 1 : ℕ) : ℝ)) /
          Real.log (2 * X : ℝ) ≤
        (2 * X : ℝ) * Real.log 2 / Real.log (2 * (X : ℝ)) := by
    rw [hcast2X]
    exact div_le_div_of_nonneg_right hnum_le hlog2X.le
  have hsqrt : Real.log (Real.sqrt X) = Real.log (X : ℝ) / 2 :=
    Real.log_sqrt (Nat.cast_nonneg _)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [h4, Real.log_rpow (by positivity : (0 : ℝ) < 2)]
  have hRmain :
      4 * Real.log 2 * (X : ℝ) / Real.log (X : ℝ) ≤
        Real.log 4 * (X : ℝ) / Real.log (Real.sqrt X) + Real.sqrt X := by
    have hrew :
        Real.log 4 * (X : ℝ) / Real.log (Real.sqrt X) =
          4 * Real.log 2 * (X : ℝ) / Real.log (X : ℝ) := by
      rw [hlog4, hsqrt]
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      field_simp [hlogX.ne', h2]
      ring
    have hsqrt0 : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
    linarith [hrew, hsqrt0]
  have hmid :
      (2 * X : ℝ) * Real.log 2 / Real.log (2 * (X : ℝ)) ≤
        4 * Real.log 2 * (X : ℝ) / Real.log (X : ℝ) := by
    rw [hcast2X, div_le_div_iff₀ hlog2X hlogX]
    have hlog2X_eq : Real.log (2 * (X : ℝ)) = Real.log 2 + Real.log (X : ℝ) :=
      Real.log_mul (by norm_num) hXpos.ne'
    rw [hlog2X_eq]
    have hL : 2 * (X : ℝ) * Real.log 2 * Real.log (X : ℝ) =
        2 * Real.log 2 * (X : ℝ) * Real.log (X : ℝ) := by ring
    have hR : 4 * Real.log 2 * (X : ℝ) * (Real.log 2 + Real.log (X : ℝ)) =
        4 * Real.log 2 * (X : ℝ) * Real.log 2 +
          4 * Real.log 2 * (X : ℝ) * Real.log (X : ℝ) := by ring
    rw [hL, hR]
    have hcoeff :
        (2 : ℝ) * Real.log 2 * (X : ℝ) * Real.log (X : ℝ) ≤
          4 * Real.log 2 * (X : ℝ) * Real.log (X : ℝ) := by
      have hc : (2 : ℝ) ≤ 4 := by norm_num
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc hlog2.le) hXpos.le) hlogX.le
    have hrest : 0 ≤ 4 * Real.log 2 * (X : ℝ) * Real.log 2 := by positivity
    linarith [hcoeff, hrest]
  have hcastLog : Real.log (2 * X : ℝ) = Real.log (2 * (X : ℝ)) := by simp
  rw [hcastLog] at hLHS
  exact hLHS.trans (hmid.trans hRmain)

end PrimeGapNormality.Prime
