import PrimeGapNormality.Prime.Fourier
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.Hausdorff

/-!
# Abstract Q-independence from mixed Weyl / non-Weyl laws

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN

If `x` is Weyl-normal to base `b ≥ 2` and `y` is irrational but not
Weyl-normal to base `b`, then `1, x, y` are linearly independent over
`ℚ`. Integer Weyl algebra and the finite Wall lift
`weylCriterion_of_mul` live here; Fourier omitted that packaging.
No prime or B-free end theorems, and no assembly of `α_{b,P}` or
`β_{b,sf}`.
-/

set_option maxHeartbeats 2000000

open Finset
open Filter (Tendsto atTop)
open scoped Topology

namespace PrimeGapNormality.Prime

/-! ### Circle-character identities (public `e`, private Fourier copies) -/

/-- Additivity of the circle character.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

/-- Integers map to `1` under the circle character.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
private theorem e_int (n : ℤ) : e n = 1 := by
  unfold e
  simp only [Complex.ofReal_intCast]
  have h : (2 * Real.pi * Complex.I * (n : ℂ)) = n * (2 * Real.pi * Complex.I) := by
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- Integer frequencies times an integer phase remain integer.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
private theorem e_int_mul_pow (τ n : ℤ) (b k : ℕ) :
    e ((τ : ℝ) * (b : ℝ) ^ k * n) = 1 := by
  have : (τ : ℝ) * (b : ℝ) ^ k * n = ((τ * (b : ℤ) ^ k * n : ℤ) : ℝ) := by
    push_cast
    ring
  rw [this, e_int]

/-- Adding an integer does not change Weyl Cesàro means:
`e(τ b^n (θ+k)) = e(τ b^n θ)`.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
theorem weylCriterion_add_int {b : ℕ} {θ : ℝ} (n : ℤ)
    (h : weylCriterion b θ) : weylCriterion b (θ + n) := by
  intro τ hτ
  have hrew : ∀ k : ℕ,
      e ((τ : ℝ) * (b : ℝ) ^ k * (θ + n)) =
        e ((τ : ℝ) * (b : ℝ) ^ k * θ) := by
    intro k
    have hsplit :
        (τ : ℝ) * (b : ℝ) ^ k * (θ + n) =
          (τ : ℝ) * (b : ℝ) ^ k * θ + (τ : ℝ) * (b : ℝ) ^ k * n := by
      ring
    rw [hsplit, e_add, e_int_mul_pow, mul_one]
  have hfun :
      (fun N : ℕ =>
        (∑ k ∈ range N, e ((τ : ℝ) * (b : ℝ) ^ k * (θ + n))) / N) =
        fun N => (∑ k ∈ range N, e ((τ : ℝ) * (b : ℝ) ^ k * θ)) / N := by
    funext N
    congr 1
    exact sum_congr rfl fun k _ => hrew k
  rw [hfun]
  exact h τ hτ

/-- Negation preserves Weyl: it replaces the integer frequency `τ` by `-τ`.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
theorem weylCriterion_neg {b : ℕ} {θ : ℝ}
    (h : weylCriterion b θ) : weylCriterion b (-θ) := by
  intro τ hτ
  have hrew : ∀ k : ℕ,
      e ((τ : ℝ) * (b : ℝ) ^ k * (-θ)) =
        e (((-τ : ℤ) : ℝ) * (b : ℝ) ^ k * θ) := by
    intro k
    have : (τ : ℝ) * (b : ℝ) ^ k * (-θ) =
        ((-τ : ℤ) : ℝ) * (b : ℝ) ^ k * θ := by
      push_cast
      ring
    rw [this]
  have hfun :
      (fun N : ℕ =>
        (∑ k ∈ range N, e ((τ : ℝ) * (b : ℝ) ^ k * (-θ))) / N) =
        fun N => (∑ k ∈ range N, e (((-τ : ℤ) : ℝ) * (b : ℝ) ^ k * θ)) / N := by
    funext N
    congr 1
    exact sum_congr rfl fun k _ => hrew k
  rw [hfun]
  exact h (-τ) (neg_ne_zero.mpr hτ)

/-- Nonzero integer scaling preserves Weyl: it replaces `τ` by `τ m`.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
theorem weylCriterion_int_mul {b : ℕ} {θ : ℝ} {m : ℤ} (hm : m ≠ 0)
    (h : weylCriterion b θ) : weylCriterion b (m * θ) := by
  intro τ hτ
  have hrew : ∀ k : ℕ,
      e ((τ : ℝ) * (b : ℝ) ^ k * (m * θ)) =
        e (((τ * m : ℤ) : ℝ) * (b : ℝ) ^ k * θ) := by
    intro k
    have : (τ : ℝ) * (b : ℝ) ^ k * (m * θ) =
        ((τ * m : ℤ) : ℝ) * (b : ℝ) ^ k * θ := by
      push_cast
      ring
    rw [this]
  have hfun :
      (fun N : ℕ =>
        (∑ k ∈ range N, e ((τ : ℝ) * (b : ℝ) ^ k * (m * θ))) / N) =
        fun N =>
          (∑ k ∈ range N, e (((τ * m : ℤ) : ℝ) * (b : ℝ) ^ k * θ)) / N := by
    funext N
    congr 1
    exact sum_congr rfl fun k _ => hrew k
  rw [hfun]
  exact h (τ * m) (mul_ne_zero hτ hm)

/-- Weyl of `m θ` implies Weyl of `|m| θ`.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
private theorem weylCriterion_natAbs_mul {b : ℕ} {θ : ℝ} {m : ℤ}
    (h : weylCriterion b (m * θ)) :
    weylCriterion b ((m.natAbs : ℝ) * θ) := by
  obtain hm | hm := Int.natAbs_eq m
  · have hmul : (m.natAbs : ℝ) * θ = m * θ := by
      have : (m.natAbs : ℝ) = (m : ℝ) := by
        calc
          (m.natAbs : ℝ) = ((m.natAbs : ℤ) : ℝ) := by rw [Int.cast_natCast]
          _ = (m : ℝ) := by rw [← hm]
      rw [this]
    rwa [hmul]
  · have hneg : weylCriterion b (-(m * θ)) := weylCriterion_neg h
    have hmul : (m.natAbs : ℝ) * θ = -(m * θ) := by
      have hm' : m = - (m.natAbs : ℤ) := hm
      have : (m : ℝ) = - (m.natAbs : ℝ) := by
        rw [hm']
        simp
      rw [this]
      ring
    rwa [hmul]

/-! ### Finite Wall lift (R97/05 §3) -/

/-- Circle character at `0`.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem e_zero : e 0 = 1 := by
  unfold e
  simp [Complex.exp_zero]

/-- Natural multiples become powers of the circle character.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem e_nat_mul (n : ℕ) (x : ℝ) : e ((n : ℝ) * x) = e x ^ n := by
  unfold e
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  have h : (2 * Real.pi * Complex.I * ((n : ℂ) * x)) =
      (n : ℂ) * (2 * Real.pi * Complex.I * x) := by
    ring
  rw [h, Complex.exp_nat_mul]

/-- `e x = 1` if and only if `x` is an integer.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem e_eq_one_iff (x : ℝ) : e x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold e
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hmul :
        (2 * Real.pi * Complex.I : ℂ) * x =
          (2 * Real.pi * Complex.I) * (n : ℂ) := by
      have hn' : (2 * Real.pi * Complex.I : ℂ) * x =
          n * (2 * Real.pi * Complex.I) := by
        convert hn using 1 <;> ring
      simpa [mul_comm] using hn'
    have := mul_left_cancel₀ Complex.two_pi_I_ne_zero hmul
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simp [Complex.ofReal_intCast]
    ring

/-- Circle characters are unimodular.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem two_pi_I_mul (x : ℝ) :
    (2 * Real.pi * Complex.I * (x : ℂ) : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) := by
  simp [mul_comm, mul_left_comm, Complex.ofReal_mul]

private theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [two_pi_I_mul, Complex.norm_exp_I_mul_ofReal]

/-- Star on the circle is negation of the phase.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem star_e (x : ℝ) : star (e x) = e (-x) := by
  have hx : e x ≠ 0 := by
    have hn : ‖e x‖ = 1 := norm_e x
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  apply mul_right_cancel₀ hx
  have hstar : star (e x) * e x = ‖e x‖ ^ 2 := by
    rw [mul_comm]
    change e x * starRingEnd ℂ (e x) = ‖e x‖ ^ 2
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [hstar, norm_e]
  simp
  rw [← e_add, neg_add_cancel, e_zero]

/-- Geometric sum of `q`-th roots: `q` on the lattice, else `0`.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem geom_root_sum {q : ℕ} (hq : 0 < q) (m : ℤ) :
    ∑ r ∈ range q, e ((m : ℝ) * r / q) =
      if (q : ℤ) ∣ m then (q : ℂ) else 0 := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
  let ω : ℂ := e ((m : ℝ) / q)
  have hsum : ∑ r ∈ range q, e ((m : ℝ) * r / q) = ∑ r ∈ range q, ω ^ r := by
    refine sum_congr rfl fun r _ => ?_
    have hr : (r : ℝ) * ((m : ℝ) / q) = (m : ℝ) * r / q := by
      field_simp [hq0]
    rw [← hr, e_nat_mul]
  have hωq : ω ^ q = 1 := by
    have : (q : ℝ) * ((m : ℝ) / q) = (m : ℝ) := by field_simp [hq0]
    rw [← e_nat_mul, this, e_int]
  by_cases hdiv : (q : ℤ) ∣ m
  · have hω : ω = 1 := by
      obtain ⟨k, hk⟩ := hdiv
      have : (m : ℝ) / q = (k : ℝ) := by
        have hk' : (m : ℝ) = (q : ℝ) * k := by exact_mod_cast hk
        field_simp [hq0]
        exact hk'
      simpa [ω, this] using e_int k
    rw [hsum, if_pos hdiv]
    simp [hω, one_pow, sum_const, nsmul_one]
  · have hω : ω ≠ 1 := by
      intro hω1
      obtain ⟨n, hn⟩ := (e_eq_one_iff _).mp hω1
      have hm : (m : ℝ) = (n : ℝ) * q := by
        rw [← hn]
        field_simp [hq0]
      have hmz : m = n * (q : ℤ) := by exact_mod_cast hm
      exact hdiv ⟨n, by simpa [mul_comm] using hmz⟩
    rw [hsum, geom_sum_eq hω q, hωq, if_neg hdiv]
    simp

/-- Off-diagonal geometric frequencies stay nonzero for `b ≥ 2`.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem freq_ne_zero {b : ℕ} (hb : 2 ≤ b) {t : ℤ} (ht : t ≠ 0)
    {j k : ℕ} (hjk : j ≠ k) :
    t * ((b : ℤ) ^ j - (b : ℤ) ^ k) ≠ 0 := by
  intro h0
  rcases mul_eq_zero.mp h0 with ht0 | hpow
  · exact ht ht0
  · have heq : (b : ℤ) ^ j = (b : ℤ) ^ k := sub_eq_zero.mp hpow
    have hb1 : 1 < b := lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hb
    have hbn : b ^ j = b ^ k := by exact_mod_cast heq
    exact hjk (Nat.pow_right_injective hb1 hbn)

/-- Real frequency matches the integer difference.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem freq_real (t : ℤ) (b j k : ℕ) :
    (t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) =
      (t * ((b : ℤ) ^ j - (b : ℤ) ^ k) : ℤ) := by
  push_cast
  ring

/-- Length-`M` Weyl kernel.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
noncomputable def weylKernel (b : ℕ) (t : ℤ) (x : ℝ) (M : ℕ) : ℂ :=
  (∑ j ∈ range M, e ((t : ℝ) * (b : ℝ) ^ j * x)) / M

/-- Squared kernel modulus `F_M`.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
noncomputable def weylKernelSq (b : ℕ) (t : ℤ) (x : ℝ) (M : ℕ) : ℝ :=
  ‖weylKernel b t x M‖ ^ 2

/-- Expand `F_M` as a double character sum.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem weylKernel_mul_star (b : ℕ) (t : ℤ) (x : ℝ) {M : ℕ} (hM : 0 < M) :
    weylKernel b t x M * star (weylKernel b t x M) =
      ((1 : ℂ) / (M : ℂ) ^ 2) *
        ∑ j ∈ range M, ∑ k ∈ range M,
          e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * x) := by
  have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)
  unfold weylKernel
  have hstarM : star (M : ℂ) = (M : ℂ) := by simp
  rw [star_div₀, hstarM, div_mul_div_comm]
  have hden : (M : ℂ) * M = (M : ℂ) ^ 2 := by ring
  rw [hden]
  have hst :
      star (∑ j ∈ range M, e ((t : ℝ) * (b : ℝ) ^ j * x)) =
        ∑ j ∈ range M, star (e ((t : ℝ) * (b : ℝ) ^ j * x)) :=
    map_sum (starAddEquiv : ℂ ≃+ ℂ)
      (fun j : ℕ => e ((t : ℝ) * (b : ℝ) ^ j * x)) (range M)
  rw [hst]
  have hterm : ∀ j k : ℕ,
      e ((t : ℝ) * (b : ℝ) ^ j * x) *
          star (e ((t : ℝ) * (b : ℝ) ^ k * x)) =
        e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * x) := by
    intro j k
    rw [star_e, ← e_add]
    congr 1
    ring
  rw [sum_mul_sum]
  simp_rw [hterm]
  rw [div_eq_mul_inv, one_div, mul_comm]

/-- Complexify `F_M`.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem ofReal_weylKernelSq (b : ℕ) (t : ℤ) (x : ℝ) {M : ℕ}
    (_hM : 0 < M) :
    (weylKernelSq b t x M : ℂ) =
      weylKernel b t x M * star (weylKernel b t x M) := by
  unfold weylKernelSq
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  rfl

/-- `F_M(x) ≤ H_M(x)` by the `r = 0` summand.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem weylKernelSq_le_shift {q : ℕ} (hq : 1 ≤ q) (b : ℕ) (t : ℤ)
    (M : ℕ) (x : ℝ) :
    weylKernelSq b t x M ≤ ∑ r ∈ range q, weylKernelSq b t (x + r / q) M := by
  have hr0 : (0 : ℕ) ∈ range q := mem_range.mpr hq
  have hnn : ∀ r ∈ range q, 0 ≤ weylKernelSq b t (x + r / q) M :=
    fun _ _ => sq_nonneg _
  have hx : weylKernelSq b t (x + (0 : ℕ) / q) M = weylKernelSq b t x M := by
    simp
  calc
    weylKernelSq b t x M = weylKernelSq b t (x + (0 : ℕ) / q) M := hx.symm
    _ ≤ ∑ r ∈ range q, weylKernelSq b t (x + r / q) M :=
      single_le_sum hnn hr0

/-- Finite Fourier form of `H_M`.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem ofReal_shift_sum {q M : ℕ} (hq : 0 < q) (hM : 0 < M)
    (b : ℕ) (t : ℤ) (x : ℝ) :
    ((∑ r ∈ range q, weylKernelSq b t (x + r / q) M : ℝ) : ℂ) =
      ((1 : ℂ) / (M : ℂ) ^ 2) *
        ∑ j ∈ range M, ∑ k ∈ range M,
          (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
            e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * x) := by
  rw [Complex.ofReal_sum]
  have hpt : ∀ r ∈ range q,
      (weylKernelSq b t (x + r / q) M : ℂ) =
        ((1 : ℂ) / (M : ℂ) ^ 2) *
          ∑ j ∈ range M, ∑ k ∈ range M,
            e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * (x + r / q)) := by
    intro r _
    rw [ofReal_weylKernelSq _ _ _ hM, weylKernel_mul_star _ _ _ hM]
  simp_rw [sum_congr rfl hpt, ← mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  have hgeom :
      ∑ r ∈ range q,
          e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * (x + r / q)) =
        (∑ r ∈ range q,
            e ((t * ((b : ℤ) ^ j - (b : ℤ) ^ k) : ℤ) * (r : ℝ) / q)) *
          e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * x) := by
    have hterm : ∀ r ∈ range q,
        e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * (x + r / q)) =
          e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * x) *
            e ((t * ((b : ℤ) ^ j - (b : ℤ) ^ k) : ℤ) * (r : ℝ) / q) := by
      intro r _
      have hx : (t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * (x + r / q) =
          (t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * x +
            (t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * (r / q) := by
        ring
      have hr : (t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * (r / q) =
          (t * ((b : ℤ) ^ j - (b : ℤ) ^ k) : ℤ) * (r : ℝ) / q := by
        have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
        rw [freq_real]
        field_simp [hq0]
      rw [hx, e_add, hr]
    rw [sum_congr rfl hterm, ← mul_sum, mul_comm]
  rw [hgeom, geom_root_sum hq, mul_comm]

/-- Finite sums of convergent sequences converge.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem tendsto_finset_sum_nhds {ι : Type*} (s : Finset ι)
    (f : ι → ℕ → ℂ) (a : ι → ℂ)
    (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (a i))) :
    Tendsto (fun N => ∑ i ∈ s, f i N) atTop (𝓝 (∑ i ∈ s, a i)) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using tendsto_const_nhds (x := (0 : ℂ))
  · intro i t hit ih hf
    have hi : Tendsto (f i) atTop (𝓝 (a i)) := hf i (mem_insert_self i t)
    have ht : ∀ j ∈ t, Tendsto (f j) atTop (𝓝 (a j)) :=
      fun j hj => hf j (mem_insert_of_mem hj)
    simp_rw [sum_insert hit]
    exact hi.add (ih ht)

/-- Shifted Cesàro means differ by `O(j/N)` for unimodular sequences.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem cesaro_shift_sub (a : ℕ → ℂ) (j N : ℕ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ‖(∑ n ∈ range N, a (n + j)) / N - (∑ n ∈ range N, a n) / N‖
      ≤ (2 * j : ℝ) / N := by
  by_cases hN : N = 0
  · subst hN
    simp
  · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hswap : ∑ n ∈ range N, a (n + j) = ∑ n ∈ range N, a (j + n) :=
      sum_congr rfl fun n _ => by rw [add_comm]
    have h1 := sum_range_add a j N
    have h2 := sum_range_add a N j
    have hdiff :
        ∑ n ∈ range N, a (j + n) - ∑ n ∈ range N, a n =
          ∑ n ∈ range j, a (N + n) - ∑ n ∈ range j, a n := by
      have hNj : N + j = j + N := Nat.add_comm _ _
      have hlong1 : ∑ n ∈ range (N + j), a n =
          ∑ n ∈ range j, a n + ∑ n ∈ range N, a (j + n) := by
        simpa [hNj] using h1
      have hlong2 : ∑ n ∈ range (N + j), a n =
          ∑ n ∈ range N, a n + ∑ n ∈ range j, a (N + n) := h2
      have hleft :
          ∑ n ∈ range N, a (j + n) =
            ∑ n ∈ range (N + j), a n - ∑ n ∈ range j, a n := by
        rw [hlong1]
        abel
      have hright :
          ∑ n ∈ range N, a n =
            ∑ n ∈ range (N + j), a n - ∑ n ∈ range j, a (N + n) := by
        rw [hlong2]
        abel
      rw [hleft, hright]
      abel
    have hbd :
        ‖∑ n ∈ range N, a (j + n) - ∑ n ∈ range N, a n‖ ≤ (2 * j : ℝ) := by
      rw [hdiff]
      have hA : ‖∑ n ∈ range j, a (N + n)‖ ≤ j := by
        have := norm_sum_le (range j) fun n => a (N + n)
        have h1' : ∑ n ∈ range j, ‖a (N + n)‖ ≤ ∑ n ∈ range j, (1 : ℝ) :=
          sum_le_sum fun n _ => ha _
        have hcard : (∑ n ∈ range j, (1 : ℝ)) = j := by simp [sum_const]
        exact this.trans (h1'.trans_eq hcard)
      have hB : ‖∑ n ∈ range j, a n‖ ≤ j := by
        have := norm_sum_le (range j) a
        have h1' : ∑ n ∈ range j, ‖a n‖ ≤ ∑ n ∈ range j, (1 : ℝ) :=
          sum_le_sum fun n _ => ha _
        have hcard : (∑ n ∈ range j, (1 : ℝ)) = j := by simp [sum_const]
        exact this.trans (h1'.trans_eq hcard)
      have hsub := (norm_sub_le (∑ n ∈ range j, a (N + n)) (∑ n ∈ range j, a n)).trans
        (add_le_add hA hB)
      have h2j : (j : ℝ) + j = 2 * j := by ring
      exact hsub.trans_eq h2j
    rw [hswap, ← sub_div, norm_div]
    have hNnorm : ‖(N : ℂ)‖ = N := by simp
    rw [hNnorm]
    exact (div_le_div_of_nonneg_right hbd (Nat.cast_nonneg N))

/-- Cesàro means of the constant `1` tend to `1`.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem tendsto_one_div_nat :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (1 : ℂ)) / N) atTop (𝓝 1) := by
  have heq :
      (fun N : ℕ => (∑ n ∈ range N, (1 : ℂ)) / N) =ᶠ[atTop]
        fun _ => (1 : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
    simp [sum_const, nsmul_eq_mul, hN0]
  exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

/-- Pair term of the `H_M` Cesàro: diagonal `q`, off-diagonal `0`.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem tendsto_pair_term {q b : ℕ} (hq : 0 < q) (hb : 2 ≤ b)
    {θ : ℝ} (hθ : weylCriterion b ((q : ℝ) * θ))
    (t : ℤ) (ht : t ≠ 0) (j k : ℕ) :
    Tendsto (fun N : ℕ =>
      (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
        ((∑ n ∈ range N,
            e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
              ((b : ℝ) ^ n * θ))) / N))
      atTop
      (𝓝 (if j = k then (q : ℂ) else 0)) := by
  by_cases hjk : j = k
  · subst hjk
    have hdiv : (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ j) := by simp
    have hfun :
        (fun N : ℕ =>
          (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ j) then (q : ℂ) else 0) *
            ((∑ n ∈ range N,
                e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ j) *
                  ((b : ℝ) ^ n * θ))) / N)) =
          fun N => (q : ℂ) * ((∑ n ∈ range N, (1 : ℂ)) / N) := by
      funext N
      simp only [hdiv, if_true, sub_self, mul_zero]
      congr 1
      congr 1
      refine sum_congr rfl fun n _ => ?_
      rw [zero_mul, e_zero]
    rw [hfun]
    simpa using tendsto_const_nhds.mul tendsto_one_div_nat
  · by_cases hdiv : (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k)
    · have hdiv' := hdiv
      obtain ⟨τ, hτeq⟩ := hdiv
      have hτ : τ ≠ 0 := by
        intro h0
        apply freq_ne_zero hb ht hjk
        simp [hτeq, h0]
      have hmode := hθ τ hτ
      have hrew : ∀ n : ℕ,
          e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * ((b : ℝ) ^ n * θ)) =
            e ((τ : ℝ) * (b : ℝ) ^ n * ((q : ℝ) * θ)) := by
        intro n
        have hx :
            (t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) * ((b : ℝ) ^ n * θ) =
              (τ : ℝ) * (b : ℝ) ^ n * ((q : ℝ) * θ) := by
          have hcast :
              (t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) =
                ((q : ℤ) * τ : ℤ) := by
            rw [freq_real, hτeq]
          rw [hcast]
          push_cast
          ring
        rw [hx]
      have hite :
          (fun N : ℕ =>
            (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
              ((∑ n ∈ range N,
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ))) / N)) =
            fun N =>
              (q : ℂ) *
                ((∑ n ∈ range N,
                    e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                      ((b : ℝ) ^ n * θ))) / N) := by
        funext N
        simp only [hdiv', if_true]
      rw [hite]
      have hces :
          Tendsto (fun N : ℕ =>
            (∑ n ∈ range N,
                e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                  ((b : ℝ) ^ n * θ))) / N)
            atTop (𝓝 0) := by
        have hfun :
            (fun N : ℕ =>
              (∑ n ∈ range N,
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ))) / N) =
              fun N =>
                (∑ n ∈ range N,
                    e ((τ : ℝ) * (b : ℝ) ^ n * ((q : ℝ) * θ))) / N := by
          funext N
          congr 1
          exact sum_congr rfl fun n _ => hrew n
        rwa [hfun]
      simpa [hjk] using tendsto_const_nhds.mul hces
    · have hfun :
          (fun N : ℕ =>
            (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
              ((∑ n ∈ range N,
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ))) / N)) =
            fun _ => (0 : ℂ) := by
        funext N
        simp only [hdiv, if_false, zero_mul]
      rw [hfun]
      simpa [hjk] using tendsto_const_nhds (x := (0 : ℂ))

/-- Cesàro of `H_M(b^n θ)` tends to `q/M`.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem tendsto_cesaro_H {q b : ℕ} (hq : 1 ≤ q) (hb : 2 ≤ b)
    {θ : ℝ} (hθ : weylCriterion b ((q : ℝ) * θ))
    {t : ℤ} (ht : t ≠ 0) {M : ℕ} (hM : 0 < M) :
    Tendsto (fun N : ℕ =>
      (((∑ n ∈ range N,
          ∑ r ∈ range q, weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M) : ℝ) /
        N : ℂ))
      atTop (𝓝 ((q : ℂ) / M)) := by
  have hqpos : 0 < q := hq
  have hident : ∀ N : ℕ,
      (((∑ n ∈ range N,
          ∑ r ∈ range q, weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M) : ℝ) /
        N : ℂ) =
        ((1 : ℂ) / (M : ℂ) ^ 2) *
          ∑ j ∈ range M, ∑ k ∈ range M,
            (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
              ((∑ n ∈ range N,
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ))) / N) := by
    intro N
    by_cases hN : N = 0
    · subst hN
      simp
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hNpos)
      rw [Complex.ofReal_sum]
      have hpt : ∀ n ∈ range N,
          ((∑ r ∈ range q, weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M : ℝ) : ℂ) =
            ((1 : ℂ) / (M : ℂ) ^ 2) *
              ∑ j ∈ range M, ∑ k ∈ range M,
                (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ)) :=
        fun n _ => ofReal_shift_sum hqpos hM b t _
      have hrew :
          (∑ n ∈ range N,
              ((∑ r ∈ range q,
                  weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M : ℝ) : ℂ)) =
            ∑ n ∈ range N,
              ((1 : ℂ) / (M : ℂ) ^ 2) *
                ∑ j ∈ range M, ∑ k ∈ range M,
                  (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                    e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                      ((b : ℝ) ^ n * θ)) :=
        sum_congr rfl hpt
      rw [hrew, ← mul_sum]
      have hswap :
          (∑ n ∈ range N, ∑ j ∈ range M, ∑ k ∈ range M,
              (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                  ((b : ℝ) ^ n * θ))) / N =
            ∑ j ∈ range M, ∑ k ∈ range M,
              (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                ((∑ n ∈ range N,
                    e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                      ((b : ℝ) ^ n * θ))) / N) := by
        have hcomm1 :
            ∑ n ∈ range N, ∑ j ∈ range M, ∑ k ∈ range M,
                (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ)) =
              ∑ j ∈ range M, ∑ n ∈ range N, ∑ k ∈ range M,
                (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ)) := by
          rw [sum_comm]
        have hcomm2 :
            ∑ j ∈ range M, ∑ n ∈ range N, ∑ k ∈ range M,
                (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ)) =
              ∑ j ∈ range M, ∑ k ∈ range M, ∑ n ∈ range N,
                (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ)) := by
          refine sum_congr rfl fun j _ => sum_comm
        have hfactor :
            ∑ j ∈ range M, ∑ k ∈ range M, ∑ n ∈ range N,
                (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ)) =
              ∑ j ∈ range M, ∑ k ∈ range M,
                (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                  ∑ n ∈ range N,
                    e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                      ((b : ℝ) ^ n * θ)) := by
          refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
          rw [← mul_sum]
        rw [hcomm1, hcomm2, hfactor, div_eq_mul_inv, sum_mul]
        refine sum_congr rfl fun j _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_assoc, ← div_eq_mul_inv]
      rw [div_eq_mul_inv]
      have hscale :
          ((1 : ℂ) / (M : ℂ) ^ 2 *
              ∑ n ∈ range N, ∑ j ∈ range M, ∑ k ∈ range M,
                (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ))) * (N : ℂ)⁻¹ =
            ((1 : ℂ) / (M : ℂ) ^ 2) *
              ((∑ n ∈ range N, ∑ j ∈ range M, ∑ k ∈ range M,
                  (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
                    e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                      ((b : ℝ) ^ n * θ))) / N) := by
        rw [div_eq_mul_inv]
        ring
      rw [hscale, hswap]
  simp_rw [hident]
  have hpairs :=
    tendsto_finset_sum_nhds (range M)
      (fun j N => ∑ k ∈ range M,
        (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
          ((∑ n ∈ range N,
              e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                ((b : ℝ) ^ n * θ))) / N))
      (fun j => ∑ k ∈ range M, (if j = k then (q : ℂ) else 0))
      (fun j _ =>
        tendsto_finset_sum_nhds (range M)
          (fun k N =>
            (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
              ((∑ n ∈ range N,
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ))) / N))
          (fun k => if j = k then (q : ℂ) else 0)
          (fun k _ => tendsto_pair_term hqpos hb hθ t ht j k))
  have hdiag : (∑ j ∈ range M, ∑ k ∈ range M, (if j = k then (q : ℂ) else 0)) =
      (M : ℂ) * q := by
    have hinner : ∀ j ∈ range M,
        (∑ k ∈ range M, (if j = k then (q : ℂ) else 0)) = q := by
      intro j hj
      rw [sum_ite_eq]
      simp [hj]
    simp_rw [sum_congr rfl hinner, sum_const, nsmul_eq_mul, card_range]
  have hscale :
      Tendsto (fun N =>
        ((1 : ℂ) / (M : ℂ) ^ 2) *
          ∑ j ∈ range M, ∑ k ∈ range M,
            (if (q : ℤ) ∣ t * ((b : ℤ) ^ j - (b : ℤ) ^ k) then (q : ℂ) else 0) *
              ((∑ n ∈ range N,
                  e ((t : ℝ) * ((b : ℝ) ^ j - (b : ℝ) ^ k) *
                    ((b : ℝ) ^ n * θ))) / N))
        atTop (𝓝 (((1 : ℂ) / (M : ℂ) ^ 2) * ((M : ℂ) * q))) :=
    tendsto_const_nhds.mul (hdiag ▸ hpairs)
  have hval : ((1 : ℂ) / (M : ℂ) ^ 2) * ((M : ℂ) * q) = (q : ℂ) / M := by
    have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)
    field_simp [hM0]
  exact hval ▸ hscale

/-- Kernel at the scaled point is a shifted block of characters.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem weylKernel_eq_avg (b : ℕ) (t : ℤ) (θ : ℝ) (M n : ℕ) :
    weylKernel b t ((b : ℝ) ^ n * θ) M =
      (∑ j ∈ range M, e ((t : ℝ) * (b : ℝ) ^ (n + j) * θ)) / M := by
  unfold weylKernel
  congr 1
  refine sum_congr rfl fun j _ => ?_
  have hpow : (t : ℝ) * (b : ℝ) ^ j * ((b : ℝ) ^ n * θ) =
      (t : ℝ) * (b : ℝ) ^ (n + j) * θ := by
    rw [pow_add]
    ring
  rw [hpow]

/-- Cauchy–Schwarz for a Cesàro mean of kernels.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
private theorem cesaro_kernel_sq_le (b : ℕ) (t : ℤ) (θ : ℝ) (M N : ℕ) :
    ‖(∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N‖ ^ 2 ≤
      (∑ n ∈ range N, weylKernelSq b t ((b : ℝ) ^ n * θ) M) / N := by
  by_cases hN : N = 0
  · subst hN
    simp
  · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hz : ‖∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M‖ ≤
        ∑ n ∈ range N, ‖weylKernel b t ((b : ℝ) ^ n * θ) M‖ :=
      norm_sum_le _ _
    have hcs : (∑ n ∈ range N, ‖weylKernel b t ((b : ℝ) ^ n * θ) M‖) ^ 2 ≤
        (range N).card * ∑ n ∈ range N, ‖weylKernel b t ((b : ℝ) ^ n * θ) M‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hcard : ((range N).card : ℝ) = N := by simp
    have hsq : ‖∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M‖ ^ 2 ≤
        (N : ℝ) * ∑ n ∈ range N, weylKernelSq b t ((b : ℝ) ^ n * θ) M := by
      have hnn : 0 ≤ ∑ n ∈ range N, ‖weylKernel b t ((b : ℝ) ^ n * θ) M‖ :=
        sum_nonneg fun _ _ => norm_nonneg _
      have := pow_le_pow_left₀ (norm_nonneg _) hz 2
      refine this.trans ?_
      simpa [weylKernelSq, hcard] using hcs
    rw [norm_div]
    have hNnorm : ‖(N : ℂ)‖ = N := by simp
    rw [hNnorm, div_pow]
    have hden : (N : ℝ) ^ 2 = N * N := by ring
    rw [hden]
    have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
    have hcalc :
        ‖∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M‖ ^ 2 / (N * N) ≤
          (∑ n ∈ range N, weylKernelSq b t ((b : ℝ) ^ n * θ) M) / N := by
      field_simp [hNne]
      have hcomm :
          ∑ n ∈ range N, weylKernelSq b t (θ * (b : ℝ) ^ n) M =
            ∑ n ∈ range N, weylKernelSq b t ((b : ℝ) ^ n * θ) M :=
        sum_congr rfl fun n _ => by rw [mul_comm θ]
      rw [hcomm]
      exact hsq
    exact hcalc

/-- R97/05 §3 finite Wall: Weyl of `qθ` implies Weyl of `θ`.

Source: `rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1.
Contract: API
Audit: GREEN -/
theorem weylCriterion_of_mul
    {q b : ℕ} (hq : 1 ≤ q) (hb : 2 ≤ b) {θ : ℝ}
    (h : weylCriterion b ((q : ℝ) * θ)) :
    weylCriterion b θ := by
  intro t ht
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨M0, hM0⟩ := exists_nat_gt (16 * (q : ℝ) / ε ^ 2)
  let M := M0 + 1
  have hM : 0 < M := Nat.succ_pos _
  have hMε : (q : ℝ) / M < (ε / 4) ^ 2 := by
    have hMgt : 16 * (q : ℝ) / ε ^ 2 < M :=
      hM0.trans (Nat.cast_lt.mpr (Nat.lt_succ_self M0))
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
    have : (q : ℝ) / M < ε ^ 2 / 16 := by
      rw [div_lt_div_iff₀ hMpos (by norm_num : (0 : ℝ) < 16)]
      have hmul := mul_lt_mul_of_pos_right hMgt hεsq
      have hcancel : 16 * (q : ℝ) / ε ^ 2 * ε ^ 2 = 16 * q := by
        field_simp [hεsq.ne']
      rw [hcancel] at hmul
      linarith
    have hsq : ε ^ 2 / 16 = (ε / 4) ^ 2 := by ring
    rwa [hsq] at this
  have hH := tendsto_cesaro_H hq hb h ht hM
  let a : ℕ → ℂ := fun n => e ((t : ℝ) * (b : ℝ) ^ n * θ)
  have ha1 : ∀ n, ‖a n‖ ≤ 1 := fun n => (norm_e _).le
  have hv : ∀ n,
      weylKernel b t ((b : ℝ) ^ n * θ) M =
        (∑ j ∈ range M, a (n + j)) / M :=
    fun n => weylKernel_eq_avg b t θ M n
  have hUeq : ∀ N,
      (∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N =
        (∑ j ∈ range M, (∑ n ∈ range N, a (n + j)) / N) / M := by
    intro N
    by_cases hN : N = 0
    · subst hN
      simp
    · have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)
      simp_rw [hv]
      have hswap :
          ∑ n ∈ range N, (∑ j ∈ range M, a (n + j)) / M =
            (∑ j ∈ range M, ∑ n ∈ range N, a (n + j)) / M := by
        have hmul : ∑ n ∈ range N, (∑ j ∈ range M, a (n + j)) / M =
            (∑ n ∈ range N, ∑ j ∈ range M, a (n + j)) / M := by
          simp_rw [div_eq_mul_inv, ← sum_mul]
        rw [hmul]
        congr 1
        rw [sum_comm]
      rw [hswap]
      have hsplit :
          (∑ j ∈ range M, ∑ n ∈ range N, a (n + j)) / M / N =
            (∑ j ∈ range M, (∑ n ∈ range N, a (n + j)) / N) / M := by
        simp_rw [div_eq_mul_inv, sum_mul]
        refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
        ring
      exact hsplit
  have hshift : ∀ N,
      ‖(∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N -
          (∑ n ∈ range N, a n) / N‖ ≤ (2 * (M : ℝ)) / N := by
    intro N
    rw [hUeq]
    have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)
    have hbound : ‖(∑ j ∈ range M, (∑ n ∈ range N, a (n + j)) / N) / M -
        (∑ n ∈ range N, a n) / N‖ ≤
        (∑ j ∈ range M, (2 * (j : ℝ)) / N) / M := by
      have hpt : ∀ j ∈ range M,
          ‖(∑ n ∈ range N, a (n + j)) / N - (∑ n ∈ range N, a n) / N‖ ≤
            (2 * (j : ℝ)) / N :=
        fun j _ => cesaro_shift_sub a j N ha1
      have havg :
          (∑ j ∈ range M, (∑ n ∈ range N, a (n + j)) / N) / M -
              (∑ n ∈ range N, a n) / N =
            (∑ j ∈ range M,
                ((∑ n ∈ range N, a (n + j)) / N - (∑ n ∈ range N, a n) / N)) /
              M := by
        set c := (∑ n ∈ range N, a n) / N
        set u := fun j : ℕ => (∑ n ∈ range N, a (n + j)) / N
        have hsumc : ∑ j ∈ range M, c = (M : ℂ) * c := by
          simp [c, sum_const, nsmul_eq_mul]
        have hMc : (M : ℂ) * c / M = c := by
          field_simp [hM0]
        calc
          (∑ j ∈ range M, u j) / M - c
              = (∑ j ∈ range M, u j) / M - (M : ℂ) * c / M := by
                congr 1
                exact hMc.symm
          _ = ((∑ j ∈ range M, u j) - (M : ℂ) * c) / M := by rw [sub_div]
          _ = ((∑ j ∈ range M, u j) - ∑ j ∈ range M, c) / M := by rw [hsumc]
          _ = (∑ j ∈ range M, (u j - c)) / M := by rw [sum_sub_distrib]
      rw [havg, norm_div]
      have hMnorm : ‖(M : ℂ)‖ = M := by simp
      rw [hMnorm]
      have hsumle :
          ‖∑ j ∈ range M,
              ((∑ n ∈ range N, a (n + j)) / N - (∑ n ∈ range N, a n) / N)‖ ≤
            ∑ j ∈ range M, (2 * (j : ℝ)) / N :=
        (norm_sum_le _ _).trans (sum_le_sum hpt)
      exact div_le_div_of_nonneg_right hsumle (Nat.cast_nonneg M)
    refine hbound.trans ?_
    have hj : ∀ j ∈ range M, (2 * (j : ℝ)) / N ≤ (2 * (M : ℝ)) / N := by
      intro j hj
      have : (j : ℝ) ≤ M := Nat.cast_le.mpr (mem_range.mp hj).le
      have hNnn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
      exact div_le_div_of_nonneg_right (by linarith) hNnn
    have hsum : ∑ j ∈ range M, (2 * (j : ℝ)) / N ≤
        ∑ j ∈ range M, (2 * (M : ℝ)) / N := sum_le_sum hj
    have hconst : ∑ j ∈ range M, (2 * (M : ℝ)) / N = M * ((2 * (M : ℝ)) / N) := by
      simp [sum_const, nsmul_eq_mul]
    have : (∑ j ∈ range M, (2 * (j : ℝ)) / N) / M ≤ (2 * (M : ℝ)) / N := by
      have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
      rw [div_le_iff₀ hMpos]
      have := hsum.trans_eq hconst
      have : M * ((2 * (M : ℝ)) / N) = M * (2 * M / N) := rfl
      linarith
    exact this
  have hHreal :
      Tendsto (fun N : ℕ =>
        (∑ n ∈ range N,
            ∑ r ∈ range q, weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M) / N)
        atTop (𝓝 ((q : ℝ) / M)) := by
    have hC := hH
    have heq : (fun N : ℕ =>
        (((∑ n ∈ range N,
            ∑ r ∈ range q, weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M) : ℝ) /
          N : ℂ)) =
        fun N =>
          (((∑ n ∈ range N,
              ∑ r ∈ range q,
                weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M) / N : ℝ) : ℂ) := by
      funext N
      simp
    have : Tendsto (fun N : ℕ =>
        (((∑ n ∈ range N,
            ∑ r ∈ range q, weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M) /
          N : ℝ) : ℂ)) atTop (𝓝 (((q : ℝ) / M : ℝ) : ℂ)) := by
      rw [heq] at hC
      simpa using hC
    exact Filter.tendsto_ofReal_iff.1 this
  have hδ : (0 : ℝ) < (ε / 4) ^ 2 := sq_pos_of_pos (div_pos hε (by norm_num))
  filter_upwards [hHreal.eventually (Metric.ball_mem_nhds ((q : ℝ) / M) hδ),
    (tendsto_const_div_atTop_nhds_zero_nat (2 * (M : ℝ))).eventually
      (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))] with N hHclose hshiftN
  have hUle : ‖(∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N‖ ^ 2 ≤
      (∑ n ∈ range N, weylKernelSq b t ((b : ℝ) ^ n * θ) M) / N :=
    cesaro_kernel_sq_le b t θ M N
  have hFle : (∑ n ∈ range N, weylKernelSq b t ((b : ℝ) ^ n * θ) M) / N ≤
      (∑ n ∈ range N,
          ∑ r ∈ range q, weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M) / N := by
    have hpt : ∀ n ∈ range N,
        weylKernelSq b t ((b : ℝ) ^ n * θ) M ≤
          ∑ r ∈ range q, weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M :=
      fun n _ => weylKernelSq_le_shift hq b t M _
    refine div_le_div_of_nonneg_right (sum_le_sum hpt) (Nat.cast_nonneg N)
  have hHavg :
      (∑ n ∈ range N,
          ∑ r ∈ range q, weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M) / N <
        (q : ℝ) / M + (ε / 4) ^ 2 := by
    set avg :=
      (∑ n ∈ range N,
          ∑ r ∈ range q, weylKernelSq b t ((b : ℝ) ^ n * θ + r / q) M) / N
    have habs : |avg - (q : ℝ) / M| < (ε / 4) ^ 2 := by
      simpa [Real.dist_eq, avg] using hHclose
    have hle : avg - (q : ℝ) / M ≤ |avg - (q : ℝ) / M| := le_abs_self _
    have hlt : avg - (q : ℝ) / M < (ε / 4) ^ 2 := lt_of_le_of_lt hle habs
    linarith [hlt]
  have hU2 : ‖(∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N‖ ^ 2 <
      (ε / 2) ^ 2 := by
    have hlt := hUle.trans hFle |>.trans_lt hHavg
    have hsum : (q : ℝ) / M + (ε / 4) ^ 2 < 2 * (ε / 4) ^ 2 := by
      linarith [hMε]
    have h2 : 2 * (ε / 4) ^ 2 = ε ^ 2 / 8 := by ring
    have hhalf : ε ^ 2 / 8 < (ε / 2) ^ 2 := by
      have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
      have : (ε / 2) ^ 2 = ε ^ 2 / 4 := by ring
      rw [this]
      exact div_lt_div_of_pos_left hεsq (by norm_num) (by norm_num)
    exact (hlt.trans hsum).trans_eq h2 |>.trans hhalf
  have hU : ‖(∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N‖ < ε / 2 :=
    (sq_lt_sq₀ (norm_nonneg _) (div_nonneg hε.le (by norm_num))).1 hU2
  have hSshift :
      ‖(∑ n ∈ range N, a n) / N -
          (∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N‖ <
        ε / 2 := by
    have hle := hshift N
    have : (2 * (M : ℝ)) / N < ε / 2 := by
      simpa [Real.dist_eq] using hshiftN
    exact lt_of_le_of_lt (by simpa [norm_sub_rev] using hle) this
  have : ‖(∑ n ∈ range N, a n) / N‖ < ε := by
    have := (norm_add_le
        ((∑ n ∈ range N, a n) / N -
          (∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N)
        ((∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N)).trans_lt
      (add_lt_add hSshift hU)
    have hdecomp :
        ((∑ n ∈ range N, a n) / N -
            (∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N) +
          (∑ n ∈ range N, weylKernel b t ((b : ℝ) ^ n * θ) M) / N =
          (∑ n ∈ range N, a n) / N := by
      ring
    simpa [hdecomp] using this
  simpa [a, dist_zero_right] using this

/-- Weyl-normal numbers are irrational: a rational `p/q` with frequency
`τ = q` makes every character `1`, so the Cesàro mean is `1`.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
theorem weylCriterion_irrational {b : ℕ} {θ : ℝ}
    (h : weylCriterion b θ) : Irrational θ := by
  intro hθ
  obtain ⟨q, rfl⟩ := hθ
  have hτ : (q.den : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr q.den_ne_zero
  have hone : ∀ n : ℕ,
      e (((q.den : ℤ) : ℝ) * (b : ℝ) ^ n * (q : ℝ)) = 1 := by
    intro n
    have hden : ((q.den : ℝ) * (q : ℝ) = (q.num : ℝ)) := by
      exact_mod_cast q.den_mul_eq_num
    have harg :
        ((q.den : ℤ) : ℝ) * (b : ℝ) ^ n * (q : ℝ) =
          ((q.num * (b : ℤ) ^ n : ℤ) : ℝ) := by
      calc
        ((q.den : ℤ) : ℝ) * (b : ℝ) ^ n * (q : ℝ)
            = (b : ℝ) ^ n * (((q.den : ℤ) : ℝ) * (q : ℝ)) := by ring
        _ = (b : ℝ) ^ n * (q.num : ℝ) := by
              simpa using congrArg (fun t => (b : ℝ) ^ n * t) hden
        _ = ((q.num * (b : ℤ) ^ n : ℤ) : ℝ) := by
              push_cast
              ring
    rw [harg, e_int]
  have heq :
      (fun N : ℕ =>
        (∑ n ∈ range N,
            e (((q.den : ℤ) : ℝ) * (b : ℝ) ^ n * (q : ℝ))) / N) =
        fun N => (∑ n ∈ range N, (1 : ℂ)) / N := by
    funext N
    congr 1
    exact sum_congr rfl fun n _ => hone n
  have h1 : Tendsto (fun N : ℕ => (∑ n ∈ range N, (1 : ℂ)) / N) atTop (𝓝 1) :=
    tendsto_one_div_nat
  have h0 := h (q.den : ℤ) hτ
  rw [heq] at h0
  exact one_ne_zero (tendsto_nhds_unique h1 h0)

/-- Clearing one rational against the product of three denominators.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
private theorem den_prod_mul_rat (q r s : ℚ) :
    ((q.den * r.den * s.den : ℕ) : ℝ) * (q : ℝ) =
      ((q.num * (r.den * s.den) : ℤ) : ℝ) := by
  have hden : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    exact_mod_cast q.den_mul_eq_num
  push_cast
  calc
    (q.den * r.den * s.den : ℝ) * (q : ℝ)
        = (r.den * s.den : ℝ) * ((q.den : ℝ) * (q : ℝ)) := by ring
    _ = (r.den * s.den : ℝ) * (q.num : ℝ) := by rw [hden]
    _ = (q.num * (r.den * s.den) : ℝ) := by ring

/-- A vanishing integer multiple of a numerator forces the rational to vanish.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
private theorem rat_eq_zero_of_num_mul_dens (q r s : ℚ)
    (h : q.num * ((r.den : ℤ) * s.den) = 0) : q = 0 := by
  have hden : ((r.den : ℤ) * s.den) ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr r.den_ne_zero)
      (Int.natCast_ne_zero.mpr s.den_ne_zero)
  have hnum : q.num = 0 := (mul_eq_zero.mp h).resolve_right hden
  exact Rat.zero_iff_num_zero.mpr hnum

/-- Transport Weyl along an equality of phases.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
private theorem weylCriterion_of_eq {b : ℕ} {θ φ : ℝ} (heq : θ = φ)
    (h : weylCriterion b θ) : weylCriterion b φ :=
  heq ▸ h

/-- Integer linear relations between a Weyl-normal `x` and a non-Weyl
irrational `y` are trivial.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
theorem no_int_relation_of_normal_notNormal
    {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    (hx : weylCriterion b x) (hy : Irrational y) (hyn : ¬ weylCriterion b y)
    (A B C : ℤ) (hrel : (A : ℝ) + B * x + C * y = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  by_cases hB : B = 0
  · by_cases hC : C = 0
    · have hA : (A : ℝ) = 0 := by
        simpa [hB, hC] using hrel
      exact ⟨Int.cast_eq_zero.mp hA, hB, hC⟩
    · have hC0 : (C : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hC
      have hyeq : y = ((-A : ℤ) : ℝ) / (C : ℝ) := by
        have : y * (C : ℝ) = ((-A : ℤ) : ℝ) := by
          simp [hB] at hrel
          push_cast
          linarith
        exact eq_div_of_mul_eq hC0 this
      exact (hy.ne_rational (-A) C hyeq).elim
  · by_cases hC : C = 0
    · have hxirr : Irrational x := weylCriterion_irrational hx
      have hB0 : (B : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hB
      have hxeq : x = ((-A : ℤ) : ℝ) / (B : ℝ) := by
        have : x * (B : ℝ) = ((-A : ℤ) : ℝ) := by
          simp [hC] at hrel
          push_cast
          linarith
        exact eq_div_of_mul_eq hB0 this
      exact (hxirr.ne_rational (-A) B hxeq).elim
    · have hBx : weylCriterion b (B * x) := weylCriterion_int_mul hB hx
      have hnegBx : weylCriterion b (-(B * x)) := weylCriterion_neg hBx
      have hCy : weylCriterion b (C * y) := by
        refine weylCriterion_of_eq ?_ (weylCriterion_add_int (-A) hnegBx)
        have hcast : ((-A : ℤ) : ℝ) = - (A : ℝ) := by simp
        rw [hcast]
        linarith
      have habs : weylCriterion b ((C.natAbs : ℝ) * y) :=
        weylCriterion_natAbs_mul hCy
      have hq : 1 ≤ C.natAbs :=
        Nat.one_le_iff_ne_zero.mpr (mt Int.natAbs_eq_zero.mp hC)
      exact (hyn (weylCriterion_of_mul hq hb habs)).elim

/-- Weyl-normal `x` and irrational non-Weyl `y` give `ℚ`-independence of
`1, x, y` after clearing denominators.

Source: `rounds/round98/04_gpt_lean_delta_and_normality_separation.md` §1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(Wall via existing `weylCriterion_of_mul`).
Contract: API
Audit: GREEN -/
theorem linearIndependent_one_normal_notNormal
    {b : ℕ} (hb : 2 ≤ b) {x y : ℝ}
    (hx : weylCriterion b x) (hy : Irrational y) (hyn : ¬ weylCriterion b y) :
    LinearIndependent ℚ ![ (1 : ℝ), x, y ] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsum : (g 0 : ℝ) + (g 1 : ℝ) * x + (g 2 : ℝ) * y = 0 := by
    simp [Fin.sum_univ_three, Algebra.smul_def, mul_one] at hg
    exact hg
  let D : ℕ := (g 0).den * (g 1).den * (g 2).den
  let A : ℤ := (g 0).num * ((g 1).den * (g 2).den)
  let B : ℤ := (g 1).num * ((g 0).den * (g 2).den)
  let C : ℤ := (g 2).num * ((g 0).den * (g 1).den)
  have hA : (D : ℝ) * (g 0 : ℝ) = A := den_prod_mul_rat (g 0) (g 1) (g 2)
  have hB : (D : ℝ) * (g 1 : ℝ) = B := by
    have h := den_prod_mul_rat (g 1) (g 0) (g 2)
    have hperm : ((g 0).den * (g 1).den * (g 2).den : ℕ) =
        (g 1).den * (g 0).den * (g 2).den := by ring
    dsimp [D, B]
    rw [hperm]
    exact h
  have hC : (D : ℝ) * (g 2 : ℝ) = C := by
    have h := den_prod_mul_rat (g 2) (g 0) (g 1)
    have hperm : ((g 0).den * (g 1).den * (g 2).den : ℕ) =
        (g 2).den * (g 0).den * (g 1).den := by ring
    dsimp [D, C]
    rw [hperm]
    exact h
  have hrel : (A : ℝ) + B * x + C * y = 0 := by
    have hexp :
        (D : ℝ) * ((g 0 : ℝ) + (g 1 : ℝ) * x + (g 2 : ℝ) * y) =
          (A : ℝ) + B * x + C * y := by
      calc
        (D : ℝ) * ((g 0 : ℝ) + (g 1 : ℝ) * x + (g 2 : ℝ) * y)
            = (D : ℝ) * (g 0 : ℝ) + (D : ℝ) * ((g 1 : ℝ) * x) +
                (D : ℝ) * ((g 2 : ℝ) * y) := by ring
        _ = (A : ℝ) + ((D : ℝ) * (g 1 : ℝ)) * x +
                ((D : ℝ) * (g 2 : ℝ)) * y := by
              rw [hA]
              ring
        _ = (A : ℝ) + B * x + C * y := by
              rw [hB, hC]
    have hD0 : (D : ℝ) * ((g 0 : ℝ) + (g 1 : ℝ) * x + (g 2 : ℝ) * y) = 0 := by
      simp [hsum]
    linarith
  obtain ⟨hA0, hB0, hC0⟩ :=
    no_int_relation_of_normal_notNormal hb hx hy hyn A B C hrel
  have hg0 : g 0 = 0 := rat_eq_zero_of_num_mul_dens (g 0) (g 1) (g 2) hA0
  have hg1 : g 1 = 0 := rat_eq_zero_of_num_mul_dens (g 1) (g 0) (g 2) hB0
  have hg2 : g 2 = 0 := rat_eq_zero_of_num_mul_dens (g 2) (g 0) (g 1) hC0
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

end PrimeGapNormality.Prime
