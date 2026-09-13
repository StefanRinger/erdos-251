import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic

/-!
# Deterministic grid Fourier and integer-frequency Weyl criterion

Source: `rounds/round97/02_gpt_khl_normality_extension.md` Lemma 5.1, Lemma 10.1;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3;
`lean/PRIME_NORMALITY.md` Fourier.
Contract: API
Audit: GREEN

Mathlib v4.33.1 has no real `Normal` class. Base-`b` normality is the
Weyl criterion on integer frequencies. Lemma 10.1 (`weylCriterion_of_mul`)
is omitted; the finite Wall packaging did not close in this module.
No KHL end theorem.
-/

open Finset
open Filter (Tendsto atTop)
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 400000

/-! ### Circle character -/

/-- Circle character `e(t) = exp(2π i t)`.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` Lemma 5.1;
`lean/PRIME_NORMALITY.md` Fourier.
Contract: API
Audit: GREEN -/
noncomputable def e (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * t)

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem e_zero : e 0 = 1 := by
  unfold e
  simp [Complex.exp_zero]

private theorem e_int (n : ℤ) : e n = 1 := by
  unfold e
  simp only [Complex.ofReal_intCast]
  have h : (2 * Real.pi * Complex.I * (n : ℂ)) = n * (2 * Real.pi * Complex.I) := by
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private theorem e_nat_mul (n : ℕ) (x : ℝ) : e ((n : ℝ) * x) = e x ^ n := by
  unfold e
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  have h : (2 * Real.pi * Complex.I * ((n : ℂ) * x)) =
      (n : ℂ) * (2 * Real.pi * Complex.I * x) := by
    ring
  rw [h, Complex.exp_nat_mul]

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

private theorem two_pi_I_mul (x : ℝ) :
    (2 * Real.pi * Complex.I * (x : ℂ) : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) := by
  simp [mul_comm, mul_left_comm, Complex.ofReal_mul]

private theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [two_pi_I_mul, Complex.norm_exp_I_mul_ofReal]

private theorem norm_e_sub_one_eq (δ : ℝ) : ‖e δ - 1‖ = 2 * |Real.sin (Real.pi * δ)| := by
  unfold e
  rw [two_pi_I_mul, Complex.norm_exp_I_mul_ofReal_sub_one]
  have : (2 * Real.pi * δ) / 2 = Real.pi * δ := by ring
  simp [this, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

private theorem abs_sin_pi_ge {δ : ℝ} (hδ : |δ| ≤ 1 / 2) :
    2 * |δ| ≤ |Real.sin (Real.pi * δ)| := by
  have hx0 : 0 ≤ Real.pi * |δ| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
  have hx1 : Real.pi * |δ| ≤ Real.pi / 2 := by
    have : |δ| * 2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hδ
    nlinarith [Real.pi_pos]
  have hsin : (2 / Real.pi) * (Real.pi * |δ|) ≤ Real.sin (Real.pi * |δ|) :=
    Real.mul_le_sin hx0 hx1
  have hsimp : (2 / Real.pi) * (Real.pi * |δ|) = 2 * |δ| := by
    field_simp [Real.pi_ne_zero]
  have hnn : 0 ≤ Real.sin (Real.pi * |δ|) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (hx1.trans (by linarith [Real.pi_pos]))
  have hbound : |Real.pi * δ| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
    nlinarith [Real.pi_pos, hδ]
  have habs : |Real.sin (Real.pi * δ)| = Real.sin (Real.pi * |δ|) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hbound, abs_mul,
      abs_of_nonneg Real.pi_pos.le]
  linarith

private theorem norm_e_sub_one_ge {δ : ℝ} (hδ : |δ| ≤ 1 / 2) :
    4 * |δ| ≤ ‖e δ - 1‖ := by
  rw [norm_e_sub_one_eq]
  have := abs_sin_pi_ge hδ
  linarith

private theorem norm_e_sub_one_le (δ : ℝ) : ‖e δ - 1‖ ≤ 2 * Real.pi * |δ| := by
  unfold e
  rw [two_pi_I_mul]
  have hle := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * δ)
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg Real.pi_pos.le, mul_comm, mul_left_comm,
    mul_assoc] using hle

private theorem norm_e_sub_e (s t : ℝ) : ‖e t - e s‖ ≤ 2 * Real.pi * |t - s| := by
  have h : e t - e s = e s * (e (t - s) - 1) := by
    have ht : t = s + (t - s) := by ring
    rw [ht, e_add]
    ring
  rw [h, norm_mul, norm_e, one_mul]
  exact norm_e_sub_one_le (t - s)

private theorem norm_div_nat (z : ℂ) (n : ℕ) : ‖z / n‖ = ‖z‖ / n := by
  rw [norm_div]
  simp

private theorem norm_div_card_le_one {α : Type*} (s : Finset α) (f : α → ℂ)
    (hf : ∀ x ∈ s, ‖f x‖ ≤ 1) :
    ‖(∑ x ∈ s, f x) / (s.card : ℂ)‖ ≤ 1 := by
  by_cases h0 : s.card = 0
  · simp [h0]
  · have hpos : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    rw [norm_div_nat]
    have hsum : ‖∑ x ∈ s, f x‖ ≤ ∑ x ∈ s, ‖f x‖ := norm_sum_le _ _
    have h1 : ∑ x ∈ s, ‖f x‖ ≤ ∑ x ∈ s, (1 : ℝ) := sum_le_sum hf
    have hcard : (∑ x ∈ s, (1 : ℝ)) = s.card := by simp [sum_const]
    have : ‖∑ x ∈ s, f x‖ ≤ s.card := hsum.trans (h1.trans_eq hcard)
    exact (div_le_one hpos).mpr this

/-! ### Weyl criterion -/

/-- Integer-frequency Weyl criterion for base-`b` normality.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` (9.6);
`lean/PRIME_NORMALITY.md` Fourier.
Contract: API
Audit: GREEN -/
def weylCriterion (b : ℕ) (θ : ℝ) : Prop :=
  ∀ τ : ℤ, τ ≠ 0 →
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, e ((τ : ℝ) * (b : ℝ) ^ n * θ)) / N)
      atTop (𝓝 0)

/-! ### Deterministic grid Fourier (Lemma 5.1) -/

/-- Grid cell of width `h` and index `r`.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` Lemma 5.1;
`lean/PRIME_NORMALITY.md` Fourier.
Contract: API
Audit: GREEN -/
def cell (r h : ℕ) (u : ℕ) : Prop :=
  r * h ≤ u ∧ u < (r + 1) * h

instance (r h : ℕ) : DecidablePred (cell r h) :=
  fun u => inferInstanceAs (Decidable (r * h ≤ u ∧ u < (r + 1) * h))

/-- Absolute constant in the Riemann-sum Fourier bound.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` Lemma 5.1;
`lean/PRIME_NORMALITY.md` Fourier.
Contract: API
Audit: GREEN -/
def gridFourierC : ℝ := 80

private theorem abs_nat_cast (n : ℕ) : |(n : ℝ)| = n :=
  abs_of_nonneg (Nat.cast_nonneg n)

private theorem norm_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x :=
  (Complex.norm_real x).trans (abs_of_nonneg hx)

private theorem norm_add4 (a b c d : ℂ) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h2 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h3 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  exact h1.trans (add_le_add (h2.trans (add_le_add h3 (le_refl _))) (le_refl _))

private theorem mul_div_eq_sub_mod (n d : ℕ) :
    d * (n / d) = n - n % d := by
  calc
    d * (n / d) = d * (n / d) + n % d - n % d :=
      (Nat.add_sub_cancel _ _).symm
    _ = n - n % d := by rw [Nat.div_add_mod n d]

private theorem add_one_mul_div (n d : ℕ) :
    (n / d + 1) * d = n - n % d + d := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d), mul_div_eq_sub_mod]

private theorem lt_mul_succ_div {u d : ℕ} (hd : 0 < d) :
    u < (u / d + 1) * d := by
  have hmod : u % d < d := Nat.mod_lt u hd
  have hsum : d * (u / d) + u % d = u := Nat.div_add_mod u d
  have hlt : u < d * (u / d) + d := by
    have := Nat.add_lt_add_left hmod (d * (u / d))
    rwa [hsum] at this
  have hrw : (u / d + 1) * d = d * (u / d) + d := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  rwa [hrw]

private theorem mul_div_le_comm (u d : ℕ) : u / d * d ≤ u := by
  simpa [Nat.mul_comm] using Nat.mul_div_le u d

private theorem cell_div_eq {r h u : ℕ}
    (hlo : r * h ≤ u) (hhi : u < (r + 1) * h) : u / h = r :=
  Nat.div_eq_of_lt_le hlo hhi

private theorem card_Ico_cast {a b : ℕ} (h : a ≤ b) :
    ((Ico a b).card : ℝ) = (b : ℝ) - a := by
  rw [Nat.card_Ico, Nat.cast_sub h]

private theorem rMin_mul_h_gt {h Wleft : ℕ} (hh : 0 < h) :
    Wleft < (Wleft / h + 1) * h := by
  have hform : (Wleft / h + 1) * h = Wleft - Wleft % h + h :=
    add_one_mul_div Wleft h
  rw [hform]
  have hm : Wleft % h ≤ Wleft := Nat.mod_le Wleft h
  have hsplit : Wleft = Wleft - Wleft % h + Wleft % h :=
    (Nat.sub_add_cancel hm).symm
  have : Wleft - Wleft % h + Wleft % h < Wleft - Wleft % h + h :=
    Nat.add_lt_add_left (Nat.mod_lt Wleft hh) _
  rwa [← hsplit] at this

private theorem grid_rMin_lt {Wleft Wright h : ℕ} (hh : 0 < h)
    (hle4 : Wleft + 4 * h ≤ Wright) :
    Wleft / h + 1 < Wright / h := by
  have hdiv : (Wleft + 4 * h) / h ≤ Wright / h := Nat.div_le_div_right hle4
  have hdiv' : Wleft / h + 4 ≤ Wright / h := by
    rwa [Nat.add_mul_div_right Wleft 4 hh] at hdiv
  have hlt : Wleft / h + 1 < Wleft / h + 4 :=
    Nat.add_lt_add_left (by norm_num : (1 : ℕ) < 4) _
  exact hlt.trans_le hdiv'

private theorem cell_block_subset {h Wleft Wright r : ℕ} (hh : 0 < h)
    (hr : r ∈ Ico (Wleft / h + 1) (Wright / h)) :
    Ico (r * h) ((r + 1) * h) ⊆ Ioo Wleft Wright := by
  intro u hu
  rw [mem_Ico] at hu hr
  rw [mem_Ioo]
  constructor
  · have h1 : Wleft < (Wleft / h + 1) * h := rMin_mul_h_gt hh
    have h2 : (Wleft / h + 1) * h ≤ r * h := Nat.mul_le_mul_right h hr.1
    exact h1.trans_le (h2.trans hu.1)
  · have h1 : r + 1 ≤ Wright / h := Nat.succ_le_of_lt hr.2
    have h2 : (r + 1) * h ≤ (Wright / h) * h := Nat.mul_le_mul_right h h1
    have h3 : (Wright / h) * h ≤ Wright := by
      simpa [Nat.mul_comm] using Nat.mul_div_le Wright h
    exact hu.2.trans_le (h2.trans h3)

private theorem cell_pairwise_disjoint (A : Finset ℕ) (h : ℕ) (s : Finset ℕ) :
    Set.PairwiseDisjoint (s : Set ℕ) (fun r => A.filter (cell r h)) := by
  intro r _ s' _ hrs
  refine disjoint_left.mpr fun u hur hut => ?_
  have hr' := (mem_filter.mp hur).2
  have hs' := (mem_filter.mp hut).2
  exact hrs (by
    rcases hr' with ⟨hr1, hr2⟩
    rcases hs' with ⟨hs1, hs2⟩
    exact (cell_div_eq hr1 hr2).symm.trans (cell_div_eq hs1 hs2))

private theorem grid_cell_span_eq {h Wleft Wright : ℕ}
    (_hh : 0 < h) (_hIco : Wleft / h + 1 ≤ Wright / h) :
    h * (Wright / h - (Wleft / h + 1)) =
      Wright - Wright % h - (Wleft - Wleft % h) - h := by
  have hmul :
      h * (Wright / h - (Wleft / h + 1)) =
        h * (Wright / h) - h * (Wleft / h + 1) :=
    Nat.mul_sub_left_distrib h (Wright / h) (Wleft / h + 1)
  have hW : h * (Wright / h) = Wright - Wright % h :=
    mul_div_eq_sub_mod Wright h
  have hL0 : h * (Wleft / h) = Wleft - Wleft % h :=
    mul_div_eq_sub_mod Wleft h
  have hL : h * (Wleft / h + 1) = h * (Wleft / h) + h := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hmul, hL, hW, hL0]
  exact Nat.sub_add_eq (Wright - Wright % h) (Wleft - Wleft % h) h

private theorem grid_span_cast {h Wleft Wright : ℕ}
    (hh : 0 < h) (hIco : Wleft / h + 1 ≤ Wright / h) :
    ((h * (Wright / h - (Wleft / h + 1)) : ℕ) : ℝ) =
      (Wright : ℝ) - (Wright % h : ℝ) - ((Wleft : ℝ) - (Wleft % h : ℝ)) -
        (h : ℝ) := by
  have heq := grid_cell_span_eq hh hIco
  have hWmod : Wright % h ≤ Wright := Nat.mod_le Wright h
  have hLmod : Wleft % h ≤ Wleft := Nat.mod_le Wleft h
  have hmid : Wleft - Wleft % h ≤ Wright - Wright % h := by
    have hdiv : Wleft / h ≤ Wright / h :=
      Nat.le_trans (Nat.le_succ (Wleft / h)) hIco
    have := Nat.mul_le_mul_left h hdiv
    simpa [mul_div_eq_sub_mod] using this
  have hmidh : h ≤ Wright - Wright % h - (Wleft - Wleft % h) := by
    have hmul := Nat.mul_le_mul_left h hIco
    have hL1 : h * (Wleft / h + 1) = Wleft - Wleft % h + h := by
      rw [Nat.mul_comm]
      exact add_one_mul_div Wleft h
    have hW : h * (Wright / h) = Wright - Wright % h :=
      mul_div_eq_sub_mod Wright h
    rw [hL1, hW] at hmul
    exact (Nat.le_sub_iff_add_le' hmid).mpr hmul
  rw [heq, Nat.cast_sub hmidh, Nat.cast_sub hmid, Nat.cast_sub hWmod,
    Nat.cast_sub hLmod]

private theorem grid_span_ge {h Wleft Wright : ℕ}
    (hh : 0 < h) (hIco : Wleft / h + 1 ≤ Wright / h) :
    ((Wright : ℝ) - Wleft) - 2 * h + 1 ≤
      (h : ℝ) * ((Wright / h : ℕ) - (Wleft / h + 1 : ℕ)) := by
  have hcast := grid_span_cast hh hIco
  have hWm : (Wright % h : ℝ) ≤ (h : ℝ) - 1 := by
    have hle : Wright % h ≤ h - 1 := Nat.le_pred_of_lt (Nat.mod_lt Wright hh)
    have h1 : 1 ≤ h := Nat.succ_le_of_lt hh
    have : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
      rw [Nat.cast_sub h1, Nat.cast_one]
    exact (Nat.cast_le.mpr hle).trans_eq this
  have hLm : (0 : ℝ) ≤ (Wleft % h : ℝ) := Nat.cast_nonneg _
  have hw : ((h * (Wright / h - (Wleft / h + 1)) : ℕ) : ℝ) =
      (h : ℝ) * ((Wright / h : ℕ) - (Wleft / h + 1 : ℕ)) := by
    rw [Nat.cast_mul, Nat.cast_sub hIco]
  linarith [hcast, hw, hWm, hLm]

private theorem grid_span_le {h Wleft Wright : ℕ}
    (hh : 0 < h) (hIco : Wleft / h + 1 ≤ Wright / h) :
    (h : ℝ) * ((Wright / h : ℕ) - (Wleft / h + 1 : ℕ)) ≤
      (Wright : ℝ) - Wleft := by
  have hcast := grid_span_cast hh hIco
  have hWm : (0 : ℝ) ≤ (Wright % h : ℝ) := Nat.cast_nonneg _
  have hLm : (Wleft % h : ℝ) ≤ (h : ℝ) - 1 := by
    have hle : Wleft % h ≤ h - 1 := Nat.le_pred_of_lt (Nat.mod_lt Wleft hh)
    have h1 : 1 ≤ h := Nat.succ_le_of_lt hh
    have : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
      rw [Nat.cast_sub h1, Nat.cast_one]
    exact (Nat.cast_le.mpr hle).trans_eq this
  have hw : ((h * (Wright / h - (Wleft / h + 1)) : ℕ) : ℝ) =
      (h : ℝ) * ((Wright / h : ℕ) - (Wleft / h + 1 : ℕ)) := by
    rw [Nat.cast_mul, Nat.cast_sub hIco]
  linarith [hcast, hw, hWm, hLm]

private theorem geom_char_bound {c : ℝ} {h n : ℕ}
    (hh : 0 < h) (_hn : 0 < n) (hc : c ≠ 0)
    (hsmall : |c| * h < 1 / 2) :
    ‖∑ k ∈ range n, e (c * ((k : ℝ) * h))‖ ≤ 1 / (2 * |c| * h) := by
  have hδ : |c * (h : ℝ)| < 1 / 2 := by
    simpa [abs_mul, abs_nat_cast h] using hsmall
  have hω : e (c * h) ≠ 1 := by
    intro h1
    obtain ⟨m, hm⟩ := (e_eq_one_iff (c * h)).mp h1
    have habs : |(m : ℝ)| < 1 / 2 := by simpa [hm] using hδ
    have hm0 : m = 0 := by
      have : |(m : ℝ)| < 1 := habs.trans (by norm_num)
      have : |m| < 1 := by exact_mod_cast this
      exact Int.abs_lt_one_iff.mp this
    have hz : c * h = (0 : ℝ) := by simpa [hm0] using hm
    have : |c| * h = 0 := by
      simpa [abs_mul, abs_nat_cast h] using congrArg abs hz
    have hpos : 0 < |c| * h := mul_pos (abs_pos.mpr hc) (Nat.cast_pos.mpr hh)
    linarith
  have hsum : ∑ k ∈ range n, e (c * ((k : ℝ) * h)) =
      ∑ k ∈ range n, e (c * h) ^ k := by
    refine sum_congr rfl fun k _ => ?_
    have : (k : ℝ) * (c * h) = c * ((k : ℝ) * h) := by ring
    rw [← this, e_nat_mul]
  rw [hsum, geom_sum_eq hω n, norm_div]
  have hnum : ‖e (c * h) ^ n - 1‖ ≤ 2 := by
    have hnrm : ‖e (c * h) ^ n‖ = 1 := by
      rw [← e_nat_mul, norm_e]
    calc
      ‖e (c * h) ^ n - 1‖ ≤ ‖e (c * h) ^ n‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 1 + 1 := by simp [hnrm]
      _ = 2 := by norm_num
  have hden : 4 * |c * (h : ℝ)| ≤ ‖e (c * h) - 1‖ :=
    norm_e_sub_one_ge hδ.le
  have hpos : 0 < 4 * |c * (h : ℝ)| := by
    have : 0 < |c| * h := mul_pos (abs_pos.mpr hc) (Nat.cast_pos.mpr hh)
    simpa [abs_mul, abs_nat_cast h] using this
  have hle : ‖e (c * h) ^ n - 1‖ / ‖e (c * h) - 1‖ ≤
      2 / (4 * |c * (h : ℝ)|) := by
    have h1 : ‖e (c * h) ^ n - 1‖ / ‖e (c * h) - 1‖ ≤ 2 / ‖e (c * h) - 1‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    have h2 : 2 / ‖e (c * h) - 1‖ ≤ 2 / (4 * |c * (h : ℝ)|) :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hpos hden
    exact h1.trans h2
  have hsimp : 2 / (4 * |c * (h : ℝ)|) = 1 / (2 * |c| * h) := by
    have : |c * (h : ℝ)| = |c| * h := by
      simp [abs_mul, abs_nat_cast h]
    rw [this]
    field_simp
    ring
  exact hle.trans_eq hsimp

private theorem grid_window_card_lower
    {A : Finset ℕ} {h : ℕ} (hh : 0 < h) {v η : ℝ}
    (_hη : 0 ≤ η) (hv : 0 < v) (hηlt : η < 1 / 2)
    (hcell : ∀ r : ℕ, |(((A.filter (cell r h)).card : ℝ) - v * h)| ≤ η * v * h)
    {Wleft Wright : ℕ}
    (hlen : (h : ℝ) ≤ ((Wright : ℝ) - (Wleft : ℝ)) / 4) :
    v * ((Wright : ℝ) - Wleft) / 4 ≤
      ((A.filter (fun u => Wleft < u ∧ u < Wright)).card : ℝ) := by
  classical
  set w : ℝ := (Wright : ℝ) - (Wleft : ℝ)
  set W : Finset ℕ := A.filter (fun u => Wleft < u ∧ u < Wright)
  have hw : 0 < w := by
    have : (0 : ℝ) < 4 * h := mul_pos (by norm_num) (Nat.cast_pos.mpr hh)
    linarith
  have hle4 : Wleft + 4 * h ≤ Wright := by
    have : (Wleft : ℝ) + 4 * h ≤ Wright := by linarith
    exact_mod_cast this
  have hrMin : Wleft / h + 1 < Wright / h := grid_rMin_lt hh hle4
  set rMin : ℕ := Wleft / h + 1
  set rMax : ℕ := Wright / h
  have hIco : rMin < rMax := hrMin
  have hinterPts :
      (Ico rMin rMax).biUnion (fun r => A.filter (cell r h)) ⊆ W := by
    intro u hu
    obtain ⟨r, hr, huA⟩ := mem_biUnion.mp hu
    have huI : u ∈ Ico (r * h) ((r + 1) * h) := by
      simpa [cell, mem_Ico] using (mem_filter.mp huA).2
    have huW : u ∈ Ioo Wleft Wright := cell_block_subset hh hr huI
    exact mem_filter.mpr ⟨(mem_filter.mp huA).1, mem_Ioo.mp huW⟩
  have hcard_cell_ge : ∀ r,
      (1 - η) * v * h ≤ ((A.filter (cell r h)).card : ℝ) := by
    intro r
    linarith [abs_le.mp (hcell r)]
  have hdisj := cell_pairwise_disjoint A h (Ico rMin rMax)
  have hinter_ge :
      (1 - η) * v * ((h : ℝ) * (rMax - rMin)) ≤
        (((Ico rMin rMax).biUnion (fun r => A.filter (cell r h))).card : ℝ) := by
    have hsum : (∑ r ∈ Ico rMin rMax, ((A.filter (cell r h)).card : ℝ)) ≥
        ∑ r ∈ Ico rMin rMax, (1 - η) * v * h :=
      sum_le_sum fun r _ => hcard_cell_ge r
    have hsumc : (∑ r ∈ Ico rMin rMax, (1 - η) * v * h) =
        (1 - η) * v * h * (rMax - rMin) := by
      simp only [sum_const, nsmul_eq_mul]
      rw [card_Ico_cast hIco.le]
      ring
    have hcast :
        (((Ico rMin rMax).biUnion (fun r => A.filter (cell r h))).card : ℝ) =
          ∑ r ∈ Ico rMin rMax, ((A.filter (cell r h)).card : ℝ) := by
      rw [card_biUnion hdisj]
      exact Nat.cast_sum _ _
    have hrw : (1 - η) * v * h * (rMax - rMin) =
        (1 - η) * v * ((h : ℝ) * (rMax - rMin)) := by ring
    linarith
  have hinter_le :
      (((Ico rMin rMax).biUnion (fun r => A.filter (cell r h))).card : ℝ) ≤
        (W.card : ℝ) :=
    Nat.cast_le.mpr (card_le_card hinterPts)
  have hspan : w / 2 ≤ (h : ℝ) * (rMax - rMin) := by
    have h1 := grid_span_ge hh hIco.le
    have h2 : w / 2 ≤ w - 2 * h + 1 := by
      have : (4 : ℝ) * h ≤ w := by linarith
      linarith
    linarith [h1, h2]
  have hnn : 0 ≤ (1 - η) * v :=
    mul_nonneg (by linarith [hηlt] : (0 : ℝ) ≤ 1 - η) hv.le
  have hmid : (1 - η) * v * (w / 2) ≤
      (1 - η) * v * ((h : ℝ) * (rMax - rMin)) :=
    mul_le_mul_of_nonneg_left hspan hnn
  have hquarter : v * w / 4 ≤ (1 - η) * v * (w / 2) := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - η := by linarith [hηlt]
    have hvw : 0 ≤ v * (w / 2) :=
      mul_nonneg hv.le (div_nonneg hw.le (by norm_num))
    have := mul_le_mul_of_nonneg_right hhalf hvw
    have hL : (1 / 2 : ℝ) * (v * (w / 2)) = v * w / 4 := by ring
    have hR : (1 - η) * (v * (w / 2)) = (1 - η) * v * (w / 2) := by ring
    linarith
  linarith

private theorem grid_fourier_bound_triv
    {A : Finset ℕ} {h : ℕ} (hh : 0 < h) {v η : ℝ}
    (hη : 0 ≤ η) (_hv : 0 < v) {Wleft Wright : ℕ} {c : ℝ} (hc : c ≠ 0)
    (hlen : (h : ℝ) ≤ ((Wright : ℝ) - (Wleft : ℝ)) / 4)
    (htriv : 1 / 2 ≤ η ∨ 1 / 2 ≤ |c| * (h : ℝ)) :
    ‖(∑ u ∈ A.filter (fun u => Wleft < u ∧ u < Wright), e (c * u))
        / (A.filter (fun u => Wleft < u ∧ u < Wright)).card‖
      ≤ gridFourierC *
        (1 / (|c| * ((Wright : ℝ) - (Wleft : ℝ))) + η + |c| * h
          + h / ((Wright : ℝ) - (Wleft : ℝ))) := by
  set w : ℝ := (Wright : ℝ) - (Wleft : ℝ)
  set W : Finset ℕ := A.filter (fun u => Wleft < u ∧ u < Wright)
  have hw : 0 < w := by
    have : (0 : ℝ) < 4 * h := mul_pos (by norm_num) (Nat.cast_pos.mpr hh)
    linarith
  have hmean : ‖(∑ u ∈ W, e (c * u)) / (W.card : ℂ)‖ ≤ 1 :=
    norm_div_card_le_one W (fun u => e (c * u)) fun _ _ => (norm_e _).le
  have hnn_c : (0 : ℝ) ≤ |c| * h := mul_nonneg (abs_nonneg _) (Nat.cast_nonneg h)
  have hpart : (1 / 2 : ℝ) ≤ η + |c| * h := by
    rcases htriv with hη' | hc'
    · exact le_add_of_le_of_nonneg hη' hnn_c
    · exact le_add_of_nonneg_of_le hη hc'
  have hpos1 : 0 ≤ 1 / (|c| * w) :=
    div_nonneg (by norm_num) (mul_pos (abs_pos.mpr hc) hw).le
  have hpos3 : 0 ≤ h / w := div_nonneg (Nat.cast_nonneg h) hw.le
  have hsum : (1 / 2 : ℝ) ≤ 1 / (|c| * w) + η + |c| * h + h / w := by
    linarith [hpos1, hpos3, hpart]
  have hC : (1 : ℝ) ≤ gridFourierC * (1 / 2) := by
    unfold gridFourierC
    norm_num
  have hmon : gridFourierC * (1 / 2) ≤
      gridFourierC * (1 / (|c| * w) + η + |c| * h + h / w) := by
    unfold gridFourierC
    exact mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 80)
  exact hmean.trans (hC.trans hmon)

private theorem grid_fourier_bound_main
    {A : Finset ℕ} {h : ℕ} (hh : 0 < h) {v η : ℝ}
    (hη : 0 ≤ η) (hv : 0 < v)
    (hcell : ∀ r : ℕ, |(((A.filter (cell r h)).card : ℝ) - v * h)| ≤ η * v * h)
    {Wleft Wright : ℕ} {c : ℝ} (hc : c ≠ 0)
    (hlen : (h : ℝ) ≤ ((Wright : ℝ) - (Wleft : ℝ)) / 4)
    (htriv : ¬(1 / 2 ≤ η ∨ 1 / 2 ≤ |c| * (h : ℝ))) :
    ‖(∑ u ∈ A.filter (fun u => Wleft < u ∧ u < Wright), e (c * u))
        / (A.filter (fun u => Wleft < u ∧ u < Wright)).card‖
      ≤ gridFourierC *
        (1 / (|c| * ((Wright : ℝ) - (Wleft : ℝ))) + η + |c| * h
          + h / ((Wright : ℝ) - (Wleft : ℝ))) := by
  classical
  set w : ℝ := (Wright : ℝ) - (Wleft : ℝ)
  set W : Finset ℕ := A.filter (fun u => Wleft < u ∧ u < Wright)
  have hw : 0 < w := by
    have : (0 : ℝ) < 4 * h := mul_pos (by norm_num) (Nat.cast_pos.mpr hh)
    linarith
  have hηlt : η < 1 / 2 := lt_of_not_ge (not_or.mp htriv).1
  have hclt : |c| * h < 1 / 2 := lt_of_not_ge (not_or.mp htriv).2
  have hle4 : Wleft + 4 * h ≤ Wright := by
    have : (Wleft : ℝ) + 4 * h ≤ Wright := by linarith
    exact_mod_cast this
  have hrMin : Wleft / h + 1 < Wright / h := grid_rMin_lt hh hle4
  set rMin : ℕ := Wleft / h + 1
  set rMax : ℕ := Wright / h
  have hIco : rMin < rMax := hrMin
  have hn : 0 < rMax - rMin := Nat.sub_pos_of_lt hIco
  have hDen : v * w / 4 ≤ (W.card : ℝ) := by
    simpa [w, W] using grid_window_card_lower hh hη hv hηlt hcell hlen
  have hcard_cell : ∀ r,
      ((A.filter (cell r h)).card : ℝ) ≤ (1 + η) * v * h := by
    intro r
    linarith [abs_le.mp (hcell r)]
  have hinterPts :
      (Ico rMin rMax).biUnion (fun r => A.filter (cell r h)) ⊆ W := by
    intro u hu
    obtain ⟨r, hr, huA⟩ := mem_biUnion.mp hu
    have huI : u ∈ Ico (r * h) ((r + 1) * h) := by
      simpa [cell, mem_Ico] using (mem_filter.mp huA).2
    have huW : u ∈ Ioo Wleft Wright := cell_block_subset hh hr huI
    exact mem_filter.mpr ⟨(mem_filter.mp huA).1, mem_Ioo.mp huW⟩
  set interiorPts := (Ico rMin rMax).biUnion (fun r => A.filter (cell r h))
  have hdisj := cell_pairwise_disjoint A h (Ico rMin rMax)
  have hinter_le_w : (h : ℝ) * (rMax - rMin) ≤ w :=
    grid_span_le hh hIco.le
  have hgeom :
      ‖∑ r ∈ Ico rMin rMax, e (c * (r : ℝ) * h)‖ ≤ 1 / (2 * |c| * h) := by
    have hsum :
        ∑ r ∈ Ico rMin rMax, e (c * (r : ℝ) * h) =
          ∑ k ∈ range (rMax - rMin),
            e (c * ((rMin + k : ℕ) : ℝ) * h) :=
      sum_Ico_eq_sum_range _ rMin rMax
    have hfact :
        ∑ k ∈ range (rMax - rMin), e (c * ((rMin + k : ℕ) : ℝ) * h) =
          e (c * (rMin : ℝ) * h) *
            ∑ k ∈ range (rMax - rMin), e (c * ((k : ℝ) * h)) := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      have hx : c * ((rMin + k : ℕ) : ℝ) * h =
          c * (rMin : ℝ) * h + c * ((k : ℝ) * h) := by
        push_cast
        ring
      rw [hx, e_add]
    rw [hsum, hfact, norm_mul, norm_e, one_mul]
    exact geom_char_bound hh hn hc hclt
  have hbd : ((W \ interiorPts).card : ℝ) ≤ 2 * (1 + η) * v * h := by
    have hsub : W \ interiorPts ⊆
        A.filter (cell (Wleft / h) h) ∪ A.filter (cell rMax h) := by
      intro u hu
      have ⟨huW, hnint⟩ := mem_sdiff.mp hu
      have ⟨huA, hwin⟩ := mem_filter.mp huW
      have ⟨hLt, hRt⟩ := hwin
      have hcellu : cell (u / h) h u :=
        ⟨mul_div_le_comm u h, lt_mul_succ_div hh⟩
      have hlo : Wleft / h ≤ u / h := Nat.div_le_div_right (Nat.le_of_lt hLt)
      have hhi : u / h ≤ rMax := Nat.div_le_div_right (Nat.le_of_lt hRt)
      have hmem : u / h = Wleft / h ∨ u / h ∈ Ico rMin rMax ∨ u / h = rMax := by
        rcases Nat.eq_or_lt_of_le hlo with h1 | h1
        · exact Or.inl h1.symm
        · rcases Nat.eq_or_lt_of_le hhi with h2 | h2
          · exact Or.inr (Or.inr h2)
          · exact Or.inr (Or.inl (mem_Ico.mpr ⟨Nat.succ_le_of_lt h1, h2⟩))
      rcases hmem with h1 | h2 | h3
      · exact mem_union.mpr <| Or.inl <|
          mem_filter.mpr ⟨huA, by simpa [h1] using hcellu⟩
      · exact False.elim <| hnint <|
          mem_biUnion.mpr ⟨u / h, h2, mem_filter.mpr ⟨huA, hcellu⟩⟩
      · exact mem_union.mpr <| Or.inr <|
          mem_filter.mpr ⟨huA, by simpa [h3] using hcellu⟩
    have hle' : (W \ interiorPts).card ≤
        (A.filter (cell (Wleft / h) h)).card + (A.filter (cell rMax h)).card :=
      (card_le_card hsub).trans (card_union_le _ _)
    have : ((W \ interiorPts).card : ℝ) ≤
        ((A.filter (cell (Wleft / h) h)).card : ℝ) +
          ((A.filter (cell rMax h)).card : ℝ) := by
      exact_mod_cast hle'
    linarith [hcard_cell (Wleft / h), hcard_cell rMax]
  have hSsplit : ∑ u ∈ W, e (c * u) =
      ∑ u ∈ interiorPts, e (c * u) + ∑ u ∈ W \ interiorPts, e (c * u) := by
    rw [← sum_sdiff (s₁ := interiorPts) (s₂ := W) hinterPts, add_comm]
  have hSint :
      ∑ u ∈ interiorPts, e (c * u) =
        ∑ r ∈ Ico rMin rMax, ∑ u ∈ A.filter (cell r h), e (c * u) :=
    sum_biUnion hdisj
  have hLip : ‖∑ r ∈ Ico rMin rMax,
      ∑ u ∈ A.filter (cell r h), (e (c * u) - e (c * (r : ℝ) * h))‖ ≤
        2 * Real.pi * |c| * h * (1 + η) * v * ((h : ℝ) * (rMax - rMin)) := by
    have hpt : ∀ r ∈ Ico rMin rMax,
        ‖∑ u ∈ A.filter (cell r h), (e (c * u) - e (c * (r : ℝ) * h))‖ ≤
          2 * Real.pi * |c| * h * ((A.filter (cell r h)).card : ℝ) := by
      intro r _
      have hle :
          ‖∑ u ∈ A.filter (cell r h), (e (c * u) - e (c * (r : ℝ) * h))‖ ≤
            ∑ u ∈ A.filter (cell r h), 2 * Real.pi * |c| * h := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun u hu => ?_)
        have hcellu := (mem_filter.mp hu).2
        have hdiff : |(u : ℝ) - (r : ℝ) * h| ≤ h := by
          rcases hcellu with ⟨hlo, hhi⟩
          have hloR : (r : ℝ) * h ≤ (u : ℝ) := by exact_mod_cast hlo
          have hhiR : (u : ℝ) < ((r + 1 : ℕ) : ℝ) * h := by exact_mod_cast hhi
          have hs : ((r + 1 : ℕ) : ℝ) * h = (r : ℝ) * h + h := by
            push_cast
            ring
          rw [abs_of_nonneg (sub_nonneg.mpr hloR)]
          linarith
        have hlip := norm_e_sub_e (c * (r : ℝ) * h) (c * u)
        have hmul : |c * (u : ℝ) - c * (r : ℝ) * h| =
            |c| * |(u : ℝ) - (r : ℝ) * h| := by
          have : c * (u : ℝ) - c * (r : ℝ) * h =
              c * ((u : ℝ) - (r : ℝ) * h) := by ring
          rw [this, abs_mul]
        have hπ : (0 : ℝ) ≤ 2 * Real.pi :=
          mul_nonneg (by norm_num) Real.pi_pos.le
        have hstep : 2 * Real.pi * |c * (u : ℝ) - c * (r : ℝ) * h| ≤
            2 * Real.pi * |c| * h := by
          rw [hmul]
          have : |c| * |(u : ℝ) - (r : ℝ) * h| ≤ |c| * h :=
            mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
          have : 2 * Real.pi * (|c| * |(u : ℝ) - (r : ℝ) * h|) ≤
              2 * Real.pi * (|c| * h) :=
            mul_le_mul_of_nonneg_left this hπ
          have : 2 * Real.pi * |c| * h = 2 * Real.pi * (|c| * h) := by ring
          linarith
        exact hlip.trans hstep
      have hcards :
          (∑ u ∈ A.filter (cell r h), (2 * Real.pi * |c| * h : ℝ)) =
            2 * Real.pi * |c| * h * ((A.filter (cell r h)).card : ℝ) := by
        simp [sum_const, nsmul_eq_mul]
        ring
      exact hle.trans_eq hcards
    have hsum := (norm_sum_le _ _).trans (sum_le_sum hpt)
    have hcards :
        ∑ r ∈ Ico rMin rMax, ((A.filter (cell r h)).card : ℝ) ≤
          (1 + η) * v * ((h : ℝ) * (rMax - rMin)) := by
      have := sum_le_sum fun r (_ : r ∈ Ico rMin rMax) => hcard_cell r
      have hsumc :
          ∑ r ∈ Ico rMin rMax, (1 + η) * v * h =
            (1 + η) * v * ((h : ℝ) * (rMax - rMin)) := by
        simp only [sum_const, nsmul_eq_mul]
        rw [card_Ico_cast hIco.le]
        ring
      linarith
    have hmulsum :
        ∑ r ∈ Ico rMin rMax,
            2 * Real.pi * |c| * h * ((A.filter (cell r h)).card : ℝ) =
          2 * Real.pi * |c| * h *
            ∑ r ∈ Ico rMin rMax, ((A.filter (cell r h)).card : ℝ) := by
      simp [← mul_sum]
    have hnn : 0 ≤ 2 * Real.pi * |c| * h :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (abs_nonneg c)) (Nat.cast_nonneg h)
    calc
      ‖∑ r ∈ Ico rMin rMax,
            ∑ u ∈ A.filter (cell r h),
              (e (c * u) - e (c * (r : ℝ) * h))‖ ≤
          ∑ r ∈ Ico rMin rMax,
            2 * Real.pi * |c| * h * ((A.filter (cell r h)).card : ℝ) := hsum
      _ = 2 * Real.pi * |c| * h *
            ∑ r ∈ Ico rMin rMax, ((A.filter (cell r h)).card : ℝ) := hmulsum
      _ ≤ 2 * Real.pi * |c| * h * ((1 + η) * v * ((h : ℝ) * (rMax - rMin))) :=
          mul_le_mul_of_nonneg_left hcards hnn
      _ = 2 * Real.pi * |c| * h * (1 + η) * v * ((h : ℝ) * (rMax - rMin)) := by
          ring
  let vh : ℂ := Complex.ofReal (v * (h : ℝ))
  let δ : ℕ → ℂ := fun r =>
    Complex.ofReal (((A.filter (cell r h)).card : ℝ) - v * h)
  have hδsum : ‖∑ r ∈ Ico rMin rMax, δ r * e (c * (r : ℝ) * h)‖ ≤
      η * v * ((h : ℝ) * (rMax - rMin)) := by
    have hpt : ∀ r ∈ Ico rMin rMax,
        ‖δ r * e (c * (r : ℝ) * h)‖ ≤ η * v * h := by
      intro r _
      rw [norm_mul, Complex.norm_real, norm_e, mul_one]
      exact hcell r
    have hsum := (norm_sum_le _ _).trans (sum_le_sum hpt)
    have hsumc : ∑ r ∈ Ico rMin rMax, (η * v * h : ℝ) =
        η * v * ((h : ℝ) * (rMax - rMin)) := by
      simp only [sum_const, nsmul_eq_mul]
      rw [card_Ico_cast hIco.le]
      ring
    exact hsum.trans_eq hsumc
  have hinter_eq :
      ∑ r ∈ Ico rMin rMax, ∑ u ∈ A.filter (cell r h), e (c * u) =
        (∑ r ∈ Ico rMin rMax, ∑ u ∈ A.filter (cell r h),
            (e (c * u) - e (c * (r : ℝ) * h))) +
        vh * ∑ r ∈ Ico rMin rMax, e (c * (r : ℝ) * h) +
        ∑ r ∈ Ico rMin rMax, δ r * e (c * (r : ℝ) * h) := by
    have h1 : ∀ r,
        ∑ u ∈ A.filter (cell r h), e (c * u) =
          ∑ u ∈ A.filter (cell r h), (e (c * u) - e (c * (r : ℝ) * h)) +
            ((A.filter (cell r h)).card : ℂ) * e (c * (r : ℝ) * h) := by
      intro r
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sub_add_cancel]
    have h2 : ∀ r,
        ((A.filter (cell r h)).card : ℂ) = vh + δ r := by
      intro r
      have hcR : ((A.filter (cell r h)).card : ℝ) =
          v * h + (((A.filter (cell r h)).card : ℝ) - v * h) := by ring
      have hC : ((A.filter (cell r h)).card : ℂ) =
          Complex.ofReal ((A.filter (cell r h)).card : ℝ) :=
        (Complex.ofReal_natCast _).symm
      rw [hC, hcR, Complex.ofReal_add]
    simp_rw [h1]
    rw [sum_add_distrib]
    have h3 :
        ∑ r ∈ Ico rMin rMax,
            ((A.filter (cell r h)).card : ℂ) * e (c * (r : ℝ) * h) =
          vh * ∑ r ∈ Ico rMin rMax, e (c * (r : ℝ) * h) +
            ∑ r ∈ Ico rMin rMax, δ r * e (c * (r : ℝ) * h) := by
      simp_rw [h2, add_mul, sum_add_distrib, ← mul_sum]
    rw [h3, add_assoc]
  have hS_eq :
      ∑ u ∈ W, e (c * u) =
        (∑ r ∈ Ico rMin rMax, ∑ u ∈ A.filter (cell r h),
            (e (c * u) - e (c * (r : ℝ) * h))) +
        vh * ∑ r ∈ Ico rMin rMax, e (c * (r : ℝ) * h) +
        ∑ r ∈ Ico rMin rMax, δ r * e (c * (r : ℝ) * h) +
        ∑ u ∈ W \ interiorPts, e (c * u) := by
    rw [hSsplit, hSint, hinter_eq]
  have hLipw :
      ‖∑ r ∈ Ico rMin rMax, ∑ u ∈ A.filter (cell r h),
          (e (c * u) - e (c * (r : ℝ) * h))‖ ≤
        2 * Real.pi * |c| * h * (1 + η) * v * w := by
    have hπc : 0 ≤ 2 * Real.pi * |c| :=
      mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (abs_nonneg c)
    have h1 : 0 ≤ 2 * Real.pi * |c| * h :=
      mul_nonneg hπc (Nat.cast_nonneg h)
    have h2 : 0 ≤ 2 * Real.pi * |c| * h * (1 + η) :=
      mul_nonneg h1 (add_nonneg (by norm_num) hη)
    have hnn : 0 ≤ 2 * Real.pi * |c| * h * (1 + η) * v :=
      mul_nonneg h2 hv.le
    exact hLip.trans (mul_le_mul_of_nonneg_left hinter_le_w hnn)
  have hMean :
      ‖vh * ∑ r ∈ Ico rMin rMax, e (c * (r : ℝ) * h)‖ ≤ v / (2 * |c|) := by
    have hvh : 0 ≤ v * (h : ℝ) := mul_nonneg hv.le (Nat.cast_nonneg h)
    have hnorm : ‖vh‖ = v * h := norm_ofReal_nonneg hvh
    rw [norm_mul, hnorm]
    have hid : v * h * (1 / (2 * |c| * h)) = v / (2 * |c|) := by
      have hc0 : |c| ≠ 0 := abs_ne_zero.mpr hc
      have hh0 : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hh.ne'
      field_simp [hc0, hh0]
    calc
      v * h * ‖∑ r ∈ Ico rMin rMax, e (c * (r : ℝ) * h)‖ ≤
          v * h * (1 / (2 * |c| * h)) :=
        mul_le_mul_of_nonneg_left hgeom hvh
      _ = v / (2 * |c|) := hid
  have hδw :
      ‖∑ r ∈ Ico rMin rMax, δ r * e (c * (r : ℝ) * h)‖ ≤ η * v * w := by
    have hnn : 0 ≤ η * v := mul_nonneg hη hv.le
    exact hδsum.trans (mul_le_mul_of_nonneg_left hinter_le_w hnn)
  have hSbd :
      ‖∑ u ∈ W \ interiorPts, e (c * u)‖ ≤ 2 * (1 + η) * v * h := by
    have h1 :
        ‖∑ u ∈ W \ interiorPts, e (c * u)‖ ≤
          ((W \ interiorPts).card : ℝ) :=
      (norm_sum_le _ _).trans <|
        (sum_le_sum fun _ _ => (norm_e _).le).trans_eq
          (by simp [sum_const, nsmul_eq_mul])
    exact h1.trans hbd
  have hS_le :
      ‖∑ u ∈ W, e (c * u)‖ ≤
        2 * Real.pi * |c| * h * (1 + η) * v * w + v / (2 * |c|) +
          η * v * w + 2 * (1 + η) * v * h := by
    have htri :
        ‖∑ u ∈ W, e (c * u)‖ ≤
          ‖∑ r ∈ Ico rMin rMax, ∑ u ∈ A.filter (cell r h),
              (e (c * u) - e (c * (r : ℝ) * h))‖ +
          ‖vh * ∑ r ∈ Ico rMin rMax, e (c * (r : ℝ) * h)‖ +
          ‖∑ r ∈ Ico rMin rMax, δ r * e (c * (r : ℝ) * h)‖ +
          ‖∑ u ∈ W \ interiorPts, e (c * u)‖ := by
      rw [hS_eq]
      exact norm_add4 _ _ _ _
    linarith [htri, hLipw, hMean, hδw, hSbd]
  have hquot :
      ‖(∑ u ∈ W, e (c * u)) / (W.card : ℂ)‖ ≤
        4 * ‖∑ u ∈ W, e (c * u)‖ / (v * w) := by
    rw [norm_div_nat]
    have hdenpos : 0 < v * w / 4 := div_pos (mul_pos hv hw) (by norm_num)
    have h1 :
        ‖∑ u ∈ W, e (c * u)‖ / (W.card : ℝ) ≤
          ‖∑ u ∈ W, e (c * u)‖ / (v * w / 4) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hdenpos hDen
    have h2 :
        ‖∑ u ∈ W, e (c * u)‖ / (v * w / 4) =
          4 * ‖∑ u ∈ W, e (c * u)‖ / (v * w) := by
      rw [div_div_eq_mul_div]
      ring
    exact h1.trans_eq h2
  have hscale :
      4 *
          (2 * Real.pi * |c| * h * (1 + η) * v * w + v / (2 * |c|) +
            η * v * w + 2 * (1 + η) * v * h) / (v * w) =
        8 * Real.pi * (1 + η) * (|c| * h) + 2 / (|c| * w) + 4 * η +
          8 * (1 + η) * (h / w) := by
    have hv0 : v ≠ 0 := hv.ne'
    have hw0 : w ≠ 0 := hw.ne'
    have hc0 : |c| ≠ 0 := abs_ne_zero.mpr hc
    have hvw0 : v * w ≠ 0 := mul_ne_zero hv0 hw0
    have h1 : 4 * (2 * Real.pi * |c| * h * (1 + η) * v * w) / (v * w) =
        8 * Real.pi * (1 + η) * (|c| * h) := by
      have : 4 * (2 * Real.pi * |c| * h * (1 + η) * v * w) =
          (8 * Real.pi * (1 + η) * (|c| * h)) * (v * w) := by ring
      rw [this, mul_div_cancel_right₀ _ hvw0]
    have h2 : 4 * (v / (2 * |c|)) / (v * w) = 2 / (|c| * w) := by
      field_simp [hv0, hw0, hc0]
      ring
    have h3 : 4 * (η * v * w) / (v * w) = 4 * η := by
      have : 4 * (η * v * w) = (4 * η) * (v * w) := by ring
      rw [this, mul_div_cancel_right₀ _ hvw0]
    have h4 : 4 * (2 * (1 + η) * v * h) / (v * w) =
        8 * (1 + η) * (h / w) := by
      have : 4 * (2 * (1 + η) * v * h) = (8 * (1 + η) * h) * v := by ring
      rw [this]
      have : ((8 * (1 + η) * h) * v) / (v * w) =
          (8 * (1 + η) * h) / w := by
        rw [div_mul_eq_div_div, mul_div_cancel_right₀ _ hv0]
      rw [this]
      ring
    have hsplit :
        4 *
            (2 * Real.pi * |c| * h * (1 + η) * v * w + v / (2 * |c|) +
              η * v * w + 2 * (1 + η) * v * h) / (v * w) =
          4 * (2 * Real.pi * |c| * h * (1 + η) * v * w) / (v * w) +
            4 * (v / (2 * |c|)) / (v * w) +
            4 * (η * v * w) / (v * w) +
            4 * (2 * (1 + η) * v * h) / (v * w) := by
      ring
    rw [hsplit, h1, h2, h3, h4]
  have h80 :
      8 * Real.pi * (1 + η) * (|c| * h) + 2 / (|c| * w) + 4 * η +
          8 * (1 + η) * (h / w) ≤
        gridFourierC * (1 / (|c| * w) + η + |c| * h + h / w) := by
    unfold gridFourierC
    have hη12 : 1 + η ≤ 3 / 2 := by linarith [hηlt]
    have hpi : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
    have hcoeff : 8 * Real.pi * (1 + η) ≤ 80 := by
      have h1 : 8 * Real.pi * (1 + η) ≤ 8 * 4 * (1 + η) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 8))
          (add_nonneg (by norm_num) hη)
      have h2 : 8 * 4 * (1 + η) ≤ 8 * 4 * (3 / 2) :=
        mul_le_mul_of_nonneg_left hη12 (by norm_num)
      have h3 : (8 : ℝ) * 4 * (3 / 2) = 48 := by norm_num
      have h4 : (48 : ℝ) ≤ 80 := by norm_num
      linarith
    have h8η : 8 * (1 + η) ≤ 80 := by
      have : 8 * (1 + η) ≤ 8 * (3 / 2) :=
        mul_le_mul_of_nonneg_left hη12 (by norm_num)
      have : (8 : ℝ) * (3 / 2) = 12 := by norm_num
      linarith
    have hposc : 0 ≤ |c| * h := mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
    have hposinv : 0 ≤ 1 / (|c| * w) :=
      div_nonneg (by norm_num) (mul_pos (abs_pos.mpr hc) hw).le
    have hposhw : 0 ≤ h / w := div_nonneg (Nat.cast_nonneg _) hw.le
    have t1 : 8 * Real.pi * (1 + η) * (|c| * h) ≤ 80 * (|c| * h) :=
      mul_le_mul_of_nonneg_right hcoeff hposc
    have t2 : 2 / (|c| * w) ≤ 80 * (1 / (|c| * w)) := by
      have : (2 : ℝ) / (|c| * w) = 2 * (1 / (|c| * w)) :=
        div_eq_mul_one_div _ _
      have : (2 : ℝ) * (1 / (|c| * w)) ≤ 80 * (1 / (|c| * w)) :=
        mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 80) hposinv
      linarith
    have t3 : 4 * η ≤ 80 * η :=
      mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 80) hη
    have t4 : 8 * (1 + η) * (h / w) ≤ 80 * (h / w) :=
      mul_le_mul_of_nonneg_right h8η hposhw
    have hcomb :
        8 * Real.pi * (1 + η) * (|c| * h) + 2 / (|c| * w) + 4 * η +
            8 * (1 + η) * (h / w) ≤
          80 * (|c| * h) + 80 * (1 / (|c| * w)) + 80 * η + 80 * (h / w) :=
      add_le_add (add_le_add (add_le_add t1 t2) t3) t4
    have hrw :
        80 * (|c| * h) + 80 * (1 / (|c| * w)) + 80 * η + 80 * (h / w) =
          80 * (1 / (|c| * w) + η + |c| * h + h / w) := by ring
    exact hcomb.trans_eq hrw
  have hfinal :
      4 * ‖∑ u ∈ W, e (c * u)‖ / (v * w) ≤
        gridFourierC * (1 / (|c| * w) + η + |c| * h + h / w) := by
    have hvw : 0 < v * w := mul_pos hv hw
    have hmul :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hS_le (by norm_num : (0 : ℝ) ≤ 4))
        hvw.le
    exact (hmul.trans_eq hscale).trans h80
  exact hquot.trans hfinal

/-- Deterministic Riemann-sum bound on a grid, R97/02 Lemma 5.1.

Source: `rounds/round97/02_gpt_khl_normality_extension.md` Lemma 5.1;
`lean/PRIME_NORMALITY.md` Fourier.
Contract: API
Audit: GREEN -/
theorem grid_fourier_bound
    {A : Finset ℕ} {h : ℕ} (hh : 0 < h) {v η : ℝ}
    (hη : 0 ≤ η) (hv : 0 < v)
    (hcell : ∀ r : ℕ, |(((A.filter (cell r h)).card : ℝ) - v * h)| ≤ η * v * h)
    {Wleft Wright : ℕ} {c : ℝ} (hc : c ≠ 0)
    (hlen : (h : ℝ) ≤ ((Wright : ℝ) - (Wleft : ℝ)) / 4) :
    ‖(∑ u ∈ A.filter (fun u => Wleft < u ∧ u < Wright), e (c * u))
        / (A.filter (fun u => Wleft < u ∧ u < Wright)).card‖
      ≤ gridFourierC *
        (1 / (|c| * ((Wright : ℝ) - (Wleft : ℝ))) + η + |c| * h
          + h / ((Wright : ℝ) - (Wleft : ℝ))) := by
  by_cases htriv : 1 / 2 ≤ η ∨ 1 / 2 ≤ |c| * (h : ℝ)
  · exact grid_fourier_bound_triv hh hη hv hc hlen htriv
  · exact grid_fourier_bound_main hh hη hv hcell hc hlen htriv

end PrimeGapNormality.Prime
