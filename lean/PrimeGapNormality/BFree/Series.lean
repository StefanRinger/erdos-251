import PrimeGapNormality.BFree.Definitions
import PrimeGapNormality.BFree.Enumeration
import PrimeGapNormality.Digital.GapAlgebra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Infinite Abel identity for the ordered position series

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (22); M1
`GapAlgebra.gapPartial_abel`.
Contract: C5
Audit: GREEN
-/

namespace PrimeGapNormality.BFree

open PrimeGapNormality Finset Filter
open scoped Topology

theorem one_lt_cast_of_two_le {b : ℕ} (hb : 2 ≤ b) : (1 : ℝ) < b := by
  have : (2 : ℝ) ≤ b := Nat.cast_le.mpr hb
  linarith

theorem b_cast_pos {b : ℕ} (hb : 2 ≤ b) : (0 : ℝ) < b :=
  lt_trans (by norm_num) (one_lt_cast_of_two_le hb)

theorem b_cast_ne_zero {b : ℕ} (hb : 2 ≤ b) : (b : ℝ) ≠ 0 :=
  (b_cast_pos hb).ne'

theorem inv_b_norm_lt_one {b : ℕ} (hb : 2 ≤ b) : ‖((b : ℝ)⁻¹)‖ < 1 := by
  have hb1 := one_lt_cast_of_two_le hb
  rw [norm_inv, Real.norm_eq_abs, abs_of_pos (b_cast_pos hb)]
  exact inv_lt_one_of_one_lt₀ hb1

theorem term_nonneg (F : AdmissibleFamily) (b n : ℕ) :
    0 ≤ (enum F n : ℝ) / (b : ℝ) ^ (n + 1) :=
  div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

theorem gap_term_nonneg (F : AdmissibleFamily) (b n : ℕ) :
    0 ≤ (gap (enum F) n : ℝ) / (b : ℝ) ^ (n + 1) :=
  div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

theorem gap_le_enum_succ (F : AdmissibleFamily) (n : ℕ) :
    (gap (enum F) n : ℝ) ≤ enum F (n + 1) := by
  have : enum F n ≤ enum F (n + 1) := (enum_strictMono F).monotone (Nat.le_succ n)
  exact_mod_cast Nat.sub_le (enum F (n + 1)) (enum F n)

theorem summable_succ_mul_geometric {b : ℕ} (hb : 2 ≤ b) :
    Summable fun n : ℕ => (n + 1 : ℝ) * (b : ℝ)⁻¹ ^ n := by
  have hr := inv_b_norm_lt_one hb
  have hpow := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have hgeo := summable_geometric_of_norm_lt_one (K := ℝ) hr
  have hpow' : Summable fun n : ℕ => (n : ℝ) * (b : ℝ)⁻¹ ^ n := by
    simpa [pow_one] using hpow
  have hfun :
      (fun n : ℕ => (n + 1 : ℝ) * (b : ℝ)⁻¹ ^ n) =
        fun n : ℕ => (n : ℝ) * (b : ℝ)⁻¹ ^ n + (b : ℝ)⁻¹ ^ n := by
    funext n
    ring
  exact hfun ▸ hpow'.add hgeo

theorem scaled_geom (C : ℝ) {b : ℕ} (hb : 2 ≤ b) (n : ℕ) (m : ℝ) :
    C * m / (b : ℝ) ^ (n + 1) = (C / b) * (m * (b : ℝ)⁻¹ ^ n) := by
  have hb0 := b_cast_ne_zero hb
  rw [pow_succ, div_mul_eq_div_div, div_eq_mul_inv, inv_pow]
  field_simp [hb0]

/-- Summability of the ordered position series under a linear bound on `enum`.

Source: `lean/BFREE_SIGNATURES.md`.
Contract: C5
Audit: GREEN -/
theorem posSeries_summable (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (hC : ∃ C : ℝ, ∀ n, (enum F n : ℝ) ≤ C * (n + 1)) :
    Summable fun n => (enum F n : ℝ) / (b : ℝ) ^ (n + 1) := by
  obtain ⟨C0, hC0⟩ := hC
  let C := max C0 0
  have hC : ∀ n, (enum F n : ℝ) ≤ C * (n + 1) := fun n =>
    (hC0 n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hdom : Summable fun n : ℕ => C / b * ((n + 1 : ℝ) * (b : ℝ)⁻¹ ^ n) :=
    (summable_succ_mul_geometric hb).mul_left (C / b)
  refine Summable.of_nonneg_of_le (fun n => term_nonneg F b n) (fun n => ?_) hdom
  have hle : (enum F n : ℝ) / (b : ℝ) ^ (n + 1) ≤
      C * (n + 1) / (b : ℝ) ^ (n + 1) :=
    div_le_div_of_nonneg_right (hC n) (pow_nonneg (Nat.cast_nonneg _) _)
  exact hle.trans_eq (scaled_geom C hb n (n + 1))

theorem summable_add_two_mul_geometric {b : ℕ} (hb : 2 ≤ b) :
    Summable fun n : ℕ => (n + 2 : ℝ) * (b : ℝ)⁻¹ ^ n := by
  have h1 := summable_succ_mul_geometric hb
  have hgeo := summable_geometric_of_norm_lt_one (K := ℝ) (inv_b_norm_lt_one hb)
  have hfun :
      (fun n : ℕ => (n + 2 : ℝ) * (b : ℝ)⁻¹ ^ n) =
        fun n : ℕ => (n + 1 : ℝ) * (b : ℝ)⁻¹ ^ n + (b : ℝ)⁻¹ ^ n := by
    funext n
    ring
  exact hfun ▸ h1.add hgeo

theorem gapSeries_summable (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (hC : ∃ C : ℝ, ∀ n, (enum F n : ℝ) ≤ C * (n + 1)) :
    Summable fun n => (gap (enum F) n : ℝ) / (b : ℝ) ^ (n + 1) := by
  obtain ⟨C0, hC0⟩ := hC
  let C := max C0 0
  have hC : ∀ n, (enum F n : ℝ) ≤ C * (n + 1) := fun n =>
    (hC0 n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hdom : Summable fun n : ℕ => C / b * ((n + 2 : ℝ) * (b : ℝ)⁻¹ ^ n) :=
    (summable_add_two_mul_geometric hb).mul_left (C / b)
  refine Summable.of_nonneg_of_le (fun n => gap_term_nonneg F b n) (fun n => ?_) hdom
  have hbound : (gap (enum F) n : ℝ) ≤ C * (n + 2 : ℝ) := by
    have h := (gap_le_enum_succ F n).trans (by simpa using hC (n + 1))
    have h2 : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by
      rw [add_assoc, one_add_one_eq_two]
    rwa [h2] at h
  have hle : (gap (enum F) n : ℝ) / (b : ℝ) ^ (n + 1) ≤
      C * (n + 2 : ℝ) / (b : ℝ) ^ (n + 1) :=
    div_le_div_of_nonneg_right hbound (pow_nonneg (Nat.cast_nonneg _) _)
  exact hle.trans_eq (scaled_geom C hb n (n + 2))

theorem tendsto_enum_div_pow (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (hC : ∃ C : ℝ, ∀ n, (enum F n : ℝ) ≤ C * (n + 1)) :
    Tendsto (fun N : ℕ => (enum F N : ℝ) / (b : ℝ) ^ (N + 1)) atTop (𝓝 0) := by
  obtain ⟨C0, hC0⟩ := hC
  let C := max C0 0
  have hC : ∀ n, (enum F n : ℝ) ≤ C * (n + 1) := fun n =>
    (hC0 n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hb1 := one_lt_cast_of_two_le hb
  have hpow0 : Tendsto (fun n : ℕ => (n : ℝ) / (b : ℝ) ^ n) atTop (𝓝 0) := by
    simpa [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hb1
  have hpow : Tendsto (fun N : ℕ => (N + 1 : ℝ) / (b : ℝ) ^ (N + 1)) atTop (𝓝 0) := by
    have hcomp := hpow0.comp (tendsto_add_atTop_nat 1)
    convert hcomp using 1
    funext N
    simp [Function.comp, Nat.cast_succ]
  have hle : ∀ N,
      (enum F N : ℝ) / (b : ℝ) ^ (N + 1) ≤
        C * ((N + 1 : ℝ) / (b : ℝ) ^ (N + 1)) := by
    intro N
    have hdiv :=
      div_le_div_of_nonneg_right (hC N) (pow_nonneg (Nat.cast_nonneg b) (N + 1))
    simpa [mul_div_assoc] using hdiv
  have hmul : Tendsto (fun N : ℕ => C * ((N + 1 : ℝ) / (b : ℝ) ^ (N + 1))) atTop (𝓝 0) := by
    simpa using hpow.const_mul C
  exact squeeze_zero (fun N => term_nonneg F b N) hle hmul

theorem posPartial_cast (a : ℕ → ℕ) (b N : ℕ) :
    (posPartial a b N : ℝ) =
      ∑ n ∈ range (N + 1), (a n : ℝ) / (b : ℝ) ^ (n + 1) := by
  rw [posPartial_eq_sum_range]
  simp [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

theorem gapPartial_cast (a : ℕ → ℕ) (b N : ℕ) :
    (gapPartial a b N : ℝ) =
      ∑ n ∈ range N, (gap a n : ℝ) / (b : ℝ) ^ (n + 1) := by
  simp [gapPartial, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

theorem tendsto_last_term_of_summable (F : AdmissibleFamily) {b : ℕ} (_hb : 2 ≤ b)
    (hsum : Summable fun n => (enum F n : ℝ) / (b : ℝ) ^ (n + 1)) :
    Tendsto (fun N : ℕ => (enum F N : ℝ) / (b : ℝ) ^ (N + 1)) atTop (𝓝 0) := by
  set f := fun n : ℕ => (enum F n : ℝ) / (b : ℝ) ^ (n + 1)
  have hs : Tendsto (fun n : ℕ => ∑ i ∈ range n, f i) atTop (𝓝 (∑' n, f n)) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun n => term_nonneg F b n) _).1 hsum.hasSum
  have hdiff := (hs.comp (tendsto_add_atTop_nat 1)).sub hs
  have hdiff0 : Tendsto (fun n : ℕ => (∑ i ∈ range (n + 1), f i) - ∑ i ∈ range n, f i)
      atTop (𝓝 0) := by
    convert hdiff using 1
    · funext n
      simp [Function.comp]
    · simp
  exact hdiff0.congr fun n => by rw [sum_range_succ, add_sub_cancel_left]

theorem gapSeries_summable_of_posSeries (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (hsum : Summable fun n => (enum F n : ℝ) / (b : ℝ) ^ (n + 1)) :
    Summable fun n => (gap (enum F) n : ℝ) / (b : ℝ) ^ (n + 1) := by
  have htail : Summable fun n =>
      (enum F (n + 1) : ℝ) / (b : ℝ) ^ (n + 2) :=
    (summable_nat_add_iff (f := fun n => (enum F n : ℝ) / (b : ℝ) ^ (n + 1)) 1).2 hsum
  have hshift : Summable fun n => (enum F (n + 1) : ℝ) / (b : ℝ) ^ (n + 1) := by
    refine (htail.mul_left (b : ℝ)).congr fun n => ?_
    have hb0 := b_cast_ne_zero hb
    rw [pow_succ]
    field_simp [hb0]
  refine Summable.of_nonneg_of_le (fun n => gap_term_nonneg F b n) (fun n => ?_) hshift
  exact div_le_div_of_nonneg_right (gap_le_enum_succ F n) (pow_nonneg (Nat.cast_nonneg _) _)

/-- Infinite Abel: `β_b = (b-1) α_b - a_1`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (22);
`lean/BFREE_SIGNATURES.md`.
Contract: C5
Audit: GREEN

Index: Lean `enum F 0` is paper `a_1`. -/
theorem gapSeries_eq_affine (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (hsum : Summable fun n => (enum F n : ℝ) / (b : ℝ) ^ (n + 1)) :
    gapSeries F b = ((b : ℝ) - 1) * posSeries F b - enum F 0 := by
  have hterm := tendsto_last_term_of_summable F hb hsum
  have hgapS := gapSeries_summable_of_posSeries F hb hsum
  have habel : ∀ N,
      (gapPartial (enum F) b N : ℝ) =
        ((b : ℝ) - 1) * (posPartial (enum F) b N : ℝ) - (enum F 0 : ℝ) +
          (enum F N : ℝ) / (b : ℝ) ^ (N + 1) := by
    intro N
    have hQ := gapPartial_abel (enum_strictMono F) hb N
    have hcast := congrArg (fun x : ℚ => (x : ℝ)) hQ
    simp [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_one] at hcast
    exact hcast
  have hposT : Tendsto (fun N : ℕ => (posPartial (enum F) b N : ℝ)) atTop
      (𝓝 (posSeries F b)) := by
    have ht :=
      (hasSum_iff_tendsto_nat_of_nonneg (fun n => term_nonneg F b n) _).1 hsum.hasSum
    have hshift := ht.comp (tendsto_add_atTop_nat 1)
    have heq : (fun N : ℕ => (posPartial (enum F) b N : ℝ)) =
        (fun n : ℕ => ∑ i ∈ range n,
            (enum F i : ℝ) / (b : ℝ) ^ (i + 1)) ∘ fun a => a + 1 := by
      funext N
      simp [Function.comp, posPartial_cast]
    simpa [heq, posSeries] using hshift
  have hgapT : Tendsto (fun N : ℕ => (gapPartial (enum F) b N : ℝ)) atTop
      (𝓝 (gapSeries F b)) := by
    have ht :=
      (hasSum_iff_tendsto_nat_of_nonneg (fun n => gap_term_nonneg F b n) _).1
        hgapS.hasSum
    have heq : (fun N : ℕ => (gapPartial (enum F) b N : ℝ)) =
        fun n : ℕ => ∑ i ∈ range n,
          (gap (enum F) i : ℝ) / (b : ℝ) ^ (i + 1) := by
      funext N
      exact gapPartial_cast (enum F) b N
    simpa [heq, gapSeries] using ht
  have htarget :
      Tendsto (fun N : ℕ =>
        ((b : ℝ) - 1) * (posPartial (enum F) b N : ℝ) - (enum F 0 : ℝ) +
          (enum F N : ℝ) / (b : ℝ) ^ (N + 1)) atTop
        (𝓝 (((b : ℝ) - 1) * posSeries F b - enum F 0)) := by
    have hmul := (tendsto_const_nhds (x := ((b : ℝ) - 1))).mul hposT
    have hsub := hmul.sub (tendsto_const_nhds (x := (enum F 0 : ℝ)))
    simpa using hsub.add hterm
  have : Tendsto (fun N : ℕ => (gapPartial (enum F) b N : ℝ)) atTop
      (𝓝 (((b : ℝ) - 1) * posSeries F b - enum F 0)) :=
    htarget.congr fun N => (habel N).symm
  exact tendsto_nhds_unique hgapT this

/-- Rational `α_b` iff rational `β_b`, via infinite Abel. No coprimeness.

Source: `lean/BFREE_IRRATIONALITY.md` §4.3;
`rounds/round92/01_gpt_positive_integer_carry.md` (4.2).
Contract: C5
Audit: GREEN

Index: Lean `enum F 0` is paper `a_1`. -/
theorem posSeries_rational_iff_gapSeries_rational
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (hsum : Summable fun n => (enum F n : ℝ) / (b : ℝ) ^ (n + 1)) :
    (∃ q : ℚ, posSeries F b = q) ↔ (∃ r : ℚ, gapSeries F b = r) :=
  affine_eq_rat_iff_real hb (gapSeries_eq_affine F hb hsum)

/-- A rational real is an integer multiple of a positive integer reciprocal.

Source: `lean/BFREE_IRRATIONALITY.md` §4.3.
Contract: C5
Audit: GREEN

Index: `Q := q.den`. No `Nat.Coprime Q b`; must work for `b = 4` and even `Q`. -/
theorem exists_pos_nat_mul_mem_int {x : ℝ} (h : ∃ q : ℚ, x = q) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ n : ℤ, (Q : ℝ) * x = n := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.den, q.den_pos, q.num, ?_⟩
  rw [hq]
  exact_mod_cast Rat.den_mul_eq_num q

end PrimeGapNormality.BFree
