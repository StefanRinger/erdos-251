import PrimeGapNormality.BFree.Series
import PrimeGapNormality.BFree.CanonicalTransfer
import PrimeGapNormality.BFree.Carry
import Mathlib.NumberTheory.Real.Irrational

/-!
# Irrationality assembly: admissible summability and rational Abel transfer

Source: `rounds/round92/01_gpt_positive_integer_carry.md` §§4–5
Contract: C3+C4+C5 assembly (not C6)
Audit: GREEN (paper); Lean open

Palm `cesaro_trunc_test_eq_root` is closed in CanonicalTransfer.
Public hyps on `posSeries_irrational` are only `F` and `2 ≤ b`.
No `rho > 1/2`, no `Nat.Coprime Q b`.
-/

namespace PrimeGapNormality.BFree

open MeasureTheory Filter
open scoped Topology

/-- Summability of the ordered position series for any admissible family.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` §§4–5;
`lean/BFREE_IRRATIONALITY.md` §4.2.
Contract: C3+C4+C5 assembly (not C6)
Audit: GREEN (paper); Lean open

Index: Lean exponent `n+1` with 0-based `n`. `hC` is discharged by
`enum_linear_bound`; it does not appear on later public theorems. -/
theorem posSeries_summable_admissible
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    Summable fun n => (enum F n : ℝ) / (b : ℝ) ^ (n + 1) :=
  posSeries_summable F hb (enum_linear_bound F)

/-- Infinite Abel without a leftover `hsum` hypothesis.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.2);
`lean/BFREE_IRRATIONALITY.md` §4.2.
Contract: C3+C4+C5 assembly (not C6)
Audit: GREEN (paper); Lean open

Index: Lean `enum F 0` is paper `a_1`. -/
theorem gapSeries_eq_affine_admissible
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    gapSeries F b = ((b : ℝ) - 1) * posSeries F b - enum F 0 :=
  gapSeries_eq_affine F hb (posSeries_summable_admissible F hb)

/-- Rational `α_b` implies rational `β_b`. No coprimeness.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.2);
`lean/BFREE_IRRATIONALITY.md` §4.3.
Contract: C3+C4+C5 assembly (not C6)
Audit: GREEN (paper); Lean open -/
theorem posSeries_gapSeries_rational
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (hα : ∃ q : ℚ, posSeries F b = q) :
    ∃ r : ℚ, gapSeries F b = r :=
  (posSeries_rational_iff_gapSeries_rational F hb
    (posSeries_summable_admissible F hb)).1 hα

/-- A rational position series yields `Q > 0` with `Q β_b ∈ ℤ`.
No `Nat.Coprime Q b`.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` §§4–5;
`lean/BFREE_IRRATIONALITY.md` §4.3.
Contract: C3+C4+C5 assembly (not C6)
Audit: GREEN (paper); Lean open

Index: `Q := q.den`. Must work for `b = 4` and even `Q`. -/
theorem exists_posQ_mul_gapSeries_int
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (hα : ∃ q : ℚ, posSeries F b = q) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ n : ℤ, (Q : ℝ) * gapSeries F b = n :=
  exists_pos_nat_mul_mem_int (posSeries_gapSeries_rational F hb hα)

theorem modelTrunc_eq_gapTailTrunc_ae
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    (fun a => modelTrunc F b J a) =ᵐ[rootMeasure F]
      fun a => gapTailTrunc F hb J a := by
  filter_upwards [ae_mem_survival_root F] with a hA
  rw [gapTailTrunc_eq_sum F hb J hA]
  rfl

/-- Lemma 4.1 mean bound from lattice Cesàro plus Palm of `distInt ∘ (Q * ·)`. -/
theorem trunc_mean_from_palm
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) {Q : ℕ} (hQ : 0 < Q)
    (hβ : ∃ z : ℤ, (Q : ℝ) * gapSeries F b = z) (J : ℕ) :
    ∫ a, distInt ((Q : ℝ) * gapTailTrunc F hb J a) ∂rootMeasure F
      ≤ (Q : ℝ) *
        ∫ a, (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F := by
  have hQ0 : (0 : ℝ) ≤ Q := (Nat.cast_pos.mpr hQ).le
  let f : ℝ → ℝ := fun t => distInt ((Q : ℝ) * t)
  have hLip : LipschitzWith ⟨(Q : ℝ), hQ0⟩ f := distInt_Q_lipschitz hQ0
  have hbdd : ∀ x, |f x| ≤ (1 : ℝ) / 2 := fun x => by
    rw [abs_of_nonneg (distInt_nonneg _)]
    exact distInt_le_half _
  have hces := cesaro_trunc_test_eq_root (F := F) (b := b) hb J hLip hbdd
  have hae := modelTrunc_eq_gapTailTrunc_ae F hb J
  have hfun :
      (fun a => f (modelTrunc F b J a)) =ᵐ[rootMeasure F]
        fun a => f (gapTailTrunc F hb J a) :=
    hae.mono fun a ha => congrArg f ha
  have hL :
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N, f (canonicalGapTailTrunc F b J n)) / N)
        atTop
        (𝓝 (∫ a, f (gapTailTrunc F hb J a) ∂rootMeasure F)) := by
    have hI := integral_congr_ae hfun
    simpa [hI] using hces
  have hR0 := canonical_mean_tail F hb J
  have hR :
      Tendsto (fun N : ℕ =>
        (Q : ℝ) *
          ((∑ n ∈ Finset.range N,
              (canonicalGapTail F b n - canonicalGapTailTrunc F b J n)) / N))
        atTop
        (𝓝 ((Q : ℝ) *
          ∫ a, (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F)) := by
    rw [expected_gapTail_sub_trunc F hb J]
    exact hR0.const_mul (Q : ℝ)
  have hpt : ∀ n : ℕ,
      f (canonicalGapTailTrunc F b J n) ≤
        (Q : ℝ) * (canonicalGapTail F b n - canonicalGapTailTrunc F b J n) := by
    intro n
    obtain ⟨z, hz⟩ := mul_canonicalGapTail_int F hb hβ n
    have hT0 : distInt ((Q : ℝ) * canonicalGapTail F b n) = 0 :=
      (distInt_eq_zero_iff_mem _).2 ⟨z, hz.symm⟩
    have hle :=
      canonicalGapTailTrunc_le_canonicalGapTail F hb J n
    have htri := distInt_le_trunc hQ0 hle
    simpa [f, hT0] using htri
  have hleN : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, f (canonicalGapTailTrunc F b J n)) / N ≤
        (Q : ℝ) *
          ((∑ n ∈ Finset.range N,
              (canonicalGapTail F b n - canonicalGapTailTrunc F b J n)) / N) := by
    intro N
    have hsum :=
      Finset.sum_le_sum (s := Finset.range N) fun n _ => hpt n
    have hdiv :=
      div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
    have hmul :
        (∑ n ∈ Finset.range N,
            (Q : ℝ) *
              (canonicalGapTail F b n - canonicalGapTailTrunc F b J n)) / N =
          (Q : ℝ) *
            ((∑ n ∈ Finset.range N,
                (canonicalGapTail F b n - canonicalGapTailTrunc F b J n)) / N) := by
      rw [← Finset.mul_sum]
      ring
    rwa [hmul] at hdiv
  exact le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hleN)

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` §5;
`lean/BFREE_IRRATIONALITY.md` §0.
Contract: C3+C4+C5 assembly (not C6)
Audit: GREEN

Public hypotheses: only `F` and `2 ≤ b`. -/
theorem posSeries_irrational
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    Irrational (posSeries F b) := by
  intro ⟨q, hq⟩
  obtain ⟨Q, hQ, z, hz⟩ :=
    exists_posQ_mul_gapSeries_int F hb ⟨q, hq.symm⟩
  have hβ : (Q : ℝ) * gapSeries F b ∈ Set.range fun n : ℤ => (n : ℝ) :=
    ⟨z, hz.symm⟩
  exact rational_posSeries_to_lattice_carry F hb hQ hβ
    (fun J => trunc_mean_from_palm F hb hQ ⟨z, hz⟩ J)

end PrimeGapNormality.BFree
