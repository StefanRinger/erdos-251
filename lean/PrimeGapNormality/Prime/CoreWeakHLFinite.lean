import PrimeGapNormality.Prime.KuperbergAHL

/-! Uniform weaker Hardy–Littlewood input and its exact finite aggregation.
The error constant and threshold precede all tuple quantifiers. -/
namespace PrimeGapNormality.Prime.CoreWeakHL
open Finset Filter
open scoped Topology
noncomputable section

def UniformError (A : ℝ) : Prop :=
  ∃ C > 0, ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ E : Finset ℕ,
    (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
    (E.card : ℝ) ≤ (A / 2) * Real.log (Real.log (x : ℝ)) →
    hlAdmissible E →
    |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤
      C * (x : ℝ) * Real.exp (-A * Real.log (Real.log (x : ℝ)) ^ 2)

def combEnvelope (S r : ℕ) : ℝ := ((r : ℝ) + 1) * 2 ^ r * (S : ℝ) ^ r

theorem binomial_sum_le (S L r : ℕ) (hS : 1 ≤ S) :
    ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * (S.choose j : ℝ) ≤
      combEnvelope S r := by
  have hterm : ∀ j ∈ Icc L r,
      ((j - 1).choose (L - 1) : ℝ) * (S.choose j : ℝ) ≤
        (2 : ℝ) ^ r * (S : ℝ) ^ r := by
    intro j hj
    have hjr := (mem_Icc.mp hj).2
    have hc : (S.choose j : ℝ) ≤ (S : ℝ) ^ r := by
      exact_mod_cast (Nat.choose_le_pow S j).trans (pow_le_pow_right' hS hjr)
    exact mul_le_mul (choose_le_two_pow_of_le hjr) hc (Nat.cast_nonneg _)
      (by positivity)
  have hsum := sum_le_card_nsmul (Icc L r) _ _ hterm
  rw [nsmul_eq_mul] at hsum
  have hc : ((Icc L r).card : ℝ) ≤ (r : ℝ) + 1 := by
    rw [Nat.card_Icc]
    exact_mod_cast (Nat.sub_le (r + 1) L)
  exact hsum.trans (by
    unfold combEnvelope
    nlinarith [mul_le_mul_of_nonneg_right hc
      (show 0 ≤ (2 : ℝ) ^ r * (S : ℝ) ^ r by positivity)])

theorem signed_error_le_abs (n : ℕ) (e : ℝ) :
    (((-1 : ℝ) ^ n) * e)⁺ ≤ |e| := by
  calc
    _ ≤ |((-1 : ℝ) ^ n) * e| := sup_le (le_abs_self _) (abs_nonneg _)
    _ = |e| := by rw [abs_mul, abs_pow]; norm_num

theorem budget_le_raw_error {κ d : ℝ} {X : ℕ} {B : ℝ}
    (hN : windowNX X ≠ 0) (hS : 1 ≤ profileS κ X) (hB : 0 ≤ B)
    (herr : ∀ H ⊆ windowOmega κ X, H.card ≤ profileR (profileL κ X) d →
      |(rootedTupleCount X H : ℝ) - rootedMainTerm X H| ≤ B) :
    ahlBudget κ d X ≤ (1 / (windowNX X : ℝ)) *
      (combEnvelope (profileS κ X) (profileR (profileL κ X) d) * B) := by
  unfold ahlBudget
  rw [if_neg hN]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d),
        ((j - 1).choose (profileL κ X - 1) : ℝ) *
          ((profileS κ X).choose j : ℝ) * B := by
      apply sum_le_sum
      intro j hj
      have he := ahlLayer_le_choose_mul κ X j (profileL κ X) hB
        (fun H hH hc => (signed_error_le_abs _ _).trans
          (herr H hH (hc.le.trans (mem_Icc.mp hj).2)))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he
        (Nat.cast_nonneg ((j - 1).choose (profileL κ X - 1)))
    _ = (∑ j ∈ Icc (profileL κ X) (profileR (profileL κ X) d),
        ((j - 1).choose (profileL κ X - 1) : ℝ) *
          ((profileS κ X).choose j : ℝ)) * B := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (binomial_sum_le _ _ _ hS) hB

theorem rooted_error_le_endpoints {X : ℕ} {H : Finset ℕ} {B₁ B₂ : ℝ}
    (h0 : 0 ∉ H)
    (h₁ : |(hlCount X (insert 0 H) : ℝ) - hlMain (X : ℝ) (insert 0 H)| ≤ B₁)
    (h₂ : |(hlCount (2 * X) (insert 0 H) : ℝ) -
      hlMain (2 * X : ℝ) (insert 0 H)| ≤ B₂) :
    |(rootedTupleCount X H : ℝ) - rootedMainTerm X H| ≤ B₂ + B₁ := by
  rw [rooted_error_eq h0]
  have htriangle (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  exact (htriangle _ _).trans (add_le_add h₂ h₁)

end
end PrimeGapNormality.Prime.CoreWeakHL
