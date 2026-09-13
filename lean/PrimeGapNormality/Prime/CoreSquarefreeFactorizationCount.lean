import PrimeGapNormality.Prime.CoreOrderedFactorizationBound
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# Squarefree values of the ordered factorization count

The elementary ordered-factorization function used by the rough CRT error
is the actual Dirichlet-convolution power of the arithmetic zeta function.
On squarefree inputs, multiplicativity therefore evaluates it as one factor
`k` for every prime divisor.  This supplies the pointwise domination of
products of local residue counts without introducing an abstract divisor
function.
-/

namespace PrimeGapNormality.Prime.CoreSquarefreeFactorizationCount

open Finset
open scoped BigOperators ArithmeticFunction.zeta

noncomputable section

private theorem sum_divisors_div (f : ℕ → ℕ) (n : ℕ) :
    (∑ d ∈ n.divisors, f (n / d)) = ∑ d ∈ n.divisors, f d := by
  calc
    (∑ d ∈ n.divisors, f (n / d)) =
        ∑ ij ∈ n.divisorsAntidiagonal, f ij.2 := by
      simpa using
        (Nat.sum_divisorsAntidiagonal (n := n) (fun _d q ↦ f q)).symm
    _ = ∑ d ∈ n.divisors, f d := by
      simpa using
        (Nat.sum_divisorsAntidiagonal' (n := n) (fun _d q ↦ f q))

/-- The recursively defined ordered count is the value of the genuine
Dirichlet-convolution power `zeta^k`. -/
theorem orderedFactorizationCount_eq_zeta_pow
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    CoreOrderedFactorizationBound.orderedFactorizationCount k n =
      (ArithmeticFunction.zeta ^ k) n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j generalizing n with
  | zero =>
      simp [CoreOrderedFactorizationBound.orderedFactorizationCount,
        ArithmeticFunction.zeta_apply]
  | succ j ih =>
      have hpos : 1 ≤ 1 + j := by omega
      rw [show 1 + (j + 1) = (1 + j) + 1 by omega,
        CoreOrderedFactorizationBound.orderedFactorizationCount_succ
          (k := 1 + j) hpos,
        pow_succ, ArithmeticFunction.mul_zeta_apply]
      calc
        (∑ a ∈ n.divisors,
            CoreOrderedFactorizationBound.orderedFactorizationCount
              (1 + j) (n / a)) =
            ∑ a ∈ n.divisors,
              (ArithmeticFunction.zeta ^ (1 + j)) (n / a) := by
          apply sum_congr rfl
          intro a ha
          exact ih (n / a) (by omega)
        _ = ∑ a ∈ n.divisors,
              (ArithmeticFunction.zeta ^ (1 + j)) a :=
          sum_divisors_div (fun d ↦ (ArithmeticFunction.zeta ^ (1 + j)) d) n

/-- A convolution power of zeta takes the value `k` at every prime. -/
theorem zeta_pow_apply_prime (k : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    (ArithmeticFunction.zeta ^ k) p = k := by
  induction k with
  | zero =>
      simp [hp.ne_one]
  | succ k ih =>
      have hone : (ArithmeticFunction.zeta ^ k) 1 = 1 :=
        (ArithmeticFunction.isMultiplicative_zeta.pow).map_one
      rw [pow_succ, ArithmeticFunction.mul_zeta_apply, hp.divisors]
      simp [hp.ne_one, hp.ne_one.symm, hone, ih]
      omega

/-- Exact squarefree evaluation: an ordered `k`-factor choice assigns one
of the `k` factors independently to every prime divisor. -/
theorem orderedFactorizationCount_squarefree
    {k n : ℕ} (hk : 1 ≤ k) (hn : Squarefree n) :
    CoreOrderedFactorizationBound.orderedFactorizationCount k n =
      k ^ n.primeFactors.card := by
  rw [orderedFactorizationCount_eq_zeta_pow hk]
  have hmult : ArithmeticFunction.IsMultiplicative
      (ArithmeticFunction.zeta ^ k) :=
    ArithmeticFunction.isMultiplicative_zeta.pow
  calc
    (ArithmeticFunction.zeta ^ k) n =
        ∏ p ∈ n.primeFactors, (ArithmeticFunction.zeta ^ k) p :=
      (hmult.prod_primeFactors hn).symm
    _ = ∏ _p ∈ n.primeFactors, k := by
      apply prod_congr rfl
      intro p hpMem
      exact zeta_pow_apply_prime k (Nat.prime_of_mem_primeFactors hpMem)
    _ = k ^ n.primeFactors.card := by
      rw [prod_const]

/-- A product of local multiplicities bounded by `k` is pointwise bounded
by the actual ordered-factorization count on squarefree integers. -/
theorem prod_primeFactors_le_orderedFactorizationCount
    {k n : ℕ} (hk : 1 ≤ k) (hn : Squarefree n) (ν : ℕ → ℕ)
    (hν : ∀ p ∈ n.primeFactors, ν p ≤ k) :
    (∏ p ∈ n.primeFactors, ν p) ≤
      CoreOrderedFactorizationBound.orderedFactorizationCount k n := by
  rw [orderedFactorizationCount_squarefree hk hn]
  calc
    (∏ p ∈ n.primeFactors, ν p) ≤
        ∏ _p ∈ n.primeFactors, k := by
      exact prod_le_prod (fun _p _hpMem ↦ Nat.zero_le _)
        (fun p hpMem ↦ hν p hpMem)
    _ = k ^ n.primeFactors.card := by
      rw [prod_const]

/-- Summatory form used by rough CRT remainders.  The support is explicitly
squarefree and the strict level convention only shrinks the compiled
ordered-factorization envelope. -/
theorem squarefreeLocalProductSum_lt_le
    (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R) (ν : ℕ → ℕ)
    (hν : ∀ p, Nat.Prime p → ν p ≤ k) :
    (∑ d ∈ Ico 1 R,
        ((if Squarefree d then ∏ p ∈ d.primeFactors, ν p else 0 : ℕ) : ℝ)) ≤
      (R : ℝ) * (1 + Real.log R) ^ (k - 1) := by
  calc
    (∑ d ∈ Ico 1 R,
        ((if Squarefree d then ∏ p ∈ d.primeFactors, ν p else 0 : ℕ) : ℝ)) ≤
        ∑ d ∈ Ico 1 R,
          (CoreOrderedFactorizationBound.orderedFactorizationCount k d : ℝ) := by
      apply sum_le_sum
      intro d hd
      by_cases hsf : Squarefree d
      · simp only [hsf, if_true]
        exact_mod_cast prod_primeFactors_le_orderedFactorizationCount hk hsf ν
          (fun p hpMem ↦ hν p (Nat.prime_of_mem_primeFactors hpMem))
      · simp only [hsf, if_false, Nat.cast_zero]
        exact Nat.cast_nonneg _
    _ ≤ (R : ℝ) * (1 + Real.log R) ^ (k - 1) :=
      CoreOrderedFactorizationBound.orderedFactorizationSum_lt_le k R hk hR

end
end PrimeGapNormality.Prime.CoreSquarefreeFactorizationCount
