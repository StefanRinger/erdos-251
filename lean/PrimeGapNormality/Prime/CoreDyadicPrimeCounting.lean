import Mathlib.NumberTheory.Bertrand

/-!
Quantitative retention of the large-prime factor in the elementary Bertrand
argument. The finite checkpoint does not assume the absence of primes in
the dyadic interval and does not assume any prime-density statement.
-/

namespace PrimeGapNormality.Prime.CoreDyadicPrimeCounting

open Nat Finset
open scoped BigOperators

noncomputable section

def dyadicPrimes (n : ℕ) : Finset ℕ := (Ioc n (2 * n)).filter Nat.Prime

def smallPrimes (n : ℕ) : Finset ℕ :=
  (range (2 * n / 3 + 1)).filter Nat.Prime

def binomialFactor (n p : ℕ) : ℕ := p ^ (centralBinom n).factorization p

theorem dyadicPrimes_card (n : ℕ) :
    (dyadicPrimes n).card = Nat.primeCounting (2 * n) - Nat.primeCounting n := by
  have heq : dyadicPrimes n = Nat.primesLE (2 * n) \ Nat.primesLE n := by
    ext p
    simp only [dyadicPrimes, mem_filter, mem_Ioc, mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      exact ⟨⟨hhi, hp⟩, fun h ↦ (Nat.not_le_of_lt hlo) h.1⟩
    · rintro ⟨⟨hhi, hp⟩, hn⟩
      exact ⟨⟨Nat.lt_of_not_ge (fun hlo ↦ hn ⟨hlo, hp⟩), hhi⟩, hp⟩
  rw [heq, card_sdiff_of_subset (Nat.primesLE_mono (by omega : n ≤ 2 * n)),
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]

/-- The exact small/large prime factorization. Prime factors in the middle
range `(2n/3,n]` have exponent zero; the entire upper dyadic range remains. -/
theorem centralBinom_eq_small_mul_large {n : ℕ} (hn : 2 < n) :
    centralBinom n =
      (∏ p ∈ smallPrimes n, binomialFactor n p) *
        ∏ p ∈ dyadicPrimes n, binomialFactor n p := by
  have hsub : smallPrimes n ∪ dyadicPrimes n ⊆ range (2 * n + 1) := by
    intro p hp
    rcases mem_union.1 hp with hp | hp
    · have h := (mem_filter.1 hp).1
      simp only [mem_range] at h ⊢
      have := Nat.div_le_self (2 * n) 3
      omega
    · have h := (mem_Ioc.1 (mem_filter.1 hp).1).2
      exact mem_range.2 (by omega)
  have hprod : (∏ p ∈ smallPrimes n ∪ dyadicPrimes n, binomialFactor n p) =
      ∏ p ∈ range (2 * n + 1), binomialFactor n p := by
    apply Finset.prod_subset hsub
    intro p hp hnot
    have hp2 : p ≤ 2 * n := Nat.le_of_lt_succ (mem_range.1 hp)
    by_cases hprime : p.Prime
    · have hsmall : 2 * n / 3 < p := by
        by_contra h
        apply hnot
        exact mem_union_left _ (mem_filter.2 ⟨mem_range.2 (by omega), hprime⟩)
      have hpn : p ≤ n := by
        by_contra h
        apply hnot
        exact mem_union_right _ (mem_filter.2 ⟨mem_Ioc.2 ⟨by omega, hp2⟩, hprime⟩)
      have hmiddle : 2 * n < 3 * p := by omega
      simp only [binomialFactor,
        Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn hmiddle, pow_zero]
    · simp only [binomialFactor, Nat.factorization_eq_zero_of_not_prime _ hprime, pow_zero]
  have hdisj : Disjoint (smallPrimes n) (dyadicPrimes n) := by
    apply disjoint_left.2
    intro p hp hq
    have hsmall := mem_range.1 (mem_filter.1 hp).1
    have hlarge := (mem_Ioc.1 (mem_filter.1 hq).1).1
    omega
  rw [← Nat.prod_pow_factorization_centralBinom n]
  change (∏ p ∈ range (2 * n + 1), binomialFactor n p) = _
  rw [← hprod, Finset.prod_union hdisj]

/-- The small-prime estimate from Mathlib's Bertrand proof, now isolated
without a no-primes hypothesis. -/
theorem small_prime_product_le {n : ℕ} (hn : 0 < n) :
    (∏ p ∈ smallPrimes n, binomialFactor n p) ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have hn2 : 1 ≤ 2 * n := by omega
  rw [← Finset.prod_filter_mul_prod_filter_not (smallPrimes n) (· ≤ Nat.sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ ↦
      (show binomialFactor n p ≤ 2 * n from Nat.pow_factorization_choose_le (by omega))).trans ?_
    rw [Finset.prod_const]
    apply pow_right_mono₀ hn2
    have hsub : (smallPrimes n).filter (· ≤ Nat.sqrt (2 * n)) ⊆
        Icc 1 (Nat.sqrt (2 * n)) := by
      intro p hp
      obtain ⟨hp, hroot⟩ := mem_filter.1 hp
      exact mem_Icc.2 ⟨(mem_filter.1 hp).2.one_lt.le, hroot⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp ↦ (show binomialFactor n p ≤ p from ?_)).trans ?_
    · obtain ⟨hp, hroot⟩ := mem_filter.1 hp
      apply (pow_right_mono₀ (mem_filter.1 hp).2.one_lt.le
        (Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.1 hroot)))).trans
      exact (pow_one p).le
    · exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
        (fun p hp _ ↦ (mem_filter.1 hp).2.one_lt.le)

theorem large_prime_product_le {n : ℕ} (hn : 0 < n) :
    (∏ p ∈ dyadicPrimes n, binomialFactor n p) ≤
      (2 * n) ^ (dyadicPrimes n).card := by
  calc
    (∏ p ∈ dyadicPrimes n, binomialFactor n p) ≤
        ∏ _p ∈ dyadicPrimes n, 2 * n :=
      Finset.prod_le_prod' fun p _ ↦ Nat.pow_factorization_choose_le (by omega)
    _ = _ := Finset.prod_const _

/-- Quantitative Bertrand's finite checkpoint: all large prime factors are
retained and counted rather than discarded by a no-primes assumption. -/
theorem centralBinom_le_dyadic_count {n : ℕ} (hn : 4 ≤ n) :
    centralBinom n ≤
      (2 * n) ^ (Nat.sqrt (2 * n) + (dyadicPrimes n).card) * 4 ^ (2 * n / 3) := by
  rw [centralBinom_eq_small_mul_large (by omega : 2 < n)]
  calc
    (∏ p ∈ smallPrimes n, binomialFactor n p) *
        (∏ p ∈ dyadicPrimes n, binomialFactor n p) ≤
      ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) *
        (2 * n) ^ (dyadicPrimes n).card :=
      Nat.mul_le_mul (small_prime_product_le (by omega)) (large_prime_product_le (by omega))
    _ = _ := by rw [pow_add]; ac_rfl

end

end PrimeGapNormality.Prime.CoreDyadicPrimeCounting
