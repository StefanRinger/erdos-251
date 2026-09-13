import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! An explicit bound for the coprime-residue error.  The only exceptional
Euler factors are 2, 3 and 5; no asymptotic totient estimate is assumed. -/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset
noncomputable section

private def primeCost (p : ℕ) : ℕ :=
  (if p = 2 then 8 else 1) * (if p = 3 then 4 else 1) *
    (if p = 5 then 2 else 1)

private theorem four_mul_prime_le (p : ℕ) (hp : p.Prime) :
    4 * p ≤ primeCost p * (p - 1) ^ 2 := by
  by_cases h2 : p = 2
  · subst p; norm_num [primeCost]
  by_cases h3 : p = 3
  · subst p; norm_num [primeCost]
  by_cases h5 : p = 5
  · subst p; norm_num [primeCost]
  have h7 : 7 ≤ p := by
    by_contra h
    have hp6 : p ≤ 6 := by omega
    interval_cases p <;> norm_num at *
  simp only [primeCost, if_neg h2, if_neg h3, if_neg h5, one_mul]
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  nlinarith

private theorem prod_primeCost_le (P : Finset ℕ) :
    (∏ p ∈ P, primeCost p) ≤ 64 := by
  simp only [primeCost, prod_mul_distrib, prod_ite_eq']
  split_ifs <;> norm_num

/-- A finite product inequality retaining the exact distinct-prime count. -/
theorem four_pow_card_mul_prime_product_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    4 ^ P.card * (∏ p ∈ P, p) ≤ 64 * (∏ p ∈ P, (p - 1)) ^ 2 := by
  have hprod := Finset.prod_le_prod (fun p hp => Nat.zero_le (4 * p))
    (fun p hp => four_mul_prime_le p (hP p hp))
  have hcost := prod_primeCost_le P
  calc
    4 ^ P.card * (∏ p ∈ P, p) = ∏ p ∈ P, (4 * p) := by
      rw [prod_mul_distrib, prod_const]
    _ ≤ ∏ p ∈ P, (primeCost p * (p - 1) ^ 2) := hprod
    _ = (∏ p ∈ P, primeCost p) * (∏ p ∈ P, (p - 1)) ^ 2 := by
      rw [prod_mul_distrib, prod_pow]
    _ ≤ 64 * (∏ p ∈ P, (p - 1)) ^ 2 := Nat.mul_le_mul_right _ hcost

/-- `4^omega(a) * a <= 64 * phi(a)^2` for the actual natural totient.
This includes `a = 1`; the zero modulus is deliberately excluded. -/
theorem four_pow_card_primeFactors_mul_le_totient_sq {a : ℕ} (ha : 0 < a) :
    4 ^ a.primeFactors.card * a ≤ 64 * a.totient ^ 2 := by
  let r : ℕ := ∏ p ∈ a.primeFactors, p
  let s : ℕ := ∏ p ∈ a.primeFactors, (p - 1)
  let t : ℕ := a / r
  have hr : 0 < r := by
    exact Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  have hra : r ∣ a := Nat.prod_primeFactors_dvd a
  have htr : t * r = a := Nat.div_mul_cancel hra
  have ht : 1 ≤ t := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    rw [hz, zero_mul] at htr
    omega
  have hphi : a.totient = t * s := Nat.totient_eq_div_primeFactors_mul a
  have hprod : 4 ^ a.primeFactors.card * r ≤ 64 * s ^ 2 :=
    four_pow_card_mul_prime_product_le a.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have ht2 : t ≤ t ^ 2 := by nlinarith
  calc
    4 ^ a.primeFactors.card * a = t * (4 ^ a.primeFactors.card * r) := by
      rw [← htr]; ring
    _ ≤ t * (64 * s ^ 2) := Nat.mul_le_mul_left t hprod
    _ ≤ t ^ 2 * (64 * s ^ 2) := Nat.mul_le_mul_right _ ht2
    _ = 64 * a.totient ^ 2 := by rw [hphi]; ring

end
end PrimeGapNormality.Prime.StretchedClock
