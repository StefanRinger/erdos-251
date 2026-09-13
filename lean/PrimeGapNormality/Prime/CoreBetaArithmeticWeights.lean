import PrimeGapNormality.Prime.CoreBetaLevelSupport
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Actual arithmetic beta weights

The parity-stopped Buchstab coefficients are indexed combinatorially by
sublists of a decreasing prime list.  This file descends them to honest
functions on natural divisors.  Unique factorization proves that two
sublists have the same product only when they are equal; consequently every
natural weight is one coefficient or zero.

The final divisor sums are exactly the Boolean Buchstab mains and hence
bracket coprimality.  No sieve-weight axioms or fundamental-lemma estimate
are assumed.
-/

namespace PrimeGapNormality.Prime.CoreBetaArithmeticWeights

open Finset CoreBetaBuchstab CoreBetaLevelSupport
open scoped BigOperators Classical

noncomputable section

/-- The finite set of all order-preserving selections from `P`. -/
def sublistFinset (P : List ℕ) : Finset (List ℕ) :=
  P.sublists'.toFinset

/-- Sublists representing the natural number `d`. -/
def productFiber (P : List ℕ) (d : ℕ) : Finset (List ℕ) :=
  (sublistFinset P).filter (fun selected => selected.prod = d)

/-- The actual upper or lower arithmetic weight.  Product-fibre uniqueness
below shows that this sum is a single Buchstab coefficient or zero. -/
def betaWeight (upper : Bool) (β : ℕ) (R : ℝ) (P : List ℕ) (d : ℕ) : ℝ :=
  ∑ selected ∈ productFiber P d,
    coefficient upper (test β R) [] selected

private theorem sublist_of_mem_sublistFinset {P selected : List ℕ}
    (h : selected ∈ sublistFinset P) : List.Sublist selected P := by
  exact List.mem_sublists'.mp (List.mem_toFinset.mp h)

private theorem prime_of_mem_sublist
    {P selected : List ℕ} (hsub : List.Sublist selected P)
    (hprime : ∀ p ∈ P, Nat.Prime p) :
    ∀ p ∈ selected, Nat.Prime p :=
  fun p hp => hprime p (hsub.subset hp)

/-- Distinct decreasing prime sublists have distinct products. -/
theorem sublist_prod_injective
    {P s t : List ℕ}
    (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hs : s ∈ sublistFinset P) (ht : t ∈ sublistFinset P)
    (hprod : s.prod = t.prod) : s = t := by
  have hsSub := sublist_of_mem_sublistFinset hs
  have htSub := sublist_of_mem_sublistFinset ht
  have hsPrime := prime_of_mem_sublist hsSub hprime
  have htPrime := prime_of_mem_sublist htSub hprime
  have hsFactors : List.Perm s s.prod.primeFactorsList :=
    Nat.primeFactorsList_unique rfl hsPrime
  have htFactors : List.Perm t s.prod.primeFactorsList :=
    Nat.primeFactorsList_unique hprod.symm htPrime
  have hperm : List.Perm s t := hsFactors.trans htFactors.symm
  exact hperm.eq_of_pairwise' (hdec.sublist hsSub) (hdec.sublist htSub)

theorem productFiber_card_le_one
    {P : List ℕ}
    (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p) (d : ℕ) :
    (productFiber P d).card ≤ 1 := by
  rw [card_le_one]
  intro s hs t ht
  have hs' := mem_filter.mp hs
  have ht' := mem_filter.mp ht
  exact sublist_prod_injective hdec hprime hs'.1 ht'.1
    (hs'.2.trans ht'.2.symm)

/-- On an occupied fibre the arithmetic weight is exactly its unique
combinatorial coefficient. -/
theorem betaWeight_eq_coefficient
    {P selected : List ℕ} {d : ℕ}
    (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hsub : List.Sublist selected P) (hprod : selected.prod = d)
    (upper : Bool) (β : ℕ) (R : ℝ) :
    betaWeight upper β R P d =
      coefficient upper (test β R) [] selected := by
  have hs : selected ∈ productFiber P d := by
    simp only [productFiber, mem_filter, sublistFinset, List.mem_toFinset,
      List.mem_sublists', hsub, hprod, and_self]
  have hfiber : productFiber P d = {selected} := by
    rw [eq_singleton_iff_unique_mem]
    exact ⟨hs, fun t ht =>
      (card_le_one.mp (productFiber_card_le_one hdec hprime d)
        t ht selected hs)⟩
  simp only [betaWeight, hfiber, sum_singleton]

theorem betaWeight_eq_zero_of_no_product
    {P : List ℕ} {d : ℕ}
    (h : ¬ ∃ selected : List ℕ, List.Sublist selected P ∧ selected.prod = d)
    (upper : Bool) (β : ℕ) (R : ℝ) :
    betaWeight upper β R P d = 0 := by
  have hempty : productFiber P d = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro selected hs
    have hs' := mem_filter.mp hs
    exact h ⟨selected, sublist_of_mem_sublistFinset hs'.1, hs'.2⟩
  simp [betaWeight, hempty]

/-- Every arithmetic beta weight has modulus at most one. -/
theorem betaWeight_abs_le_one
    {P : List ℕ}
    (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (upper : Bool) (β : ℕ) (R : ℝ) (d : ℕ) :
    |betaWeight upper β R P d| ≤ 1 := by
  unfold betaWeight
  calc
    |∑ selected ∈ productFiber P d,
        coefficient upper (test β R) [] selected| ≤
      ∑ selected ∈ productFiber P d,
        |coefficient upper (test β R) [] selected| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _selected ∈ productFiber P d, (1 : ℝ) :=
      sum_le_sum fun selected _ =>
        coefficient_abs_le_one upper (test β R) [] selected
    _ = ((productFiber P d).card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast productFiber_card_le_one hdec hprime d

/-- A nonzero arithmetic weight comes from one genuine selected sublist and
that selected coefficient is nonzero. -/
theorem exists_sublist_of_betaWeight_ne_zero
    {P : List ℕ}
    (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p)
    {upper : Bool} {β : ℕ} {R : ℝ} {d : ℕ}
    (hd : betaWeight upper β R P d ≠ 0) :
    ∃ selected : List ℕ, List.Sublist selected P ∧ selected.prod = d ∧
      coefficient upper (test β R) [] selected ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hd
  apply betaWeight_eq_zero_of_no_product
  rintro ⟨selected, hsub, hprod⟩
  have heq := betaWeight_eq_coefficient hdec hprime hsub hprod upper β R
  rw [heq] at hd
  exact hd (hnone selected hsub hprod)

private theorem sublist_prod_pos
    {P selected : List ℕ} (hsub : List.Sublist selected P)
    (hprime : ∀ p ∈ P, Nat.Prime p) : 0 < selected.prod := by
  exact List.prod_pos fun p hp => (hprime p (hsub.subset hp)).pos

private theorem sublist_nodup
    {P selected : List ℕ} (hdec : P.Pairwise (fun p q => q < p))
    (hsub : List.Sublist selected P) : selected.Nodup := by
  exact (hdec.sublist hsub).imp fun hqp => by omega

theorem squarefree_prod_of_prime_sublist
    {P selected : List ℕ}
    (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hsub : List.Sublist selected P) : Squarefree selected.prod := by
  have hpos := sublist_prod_pos hsub hprime
  have hperm : List.Perm selected selected.prod.primeFactorsList :=
    Nat.primeFactorsList_unique rfl (prime_of_mem_sublist hsub hprime)
  apply (Nat.squarefree_iff_nodup_primeFactorsList hpos.ne').2
  exact hperm.nodup_iff.mp (sublist_nodup hdec hsub)

/-- Nonzero weights have the honest arithmetic support required of beta
weights: squarefree divisors of the prime product, strictly below the level. -/
theorem betaWeight_support
    {β : ℕ} (hβ : 1 ≤ β) {Z R : ℝ} (hZ : 1 ≤ Z) (hR : 1 < R)
    (hlevel : Z ^ β ≤ R) (P : List ℕ)
    (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hbelow : ∀ p ∈ P, (p : ℝ) < Z)
    (upper : Bool) {d : ℕ} (hd : betaWeight upper β R P d ≠ 0) :
    Squarefree d ∧ d ∣ P.prod ∧ (d : ℝ) < R := by
  obtain ⟨selected, hsub, hprod, hcoeff⟩ :=
    exists_sublist_of_betaWeight_ne_zero hdec hprime hd
  have hlt := coefficient_ne_zero_product_lt hβ hZ hR hlevel upper selected
    (hdec.sublist hsub) (prime_of_mem_sublist hsub hprime)
    (fun p hp => hbelow p (hsub.subset hp)) hcoeff
  have hnatProduct : natProduct selected = (selected.prod : ℝ) := by
    simp [natProduct, CoreBetaBuchstab.product]
  rw [hnatProduct, hprod] at hlt
  exact ⟨hprod ▸ squarefree_prod_of_prime_sublist hdec hprime hsub,
    hprod ▸ hsub.prod_dvd_prod, hlt⟩

/-! ## Divisor sums -/

private theorem primeSublist_prod_dvd_iff
    {P selected : List ℕ} (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p) (hsub : List.Sublist selected P) (n : ℕ) :
    selected.prod ∣ n ↔ ∀ p ∈ selected, p ∣ n := by
  have hpair : selected.Pairwise (· ≠ ·) := sublist_nodup hdec hsub
  have hsPrime := prime_of_mem_sublist hsub hprime
  constructor
  · intro hd p hp
    exact (List.dvd_prod hp).trans hd
  · intro hall
    induction selected with
    | nil => simp
    | cons p ps ih =>
        rw [List.pairwise_cons] at hpair
        have htailSub : List.Sublist ps P :=
          (List.sublist_cons_of_sublist p (List.Sublist.refl ps)).trans hsub
        have hprimeTail : ∀ q ∈ ps, Nat.Prime q :=
          fun q hq => hsPrime q (by simp [hq])
        have hcop : Nat.Coprime p ps.prod := by
          rw [Nat.coprime_list_prod_right_iff]
          intro q hq
          exact (Nat.coprime_primes (hsPrime p (by simp)) (hprimeTail q hq)).mpr
            (hpair.1 q hq)
        rw [List.prod_cons]
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
          (hall p (by simp))
          (ih htailSub hpair.2 hprimeTail (fun q hq => hall q (by simp [hq])))

private theorem boolean_product
    (hit : ℕ → Prop) (selected : List ℕ) :
    product (fun p => if hit p then (1 : ℝ) else 0) selected =
      if ∀ p ∈ selected, hit p then 1 else 0 := by
  induction selected with
  | nil => simp
  | cons p ps ih =>
      rw [product_cons, ih]
      by_cases hp : hit p <;> simp [hp]

private theorem boolean_product_eq_prod_dvd
    {P selected : List ℕ} (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p) (hsub : List.Sublist selected P) (n : ℕ) :
    product (fun p => if p ∣ n then (1 : ℝ) else 0) selected =
      if selected.prod ∣ n then 1 else 0 := by
  simp only [primeSublist_prod_dvd_iff hdec hprime hsub]
  induction selected with
  | nil => simp [product]
  | cons p ps ih =>
      have htailSub : List.Sublist ps P :=
        (List.sublist_cons_of_sublist p (List.Sublist.refl ps)).trans hsub
      rw [product_cons]
      by_cases hp : p ∣ n <;> simp [hp, ih htailSub]

private theorem main_eq_sublistFinset_sum
    (P : List ℕ) (hdec : P.Pairwise (fun p q => q < p))
    (upper : Bool) (A : List ℕ → Prop) (g : ℕ → ℝ) :
    main upper A [] P g =
      ∑ selected ∈ sublistFinset P,
        coefficient upper A [] selected * product g selected := by
  unfold main sublistFinset
  have hnodupP : P.Nodup := hdec.imp fun hpq => by omega
  exact (List.sum_toFinset
    (fun selected => coefficient upper A [] selected * product g selected)
    ((List.nodup_sublists').2 hnodupP)).symm

private theorem divisorSum_betaWeight_eq_main
    {P : List ℕ} (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (upper : Bool) (β : ℕ) (R : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, betaWeight upper β R P d) =
      main upper (test β R) [] P (fun p => if p ∣ n then 1 else 0) := by
  rw [main_eq_sublistFinset_sum P hdec]
  unfold betaWeight productFiber
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro selected hs
  have hsub := sublist_of_mem_sublistFinset hs
  let c := coefficient upper (test β R) [] selected
  have hinner :
      (∑ d ∈ n.divisors, if selected.prod = d then c else 0) =
        if selected.prod ∣ n then c else 0 := by
    by_cases hd : selected.prod ∣ n
    · rw [if_pos hd]
      have hmem : selected.prod ∈ n.divisors :=
        Nat.mem_divisors.mpr ⟨hd, hn⟩
      rw [sum_eq_single selected.prod]
      · simp
      · intro d hdmem hne
        rw [if_neg]
        exact Ne.symm hne
      · exact fun hnot => (hnot hmem).elim
    · rw [if_neg hd]
      apply sum_eq_zero
      intro d hdmem
      rw [if_neg]
      intro heq
      apply hd
      rw [heq]
      exact Nat.dvd_of_mem_divisors hdmem
  rw [hinner, boolean_product_eq_prod_dvd hdec hprime hsub]
  by_cases hd : selected.prod ∣ n <;> simp [hd, c]

private theorem gcd_one_iff_avoids_primes
    {P : List ℕ} (hprime : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    Nat.gcd n P.prod = 1 ↔ ∀ p ∈ P, ¬ p ∣ n := by
  rw [← Nat.coprime_iff_gcd_eq_one, Nat.coprime_list_prod_right_iff]
  constructor
  · intro h p hp
    have hnp := h p hp
    rwa [Nat.coprime_comm, (hprime p hp).coprime_iff_not_dvd] at hnp
  · intro h p hp
    rw [Nat.coprime_comm, (hprime p hp).coprime_iff_not_dvd]
    exact h p hp

private theorem euler_divides (n : ℕ) (P : List ℕ) :
    euler (fun p => if p ∣ n then (1 : ℝ) else 0) P =
      if ∀ p ∈ P, ¬ p ∣ n then 1 else 0 := by
  induction P with
  | nil => simp [euler]
  | cons p ps ih =>
      rw [euler_cons, ih]
      by_cases hp : p ∣ n <;> simp [hp]

/-- The actual natural divisor weights bracket the coprimality indicator
pointwise. -/
theorem betaWeight_divisor_sandwich
    (β : ℕ) (R : ℝ) (P : List ℕ)
    (hdec : P.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ P, Nat.Prime p)
    {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, betaWeight false β R P d) ≤
      (if Nat.gcd n P.prod = 1 then (1 : ℝ) else 0) ∧
    (if Nat.gcd n P.prod = 1 then (1 : ℝ) else 0) ≤
      ∑ d ∈ n.divisors, betaWeight true β R P d := by
  rw [divisorSum_betaWeight_eq_main hdec hprime false β R hn,
    divisorSum_betaWeight_eq_main hdec hprime true β R hn]
  have hmiddle :
      (if Nat.gcd n P.prod = 1 then (1 : ℝ) else 0) =
        if ∀ p ∈ P, ¬ p ∣ n then 1 else 0 :=
    if_congr (gcd_one_iff_avoids_primes hprime n) rfl rfl
  rw [hmiddle]
  have hsieve := sieve_sandwich (test β R) P
    (fun p => if p ∣ n then (1 : ℝ) else 0)
    (by intro p hp; split_ifs <;> norm_num)
  rw [euler_divides] at hsieve
  exact hsieve

end
end PrimeGapNormality.Prime.CoreBetaArithmeticWeights
