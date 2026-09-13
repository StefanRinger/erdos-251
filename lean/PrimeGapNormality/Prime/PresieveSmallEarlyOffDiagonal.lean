import PrimeGapNormality.Prime.PresieveSmallEarlyVariance

/-!
# The rooted off-diagonal presieve kernel

This file records the exact one-prime two-point law which the early
Brun/CRT estimate has to average.  It also separates the genuinely
arithmetic pair discrepancy from the lower-order first-moment and
deleted-diagonal errors.

For a prime `p`, the forbidden class is uniform among the nonzero
classes.  Thus the joint survival factor is `1` if both candidates are
zero modulo `p`, `(p-2)/(p-1)` if exactly one is zero or if the two
nonzero residues coincide, and `(p-3)/(p-1)` for two distinct nonzero
residues.  In particular the exceptional local factors depend on
`p ∣ n`, `p ∣ m`, and `p ∣ n-m`; they cannot be replaced by the
unrooted two-point factor uniformly in the pair.

The final inequality is finite and assumption-free.  After division
by `(S * V(w))^2`, only `earlyPresievePairOffDiagonalMass -
(S * V(w))^2` requires a Brun/CRT summation estimate; all other terms
are bounded by `3 * S * V(w) + 2`.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-! ## Exact rooted local pair law -/

private theorem pair_filter_card_both_zero {w n m : ℕ}
    (p : SievePrime w) (hn : n % p.val = 0) (hm : m % p.val = 0) :
    ((univ : Finset (Fin (p.val - 1))).filter fun a =>
        n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1).card =
      p.val - 1 := by
  have hfilter :
      (univ : Finset (Fin (p.val - 1))).filter (fun a =>
          n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1) = univ := by
    apply filter_eq_self.mpr
    intro a _ha
    rw [hn, hm]
    omega
  rw [hfilter, card_univ, Fintype.card_fin]

private theorem pair_filter_card_left_zero {w n m : ℕ}
    (p : SievePrime w) (hn : n % p.val = 0) (hm : m % p.val ≠ 0) :
    ((univ : Finset (Fin (p.val - 1))).filter fun a =>
        n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1).card =
      p.val - 2 := by
  have hp : Nat.Prime p.val := Nat.prime_of_mem_primesLE p.property
  have hmpos : 0 < m % p.val := Nat.pos_of_ne_zero hm
  have hmlt : m % p.val < p.val := Nat.mod_lt _ hp.pos
  let am : Fin (p.val - 1) := ⟨m % p.val - 1, by omega⟩
  have hfilter :
      (univ : Finset (Fin (p.val - 1))).filter (fun a =>
          n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1) =
        univ.erase am := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨_ha, ham⟩
      refine ⟨?_, trivial⟩
      intro ha
      subst a
      apply ham
      dsimp [am]
      omega
    · rintro ⟨ha, _⟩
      constructor
      · rw [hn]
        omega
      · intro ham
        apply ha
        apply Fin.ext
        dsimp [am]
        omega
  rw [hfilter, card_erase_of_mem (mem_univ am), card_univ,
    Fintype.card_fin]
  omega

private theorem pair_filter_card_right_zero {w n m : ℕ}
    (p : SievePrime w) (hn : n % p.val ≠ 0) (hm : m % p.val = 0) :
    ((univ : Finset (Fin (p.val - 1))).filter fun a =>
        n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1).card =
      p.val - 2 := by
  have hp : Nat.Prime p.val := Nat.prime_of_mem_primesLE p.property
  have hnpos : 0 < n % p.val := Nat.pos_of_ne_zero hn
  have hnlt : n % p.val < p.val := Nat.mod_lt _ hp.pos
  let an : Fin (p.val - 1) := ⟨n % p.val - 1, by omega⟩
  have hfilter :
      (univ : Finset (Fin (p.val - 1))).filter (fun a =>
          n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1) =
        univ.erase an := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨han, _ha⟩
      refine ⟨?_, trivial⟩
      intro ha
      subst a
      apply han
      dsimp [an]
      omega
    · rintro ⟨ha, _⟩
      constructor
      · intro han
        apply ha
        apply Fin.ext
        dsimp [an]
        omega
      · rw [hm]
        omega
  rw [hfilter, card_erase_of_mem (mem_univ an), card_univ,
    Fintype.card_fin]
  omega

private theorem pair_filter_card_same_nonzero {w n m : ℕ}
    (p : SievePrime w) (hn : n % p.val ≠ 0)
    (heq : n % p.val = m % p.val) :
    ((univ : Finset (Fin (p.val - 1))).filter fun a =>
        n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1).card =
      p.val - 2 := by
  have hp : Nat.Prime p.val := Nat.prime_of_mem_primesLE p.property
  have hnpos : 0 < n % p.val := Nat.pos_of_ne_zero hn
  have hnlt : n % p.val < p.val := Nat.mod_lt _ hp.pos
  let an : Fin (p.val - 1) := ⟨n % p.val - 1, by omega⟩
  have hfilter :
      (univ : Finset (Fin (p.val - 1))).filter (fun a =>
          n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1) =
        univ.erase an := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    rw [← heq]
    constructor
    · rintro ⟨han, _⟩
      refine ⟨?_, trivial⟩
      intro ha
      subst a
      apply han
      dsimp [an]
      omega
    · rintro ⟨ha, _⟩
      constructor <;> intro han <;> apply ha <;> apply Fin.ext <;>
        dsimp [an] <;> omega
  rw [hfilter, card_erase_of_mem (mem_univ an), card_univ,
    Fintype.card_fin]
  omega

private theorem pair_filter_card_distinct_nonzero {w n m : ℕ}
    (p : SievePrime w) (hn : n % p.val ≠ 0) (hm : m % p.val ≠ 0)
    (hne : n % p.val ≠ m % p.val) :
    ((univ : Finset (Fin (p.val - 1))).filter fun a =>
        n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1).card =
      p.val - 3 := by
  have hp : Nat.Prime p.val := Nat.prime_of_mem_primesLE p.property
  have hnpos : 0 < n % p.val := Nat.pos_of_ne_zero hn
  have hmpos : 0 < m % p.val := Nat.pos_of_ne_zero hm
  have hnlt : n % p.val < p.val := Nat.mod_lt _ hp.pos
  have hmlt : m % p.val < p.val := Nat.mod_lt _ hp.pos
  let an : Fin (p.val - 1) := ⟨n % p.val - 1, by omega⟩
  let am : Fin (p.val - 1) := ⟨m % p.val - 1, by omega⟩
  have hanm : an ≠ am := by
    intro h
    apply hne
    have hv := congrArg Fin.val h
    dsimp [an, am] at hv
    omega
  have hfilter :
      (univ : Finset (Fin (p.val - 1))).filter (fun a =>
          n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1) =
        (univ.erase an).erase am := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨han, ham⟩
      refine ⟨?_, ?_, trivial⟩
      · intro ha
        subst a
        apply ham
        dsimp [am]
        omega
      · intro ha
        subst a
        apply han
        dsimp [an]
        omega
    · rintro ⟨ham, han, _⟩
      constructor
      · intro h
        apply han
        apply Fin.ext
        dsimp [an]
        omega
      · intro h
        apply ham
        apply Fin.ext
        dsimp [am]
        omega
  have ham_mem : am ∈ univ.erase an := by simp [hanm.symm]
  rw [hfilter, card_erase_of_mem ham_mem,
    card_erase_of_mem (mem_univ an), card_univ, Fintype.card_fin]
  omega

/-- Exact one-prime rooted pair law.  The final branch is possible
only for primes at least three, so the natural subtraction `p-3` is
the literal number of allowed nonzero forbidden classes. -/
theorem earlyPresievePairLocalMass_eq_rooted_cases {w : ℕ}
    (p : SievePrime w) (n m : ℕ) :
    earlyPresievePairLocalMass p n m =
      if n % p.val = 0 then
        if m % p.val = 0 then 1
        else ((p.val - 2 : ℕ) : ℝ) / (p.val - 1 : ℕ)
      else if m % p.val = 0 then
        ((p.val - 2 : ℕ) : ℝ) / (p.val - 1 : ℕ)
      else if n % p.val = m % p.val then
        ((p.val - 2 : ℕ) : ℝ) / (p.val - 1 : ℕ)
      else ((p.val - 3 : ℕ) : ℝ) / (p.val - 1 : ℕ) := by
  rw [earlyPresievePairLocalMass_eq_card]
  split_ifs with hn hm hm' heq
  · rw [pair_filter_card_both_zero p hn hm]
    have hp : Nat.Prime p.val := Nat.prime_of_mem_primesLE p.property
    have hsub : 0 < p.val - 1 := Nat.sub_pos_iff_lt.mpr hp.one_lt
    exact div_self (Nat.cast_ne_zero.mpr
      hsub.ne')
  · rw [pair_filter_card_left_zero p hn hm]
  · rw [pair_filter_card_right_zero p hn hm']
  · rw [pair_filter_card_same_nonzero p hn heq]
  · rw [pair_filter_card_distinct_nonzero p hn hm' heq]

/-! ## Finite reduction to the genuine Brun pair discrepancy -/

/-- Total rooted joint survival mass over ordered distinct pairs in
the interval.  This is the quantity to which the uniform pair CRT
count applies. -/
def earlyPresievePairOffDiagonalMass (S w : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 S, ∑ m ∈ (Icc 1 S).erase n,
    earlyPresievePairWeight w n m

private def earlyPresieveProductOffDiagonalMass (S w : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 S, ∑ m ∈ (Icc 1 S).erase n,
    earlyPresieveOneWeight w n * earlyPresieveOneWeight w m

theorem earlyPresieve_offDiagonal_eq_pair_sub_product (S w : ℕ) :
    earlyPresieveOffDiagonalCovariance S w =
      earlyPresievePairOffDiagonalMass S w -
        earlyPresieveProductOffDiagonalMass S w := by
  unfold earlyPresieveOffDiagonalCovariance earlyPresievePairOffDiagonalMass
    earlyPresieveProductOffDiagonalMass earlyPresieveCovariance
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro n _hn
  rw [← sum_sub_distrib]

private theorem earlyPresieve_productOffDiagonal_eq_mean_sq_sub_diagSq
    (S w : ℕ) :
    earlyPresieveProductOffDiagonalMass S w =
      earlyPresieveUniformMean S w ^ 2 -
        ∑ n ∈ Icc 1 S, earlyPresieveOneWeight w n ^ 2 := by
  rw [earlyPresieve_uniformMean_eq_exact]
  unfold earlyPresieveProductOffDiagonalMass
  rw [pow_two, Finset.sum_mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have herase := Finset.sum_erase_add
    (s := Icc 1 S)
    (f := fun m => earlyPresieveOneWeight w n * earlyPresieveOneWeight w m)
    hn
  rw [pow_two]
  linarith

private theorem earlyPresieve_sum_oneWeight_sq_le_mean (S w : ℕ) :
    ∑ n ∈ Icc 1 S, earlyPresieveOneWeight w n ^ 2 ≤
      earlyPresieveUniformMean S w := by
  rw [earlyPresieve_uniformMean_eq_exact]
  apply sum_le_sum
  intro n _hn
  have h0 := earlyPresieveOneWeight_nonneg w n
  have h1 := earlyPresieveOneWeight_le_one w n
  nlinarith

/-- Quantitative finite reduction of the covariance sum to the
uniform Brun/CRT pair count.  The bound has no analytic hypothesis.
The `3 * main + 2` term is negligible at the paper scales by
`tendsto_ahlSmall_earlyPresieve_main_atTop`; the absolute pair
discrepancy displayed on the right is the sole remaining summation
estimate. -/
theorem abs_earlyPresieveOffDiagonalCovariance_le_pairBrunError
    (S w : ℕ) :
    |earlyPresieveOffDiagonalCovariance S w| ≤
      |earlyPresievePairOffDiagonalMass S w -
        (((S : ℝ) * eulerProdNat w) ^ 2)| +
      3 * ((S : ℝ) * eulerProdNat w) + 2 := by
  let main : ℝ := (S : ℝ) * eulerProdNat w
  let mean : ℝ := earlyPresieveUniformMean S w
  let diag : ℝ := ∑ n ∈ Icc 1 S, earlyPresieveOneWeight w n ^ 2
  have hmain0 : 0 ≤ main :=
    mul_nonneg (Nat.cast_nonneg _) (eulerProdNat_pos w).le
  have hmean0 : 0 ≤ mean := by
    dsimp only [mean]
    rw [earlyPresieve_uniformMean_eq_exact]
    exact sum_nonneg fun n _hn => earlyPresieveOneWeight_nonneg w n
  have hmeanerr : |mean - main| ≤ 1 := by
    simpa only [mean, main] using
      earlyPresieve_uniformMean_abs_sub_main_le_one S w
  have hdiff : mean - main ≤ 1 := (le_abs_self (mean - main)).trans hmeanerr
  have hmeanle : mean ≤ main + 1 := by linarith
  have hdiag0 : 0 ≤ diag := by
    dsimp only [diag]
    exact sum_nonneg fun n _hn => sq_nonneg _
  have hdiag : diag ≤ mean := by
    simpa only [diag, mean] using earlyPresieve_sum_oneWeight_sq_le_mean S w
  have hsquares : |mean ^ 2 - main ^ 2| ≤ 2 * main + 1 := by
    rw [sq_sub_sq, abs_mul]
    have hsum0 : 0 ≤ mean + main := add_nonneg hmean0 hmain0
    rw [abs_of_nonneg hsum0]
    calc
      (mean + main) * |mean - main| ≤ (mean + main) * 1 :=
        mul_le_mul_of_nonneg_left hmeanerr hsum0
      _ ≤ 2 * main + 1 := by nlinarith
  rw [earlyPresieve_offDiagonal_eq_pair_sub_product,
    earlyPresieve_productOffDiagonal_eq_mean_sq_sub_diagSq]
  change |earlyPresievePairOffDiagonalMass S w - (mean ^ 2 - diag)| ≤
    |earlyPresievePairOffDiagonalMass S w - main ^ 2| + 3 * main + 2
  have htri :
      |earlyPresievePairOffDiagonalMass S w - (mean ^ 2 - diag)| ≤
        |earlyPresievePairOffDiagonalMass S w - main ^ 2| +
          |mean ^ 2 - main ^ 2| + |diag| := by
    calc
      |earlyPresievePairOffDiagonalMass S w - (mean ^ 2 - diag)| =
          |(earlyPresievePairOffDiagonalMass S w - main ^ 2) -
            (mean ^ 2 - main ^ 2) + diag| := by ring_nf
      _ ≤ |(earlyPresievePairOffDiagonalMass S w - main ^ 2) -
            (mean ^ 2 - main ^ 2)| + |diag| := abs_add_le _ _
      _ ≤ |earlyPresievePairOffDiagonalMass S w - main ^ 2| +
            |mean ^ 2 - main ^ 2| + |diag| := by
          gcongr
          exact abs_sub _ _
  refine htri.trans ?_
  rw [abs_of_nonneg hdiag0]
  calc
    |earlyPresievePairOffDiagonalMass S w - main ^ 2| +
          |mean ^ 2 - main ^ 2| + diag ≤
        |earlyPresievePairOffDiagonalMass S w - main ^ 2| +
          (2 * main + 1) + mean := by gcongr
    _ ≤ |earlyPresievePairOffDiagonalMass S w - main ^ 2| +
          3 * main + 2 := by linarith

end

end PrimeGapNormality.Prime
