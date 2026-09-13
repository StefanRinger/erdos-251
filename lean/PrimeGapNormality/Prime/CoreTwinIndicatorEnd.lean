import PrimeGapNormality.Prime.CoreTwinInfinitude
import PrimeGapNormality.Prime.PrimeShortS

/-!
# The actual twin-gap binary indicator

This closes the paper's sparse binary example.  A twin-prime start is
identified with the unique zero-based prime index whose next gap is two;
the exceptional prime `2` is ruled out explicitly.  Kuperberg therefore
makes the one-support infinite, while the unconditional sieve result in
`CoreTwinGapDensity` already makes its density zero and the associated
number nonnormal.
-/

namespace PrimeGapNormality.Prime.CoreTwinIndicatorEnd

open CoreSparseBinarySeries CoreTwinGapDensity CoreTwinInfinitude
open scoped Classical Topology BigOperators

noncomputable section

/-- If `p` and `p+2` are prime, then `p` is not the exceptional prime two. -/
theorem twinPrimeStart_ne_two {p : ℕ} (hp2 : Nat.Prime (p + 2)) : p ≠ 2 := by
  intro hp
  subst p
  norm_num at hp2

/-- For an actual prime pair `p,p+2`, the prime with rank
`primeCounting' p + 1` is exactly `p+2`.  The only intervening integer
is even; the `p=2` exception was excluded above. -/
theorem nthPrime_succ_primeCounting'_eq_add_two {p : ℕ}
    (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2)) :
    nthPrime (Nat.primeCounting' p + 1) = p + 2 := by
  let i := Nat.primeCounting' p
  let j := Nat.primeCounting' (p + 2)
  have hi : nthPrime i = p := by
    dsimp only [i]
    exact nthPrime_primeCounting' hp
  have hj : nthPrime j = p + 2 := by
    dsimp only [j]
    exact nthPrime_primeCounting' hp2
  have hij : i < j := by
    apply (nthPrime_strictMono.lt_iff_lt).mp
    rw [hi, hj]
    omega
  have hupper : nthPrime (i + 1) ≤ p + 2 := by
    rw [← hj]
    exact nthPrime_mono (Nat.succ_le_of_lt hij)
  have hlower : p < nthPrime (i + 1) := by
    rw [← hi]
    exact nthPrime_strictMono (Nat.lt_succ_self i)
  have hpne : p ≠ 2 := twinPrimeStart_ne_two hp2
  have hpTwo : 2 ≤ p := hp.two_le
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hpne
  have hnotMiddle : ¬Nat.Prime (p + 1) := by
    intro hprime
    have hp1ne : p + 1 ≠ 2 := by
      have hp3 : 3 ≤ p := by omega
      omega
    have hp1odd : (p + 1) % 2 = 1 :=
      hprime.eq_two_or_odd.resolve_left hp1ne
    omega
  have hnextPrime := prime_nthPrime (i + 1)
  have hneq : nthPrime (i + 1) ≠ p + 1 := by
    intro he
    exact hnotMiddle (he ▸ hnextPrime)
  change nthPrime (i + 1) = p + 2
  omega

/-- A genuine twin-prime start maps to a one of the literal prime-gap
indicator. -/
theorem twinGapBit_primeCounting'_eq_one {p : ℕ}
    (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2)) :
    twinGapBit (Nat.primeCounting' p) = 1 := by
  have hnext := nthPrime_succ_primeCounting'_eq_add_two hp hp2
  have hhere := nthPrime_primeCounting' hp
  unfold twinGapBit primeGap
  rw [hnext, hhere]
  simp

/-- Conversely, a one in the actual indicator supplies the corresponding
pair of consecutive primes. -/
theorem twinPrimes_of_twinGapBit_eq_one {n : ℕ} (hn : twinGapBit n = 1) :
    Nat.Prime (nthPrime n) ∧ Nat.Prime (nthPrime n + 2) := by
  have hgap : primeGap n = 2 := by
    unfold twinGapBit at hn
    split_ifs at hn with h
    · exact h
  have hmono : nthPrime n < nthPrime (n + 1) :=
    nthPrime_strictMono (Nat.lt_succ_self n)
  have hnext : nthPrime (n + 1) = nthPrime n + 2 := by
    unfold primeGap at hgap
    omega
  exact ⟨prime_nthPrime n, by rw [← hnext]; exact prime_nthPrime (n + 1)⟩

/-- Actual bijection between physical twin-prime starts and the one-support
of the zero-based prime-gap indicator. -/
def twinPrimeStartEquivGapOne :
    {p : ℕ // Nat.Prime p ∧ Nat.Prime (p + 2)} ≃
      {n : ℕ // twinGapBit n = 1} where
  toFun p := ⟨Nat.primeCounting' p.1,
    twinGapBit_primeCounting'_eq_one p.2.1 p.2.2⟩
  invFun n := ⟨nthPrime n.1, twinPrimes_of_twinGapBit_eq_one n.2⟩
  left_inv p := by
    apply Subtype.ext
    exact nthPrime_primeCounting' p.2.1
  right_inv n := by
    apply Subtype.ext
    exact primeCounting'_nthPrime n.1

/-- Kuperberg makes the one-support of the actual twin-gap indicator
infinite. -/
theorem twinGapBit_support_infinite_of_kuperberg (hKup : KuperbergConj13) :
    Set.Infinite {n : ℕ | twinGapBit n = 1} := by
  have hsource := infinite_twinPrimeStarts_of_kuperberg hKup
  letI : Infinite {p : ℕ // Nat.Prime p ∧ Nat.Prime (p + 2)} :=
    Set.infinite_coe_iff.mpr hsource
  have htarget : Infinite {n : ℕ // twinGapBit n = 1} :=
    twinPrimeStartEquivGapOne.infinite_iff.mp inferInstance
  exact Set.infinite_coe_iff.mp htarget

/-- The displayed series is literally the binary series with digit one
exactly at a prime gap of two. -/
theorem twinGapBinarySeries_eq_literal :
    binarySeries twinGapBit =
      ∑' n : ℕ, (if primeGap n = 2 then (1 : ℝ) else 0) /
        (2 : ℝ) ^ (n + 1) := by
  unfold binarySeries
  apply tsum_congr
  intro n
  unfold twinGapBit
  split_ifs <;> simp

/-- The literal twin-gap digit series is summable, unconditionally. -/
theorem twinGapBinarySeries_summable :
    Summable (fun n : ℕ => (twinGapBit n : ℝ) /
      (2 : ℝ) ^ (n + 1)) :=
  binarySeries_summable twinGapBit_isBitSequence

/-- The actual base-two orbit has the shifted twin-gap digit tail; this
specializes the generic digit reconstruction and uses the unconditional
zero-density theorem to exclude the ambiguous eventually-one expansion. -/
theorem fract_two_pow_mul_twinGapBinarySeries (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * binarySeries twinGapBit) =
      binaryTail twinGapBit n :=
  fract_two_pow_mul_binarySeries twinGapBit_isBitSequence
    twinGapBit_hasZeroOneDensity n

/-- Under Kuperberg, the actual twin-gap binary series is irrational. -/
theorem twinGapBinarySeries_irrational_of_kuperberg
    (hKup : KuperbergConj13) :
    Irrational (binarySeries twinGapBit) :=
  (binarySeries_irrational_iff_support_infinite
    twinGapBit_isBitSequence twinGapBit_hasZeroOneDensity).2
      (twinGapBit_support_infinite_of_kuperberg hKup)

/-- Final paper endpoint: under Kuperberg the literal twin-gap indicator
series converges, is irrational, and is not normal in base two.  The last
claim is the unconditional fixed-dimensional sieve result. -/
theorem twinGapIndicator_end_of_kuperberg (hKup : KuperbergConj13) :
    Summable (fun n : ℕ => (twinGapBit n : ℝ) /
        (2 : ℝ) ^ (n + 1)) ∧
      Irrational (binarySeries twinGapBit) ∧
      ¬ PrimeGapNormality.BFree.IsNormal 2 (binarySeries twinGapBit) :=
  ⟨twinGapBinarySeries_summable,
    twinGapBinarySeries_irrational_of_kuperberg hKup,
    twinGapBinarySeries_not_isNormal_two⟩

end

end PrimeGapNormality.Prime.CoreTwinIndicatorEnd
