import PrimeGapNormality.Prime.StretchedClock.RestrictedQuadratic

/-! Genuine CRT counting for the filtered Selberg quadratic in one AP. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset
noncomputable section
set_option maxHeartbeats 1000000

def restrictedAPSet (a b Y : ℕ) : Finset ℕ :=
  (Icc 1 Y).filter fun n => n % a = b % a

def restrictedAPCount (a b Y l : ℕ) : ℕ :=
  ((Icc 1 Y).filter fun n => n % a = b % a ∧ l ∣ n).card

/-- The actual simultaneous AP/divisibility count, with error at most one. -/
theorem restrictedAPCount_rounding (a b Y l : ℕ)
    (ha : 0 < a) (hl : 0 < l) (hco : a.Coprime l) :
    |(restrictedAPCount a b Y l : ℝ) - (Y : ℝ) / ((a : ℝ) * l)| ≤ 1 := by
  let c := Nat.chineseRemainder hco b 0
  have hiff (n : ℕ) :
      (n % a = b % a ∧ l ∣ n) ↔ n ≡ (c : ℕ) [MOD a * l] := by
    constructor
    · intro hn
      exact Nat.chineseRemainder_modEq_unique hco hn.1
        (Nat.modEq_zero_iff_dvd.mpr hn.2)
    · intro hn
      obtain ⟨hna, hnl⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hco).mpr hn
      exact ⟨hna.trans c.property.1,
        Nat.modEq_zero_iff_dvd.mp (hnl.trans c.property.2)⟩
  have hset : ((Icc 1 Y).filter fun n => n % a = b % a ∧ l ∣ n) =
      (Ico 1 (1 + Y)).filter (fun n => n ≡ (c : ℕ) [MOD a * l]) := by
    ext n
    simp only [Nat.add_comm 1 Y, Ico_add_one_right_eq_Icc, mem_filter, hiff]
  have hm : 1 ≤ a * l := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero ha.ne' hl.ne')
  have hround := selbergCrt_residueCount_abs_le 1 Y (a * l) (c : ℕ) hm
  rw [restrictedAPCount, hset]
  simpa only [selbergCrt_residueCount, Nat.cast_mul] using hround

def restrictedDivisorIndicator (d n : ℕ) : ℝ := if d ∣ n then 1 else 0

def restrictedDivisorSum (a R n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 R, restrictedWeight a R d * restrictedDivisorIndicator d n

theorem restrictedDivisorIndicator_mul (d e n : ℕ) :
    restrictedDivisorIndicator d n * restrictedDivisorIndicator e n =
      restrictedDivisorIndicator (Nat.lcm d e) n := by
  unfold restrictedDivisorIndicator
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;>
    simp [hd, he, Nat.lcm_dvd_iff]

theorem restrictedAPCount_eq_indicator_sum (a b Y l : ℕ) :
    (restrictedAPCount a b Y l : ℝ) =
      ∑ n ∈ restrictedAPSet a b Y, restrictedDivisorIndicator l n := by
  have hset : ((Icc 1 Y).filter fun n => n % a = b % a ∧ l ∣ n) =
      (restrictedAPSet a b Y).filter (fun n => l ∣ n) := by
    ext n
    simp [restrictedAPSet, and_assoc]
  rw [restrictedAPCount, hset]
  simp [restrictedDivisorIndicator]

theorem restrictedDivisorSum_one_on_prime (a : ℕ) {R p : ℕ}
    (hR : 1 ≤ R) (hp : Nat.Prime p) (hRp : R < p) :
    restrictedDivisorSum a R p = 1 := by
  unfold restrictedDivisorSum
  rw [sum_eq_single 1]
  · simp [restrictedDivisorIndicator, restrictedWeight_one a hR]
  · intro d hd hd1
    have hnot : ¬ d ∣ p := by
      intro hdiv
      have hdp : d = p := (hp.eq_one_or_self_of_dvd d hdiv).resolve_left hd1
      have hdR := (mem_Icc.mp hd).2
      omega
    simp [restrictedDivisorIndicator, hnot]
  · intro hnot
    exact (hnot (mem_Icc.mpr ⟨le_rfl, hR⟩)).elim

/-- Expansion retains the literal progression count for each supported lcm. -/
theorem restrictedAP_square_expand (a R b Y : ℕ) :
    (∑ n ∈ restrictedAPSet a b Y, restrictedDivisorSum a R n ^ 2) =
      ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        restrictedWeight a R d * restrictedWeight a R e *
          (restrictedAPCount a b Y (Nat.lcm d e) : ℝ) := by
  calc
    _ = ∑ n ∈ restrictedAPSet a b Y, ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        restrictedWeight a R d * restrictedWeight a R e *
          restrictedDivisorIndicator (Nat.lcm d e) n := by
      apply sum_congr rfl
      intro n hn
      unfold restrictedDivisorSum
      rw [pow_two, sum_mul]
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
      apply sum_congr rfl
      intro e he
      calc
        _ = (restrictedWeight a R d * restrictedWeight a R e) *
            (restrictedDivisorIndicator d n * restrictedDivisorIndicator e n) := by ring
        _ = _ := by rw [restrictedDivisorIndicator_mul]
    _ = ∑ d ∈ Icc 1 R, ∑ n ∈ restrictedAPSet a b Y, ∑ e ∈ Icc 1 R,
        restrictedWeight a R d * restrictedWeight a R e *
          restrictedDivisorIndicator (Nat.lcm d e) n := by rw [sum_comm]
    _ = ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R, ∑ n ∈ restrictedAPSet a b Y,
        restrictedWeight a R d * restrictedWeight a R e *
          restrictedDivisorIndicator (Nat.lcm d e) n := by
      exact sum_congr rfl fun d hd => sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro e he
      rw [restrictedAPCount_eq_indicator_sum, mul_sum]

end
end PrimeGapNormality.Prime.StretchedClock
