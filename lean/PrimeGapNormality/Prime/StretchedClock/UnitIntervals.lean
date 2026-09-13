import PrimeGapNormality.Prime.CoreResidueCounting
import PrimeGapNormality.Prime.StretchedClock.UnitTotient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

/-! Exact Möbius inversion and the `2^omega(a)` error for coprime integers
in a half-open interval. All sums are finite and use the actual totient. -/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset
open scoped Classical
noncomputable section

def unitCount (a lo len : ℕ) : ℕ :=
  ((Ico lo (lo + len)).filter fun n => a.Coprime n).card

private theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) =
      if n = 1 then 1 else 0 := by
  have hc := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) hc
  rw [ArithmeticFunction.coe_zeta_mul_apply] at h
  simpa [ArithmeticFunction.one_apply] using h

/-- The actual coprimality indicator, including the integer zero. -/
theorem coprime_indicator_eq_moebius {a : ℕ} (ha : 0 < a) (n : ℕ) :
    (if a.Coprime n then (1 : ℝ) else 0) =
      ∑ d ∈ a.divisors, if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  have hg : a.gcd n ≠ 0 := (Nat.gcd_pos_of_pos_left n ha).ne'
  have hfilter : a.divisors.filter (fun d => d ∣ n) = (a.gcd n).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hda, _⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hda hdn, hg⟩
    · rintro ⟨hdg, _⟩
      exact ⟨⟨hdg.trans (Nat.gcd_dvd_left a n), ha.ne'⟩,
        hdg.trans (Nat.gcd_dvd_right a n)⟩
  calc
    (if a.Coprime n then (1 : ℝ) else 0) =
        if a.gcd n = 1 then (1 : ℝ) else 0 := rfl
    _ = ∑ d ∈ (a.gcd n).divisors, (ArithmeticFunction.moebius d : ℝ) :=
      (sum_moebius_divisors _).symm
    _ = _ := by rw [← hfilter, sum_filter]

theorem unitCount_eq_moebius_sum {a : ℕ} (ha : 0 < a) (lo len : ℕ) :
    (unitCount a lo len : ℝ) =
      ∑ d ∈ a.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (((Ico lo (lo + len)).filter fun n => d ∣ n).card : ℝ) := by
  calc
    (unitCount a lo len : ℝ) =
        ∑ n ∈ Ico lo (lo + len), if a.Coprime n then (1 : ℝ) else 0 := by
      simp [unitCount, ← sum_filter]
    _ = ∑ n ∈ Ico lo (lo + len),
        ∑ d ∈ a.divisors, if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
      exact sum_congr rfl (fun n _ => coprime_indicator_eq_moebius ha n)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter]
      simp [mul_comm]

/-- The exact sum of absolute Möbius coefficients on the divisors. -/
theorem sum_abs_moebius_eq_two_pow {a : ℕ} (ha : 0 < a) :
    (∑ d ∈ a.divisors, |(ArithmeticFunction.moebius d : ℝ)|) =
      (2 : ℝ) ^ a.primeFactors.card := by
  have habs (d : ℕ) : |(ArithmeticFunction.moebius d : ℝ)| =
      if Squarefree d then (1 : ℝ) else 0 := by
    rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
    split_ifs <;> norm_num
  simp_rw [habs]
  rw [← sum_filter, Nat.sum_divisors_filter_squarefree ha.ne']
  simp only [Nat.factors_eq, sum_const, card_powerset, nsmul_eq_mul,
    mul_one, Nat.cast_pow, Nat.cast_ofNat] <;> rfl

private theorem card_dvd_Ico_one (a d : ℕ) :
    ((Ico 1 (1 + a)).filter fun n => d ∣ n).card = a / d := by
  have hs : Ico 1 (1 + a) = Ioc 0 a := by
    ext n
    simp only [mem_Ico, mem_Ioc]
    omega
  rw [hs]
  exact Nat.Ioc_filter_dvd_card_eq_div a d

/-- The reciprocal Möbius sum equals the actual totient density. -/
theorem sum_moebius_div_eq_totient_ratio {a : ℕ} (ha : 0 < a) :
    (∑ d ∈ a.divisors, (ArithmeticFunction.moebius d : ℝ) / d) =
      (a.totient : ℝ) / a := by
  have he := unitCount_eq_moebius_sum ha 1 a
  have hu : unitCount a 1 a = a.totient := Nat.filter_coprime_Ico_eq_totient a 1
  rw [hu] at he
  simp_rw [card_dvd_Ico_one] at he
  have hdens : (a.totient : ℝ) =
      (a : ℝ) * ∑ d ∈ a.divisors, (ArithmeticFunction.moebius d : ℝ) / d := by
    rw [he, mul_sum]
    apply sum_congr rfl
    intro d hd
    rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
    ring
  rw [hdens]
  field_simp [show (a : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr ha.ne']

/-- Each divisor class has a rounding error at most one. -/
theorem abs_card_dvd_Ico_sub_div (lo len d : ℕ) (hd : 0 < d) :
    |((((Ico lo (lo + len)).filter fun n => d ∣ n).card : ℝ) -
      (len : ℝ) / d)| ≤ 1 := by
  have hsets : ((Ico lo (lo + len)).filter fun n => d ∣ n) =
      ((Ico lo (lo + len)).filter fun n => n % d = 0 % d) := by
    ext n
    constructor
    · intro hn
      apply mem_filter.mpr
      refine ⟨(mem_filter.mp hn).1, ?_⟩
      simpa only [Nat.zero_mod] using Nat.dvd_iff_mod_eq_zero.mp (mem_filter.mp hn).2
    · intro hn
      apply mem_filter.mpr
      refine ⟨(mem_filter.mp hn).1, ?_⟩
      apply Nat.dvd_iff_mod_eq_zero.mpr
      simpa only [Nat.zero_mod] using (mem_filter.mp hn).2
  rw [hsets]
  exact core_abs_card_Ico_mod_sub_div lo len d 0 hd

/-- Uniform coprime counting, with the sharp elementary error `2^omega(a)`.
There is no relative error or hidden assumption on the interval's length. -/
theorem abs_unitCount_sub_density_le {a : ℕ} (ha : 0 < a) (lo len : ℕ) :
    |(unitCount a lo len : ℝ) - (len : ℝ) * (a.totient : ℝ) / a| ≤
      (2 : ℝ) ^ a.primeFactors.card := by
  have he : (unitCount a lo len : ℝ) - (len : ℝ) * (a.totient : ℝ) / a =
      ∑ d ∈ a.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (((((Ico lo (lo + len)).filter fun n => d ∣ n).card : ℝ)) -
          (len : ℝ) / d) := by
    rw [unitCount_eq_moebius_sum ha lo len]
    rw [show (len : ℝ) * (a.totient : ℝ) / a =
      (len : ℝ) * ((a.totient : ℝ) / a) by ring,
      ← sum_moebius_div_eq_totient_ratio ha, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun _ _ => by ring)
  rw [he, ← sum_abs_moebius_eq_two_pow ha]
  calc
    _ ≤ ∑ d ∈ a.divisors, |(ArithmeticFunction.moebius d : ℝ) *
        (((((Ico lo (lo + len)).filter fun n => d ∣ n).card : ℝ)) -
          (len : ℝ) / d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ a.divisors, |(ArithmeticFunction.moebius d : ℝ)| := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left
        (abs_card_dvd_Ico_sub_div lo len d (Nat.pos_of_mem_divisors hd))
        (abs_nonneg _)).trans_eq (mul_one _)

end
end PrimeGapNormality.Prime.StretchedClock
