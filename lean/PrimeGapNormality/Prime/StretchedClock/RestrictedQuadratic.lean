import PrimeGapNormality.Prime.StretchedClock.RestrictedWeights
import PrimeGapNormality.Prime.FiniteSelbergIntervalCap

/-! Normalization, finite divisor inversion and the restricted quadratic. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset
noncomputable section
set_option maxHeartbeats 1000000

theorem restrictedWeight_one (a : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    restrictedWeight a R 1 = 1 := by
  have hJ : restrictedJ a R ≠ 0 := (restrictedJ_pos a hR).ne'
  rw [restrictedWeight, Nat.cast_one, one_mul, Nat.div_one]
  simp only [one_mul]
  calc
    _ = ∑ m ∈ Icc 1 R,
        if m.Coprime a then selbergJR_term m / restrictedJ a R else 0 := by
      apply sum_congr rfl
      intro m hm
      by_cases hco : m.Coprime a
      · rw [restrictedY, if_pos hco, if_pos hco, selbergJR_term]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      · simp [restrictedY, hco]
    _ = ∑ m ∈ restrictedDivisors a R, selbergJR_term m / restrictedJ a R := by
      rw [restrictedDivisors, sum_filter]
    _ = restrictedJ a R / restrictedJ a R := by
      rw [← sum_div]
      rfl
    _ = 1 := div_self hJ

theorem restrictedWeight_div_eq_inner {a R d : ℕ} (hd : d ∈ Icc 1 R) :
    restrictedWeight a R d / (d : ℝ) =
      ∑ m ∈ Icc 1 (R / d),
        (ArithmeticFunction.moebius m : ℝ) * restrictedY a R (d * m) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hd).1)
  rw [restrictedWeight, mul_div_cancel_left₀ _ hd0]

theorem restricted_divisor_inversion {a R r : ℕ} (hr : r ∈ Icc 1 R) :
    (∑ d ∈ Icc 1 R with r ∣ d, restrictedWeight a R d / (d : ℝ)) =
      restrictedY a R r := by
  have hlhs :
      (∑ d ∈ Icc 1 R with r ∣ d, restrictedWeight a R d / (d : ℝ)) =
      ∑ d ∈ Icc 1 R with r ∣ d, ∑ m ∈ Icc 1 (R / d),
        (ArithmeticFunction.moebius m : ℝ) * restrictedY a R (d * m) := by
    exact sum_congr rfl fun d hd => restrictedWeight_div_eq_inner (mem_filter.mp hd).1
  rw [hlhs, finiteSelberg_sum_multiples hr]
  let T := R / r
  have hrpos : 0 < r := by have := (mem_Icc.mp hr).1; omega
  have hT : 1 ≤ T := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.div_pos (mem_Icc.mp hr).2 hrpos).ne'
  calc
    _ = ∑ q ∈ Icc 1 T, ∑ k ∈ q.divisors,
        (ArithmeticFunction.moebius (q / k) : ℝ) * restrictedY a R (r * q) := by
      calc
        _ = ∑ q ∈ Icc 1 T, ∑ k ∈ q.divisors,
            (ArithmeticFunction.moebius (q / k) : ℝ) *
              restrictedY a R (r * (k * (q / k))) := by
          simpa [T, Nat.div_div_eq_div_mul, mul_assoc] using
            finiteSelberg_sum_hyperbola T
              (fun k m => (ArithmeticFunction.moebius m : ℝ) *
                restrictedY a R (r * (k * m)))
        _ = _ := by
          apply sum_congr rfl
          intro q hq
          apply sum_congr rfl
          intro k hk
          rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hk)]
    _ = ∑ q ∈ Icc 1 T,
        (if q = 1 then 1 else 0) * restrictedY a R (r * q) := by
      apply sum_congr rfl
      intro q hq
      rw [← sum_mul, finiteSelberg_sum_moebius_div_divisors]
    _ = restrictedY a R r := by simp [hT]

theorem restricted_diagonalY_eq (a : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    (∑ r ∈ Icc 1 R, (r.totient : ℝ) * restrictedY a R r ^ 2) =
      1 / restrictedJ a R := by
  have hJ : restrictedJ a R ≠ 0 := (restrictedJ_pos a hR).ne'
  calc
    _ = ∑ r ∈ Icc 1 R,
        if r.Coprime a then selbergJR_term r / restrictedJ a R ^ 2 else 0 := by
      apply sum_congr rfl
      intro r hr
      have hrpos : 0 < r := by have := (mem_Icc.mp hr).1; omega
      have hphi : (r.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hrpos).ne'
      by_cases hco : r.Coprime a
      · rw [restrictedY, if_pos hco, if_pos hco, selbergJR_term]
        field_simp
      · simp [restrictedY, hco]
    _ = ∑ r ∈ restrictedDivisors a R, selbergJR_term r / restrictedJ a R ^ 2 := by
      rw [restrictedDivisors, sum_filter]
    _ = restrictedJ a R / restrictedJ a R ^ 2 := by
      rw [← sum_div]
      rfl
    _ = 1 / restrictedJ a R := by field_simp

theorem restricted_div_lcm_eq_gcd {d e : ℕ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (x y : ℝ) :
    x * y / (Nat.lcm d e : ℝ) =
      (Nat.gcd d e : ℝ) * (x / d) * (y / e) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hd)
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp he)
  have hl0 : (Nat.lcm d e : ℝ) ≠ 0 := by
    exact_mod_cast Nat.lcm_ne_zero
      (Nat.one_le_iff_ne_zero.mp hd) (Nat.one_le_iff_ne_zero.mp he)
  have hgl : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * (e : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have hinv : (Nat.lcm d e : ℝ)⁻¹ =
      (Nat.gcd d e : ℝ) * (d : ℝ)⁻¹ * (e : ℝ)⁻¹ := by
    field_simp
    nlinarith [hgl]
  simp only [div_eq_mul_inv, hinv]
  ring

/-- The exact quadratic main term; coprimality was already proved in the weights. -/
theorem restricted_quadratic_eq (a : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    (∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
      restrictedWeight a R d * restrictedWeight a R e / (Nat.lcm d e : ℝ)) =
        1 / restrictedJ a R := by
  calc
    _ = ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        (Nat.gcd d e : ℝ) * (restrictedWeight a R d / d) *
          (restrictedWeight a R e / e) := by
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro e he
      exact restricted_div_lcm_eq_gcd (mem_Icc.mp hd).1 (mem_Icc.mp he).1 _ _
    _ = ∑ r ∈ Icc 1 R, (r.totient : ℝ) *
        (∑ d ∈ Icc 1 R with r ∣ d, restrictedWeight a R d / d) ^ 2 :=
      finiteSelberg_gcd_diagonal R (fun d => restrictedWeight a R d / d)
    _ = ∑ r ∈ Icc 1 R, (r.totient : ℝ) * restrictedY a R r ^ 2 := by
      exact sum_congr rfl fun r hr => by rw [restricted_divisor_inversion hr]
    _ = 1 / restrictedJ a R := restricted_diagonalY_eq a hR

theorem restrictedWeight_double_error_le (a R : ℕ) (hR : 1 ≤ R)
    (E : ℕ → ℕ → ℝ)
    (hE : ∀ d ∈ Icc 1 R, ∀ e ∈ Icc 1 R,
      d.Coprime a → e.Coprime a → |E d e| ≤ 1) :
    |∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
      restrictedWeight a R d * restrictedWeight a R e * E d e| ≤ (R : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        |restrictedWeight a R d * restrictedWeight a R e * E d e| := by
      exact (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun d hd => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro e he
      by_cases hdco : d.Coprime a
      · by_cases heco : e.Coprime a
        · rw [abs_mul, abs_mul]
          exact mul_le_one₀
            (mul_le_one₀ (restrictedWeight_abs_le_one a hR)
              (abs_nonneg _) (restrictedWeight_abs_le_one a hR))
            (abs_nonneg _) (hE d hd e he hdco heco)
        · simp [restrictedWeight_zero_of_not_coprime heco]
      · simp [restrictedWeight_zero_of_not_coprime hdco]
    _ = (R : ℝ) ^ 2 := by simp [Nat.card_Icc, pow_two]

end
end PrimeGapNormality.Prime.StretchedClock
