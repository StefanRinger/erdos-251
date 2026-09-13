import PrimeGapNormality.Prime.StretchedClock.RestrictedAPCount

/-! The actual finite prime AP majorant, with the restricted Selberg mass. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset
noncomputable section
set_option maxHeartbeats 1000000

theorem restrictedAP_square_le (a R b Y : ℕ) (ha : 0 < a) (hR : 1 ≤ R) :
    (∑ n ∈ restrictedAPSet a b Y, restrictedDivisorSum a R n ^ 2) ≤
      (Y : ℝ) / ((a : ℝ) * restrictedJ a R) + (R : ℝ) ^ 2 := by
  let E : ℕ → ℕ → ℝ := fun d e =>
    (restrictedAPCount a b Y (Nat.lcm d e) : ℝ) -
      (Y : ℝ) / ((a : ℝ) * (Nat.lcm d e : ℝ))
  let err : ℝ := ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
    restrictedWeight a R d * restrictedWeight a R e * E d e
  have hround : |err| ≤ (R : ℝ) ^ 2 := by
    apply restrictedWeight_double_error_le a R hR
    intro d hd e he hdco heco
    have hl : 0 < Nat.lcm d e := Nat.pos_of_ne_zero
      (Nat.lcm_ne_zero
        (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hd).1)
        (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp he).1))
    have hco : a.Coprime (Nat.lcm d e) :=
      (Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul d e)
        (Nat.Coprime.mul_left hdco heco)).symm
    exact restrictedAPCount_rounding a b Y (Nat.lcm d e) ha hl hco
  have hdecomp :
      (∑ n ∈ restrictedAPSet a b Y, restrictedDivisorSum a R n ^ 2) =
        ((Y : ℝ) / (a : ℝ)) *
          (∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
            restrictedWeight a R d * restrictedWeight a R e /
              (Nat.lcm d e : ℝ)) + err := by
    rw [restrictedAP_square_expand]
    calc
      _ = ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
          (((Y : ℝ) / (a : ℝ)) *
            (restrictedWeight a R d * restrictedWeight a R e /
              (Nat.lcm d e : ℝ)) +
            restrictedWeight a R d * restrictedWeight a R e * E d e) := by
        apply sum_congr rfl
        intro d hd
        apply sum_congr rfl
        intro e he
        dsimp [E]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by
        dsimp [err]
        simp_rw [sum_add_distrib]
        rw [mul_sum]
        apply congrArg₂ (fun x y : ℝ => x + y)
        · exact sum_congr rfl fun d hd => (mul_sum _ _ _).symm
        · rfl
  rw [hdecomp, restricted_quadratic_eq a hR]
  have hmain : (Y : ℝ) / (a : ℝ) * (1 / restrictedJ a R) =
      (Y : ℝ) / ((a : ℝ) * restrictedJ a R) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hmain]
  exact _root_.add_le_add le_rfl ((le_abs_self err).trans hround)

/-- A global-height prime AP count. No AP-distribution or tuple hypothesis
is used. The residue need not be a unit; all primes at most R are excluded. -/
theorem restricted_prime_ap_count_le (a R Y b : ℕ) (ha : 0 < a) (hR : 1 ≤ R) :
    ((((Icc 1 Y).filter fun p => Nat.Prime p ∧ R < p ∧ p % a = b % a).card : ℕ) : ℝ) ≤
      (Y : ℝ) / ((a : ℝ) * restrictedJ a R) + (R : ℝ) ^ 2 := by
  let P := (Icc 1 Y).filter fun p => Nat.Prime p ∧ R < p ∧ p % a = b % a
  have hsub : P ⊆ restrictedAPSet a b Y := by
    intro p hp
    obtain ⟨hpI, hprime, hRp, hmod⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hpI, hmod⟩
  calc
    (P.card : ℝ) = ∑ p ∈ P, (1 : ℝ) := by simp
    _ = ∑ p ∈ P, restrictedDivisorSum a R p ^ 2 := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨hpI, hprime, hRp, hmod⟩ := mem_filter.mp hp
      rw [restrictedDivisorSum_one_on_prime a hR hprime hRp]
      norm_num
    _ ≤ ∑ p ∈ restrictedAPSet a b Y, restrictedDivisorSum a R p ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot => sq_nonneg _)
    _ ≤ _ := restrictedAP_square_le a R b Y ha hR

end
end PrimeGapNormality.Prime.StretchedClock
