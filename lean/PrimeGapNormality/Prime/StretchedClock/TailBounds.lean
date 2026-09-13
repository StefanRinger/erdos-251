import PrimeGapNormality.Prime.StretchedClock.TailAndPositions

/-!
# Freezing the actual stretched-clock tail

Monotonicity of the concrete steps makes every later variable denominator
at least the frozen denominator. A finite constant-clock prefix therefore
leaves only an explicit geometric prime-position remainder.
-/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset Filter
open scoped Topology
noncomputable section

theorem position_span_ge_step_mul {B : ℕ} (hB : 2 ≤ B) (n j : ℕ) :
    step B n * (j + 1) ≤ position B (n + j + 1) - position B n := by
  have hp := position_add B n (j + 1)
  have hs : step B n * (j + 1) ≤ ∑ i ∈ range (j + 1), step B (n + i) := by
    calc
      step B n * (j + 1) = ∑ _i ∈ range (j + 1), step B n := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ range (j + 1), step B (n + i) :=
        sum_le_sum fun i _ => step_mono hB (Nat.le_add_right _ _)
  rw [show n + (j + 1) = n + j + 1 by omega] at hp
  omega

theorem frozen_denominator_le_actual {B : ℕ} (hB : 2 ≤ B) (n j : ℕ) :
    (localBase B n : ℝ) ^ (j + 1) ≤
      (B : ℝ) ^ (position B (n + j + 1) - position B n) := by
  calc
    (localBase B n : ℝ) ^ (j + 1) = (B : ℝ) ^ (step B n * (j + 1)) := by
      simp only [localBase, Nat.cast_pow, pow_mul]
    _ ≤ _ := pow_le_pow_right₀ (one_lt_base hB).le (position_span_ge_step_mul hB n j)

theorem actualTail_le_frozenTail {B : ℕ} (hB : 2 ≤ B) (n : ℕ) :
    actualTail B n ≤ frozenTail (localBase B n) n := by
  have hq : (1 : ℝ) < localBase B n := by
    exact_mod_cast (show 1 < localBase B n by have := localBase_two_le hB n; omega)
  apply (actualTail_summable hB n).tsum_le_tsum _ (summable_posMass_nthPrime hq n)
  intro j
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos (zero_lt_one.trans hq) _)
    (frozen_denominator_le_actual hB n j)

theorem frozenTail_le_two {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    frozenTail q n ≤ frozenTail 2 n := by
  have hqreal : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  apply (summable_posMass_nthPrime hqreal n).tsum_le_tsum _
    (summable_posMass_nthPrime (by norm_num : (1 : ℝ) < 2) n)
  intro j
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by exact_mod_cast hq) _)

theorem frozenTail_two_le_polynomial (n : ℕ) :
    frozenTail 2 n ≤ 864 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have h := posMass_nthPrime_le_mul_sq (by norm_num : (1 : ℝ) < 2) n
  norm_num [posMassScaleCoeff, posMassGeomCoeff] at h
  simpa only [frozenTail, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using h

theorem position_span_eq_of_constant {B n H j : ℕ}
    (hconstant : ∀ i < H, step B (n + i) = step B n) (hj : j < H) :
    position B (n + j + 1) - position B n = step B n * (j + 1) := by
  have hp := position_add B n (j + 1)
  have hs : (∑ i ∈ range (j + 1), step B (n + i)) = step B n * (j + 1) := by
    rw [sum_congr rfl (fun i hi => hconstant i (by have := mem_range.mp hi; omega))]
    simp [Nat.mul_comm]
  rw [show n + (j + 1) = n + j + 1 by omega, hs] at hp
  omega

theorem actual_tail_term_eq_frozen_of_constant {B n H j : ℕ}
    (hconstant : ∀ i < H, step B (n + i) = step B n) (hj : j < H) :
    (nthPrime (n + j) : ℝ) /
        (B : ℝ) ^ (position B (n + j + 1) - position B n) =
      (nthPrime (n + j) : ℝ) / (localBase B n : ℝ) ^ (j + 1) := by
  rw [position_span_eq_of_constant hconstant hj]
  simp only [localBase, Nat.cast_pow, pow_mul]

/-- A good anchor has an actual constant-step prefix, not a probabilistic
condition on a rare label class. -/
theorem frozenTail_sub_actualTail_le {B n H : ℕ} (hB : 2 ≤ B)
    (hconstant : ∀ i < H, step B (n + i) = step B n) :
    frozenTail (localBase B n) n - actualTail B n ≤
      (localBase B n : ℝ)⁻¹ ^ H * frozenTail (localBase B n) (n + H) := by
  have hq : (1 : ℝ) < localBase B n := by
    exact_mod_cast (show 1 < localBase B n by have := localBase_two_le hB n; omega)
  have hprefix : posMassTrunc (localBase B n : ℝ) (fun k => (nthPrime k : ℝ)) n H ≤
      actualTail B n := by
    have h := (actualTail_summable hB n).sum_le_tsum (range H)
      (fun j _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (base_pos hB).le _))
    unfold posMassTrunc
    have he : (∑ j ∈ range H, (nthPrime (n + j) : ℝ) /
        (B : ℝ) ^ (position B (n + j + 1) - position B n)) =
        ∑ j ∈ range H, (nthPrime (n + j) : ℝ) / (localBase B n : ℝ) ^ (j + 1) :=
      sum_congr rfl fun j hj => actual_tail_term_eq_frozen_of_constant hconstant (mem_range.mp hj)
    rwa [he] at h
  have hsplit := posMass_eq_trunc_add hq (fun k => (nthPrime k : ℝ))
    (nthPrime_div_pow_summable hq) n H
  change frozenTail (localBase B n) n =
    posMassTrunc (localBase B n : ℝ) (fun k => (nthPrime k : ℝ)) n H +
      (localBase B n : ℝ)⁻¹ ^ H * frozenTail (localBase B n) (n + H) at hsplit
  linarith

/-- An explicit uniform freeze error; its exponential decay is more than
enough for `H = ceil(log(N)^2)`. -/
theorem abs_actualTail_sub_frozenTail_le {B n H : ℕ} (hB : 2 ≤ B)
    (hconstant : ∀ i < H, step B (n + i) = step B n) :
    |actualTail B n - frozenTail (localBase B n) n| ≤
      864 * ((n + H + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ H := by
  rw [abs_of_nonpos (sub_nonpos.mpr (actualTail_le_frozenTail hB n)), neg_sub]
  have hq : (2 : ℝ) ≤ localBase B n := by exact_mod_cast localBase_two_le hB n
  have hinv : (localBase B n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num : (0 : ℝ) < 2) hq
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ localBase B n)) hinv H
  have hF := (frozenTail_le_two (localBase_two_le hB n) (n + H)).trans
    (frozenTail_two_le_polynomial (n + H))
  have hF0 : 0 ≤ frozenTail (localBase B n) (n + H) :=
    posMass_nonneg (by exact_mod_cast (show 1 < localBase B n by have := localBase_two_le hB n; omega))
      (fun k => (nthPrime k : ℝ)) (fun k => Nat.cast_nonneg _) _
  calc
    frozenTail (localBase B n) n - actualTail B n ≤
        (localBase B n : ℝ)⁻¹ ^ H * frozenTail (localBase B n) (n + H) :=
      frozenTail_sub_actualTail_le hB hconstant
    _ ≤ (2 : ℝ)⁻¹ ^ H * (864 * ((n + H + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul hpow hF hF0 (by positivity)
    _ = _ := by ring

end
end PrimeGapNormality.Prime.StretchedClock
