import PrimeGapNormality.Prime.StretchedClock.RestrictedSelberg
import Mathlib.Algebra.BigOperators.Intervals

/-! Complete coprime blocks give the literal `φ(a)/a` harmonic factor. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset
noncomputable section
set_option maxHeartbeats 800000

def restrictedHarmonic (a R : ℕ) : ℝ :=
  ∑ n ∈ restrictedDivisors a R, (n : ℝ)⁻¹

theorem restrictedHarmonic_eq_Ico (a R : ℕ) :
    restrictedHarmonic a R =
      ∑ n ∈ Ico 1 (R + 1), if n.Coprime a then (n : ℝ)⁻¹ else 0 := by
  simp only [restrictedHarmonic, restrictedDivisors, sum_filter,
    Ico_add_one_right_eq_Icc]

theorem restrictedHarmonic_mono (a : ℕ) {R T : ℕ} (hRT : R ≤ T) :
    restrictedHarmonic a R ≤ restrictedHarmonic a T := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hnI, hnco⟩ := mem_restrictedDivisors.mp hn
    exact mem_restrictedDivisors.mpr
      ⟨mem_Icc.mpr ⟨(mem_Icc.mp hnI).1, (mem_Icc.mp hnI).2.trans hRT⟩, hnco⟩
  · intro n hn hnot
    exact inv_nonneg.mpr (Nat.cast_nonneg n)

theorem restrictedHarmonic_block_lower {a : ℕ} (ha : 0 < a) (j : ℕ) :
    (a.totient : ℝ) / ((a * (j + 1) : ℕ) : ℝ) ≤
      ∑ n ∈ (Ico (a * j + 1) (a * j + 1 + a)).filter
        (fun n => n.Coprime a), (n : ℝ)⁻¹ := by
  let E := (Ico (a * j + 1) (a * j + 1 + a)).filter
    (fun n => n.Coprime a)
  have hcard : E.card = a.totient := by
    simpa only [E, Nat.coprime_comm] using
      Nat.filter_coprime_Ico_eq_totient a (a * j + 1)
  calc
    (a.totient : ℝ) / ((a * (j + 1) : ℕ) : ℝ) =
        ∑ n ∈ E, (((a * (j + 1) : ℕ) : ℝ))⁻¹ := by
      simp [hcard, div_eq_mul_inv]
    _ ≤ ∑ n ∈ E, (n : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hnI := mem_Ico.mp (mem_filter.mp hn).1
      have hnpos : 0 < n := by omega
      have hnle : n ≤ a * (j + 1) := by nlinarith
      have hnposR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnpos
      have hnleR : (n : ℝ) ≤ ((a * (j + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hnle
      simpa only [one_div] using
        one_div_le_one_div_of_le hnposR hnleR

theorem restrictedHarmonic_complete_blocks {a : ℕ} (ha : 0 < a) (t : ℕ) :
    ((a.totient : ℝ) / (a : ℝ)) * (harmonic t : ℝ) ≤
      restrictedHarmonic a (a * t) := by
  induction t with
  | zero => simp [restrictedHarmonic, restrictedDivisors]
  | succ t ih =>
    let f : ℕ → ℝ := fun n => if n.Coprime a then (n : ℝ)⁻¹ else 0
    have hsplit : restrictedHarmonic a (a * (t + 1)) =
        restrictedHarmonic a (a * t) +
          ∑ n ∈ (Ico (a * t + 1) (a * t + 1 + a)).filter
            (fun n => n.Coprime a), (n : ℝ)⁻¹ := by
      rw [restrictedHarmonic_eq_Ico, restrictedHarmonic_eq_Ico, sum_filter]
      have he : a * (t + 1) + 1 = a * t + 1 + a := by ring
      rw [he]
      exact (sum_Ico_consecutive f (by omega : 1 ≤ a * t + 1)
        (by omega : a * t + 1 ≤ a * t + 1 + a)).symm
    have hstep := restrictedHarmonic_block_lower ha t
    have hleft : ((a.totient : ℝ) / (a : ℝ)) * (harmonic (t + 1) : ℝ) =
        ((a.totient : ℝ) / (a : ℝ)) * (harmonic t : ℝ) +
          (a.totient : ℝ) / ((a * (t + 1) : ℕ) : ℝ) := by
      rw [harmonic_succ]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hleft, hsplit]
    exact add_le_add ih hstep

/-- The exact lower bound needed for a uniformly growing AP modulus. -/
theorem restrictedJ_ge_totient_harmonic {a : ℕ} (ha : 0 < a) (R : ℕ) :
    ((a.totient : ℝ) / (a : ℝ)) * (harmonic (R / a) : ℝ) ≤
      restrictedJ a R := by
  have hmul : a * (R / a) ≤ R := by
    simpa only [Nat.mul_comm] using Nat.mul_div_le R a
  exact (restrictedHarmonic_complete_blocks ha (R / a)).trans
    ((restrictedHarmonic_mono a hmul).trans (restrictedJ_ge_sum_inv a R))

theorem restrictedJ_ge_totient_log {a : ℕ} (ha : 0 < a) (R : ℕ) :
    ((a.totient : ℝ) / (a : ℝ)) * Real.log ((R / a : ℕ) + 1 : ℝ) ≤
      restrictedJ a R := by
  have hlog : Real.log ((R / a : ℕ) + 1 : ℝ) ≤ (harmonic (R / a) : ℝ) := by
    simpa only [Nat.cast_add_one] using log_add_one_le_harmonic (R / a)
  exact (mul_le_mul_of_nonneg_left hlog
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans
      (restrictedJ_ge_totient_harmonic ha R)

end
end PrimeGapNormality.Prime.StretchedClock
