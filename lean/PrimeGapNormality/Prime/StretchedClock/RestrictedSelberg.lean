import PrimeGapNormality.Prime.FiniteSelbergWeights

/-!
# Coprimality-restricted Selberg normalization

This is the literal finite diagonal mass used to sieve a unit residue
class modulo `a`. The harmonic comparison is proved by restricting the
existing radical fibers; no unfiltered sieve bound is substituted for it.
-/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset
open scoped ArithmeticFunction.Moebius
noncomputable section
set_option maxHeartbeats 800000

def restrictedDivisors (a R : ℕ) : Finset ℕ :=
  (Icc 1 R).filter fun d => d.Coprime a

def restrictedJ (a R : ℕ) : ℝ :=
  ∑ d ∈ restrictedDivisors a R, selbergJR_term d

theorem mem_restrictedDivisors {a R d : ℕ} :
    d ∈ restrictedDivisors a R ↔ d ∈ Icc 1 R ∧ d.Coprime a :=
  mem_filter

theorem restrictedJ_nonneg (a R : ℕ) : 0 ≤ restrictedJ a R := by
  apply sum_nonneg
  intro d hd
  exact selbergJR_term_nonneg (by
    have := (mem_Icc.mp (mem_restrictedDivisors.mp hd).1).1
    omega)

theorem restrictedJ_ge_one (a : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    (1 : ℝ) ≤ restrictedJ a R := by
  have hmem : 1 ∈ restrictedDivisors a R := by
    simp [restrictedDivisors, hR]
  have hterm : selbergJR_term 1 = 1 := by
    simp [selbergJR_term, ArithmeticFunction.moebius_apply_one]
  calc
    (1 : ℝ) = selbergJR_term 1 := hterm.symm
    _ ≤ ∑ d ∈ restrictedDivisors a R, selbergJR_term d := by
      apply single_le_sum _ hmem
      intro d hd
      exact selbergJR_term_nonneg (by
        have := (mem_Icc.mp (mem_restrictedDivisors.mp hd).1).1
        omega)
    _ = restrictedJ a R := rfl

theorem restrictedJ_pos (a : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    0 < restrictedJ a R :=
  zero_lt_one.trans_le (restrictedJ_ge_one a hR)

theorem restricted_radical_mem {a R n : ℕ}
    (hn : n ∈ restrictedDivisors a R) :
    UniqueFactorizationMonoid.radical n ∈ restrictedDivisors a R := by
  obtain ⟨hnI, hnco⟩ := mem_restrictedDivisors.mp hn
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hnI).1
  apply mem_restrictedDivisors.mpr
  refine ⟨mem_Icc.mpr ⟨Nat.radical_pos n, ?_⟩, ?_⟩
  · exact (Nat.radical_le_self_iff.mpr hn0).trans (mem_Icc.mp hnI).2
  · exact Nat.Coprime.of_dvd_left UniqueFactorizationMonoid.radical_dvd_self hnco

/-- The restricted fiber is a genuine subsum of the already bounded
unrestricted radical fiber. -/
theorem restricted_radical_fiber_le (a R d : ℕ) :
    (∑ n ∈ (restrictedDivisors a R).filter
      (fun n => UniqueFactorizationMonoid.radical n = d), (n : ℝ)⁻¹) ≤
      selbergJR_term d := by
  apply le_trans _ (selbergJR_sum_rad_le_term R d)
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hn, hrad⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨(mem_restrictedDivisors.mp hn).1, hrad⟩
  · intro n hn hnot
    exact inv_nonneg.mpr (Nat.cast_nonneg n)

/-- Exact coprimality-restricted harmonic comparison. -/
theorem restrictedJ_ge_sum_inv (a R : ℕ) :
    (∑ n ∈ restrictedDivisors a R, (n : ℝ)⁻¹) ≤ restrictedJ a R := by
  have hmaps : ∀ n ∈ restrictedDivisors a R,
      UniqueFactorizationMonoid.radical n ∈ restrictedDivisors a R :=
    fun n hn => restricted_radical_mem hn
  have hsplit :
      (∑ n ∈ restrictedDivisors a R, (n : ℝ)⁻¹) =
        ∑ d ∈ restrictedDivisors a R,
          ∑ n ∈ (restrictedDivisors a R).filter
            (fun n => UniqueFactorizationMonoid.radical n = d), (n : ℝ)⁻¹ :=
    (sum_fiberwise_of_maps_to hmaps fun n => (n : ℝ)⁻¹).symm
  rw [hsplit, restrictedJ]
  exact sum_le_sum fun d hd => restricted_radical_fiber_le a R d

end
end PrimeGapNormality.Prime.StretchedClock
