import PrimeGapNormality.Prime.CoreMovingRoughSequence
import PrimeGapNormality.Prime.ChebyshevNthPrime
import PrimeGapNormality.Prime.CoreCyclicSeriesConvergence

/-!
# Polynomial growth of the moving-threshold rough enumeration

Once `z(n)<n`, every sufficiently large prime is literally moving-rough.
The increasing enumeration of the moving-rough set is therefore bounded by
a fixed shift of the prime enumeration.  The proved Chebyshev bound for
`nthPrime` then gives a genuine global quadratic majorant, including the
finite initial segment.

No density, ShapeS, or gap-tail premise is used.
-/

namespace PrimeGapNormality.Prime.CoreMovingRoughPolynomialGrowth

open Filter
open CoreMovingRoughSequence CoreCyclic

noncomputable section

/-- A prime beyond the threshold where `z(n)<n` is an actual member of the
moving-rough set. -/
theorem prime_isMovingRough_of_large
    {z : ℕ → ℕ} {N p : ℕ}
    (hN : ∀ n, N ≤ n → z n < n) (hNp : N ≤ p) (hp : Nat.Prime p) :
    IsMovingRough z p := by
  refine ⟨hp.one_le, ?_⟩
  intro q hq hqp
  have hqpEq : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  rw [hqpEq]
  exact hN p hNp

/-- The actual moving-rough enumeration is pointwise bounded by one fixed
shift of the prime enumeration. -/
theorem exists_shifted_nthPrime_majorant
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) :
    ∃ N : ℕ, ∀ i : ℕ,
      movingRoughSequence z i ≤ nthPrime (i + N) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hz
  refine ⟨N, ?_⟩
  intro i
  let f : ℕ → ℕ := fun j ↦ nthPrime (j + N)
  have hmaps : Set.MapsTo f
      {j : ℕ | ∀ hf : Set.Finite (Set.ofPred (IsMovingRough z)),
        j < hf.toFinset.card}
      (Set.ofPred (IsMovingRough z)) := by
    intro j hj
    change IsMovingRough z (nthPrime (j + N))
    apply prime_isMovingRough_of_large hN
    · exact (show N ≤ j + N + 1 by omega).trans (succ_le_nthPrime (j + N))
    · exact prime_nthPrime _
  have hmono : StrictMonoOn f
      {j : ℕ | ∀ hf : Set.Finite (Set.ofPred (IsMovingRough z)),
        j < hf.toFinset.card} := by
    intro x hx y hy hxy
    exact nthPrime_strictMono (Nat.add_lt_add_right hxy N)
  exact Nat.nth_le_of_strictMonoOn_of_mapsTo f hmaps hmono

/-- Explicit global natural-number quadratic bound. -/
theorem exists_global_quadratic_bound
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) :
    ∃ C : ℕ, ∀ i : ℕ,
      movingRoughSequence z i ≤ C * (i + 1) ^ 2 := by
  obtain ⟨N, hprime⟩ := exists_shifted_nthPrime_majorant hz
  refine ⟨144 * (N + 1) ^ 2, ?_⟩
  intro i
  have hnth := nthPrime_le_succ_sq (i + N)
  have hindex : i + N + 1 ≤ (N + 1) * (i + 1) := by
    nlinarith [Nat.zero_le (N * i)]
  calc
    movingRoughSequence z i ≤ nthPrime (i + N) := hprime i
    _ ≤ 144 * (i + N + 1) ^ 2 := hnth
    _ ≤ 144 * ((N + 1) * (i + 1)) ^ 2 :=
      Nat.mul_le_mul_left 144 (Nat.pow_le_pow_left hindex 2)
    _ = (144 * (N + 1) ^ 2) * (i + 1) ^ 2 := by ring

/-- The actual position sequence has polynomial growth as a proved
corollary of the explicit global bound. -/
theorem movingRoughSequence_hasPolynomialGrowth
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) :
    HasPolynomialGrowth (fun i ↦ (movingRoughSequence z i : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_global_quadratic_bound hz
  refine ⟨C, 2, Nat.cast_nonneg _, ?_⟩
  intro i
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  dsimp only
  exact_mod_cast hC i

/-- Consecutive moving-rough gaps inherit a global quadratic majorant. -/
theorem exists_global_gap_quadratic_bound
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) :
    ∃ C : ℕ, ∀ i : ℕ,
      seqGap (movingRoughSequence z) i ≤ C * (i + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_global_quadratic_bound hz
  refine ⟨4 * C, ?_⟩
  intro i
  have hgap : seqGap (movingRoughSequence z) i ≤
      movingRoughSequence z (i + 1) := Nat.sub_le _ _
  have hnext := hC (i + 1)
  have hindex : i + 2 ≤ 2 * (i + 1) := by omega
  calc
    seqGap (movingRoughSequence z) i ≤
        movingRoughSequence z (i + 1) := hgap
    _ ≤ C * (i + 2) ^ 2 := by
      simpa only [Nat.add_assoc] using hnext
    _ ≤ C * (2 * (i + 1)) ^ 2 :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hindex 2)
    _ = (4 * C) * (i + 1) ^ 2 := by ring

theorem movingRoughGap_hasPolynomialGrowth
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) :
    HasPolynomialGrowth
      (fun i ↦ (seqGap (movingRoughSequence z) i : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_global_gap_quadratic_bound hz
  refine ⟨C, 2, Nat.cast_nonneg _, ?_⟩
  intro i
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  dsimp only
  exact_mod_cast hC i

end
end PrimeGapNormality.Prime.CoreMovingRoughPolynomialGrowth
