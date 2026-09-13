import PrimeGapNormality.Prime.CoreMovingRoughPolynomialGrowth
import PrimeGapNormality.Prime.CoreRoughThreshold

/-!
# Log-linear growth of the moving-rough enumeration

The eventual inequality `z(n)<n` puts every sufficiently large prime in the
moving-rough set.  Hence its increasing enumeration is bounded by one fixed
shift of `nthPrime`.  The proved Chebyshev inversion then gives the sharper
paper bound `a_i \ll (i+1) log(i+2)`, not merely polynomial growth.

No density, Shape S, or Tail T input is used.
-/

namespace PrimeGapNormality.Prime.CoreMovingRoughLogGrowth

open Filter
open CoreMovingRoughSequence CoreMovingRoughPolynomialGrowth

noncomputable section

/-- Literal global log-linear majorant for the moving-rough enumeration. -/
theorem exists_global_logLinear_bound
    {z : ℕ → ℕ} (hz : ∀ᶠ n : ℕ in atTop, z n < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ,
      (movingRoughSequence z i : ℝ) ≤
        C * ((i + 1 : ℕ) : ℝ) * Real.log ((i + 2 : ℕ) : ℝ) := by
  obtain ⟨N, hshift⟩ := exists_shifted_nthPrime_majorant hz
  let A : ℝ := Real.log ((N + 2 : ℕ) : ℝ) + 1
  let D : ℝ := A / Real.log 2 + 1
  let C : ℝ := 4 * (N + 1 : ℕ) * D
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by
    dsimp only [A]
    have : 0 ≤ Real.log ((N + 2 : ℕ) : ℝ) :=
      Real.log_natCast_nonneg _
    linarith
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro i
  have hseq : (movingRoughSequence z i : ℝ) ≤ nthPrime (i + N) := by
    exact_mod_cast hshift i
  have hp := nthPrime_le_succ_mul_log (i + N)
  have hindexNat : i + N + 1 ≤ (N + 1) * (i + 1) := by
    nlinarith [Nat.zero_le (N * i)]
  have hindex : ((i + N + 1 : ℕ) : ℝ) ≤
      (N + 1 : ℕ) * ((i + 1 : ℕ) : ℝ) := by
    exact_mod_cast hindexNat
  have hargNat : i + N + 2 ≤ (N + 2) * (i + 2) := by
    nlinarith [Nat.zero_le (N * i)]
  have harg : ((i + N + 2 : ℕ) : ℝ) ≤
      ((N + 2 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ) := by
    exact_mod_cast hargNat
  have hleftPos : (0 : ℝ) < (i + N + 2 : ℕ) := by positivity
  have hNne : (((N + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hine : (((i + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hlogShift : Real.log ((i + N + 2 : ℕ) : ℝ) ≤
      Real.log ((N + 2 : ℕ) : ℝ) +
        Real.log ((i + 2 : ℕ) : ℝ) := by
    have hh := Real.log_le_log hleftPos harg
    rw [Real.log_mul hNne hine] at hh
    exact hh
  have hlogBase : Real.log 2 ≤ Real.log ((i + 2 : ℕ) : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show 2 ≤ i + 2 by omega)
  have hAterm : A ≤
      (A / Real.log 2) * Real.log ((i + 2 : ℕ) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlogBase
      (div_nonneg hA hlogTwo.le)
    have heq : (A / Real.log 2) * Real.log 2 = A := by
      field_simp [hlogTwo.ne']
    rwa [heq] at hh
  have hlogBound : Real.log ((i + N + 2 : ℕ) : ℝ) + 1 ≤
      D * Real.log ((i + 2 : ℕ) : ℝ) := by
    dsimp only [A, D] at hAterm ⊢
    linarith
  have hlogNonneg : 0 ≤ Real.log ((i + N + 2 : ℕ) : ℝ) + 1 := by
    have := Real.log_natCast_nonneg (i + N + 2)
    linarith
  have hindexNonneg : 0 ≤ ((i + N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc
    (movingRoughSequence z i : ℝ) ≤ (nthPrime (i + N) : ℝ) := hseq
    _ ≤ 4 * ((i + N + 1 : ℕ) : ℝ) *
        (Real.log ((i + N + 2 : ℕ) : ℝ) + 1) := by
      simpa only [Nat.add_assoc] using hp
    _ ≤ 4 * (((N + 1 : ℕ) : ℝ) * ((i + 1 : ℕ) : ℝ)) *
        (D * Real.log ((i + 2 : ℕ) : ℝ)) := by
      have hfirst := mul_le_mul_of_nonneg_left hindex (by norm_num : (0 : ℝ) ≤ 4)
      exact mul_le_mul hfirst hlogBound hlogNonneg
        (by positivity)
    _ = C * ((i + 1 : ℕ) : ℝ) *
        Real.log ((i + 2 : ℕ) : ℝ) := by
      dsimp only [C]
      ring

/-- The paper's literal cutoff profile supplies the sole hypothesis of the
log-linear enumeration bound directly from `HasSlopeBudget`.  No density,
pattern comparison, or tail estimate is used. -/
theorem exists_global_logLinear_bound_zPsi
    {Ψ : ℝ → ℝ} {A : ℝ}
    (hSlope : CoreRoughThreshold.HasSlopeBudget Ψ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ,
      (movingRoughSequence (CoreRoughThreshold.zPsi Ψ) i : ℝ) ≤
        C * ((i + 1 : ℕ) : ℝ) * Real.log ((i + 2 : ℕ) : ℝ) :=
  exists_global_logLinear_bound hSlope.eventually_zPsi_lt

end
end PrimeGapNormality.Prime.CoreMovingRoughLogGrowth
