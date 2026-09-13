import PrimeGapNormality.Prime.CoreCyclicSeriesConvergence

/-! The rational half of the local-polynomial classification. Convergence
and the infinite boundary identity have been proved upstream. No tuple or
normality hypothesis is required for a vanishing canonical class. -/

namespace PrimeGapNormality.Prime.CoreCyclic

open MvPolynomial

/-- Every zero canonical class has an explicit rational series value on an
integer gap sequence of polynomial growth. -/
theorem infiniteSeries_rational_of_normalForm_zero
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℤ) (hg : HasPolynomialGrowth fun n => (g n : ℝ))
    (F : PeriodicLocal k) (hF : normalForm hB hk F = 0) (a : ℕ) :
    ∃ q : ℚ,
      (∑' n : ℕ, localValue hk r (fun m => (g m : ℝ)) F (a + n) /
        (B : ℝ) ^ (n + 1)) = (q : ℝ) := by
  refine ⟨localBoundaryRat hB hk r g F a, ?_⟩
  have h := infiniteSeries_normalForm_eq_rat hB hk r g hg F a
  simpa only [hF, localValue, Pi.zero_apply, eval₂_zero, zero_div, tsum_zero,
    sub_zero] using h

/-- In particular the rational exceptions for actual prime gaps are
unconditional, with no convergence or prime-distribution assumption. -/
theorem primeGap_series_rational_of_normalForm_zero
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F = 0) (a : ℕ) :
    ∃ q : ℚ,
      (∑' n : ℕ, localValue hk r (fun m => (primeGap m : ℝ)) F (a + n) /
        (B : ℝ) ^ (n + 1)) = (q : ℝ) := by
  have hg : HasPolynomialGrowth fun n => ((primeGap n : ℤ) : ℝ) := by
    simpa only [Int.cast_natCast] using primeGap_hasPolynomialGrowth
  simpa only [Int.cast_natCast] using
    infiniteSeries_rational_of_normalForm_zero hB hk r
      (fun n => (primeGap n : ℤ)) hg F hF a

end PrimeGapNormality.Prime.CoreCyclic
