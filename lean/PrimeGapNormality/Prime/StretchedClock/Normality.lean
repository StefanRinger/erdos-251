import PrimeGapNormality.Prime.StretchedClock.PositiveComparison
import PrimeGapNormality.Prime.StretchedClock.FullPrefixNormality

/-!
# Unconditional normality of the literal stretched prime series

The arithmetic bound is constructed by `exists_positive_prefix_bound`;
it is not an argument of the public theorem. The series and the insertion
clock are those defined in `Definitions`, using the actual `nthPrime`.
Compilation and the separate audit, not this header, certify completion.
-/

namespace PrimeGapNormality.Prime.StretchedClock

/-- The actual prime coefficients at the logarithmically stretched clock
give ordinary base-B normality, at every digit position. -/
theorem value_isNormal {B : ℕ} (hB : 2 ≤ B) :
    PrimeGapNormality.BFree.IsNormal B (value B) := by
  obtain ⟨A, hA, hbound⟩ := exists_positive_prefix_bound hB
  exact value_isNormal_of_clockPrefix_lipschitz_bounds hB hA hbound

end PrimeGapNormality.Prime.StretchedClock
