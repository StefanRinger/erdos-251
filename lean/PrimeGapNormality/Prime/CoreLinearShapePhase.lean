import PrimeGapNormality.Prime.CorePrimeWindowMean
import PrimeGapNormality.Prime.StatisticalCriterion

/-! Actual finite linear phase on an ordered survivor subset. -/

open Finset

namespace PrimeGapNormality.Prime

noncomputable def coreLinearShapePhase (B L : ℕ) (U : Finset ℕ) : ℝ :=
  ∑ j ∈ range L, (subsetGap U j : ℝ) / (B : ℝ) ^ (j + 1)

theorem coreLinearShapePhase_prefix (B L n : ℕ) :
    coreLinearShapePhase B L (corePrimePrefix n L) =
      seqGapPolyTailTrunc nthPrime (fun _ => Polynomial.X) B L n := by
  simp only [seqGapPolyTailTrunc, Polynomial.eval_X]
  unfold coreLinearShapePhase
  apply sum_congr rfl
  intro j hj
  rw [corePrimePrefix_gap n L j (mem_range.mp hj)]
  rfl

end PrimeGapNormality.Prime
