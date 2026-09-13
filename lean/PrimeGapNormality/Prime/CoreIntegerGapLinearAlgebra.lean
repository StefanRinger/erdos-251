import PrimeGapNormality.Prime.CoreIntegerGapObservable
import PrimeGapNormality.Prime.CoreSubexponentialAlgebra

namespace PrimeGapNormality.Prime.CoreIntegerGapLinearAlgebra

open Finset CoreCyclic CoreIntegerGapObservable
open CoreSequenceSubexponentialGrowth
open scoped Classical BigOperators
noncomputable section

def integerCombination {I : Type*} [Fintype I] {k : ℕ}
    (c : I → ℤ) (F : I → Fin k → ℕ → ℤ) (s : Fin k) (q : ℕ) : ℤ :=
  ∑ i, c i * F i s q

/-- Exact finite-linearity of the convergent integer-observable series. -/
theorem observableFullSeries_integerCombination
    {I : Type*} [Fintype I] {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℕ) (hgpos : ∀ n, 1 ≤ g n)
    (hg : HasSubexponentialGrowth (fun n => (g n : ℝ)))
    (c : I → ℤ) (F : I → Fin k → ℕ → ℤ) (C : I → ℝ)
    (hC : ∀ i, 0 ≤ C i)
    (hF : ∀ i s q, 1 ≤ q → |(F i s q : ℝ)| ≤ C i * (q : ℝ)) :
    observableFullSeries B hk r (integerCombination c F) g =
      ∑ i, (c i : ℝ) * observableFullSeries B hk r (F i) g := by
  let term := fun i : I => fun n : ℕ => (c i : ℝ) *
    ((observableValue hk r (F i) g 0 n : ℝ) / (B : ℝ) ^ (n + 1))
  have hs : ∀ i, Summable (term i) := fun i =>
    (observableSeries_summable hB hk r (F i) hgpos hg (hC i) (hF i) 0).mul_left _
  unfold observableFullSeries observableSeries
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (s := (univ : Finset I)) (fun i hi => hs i)]
  apply tsum_congr
  intro n
  dsimp only [term]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  apply congrArg (fun z : ℝ => z / (B : ℝ) ^ (n + 1))
  simp only [observableValue, integerCombination, Nat.zero_add, Int.cast_sum,
    Int.cast_mul]

end
end PrimeGapNormality.Prime.CoreIntegerGapLinearAlgebra
