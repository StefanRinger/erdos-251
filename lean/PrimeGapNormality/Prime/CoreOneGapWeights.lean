import PrimeGapNormality.Prime.CoreCyclicTopDegree
import PrimeGapNormality.Prime.CoreCyclicOrbitIdentification

/-! Concrete periodic linear gap tuples. These are algebraic adapters, not
an additional distribution hypothesis. -/

namespace PrimeGapNormality.Prime.CoreOneGapWeights
open CoreCyclic MvPolynomial
noncomputable section

def tuple {k : ℕ} (d : Fin k → ℚ) : PeriodicLocal k :=
  fun s ↦ C (d s) * X 0

theorem rooted {k : ℕ} (hk : 0 < k) (d : Fin k → ℚ) :
    drop hk (tuple d) = 0 := by
  ext s
  simp [drop_apply, tuple]

theorem ne_zero {k : ℕ} (d : Fin k → ℚ) (hd : d ≠ 0) :
    tuple d ≠ 0 := by
  intro h
  apply hd
  funext s
  have hs := congrArg (eval (fun _ : ℕ ↦ (1 : ℚ))) (congrFun h s)
  simpa [tuple] using hs

theorem degree_le_one {k : ℕ} (d : Fin k → ℚ) :
    topDegree (tuple d) ≤ 1 := by
  apply Finset.sup_le
  intro s hs
  exact (totalDegree_mul _ _).trans (by simp [tuple])

theorem degree_eq_one {k : ℕ} (hk : 0 < k) (d : Fin k → ℚ)
    (hd : d ≠ 0) : topDegree (tuple d) = 1 :=
  le_antisymm (degree_le_one d)
    (one_le_topDegree_of_rooted hk _ (rooted hk d) (ne_zero d hd))

theorem normalForm_tuple {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (d : Fin k → ℚ) : normalForm hB hk (tuple d) = tuple d :=
  normalForm_of_rooted hB hk _ (rooted hk d)

theorem localValue_tuple {k : ℕ} (hk : 0 < k) (r : Fin k)
    (d : Fin k → ℚ) (g : ℕ → ℝ) (n : ℕ) :
    localValue hk r g (tuple d) n = (d (phaseAt hk r n) : ℝ) * g n := by
  simp [localValue, tuple]

theorem series_tuple (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (d : Fin k → ℚ) (g : ℕ → ℝ) :
    coreCyclicFullSeries B hk r g (tuple d) =
      ∑' n : ℕ, (d (phaseAt hk r n) : ℝ) * g n / (B : ℝ) ^ (n + 1) := by
  simp [coreCyclicFullSeries, localValue_tuple]

end
end PrimeGapNormality.Prime.CoreOneGapWeights
