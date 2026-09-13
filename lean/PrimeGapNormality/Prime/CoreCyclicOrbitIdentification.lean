import PrimeGapNormality.Prime.CoreLocalSeriesRecurrence

/-!
# Identifying the periodic local series with an actual circle orbit

This is an algebraic restriction to the progression `n₀ + k t`, not an
equidistribution assertion about residue classes.  The literal `k`-step
recurrence supplies every iterate of multiplication by `B^k`.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open MvPolynomial

noncomputable section

/-- A `k`-step circle recurrence gives the exact orbit on every progression
`n₀ + k t`. -/
theorem circleOrbit_of_add_period
    {u : ℕ → AddCircle (1 : ℝ)} {k C : ℕ}
    (hrec : ∀ n, u (n + k) = C • u n) (n₀ t : ℕ) :
    u (n₀ + k * t) = C ^ t • u n₀ := by
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        u (n₀ + k * (t + 1)) = u ((n₀ + k * t) + k) := by
          simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        _ = C • u (n₀ + k * t) := hrec _
        _ = C • (C ^ t • u n₀) := by rw [ih]
        _ = (C * C ^ t) • u n₀ := (mul_smul C (C ^ t) (u n₀)).symm
        _ = (C ^ t * C) • u n₀ := by rw [Nat.mul_comm C]
        _ = C ^ (t + 1) • u n₀ := by rw [pow_succ]

/-- The original full local series, with absolute index and cyclic label both
starting at zero. -/
def coreCyclicFullSeries (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F : PeriodicLocal k) : ℝ :=
  ∑' i : ℕ, localValue hk r g F i / (B : ℝ) ^ (i + 1)

/-- Restarting the relative-label series at absolute index zero is exactly
the original full series `α_F`. -/
theorem coreLocalSeries_zero_eq_fullSeries
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F : PeriodicLocal k) :
    coreLocalSeries B hk r g F 0 = coreCyclicFullSeries B hk r g F := by
  unfold coreLocalSeries coreCyclicFullSeries
  apply tsum_congr
  intro i
  congr 1
  unfold relativeLocalValue localValue
  congr 1
  funext j
  congr 1
  omega

/-- Concrete integer-coefficient progression orbit, based at any absolute
index.  All hypotheses are arithmetic/growth data used to prove the literal
series recurrence; the orbit relation is a conclusion. -/
theorem coreLocalSeriesCircle_progression_of_intTuple
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℤ) (hg : HasPolynomialGrowth fun n ↦ (g n : ℝ))
    (F : Fin k → MvPolynomial ℕ ℤ) (n₀ t : ℕ) :
    coreLocalSeriesCircle B hk r (fun n ↦ (g n : ℝ)) (mapIntTuple F)
        (n₀ + k * t) =
      (B ^ k) ^ t •
        coreLocalSeriesCircle B hk r (fun n ↦ (g n : ℝ)) (mapIntTuple F) n₀ := by
  apply circleOrbit_of_add_period
  intro n
  exact coreLocalSeriesCircle_add_period_of_intTuple hB hk r g hg F n

/-- At the zero base point, the preceding progression is the actual
`(B^k)^t` orbit of the original full local series. -/
theorem coreLocalSeriesCircle_progression_zero_eq_fullSeries_of_intTuple
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℤ) (hg : HasPolynomialGrowth fun n ↦ (g n : ℝ))
    (F : Fin k → MvPolynomial ℕ ℤ) (t : ℕ) :
    coreLocalSeriesCircle B hk r (fun n ↦ (g n : ℝ)) (mapIntTuple F) (k * t) =
      (B ^ k) ^ t •
        (coreCyclicFullSeries B hk r (fun n ↦ (g n : ℝ)) (mapIntTuple F) :
          AddCircle (1 : ℝ)) := by
  rw [← coreLocalSeries_zero_eq_fullSeries]
  simpa only [Nat.zero_add, coreLocalSeriesCircle] using
    coreLocalSeriesCircle_progression_of_intTuple hB hk r g hg F 0 t

end

end PrimeGapNormality.Prime.CoreCyclic
