import PrimeGapNormality.Prime.CorePrimeComparisonInput

/-! A finite upper bound for the frozen D quantity at c=1. It separates
actual/main-term error from model calibration, with no extra tuple depth.
The sharper one-sided transfer remains available separately. -/

open Finset

namespace PrimeGapNormality.Prime.Stopped

private theorem core_signed_reference_point (a j q : ℝ) :
    -a + max (a - j) 0 ≤ -q + |a - j| + |j - q| := by
  have ha := neg_abs_le (a - j)
  have hj := neg_abs_le (j - q)
  have hna := abs_nonneg (a - j)
  have hm : max (a - j) 0 ≤ a - q + |a - j| + |j - q| := by
    apply max_le <;> linarith
  linarith

theorem stoppedPositiveBudgetAgainst_le_absolute_errors
    {Ω : Finset ℕ} {μ ν J : Finset ℕ → ℝ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L)) :
    stoppedPositiveBudgetAgainst Ω μ J L r 1 ≤
      |(∑ U ∈ Ω.powerset, μ U) - ∑ U ∈ Ω.powerset, ν U| +
        failureMass Ω ν L + modelRemainder Ω ν L r +
        (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          |janossyTrunc Ω μ L r K - J K|) +
        (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          |J K - janossyTrunc Ω ν L r K|) := by
  classical
  have hpoint : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L),
      -janossyTrunc Ω μ L r K + max (janossyTrunc Ω μ L r K - J K) 0 ≤
        -janossyTrunc Ω ν L r K + |janossyTrunc Ω μ L r K - J K| +
          |J K - janossyTrunc Ω ν L r K| := by
    intro K _
    exact core_signed_reference_point _ _ _
  have hs := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_neg_distrib] at hs
  have hres := modelRemainder_eq_shapeResidual (Ω := Ω) (ν := ν) hL hr hpar
  rw [sum_sub_distrib] at hres
  have hm := shortShapeMass_add_failureMass (Ω := Ω) (μ := ν) (L := L)
  have hd := le_abs_self ((∑ U ∈ Ω.powerset, μ U) - ∑ U ∈ Ω.powerset, ν U)
  unfold stoppedPositiveBudgetAgainst
  simp only [one_mul]
  linarith

end PrimeGapNormality.Prime.Stopped

namespace PrimeGapNormality.Prime

theorem corePrimeComparisonQuantity_le_absolute_errors
    {X L r : ℕ} {Ω : Finset ℕ} {ν : Finset ℕ → ℝ}
    (hN : 0 < windowNX X) (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L)) :
    corePrimeComparisonQuantity X Ω L r 1 ≤
      |1 - ∑ U ∈ Ω.powerset, ν U| +
        Stopped.failureMass Ω ν L + Stopped.modelRemainder Ω ν L r +
        (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          |coreJanossyTransform Ω (fun H => (rootedTupleCount X H : ℝ)) L r K /
              (windowNX X : ℝ) -
            coreJanossyTransform Ω (rootedMainTerm X) L r K / (windowNX X : ℝ)|) +
        (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          |coreJanossyTransform Ω (rootedMainTerm X) L r K / (windowNX X : ℝ) -
            Stopped.janossyTrunc Ω ν L r K|) := by
  have h := Stopped.stoppedPositiveBudgetAgainst_le_absolute_errors
    (Ω := Ω) (μ := coreActualPatternMass X Ω) (ν := ν)
    (J := fun K => coreJanossyTransform Ω (rootedMainTerm X) L r K / (windowNX X : ℝ))
    hL hr hpar
  rw [corePrimeComparisonQuantity_eq_budget hN Ω L r 1,
    coreActualPatternMass_total Ω hN] at h
  have heq :
      (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        |Stopped.janossyTrunc Ω (coreActualPatternMass X Ω) L r K -
          coreJanossyTransform Ω (rootedMainTerm X) L r K / (windowNX X : ℝ)|) =
      (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        |coreJanossyTransform Ω (fun H => (rootedTupleCount X H : ℝ)) L r K /
            (windowNX X : ℝ) -
          coreJanossyTransform Ω (rootedMainTerm X) L r K / (windowNX X : ℝ)|) := by
    apply sum_congr rfl
    intro K hK
    rw [coreActualPatternMass_janossy X Ω L r (mem_powerset.mp (mem_filter.mp hK).1)]
  rwa [heq] at h

end PrimeGapNormality.Prime
