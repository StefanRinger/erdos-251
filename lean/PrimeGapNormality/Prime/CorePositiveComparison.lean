import PrimeGapNormality.Prime.StoppedUnequalMass

/-! Finite positive comparison from the odd stopped transform.
The budget is the actual algebraic expression used by the frozen paper's
`D_(X,c)`, with arbitrary nonnegative finite masses. Arithmetic calibration
and convergence are separate suppliers, not assumptions disguised here.
-/

namespace PrimeGapNormality.Prime.Stopped

open Finset

variable {α : Type*} [DecidableEq α] [LinearOrder α]

noncomputable def positiveShapeExcess (Ω : Finset α)
    (μ ν : Finset α → ℝ) (L : ℕ) (c : ℝ) : ℝ :=
  ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
    max (shortShapeMass Ω μ L K - c * shortShapeMass Ω ν L K) 0

noncomputable def stoppedPositiveBudget (Ω : Finset α)
    (μ ν : Finset α → ℝ) (L r : ℕ) (c : ℝ) : ℝ :=
  (∑ U ∈ Ω.powerset, μ U) -
      (∑ K ∈ Ω.powerset.filter (fun K => K.card = L), janossyTrunc Ω μ L r K) +
    ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
      max (janossyTrunc Ω μ L r K - c * janossyTrunc Ω ν L r K) 0

private theorem positive_excess_le_residual {a b j q c : ℝ}
    (hja : j ≤ a) (hqb : q ≤ b) (hc : 0 ≤ c) :
    max (a - c * b) 0 ≤ a - j + max (j - c * q) 0 := by
  have hmult := mul_le_mul_of_nonneg_left hqb hc
  apply max_le
  · have := le_max_left (j - c * q) 0
    linarith
  · have := le_max_right (j - c * q) 0
    linarith

/-- Actual span failure and positive shape excess are controlled together.
No normalization of either mass is needed; only the odd stop and positivity.
-/
theorem failure_add_positiveShapeExcess_le_stoppedPositiveBudget
    {Ω : Finset α} {μ ν : Finset α → ℝ} {L r : ℕ} {c : ℝ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L)) (hc : 0 ≤ c)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U) :
    failureMass Ω μ L + positiveShapeExcess Ω μ ν L c ≤
      stoppedPositiveBudget Ω μ ν L r c := by
  have hpoint : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L),
      max (shortShapeMass Ω μ L K - c * shortShapeMass Ω ν L K) 0 ≤
        shortShapeMass Ω μ L K - janossyTrunc Ω μ L r K +
          max (janossyTrunc Ω μ L r K - c * janossyTrunc Ω ν L r K) 0 := by
    intro K hK
    have hcard := (mem_filter.mp hK).2
    exact positive_excess_le_residual
      (janossyTrunc_le_shortShapeMass hL hr hpar hcard hμ)
      (janossyTrunc_le_shortShapeMass hL hr hpar hcard hν) hc
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, sum_sub_distrib] at hsum
  have hmass := shortShapeMass_add_failureMass (Ω := Ω) (μ := μ) (L := L)
  unfold positiveShapeExcess stoppedPositiveBudget
  linarith

/-- Bounded positive tests need positive excess, not total variation. -/
theorem positive_shape_test_le
    {Ω : Finset α} {μ ν : Finset α → ℝ} {L : ℕ} {c : ℝ}
    {f : Finset α → ℝ}
    (hf0 : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), 0 ≤ f K)
    (hf1 : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), f K ≤ 1) :
    (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * shortShapeMass Ω μ L K) ≤
      c * (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * shortShapeMass Ω ν L K) + positiveShapeExcess Ω μ ν L c := by
  have hpoint : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L),
      f K * shortShapeMass Ω μ L K ≤
        c * (f K * shortShapeMass Ω ν L K) +
          max (shortShapeMass Ω μ L K - c * shortShapeMass Ω ν L K) 0 := by
    intro K hK
    have hupper := mul_le_mul_of_nonneg_left
      (le_max_left (shortShapeMass Ω μ L K - c * shortShapeMass Ω ν L K) 0)
      (hf0 K hK)
    have hcap := mul_le_mul_of_nonneg_right (hf1 K hK)
      (le_max_right (shortShapeMass Ω μ L K - c * shortShapeMass Ω ν L K) 0)
    nlinarith
  have hsum := sum_le_sum hpoint
  simpa only [sum_add_distrib, ← mul_sum, positiveShapeExcess] using hsum

theorem failure_add_positive_test_le_stopped_budget
    {Ω : Finset α} {μ ν : Finset α → ℝ} {L r : ℕ} {c : ℝ}
    {f : Finset α → ℝ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L)) (hc : 0 ≤ c)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U)
    (hf0 : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), 0 ≤ f K)
    (hf1 : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), f K ≤ 1) :
    failureMass Ω μ L +
      (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * shortShapeMass Ω μ L K) ≤
      c * (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * shortShapeMass Ω ν L K) + stoppedPositiveBudget Ω μ ν L r c := by
  have htest := positive_shape_test_le (μ := μ) (ν := ν) (c := c) hf0 hf1
  have hbudget := failure_add_positiveShapeExcess_le_stoppedPositiveBudget
    hL hr hpar hc hμ hν
  linarith

/-- A signed reference transform is not required to be a probability law.
This is needed for the Hardy--Littlewood main-term transform J_M. -/
noncomputable def stoppedPositiveBudgetAgainst (Ω : Finset α)
    (μ : Finset α → ℝ) (J : Finset α → ℝ) (L r : ℕ) (c : ℝ) : ℝ :=
  (∑ U ∈ Ω.powerset, μ U) -
      (∑ K ∈ Ω.powerset.filter (fun K => K.card = L), janossyTrunc Ω μ L r K) +
    ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
      max (janossyTrunc Ω μ L r K - c * J K) 0

/-- Calibration of the signed reference costs only its summed transform error.
There is no division by a pattern mass or conditioning on a rare cell. -/
theorem stoppedPositiveBudget_le_reference_add_error
    (Ω : Finset α) (μ ν J : Finset α → ℝ) (L r : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    stoppedPositiveBudget Ω μ ν L r c ≤
      stoppedPositiveBudgetAgainst Ω μ J L r c +
        c * ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          |J K - janossyTrunc Ω ν L r K| := by
  have hpoint : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L),
      max (janossyTrunc Ω μ L r K - c * janossyTrunc Ω ν L r K) 0 ≤
        max (janossyTrunc Ω μ L r K - c * J K) 0 +
          c * |J K - janossyTrunc Ω ν L r K| := by
    intro K _
    have hmul := mul_le_mul_of_nonneg_left
      (le_abs_self (J K - janossyTrunc Ω ν L r K)) hc
    have h0 := mul_nonneg hc (abs_nonneg (J K - janossyTrunc Ω ν L r K))
    apply max_le
    · have := le_max_left (janossyTrunc Ω μ L r K - c * J K) 0
      linarith
    · have := le_max_right (janossyTrunc Ω μ L r K - c * J K) 0
      linarith
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, ← mul_sum] at hsum
  unfold stoppedPositiveBudget stoppedPositiveBudgetAgainst
  linarith

theorem failure_add_positive_test_le_reference_budget
    {Ω : Finset α} {μ ν J : Finset α → ℝ} {L r : ℕ} {c : ℝ}
    {f : Finset α → ℝ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hpar : Odd (r - L)) (hc : 0 ≤ c)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U)
    (hf0 : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), 0 ≤ f K)
    (hf1 : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), f K ≤ 1) :
    failureMass Ω μ L +
      (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * shortShapeMass Ω μ L K) ≤
      c * (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * shortShapeMass Ω ν L K) +
      stoppedPositiveBudgetAgainst Ω μ J L r c +
        c * ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          |J K - janossyTrunc Ω ν L r K| := by
  have hbase := failure_add_positive_test_le_stopped_budget
    hL hr hpar hc hμ hν hf0 hf1
  have hcal := stoppedPositiveBudget_le_reference_add_error Ω μ ν J L r hc
  linarith

end PrimeGapNormality.Prime.Stopped
