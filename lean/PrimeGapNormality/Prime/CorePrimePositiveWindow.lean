import PrimeGapNormality.Prime.CorePrimeGapOrbit
import PrimeGapNormality.Prime.CorePrimeComparisonInput

/-! Finite positive transfer with the original physical span failure charged
before restoring the infinite tail. The arithmetic error is exactly D;
only the separately proved model/main-term calibration is charged absolutely.
-/

open Finset MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace PrimeGapNormality.Prime

theorem coreActual_span_failure_eq_index (X S : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    Stopped.failureMass (Icc 1 S) (coreActualPatternMass X (Icc 1 S)) L =
      (∑ n ∈ Ico (Nat.primeCounting X) (Nat.primeCounting (2 * X)),
        if nthPrime (n + L) - nthPrime n ≤ S then (0 : ℝ) else 1) /
          (windowNX X : ℝ) := by
  classical
  have hleft : Stopped.failureMass (Icc 1 S) (coreActualPatternMass X (Icc 1 S)) L =
      ∑ U ∈ (Icc 1 S).powerset,
        coreActualPatternMass X (Icc 1 S) U * if U.card < L then 1 else 0 := by
    simp [Stopped.failureMass, sum_filter]
  rw [hleft, coreActualPatternMass_eval, corePrimeRoots_sum]
  congr 1
  apply sum_congr rfl
  intro n hn
  by_cases hs : nthPrime (n + L) - nthPrime n ≤ S
  · have hc := (coreActualPattern_card_ge_iff_span hL).mpr hs
    simp [hs, Nat.not_lt_of_ge hc]
  · have hc : (coreActualPattern (Icc 1 S) (nthPrime n)).card < L :=
      Nat.lt_of_not_ge (fun hc => hs ((coreActualPattern_card_ge_iff_span hL).mp hc))
    simp [hs, hc]

theorem corePrime_truncated_positive_window_le
    (B X S : ℕ) {L : ℕ} (hL : 1 ≤ L)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {C : ℝ} (hf : ∀ x, f x ≤ C) :
    windowAvgReal (seqWindow nthPrime X) (fun n =>
      f (seqGapPolyTailTrunc nthPrime (fun _ => Polynomial.X) B L n :
        AddCircle (1 : ℝ))) ≤
      C * Stopped.failureMass (Icc 1 S) (coreActualPatternMass X (Icc 1 S)) L +
      ∑ U ∈ (Icc 1 S).powerset.filter (fun U => U.card = L),
        f (coreLinearShapePhase B L U : AddCircle (1 : ℝ)) *
          Stopped.shortShapeMass (Icc 1 S) (coreActualPatternMass X (Icc 1 S)) L U := by
  classical
  rw [coreActual_span_failure_eq_index X S hL,
    coreActual_firstL_test_eq_index_average X S hL]
  simp_rw [coreLinearShapePhase_prefix]
  unfold windowAvgReal
  rw [seqWindow_nthPrime_card, corePrime_seqWindow_eq_Ico,
    ← mul_div_assoc, ← add_div, mul_sum, ← sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro n hn
  by_cases hs : nthPrime (n + L) - nthPrime n ≤ S
  · simp [hs]
  · simp only [hs, if_false, mul_one, add_zero]
    exact hf _

theorem corePrime_positive_test_bounded_le_comparisonQuantity
    {X L r : ℕ} {Ω : Finset ℕ} {ν : Finset ℕ → ℝ} {c C : ℝ}
    {f : Finset ℕ → ℝ}
    (hN : 0 < windowNX X) (hL : 1 ≤ L) (hr : L ≤ r)
    (hpar : Odd (r - L)) (hc : 0 ≤ c) (hC : 0 < C)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U)
    (hf0 : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), 0 ≤ f K)
    (hfC : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), f K ≤ C) :
    C * Stopped.failureMass Ω (coreActualPatternMass X Ω) L +
      (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * Stopped.shortShapeMass Ω (coreActualPatternMass X Ω) L K) ≤
      c * (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * Stopped.shortShapeMass Ω ν L K) +
      C * (corePrimeComparisonQuantity X Ω L r c +
        c * ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
          |coreJanossyTransform Ω (rootedMainTerm X) L r K / (windowNX X : ℝ) -
            Stopped.janossyTrunc Ω ν L r K|) := by
  have h := corePrime_positive_test_le_comparisonQuantity (f := fun K => f K / C)
    hN hL hr hpar hc hν
    (fun K hK => div_nonneg (hf0 K hK) hC.le)
    (fun K hK => (div_le_one hC).mpr (hfC K hK))
  have hm := mul_le_mul_of_nonneg_left h hC.le
  have heq (μ : Finset ℕ → ℝ) :
      C * (∑ K ∈ Ω.powerset.filter (fun K => K.card = L), f K / C * μ K) =
        ∑ K ∈ Ω.powerset.filter (fun K => K.card = L), f K * μ K := by
    rw [mul_sum]
    apply sum_congr rfl
    intro K hK
    field_simp [hC.ne']
  simp only [mul_add] at hm
  rw [heq] at hm
  have heq2 : C * (c * (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
      f K / C * Stopped.shortShapeMass Ω ν L K)) =
      c * (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * Stopped.shortShapeMass Ω ν L K) := by
    rw [mul_left_comm, heq]
  rw [heq2] at hm
  simpa only [mul_add, add_assoc] using hm

theorem corePrime_full_positive_window_le_comparisonQuantity
    {B X S L r : ℕ} {ν : Finset ℕ → ℝ} {c C : ℝ}
    (hN : 0 < windowNX X) (hL : 1 ≤ L) (hr : L ≤ r)
    (hpar : Odd (r - L)) (hc : 0 ≤ c) (hC : 0 < C)
    (hν : ∀ U ∈ (Icc 1 S).powerset, 0 ≤ ν U)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C) :
    windowAvgReal (seqWindow nthPrime X) (fun n => f (corePrimeGapCircleOrbit B n)) ≤
      c * (∑ U ∈ (Icc 1 S).powerset.filter (fun U => U.card = L),
        f (coreLinearShapePhase B L U : AddCircle (1 : ℝ)) *
          Stopped.shortShapeMass (Icc 1 S) ν L U) +
      C * (corePrimeComparisonQuantity X (Icc 1 S) L r c +
        c * ∑ U ∈ (Icc 1 S).powerset.filter (fun U => U.card = L),
          |coreJanossyTransform (Icc 1 S) (rootedMainTerm X) L r U / (windowNX X : ℝ) -
            Stopped.janossyTrunc (Icc 1 S) ν L r U|) +
      windowAvgReal (seqWindow nthPrime X) (fun n =>
        |f (corePrimeGapCircleOrbit B n) -
          f (seqGapPolyTailTrunc nthPrime (fun _ => Polynomial.X) B L n :
            AddCircle (1 : ℝ))|) := by
  have hfinite := (corePrime_truncated_positive_window_le B X S hL f hfC).trans
    (corePrime_positive_test_bounded_le_comparisonQuantity hN hL hr hpar hc hC hν
      (fun U _ => hf0 _) (fun U _ => hfC _))
  have htriangle :
      windowAvgReal (seqWindow nthPrime X) (fun n => f (corePrimeGapCircleOrbit B n)) ≤
        windowAvgReal (seqWindow nthPrime X) (fun n =>
          f (seqGapPolyTailTrunc nthPrime (fun _ => Polynomial.X) B L n :
            AddCircle (1 : ℝ))) +
        windowAvgReal (seqWindow nthPrime X) (fun n =>
          |f (corePrimeGapCircleOrbit B n) -
            f (seqGapPolyTailTrunc nthPrime (fun _ => Polynomial.X) B L n :
              AddCircle (1 : ℝ))|) := by
    unfold windowAvgReal
    rw [← add_div, ← sum_add_distrib]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro n hn
    linarith [le_abs_self (f (corePrimeGapCircleOrbit B n) -
      f (seqGapPolyTailTrunc nthPrime (fun _ => Polynomial.X) B L n :
        AddCircle (1 : ℝ)))]
  exact htriangle.trans (add_le_add hfinite le_rfl)

end PrimeGapNormality.Prime
