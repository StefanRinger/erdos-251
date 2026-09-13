import PrimeGapNormality.Prime.CorePrimePositiveWindow
import PrimeGapNormality.Prime.CoreCyclicOrderedInsertion
import PrimeGapNormality.Prime.CoreLocalPolynomialTailLimit

/-!
# Positive prime-window transfer for periodic local polynomials

This is the finite arithmetic bridge for a fixed relative cyclic label.  A
width-`w` tuple is evaluated for its first `L-w` emissions from the actual
first-`L` prime shape, so every variable still lies inside that same shape.
The stopped comparison is then applied verbatim.  Passing from the finite
phase to the actual infinite local series leaves the phase-test remainder as
an explicit physical-window term.
-/

namespace PrimeGapNormality.Prime

open Finset MeasureTheory MvPolynomial
open scoped Topology BoundedContinuousFunction

noncomputable section

/-- The first `L-w` local emissions read from the actual first-`L` prime
shape are exactly the corresponding truncation of the relative-label local
series.  In particular, no `L+w` physical shape is introduced. -/
theorem coreCyclicFinitePhase_primePrefix_eq
    (B : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {w L : ℕ} (hwL : w ≤ L)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w) (n : ℕ) :
    CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
        (CoreCyclic.orderedRealGap (corePrimePrefix n L)) =
      CoreCyclic.coreLocalSeriesTrunc B hk phase
        (fun q ↦ (primeGap q : ℝ)) F n (L - w) := by
  unfold CoreCyclic.coreCyclicFinitePhase CoreCyclic.coreLocalSeriesTrunc
  apply sum_congr rfl
  intro e he
  apply congrArg (fun z : ℝ ↦ z / (B : ℝ) ^ (e + 1))
  unfold CoreCyclic.relativeLocalValue
  apply eval₂_congr
  intro i m hi hm
  have hivars : i ∈ (F (CoreCyclic.phaseAt hk phase e)).vars :=
    (mem_vars_iff_mem_support i).2 ⟨m, mem_support_iff.mpr hm, hi⟩
  have hiw := hw (CoreCyclic.phaseAt hk phase e) i hivars
  have heiL : e + i < L := by
    have heK : e < L - w := mem_range.mp he
    omega
  unfold CoreCyclic.orderedRealGap
  rw [corePrimePrefix_gap n L (e + i) heiL]
  congr 2
  omega

/-- Direct stopped-pattern form of the preceding identity: whenever the
physical pattern contains at least `L` survivors, its first-`L` shape emits
the actual first `L-w` local terms. -/
theorem coreCyclicFinitePhase_actual_firstL_eq
    (B S : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {w L : ℕ}
    (hwL : w ≤ L) (hL : 1 ≤ L)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w) (n : ℕ)
    (hcard : L ≤ (coreActualPattern (Icc 1 S) (nthPrime n)).card) :
    CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
        (CoreCyclic.orderedRealGap
          (Stopped.firstL L (coreActualPattern (Icc 1 S) (nthPrime n)))) =
      CoreCyclic.coreLocalSeriesTrunc B hk phase
        (fun q ↦ (primeGap q : ℝ)) F n (L - w) := by
  have hspan := (coreActualPattern_card_ge_iff_span hL).mp hcard
  rw [coreActualPattern_firstL_eq_prefix hL hspan]
  exact coreCyclicFinitePhase_primePrefix_eq B hk phase F hwL hw n

/-- Finite positive transfer from the actual prime window to stopped
first-`L` shapes, with the local tuple evaluated for `L-w` emissions. -/
theorem corePrime_localTruncated_positive_window_le
    (B X S : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {w L : ℕ}
    (hwL : w ≤ L) (hL : 1 ≤ L)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {C : ℝ} (hf : ∀ x, f x ≤ C) :
    windowAvgReal (seqWindow nthPrime X) (fun n ↦
      f (CoreCyclic.coreLocalSeriesTrunc B hk phase
        (fun q ↦ (primeGap q : ℝ)) F n (L - w) : AddCircle (1 : ℝ))) ≤
      C * Stopped.failureMass (Icc 1 S)
        (coreActualPatternMass X (Icc 1 S)) L +
      ∑ U ∈ (Icc 1 S).powerset.filter (fun U ↦ U.card = L),
        f (CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
          (CoreCyclic.orderedRealGap U) : AddCircle (1 : ℝ)) *
          Stopped.shortShapeMass (Icc 1 S)
            (coreActualPatternMass X (Icc 1 S)) L U := by
  classical
  rw [coreActual_span_failure_eq_index X S hL,
    coreActual_firstL_test_eq_index_average X S hL]
  simp_rw [coreCyclicFinitePhase_primePrefix_eq B hk phase F hwL hw]
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

/-- The stopped positive comparison with the local finite shape inserted as
the test.  The arithmetic term is the unchanged actual
`corePrimeComparisonQuantity`, and calibration remains multiplied by `c`. -/
theorem corePrime_localTruncated_positive_window_le_comparisonQuantity
    {B X S L w R k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hwL : w ≤ L)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    {ν : Finset ℕ → ℝ} {c C : ℝ}
    (hN : 0 < windowNX X) (hL : 1 ≤ L) (hLR : L ≤ R)
    (hpar : Odd (R - L)) (hc : 0 ≤ c) (hC : 0 < C)
    (hν : ∀ U ∈ (Icc 1 S).powerset, 0 ≤ ν U)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfC : ∀ x, f x ≤ C) :
    windowAvgReal (seqWindow nthPrime X) (fun n ↦
      f (CoreCyclic.coreLocalSeriesTrunc B hk phase
        (fun q ↦ (primeGap q : ℝ)) F n (L - w) : AddCircle (1 : ℝ))) ≤
      c * (∑ U ∈ (Icc 1 S).powerset.filter (fun U ↦ U.card = L),
        f (CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
          (CoreCyclic.orderedRealGap U) : AddCircle (1 : ℝ)) *
          Stopped.shortShapeMass (Icc 1 S) ν L U) +
      C * (corePrimeComparisonQuantity X (Icc 1 S) L R c +
        c * ∑ U ∈ (Icc 1 S).powerset.filter (fun U ↦ U.card = L),
          |coreJanossyTransform (Icc 1 S) (rootedMainTerm X) L R U /
              (windowNX X : ℝ) -
            Stopped.janossyTrunc (Icc 1 S) ν L R U|) := by
  have hfinite := corePrime_localTruncated_positive_window_le
    B X S hk phase F hwL hL hw f hfC
  exact hfinite.trans
    (corePrime_positive_test_bounded_le_comparisonQuantity
      hN hL hLR hpar hc hC hν
      (f := fun U ↦ f (CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
        (CoreCyclic.orderedRealGap U) : AddCircle (1 : ℝ)))
      (fun U _ ↦ hf0 _) (fun U _ ↦ hfC _))

/-- Restoring the actual infinite relative-label local series.  The final
summand is deliberately the literal absolute phase-test remainder on the
same physical prime window; a separate tail theorem can bound it later. -/
theorem corePrime_localFull_positive_window_le_comparisonQuantity
    {B X S L w R k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hwL : w ≤ L)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    {ν : Finset ℕ → ℝ} {c C : ℝ}
    (hN : 0 < windowNX X) (hL : 1 ≤ L) (hLR : L ≤ R)
    (hpar : Odd (R - L)) (hc : 0 ≤ c) (hC : 0 < C)
    (hν : ∀ U ∈ (Icc 1 S).powerset, 0 ≤ ν U)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfC : ∀ x, f x ≤ C) :
    windowAvgReal (seqWindow nthPrime X) (fun n ↦
      f (CoreCyclic.coreLocalSeries B hk phase
        (fun q ↦ (primeGap q : ℝ)) F n : AddCircle (1 : ℝ))) ≤
      c * (∑ U ∈ (Icc 1 S).powerset.filter (fun U ↦ U.card = L),
        f (CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
          (CoreCyclic.orderedRealGap U) : AddCircle (1 : ℝ)) *
          Stopped.shortShapeMass (Icc 1 S) ν L U) +
      C * (corePrimeComparisonQuantity X (Icc 1 S) L R c +
        c * ∑ U ∈ (Icc 1 S).powerset.filter (fun U ↦ U.card = L),
          |coreJanossyTransform (Icc 1 S) (rootedMainTerm X) L R U /
              (windowNX X : ℝ) -
            Stopped.janossyTrunc (Icc 1 S) ν L R U|) +
      windowAvgReal (seqWindow nthPrime X) (fun n ↦
        |f (CoreCyclic.coreLocalSeries B hk phase
            (fun q ↦ (primeGap q : ℝ)) F n : AddCircle (1 : ℝ)) -
          f (CoreCyclic.coreLocalSeriesTrunc B hk phase
            (fun q ↦ (primeGap q : ℝ)) F n (L - w) : AddCircle (1 : ℝ))|) := by
  have hfinite := corePrime_localTruncated_positive_window_le_comparisonQuantity (B := B)
    hk phase F hwL hw hN hL hLR hpar hc hC hν f hf0 hfC
  have htriangle :
      windowAvgReal (seqWindow nthPrime X) (fun n ↦
        f (CoreCyclic.coreLocalSeries B hk phase
          (fun q ↦ (primeGap q : ℝ)) F n : AddCircle (1 : ℝ))) ≤
        windowAvgReal (seqWindow nthPrime X) (fun n ↦
          f (CoreCyclic.coreLocalSeriesTrunc B hk phase
            (fun q ↦ (primeGap q : ℝ)) F n (L - w) : AddCircle (1 : ℝ))) +
        windowAvgReal (seqWindow nthPrime X) (fun n ↦
          |f (CoreCyclic.coreLocalSeries B hk phase
              (fun q ↦ (primeGap q : ℝ)) F n : AddCircle (1 : ℝ)) -
            f (CoreCyclic.coreLocalSeriesTrunc B hk phase
              (fun q ↦ (primeGap q : ℝ)) F n (L - w) :
                AddCircle (1 : ℝ))|) := by
    unfold windowAvgReal
    rw [← add_div, ← sum_add_distrib]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro n hn
    linarith [le_abs_self
      (f (CoreCyclic.coreLocalSeries B hk phase
          (fun q ↦ (primeGap q : ℝ)) F n : AddCircle (1 : ℝ)) -
        f (CoreCyclic.coreLocalSeriesTrunc B hk phase
          (fun q ↦ (primeGap q : ℝ)) F n (L - w) : AddCircle (1 : ℝ)))]
  exact htriangle.trans (add_le_add hfinite le_rfl)

end

end PrimeGapNormality.Prime
