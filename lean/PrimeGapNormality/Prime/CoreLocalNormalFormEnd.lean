import PrimeGapNormality.Prime.CoreCyclicRationalBoundary
import PrimeGapNormality.Prime.CoreCyclicOrbitIdentification
import PrimeGapNormality.Prime.CoreWeylNormality
import PrimeGapNormality.Prime.CoreRationalAffine

/-!
# End-value packaging for the cyclic normal form

The actual prime-gap local series differs from the series of its canonical
normal form by the explicitly constructed rational boundary.  Consequently
the zero canonical class is rational unconditionally, while Weyl's criterion
is invariant under passage between a tuple and its normal form.  The final
classification theorem below deliberately leaves the nonzero-normal-form
Weyl statement as an intermediate model interface.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open MvPolynomial

noncomputable section

/-- The explicit rational boundary at the zero starting index. -/
def primeLocalBoundaryRat
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) : ℚ :=
  localBoundaryRat hB hk phase (fun n ↦ (primeGap n : ℤ)) F 0

/-- Both the original and canonical prime-gap local series converge, with no
arithmetic-distribution premise. -/
theorem primeLocalSeries_and_normalForm_summable
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) :
    (Summable fun n : ℕ ↦
      localValue hk phase (fun q ↦ (primeGap q : ℝ)) F n /
        (B : ℝ) ^ (n + 1)) ∧
    (Summable fun n : ℕ ↦
      localValue hk phase (fun q ↦ (primeGap q : ℝ))
          (normalForm hB hk F) n /
        (B : ℝ) ^ (n + 1)) := by
  constructor
  · simpa only [Nat.zero_add] using
      primeGap_localSeries_summable hB hk phase F 0
  · simpa only [Nat.zero_add] using
      primeGap_localSeries_summable hB hk phase (normalForm hB hk F) 0

/-- Exact infinite end-value decomposition by the actual rational boundary. -/
theorem coreCyclicFullSeries_eq_normalForm_add_boundary
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) :
    coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F =
      coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
          (normalForm hB hk F) +
        (primeLocalBoundaryRat hB hk phase F : ℝ) := by
  have h := primeGap_infiniteSeries_normalForm hB hk phase F 0
  have hdiff :
      coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F -
        coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
          (normalForm hB hk F) =
        (primeLocalBoundaryRat hB hk phase F : ℝ) := by
    simpa only [coreCyclicFullSeries, primeLocalBoundaryRat, Nat.zero_add] using h
  linarith

/-- A vanishing normal form gives the explicit rational value, not merely
an abstract rationality predicate. -/
theorem coreCyclicFullSeries_eq_boundary_of_normalForm_zero
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hzero : normalForm hB hk F = 0) :
    coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F =
      (primeLocalBoundaryRat hB hk phase F : ℝ) := by
  rw [coreCyclicFullSeries_eq_normalForm_add_boundary hB hk phase F, hzero]
  simp [coreCyclicFullSeries, localValue]

theorem coreCyclicFullSeries_rational_of_normalForm_zero
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hzero : normalForm hB hk F = 0) :
    ∃ q : ℚ,
      coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F = (q : ℝ) :=
  ⟨primeLocalBoundaryRat hB hk phase F,
    coreCyclicFullSeries_eq_boundary_of_normalForm_zero hB hk phase F hzero⟩

/-- Weyl's criterion is unchanged by canonical reduction because the exact
difference is rational. -/
theorem weylCriterion_coreCyclicFullSeries_iff_normalForm
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) :
    weylCriterion B
        (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) ↔
      weylCriterion B
        (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
          (normalForm hB hk F)) := by
  let q : ℚ := primeLocalBoundaryRat hB hk phase F
  have heq := coreCyclicFullSeries_eq_normalForm_add_boundary hB hk phase F
  constructor
  · intro hF
    have hshift := CoreRationalAffine.weylCriterion_add_rat hB (-q) hF
    have hcancel :
        coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F +
            ((-q : ℚ) : ℝ) =
          coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ))
            (normalForm hB hk F) := by
      rw [heq]
      push_cast
      ring
    rwa [hcancel] at hshift
  · intro hNF
    have hshift := CoreRationalAffine.weylCriterion_add_rat hB q hNF
    change weylCriterion B
      (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ))
        (normalForm hB hk F) + (q : ℝ)) at hshift
    rw [← heq] at hshift
    exact hshift

/-- One-way digit-normality consequence when the model supplies Weyl for
the nonzero canonical series. -/
theorem coreCyclicFullSeries_isNormal_of_normalForm_weyl
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k)
    (hW : weylCriterion B
      (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
        (normalForm hB hk F))) :
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) :=
  CoreWeylNormality.isNormal_of_weyl hB
    ((weylCriterion_coreCyclicFullSeries_iff_normalForm hB hk phase F).2 hW)

/-- Generic rational-or-normal classification.  The hypothesis is exactly
the still-intermediate assertion that every nonzero rooted canonical tuple
has a Weyl prime-gap series. -/
theorem coreCyclicFullSeries_classification
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hW : ∀ N : PeriodicLocal k, drop hk N = 0 → N ≠ 0 →
      weylCriterion B
        (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) N))
    (F : PeriodicLocal k) :
    (normalForm hB hk F = 0 ∧
      coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F =
        (primeLocalBoundaryRat hB hk phase F : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion B
        (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) ∧
      Irrational
        (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F)) := by
  by_cases hzero : normalForm hB hk F = 0
  · exact Or.inl ⟨hzero,
      coreCyclicFullSeries_eq_boundary_of_normalForm_zero hB hk phase F hzero⟩
  · have hNF : weylCriterion B
        (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
          (normalForm hB hk F)) :=
      hW (normalForm hB hk F) (drop_normalForm hB hk F) hzero
    have hF : weylCriterion B
        (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) :=
      (weylCriterion_coreCyclicFullSeries_iff_normalForm hB hk phase F).2 hNF
    exact Or.inr ⟨hzero, hF,
      CoreWeylNormality.isNormal_of_weyl hB hF,
      weylCriterion_irrational hF⟩

end

end PrimeGapNormality.Prime.CoreCyclic
