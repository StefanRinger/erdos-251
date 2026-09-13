import PrimeGapNormality.Prime.CorePrimeLocalNormality
import PrimeGapNormality.Prime.CoreLocalNormalFormEnd

/-!
# Rational-or-normal classification for actual local prime-gap series

This packages the proved convergence and rational boundary with the actual
prime-local Weyl theorem.  The D budget uses only the top degree of the
canonical normal form.  The zero class is handled unconditionally; no model,
frame, reference, or tail premise is added here.
-/

namespace PrimeGapNormality.Prime

open CoreCyclic MvPolynomial

noncomputable section

private theorem localClock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    2 ≤ B ^ k := by
  have hsplit : k = k - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [hsplit, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

/-- Actual convergence is unconditional and does not consume D or
Kuperberg. -/
theorem corePrime_local_series_summable
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) :
    Summable fun n : ℕ ↦
      localValue hk phase (fun q ↦ (primeGap q : ℝ)) F n /
        (B : ℝ) ^ (n + 1) :=
  (primeLocalSeries_and_normalForm_summable hB hk phase F).1

/-- Under the actual D input, rationality is equivalent to vanishing of the
canonical normal form.  The reverse implication uses the explicit rational
boundary; the forward implication uses irrationality of every nonzero
class. -/
theorem corePrime_local_rational_iff_normalForm_zero_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {κ d0 c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    (∃ q : ℚ,
      coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F = (q : ℝ)) ↔
      normalForm hB hk F = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    by_contra hnonzero
    have hirr := corePrime_local_irrational_of_D
      hB hk phase F hnonzero hκ hd0 hc hD
    exact hirr ⟨q, hq.symm⟩
  · intro hzero
    exact coreCyclicFullSeries_rational_of_normalForm_zero
      hB hk phase F hzero

/-- Equivalent nonzero-class formulation at the literal period clock. -/
theorem corePrime_local_normalForm_ne_zero_iff_weyl_clock_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {κ d0 c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    normalForm hB hk F ≠ 0 ↔
      weylCriterion (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) := by
  constructor
  · intro hnonzero
    exact corePrime_local_weyl_clock_of_D
      hB hk phase F hnonzero hκ hd0 hc hD
  · intro hW hzero
    obtain ⟨q, hq⟩ := coreCyclicFullSeries_rational_of_normalForm_zero
      hB hk phase F hzero
    exact (weylCriterion_irrational hW) ⟨q, hq.symm⟩

/-- Literal digit normality at the period clock `B^k`. -/
theorem corePrime_local_isNormal_clock_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    {κ d0 c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) :=
  CoreWeylNormality.isNormal_of_weyl (localClock_ge hB hk)
    (corePrime_local_weyl_clock_of_D hB hk phase F hF hκ hd0 hc hD)

/-- Nonvanishing of the normal form is equivalent to the complete proved
normal branch: Weyl at the literal period clock and digit normality at both
`B^k` and `B`.  No converse `IsNormal → Weyl` is asserted separately. -/
theorem corePrime_local_normalForm_ne_zero_iff_normal_branch_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {κ d0 c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    normalForm hB hk F ≠ 0 ↔
      weylCriterion (B ^ k)
          (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) ∧
        PrimeGapNormality.BFree.IsNormal (B ^ k)
          (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) ∧
        PrimeGapNormality.BFree.IsNormal B
          (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) := by
  constructor
  · intro hnonzero
    exact ⟨corePrime_local_weyl_clock_of_D
        hB hk phase F hnonzero hκ hd0 hc hD,
      corePrime_local_isNormal_clock_of_D
        hB hk phase F hnonzero hκ hd0 hc hD,
      corePrime_local_isNormal_of_D
        hB hk phase F hnonzero hκ hd0 hc hD⟩
  · intro hbranch
    exact (corePrime_local_normalForm_ne_zero_iff_weyl_clock_of_D
      hB hk phase F hκ hd0 hc hD).2 hbranch.1

/-- Exact D-conditional rational-or-normal classification, including the
period clock and the descended base. -/
theorem corePrime_local_classification_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {κ d0 c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    (normalForm hB hk F = 0 ∧
      coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F =
        (primeLocalBoundaryRat hB hk phase F : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) ∧
      weylCriterion B
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) ∧
      Irrational
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F)) := by
  by_cases hzero : normalForm hB hk F = 0
  · exact Or.inl ⟨hzero,
      coreCyclicFullSeries_eq_boundary_of_normalForm_zero hB hk phase F hzero⟩
  · exact Or.inr ⟨hzero,
      corePrime_local_weyl_clock_of_D hB hk phase F hzero hκ hd0 hc hD,
      corePrime_local_isNormal_clock_of_D hB hk phase F hzero hκ hd0 hc hD,
      corePrime_local_weyl_of_D hB hk phase F hzero hκ hd0 hc hD,
      corePrime_local_isNormal_of_D hB hk phase F hzero hκ hd0 hc hD,
      corePrime_local_irrational_of_D hB hk phase F hzero hκ hd0 hc hD⟩

/-! ## Kuperberg specialization -/

theorem corePrime_local_rational_iff_normalForm_zero_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hK : KuperbergConj13) :
    (∃ q : ℚ,
      coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F = (q : ℝ)) ↔
      normalForm hB hk F = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    by_contra hnonzero
    have hW := corePrime_local_weyl_clock_of_kuperberg
      hB hk phase F hnonzero hK
    exact (weylCriterion_irrational hW) ⟨q, hq.symm⟩
  · intro hzero
    exact coreCyclicFullSeries_rational_of_normalForm_zero
      hB hk phase F hzero

theorem corePrime_local_normalForm_ne_zero_iff_weyl_clock_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hK : KuperbergConj13) :
    normalForm hB hk F ≠ 0 ↔
      weylCriterion (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) := by
  constructor
  · intro hnonzero
    exact corePrime_local_weyl_clock_of_kuperberg hB hk phase F hnonzero hK
  · intro hW hzero
    obtain ⟨q, hq⟩ := coreCyclicFullSeries_rational_of_normalForm_zero
      hB hk phase F hzero
    exact (weylCriterion_irrational hW) ⟨q, hq.symm⟩

theorem corePrime_local_weyl_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    (hK : KuperbergConj13) :
    weylCriterion B
      (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) :=
  weylCriterion_of_pow hB (by omega : 1 ≤ k)
    (corePrime_local_weyl_clock_of_kuperberg hB hk phase F hF hK)

theorem corePrime_local_isNormal_clock_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    (hK : KuperbergConj13) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) :=
  CoreWeylNormality.isNormal_of_weyl (localClock_ge hB hk)
    (corePrime_local_weyl_clock_of_kuperberg hB hk phase F hF hK)

theorem corePrime_local_irrational_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    (hK : KuperbergConj13) :
    Irrational
      (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) :=
  weylCriterion_irrational
    (corePrime_local_weyl_of_kuperberg hB hk phase F hF hK)

theorem corePrime_local_classification_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hK : KuperbergConj13) :
    (normalForm hB hk F = 0 ∧
      coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F =
        (primeLocalBoundaryRat hB hk phase F : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) ∧
      weylCriterion B
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) ∧
      Irrational
        (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F)) := by
  by_cases hzero : normalForm hB hk F = 0
  · exact Or.inl ⟨hzero,
      coreCyclicFullSeries_eq_boundary_of_normalForm_zero hB hk phase F hzero⟩
  · exact Or.inr ⟨hzero,
      corePrime_local_weyl_clock_of_kuperberg hB hk phase F hzero hK,
      corePrime_local_isNormal_clock_of_kuperberg hB hk phase F hzero hK,
      corePrime_local_weyl_of_kuperberg hB hk phase F hzero hK,
      corePrime_local_isNormal_of_kuperberg hB hk phase F hzero hK,
      corePrime_local_irrational_of_kuperberg hB hk phase F hzero hK⟩

end

end PrimeGapNormality.Prime
