import PrimeGapNormality.Prime.CoreSequencePatternLaw
import PrimeGapNormality.Prime.CoreCyclicOrderedInsertion
import PrimeGapNormality.Prime.CoreLocalPolynomialTailLimit
import PrimeGapNormality.Prime.CorePositiveComparison

/-! Exact local-polynomial transfer for an arbitrary increasing integer
sequence. The arithmetic budget is an explicit intermediate input; this
module does not assume it vanishes or claim the unconditional rough theorem.
Only the original first L offsets are used for the L-w emissions. -/

namespace PrimeGapNormality.Prime.CoreSequenceLocalPositiveWindow

open Finset MvPolynomial CoreSequencePattern CoreSequencePatternLaw
open scoped Topology BoundedContinuousFunction
noncomputable section

def realGap (a : ℕ → ℕ) (n : ℕ) : ℝ := (a (n + 1) - a n : ℕ)

theorem finitePhase_prefix_eq {a : ℕ → ℕ} (ha : StrictMono a)
    (B : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {w L : ℕ} (hwL : w ≤ L)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w) (n : ℕ) :
    CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
        (CoreCyclic.orderedRealGap (prefixSet a n L)) =
      CoreCyclic.coreLocalSeriesTrunc B hk phase (realGap a) F n (L - w) := by
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
  rw [prefixSet_gap ha n L (e + i) heiL]
  simp only [realGap, Nat.add_assoc]

/-- Charge the physical span failure before using the finite pattern law. -/
theorem truncated_positive_window_le {a : ℕ → ℕ} (ha : StrictMono a)
    (B X S : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {w L : ℕ} (hwL : w ≤ L) (hL : 1 ≤ L)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {C : ℝ} (hf : ∀ x, f x ≤ C) :
    windowAvgReal (seqWindow a X) (fun n ↦
      f (CoreCyclic.coreLocalSeriesTrunc B hk phase (realGap a) F n (L - w) :
        AddCircle (1 : ℝ))) ≤
      C * Stopped.failureMass (Icc 1 S) (patternMass a X (Icc 1 S)) L +
        ∑ U ∈ (Icc 1 S).powerset.filter (fun U ↦ U.card = L),
          f (CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
            (CoreCyclic.orderedRealGap U) : AddCircle (1 : ℝ)) *
              Stopped.shortShapeMass (Icc 1 S) (patternMass a X (Icc 1 S)) L U := by
  have h := positive_firstL_window_le ha X S hL
    (fun U ↦ f (CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
      (CoreCyclic.orderedRealGap U) : AddCircle (1 : ℝ))) (fun U ↦ hf _)
  simpa only [finitePhase_prefix_eq ha B hk phase F hwL hw] using h

/-- The finite stopped inequality in arbitrary positive test units. -/
theorem bounded_positive_test_le_budget
    {Ω : Finset ℕ} {μ ν : Finset ℕ → ℝ} {L R : ℕ} {c C : ℝ}
    {f : Finset ℕ → ℝ}
    (hL : 1 ≤ L) (hLR : L ≤ R) (hpar : Odd (R - L))
    (hc : 0 ≤ c) (hC : 0 < C)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U) (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U)
    (hf0 : ∀ U ∈ Ω.powerset.filter (fun U ↦ U.card = L), 0 ≤ f U)
    (hfC : ∀ U ∈ Ω.powerset.filter (fun U ↦ U.card = L), f U ≤ C) :
    C * Stopped.failureMass Ω μ L +
        (∑ U ∈ Ω.powerset.filter (fun U ↦ U.card = L),
          f U * Stopped.shortShapeMass Ω μ L U) ≤
      c * (∑ U ∈ Ω.powerset.filter (fun U ↦ U.card = L),
          f U * Stopped.shortShapeMass Ω ν L U) +
        C * Stopped.stoppedPositiveBudget Ω μ ν L R c := by
  have h := Stopped.failure_add_positive_test_le_stopped_budget
    (f := fun U ↦ f U / C) hL hLR hpar hc hμ hν
    (fun U hU ↦ div_nonneg (hf0 U hU) hC.le)
    (fun U hU ↦ (div_le_one hC).mpr (hfC U hU))
  have hm := mul_le_mul_of_nonneg_left h hC.le
  have heq (m : Finset ℕ → ℝ) :
      C * (∑ U ∈ Ω.powerset.filter (fun U ↦ U.card = L), f U / C * m U) =
        ∑ U ∈ Ω.powerset.filter (fun U ↦ U.card = L), f U * m U := by
    rw [mul_sum]
    apply sum_congr rfl
    intro U hU
    field_simp [hC.ne']
  simp only [mul_add] at hm
  rw [heq] at hm
  have heq2 : C * (c * (∑ U ∈ Ω.powerset.filter (fun U ↦ U.card = L),
      f U / C * Stopped.shortShapeMass Ω ν L U)) =
      c * (∑ U ∈ Ω.powerset.filter (fun U ↦ U.card = L),
        f U * Stopped.shortShapeMass Ω ν L U) := by
    rw [mul_left_comm, heq]
  rwa [heq2] at hm

/-- Positive transfer to any nonnegative model, with the exact stopped
budget and no calibration or distribution assumption hidden in the type. -/
theorem truncated_positive_window_le_budget
    {a : ℕ → ℕ} (ha : StrictMono a) {B X S L w R k : ℕ}
    (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k) (hwL : w ≤ L)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    {ν : Finset ℕ → ℝ} {c C : ℝ}
    (hL : 1 ≤ L) (hLR : L ≤ R) (hpar : Odd (R - L))
    (hc : 0 ≤ c) (hC : 0 < C)
    (hν : ∀ U ∈ (Icc 1 S).powerset, 0 ≤ ν U)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C) :
    windowAvgReal (seqWindow a X) (fun n ↦
      f (CoreCyclic.coreLocalSeriesTrunc B hk phase (realGap a) F n (L - w) :
        AddCircle (1 : ℝ))) ≤
      c * (∑ U ∈ (Icc 1 S).powerset.filter (fun U ↦ U.card = L),
        f (CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
          (CoreCyclic.orderedRealGap U) : AddCircle (1 : ℝ)) *
            Stopped.shortShapeMass (Icc 1 S) ν L U) +
      C * Stopped.stoppedPositiveBudget (Icc 1 S)
        (patternMass a X (Icc 1 S)) ν L R c := by
  exact (truncated_positive_window_le ha B X S hk phase F hwL hL hw f hfC).trans
    (bounded_positive_test_le_budget hL hLR hpar hc hC
      (fun U _ ↦ patternMass_nonneg a X (Icc 1 S) U) hν
      (fun U _ ↦ hf0 _) (fun U _ ↦ hfC _))

end
end PrimeGapNormality.Prime.CoreSequenceLocalPositiveWindow
