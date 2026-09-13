import PrimeGapNormality.Prime.CoreSequenceSTClassification
import PrimeGapNormality.Prime.CoreLocalRelations
import PrimeGapNormality.Prime.JointWeyl

/-!
# Finite-family relations for concrete sequence S/T

Every nonzero character of a fixed finite family is treated as one rational
combination of its local tuples.  The sequence count, subexponential growth,
and summability needed to exchange the finite sum with the infinite series
are derived from the same concrete `SequencePositiveShapeS` and `GapTailT`
inputs.  No scalar-normality-to-joint shortcut is used.

As in the underlying classification, the model is specifically
`finiteRootMix (T X)`; this is not yet the arbitrary calibrated-mixture
version of the paper criterion.
-/

namespace PrimeGapNormality.Prime.CoreSequenceSTRelations

open Finset Filter MvPolynomial CoreCyclic
open CoreSequenceSTConsumer CoreSequenceSTClassification
open CoreSequenceSubexponentialGrowth
open scoped Topology Classical

noncomputable section

set_option maxHeartbeats 800000

private theorem localClock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    2 ≤ B ^ k := by
  have hsplit : k = k - 1 + 1 :=
    (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [hsplit, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

private theorem kappa_pos_of_gapTail
    {κ : ℝ} {a T : ℕ → ℕ}
    (hTail : GapTailT a (localTailBase κ) (windowG ∘ T)) : 0 < κ := by
  have h : 0 < 1 / κ := by
    rw [← Real.one_lt_exp_iff]
    simpa only [localTailBase] using hTail.1
  exact one_div_pos.mp h

private theorem gap_hasSubexponentialGrowth_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a) {κ c : ℝ} (hc : 0 < c)
    (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    HasSubexponentialGrowth (fun n ↦ (seqGap a n : ℝ)) := by
  have hκ := kappa_pos_of_gapTail hGapTail
  have hcount := CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
    ha hκ hc hmodelScale hS hGapTail
  exact sequenceGap_hasSubexponentialGrowth ha hcount

private theorem sequenceSeries_summable
    {a : ℕ → ℕ} {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k)
    (hgrowth : HasSubexponentialGrowth (fun n ↦ (seqGap a n : ℝ))) :
    Summable (fun n : ℕ ↦
      localValue hk phase (fun q ↦ (seqGap a q : ℝ)) F n /
        (B : ℝ) ^ (n + 1)) := by
  simpa only [Nat.zero_add] using
    localSeries_summable_of_subexponential hB hk phase
      (fun q ↦ (seqGap a q : ℝ)) hgrowth F 0

private theorem localValue_smul
    {k : ℕ} (hk : 0 < k) (phase : Fin k) (g : ℕ → ℝ)
    (q : ℚ) (F : PeriodicLocal k) (n : ℕ) :
    localValue hk phase g (q • F) n =
      (q : ℝ) * localValue hk phase g F n := by
  simp [localValue, Pi.smul_apply, smul_eq_C_mul]

/-- The convergent series evaluation is an actual rational linear map once
the internally derived subexponential bound is supplied. -/
def sequenceSeriesLinear
    {a : ℕ → ℕ} {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k)
    (hgrowth : HasSubexponentialGrowth (fun n ↦ (seqGap a n : ℝ))) :
    PeriodicLocal k →ₗ[ℚ] ℝ where
  toFun := coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ))
  map_add' F H := by
    unfold coreCyclicFullSeries
    simp_rw [localValue_add, add_div]
    exact (sequenceSeries_summable hB hk phase F hgrowth).tsum_add
      (sequenceSeries_summable hB hk phase H hgrowth)
  map_smul' q F := by
    change coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ))
        (q • F) =
      q • coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) F
    unfold coreCyclicFullSeries
    simp_rw [localValue_smul, mul_div_assoc]
    rw [tsum_mul_left, Rat.smul_def]

private theorem fullSeries_sum_smul_of_growth
    {I : Type*} [Fintype I] {a : ℕ → ℕ}
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hgrowth : HasSubexponentialGrowth (fun n ↦ (seqGap a n : ℝ)))
    (F : I → PeriodicLocal k) (q : I → ℚ) :
    coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ))
        (∑ i, q i • F i) =
      ∑ i, (q i : ℝ) *
        coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap a n : ℝ)) (F i) := by
  change sequenceSeriesLinear hB hk phase hgrowth (∑ i, q i • F i) =
    ∑ i, (q i : ℝ) * sequenceSeriesLinear hB hk phase hgrowth (F i)
  simp only [map_sum, map_smul, Rat.smul_def]

/-- Public finite-sum/tsum linearity with all convergence derived from the
actual concrete S/T inputs. -/
theorem fullSeries_sum_smul_of_shapeS
    {I : Type*} [Fintype I] {a T : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k) (q : I → ℚ)
    {κ c : ℝ} (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ))
        (∑ i, q i • F i) =
      ∑ i, (q i : ℝ) *
        coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap a n : ℝ)) (F i) := by
  exact fullSeries_sum_smul_of_growth hB hk phase
    (gap_hasSubexponentialGrowth_of_shapeS ha hc hmodelScale hGapTail hS) F q

/-- Every nonzero rational combination has Weyl cancellation at the one
common period clock and one common effective-degree budget. -/
theorem combination_weyl_clock_of_shapeS
    {I : Type*} [Fintype I] {a T : ℕ → ℕ} (ha : StrictMono a)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    {κ c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c)
    (q : I → ℚ) (hq : (∑ i, q i • normalForm hB hk (F i)) ≠ 0) :
    weylCriterion (B ^ k)
      (∑ i, (q i : ℝ) * coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap a n : ℝ)) (F i)) := by
  have hlog : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hκq :
      (topDegree (normalForm hB hk (∑ i, q i • F i)) : ℝ) /
          Real.log (B : ℝ) ≤ κ :=
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr
      (CoreLocalRelations.topDegree_normalForm_sum_le hB hk F q hdeg)) hlog).trans hκ
  have hW := local_weyl_clock_of_shapeS ha hB hk phase (∑ i, q i • F i)
    (by rwa [CoreLocalRelations.normalForm_sum_smul]) hκq hc
    hmodelScale hGapTail hS
  rw [fullSeries_sum_smul_of_shapeS ha hB hk phase F q hc
    hmodelScale hGapTail hS] at hW
  exact hW

/-- Rational relations among the actual sequence series are exactly the
rational relations among their canonical normal forms. -/
theorem rational_relation_iff_of_shapeS
    {I : Type*} [Fintype I] {a T : ℕ → ℕ} (ha : StrictMono a)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    {κ c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) (q : I → ℚ) :
    (∃ r : ℚ, (∑ i, (q i : ℝ) *
      coreCyclicFullSeries B hk phase (fun n ↦ (seqGap a n : ℝ)) (F i)) =
        (r : ℝ)) ↔
      (∑ i, q i • normalForm hB hk (F i)) = 0 := by
  have hlog : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hκq :
      (topDegree (normalForm hB hk (∑ i, q i • F i)) : ℝ) /
          Real.log (B : ℝ) ≤ κ :=
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr
      (CoreLocalRelations.topDegree_normalForm_sum_le hB hk F q hdeg)) hlog).trans hκ
  have hrel := local_rational_iff_normalForm_zero ha hB hk phase
    (∑ i, q i • F i) hκq hc hmodelScale hGapTail hS
  rw [fullSeries_sum_smul_of_shapeS ha hB hk phase F q hc
    hmodelScale hGapTail hS,
    CoreLocalRelations.normalForm_sum_smul] at hrel
  exact hrel

/-- Q-independent normal classes give genuine joint Weyl cancellation at
the common `B^k` clock. -/
theorem jointWeyl_of_independent_normalForms_of_shapeS
    {I : Type*} [Fintype I] [DecidableEq I]
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i ↦ normalForm hB hk (F i)))
    {κ c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    JointWeyl (fun _ : I ↦ B ^ k)
      (fun i ↦ coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap a n : ℝ)) (F i)) := by
  intro t ht
  have hq : (∑ i, (t i : ℚ) • normalForm hB hk (F i)) ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := ht
    have heq := (Fintype.linearIndependent_iff.mp hlin)
      (fun i ↦ (t i : ℚ)) hz i
    exact hi (Int.cast_eq_zero.mp heq)
  have hW := combination_weyl_clock_of_shapeS ha hB hk phase F hdeg hκ hc
    hmodelScale hGapTail hS (fun i ↦ (t i : ℚ)) hq
  have hchar := hW 1 (by norm_num)
  have heq (n : ℕ) :
      (∑ i, (t i : ℝ) * ((B ^ k : ℕ) : ℝ) ^ n *
        coreCyclicFullSeries B hk phase
          (fun q ↦ (seqGap a q : ℝ)) (F i)) =
      ((1 : ℤ) : ℝ) * ((B ^ k : ℕ) : ℝ) ^ n *
        (∑ i, ((t i : ℚ) : ℝ) *
          coreCyclicFullSeries B hk phase
            (fun q ↦ (seqGap a q : ℝ)) (F i)) := by
    simp only [Int.cast_one, one_mul, Rat.cast_intCast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa only [heq] using hchar

/-- Consequently `1` and all actual family series are rationally linearly
independent. -/
theorem linearIndependent_one_of_independent_normalForms_of_shapeS
    {I : Type*} [Fintype I] [DecidableEq I]
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i ↦ normalForm hB hk (F i)))
    {κ c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hGapTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    LinearIndependent ℚ (fun i : Option I ↦ match i with
      | none => (1 : ℝ)
      | some i => coreCyclicFullSeries B hk phase
          (fun n ↦ (seqGap a n : ℝ)) (F i)) := by
  exact linearIndependent_one_jointWeyl (localClock_ge hB hk)
    (jointWeyl_of_independent_normalForms_of_shapeS ha hB hk phase
      F hdeg hlin hκ hc hmodelScale hGapTail hS)

end
end PrimeGapNormality.Prime.CoreSequenceSTRelations
