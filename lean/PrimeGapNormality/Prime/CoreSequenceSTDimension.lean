import PrimeGapNormality.Prime.CorePrimeLocalDimensionEnd
import PrimeGapNormality.Prime.CoreSequenceSTRelations

/-!
# Dimension of actual sequence series under concrete S/T

The finite-variable embeddings and rooted monomial count are reused from
the previously proved finite algebra. No prime arithmetic theorem is used.
The new evaluation map uses the actual gaps of a general sequence, and its
kernel is proved trivial by the generic S/T rational-relation criterion.
The span is the literal rational span of 1 and all bounded-degree local
series, not a postulated finite-dimensional image.
-/

namespace PrimeGapNormality.Prime.CoreSequenceSTDimension

open Finset Filter MvPolynomial CoreCyclic CoreNormalMonomialDimension
open CoreSequenceSTConsumer CoreSequenceSTClassification CoreSequenceSTRelations
open CoreSequenceSubexponentialGrowth
open CorePrimeLocalDimensionEnd
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Q-linear evaluation of the rational constant coordinate and the actual
convergent local sequence series. Growth is internal data for this map; it
is derived, not assumed, in the final S/T theorem. -/
def evaluation {a : ℕ → ℕ} {B H k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (hH : 0 < H) (D : ℕ)
    (hg : HasSubexponentialGrowth (fun n => (seqGap a n : ℝ))) :
    (ℚ × (Fin k → rootedSpace hH D)) →ₗ[ℚ] ℝ :=
  (Algebra.linearMap ℚ ℝ).comp (LinearMap.fst ℚ ℚ (Fin k → rootedSpace hH D)) +
    (sequenceSeriesLinear hB hk phase hg).comp
      ((embedRooted hH D k).comp (LinearMap.snd ℚ ℚ (Fin k → rootedSpace hH D)))

theorem evaluation_apply {a : ℕ → ℕ} {B H k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (hH : 0 < H) (D : ℕ)
    (hg : HasSubexponentialGrowth (fun n => (seqGap a n : ℝ)))
    (q : ℚ) (F : Fin k → rootedSpace hH D) :
    evaluation hB hk phase hH D hg (q, F) = (q : ℝ) +
      coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (embedRooted hH D k F) := rfl

theorem evaluation_injective_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k) (hH : 0 < H)
    (hg : HasSubexponentialGrowth (fun n => (seqGap a n : ℝ)))
    {κ c : ℝ} (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    Function.Injective (evaluation hB hk phase hH D hg) := by
  have hker : ∀ v, evaluation hB hk phase hH D hg v = 0 → v = 0 := by
    rintro ⟨q, F⟩ hz
    have hκF : (topDegree (normalForm hB hk (embedRooted hH D k F)) : ℝ) /
        Real.log (B : ℝ) ≤ κ := by
      rw [normalForm_embedRooted]
      exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr (topDegree_embedRooted_le hH F))
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega)))).trans hκ
    have hNF := (local_rational_iff_normalForm_zero ha hB hk phase
      (embedRooted hH D k F) hκF hc hmodelScale hTail hS).mp
      (show ∃ r : ℚ, coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ))
        (embedRooted hH D k F) = (r : ℝ) from by
          refine ⟨-q, ?_⟩
          rw [evaluation_apply] at hz
          push_cast
          linarith)
    rw [normalForm_embedRooted] at hNF
    have hF : F = 0 := by
      apply embedRooted_injective hH D k
      simpa only [map_zero] using hNF
    subst F
    have hq : q = 0 := by
      change (q : ℝ) + sequenceSeriesLinear hB hk phase hg (embedRooted hH D k 0) = 0 at hz
      simp only [map_zero, add_zero] at hz
      exact Rat.cast_eq_zero.mp hz
    subst q
    rfl
  intro v w hvw
  exact sub_eq_zero.mp (hker (v - w) (by rw [map_sub, hvw, sub_self]))

/-- The literal generating set, including the rational coordinate 1. -/
def seriesGenerators (a : ℕ → ℕ) (B H D : ℕ) {k : ℕ} (hk : 0 < k)
    (phase : Fin k) : Set ℝ :=
  insert 1 {x | ∃ F : Fin k → MvPolynomial (Fin H) ℚ,
    (∀ r, (F r).totalDegree ≤ D) ∧
      x = coreCyclicFullSeries B hk phase (fun n => (seqGap a n : ℝ)) (embedTuple H k F)}

def seriesSpan (a : ℕ → ℕ) (B H D : ℕ) {k : ℕ} (hk : 0 < k)
    (phase : Fin k) : Submodule ℚ ℝ :=
  Submodule.span ℚ (seriesGenerators a B H D hk phase)

/-- Exact range/span identification. Canonical finite support and the
actual integer-gap rational boundary provide the reverse inclusion. -/
theorem evaluation_range_eq_seriesSpan
    {a : ℕ → ℕ} {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (hH : 0 < H)
    (hg : HasSubexponentialGrowth (fun n => (seqGap a n : ℝ))) :
    LinearMap.range (evaluation hB hk phase hH D hg) = seriesSpan a B H D hk phase := by
  apply le_antisymm
  · rintro x ⟨⟨q, R⟩, rfl⟩
    rw [evaluation_apply]
    apply Submodule.add_mem
    · have h1 : (1 : ℝ) ∈ seriesSpan a B H D hk phase :=
        Submodule.subset_span (Set.mem_insert _ _)
      have hq := (seriesSpan a B H D hk phase).smul_mem q h1
      simpa only [Rat.smul_def, mul_one] using hq
    · apply Submodule.subset_span
      apply Set.mem_insert_of_mem
      exact ⟨fun r => (R r : MvPolynomial (Fin H) ℚ),
        fun r => rootedSpace_totalDegree hH (R r), rfl⟩
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · refine ⟨(1, 0), ?_⟩
      rw [evaluation_apply, map_zero]
      simp [coreCyclicFullSeries, localValue]
    · obtain ⟨F, hdeg, rfl⟩ := hx
      obtain ⟨R, hR⟩ := exists_finite_rooted_normalForm hB hk hH F hdeg
      refine ⟨(sequenceLocalBoundaryRat hB hk phase a (embedTuple H k F), R), ?_⟩
      rw [evaluation_apply, hR,
        coreCyclicFullSeries_eq_normalForm_add_boundary_of_subexponential
          hB hk phase (embedTuple H k F) hg]
      ring

/-- Actual image dimension under the concrete S/T inputs. -/
theorem finrank_evaluation_range_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hH : 0 < H) (hD : 0 < D)
    (hg : HasSubexponentialGrowth (fun n => (seqGap a n : ℝ)))
    {κ c : ℝ} (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    Module.finrank ℚ (LinearMap.range (evaluation hB hk phase hH D hg)) =
      1 + k * (H + D - 1).choose (D - 1) := by
  rw [LinearMap.finrank_range_of_inj
    (evaluation_injective_of_shapeS ha hB hk phase hH hg hκ hc hmodelScale hTail hS)]
  exact finrank_constant_and_labelled_rootedSpace hH hD k

/-- The paper's actual series-span dimension for a general sequence under
concrete ShapeS and genuine GapTailT. No growth, count, rank or independence
hypothesis is retained; the effective degree budget is unchanged. -/
theorem finrank_seriesSpan_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a)
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hH : 0 < H) (hD : 0 < D)
    {κ c : ℝ} (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hc : 0 < c) (hmodelScale : Tendsto T atTop atTop)
    (hTail : GapTailT a (localTailBase κ) (windowG ∘ T))
    (hS : SequencePositiveShapeS a T κ c) :
    Module.finrank ℚ (seriesSpan a B H D hk phase) =
      1 + k * (H + D - 1).choose (D - 1) := by
  have hκpos : 0 < κ := (div_pos (Nat.cast_pos.mpr hD)
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hcount := CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
    ha hκpos hc hmodelScale hS hTail
  have hg := sequenceGap_hasSubexponentialGrowth ha hcount
  rw [← evaluation_range_eq_seriesSpan hB hk phase hH hg]
  exact finrank_evaluation_range_of_shapeS ha hB hk phase hH hD hg hκ hc hmodelScale hTail hS

end
end PrimeGapNormality.Prime.CoreSequenceSTDimension
