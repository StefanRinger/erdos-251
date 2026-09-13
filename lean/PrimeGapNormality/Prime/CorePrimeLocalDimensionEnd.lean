import PrimeGapNormality.Prime.CoreNormalMonomialDimension
import PrimeGapNormality.Prime.CoreLocalRelations
import PrimeGapNormality.Prime.CoreCyclicDegree

/-!
# Dimension of the span of the actual local prime-gap series

The finite canonical algebra evaluates into the actual convergent series.
Injectivity is derived from the D-only irrationality theorem for nonzero
normal classes; no independence or rank assumption is introduced.
-/

namespace PrimeGapNormality.Prime.CorePrimeLocalDimensionEnd

open Finset MvPolynomial CoreCyclic CoreNormalMonomialDimension
noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def embedTuple (H k : ℕ) : (Fin k → MvPolynomial (Fin H) ℚ) →ₗ[ℚ] PeriodicLocal k where
  toFun F := fun r => rename Fin.val (F r)
  map_add' F G := by funext r; simp
  map_smul' q F := by funext r; simp

def embedRooted {H : ℕ} (hH : 0 < H) (D k : ℕ) :
    (Fin k → rootedSpace hH D) →ₗ[ℚ] PeriodicLocal k where
  toFun F := embedTuple H k (fun r => (F r : MvPolynomial (Fin H) ℚ))
  map_add' F G := by funext r; simp [embedTuple]
  map_smul' q F := by funext r; simp [embedTuple]

theorem embedRooted_injective {H : ℕ} (hH : 0 < H) (D k : ℕ) :
    Function.Injective (embedRooted hH D k) := by
  intro F G h
  funext r
  apply Subtype.ext
  exact rename_injective Fin.val Fin.val_injective (congrFun h r)

theorem embedTuple_usesBelow (H k : ℕ) (F : Fin k → MvPolynomial (Fin H) ℚ) :
    UsesBelow (embedTuple H k F) H := by
  intro r i hi
  obtain ⟨j, hj, hji⟩ := mem_vars_rename Fin.val (F r) hi
  exact hji ▸ j.isLt

theorem rootedSpace_totalDegree {H D : ℕ} (hH : 0 < H) (p : rootedSpace hH D) :
    (p : MvPolynomial (Fin H) ℚ).totalDegree ≤ D := by
  unfold totalDegree
  apply Finset.sup_le
  intro m hm
  exact (p.2 hm).2

theorem embedRooted_degree {H D k : ℕ} (hH : 0 < H)
    (F : Fin k → rootedSpace hH D) (r : Fin k) :
    (embedRooted hH D k F r).totalDegree ≤ D :=
  (totalDegree_rename_le Fin.val (F r : MvPolynomial (Fin H) ℚ)).trans
    (rootedSpace_totalDegree hH (F r))

theorem embedRooted_rooted {H D k : ℕ} (hH : 0 < H) (hk : 0 < k)
    (F : Fin k → rootedSpace hH D) : drop hk (embedRooted hH D k F) = 0 := by
  rw [drop_eq_zero_iff_rooted]
  intro r m hm
  by_contra hc
  have hs : m ∈ (rename Fin.val (F r : MvPolynomial (Fin H) ℚ)).support :=
    mem_support_iff.mpr hc
  rw [support_rename_of_injective Fin.val_injective] at hs
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
  have hr := (F r).2 he
  have hval : (e.mapDomain Fin.val) 0 = e (origin hH) := by
    simpa only [origin] using Finsupp.mapDomain_apply Fin.val_injective e (origin hH)
  rw [hval] at hm
  exact hr.1.ne' hm

theorem normalForm_embedRooted {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (hH : 0 < H) (F : Fin k → rootedSpace hH D) :
    normalForm hB hk (embedRooted hH D k F) = embedRooted hH D k F :=
  normalForm_of_rooted hB hk _ (embedRooted_rooted hH hk F)

theorem topDegree_embedRooted_le {H D k : ℕ} (hH : 0 < H)
    (F : Fin k → rootedSpace hH D) : topDegree (embedRooted hH D k F) ≤ D :=
  Finset.sup_le fun r _ => embedRooted_degree hH F r

/-- The actual Q-linear evaluation, including the rational boundary
coordinate. Both polynomial and series maps are proved linear. -/
def evaluation {B H k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hH : 0 < H) (D : ℕ) : (ℚ × (Fin k → rootedSpace hH D)) →ₗ[ℚ] ℝ :=
  (Algebra.linearMap ℚ ℝ).comp (LinearMap.fst ℚ ℚ (Fin k → rootedSpace hH D)) +
    (CoreLocalRelations.primeSeriesLinear hB hk phase).comp
      ((embedRooted hH D k).comp (LinearMap.snd ℚ ℚ (Fin k → rootedSpace hH D)))

theorem evaluation_apply {B H k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hH : 0 < H) (D : ℕ) (a : ℚ) (F : Fin k → rootedSpace hH D) :
    evaluation hB hk phase hH D (a, F) = (a : ℝ) +
      coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (embedRooted hH D k F) := rfl

/-- A nonzero normal class cannot cancel the rational boundary coordinate.
This is where the actual arithmetic theorem enters. -/
theorem evaluation_injective_of_D
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k) (hH : 0 < H)
    {κ d0 c : ℝ} (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    Function.Injective (evaluation hB hk phase hH D) := by
  have hker : ∀ v, evaluation hB hk phase hH D v = 0 → v = 0 := by
    rintro ⟨a, F⟩ hz
    have hF : F = 0 := by
      by_contra hF
      have hN : embedRooted hH D k F ≠ 0 := by
        intro he
        apply hF
        apply embedRooted_injective hH D k
        simpa only [map_zero] using he
      have hκN : (topDegree (normalForm hB hk (embedRooted hH D k F)) : ℝ) /
          Real.log (B : ℝ) ≤ κ := by
        rw [normalForm_embedRooted]
        exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr (topDegree_embedRooted_le hH F))
          (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B)))).trans hκ
      have hi := corePrime_local_irrational_of_D hB hk phase (embedRooted hH D k F)
        (by rwa [normalForm_embedRooted]) hκN hd0 hc hD
      apply hi
      refine ⟨-a, ?_⟩
      rw [evaluation_apply] at hz
      push_cast
      linarith
    subst F
    have ha : a = 0 := by
      change (a : ℝ) + CoreLocalRelations.primeSeriesLinear hB hk phase
        (embedRooted hH D k 0) = 0 at hz
      simp only [map_zero, add_zero] at hz
      exact Rat.cast_eq_zero.mp hz
    subst a
    rfl
  intro v z hvz
  have hz := hker (v - z) (by rw [map_sub, hvz, sub_self])
  exact sub_eq_zero.mp hz

/-- Already an actual-series image dimension, with no rank hypothesis. -/
theorem finrank_evaluation_range_of_D
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hH : 0 < H) (hDpos : 0 < D)
    {κ d0 c : ℝ} (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    Module.finrank ℚ (LinearMap.range (evaluation hB hk phase hH D)) =
      1 + k * (H + D - 1).choose (D - 1) := by
  rw [LinearMap.finrank_range_of_inj (evaluation_injective_of_D hB hk phase hH hκ hd0 hc hD)]
  exact finrank_constant_and_labelled_rootedSpace hH hDpos k

/-- Actual normal reduction stays within the same H finite variables and
degree bound, and can therefore be pulled back through their embedding. -/
theorem exists_finite_rooted_normalForm
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (hH : 0 < H)
    (F : Fin k → MvPolynomial (Fin H) ℚ) (hdeg : ∀ r, (F r).totalDegree ≤ D) :
    ∃ R : Fin k → rootedSpace hH D,
      embedRooted hH D k R = normalForm hB hk (embedTuple H k F) := by
  let N := normalForm hB hk (embedTuple H k F)
  have hNroot : drop hk N = 0 := drop_normalForm hB hk _
  have hNwidth : UsesBelow N H :=
    normalForm_usesBelow hB hk _ (embedTuple_usesBelow H k F)
  have hNdeg : ∀ r, (N r).totalDegree ≤ D :=
    normalForm_totalDegree_le hB hk _ D
      (fun r => (totalDegree_rename_le Fin.val (F r)).trans (hdeg r))
  let q : Fin k → MvPolynomial (Fin H) ℚ := fun r => killCompl Fin.val_injective (N r)
  have hq : ∀ r, q r ∈ rootedSpace hH D := by
    intro r
    change ∀ m, m ∈ (q r).support → 0 < m (origin hH) ∧ m.degree ≤ D
    intro m hm
    have hcoeff : (N r).coeff (m.mapDomain Fin.val) ≠ 0 := by
      simpa only [q, coeff_killCompl] using mem_support_iff.mp hm
    constructor
    · by_contra hn
      have hm0 : m (origin hH) = 0 := Nat.eq_zero_of_not_pos hn
      have hmap0 : (m.mapDomain Fin.val) 0 = 0 := by
        exact (Finsupp.mapDomain_apply Fin.val_injective m (origin hH)).trans hm0
      exact hcoeff ((drop_eq_zero_iff_rooted hk N).mp hNroot r _ hmap0)
    · have hdegree : (m.mapDomain Fin.val).degree ≤ D :=
        (le_totalDegree (mem_support_iff.mpr hcoeff)).trans (hNdeg r)
      simpa only [Finsupp.degree_mapDomain] using hdegree
  refine ⟨fun r => ⟨q r, hq r⟩, ?_⟩
  funext r
  obtain ⟨P, hP⟩ := exists_rename_eq_of_vars_subset_range (N r)
    (Fin.val : Fin H → ℕ) Fin.val_injective
    (fun i hi => ⟨⟨i, hNwidth r i hi⟩, rfl⟩)
  change rename Fin.val (killCompl Fin.val_injective (N r)) = N r
  rw [← hP, killCompl_rename_app]

/-- The generators in the paper's span: 1 and all actual series of tuples
in precisely H variables, componentwise total degree at most D. -/
def seriesGenerators (B H D : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k) : Set ℝ :=
  insert 1 {x | ∃ F : Fin k → MvPolynomial (Fin H) ℚ,
    (∀ r, (F r).totalDegree ≤ D) ∧
      x = coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (embedTuple H k F)}

def seriesSpan (B H D : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k) : Submodule ℚ ℝ :=
  Submodule.span ℚ (seriesGenerators B H D hk phase)

/-- Exact range/span identification. Normal reduction and its rational
boundary supply surjectivity; neither a span equality nor a rank is assumed. -/
theorem evaluation_range_eq_seriesSpan
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k) (hH : 0 < H) :
    LinearMap.range (evaluation hB hk phase hH D) = seriesSpan B H D hk phase := by
  apply le_antisymm
  · rintro x ⟨⟨a, R⟩, rfl⟩
    rw [evaluation_apply]
    apply Submodule.add_mem
    · have h1 : (1 : ℝ) ∈ seriesSpan B H D hk phase :=
        Submodule.subset_span (Set.mem_insert _ _)
      have ha := (seriesSpan B H D hk phase).smul_mem a h1
      simpa only [Rat.smul_def, mul_one] using ha
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
      refine ⟨(primeLocalBoundaryRat hB hk phase (embedTuple H k F), R), ?_⟩
      rw [evaluation_apply, hR, coreCyclicFullSeries_eq_normalForm_add_boundary hB hk phase
        (embedTuple H k F)]
      ring

/-- The frozen paper's dimension formula for the span of the actual
prime-gap series, under the single common D hypothesis. -/
theorem finrank_seriesSpan_of_D
    {B H D k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (hH : 0 < H) (hDpos : 0 < D)
    {κ d0 c : ℝ} (hκ : (D : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    Module.finrank ℚ (seriesSpan B H D hk phase) =
      1 + k * (H + D - 1).choose (D - 1) := by
  rw [← evaluation_range_eq_seriesSpan hB hk phase hH]
  exact finrank_evaluation_range_of_D hB hk phase hH hDpos hκ hd0 hc hD

end
end PrimeGapNormality.Prime.CorePrimeLocalDimensionEnd
