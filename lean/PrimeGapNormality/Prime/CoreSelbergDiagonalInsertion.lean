import PrimeGapNormality.Prime.CoreSelbergShrinkingMesh
import PrimeGapNormality.Prime.CoreDigitalLinearDomination
import PrimeGapNormality.Prime.CorePositiveTail

/-!
# Uniform positive insertion on a genuinely shrinking mesh

The threshold in this theorem is chosen before the slot, its length, the
test, its supremum bound, and its Lipschitz constant. In particular the
test may depend on the model scale. This is the diagonal, finite-scale
supplier needed by the quantitative appendix; it does not specialize an
eventual theorem for fixed mesh width to a varying width.

The final incomplete cell is paid once by the supremum bound. No bounded
slot length, compact-frame truncation, or gap moment is an assumption.
Pending central compilation; not an accepted quantitative normality result.
-/

namespace PrimeGapNormality.Prime.CoreSelbergDiagonalInsertion

open Filter Finset MeasureTheory
open CoreSelberg CoreSelbergShrinkingMesh
open scoped Topology NNReal Classical BoundedContinuousFunction

noncomputable section

/-- The scale threshold is uniform over all nonnegative bounded Lipschitz
tests and every physical slot. All constants and the square-root error are
supplied by the actual finite Selberg sieve. -/
theorem eventually_positive_insertion :
    ∀ᶠ G : ℝ in atTop, ∀ (a : ℕ) (E : Finset ℕ) (W C : ℝ)
      (f : ℝ → ℝ) (K : ℝ≥0),
      0 ≤ W → 0 ≤ C →
      (∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G) →
      AvoidsResidues E ⌊G⌋₊ → LipschitzWith K f →
      (∀ t, 0 ≤ f t ∧ f t ≤ C) →
      (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
        (6 * G / Real.log G) *
          ((∫ t in (0 : ℝ)..W, f t) +
            G ^ (-(1 / 2 : ℝ)) * ((K : ℝ) * W + C)) := by
  filter_upwards [eventually_shrinkingMesh_data] with G hdata
  intro a E W C f K hW hC hE havoid hLip hf
  obtain ⟨hG, hR, hRH, hHG, hδ, hcap⟩ := hdata
  have hG0 : 0 < G := zero_lt_one.trans hG
  have hδ0 : 0 ≤ shrinkingMeshDelta G :=
    div_nonneg (Nat.cast_nonneg _) hG0.le
  have havoidR : AvoidsResidues E (shrinkingMeshRadius G) :=
    havoid.radius_mono (hRH.trans hHG)
  have hfinite := finite_positive_insertion_with_last_cell
    hG0 hR hRH hC hW hE havoidR f hLip hf
  change (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
    cellCap (shrinkingMeshLength G) (shrinkingMeshRadius G) /
      shrinkingMeshDelta G *
        ((∫ t in (0 : ℝ)..W, f t) +
          (K : ℝ) * W * shrinkingMeshDelta G + C * shrinkingMeshDelta G)
    at hfinite
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..W, f t :=
    intervalIntegral.integral_nonneg hW (fun t _ ↦ (hf t).1)
  have hbracket0 : 0 ≤ (∫ t in (0 : ℝ)..W, f t) +
      (K : ℝ) * W * shrinkingMeshDelta G + C * shrinkingMeshDelta G :=
    add_nonneg (add_nonneg hI0 (mul_nonneg (mul_nonneg K.coe_nonneg hW) hδ0))
      (mul_nonneg hC hδ0)
  have herror := mul_le_mul_of_nonneg_left hδ
    (add_nonneg (mul_nonneg K.coe_nonneg hW) hC)
  have hbracket :
      (∫ t in (0 : ℝ)..W, f t) +
          (K : ℝ) * W * shrinkingMeshDelta G + C * shrinkingMeshDelta G ≤
        (∫ t in (0 : ℝ)..W, f t) +
          G ^ (-(1 / 2 : ℝ)) * ((K : ℝ) * W + C) := by
    nlinarith only [herror]
  have hcoef0 : 0 ≤ 6 * G / Real.log G :=
    div_nonneg (mul_nonneg (by norm_num) hG0.le) (Real.log_pos hG).le
  exact hfinite.trans ((mul_le_mul_of_nonneg_right hcap hbracket0).trans
    (mul_le_mul_of_nonneg_left hbracket hcoef0))

/-- Quantitative linear circle-phase insertion, uniform even over tests
whose Lipschitz constants grow with G. The nonzero slope bounds the
positive interval integral by its periodic mean times W+1. -/
theorem eventually_circle_linear_insertion :
    ∀ᶠ G : ℝ in atTop, ∀ (a : ℕ) (E : Finset ℕ) (W O s : ℝ)
      (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0),
      0 ≤ W → 1 ≤ |s| →
      (∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G) →
      AvoidsResidues E ⌊G⌋₊ → LipschitzWith K f →
      (∀ x, 0 ≤ f x) →
      (∑ n ∈ E, f ((O + s * (((n : ℝ) - a) / G) : ℝ) : AddCircle (1 : ℝ))) ≤
        (6 * G / Real.log G) *
          ((W + 1) * (∫ x : AddCircle (1 : ℝ), f x) +
            G ^ (-(1 / 2 : ℝ)) * ((K : ℝ) * |s| * W + ‖f‖)) := by
  filter_upwards [eventually_positive_insertion,
    eventually_gt_atTop (1 : ℝ)] with G hmain hG
  intro a E W O s f K hW hs hE havoid hLip hf
  let sabs : ℝ≥0 := ⟨|s|, abs_nonneg s⟩
  let K' : ℝ≥0 := K * sabs
  let g : ℝ → ℝ := fun t ↦ f ((O + s * t : ℝ) : AddCircle (1 : ℝ))
  have hK' : (K' : ℝ) = (K : ℝ) * |s| := rfl
  have hgLip : LipschitzWith K' g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (g x) (g y) ≤ (K : ℝ) *
          dist ((O + s * x : ℝ) : AddCircle (1 : ℝ))
            ((O + s * y : ℝ) : AddCircle (1 : ℝ)) := hLip.dist_le_mul _ _
      _ ≤ (K : ℝ) * |(O + s * x) - (O + s * y)| :=
        mul_le_mul_of_nonneg_left (coreCircle_dist_coe_le _ _) K.coe_nonneg
      _ = (K' : ℝ) * dist x y := by
        rw [show O + s * x - (O + s * y) = s * (x - y) by ring,
          abs_mul, Real.dist_eq, hK']
        ring
  have hg : ∀ t : ℝ, 0 ≤ g t ∧ g t ≤ ‖f‖ :=
    fun t ↦ ⟨hf _, f.apply_le_norm _⟩
  have hh := hmain a E W ‖f‖ g K' hW (norm_nonneg _) hE havoid hgLip hg
  have hI := coreDigital_circle_linear_insertion_integral_le
    (fun x ↦ f x) f.continuous hf O s W hs hW
  have hcoef : 0 ≤ 6 * G / Real.log G :=
    div_nonneg (mul_nonneg (by norm_num) (zero_lt_one.trans hG).le)
      (Real.log_pos hG).le
  change (∑ n ∈ E, f ((O + s * (((n : ℝ) - a) / G) : ℝ) : AddCircle (1 : ℝ))) ≤
    (6 * G / Real.log G) *
      ((∫ t in (0 : ℝ)..W, g t) +
        G ^ (-(1 / 2 : ℝ)) * ((K' : ℝ) * W + ‖f‖)) at hh
  rw [hK'] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (_root_.add_le_add hI le_rfl) hcoef)

end

end PrimeGapNormality.Prime.CoreSelbergDiagonalInsertion
