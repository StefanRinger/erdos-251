import PrimeGapNormality.Prime.CoreSelbergInsertionCells
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Positive insertion cells with an arbitrary common modulus

The paper's positive insertion estimate concerns bounded equicontinuous
families, not only families with one Lipschitz constant. The cell estimate
below uses only the oscillation on the cell. Compact equicontinuity gives
that oscillation uniformly before the test index is chosen.

This is a finite supplier, not by itself the final asymptotic Selberg
insertion theorem. Cell counts still come from the existing sieve proof.
-/

namespace PrimeGapNormality.Prime.CoreSelberg

open Finset Filter
open MeasureTheory (volume)
open scoped Topology
noncomputable section

/-- Integrate a cellwise oscillation bound. No differentiability or
Lipschitz assumption is needed. -/
theorem oscillation_cell_majorant {ι : Type*} (E : Finset ι) (z : ι → ℝ)
    (f : ℝ → ℝ) (l δ cap η : ℝ) (hδ : 0 < δ) (hη : 0 ≤ η)
    (hint : IntervalIntegrable f volume l (l + δ))
    (hz : ∀ n ∈ E, z n ∈ Set.Icc l (l + δ))
    (hf : ∀ t ∈ Set.Icc l (l + δ), 0 ≤ f t)
    (hosc : ∀ n ∈ E, ∀ t ∈ Set.Icc l (l + δ), f (z n) ≤ f t + η)
    (hcard : (E.card : ℝ) ≤ cap) :
    δ * (∑ n ∈ E, f (z n)) ≤
      cap * ((∫ t in l..(l + δ), f t) + η * δ) := by
  have hl : l ≤ l + δ := by linarith
  have hpoint : ∀ n ∈ E, δ * f (z n) ≤
      (∫ t in l..(l + δ), f t) + η * δ := by
    intro n hn
    have hmono := intervalIntegral.integral_mono_on hl
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f (z n))
        volume l (l + δ))
      (hint.add intervalIntegrable_const) (hosc n hn)
    calc
      δ * f (z n) = ∫ t in l..(l + δ), f (z n) := by
        simp [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ t in l..(l + δ), f t + η := hmono
      _ = (∫ t in l..(l + δ), f t) + η * δ := by
        rw [intervalIntegral.integral_add hint intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [add_sub_cancel_left, smul_eq_mul]
        ring
  have hnon : 0 ≤ (∫ t in l..(l + δ), f t) + η * δ :=
    add_nonneg (intervalIntegral.integral_nonneg hl hf) (mul_nonneg hη hδ.le)
  calc
    δ * (∑ n ∈ E, f (z n)) = ∑ n ∈ E, δ * f (z n) := Finset.mul_sum ..
    _ ≤ ∑ _n ∈ E, ((∫ t in l..(l + δ), f t) + η * δ) :=
      Finset.sum_le_sum hpoint
    _ = (E.card : ℝ) * ((∫ t in l..(l + δ), f t) + η * δ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ cap * ((∫ t in l..(l + δ), f t) + η * δ) :=
      mul_le_mul_of_nonneg_right hcard hnon

/-- The exact compactness step: one radius works for every member of a
compact equicontinuous family, with no common Lipschitz assumption. -/
theorem compact_equicontinuous_modulus {ι : Type*} (f : ι → ℝ → ℝ)
    {a b : ℝ} (heq : EquicontinuousOn f (Set.Icc a b))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ i u, u ∈ Set.Icc a b → ∀ v, v ∈ Set.Icc a b →
      |u - v| ≤ δ → |f i u - f i v| ≤ η := by
  have hcont := equicontinuousOn_iff_continuousOn.mp heq
  have huni := isCompact_Icc.uniformContinuousOn_of_continuous hcont
  have hueq := uniformEquicontinuousOn_iff_uniformContinuousOn.mpr huni
  have hrestr := (uniformEquicontinuous_restrict_iff f).mpr hueq
  obtain ⟨d, hd, hmod⟩ := Metric.uniformEquicontinuous_iff.mp hrestr η hη
  refine ⟨d / 2, half_pos hd, ?_⟩
  intro i u hu v hv huv
  have hdist : dist (⟨u, hu⟩ : Set.Icc a b) ⟨v, hv⟩ < d := by
    change dist u v < d
    rw [Real.dist_eq]
    exact lt_of_le_of_lt huv (half_lt_self hd)
  have hh := (hmod ⟨u, hu⟩ ⟨v, hv⟩ hdist i).le
  simpa only [Function.comp_apply, Set.domRestrict_apply, Real.dist_eq] using hh

end
end PrimeGapNormality.Prime.CoreSelberg
