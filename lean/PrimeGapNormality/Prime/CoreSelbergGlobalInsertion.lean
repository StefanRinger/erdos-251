import PrimeGapNormality.Prime.CoreSelbergPositiveInsertion

/-! Positive insertion on slots of arbitrary length. The explicit error
is linear in the normalized width, so its frame average uses the gap mean. -/

namespace PrimeGapNormality.Prime.CoreSelberg

open Finset Filter
open scoped Topology NNReal

noncomputable section

theorem eventually_global_positive_insertion {C : ℝ} {K : ℝ≥0} (hC : 0 ≤ C)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ G : ℝ in atTop, ∀ (a : ℕ) (W : ℝ) (E : Finset ℕ) (f : ℝ → ℝ),
      0 ≤ W → (∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G) →
      AvoidsResidues E ⌊G⌋₊ → LipschitzWith K f →
      (∀ t : ℝ, 0 ≤ f t ∧ f t ≤ C) →
      (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤ 3 * G / Real.log G *
        ((∫ t in 0..W, f t) + δ * (C + (K : ℝ) * (W + 1))) := by
  filter_upwards [eventually_mesh_density_le_three hδ hδ1] with G hmesh
  obtain ⟨hG, _, hR, hRH, hHfloor, hmeshδ, hcap⟩ := hmesh
  intro a W E f hW hE havoid hLip hf
  have hG0 : 0 < G := lt_trans zero_lt_one hG
  have havoidR := havoid.radius_mono (hRH.trans hHfloor)
  have hfinite := finite_positive_insertion hG0 hR hRH (hmeshδ.trans hδ1)
    hC hW le_rfl hE havoidR f hLip (fun t _ ↦ hf t)
  let D : ℝ := C + (K : ℝ) * (W + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hI : 0 ≤ ∫ t in 0..W, f t :=
    intervalIntegral.integral_nonneg_of_forall hW (fun t ↦ (hf t).1)
  have hwidth : 0 ≤ (meshLength δ G : ℝ) / G := div_nonneg (Nat.cast_nonneg _) hG0.le
  have hbracket : 0 ≤ (∫ t in 0..W, f t) + D * ((meshLength δ G : ℝ) / G) :=
    add_nonneg hI (mul_nonneg hD hwidth)
  have herror : D * ((meshLength δ G : ℝ) / G) ≤ δ * D := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmeshδ hD
  have hfactor : 0 ≤ 3 * G / Real.log G :=
    div_nonneg (mul_nonneg (by norm_num) hG0.le) (Real.log_pos hG).le
  change cellCap (meshLength δ G) (selbergRadius (meshLength δ G)) /
    ((meshLength δ G : ℝ) / G) ≤ 3 * G / Real.log G at hcap
  exact hfinite.trans ((mul_le_mul_of_nonneg_right hcap hbracket).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl herror) hfactor))

end

end PrimeGapNormality.Prime.CoreSelberg
