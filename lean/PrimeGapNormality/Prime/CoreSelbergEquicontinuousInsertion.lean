import PrimeGapNormality.Prime.CoreSelbergEquicontinuousCells
import PrimeGapNormality.Prime.CoreCompactContinuousInsertion

/-!
# Uniform positive insertion for equicontinuous test families

This is the literal equicontinuous version of the positive-insertion estimate
used in the paper.  The family has a common compact modulus, but it need not
have a common Lipschitz constant.  The Selberg bound on every integer cell is
the already-proved arithmetic input; the only new error is the common
oscillation on a normalized cell, plus the bounded padded endpoint.
-/

namespace PrimeGapNormality.Prime.CoreSelbergEquicontinuousInsertion

open Finset Filter PrimeGapNormality.Prime.CoreSelberg
open MeasureTheory (volume)
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- The finite mesh estimate, exposed in the equicontinuous insertion
namespace. Its proof is already oscillation-only: it uses no Lipschitz
constant. -/
theorem finite_mesh_majorant {E : Finset ℕ} {a H R M : ℕ} {G η : ℝ}
    (hG : 0 < G) (hR : 1 ≤ R) (hRH : R ≤ H) (hη : 0 ≤ η)
    (hE : E ⊆ Ioc a (a + M * H)) (havoid : AvoidsResidues E R)
    (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Icc 0 ((M : ℝ) * ((H : ℝ) / G))))
    (hf : ∀ t ∈ Set.Icc 0 ((M : ℝ) * ((H : ℝ) / G)), 0 ≤ f t)
    (hosc : ∀ t ∈ Set.Icc 0 ((M : ℝ) * ((H : ℝ) / G)),
      ∀ u ∈ Set.Icc 0 ((M : ℝ) * ((H : ℝ) / G)),
        dist t u ≤ (H : ℝ) / G → |f t - f u| ≤ η) :
    ((H : ℝ) / G) * (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
      cellCap H R * ((∫ t in 0..((M : ℝ) * ((H : ℝ) / G)), f t) +
        η * ((M : ℝ) * ((H : ℝ) / G))) := by
  exact CoreCompactContinuousInsertion.finite_mesh_majorant hG hR hRH hη
    hE havoid f hc hf hosc

/-- Finite positive insertion with an arbitrary common cell oscillation. -/
theorem finite_positive_insertion {E : Finset ℕ} {a H R : ℕ}
    {G A C W η : ℝ}
    (hG : 0 < G) (hR : 1 ≤ R) (hRH : R ≤ H)
    (hmesh : (H : ℝ) / G ≤ 1) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hW : 0 ≤ W) (hWA : W ≤ A)
    (hE : ∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G)
    (havoid : AvoidsResidues E R) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Set.Icc 0 (A + 1)))
    (hf : ∀ t ∈ Set.Icc 0 (A + 1), 0 ≤ f t ∧ f t ≤ C)
    (hosc : ∀ t ∈ Set.Icc 0 (A + 1), ∀ u ∈ Set.Icc 0 (A + 1),
      dist t u ≤ (H : ℝ) / G → |f t - f u| ≤ η) :
    (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
      cellCap H R / ((H : ℝ) / G) *
        ((∫ t in 0..W, f t) + C * ((H : ℝ) / G) + η * (A + 1)) := by
  exact CoreCompactContinuousInsertion.finite_positive_insertion hG hR hRH
    hmesh hC hη hW hWA hE havoid f hc hf hosc

/-- The paper's positive insertion estimate for an arbitrary bounded
equicontinuous family.  The threshold in `G` is chosen before the family
index, integer location, presieve, and normalized width. -/
theorem eventually_positive_insertion {ι : Type*} (f : ι → ℝ → ℝ)
    {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (heq : EquicontinuousOn f (Set.Icc 0 (A + 1)))
    (hf : ∀ i t, t ∈ Set.Icc 0 (A + 1) → 0 ≤ f i t ∧ f i t ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ G : ℝ in atTop, ∀ (i : ι) (a : ℕ) (W : ℝ) (E : Finset ℕ),
      0 ≤ W → W ≤ A →
      (∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G) →
      AvoidsResidues E ⌊G⌋₊ →
      (∑ n ∈ E, f i (((n : ℝ) - a) / G)) ≤
        3 * G / Real.log G * ((∫ t in 0..W, f i t) + ε) := by
  let η : ℝ := ε / (2 * (A + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ0, hδ0, hmod⟩ := CoreSelberg.compact_equicontinuous_modulus f heq hη
  let δ : ℝ := min 1 (min δ0 (ε / (2 * (C + 1))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ0' : δ ≤ δ0 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : C * δ + η * (A + 1) ≤ ε := by
    have hh : δ ≤ ε / (2 * (C + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp hh
    have heq : η * (A + 1) = ε / 2 := by
      dsimp [η]
      field_simp [ne_of_gt (by positivity : 0 < A + 1)]
    rw [heq]
    nlinarith [hδ.le]
  filter_upwards [eventually_mesh_density_le_three hδ hδ1] with G hmesh
  obtain ⟨hGone, hH, hR, hRH, hHfloor, hmeshδ, hcap⟩ := hmesh
  intro i a W E hW hWA hE havoid
  have hG : 0 < G := zero_lt_one.trans hGone
  have hcont : ContinuousOn (f i) (Set.Icc 0 (A + 1)) := heq.continuousOn i
  have hlocal : ∀ t ∈ Set.Icc 0 (A + 1), ∀ u ∈ Set.Icc 0 (A + 1),
      dist t u ≤ (meshLength δ G : ℝ) / G → |f i t - f i u| ≤ η := by
    intro t ht u hu htu
    apply hmod i t ht u hu
    rw [← Real.dist_eq]
    exact htu.trans (hmeshδ.trans hδ0')
  have hfinite := finite_positive_insertion hG hR hRH (hmeshδ.trans hδ1)
    hC hη.le hW hWA hE (havoid.radius_mono (hRH.trans hHfloor)) (f i)
    hcont (fun t ht => hf i t ht) hlocal
  have hI : 0 ≤ ∫ t in 0..W, f i t :=
    intervalIntegral.integral_nonneg hW
      (fun t ht => (hf i t ⟨ht.1, ht.2.trans (by linarith)⟩).1)
  have hmeshnonneg : 0 ≤ (meshLength δ G : ℝ) / G :=
    div_nonneg (Nat.cast_nonneg _) hG.le
  have herr : C * ((meshLength δ G : ℝ) / G) + η * (A + 1) ≤ ε :=
    (add_le_add (mul_le_mul_of_nonneg_left hmeshδ hC) le_rfl).trans hδε
  have hbracket : 0 ≤ (∫ t in 0..W, f i t) +
      C * ((meshLength δ G : ℝ) / G) + η * (A + 1) := by
    exact add_nonneg
      (add_nonneg hI (mul_nonneg hC hmeshnonneg))
      (mul_nonneg hη.le (by linarith : 0 ≤ A + 1))
  have hfactor : 0 ≤ 3 * G / Real.log G :=
    div_nonneg (by positivity) (Real.log_pos hGone).le
  change cellCap (meshLength δ G) (selbergRadius (meshLength δ G)) /
    ((meshLength δ G : ℝ) / G) ≤ 3 * G / Real.log G at hcap
  exact hfinite.trans ((mul_le_mul_of_nonneg_right hcap hbracket).trans
    (mul_le_mul_of_nonneg_left (by linarith) hfactor))

end
end PrimeGapNormality.Prime.CoreSelbergEquicontinuousInsertion
