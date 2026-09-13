import PrimeGapNormality.Prime.CoreAuxiliaryGapMean

/-!
# Finite-mixture form of the auxiliary physical gap bound

This small wrapper averages the exact auxiliary-frame mean over an existing
`SieveMixture`.  The arithmetic support calibration is deliberately kept as
an explicit finite support inequality; cutoff and finite-root consumers can
supply it from their own concrete scales.
-/

open Finset
open scoped BigOperators

namespace PrimeGapNormality.Prime

noncomputable section

noncomputable def coreAuxiliaryMixturePhysicalGapMean
    (m : SieveMixture) (S L j : ℕ) : ℝ :=
  ∑ y ∈ m.support, m.weight y * coreAuxiliaryLayerPhysicalGapMean S y L j

/-- Direct paper-layer bound, after the exact late-fibre aggregation. -/
theorem coreAuxiliaryLayerPhysicalGapMean_le
    (S y L j : ℕ) (hSy : S ≤ y) (hj : j + 1 < L) :
    coreAuxiliaryLayerPhysicalGapMean S y L j ≤
      (2 : ℝ) * (eulerProdNat y)⁻¹ := by
  rw [coreAuxiliaryLayerPhysicalGapMean_eq_actual S y L j hSy
    (by omega : 1 ≤ L)]
  exact coreAuxiliaryPhysicalGapMean_le y S L j hj

/-- A normalized finite sieve mixture has auxiliary physical mean bounded by
the same mixture of the exact `2 / V(y)` first moments. -/
theorem coreAuxiliaryMixturePhysicalGapMean_le
    (m : SieveMixture) (S L j : ℕ)
    (hSy : ∀ y ∈ m.support, S ≤ y) (hj : j + 1 < L) :
    coreAuxiliaryMixturePhysicalGapMean m S L j ≤
      (2 : ℝ) * ∑ y ∈ m.support, m.weight y * (eulerProdNat y)⁻¹ := by
  unfold coreAuxiliaryMixturePhysicalGapMean
  calc
    (∑ y ∈ m.support,
        m.weight y * coreAuxiliaryLayerPhysicalGapMean S y L j) ≤
      ∑ y ∈ m.support,
        m.weight y * ((2 : ℝ) * (eulerProdNat y)⁻¹) := by
      refine sum_le_sum fun y hy => ?_
      exact mul_le_mul_of_nonneg_left
        (coreAuxiliaryLayerPhysicalGapMean_le S y L j (hSy y hy) hj)
        (m.weight_nonneg y hy)
    _ = (2 : ℝ) * ∑ y ∈ m.support,
        m.weight y * (eulerProdNat y)⁻¹ := by
      simp only [← mul_assoc]
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro y _hy
      ring

/-- Scale-normalized form.  The bound `V(y)⁻¹/G ≤ C` is supplied by the
concrete mixture calibration; it is not inferred from the abstract mixture. -/
theorem coreAuxiliaryMixturePhysicalGapMean_div_le
    (m : SieveMixture) (S L j : ℕ) {G C : ℝ}
    (hSy : ∀ y ∈ m.support, S ≤ y) (hj : j + 1 < L) (hG : 0 < G)
    (hcal : ∀ y ∈ m.support, (eulerProdNat y)⁻¹ / G ≤ C) :
    coreAuxiliaryMixturePhysicalGapMean m S L j / G ≤ (2 : ℝ) * C := by
  unfold coreAuxiliaryMixturePhysicalGapMean
  rw [Finset.sum_div]
  calc
    (∑ y ∈ m.support,
        (m.weight y * coreAuxiliaryLayerPhysicalGapMean S y L j) / G) =
      ∑ y ∈ m.support,
        m.weight y * (coreAuxiliaryLayerPhysicalGapMean S y L j / G) := by
      refine sum_congr rfl fun y _ => ?_
      ring
    _ ≤ ∑ y ∈ m.support, m.weight y * ((2 : ℝ) * C) := by
      refine sum_le_sum fun y hy => ?_
      apply mul_le_mul_of_nonneg_left _ (m.weight_nonneg y hy)
      calc
        coreAuxiliaryLayerPhysicalGapMean S y L j / G ≤
            ((2 : ℝ) * (eulerProdNat y)⁻¹) / G :=
          div_le_div_of_nonneg_right
            (coreAuxiliaryLayerPhysicalGapMean_le S y L j (hSy y hy) hj) hG.le
        _ = (2 : ℝ) * ((eulerProdNat y)⁻¹ / G) := by ring
        _ ≤ (2 : ℝ) * C := mul_le_mul_of_nonneg_left (hcal y hy) (by norm_num)
    _ = (2 : ℝ) * C := by
      rw [← Finset.sum_mul, m.weight_sum]
      ring

end

end PrimeGapNormality.Prime
