import PrimeGapNormality.Prime.CoreAuxiliaryFrameMass
import PrimeGapNormality.Prime.CoreFiniteRootMixUpperException
import PrimeGapNormality.Prime.AuxThetaBound

/-!
# Positive-test auxiliary-frame assembly

This file starts the nonlinear finite-model assembly with the exact
fixed-rank erase/insert identity for an arbitrary nonnegative configuration
test.  On a good cardinality layer, any pointwise bound for the undivided
slot insertion sum is transported to the uniform deleted-frame law with the
proved coefficient `n / (M - n + 1) ≤ 4 * θ`.

No abstract probability distribution is introduced: all means below are the
literal uniform exact-cardinality means used by `coreAuxiliaryLayerFrameMass`.
-/

open Finset
open scoped BigOperators Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-- Monotonicity of the literal uniform exact-cardinality mean. -/
theorem corePositive_auxFrame_uniformMean_mono
    (A : Finset ℕ) (m : ℕ) {f g : Finset ℕ → ℝ}
    (hfg : ∀ F ∈ A.powersetCard m, f F ≤ g F) :
    auxFrame_uniformMean A m f ≤ auxFrame_uniformMean A m g := by
  unfold auxFrame_uniformMean
  exact div_le_div_of_nonneg_right (sum_le_sum hfg) (Nat.cast_nonneg _)

/-- Exact fixed-rank disintegration of an arbitrary nonnegative test.
The inner slot sum is deliberately not divided by the slot cardinality. -/
theorem corePositive_uniformMean_eq_frameMean
    (A : Finset ℕ) (n j : ℕ) (test : Finset ℕ → ℝ)
    (hn : 1 ≤ n) (hnM : n ≤ A.card) (hj : j + 1 < n)
    (hpos : ∀ x ∈ A, 0 < x) (htest0 : ∀ U, 0 ≤ test U) :
    auxFrame_uniformMean A n test =
      (n : ℝ) / ((A.card : ℝ) - n + 1) *
        auxFrame_uniformMean A (n - 1)
          (auxFrame_slotInsertSum A j test) := by
  rw [auxFrame_uniformMean_eq test hn hnM hj hpos htest0]
  unfold auxFrame_uniformMean
  ring

/-- The same exact disintegration with the original cardinality-layer
weight kept outside. -/
theorem corePositive_cardinalityLayer_eq_frameMean
    (A : Finset ℕ) (μ : Finset ℕ → ℝ) (n j : ℕ)
    (test : Finset ℕ → ℝ)
    (hn : 1 ≤ n) (hnM : n ≤ A.card) (hj : j + 1 < n)
    (hpos : ∀ x ∈ A, 0 < x) (htest0 : ∀ U, 0 ≤ test U) :
    cardinalityLayer A μ n * auxFrame_uniformMean A n test =
      cardinalityLayer A μ n *
        ((n : ℝ) / ((A.card : ℝ) - n + 1) *
          auxFrame_uniformMean A (n - 1)
            (auxFrame_slotInsertSum A j test)) := by
  rw [corePositive_uniformMean_eq_frameMean A n j test
    hn hnM hj hpos htest0]

private theorem corePositive_cardinalityLayer_nonneg
    {A : Finset ℕ} {μ : Finset ℕ → ℝ}
    (hμ : CardinalitySymmetricMass A μ) (n : ℕ) :
    0 ≤ cardinalityLayer A μ n := by
  unfold cardinalityLayer
  exact sum_nonneg fun U hU ↦ hμ.1 U (mem_filter.mp hU).1

/-- A good exact-cardinality layer is bounded by the same original layer
weight times `4θ` and the uniform deleted-frame mean of any nonnegative
slot-sum majorant.  The cutoff represented by `frameBound F` depends only
on the deleted frame, hence is constant throughout each insertion fibre. -/
theorem corePositive_goodLayer_le_frameBound
    (A : Finset ℕ) (μ : Finset ℕ → ℝ) (n j : ℕ)
    (test frameBound : Finset ℕ → ℝ) {θ : ℝ}
    (hμ : CardinalitySymmetricMass A μ)
    (hn : 1 ≤ n) (hnM : n ≤ A.card) (hj : j + 1 < n)
    (hpos : ∀ x ∈ A, 0 < x)
    (htest0 : ∀ U, 0 ≤ test U)
    (hframe0 : ∀ F, 0 ≤ frameBound F)
    (hslot : ∀ F ∈ A.powersetCard (n - 1),
      auxFrame_slotInsertSum A j test F ≤ frameBound F)
    (hcount : (n : ℝ) ≤ 2 * (A.card : ℝ) * θ)
    (hθ : 0 < θ) (hθ4 : θ ≤ (1 : ℝ) / 4) :
    cardinalityLayer A μ n * auxFrame_uniformMean A n test ≤
      cardinalityLayer A μ n *
        ((4 : ℝ) * θ * auxFrame_uniformMean A (n - 1) frameBound) := by
  have hmean := corePositive_auxFrame_uniformMean_mono A (n - 1) hslot
  have hmean0 : 0 ≤ auxFrame_uniformMean A (n - 1) frameBound :=
    auxFrame_uniformMean_nonneg hframe0
  have hcoef0 : 0 ≤ (n : ℝ) / ((A.card : ℝ) - n + 1) := by
    apply div_nonneg (Nat.cast_nonneg _)
    rw [← auxFrame_cast_sub hnM]
    positivity
  have hcoef : (n : ℝ) / ((A.card : ℝ) - n + 1) ≤ (4 : ℝ) * θ :=
    auxTheta_ratio_le_four_theta_nat (by omega) hnM hcount hθ hθ4
  have hlayer0 := corePositive_cardinalityLayer_nonneg hμ n
  rw [corePositive_uniformMean_eq_frameMean A n j test
    hn hnM hj hpos htest0]
  apply mul_le_mul_of_nonneg_left _ hlayer0
  exact (mul_le_mul_of_nonneg_left hmean hcoef0).trans
    (mul_le_mul_of_nonneg_right hcoef hmean0)

end

end PrimeGapNormality.Prime
