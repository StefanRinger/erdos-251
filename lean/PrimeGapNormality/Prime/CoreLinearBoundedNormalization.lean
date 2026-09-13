import PrimeGapNormality.Prime.CoreLinearMeanNormalization
import PrimeGapNormality.Prime.CoreLinearModelLimit
import PrimeGapNormality.Prime.CorePrimeDensityBounds

/-!
# PNT-free bounded normalization of the positive linear model

The exact identity is unchanged, but the scalar `mixZeta` is bounded by the
unconditional dyadic density theorem rather than shown to converge to one.
Thus a normalized constant `A` becomes `16 A`; no Kuperberg premise occurs.
-/

open Filter Finset MeasureTheory
open scoped Classical Topology NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

noncomputable section

private theorem coreLinearBounded_mixZ_pos {X : ℕ} (hX : 1 ≤ X) :
    0 < mixZ X := by
  unfold mixZ
  apply sum_pos
  · intro t ht
    exact eulerProdNat_pos (sieveCutoff (t : ℝ))
  · exact ⟨2 * X, by simp only [mixScale, mem_Ioc]; omega⟩

/-- Generic conversion of a normalized positive bound into the actual
unnormalized stopped-mean bound.  The supplied profile `κ` is preserved. -/
theorem coreLinearStoppedMean_unnorm_eventually_le_of_normalized
    {B : ℕ} {κ A : ℝ} (hA : 0 ≤ A)
    (hmodel : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
        coreLinearStoppedMean B (ahlSmall_window κ X) (profileL κ X)
          (finiteRootMix X (ahlSmall_window κ X)) f ≤
            A * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε) :
    ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
        coreLinearStoppedMean B (ahlSmall_window κ X) (profileL κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X)) f ≤
            (16 * A) * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε := by
  intro f K hK hf0 ε hε
  have hε16 : 0 < ε / 16 := div_pos hε (by norm_num)
  filter_upwards [hmodel f K hK hf0 (ε / 16) hε16,
    CorePrimeDensity.eventually_mixZeta_le_sixteen,
    CorePrimeDensity.tendsto_windowNX_atTop.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with X hm hζ hN hX
  have hNpos : 0 < windowNX X := by omega
  have hZpos : 0 < mixZ X := coreLinearBounded_mixZ_pos hX
  rw [coreLinearStoppedMean_finiteRootMixUnnorm_eq_mixZeta_mul
    hNpos hZpos]
  have hI : 0 ≤ (∫ x : AddCircle (1 : ℝ), f x ∂volume) :=
    integral_nonneg hf0
  have hmain0 : 0 ≤ A * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε / 16 :=
    add_nonneg (mul_nonneg hA hI) hε16.le
  calc
    mixZeta X *
        coreLinearStoppedMean B (ahlSmall_window κ X) (profileL κ X)
          (finiteRootMix X (ahlSmall_window κ X)) f ≤
      mixZeta X *
        (A * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε / 16) :=
      mul_le_mul_of_nonneg_left hm (crtMixUnnormRem_mixZeta_nonneg X)
    _ ≤ 16 *
        (A * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε / 16) :=
      mul_le_mul_of_nonneg_right hζ hmain0
    _ = (16 * A) * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε := by ring

/-- The unconditional normalized model theorem, converted to the literal
unnormalized finite-root mean for every supplied `κ ≥ 1/log B`. -/
theorem coreLinearFiniteRootMeanUnnorm_eventually_le_volume
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0),
        LipschitzWith K f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
          coreLinearStoppedMean B (ahlSmall_window κ X) (profileL κ X)
            (finiteRootMixUnnorm X (ahlSmall_window κ X)) f ≤
              A * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε := by
  obtain ⟨A, hA, hmodel⟩ :=
    coreLinearFiniteRootMean_eventually_le_volume B hB hκ
  refine ⟨16 * A, mul_nonneg (by norm_num) hA, ?_⟩
  apply coreLinearStoppedMean_unnorm_eventually_le_of_normalized hA
  intro f K hK hf0 ε hε
  simpa only [coreLinearFiniteRootMean, coreLinearStoppedMean, offsetWindow] using
    hmodel f K hK hf0 ε hε

end

end PrimeGapNormality.Prime
