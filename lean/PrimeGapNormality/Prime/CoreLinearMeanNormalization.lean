import PrimeGapNormality.Prime.CorePrimeLinearCriterion

/-!
# Normalization of the finite positive linear model mean

`finiteRootMixUnnorm = mixZeta · finiteRootMix`.  This file records the
corresponding exact scalar identity for `coreLinearStoppedMean` and converts
a normalized positive-model estimate with constant `A` into the
unnormalized estimate with constant `2A`, using only `mixZeta → 1` from
Kuperberg.  The normalized finite-model estimate remains an explicit input.
-/

open Filter Finset MeasureTheory
open scoped Classical Topology NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

noncomputable section

private theorem shortShapeMass_const_mul
    (Ω : Finset ℕ) (ν : Finset ℕ → ℝ) (L : ℕ) (c : ℝ) (K : Finset ℕ) :
    Stopped.shortShapeMass Ω (fun U => c * ν U) L K =
      c * Stopped.shortShapeMass Ω ν L K := by
  unfold Stopped.shortShapeMass
  rw [mul_sum]
  apply sum_congr rfl
  intro U _
  split_ifs <;> simp

/-- Scalar linearity in the configuration mass. -/
theorem coreLinearStoppedMean_const_mul
    (B S L : ℕ) (ν : Finset ℕ → ℝ) (c : ℝ)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) :
    coreLinearStoppedMean B S L (fun U => c * ν U) f =
      c * coreLinearStoppedMean B S L ν f := by
  unfold coreLinearStoppedMean
  rw [mul_sum]
  apply sum_congr rfl
  intro K _
  rw [shortShapeMass_const_mul]
  ring

/-- Nonnegativity for a nonnegative test and a nonnegative configuration
mass on the finite window. -/
theorem coreLinearStoppedMean_nonneg
    {B S L : ℕ} {ν : Finset ℕ → ℝ}
    {f : AddCircle (1 : ℝ) →ᵇ ℝ}
    (hν : ∀ U ∈ (Icc 1 S).powerset, 0 ≤ ν U)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ coreLinearStoppedMean B S L ν f := by
  unfold coreLinearStoppedMean
  apply sum_nonneg
  intro K _
  apply mul_nonneg (hf _)
  unfold Stopped.shortShapeMass
  exact sum_nonneg fun U hU => by
    split_ifs
    · exact hν U hU
    · exact le_rfl

private theorem coreLinear_mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos
  · intro t _
    exact eulerProdNat_pos (sieveCutoff (t : ℝ))
  · exact ⟨2 * X, by simp only [mixScale, mem_Ioc]; omega⟩

/-- Exact normalized/unnormalized identity for the finite stopped mean. -/
theorem coreLinearStoppedMean_finiteRootMixUnnorm_eq_mixZeta_mul
    {X : ℕ} (hN : 0 < windowNX X) (hZ : 0 < mixZ X)
    (B S L : ℕ) (f : AddCircle (1 : ℝ) →ᵇ ℝ) :
    coreLinearStoppedMean B S L (finiteRootMixUnnorm X S) f =
      mixZeta X * coreLinearStoppedMean B S L (finiteRootMix X S) f := by
  have hfun : finiteRootMixUnnorm X S =
      fun U => mixZeta X * finiteRootMix X S U := by
    funext U
    exact finiteRootMixUnnorm_eq_mixZeta_mul_finiteRootMix hN hZ S U
  rw [hfun, coreLinearStoppedMean_const_mul]

/-- A normalized positive-model bound is enough for the prime linear
criterion.  The factor two only reflects the eventual bound
`mixZeta X ≤ 2`; normalization is not charged per Janossy term. -/
theorem corePrime_position_weyl_of_kuperberg_and_normalized_model_bound
    {B : ℕ} (hB : 2 ≤ B) (hKuperberg : KuperbergConj13)
    {A : ℝ} (hA : 0 ≤ A)
    (hmodel : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
        coreLinearStoppedMean B (ahlSmall_window (1 / Real.log (B : ℝ)) X)
          (profileL (1 / Real.log (B : ℝ)) X)
          (finiteRootMix X (ahlSmall_window (1 / Real.log (B : ℝ)) X)) f ≤
            A * ∫ x, f x ∂volume + ε) :
    weylCriterion B (primePosSeries B) := by
  refine corePrime_position_weyl_of_kuperberg_and_unnormalized_model_bound
    hB hKuperberg (A := 2 * A) (mul_nonneg (by norm_num) hA) ?_
  intro f K hK hf0 ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hζ := (PrimeCountingNormalization.mixZeta_one_of_kuperberg hKuperberg).eventually_le_const
    (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hmodel f K hK hf0 (ε / 2) hε2, hζ,
    eventually_ge_atTop 1] with X hm hζ2 hX
  have hN := windowNX_pos (by omega : 0 < X)
  have hZ := coreLinear_mixZ_pos hX
  rw [coreLinearStoppedMean_finiteRootMixUnnorm_eq_mixZeta_mul hN hZ]
  have hI : 0 ≤ (∫ x : AddCircle (1 : ℝ), f x ∂volume) := integral_nonneg hf0
  have hmain0 :
      0 ≤ A * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε / 2 :=
    add_nonneg (mul_nonneg hA hI) hε2.le
  calc
    mixZeta X *
        coreLinearStoppedMean B
          (ahlSmall_window (1 / Real.log (B : ℝ)) X)
          (profileL (1 / Real.log (B : ℝ)) X)
          (finiteRootMix X (ahlSmall_window (1 / Real.log (B : ℝ)) X)) f ≤
      mixZeta X * (A * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε / 2) :=
        mul_le_mul_of_nonneg_left hm (crtMixUnnormRem_mixZeta_nonneg X)
    _ ≤ 2 * (A * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε / 2) :=
      mul_le_mul_of_nonneg_right hζ2 hmain0
    _ = (2 * A) * (∫ x : AddCircle (1 : ℝ), f x ∂volume) + ε := by ring

end

end PrimeGapNormality.Prime
