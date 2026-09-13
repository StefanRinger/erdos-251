import PrimeGapNormality.Prime.CorePrimePositiveWindow
import PrimeGapNormality.Prime.CoreKuperbergComparison
import PrimeGapNormality.Prime.CoreLinearCriticalRank

/-! Last linear assembly after the positive model estimate. The displayed
model premise is the remaining supplier being implemented in
`CoreLinearModelMean`; it is not an extra allowed hypothesis of the intended
prime end theorem. All arithmetic comparison and tail premises are proved
here from the literal Kuperberg input. -/

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

noncomputable def coreLinearStoppedMean (B S L : ℕ) (ν : Finset ℕ → ℝ)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) : ℝ :=
  ∑ U ∈ (Icc 1 S).powerset.filter (fun U => U.card = L),
    f (coreLinearShapePhase B L U : AddCircle (1 : ℝ)) *
      Stopped.shortShapeMass (Icc 1 S) ν L U

theorem corePrime_position_weyl_of_kuperberg_and_unnormalized_model_bound
    {B : ℕ} (hB : 2 ≤ B) (hKuperberg : KuperbergConj13)
    {A : ℝ} (hA : 0 ≤ A)
    (hmodel : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
        coreLinearStoppedMean B (ahlSmall_window (1 / Real.log (B : ℝ)) X)
          (profileL (1 / Real.log (B : ℝ)) X)
          (finiteRootMixUnnorm X (ahlSmall_window (1 / Real.log (B : ℝ)) X)) f ≤
            A * ∫ x, f x ∂volume + ε) :
    weylCriterion B (primePosSeries B) := by
  let κ : ℝ := 1 / Real.log (B : ℝ)
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hκ : 0 < κ := div_pos zero_lt_one (Real.log_pos hBr)
  have hLstd (X : ℕ) : profileL κ X = stdProfileL (B : ℝ) (windowG X) := by
    exact (CoreLinearInsertion.stdProfileL_eq_linearProfileL (B : ℝ) (windowG X)).symm
  apply corePrime_position_weyl_of_positive_window_bounds hB hKuperberg hA
  intro f K hK hf0 ε hε
  let C : ℝ := ‖f‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hfC (x : AddCircle (1 : ℝ)) : f x ≤ C := by
    exact (le_abs_self _).trans ((f.norm_coe_le_norm x).trans
      (le_add_of_nonneg_right zero_le_one))
  let R : ℕ → ℝ := fun X => windowAvgReal (seqWindow nthPrime X) (fun n =>
    |f (corePrimeGapCircleOrbit B n) -
      f (seqGapPolyTailTrunc nthPrime (fun _ => Polynomial.X) B (profileL κ X) n :
        AddCircle (1 : ℝ))|)
  have hR : Tendsto R atTop (𝓝 0) := by
    simpa only [R, corePrimeGapCircleOrbit, hLstd] using
      corePrime_positive_tail_window_tendsto hB hBr le_rfl hKuperberg f hK
  let E : ℕ → ℝ := fun X => C *
    (corePrimeComparisonQuantity X (ahlSmall_omega κ X) (profileL κ X)
      (profileR (profileL κ X) 20) 1 + coreMixtureJanossyCalibration κ 20 X) + R X
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := ((tendsto_corePrimeComparisonQuantity_small_of_kuperberg hKuperberg hκ).add
      (tendsto_coreMixtureJanossyCalibration_of_kuperberg hKuperberg hκ
        (by norm_num : (0 : ℝ) < 20))).const_mul C
    simpa only [E, add_zero, mul_zero] using h.add hR
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [eventually_ge_atTop 1, eventually_one_le_profileL hκ,
    hmodel f K hK hf0 (ε / 2) hε2,
    hE.eventually (Metric.ball_mem_nhds (0 : ℝ) hε2)] with X hX hL hm he
  have hN := windowNX_pos (by omega : 0 < X)
  have hfull := corePrime_full_positive_window_le_comparisonQuantity
    (B := B) (X := X) (S := ahlSmall_window κ X)
    (ν := finiteRootMixUnnorm X (ahlSmall_window κ X))
    hN hL (crtMixProf_le_at κ 20 X) (crtMixProf_odd_at κ 20 X)
    (by norm_num : (0 : ℝ) ≤ 1) hC
    (fun U _ => crtMixUnnorm_finiteRootMixUnnorm_nonneg X _ U) f hf0 hfC
  have he' : E X ≤ ε / 2 := by
    have habs : |E X - 0| < ε / 2 := he
    rw [sub_zero] at habs
    exact (le_abs_self _).trans habs.le
  have hfull' :
      windowAvgReal (seqWindow nthPrime X) (fun n => f (corePrimeGapCircleOrbit B n)) ≤
        coreLinearStoppedMean B (ahlSmall_window κ X) (profileL κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X)) f + E X := by
    simpa only [coreLinearStoppedMean, E, R, coreMixtureJanossyCalibration,
      ahlSmall_omega, one_mul, add_assoc] using hfull
  change coreLinearStoppedMean B (ahlSmall_window κ X) (profileL κ X)
      (finiteRootMixUnnorm X (ahlSmall_window κ X)) f ≤
        A * ∫ x, f x ∂volume + ε / 2 at hm
  linarith

end PrimeGapNormality.Prime
