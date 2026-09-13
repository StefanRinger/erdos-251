import PrimeGapNormality.Prime.CoreLocalModelIdentification
import PrimeGapNormality.Prime.CoreLocalTailAtProfile
import PrimeGapNormality.Prime.CorePrimeNormalityOfD
import PrimeGapNormality.Prime.CoreResidueSubsequenceReference

/-! Arithmetic assembly for local polynomials. This is an intermediate
consumer: its explicit normalized model-reference bound must still be
proved from the actual resampling law. D, calibration and tails are never
replaced by an assumed prime Fourier estimate. -/

namespace PrimeGapNormality.Prime
open Finset Filter MeasureTheory
open scoped Classical Topology NNReal BoundedContinuousFunction
noncomputable section

private theorem coreLocal_mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos
  · intro t _
    exact eulerProdNat_pos (sieveCutoff (t : ℝ))
  · exact ⟨2 * X, by simp only [mixScale, mem_Ioc]; omega⟩

/-- Positive reference domination transfers along any diverging physical
subsequence. The parameter κ, width and actual D budget are unchanged. -/
theorem coreLocal_positive_reference_of_D_and_model
    {B d k : ℕ} (hB : 2 ≤ B) (hd : 1 ≤ d) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) (w : ℕ)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hdeg : ∀ s, (F s).totalDegree ≤ d)
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c)
    (Y : ℕ → ℕ) (hY : Tendsto Y atTop atTop)
    (σ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure σ]
    {A : ℝ} (hA : 0 ≤ A)
    (hmodel : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        coreLocalStoppedMean B (ahlSmall_window κ (Y n)) (profileL κ (Y n)) w
          hk phase F (finiteRootMix (Y n) (ahlSmall_window κ (Y n))) f ≤
            A * (∫ x, f x ∂σ) + ε) :
    ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        coreDigitalWindowAverage
          (CoreCyclic.coreLocalSeriesCircle B hk phase (fun q ↦ (primeGap q : ℝ)) F)
          f (Nat.primeCounting (Y n)) (windowNX (Y n)) ≤
            (16 * c * A) * (∫ x, f x ∂σ) + ε := by
  have hκpos : 0 < κ :=
    (div_pos (by exact_mod_cast (show 0 < d by omega))
      (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  intro f K hK hf0 ε hε
  let C : ℝ := ‖f‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hfC (x : AddCircle (1 : ℝ)) : f x ≤ C := by
    exact (f.apply_le_norm x).trans (le_add_of_nonneg_right zero_le_one)
  let R : ℕ → ℝ := fun X ↦
    windowAvgReal (seqWindow nthPrime X) (fun q ↦
      |f (CoreCyclic.coreLocalSeries B hk phase (fun t ↦ (primeGap t : ℝ)) F q :
          AddCircle (1 : ℝ)) -
        f (CoreCyclic.coreLocalSeriesTrunc B hk phase (fun t ↦ (primeGap t : ℝ)) F q
          (profileL κ X - w) : AddCircle (1 : ℝ))|)
  have hR : Tendsto R atTop (𝓝 0) :=
    CoreCyclic.tendsto_primeGap_localPositiveTestRemainder_profileL_zero
      hB hd hκ hk phase F w hw hdeg f hK
  let E : ℕ → ℝ := fun X ↦ C *
    (corePrimeComparisonQuantity X (ahlSmall_omega κ X) (profileL κ X)
      (profileR (profileL κ X) d0) c + c * coreMixtureJanossyCalibration κ d0 X) + R X
  have hE : Tendsto E atTop (𝓝 0) := by
    have hcal := (CoreCalibrationUnconditional.tendsto_calibration hκpos hd0).const_mul c
    simp only [mul_zero] at hcal
    have h := (hD.add hcal).const_mul C
    simpa only [E, add_zero, mul_zero] using h.add hR
  have hsmall : 0 < ε / (32 * c) := div_pos hε (mul_pos (by norm_num) hcpos)
  filter_upwards [hY.eventually (eventually_ge_atTop 1),
    hY.eventually ((tendsto_profileL_atTop hκpos).eventually_ge_atTop (w + 1)),
    hY.eventually CorePrimeDensity.eventually_mixZeta_le_sixteen,
    (hE.comp hY).eventually (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε)),
    hmodel f K hK hf0 (ε / (32 * c)) hsmall] with n hX hL hζ he hm
  have hN : 0 < windowNX (Y n) := windowNX_pos (by omega)
  have hZ : 0 < mixZ (Y n) := coreLocal_mixZ_pos hX
  have hfull := corePrime_localFull_positive_window_le_comparisonQuantity
    (B := B) (X := Y n) (S := ahlSmall_window κ (Y n))
    (ν := finiteRootMixUnnorm (Y n) (ahlSmall_window κ (Y n)))
    hk phase F (by omega : w ≤ profileL κ (Y n)) hw hN (by omega)
    (crtMixProf_le_at κ d0 (Y n)) (crtMixProf_odd_at κ d0 (Y n))
    hcpos.le hC (fun U _ ↦ crtMixUnnorm_finiteRootMixUnnorm_nonneg _ _ U) f hf0 hfC
  have hfull' :
      windowAvgReal (seqWindow nthPrime (Y n)) (fun q ↦
        f (CoreCyclic.coreLocalSeries B hk phase (fun t ↦ (primeGap t : ℝ)) F q :
          AddCircle (1 : ℝ))) ≤
      c * coreLocalStoppedMean B (ahlSmall_window κ (Y n)) (profileL κ (Y n)) w
        hk phase F (finiteRootMixUnnorm (Y n) (ahlSmall_window κ (Y n))) f + E (Y n) := by
    simpa only [coreLocalStoppedMean, E, R, coreMixtureJanossyCalibration,
      ahlSmall_omega, offsetWindow, add_assoc] using hfull
  rw [coreLocalStoppedMean_unnormalized_eq B (Y n) _ _ w hk phase F f hN hZ] at hfull'
  have hI : 0 ≤ ∫ x, f x ∂σ := integral_nonneg hf0
  have hmain0 : 0 ≤ A * (∫ x, f x ∂σ) + ε / (32 * c) :=
    add_nonneg (mul_nonneg hA hI) hsmall.le
  have hbound :
      mixZeta (Y n) * coreLocalStoppedMean B (ahlSmall_window κ (Y n)) (profileL κ (Y n)) w
        hk phase F (finiteRootMix (Y n) (ahlSmall_window κ (Y n))) f ≤
      16 * (A * (∫ x, f x ∂σ) + ε / (32 * c)) :=
    (mul_le_mul_of_nonneg_left hm (crtMixUnnormRem_mixZeta_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hζ hmain0)
  have he' : E (Y n) ≤ ε / 2 := by
    have habs : |E (Y n) - 0| < ε / 2 := he
    rw [sub_zero] at habs
    exact (le_abs_self _).trans habs.le
  have heps : c * (16 * (ε / (32 * c))) = ε / 2 := by field_simp [hcpos.ne'] <;> ring
  have hmc := mul_le_mul_of_nonneg_left hbound hcpos.le
  rw [mul_add, mul_add, heps] at hmc
  have hfinal := hfull'.trans (add_le_add hmc he')
  rw [corePrime_window_positive_average_eq] at hfinal
  change coreDigitalWindowAverage
    (fun q ↦ (CoreCyclic.coreLocalSeries B hk phase (fun t ↦ (primeGap t : ℝ)) F q :
      AddCircle (1 : ℝ))) f (Nat.primeCounting (Y n)) (windowNX (Y n)) ≤ _
  exact hfinal.trans_eq (by ring)

end
end PrimeGapNormality.Prime
