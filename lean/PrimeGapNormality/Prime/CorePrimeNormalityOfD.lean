import PrimeGapNormality.Prime.CorePrimeDigitalUnconditional
import PrimeGapNormality.Prime.CorePrimeGapTailUnconditional
import PrimeGapNormality.Prime.CoreMixtureCalibrationUnconditional
import PrimeGapNormality.Prime.CoreLinearBoundedNormalization
import PrimeGapNormality.Prime.CoreWeylNormality

/-!
# The actual one-sided D input suffices for the linear prime theorem

The original profile κ is retained. Neither PNT nor Kuperberg is an
extra premise: density, calibration, tail and positive model domination
are proved independently. D is the actual stopped-count error expression,
not a model-cancellation hypothesis.
-/

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace PrimeGapNormality.Prime

def CoreLinearD (κ d0 c : ℝ) : Prop :=
  Tendsto (fun X : ℕ =>
    corePrimeComparisonQuantity X (ahlSmall_omega κ X) (profileL κ X)
      (profileR (profileL κ X) d0) c) atTop (nhds 0)

/-- The literature hypothesis is one sufficient supplier, not a hidden
argument of the weaker-input endpoint. -/
theorem coreLinearD_of_kuperberg (hK : KuperbergConj13) {κ : ℝ} (hκ : 0 < κ) :
    CoreLinearD κ 20 1 :=
  tendsto_corePrimeComparisonQuantity_small_of_kuperberg hK hκ

theorem corePrime_position_weyl_of_D
    {B : ℕ} (hB : 2 ≤ B) {κ d0 c : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hd0 : 0 < d0)
    (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    weylCriterion B (primePosSeries B) := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos hBr
  have hκpos : 0 < κ := (div_pos zero_lt_one hlogB).trans_le hκ
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  let ρ : ℝ := Real.exp (1 / κ)
  have hρ : 1 < ρ := by
    dsimp only [ρ]
    exact Real.one_lt_exp_iff.mpr (div_pos zero_lt_one hκpos)
  have hρκ : 1 / Real.log ρ = κ := by
    dsimp only [ρ]
    rw [Real.log_exp]
    field_simp [hκpos.ne']
  have hρB : ρ ≤ (B : ℝ) := by
    have hmul : 1 ≤ κ * Real.log (B : ℝ) := (div_le_iff₀ hlogB).mp hκ
    have hquot : 1 / κ ≤ Real.log (B : ℝ) :=
      (div_le_iff₀ hκpos).mpr (by nlinarith)
    calc
      ρ ≤ Real.exp (Real.log (B : ℝ)) := Real.exp_le_exp.mpr hquot
      _ = (B : ℝ) := Real.exp_log (zero_lt_one.trans hBr)
  have hLstd (X : ℕ) : profileL κ X = stdProfileL ρ (windowG X) := by
    rw [CoreLinearInsertion.stdProfileL_eq_linearProfileL, hρκ]
    rfl
  obtain ⟨A, hA, hmodel⟩ :=
    coreLinearFiniteRootMeanUnnorm_eventually_le_volume B hB hκ
  apply corePrime_position_weyl_of_positive_bounds hB (mul_nonneg hcpos.le hA)
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
      corePositiveTest_tail_window_tendsto hB hρB
        (CorePrimeGapTailUnconditional.gapTailT_nthPrime_windowG hρ) f hK
  let E : ℕ → ℝ := fun X => C *
    (corePrimeComparisonQuantity X (ahlSmall_omega κ X) (profileL κ X)
      (profileR (profileL κ X) d0) c + c * coreMixtureJanossyCalibration κ d0 X) + R X
  have hE : Tendsto E atTop (𝓝 0) := by
    have hcal := (CoreCalibrationUnconditional.tendsto_calibration hκpos hd0).const_mul c
    simp only [mul_zero] at hcal
    have h := (hD.add hcal).const_mul C
    simpa only [E, add_zero, mul_zero] using h.add hR
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [eventually_ge_atTop 1, eventually_one_le_profileL hκpos,
    hmodel f K hK hf0 (ε / (2 * c)) (div_pos hε (mul_pos (by norm_num) hcpos)),
    hE.eventually (Metric.ball_mem_nhds (0 : ℝ) hε2)] with X hX hL hm he
  have hN := windowNX_pos (by omega : 0 < X)
  have hfull := corePrime_full_positive_window_le_comparisonQuantity
    (B := B) (X := X) (S := ahlSmall_window κ X)
    (ν := finiteRootMixUnnorm X (ahlSmall_window κ X))
    hN hL (crtMixProf_le_at κ d0 X) (crtMixProf_odd_at κ d0 X)
    hcpos.le hC
    (fun U _ => crtMixUnnorm_finiteRootMixUnnorm_nonneg X _ U) f hf0 hfC
  have he' : E X ≤ ε / 2 := by
    have habs : |E X - 0| < ε / 2 := he
    rw [sub_zero] at habs
    exact (le_abs_self _).trans habs.le
  have hfull' :
      windowAvgReal (seqWindow nthPrime X) (fun n => f (corePrimeGapCircleOrbit B n)) ≤
        c * coreLinearStoppedMean B (ahlSmall_window κ X) (profileL κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X)) f + E X := by
    simpa only [coreLinearStoppedMean, E, R, coreMixtureJanossyCalibration,
      ahlSmall_omega, add_assoc] using hfull
  change coreLinearStoppedMean B (ahlSmall_window κ X) (profileL κ X)
      (finiteRootMixUnnorm X (ahlSmall_window κ X)) f ≤
        A * ∫ x, f x ∂volume + ε / (2 * c) at hm
  have hmc := mul_le_mul_of_nonneg_left hm hcpos.le
  have heps : c * (ε / (2 * c)) = ε / 2 := by field_simp [hcpos.ne']
  rw [mul_add, heps] at hmc
  nlinarith

theorem corePrime_position_isNormal_of_D
    {B : ℕ} (hB : 2 ≤ B) {κ d0 c : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hd0 : 0 < d0)
    (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    PrimeGapNormality.BFree.IsNormal B (primePosSeries B) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (corePrime_position_weyl_of_D hB hκ hd0 hc hD)

theorem corePrime_position_irrational_of_D
    {B : ℕ} (hB : 2 ≤ B) {κ d0 c : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hd0 : 0 < d0)
    (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) : Irrational (primePosSeries B) :=
  weylCriterion_irrational (corePrime_position_weyl_of_D hB hκ hd0 hc hD)

end PrimeGapNormality.Prime
