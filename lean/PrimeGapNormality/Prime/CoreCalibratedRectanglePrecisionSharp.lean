import PrimeGapNormality.Prime.CoreCalibratedRectanglePrecision
import PrimeGapNormality.Prime.CoreRectangleMeasureDominationSharp

/-!
# Exact sharp domination for calibrated frame limits

This is the final measure-theoretic wrapper.  The arithmetic module gives
the literal `8^r` open-rectangle estimate for every supplied weak limit;
the sharp coordinate-hull extension converts it to domination by exactly
`8^r` times Lebesgue measure.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedRectanglePrecisionSharp

open Finset Filter MeasureTheory
open CoreCalibratedMixtureFiniteSupport CoreCalibratedFrameProbability
open scoped Classical Topology ENNReal BigOperators

noncomputable section

/-- Every weak limit of the actual calibrated laws, with ranks allowed to
vary deterministically and injectively, is bounded by exactly `8^r` times
Lebesgue measure. -/
theorem weak_limit_le_volume_precision_sharp
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧
      ∀ i, q X i + 1 < M X)
    (theta : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ)))
    (nu : ProbabilityMeasure (CoreCalibratedFrameProbability.Joint r)) (phi : ℕ → ℕ)
    (hphi : Tendsto phi atTop atTop)
    (hweak : Tendsto (fun n => profileLaw G M w q theta O (phi n))
      atTop (nhds nu)) :
    (CoreJointFrameLimit.frameMarginal nu : Measure (Fin r → ℝ)) ≤
      ENNReal.ofReal ((8 : ℝ) ^ r) • volume := by
  apply CoreRectangleMeasureDominationSharp.le_volume_of_open_rectangle_bound_sharp
    (CoreJointFrameLimit.frameMarginal nu : Measure (Fin r → ℝ))
    (pow_pos (by norm_num : (0 : ℝ) < 8) r)
  exact CoreCalibratedRectanglePrecision.weak_limit_open_rectangle_precision
    hG hκ hM hw hsum hcal q hq theta O nu phi hphi hweak

theorem weak_limit_absolutelyContinuous_precision_sharp
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧
      ∀ i, q X i + 1 < M X)
    (theta : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ)))
    (nu : ProbabilityMeasure (CoreCalibratedFrameProbability.Joint r)) (phi : ℕ → ℕ)
    (hphi : Tendsto phi atTop atTop)
    (hweak : Tendsto (fun n => profileLaw G M w q theta O (phi n))
      atTop (nhds nu)) :
    (CoreJointFrameLimit.frameMarginal nu : Measure (Fin r → ℝ)) ≪ volume :=
  Measure.absolutelyContinuous_of_le_smul
    (weak_limit_le_volume_precision_sharp
      hG hκ hM hw hsum hcal q hq theta O nu phi hphi hweak)

end

end PrimeGapNormality.Prime.CoreCalibratedRectanglePrecisionSharp
