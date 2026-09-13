import PrimeGapNormality.Prime.CoreRoughLocalNormality

/-!
# Little-o rough profiles support every fixed algebraic budget

This is the literal adapter for the final assertion following the paper's
rough-range condition.  The hypothesis

`Psi(t) * log (3 * Psi(t)) = o(t)`

together with `Psi(t) -> infinity` supplies `HasSlopeBudget Psi A` for every
fixed positive `A`.  Consequently a single rough sequence can be used for
each separately fixed base, period and local polynomial: the required
`kappa` is chosen inside the theorem from that polynomial's effective degree.

The weighted-derivative regularity used by the genuine rough sieve remains an
explicit input.  No uniformity over a base or polynomial varying with the
limit is asserted.
-/

namespace PrimeGapNormality.Prime.CoreRoughLittleOProfile

open Asymptotics Filter MvPolynomial CoreCyclic
open CoreRoughThreshold CoreRoughSyntheticScale CoreMovingRoughSequence
open scoped Topology Classical

noncomputable section

/-- The paper's literal universal-profile condition.  Divergence is recorded
separately because the little-o relation alone does not imply it. -/
def HasLittleOSlopeProfile (Psi : ℝ → ℝ) : Prop :=
  Tendsto Psi atTop atTop ∧
    (fun t : ℝ => Psi t * Real.log (3 * Psi t)) =o[atTop]
      (fun t : ℝ => t)

/-- A little-o profile satisfies every separately fixed positive slope
budget. -/
theorem HasLittleOSlopeProfile.hasSlopeBudget
    {Psi : ℝ → ℝ} (h : HasLittleOSlopeProfile Psi)
    {A : ℝ} (hA : 0 < A) :
    HasSlopeBudget Psi A := by
  refine ⟨hA, h.1, ?_⟩
  have hbound := h.2.bound (show 0 < 1 / A from one_div_pos.mpr hA)
  filter_upwards [hbound, h.1.eventually_ge_atTop 1,
    eventually_ge_atTop (0 : ℝ)] with t ht hPsi ht0
  have hPsiPos : 0 < Psi t := zero_lt_one.trans_le hPsi
  have hlog : 0 ≤ Real.log (3 * Psi t) := by
    apply Real.log_nonneg
    nlinarith
  have hproduct : 0 ≤ Psi t * Real.log (3 * Psi t) :=
    mul_nonneg hPsiPos.le hlog
  have hraw : Psi t * Real.log (3 * Psi t) ≤ (1 / A) * t := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hproduct,
      abs_of_nonneg ht0] using ht
  have hmul := mul_le_mul_of_nonneg_left hraw hA.le
  have hcost : A * (Psi t * Real.log (3 * Psi t)) ≤ t := by
    calc
      A * (Psi t * Real.log (3 * Psi t)) ≤ A * ((1 / A) * t) := hmul
      _ = t := by field_simp [hA.ne']
  apply (le_div_iff₀ hPsiPos).mpr
  calc
    A * Real.log (3 * Psi t) * Psi t =
        A * (Psi t * Real.log (3 * Psi t)) := by ring
    _ ≤ t := hcost

/-- The same profile supplies all fixed positive constants.  This formulation
makes the paper's quantifier order explicit. -/
theorem HasLittleOSlopeProfile.hasSlopeBudget_all
    {Psi : ℝ → ℝ} (h : HasLittleOSlopeProfile Psi) :
    ∀ A : ℝ, 0 < A → HasSlopeBudget Psi A :=
  fun _ hA => h.hasSlopeBudget hA

/-- Literal local-series classification on the actual moving-rough sequence,
with the effective `kappa` selected internally.  Thus the same `Psi` handles
every base, period and local polynomial fixed before the limiting process.
The derivative hypothesis is the original rough-sieve regularity input. -/
theorem movingRough_local_classification
    {Psi dPsi : ℝ → ℝ} (hLittle : HasLittleOSlopeProfile Psi)
    {C : ℝ} (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Psi dPsi C)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) :
    (normalForm hB hk F = 0 ∧
      ∃ q : ℚ,
        coreCyclicFullSeries B hk phase
            (fun n =>
              (seqGap (movingRoughSequence (zPsi Psi)) n : ℝ)) F =
          (q : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k)
        (coreCyclicFullSeries B hk phase
          (fun n =>
            (seqGap (movingRoughSequence (zPsi Psi)) n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k)
        (coreCyclicFullSeries B hk phase
          (fun n =>
            (seqGap (movingRoughSequence (zPsi Psi)) n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B
        (coreCyclicFullSeries B hk phase
          (fun n =>
            (seqGap (movingRoughSequence (zPsi Psi)) n : ℝ)) F)) := by
  let d : ℕ := topDegree (normalForm hB hk F)
  let kappa : ℝ := max 1 ((d : ℝ) / Real.log (B : ℝ))
  have hkappaPos : 0 < kappa := by
    exact zero_lt_one.trans_le (le_max_left _ _)
  have hdegree : (topDegree (normalForm hB hk F) : ℝ) /
      Real.log (B : ℝ) ≤ kappa := by
    dsimp only [kappa, d]
    exact le_max_right _ _
  have hSlope : HasSlopeBudget Psi (1000000 * kappa) :=
    hLittle.hasSlopeBudget (mul_pos (by norm_num) hkappaPos)
  exact CoreRoughLocalNormality.movingRough_local_classification
    hkappaPos hSlope hC hreg hB hk phase F hdegree

end

end PrimeGapNormality.Prime.CoreRoughLittleOProfile
