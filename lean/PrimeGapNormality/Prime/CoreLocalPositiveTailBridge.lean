import PrimeGapNormality.Prime.CorePrimeLocalPositiveWindow
import PrimeGapNormality.Prime.CoreLocalPolynomialTailAverage
import PrimeGapNormality.Prime.CorePrimeGapTailUnconditional
import PrimeGapNormality.Prime.CorePositiveTail
import PrimeGapNormality.Prime.FractionalTail

/-!
# Bounded Lipschitz restoration of the infinite local phase

The local-polynomial tail theorem controls the physical-window mean of
`min 1 |R|^(1/d)`.  A Lipschitz estimate handles `|R| ≤ 1`, while boundedness
of a continuous test handles the complementary case.  This discharges the
literal phase-test remainder left by `CorePrimeLocalPositiveWindow`, using
the unconditional prime-gap tail convergence and no higher moment.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

noncomputable section

/-- A bounded Lipschitz circle test costs only the bounded `1/d`-root of the
real local-series remainder. -/
theorem localPositiveTest_difference_le_min_root
    {B d k : ℕ} (hd : 1 ≤ d) (hk : 0 < k) (phase : Fin k)
    (g : ℕ → ℝ) (F : PeriodicLocal k)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    (n J : ℕ) :
    |f (coreLocalSeries B hk phase g F n : AddCircle (1 : ℝ)) -
        f (coreLocalSeriesTrunc B hk phase g F n J : AddCircle (1 : ℝ))| ≤
      max (2 * ‖f‖) (K : ℝ) *
        min 1 (|coreLocalSeriesRemainder B hk phase g F n J| ^
          ((1 : ℝ) / (d : ℝ))) := by
  let t : ℝ := coreLocalSeriesTrunc B hk phase g F n J
  let R : ℝ := coreLocalSeriesRemainder B hk phase g F n J
  let fR : ℝ → ℝ := fun x ↦ f (x : AddCircle (1 : ℝ))
  have hsum : t + R = coreLocalSeries B hk phase g F n := by
    dsimp only [t, R]
    unfold coreLocalSeriesRemainder
    ring
  have hbound : ∀ x, |fR x| ≤ ‖f‖ := by
    intro x
    change |f (x : AddCircle (1 : ℝ))| ≤ ‖f‖
    rw [← Real.norm_eq_abs]
    exact f.norm_coe_le_norm _
  have hlip : ∀ x y, |fR x - fR y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    exact corePositiveTest_real_dist_le f hK x y
  have hdirect :
      |f (coreLocalSeries B hk phase g F n : AddCircle (1 : ℝ)) -
          f (coreLocalSeriesTrunc B hk phase g F n J : AddCircle (1 : ℝ))| ≤
        max (2 * ‖f‖) (K : ℝ) * |R| ^ ((1 : ℝ) / (d : ℝ)) := by
    have h := direct_bounded_test_real hd (norm_nonneg f) K.coe_nonneg
      hbound hlip t R
    rw [hsum] at h
    simpa only [fR, t] using h
  have htri :
      |f (coreLocalSeries B hk phase g F n : AddCircle (1 : ℝ)) -
          f (coreLocalSeriesTrunc B hk phase g F n J : AddCircle (1 : ℝ))| ≤
        2 * ‖f‖ := by
    rw [← Real.norm_eq_abs]
    calc
      ‖f (coreLocalSeries B hk phase g F n : AddCircle (1 : ℝ)) -
          f (coreLocalSeriesTrunc B hk phase g F n J : AddCircle (1 : ℝ))‖ ≤
          ‖f (coreLocalSeries B hk phase g F n : AddCircle (1 : ℝ))‖ +
            ‖f (coreLocalSeriesTrunc B hk phase g F n J : AddCircle (1 : ℝ))‖ :=
        norm_sub_le _ _
      _ ≤ ‖f‖ + ‖f‖ :=
        add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
      _ = 2 * ‖f‖ := by ring
  let root : ℝ := |R| ^ ((1 : ℝ) / (d : ℝ))
  by_cases hroot : root ≤ 1
  · rw [tailMin_eq_t hroot]
    simpa only [root, R] using hdirect
  · have hroot' : 1 ≤ root := le_of_not_ge hroot
    rw [tailMin_eq_one hroot', mul_one]
    exact htri.trans (le_max_left _ _)

/-- On actual prime windows, the bounded Lipschitz phase-test remainder
between the infinite local series and its first `L-w` emissions tends to
zero.  The profile is the genuine `stdProfileL rho windowG`; choosing the
critical base with `rho^d = B` gives the `d / log B` endpoint downstream. -/
theorem tendsto_primeGap_localPositiveTestRemainder_zero
    {B d : ℕ} {rho : ℝ} (hB : 2 ≤ B) (hrho : 1 < rho)
    (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k)
    (w : ℕ) (hd : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hdeg : ∀ s, (F s).totalDegree ≤ d)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    Tendsto (fun X : ℕ ↦
      windowAvgReal (seqWindow nthPrime X) (fun n ↦
        |f (coreLocalSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F n :
              AddCircle (1 : ℝ)) -
          f (coreLocalSeriesTrunc B hk phase (fun q ↦ (primeGap q : ℝ)) F n
              (stdProfileL rho (windowG X) - w) : AddCircle (1 : ℝ))|))
      atTop (𝓝 0) := by
  let A : ℝ := max (2 * ‖f‖) (K : ℝ)
  have hA : 0 ≤ A :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg f)).trans
      (le_max_left _ _)
  have hroot := tendsto_primeGap_localTailRootMean_zero hB hbase hk phase F w
    hd hw hdeg
    (CorePrimeGapTailUnconditional.gapTailT_nthPrime_windowG hrho)
  have hmajor := hroot.const_mul A
  simp only [mul_zero] at hmajor
  apply squeeze_zero' _ _ hmajor
  · exact Eventually.of_forall fun X ↦
      div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (Nat.cast_nonneg _)
  · exact Eventually.of_forall fun X ↦ by
      have hsum := sum_le_sum fun n (_ : n ∈ seqWindow nthPrime X) ↦
        localPositiveTest_difference_le_min_root (B := B) hd hk phase
          (fun q ↦ (primeGap q : ℝ)) F f hK n
          (stdProfileL rho (windowG X) - w)
      unfold windowAvgReal
      rw [← mul_div_assoc, mul_sum]
      exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

end

end PrimeGapNormality.Prime.CoreCyclic
