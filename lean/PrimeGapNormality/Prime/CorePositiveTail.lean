import PrimeGapNormality.Prime.CoreLinearShapePhase
import PrimeGapNormality.Prime.CoreDigitalLipschitz
import PrimeGapNormality.Prime.GapTailLogKuperberg

/-! Positive Lipschitz tail restoration on the original physical window.
The only analytic supplier below is the existing first-gap mean theorem;
its prime specialization is discharged from Kuperberg, not postulated.
-/

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

theorem coreCircle_dist_coe_le (x y : ℝ) :
    dist (x : AddCircle (1 : ℝ)) (y : AddCircle (1 : ℝ)) ≤ |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem corePositiveTest_real_dist_le
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    (x y : ℝ) :
    |f (x : AddCircle (1 : ℝ)) - f (y : AddCircle (1 : ℝ))| ≤ K * |x - y| := by
  have h := hK.dist_le_mul (x : AddCircle (1 : ℝ)) (y : AddCircle (1 : ℝ))
  rw [Real.dist_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (coreCircle_dist_coe_le x y) K.coe_nonneg)

theorem corePositiveTest_tail_le
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} (hB : 2 ≤ B)
    (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hsm : Summable fun n : ℕ => (a n : ℝ) / ρ ^ n)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    (n L : ℕ) :
    |f (seqGapPolyTail a (fun _ => Polynomial.X) B n : AddCircle (1 : ℝ)) -
      f (seqGapPolyTailTrunc a (fun _ => Polynomial.X) B L n : AddCircle (1 : ℝ))| ≤
      K * scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L := by
  exact (corePositiveTest_real_dist_le f hK _ _).trans
    (mul_le_mul_of_nonneg_left
      (abs_seqGapPolyTail_sub_trunc_le_scaledGapTail hB hρ hρB
        (summable_seqGap_div_base hρ hB hρB hsm n)
        (summable_seqGap_div_pow hρ hsm (n + L))) K.coe_nonneg)

theorem corePositiveTest_tail_window_tendsto
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hB : 2 ≤ B) (hρB : ρ ≤ (B : ℝ)) (hT : GapTailT a ρ G)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    Tendsto (fun X : ℕ => windowAvgReal (seqWindow a X) (fun n =>
      |f (seqGapPolyTail a (fun _ => Polynomial.X) B n : AddCircle (1 : ℝ)) -
       f (seqGapPolyTailTrunc a (fun _ => Polynomial.X) B
         (stdProfileL ρ (G X)) n : AddCircle (1 : ℝ))|)) atTop (𝓝 0) := by
  have hr := tendsto_scaledGapTail_avg_of_GapTailT hT
  have hmaj := hr.const_mul (K : ℝ)
  simp only [mul_zero] at hmaj
  apply squeeze_zero' _ _ hmaj
  · exact Eventually.of_forall fun X =>
      div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg _)
  · apply Eventually.of_forall
    intro X
    have hsum := sum_le_sum fun n (_ : n ∈ seqWindow a X) =>
      corePositiveTest_tail_le hB hT.1 hρB hT.2.2.1 f hK n (stdProfileL ρ (G X))
    unfold windowAvgReal
    rw [← mul_div_assoc, mul_sum]
    exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

theorem corePrime_positive_tail_window_tendsto
    {B : ℕ} {ρ : ℝ} (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hKuperberg : KuperbergConj13)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    Tendsto (fun X : ℕ => windowAvgReal (seqWindow nthPrime X) (fun n =>
      |f (seqGapPolyTail nthPrime (fun _ => Polynomial.X) B n : AddCircle (1 : ℝ)) -
       f (seqGapPolyTailTrunc nthPrime (fun _ => Polynomial.X) B
         (stdProfileL ρ (windowG X)) n : AddCircle (1 : ℝ))|)) atTop (𝓝 0) :=
  corePositiveTest_tail_window_tendsto hB hρB
    (gapTailT_nthPrime_windowG_of_kuperberg hρ hKuperberg) f hK

end PrimeGapNormality.Prime
