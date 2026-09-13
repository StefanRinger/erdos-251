import PrimeGapNormality.Prime.CoreLocalPositiveTailBridge
import PrimeGapNormality.Prime.CoreSequenceResiduePassage
import PrimeGapNormality.Prime.FreqBoostAvg

/-!
# Local-polynomial tails for an arbitrary increasing sequence

This is the sequence-generic form of the rooted local tail argument.  Its
only sequence inputs are strict monotonicity, divergence of the physical
window count, polynomial growth of the actual real gap sequence, and the
literal `GapTailT` bound.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Filter Finset MvPolynomial
open scoped BigOperators Topology NNReal BoundedContinuousFunction

noncomputable section

private theorem sequenceGap_one_le {a : ℕ → ℕ} (ha : StrictMono a) (n : ℕ) :
    1 ≤ seqGap a n := by
  unfold seqGap
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.sub_ne_zero_of_lt (ha (Nat.lt_succ_self n)))

private theorem freqBoost_avg_ofReal_sequence (I : Finset ℕ) (f : ℕ → ℝ) :
    freqBoost_avg I (fun n ↦ (f n : ℂ)) = (windowAvgReal I f : ℂ) := by
  unfold freqBoost_avg windowAvgReal
  rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

private theorem windowAvgReal_shift_le_Ico_sequence
    {a b : ℕ} (hab : a < b) (f : ℕ → ℝ) (w : ℕ)
    (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1) :
    windowAvgReal (Ico a b) f ≤
      windowAvgReal (Ico a b) (fun n ↦ f (n + w)) +
        2 * (w : ℝ) / (Ico a b).card := by
  let fc : ℕ → ℂ := fun n ↦ (f n : ℂ)
  have hfc : ∀ n, ‖fc n‖ ≤ 1 := by
    intro n
    simp only [fc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 n)]
    exact hf1 n
  have hshift := freqBoost_shift_avg_norm_le_Ico hab fc w hfc
  rw [freqBoost_avg_ofReal_sequence, freqBoost_avg_ofReal_sequence] at hshift
  have habs :
      |windowAvgReal (Ico a b) (fun n ↦ f (n + w)) -
        windowAvgReal (Ico a b) f| ≤
          2 * (w : ℝ) / (Ico a b).card := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hshift
  linarith [neg_abs_le
    (windowAvgReal (Ico a b) (fun n ↦ f (n + w)) -
      windowAvgReal (Ico a b) f)]

private theorem windowAvgReal_nonneg_sequence (I : Finset ℕ) {f : ℕ → ℝ}
    (hf : ∀ n ∈ I, 0 ≤ f n) : 0 ≤ windowAvgReal I f := by
  unfold windowAvgReal
  exact div_nonneg (sum_nonneg hf) (Nat.cast_nonneg _)

private theorem windowAvgReal_mono_sequence (I : Finset ℕ) {f g : ℕ → ℝ}
    (hfg : ∀ n ∈ I, f n ≤ g n) :
    windowAvgReal I f ≤ windowAvgReal I g := by
  unfold windowAvgReal
  exact div_le_div_of_nonneg_right (sum_le_sum hfg) (Nat.cast_nonneg _)

private theorem windowAvgReal_const_mul_sequence (I : Finset ℕ) (c : ℝ)
    (f : ℕ → ℝ) :
    windowAvgReal I (fun n ↦ c * f n) = c * windowAvgReal I f := by
  unfold windowAvgReal
  rw [← Finset.mul_sum]
  ring

/-- The bounded `1/d`-root local-tail mean tends to zero for any actual
strictly increasing sequence satisfying the stated tail and growth inputs.
The truncation is exactly `L-w`; the only finite shift is paid after
applying `min 1`. -/
theorem tendsto_sequence_localTailRootMean_zero
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B d : ℕ} {rho : ℝ} (hB : 2 ≤ B) (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k)
    (w : ℕ) (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hgrowth : HasPolynomialGrowth (fun q ↦ (seqGap a q : ℝ)))
    {G : ℕ → ℝ} (hT : GapTailT a rho G) :
    Tendsto (fun X : ℕ ↦
      windowAvgReal (seqWindow a X) (fun n ↦
        min 1 (|coreLocalSeriesRemainder B hk phase
          (fun q ↦ (seqGap a q : ℝ)) F n
          (stdProfileL rho (G X) - w)| ^ ((1 : ℝ) / (d : ℝ)))))
      atTop (nhds 0) := by
  rcases hT with ⟨hrho, hG, hsm, C, hC, hTail⟩
  let A : ℝ := localTailRootConst (d := d) F *
    (∑ i ∈ range (w + 1), rho ^ i)
  have hA : 0 ≤ A := mul_nonneg (localTailRootConst_nonneg F)
    (sum_nonneg fun i _ ↦ pow_nonneg (zero_lt_one.trans hrho).le _)
  have hL : ∀ᶠ X : ℕ in atTop, w ≤ stdProfileL rho (G X) :=
    (tendsto_stdProfileL_atTop hrho hG).eventually_ge_atTop w
  have hrate0 : Tendsto (fun X : ℕ ↦
      A * C * rho ^ w *
        (G X * (rho ^ stdProfileL rho (G X))⁻¹)) atTop (nhds 0) := by
    have hcore := tendsto_G_mul_inv_pow_stdProfileL hrho hG
    simpa only [mul_zero] using hcore.const_mul (A * C * rho ^ w)
  have hedge0 : Tendsto
      (fun X : ℕ ↦ 2 * (w : ℝ) / ((seqWindow a X).card : ℝ))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hcount).const_mul (2 * (w : ℝ))
  let bound : ℕ → ℝ := fun X ↦
    A * C * rho ^ w * (G X * (rho ^ stdProfileL rho (G X))⁻¹) +
      2 * (w : ℝ) / ((seqWindow a X).card : ℝ)
  have hbound0 : Tendsto bound atTop (nhds 0) := by
    simpa only [zero_add, bound] using hrate0.add hedge0
  refine squeeze_zero' ?_ ?_ hbound0
  · exact Eventually.of_forall fun X ↦
      windowAvgReal_nonneg_sequence _ fun n _ ↦
        tailMin_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
  · filter_upwards [hL, hTail] with X hLX hTX
    let L := stdProfileL rho (G X)
    let K := L - w
    let q : ℕ → ℝ := fun n ↦
      A * (rho ^ K)⁻¹ * seqGapTail rho a n
    let f : ℕ → ℝ := fun n ↦ min 1 (q n)
    have hq0 : ∀ n, 0 ≤ q n := fun n ↦
      mul_nonneg (mul_nonneg hA
        (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hrho).le _)))
        (seqGapTail_nonneg hrho a _)
    have hf0 : ∀ n, 0 ≤ f n := fun n ↦ tailMin_nonneg (hq0 n)
    have hf1 : ∀ n, f n ≤ 1 := fun n ↦ tailMin_le_one _
    have hpoint : ∀ n,
        min 1 (|coreLocalSeriesRemainder B hk phase
          (fun q ↦ (seqGap a q : ℝ)) F n K| ^
            ((1 : ℝ) / (d : ℝ))) ≤ f (n + K) := by
      intro n
      have hroot := rpow_abs_coreLocalSeriesRemainder_le hrho hB hbase
        hk phase F w n K (fun q ↦ (seqGap a q : ℝ)) hd0 hw hd
        (fun i ↦ by exact_mod_cast sequenceGap_one_le ha i)
        hgrowth (fun q ↦ summable_seqGap_div_pow hrho hsm q)
      have hwindow := scaledGapTail_localGapWindow_le hrho w n K
        (fun q ↦ (seqGap a q : ℝ)) (fun i ↦ Nat.cast_nonneg _)
        (fun q ↦ summable_seqGap_div_pow hrho hsm q)
      have hmajor :
          localTailRootConst (d := d) F *
              scaledGapTail rho (localGapWindow w
                (fun q ↦ (seqGap a q : ℝ))) n K ≤ q (n + K) := by
        have hc0 := localTailRootConst_nonneg (d := d) F
        exact (mul_le_mul_of_nonneg_left hwindow hc0).trans_eq (by
          dsimp only [q, A]
          change localTailRootConst (d := d) F *
              ((rho ^ K)⁻¹ * (∑ i ∈ range (w + 1), rho ^ i) *
                seqGapTail rho a (n + K)) = _
          ring)
      exact min_le_min le_rfl (hroot.trans hmajor)
    have hmono := windowAvgReal_mono_sequence (seqWindow a X)
      (fun n _ ↦ hpoint n)
    have hI : seqCount a X < seqCount a (2 * X) := by
      have hc : 0 < (Ico (seqCount a X) (seqCount a (2 * X))).card := by
        rw [← CoreSequenceResiduePassage.seqWindow_eq_Ico_seqCount ha]
        exact hTX.1
      rw [Nat.card_Ico] at hc
      omega
    have hshift := windowAvgReal_shift_le_Ico_sequence hI
      (fun n ↦ f (n + K)) w (fun n ↦ hf0 _) (fun n ↦ hf1 _)
    rw [← CoreSequenceResiduePassage.seqWindow_eq_Ico_seqCount ha] at hshift
    have hKL : K + w = L := by dsimp only [K, L]; omega
    have hwK : w + K = L := by omega
    have htailPoint : ∀ n, f (n + L) ≤
        A * (rho ^ K)⁻¹ * seqGapTail rho a (n + L) := by
      intro n
      calc
        f (n + L) ≤ q (n + L) := tailMin_le_t _
        _ = A * (rho ^ K)⁻¹ * seqGapTail rho a (n + L) := rfl
    have hshift' : windowAvgReal (seqWindow a X) (fun n ↦ f (n + K)) ≤
        windowAvgReal (seqWindow a X) (fun n ↦ f (n + L)) +
          2 * (w : ℝ) / (seqWindow a X).card := by
      simpa only [Nat.add_assoc, hwK] using hshift
    have htailMean := windowAvgReal_mono_sequence (seqWindow a X)
      (fun n _ ↦ htailPoint n)
    rw [windowAvgReal_const_mul_sequence] at htailMean
    have hmain : windowAvgReal (seqWindow a X) (fun n ↦ f (n + L)) ≤
        A * (rho ^ K)⁻¹ * (C * G X) := htailMean.trans
      (mul_le_mul_of_nonneg_left hTX.2
        (mul_nonneg hA (inv_nonneg.mpr
          (pow_nonneg (zero_lt_one.trans hrho).le _))))
    have hpowK : (rho ^ K)⁻¹ = rho ^ w * (rho ^ L)⁻¹ := by
      have hrho0 : rho ≠ 0 := (zero_lt_one.trans hrho).ne'
      have hp : rho ^ L = rho ^ K * rho ^ w := by
        rw [← pow_add, hKL]
      rw [hp]
      field_simp [pow_ne_zero K hrho0, pow_ne_zero w hrho0]
    have hadd := _root_.add_le_add hmain
      (le_refl (2 * (w : ℝ) / (seqWindow a X).card))
    exact hmono.trans (hshift'.trans (hadd.trans_eq (by
      rw [hpowK]
      dsimp only [bound, L]
      ring)))

/-- Bounded Lipschitz circle tests inherit the sequence-generic local-tail
vanishing, with the same actual truncation `stdProfileL rho (G X)-w`. -/
theorem tendsto_sequence_localPositiveTestRemainder_zero
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B d : ℕ} {rho : ℝ} (hB : 2 ≤ B) (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k)
    (w : ℕ) (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hgrowth : HasPolynomialGrowth (fun q ↦ (seqGap a q : ℝ)))
    {G : ℕ → ℝ} (hT : GapTailT a rho G)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    Tendsto (fun X : ℕ ↦
      windowAvgReal (seqWindow a X) (fun n ↦
        |f (coreLocalSeries B hk phase (fun q ↦ (seqGap a q : ℝ)) F n :
              AddCircle (1 : ℝ)) -
          f (coreLocalSeriesTrunc B hk phase
              (fun q ↦ (seqGap a q : ℝ)) F n
              (stdProfileL rho (G X) - w) : AddCircle (1 : ℝ))|))
      atTop (nhds 0) := by
  let A : ℝ := max (2 * ‖f‖) (K : ℝ)
  have hA : 0 ≤ A :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg f)).trans
      (le_max_left _ _)
  have hroot := tendsto_sequence_localTailRootMean_zero ha hcount hB hbase
    hk phase F w hd0 hw hd hgrowth hT
  have hmajor := hroot.const_mul A
  simp only [mul_zero] at hmajor
  apply squeeze_zero' _ _ hmajor
  · exact Eventually.of_forall fun X ↦
      div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (Nat.cast_nonneg _)
  · exact Eventually.of_forall fun X ↦ by
      have hsum := sum_le_sum fun n (_ : n ∈ seqWindow a X) ↦
        localPositiveTest_difference_le_min_root (B := B) hd0 hk phase
          (fun q ↦ (seqGap a q : ℝ)) F f hK n
          (stdProfileL rho (G X) - w)
      unfold windowAvgReal
      rw [← mul_div_assoc, mul_sum]
      exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

end

end PrimeGapNormality.Prime.CoreCyclic
