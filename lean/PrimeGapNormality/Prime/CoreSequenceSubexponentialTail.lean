import PrimeGapNormality.Prime.CoreSubexponentialRecurrence
import PrimeGapNormality.Prime.CoreSequenceLocalTailAverage
import PrimeGapNormality.Prime.FreqBoostAvg

/-!
# Sequence-local polynomial tails from subexponential growth

This is the S/T tail consumer with the analytic growth input weakened from a
global polynomial majorant to `HasSubexponentialGrowth`.  The finite
polynomial estimate and first-gap-tail comparison are unchanged; the only new
step is deriving the true infinite-series summability from the subexponential
algebra before passing the finite bounds to the limit.
-/

namespace PrimeGapNormality.Prime.CoreSequenceSubexponentialGrowth

open Filter Finset MvPolynomial
open CoreCyclic
open scoped BigOperators Topology NNReal BoundedContinuousFunction

noncomputable section

private theorem localLinearShift_summable_subexp
    {rho : ℝ} (hrho : 1 < rho) (h : ℕ → ℝ) (n K : ℕ)
    (hsm : Summable (fun j : ℕ ↦ h (n + K + j) / rho ^ (j + 1))) :
    Summable (fun j : ℕ ↦ h (n + K + j) / rho ^ (K + j + 1)) := by
  have hrho0 : rho ≠ 0 := (zero_lt_one.trans hrho).ne'
  have hfun :
      (fun j : ℕ ↦ h (n + K + j) / rho ^ (K + j + 1)) =
        fun j : ℕ ↦ (rho ^ K)⁻¹ *
          (h (n + K + j) / rho ^ (j + 1)) := by
    funext j
    rw [show K + j + 1 = K + (j + 1) by omega, pow_add]
    field_simp [pow_ne_zero K hrho0, pow_ne_zero (j + 1) hrho0]
  rw [hfun]
  exact hsm.mul_left (rho ^ K)⁻¹

private theorem linearGapTailTrunc_le_scaled_subexp
    {rho : ℝ} (hrho : 1 < rho) (h : ℕ → ℝ) (n K N : ℕ)
    (hh : ∀ i, 0 ≤ h i)
    (hsm : Summable (fun j : ℕ ↦ h (n + K + j) / rho ^ (j + 1))) :
    linearGapTailTrunc rho h n K (K + N) ≤
      scaledGapTail rho h n K := by
  have hs := localLinearShift_summable_subexp hrho h n K hsm
  rw [linearGapTailTrunc, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  rw [scaledGapTail_eq_linear_tsum hrho hsm]
  simpa only [Nat.add_assoc] using
    hs.sum_le_tsum (range N) (fun j _ ↦
      div_nonneg (hh _) (pow_nonneg (zero_lt_one.trans hrho).le _))

private theorem finite_localTail_abs_le_scaled_pow_subexp
    {B d : ℕ} {rho : ℝ} (hrho : 1 < rho) (hB : 2 ≤ B)
    (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : PeriodicLocal k)
    (w n K N : ℕ) (g : ℕ → ℝ)
    (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hg : ∀ i, 1 ≤ g i)
    (hsm : Summable (fun j : ℕ ↦
      localGapWindow w g (n + K + j) / rho ^ (j + 1))) :
    (∑ j ∈ range N,
      |relativeLocalValue hk r g F n (K + j) /
        (B : ℝ) ^ (K + j + 1)|) ≤
      localTupleCoeffMass F *
        scaledGapTail rho (localGapWindow w g) n K ^ d := by
  let h : ℕ → ℝ := localGapWindow w g
  let C : ℝ := localTupleCoeffMass F
  have hC : 0 ≤ C := localTupleCoeffMass_nonneg F
  have hh : ∀ q, 0 ≤ h q := fun q ↦
    localGapWindow_nonneg w (fun i ↦ zero_le_one.trans (hg i)) q
  have hterm : ∀ j ∈ range N,
      |relativeLocalValue hk r g F n (K + j) /
        (B : ℝ) ^ (K + j + 1)| ≤
        C * h (n + K + j) ^ d / (B : ℝ) ^ (K + j + 1) := by
    intro j _
    have hv := abs_localValue_le_localTupleCoeffMass_mul_sum_pow
      hk r F w d (K + j) (fun q ↦ g (n + q)) hw hd
      (fun q ↦ hg (n + q))
    have hv' : |relativeLocalValue hk r g F n (K + j)| ≤
        C * h (n + K + j) ^ d := by
      simpa only [relativeLocalValue, localValue, C, h, localGapWindow,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv
    have hden : 0 ≤ (B : ℝ) ^ (K + j + 1) :=
      pow_nonneg (Nat.cast_nonneg _) _
    rw [abs_div, abs_of_nonneg hden]
    exact div_le_div_of_nonneg_right hv' hden
  have hsum := sum_le_sum hterm
  have hrewrite :
      (∑ j ∈ range N,
        C * h (n + K + j) ^ d / (B : ℝ) ^ (K + j + 1)) =
        C * gapPowerRemainderTrunc h B d n K (K + N) := by
    unfold gapPowerRemainderTrunc
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [Nat.add_assoc]
    ring
  rw [hrewrite] at hsum
  have hpower := gapPowerRemainderTrunc_le_pow_linearGapTailTrunc
    h n K (K + N) hrho hB hbase hd0 le_rfl hh
  have hlin := linearGapTailTrunc_le_scaled_subexp hrho h n K N hh hsm
  have hlin0 : 0 ≤ linearGapTailTrunc rho h n K (K + N) :=
    sum_nonneg fun j _ ↦
      div_nonneg (hh _) (pow_nonneg (zero_lt_one.trans hrho).le _)
  have hpow := pow_le_pow_left₀ hlin0 hlin d
  exact hsum.trans (mul_le_mul_of_nonneg_left (hpower.trans hpow) hC)

/-- Infinite local remainder controlled by the same first-moment gap tail,
now with true summability supplied by subexponential growth. -/
theorem abs_coreLocalSeriesRemainder_le_scaledGapTail_pow_of_subexponential
    {B d : ℕ} {rho : ℝ} (hrho : 1 < rho) (hB : 2 ≤ B)
    (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : PeriodicLocal k)
    (w n K : ℕ) (g : ℕ → ℝ)
    (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hg : ∀ i, 1 ≤ g i)
    (hgrowth : HasSubexponentialGrowth g) :
    |coreLocalSeriesRemainder B hk r g F n K| ≤
      localTupleCoeffMass F *
        scaledGapTail rho (localGapWindow w g) n K ^ d := by
  have hlocal := relativeLocalSeries_summable_of_subexponential
    hB hk r g hgrowth F n
  rw [coreLocalSeriesRemainder_eq_tsum B hk r g F n K hlocal]
  let term : ℕ → ℝ := fun j ↦
    relativeLocalValue hk r g F n (K + j) /
      (B : ℝ) ^ (K + j + 1)
  have hterm : Summable term := by
    have hs := (summable_nat_add_iff K).2 hlocal
    apply hs.congr
    intro j
    dsimp only [term]
    congr 2 <;> omega
  have hsmGap : ∀ a : ℕ, Summable (fun j : ℕ ↦
      g (a + j) / rho ^ (j + 1)) := by
    intro a
    have hshift : HasSubexponentialGrowth (fun j ↦ g (j + a)) :=
      hgrowth.shift a
    simpa only [Nat.add_comm] using hshift.summable_div_pow_succ hrho
  have hsmWindow : Summable (fun j : ℕ ↦
      localGapWindow w g (n + K + j) / rho ^ (j + 1)) :=
    summable_localGapWindow_div w g (n + K) hsmGap
  have hbound : ∀ N : ℕ,
      ∑ j ∈ range N, |term j| ≤
        localTupleCoeffMass F *
          scaledGapTail rho (localGapWindow w g) n K ^ d := by
    intro N
    exact finite_localTail_abs_le_scaled_pow_subexp hrho hB hbase hk r F
      w n K N g hd0 hw hd hg hsmWindow
  have htsum := Real.tsum_le_of_sum_range_le
    (fun j ↦ abs_nonneg (term j)) hbound
  exact (norm_tsum_le_tsum_norm hterm.norm).trans htsum

/-- Pointwise `1/d`-root tail bound under subexponential growth. -/
theorem rpow_abs_coreLocalSeriesRemainder_le_of_subexponential
    {B d : ℕ} {rho : ℝ} (hrho : 1 < rho) (hB : 2 ≤ B)
    (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : PeriodicLocal k)
    (w n K : ℕ) (g : ℕ → ℝ)
    (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hg : ∀ i, 1 ≤ g i)
    (hgrowth : HasSubexponentialGrowth g) :
    |coreLocalSeriesRemainder B hk r g F n K| ^
        ((1 : ℝ) / (d : ℝ)) ≤
      localTailRootConst (d := d) F *
        scaledGapTail rho (localGapWindow w g) n K := by
  have hraw := abs_coreLocalSeriesRemainder_le_scaledGapTail_pow_of_subexponential
    hrho hB hbase hk r F w n K g hd0 hw hd hg hgrowth
  let C : ℝ := localTupleCoeffMass F
  let s : ℝ := scaledGapTail rho (localGapWindow w g) n K
  have hC : 0 ≤ C := localTupleCoeffMass_nonneg F
  have hs : 0 ≤ s := by
    unfold s scaledGapTail
    exact mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hrho).le _))
      (tsum_nonneg fun j ↦ div_nonneg
        (localGapWindow_nonneg w (fun i ↦ zero_le_one.trans (hg i)) _)
        (pow_nonneg (zero_lt_one.trans hrho).le _))
  have hexp : 0 ≤ (1 : ℝ) / (d : ℝ) :=
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hroot := Real.rpow_le_rpow (abs_nonneg _)
    (by simpa [C, s] using hraw) hexp
  have hdne : d ≠ 0 := by omega
  have hsroot : (s ^ d) ^ ((1 : ℝ) / (d : ℝ)) = s := by
    rw [one_div, Real.pow_rpow_inv_natCast hs hdne]
  have hprod : (C * s ^ d) ^ ((1 : ℝ) / (d : ℝ)) =
      C ^ ((1 : ℝ) / (d : ℝ)) * s := by
    rw [Real.mul_rpow hC (pow_nonneg hs _), hsroot]
  rw [hprod] at hroot
  simpa only [localTailRootConst, C, s] using hroot

private theorem sequenceGap_one_le_subexp
    {a : ℕ → ℕ} (ha : StrictMono a) (n : ℕ) :
    1 ≤ seqGap a n := by
  unfold seqGap
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.sub_ne_zero_of_lt (ha (Nat.lt_succ_self n)))

private theorem freqBoost_avg_ofReal_sequence_subexp
    (I : Finset ℕ) (f : ℕ → ℝ) :
    freqBoost_avg I (fun n ↦ (f n : ℂ)) = (windowAvgReal I f : ℂ) := by
  unfold freqBoost_avg windowAvgReal
  rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

private theorem windowAvgReal_shift_le_Ico_subexp
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
  rw [freqBoost_avg_ofReal_sequence_subexp,
    freqBoost_avg_ofReal_sequence_subexp] at hshift
  have habs :
      |windowAvgReal (Ico a b) (fun n ↦ f (n + w)) -
        windowAvgReal (Ico a b) f| ≤
          2 * (w : ℝ) / (Ico a b).card := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      using hshift
  linarith [neg_abs_le
    (windowAvgReal (Ico a b) (fun n ↦ f (n + w)) -
      windowAvgReal (Ico a b) f)]

private theorem windowAvgReal_nonneg_subexp
    (I : Finset ℕ) {f : ℕ → ℝ} (hf : ∀ n ∈ I, 0 ≤ f n) :
    0 ≤ windowAvgReal I f := by
  unfold windowAvgReal
  exact div_nonneg (sum_nonneg hf) (Nat.cast_nonneg _)

private theorem windowAvgReal_mono_subexp
    (I : Finset ℕ) {f g : ℕ → ℝ} (hfg : ∀ n ∈ I, f n ≤ g n) :
    windowAvgReal I f ≤ windowAvgReal I g := by
  unfold windowAvgReal
  exact div_le_div_of_nonneg_right (sum_le_sum hfg) (Nat.cast_nonneg _)

private theorem windowAvgReal_const_mul_subexp
    (I : Finset ℕ) (c : ℝ) (f : ℕ → ℝ) :
    windowAvgReal I (fun n ↦ c * f n) = c * windowAvgReal I f := by
  unfold windowAvgReal
  rw [← Finset.mul_sum]
  ring

/-- The genuine first-gap `GapTailT` estimate makes the bounded local
`1/d`-root remainder vanish for a subexponential gap sequence. -/
theorem tendsto_sequence_localTailRootMean_zero_of_subexponential
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B d : ℕ} {rho : ℝ} (hB : 2 ≤ B) (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k)
    (w : ℕ) (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hgrowth : HasSubexponentialGrowth (fun q ↦ (seqGap a q : ℝ)))
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
      windowAvgReal_nonneg_subexp _ fun n _ ↦
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
      have hroot := rpow_abs_coreLocalSeriesRemainder_le_of_subexponential
        hrho hB hbase hk phase F w n K (fun q ↦ (seqGap a q : ℝ))
        hd0 hw hd (fun i ↦ by exact_mod_cast sequenceGap_one_le_subexp ha i)
        hgrowth
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
    have hmono := windowAvgReal_mono_subexp (seqWindow a X)
      (fun n _ ↦ hpoint n)
    have hI : seqCount a X < seqCount a (2 * X) := by
      have hc : 0 < (Ico (seqCount a X) (seqCount a (2 * X))).card := by
        rw [← CoreSequenceResiduePassage.seqWindow_eq_Ico_seqCount ha]
        exact hTX.1
      rw [Nat.card_Ico] at hc
      omega
    have hshift := windowAvgReal_shift_le_Ico_subexp hI
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
    have htailMean := windowAvgReal_mono_subexp (seqWindow a X)
      (fun n _ ↦ htailPoint n)
    rw [windowAvgReal_const_mul_subexp] at htailMean
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

/-- Bounded Lipschitz phase tests inherit the subexponential local-tail
vanishing with the identical `L-w` truncation. -/
theorem tendsto_sequence_localPositiveTestRemainder_zero_of_subexponential
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B d : ℕ} {rho : ℝ} (hB : 2 ≤ B) (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k)
    (w : ℕ) (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hgrowth : HasSubexponentialGrowth (fun q ↦ (seqGap a q : ℝ)))
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
  have hroot := tendsto_sequence_localTailRootMean_zero_of_subexponential
    ha hcount hB hbase hk phase F w hd0 hw hd hgrowth hT
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
end PrimeGapNormality.Prime.CoreSequenceSubexponentialGrowth
