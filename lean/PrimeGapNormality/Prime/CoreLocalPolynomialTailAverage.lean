import PrimeGapNormality.Prime.CoreLocalPolynomialTailLimit
import PrimeGapNormality.Prime.CorePrimeDensityBounds
import PrimeGapNormality.Prime.FreqBoostAvg

/-!
# Rooted and averaged local-polynomial tail

This file converts the natural-power local tail estimate to the paper's
`1/d`-root form and compares the finite-width gap-window tail with the
ordinary first-gap tail.  The bounded cutoff `min 1 t` is used before any
fixed index shift.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Filter Finset MvPolynomial
open scoped BigOperators Topology

noncomputable section

/-- The fixed root of the coefficient mass. -/
def localTailRootConst {k d : ℕ} (F : PeriodicLocal k) : ℝ :=
  localTupleCoeffMass F ^ ((1 : ℝ) / (d : ℝ))

theorem localTailRootConst_nonneg {k d : ℕ} (F : PeriodicLocal k) :
    0 ≤ localTailRootConst (d := d) F :=
  Real.rpow_nonneg (localTupleCoeffMass_nonneg F) _

/-- Pointwise `1/d`-root form of the true relative-label local tail. -/
theorem rpow_abs_coreLocalSeriesRemainder_le
    {B d : ℕ} {rho : ℝ} (hrho : 1 < rho) (hB : 2 ≤ B)
    (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : PeriodicLocal k)
    (w n K : ℕ) (g : ℕ → ℝ)
    (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hg : ∀ i, 1 ≤ g i)
    (hgrowth : HasPolynomialGrowth g)
    (hsmGap : ∀ a : ℕ, Summable fun j : ℕ ↦
      g (a + j) / rho ^ (j + 1)) :
    |coreLocalSeriesRemainder B hk r g F n K| ^
        ((1 : ℝ) / (d : ℝ)) ≤
      localTailRootConst (d := d) F *
        scaledGapTail rho (localGapWindow w g) n K := by
  have hraw := abs_coreLocalSeriesRemainder_le_scaledGapTail_pow
    hrho hB hbase hk r F w n K g hd0 hw hd hg hgrowth hsmGap
  let C : ℝ := localTupleCoeffMass F
  let s : ℝ := scaledGapTail rho (localGapWindow w g) n K
  have hC : 0 ≤ C := localTupleCoeffMass_nonneg F
  have hs : 0 ≤ s := by
    unfold s scaledGapTail
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hrho).le _))
      (tsum_nonneg fun j ↦ div_nonneg
        (localGapWindow_nonneg w (fun i ↦ zero_le_one.trans (hg i)) _)
        (pow_nonneg (zero_lt_one.trans hrho).le _))
  have hexp : 0 ≤ (1 : ℝ) / (d : ℝ) :=
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hroot := Real.rpow_le_rpow (abs_nonneg _) (by simpa [C, s] using hraw) hexp
  have hdne : d ≠ 0 := by omega
  have hsroot : (s ^ d) ^ ((1 : ℝ) / (d : ℝ)) = s := by
    rw [one_div, Real.pow_rpow_inv_natCast hs hdne]
  have hprod : (C * s ^ d) ^ ((1 : ℝ) / (d : ℝ)) =
      C ^ ((1 : ℝ) / (d : ℝ)) * s := by
    rw [Real.mul_rpow hC (pow_nonneg hs _), hsroot]
  rw [hprod] at hroot
  simpa only [localTailRootConst, C, s] using hroot

/-- Ordinary first-gap tail for a real nonnegative gap sequence. -/
def firstGapTail (rho : ℝ) (g : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑' j : ℕ, g (q + j) / rho ^ (j + 1)

theorem firstGapTail_nonneg {rho : ℝ} (hrho : 1 < rho)
    {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i) (q : ℕ) :
    0 ≤ firstGapTail rho g q :=
  tsum_nonneg fun j ↦
    div_nonneg (hg _) (pow_nonneg (zero_lt_one.trans hrho).le _)

private theorem shifted_firstGapTail_le
    {rho : ℝ} (hrho : 1 < rho) {g : ℕ → ℝ}
    (hg : ∀ i, 0 ≤ g i) (q i : ℕ)
    (hsm : Summable fun j : ℕ ↦ g (q + j) / rho ^ (j + 1)) :
    firstGapTail rho g (q + i) ≤ rho ^ i * firstGapTail rho g q := by
  let term : ℕ → ℝ := fun j ↦ g (q + j) / rho ^ (j + 1)
  have htail : Summable fun j : ℕ ↦ term (j + i) :=
    (summable_nat_add_iff i).2 hsm
  have hsplit := hsm.sum_add_tsum_nat_add i
  have hfinite0 : 0 ≤ ∑ j ∈ range i, term j :=
    sum_nonneg fun j _ ↦
      div_nonneg (hg _) (pow_nonneg (zero_lt_one.trans hrho).le _)
  have htailLe : (∑' j : ℕ, term (j + i)) ≤ ∑' j : ℕ, term j := by
    linarith
  have hrho0 : rho ≠ 0 := (zero_lt_one.trans hrho).ne'
  have hrewrite : firstGapTail rho g (q + i) =
      rho ^ i * ∑' j : ℕ, term (j + i) := by
    unfold firstGapTail
    rw [← htail.tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp only [term]
    have hpow : rho ^ (j + i + 1) = rho ^ i * rho ^ (j + 1) := by
      rw [show j + i + 1 = i + (j + 1) by omega, pow_add]
    rw [hpow]
    field_simp [pow_ne_zero i hrho0, pow_ne_zero (j + 1) hrho0]
    congr 1
    omega
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_left htailLe (pow_nonneg (zero_lt_one.trans hrho).le _)

/-- A width-`w` local gap-window tail costs only the fixed geometric
factor `∑_{i≤w} rho^i` against the ordinary first-gap tail. -/
theorem scaledGapTail_localGapWindow_le
    {rho : ℝ} (hrho : 1 < rho) (w n K : ℕ) (g : ℕ → ℝ)
    (hg : ∀ i, 0 ≤ g i)
    (hsm : ∀ q : ℕ, Summable fun j : ℕ ↦
      g (q + j) / rho ^ (j + 1)) :
    scaledGapTail rho (localGapWindow w g) n K ≤
      (rho ^ K)⁻¹ * (∑ i ∈ range (w + 1), rho ^ i) *
        firstGapTail rho g (n + K) := by
  have hi : ∀ i ∈ range (w + 1), Summable fun j : ℕ ↦
      g (n + K + j + i) / rho ^ (j + 1) := by
    intro i _
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsm (n + K + i)
  unfold scaledGapTail
  simp_rw [localGapWindow, Finset.sum_div]
  rw [Summable.tsum_finsetSum hi]
  have hsum :
      (∑ i ∈ range (w + 1),
        ∑' j : ℕ, g (n + K + j + i) / rho ^ (j + 1)) ≤
        ∑ i ∈ range (w + 1), rho ^ i * firstGapTail rho g (n + K) := by
    apply sum_le_sum
    intro i _
    simpa only [firstGapTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      shifted_firstGapTail_le hrho hg (n + K) i (hsm (n + K))
  have hinv : 0 ≤ (rho ^ K)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hrho).le _)
  calc
    (rho ^ K)⁻¹ *
        ∑ i ∈ range (w + 1),
          ∑' j : ℕ, g (n + K + j + i) / rho ^ (j + 1) ≤
      (rho ^ K)⁻¹ *
        ∑ i ∈ range (w + 1), rho ^ i * firstGapTail rho g (n + K) :=
      mul_le_mul_of_nonneg_left hsum hinv
    _ = (rho ^ K)⁻¹ * (∑ i ∈ range (w + 1), rho ^ i) *
        firstGapTail rho g (n + K) := by
      rw [← Finset.sum_mul, mul_assoc]

/-! ### Bounded shift and the actual first-gap mean -/

private theorem freqBoost_avg_ofReal (I : Finset ℕ) (f : ℕ → ℝ) :
    freqBoost_avg I (fun n ↦ (f n : ℂ)) = (windowAvgReal I f : ℂ) := by
  unfold freqBoost_avg windowAvgReal
  rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

private theorem windowAvgReal_shift_le_Ico
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
  rw [freqBoost_avg_ofReal, freqBoost_avg_ofReal] at hshift
  have habs :
      |windowAvgReal (Ico a b) (fun n ↦ f (n + w)) -
        windowAvgReal (Ico a b) f| ≤
          2 * (w : ℝ) / (Ico a b).card := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hshift
  linarith [neg_abs_le
    (windowAvgReal (Ico a b) (fun n ↦ f (n + w)) -
      windowAvgReal (Ico a b) f)]

private theorem windowAvgReal_nonneg_local (I : Finset ℕ) {f : ℕ → ℝ}
    (hf : ∀ n ∈ I, 0 ≤ f n) : 0 ≤ windowAvgReal I f := by
  unfold windowAvgReal
  exact div_nonneg (sum_nonneg hf) (Nat.cast_nonneg _)

private theorem windowAvgReal_mono_local (I : Finset ℕ) {f g : ℕ → ℝ}
    (hfg : ∀ n ∈ I, f n ≤ g n) :
    windowAvgReal I f ≤ windowAvgReal I g := by
  unfold windowAvgReal
  exact div_le_div_of_nonneg_right (sum_le_sum hfg) (Nat.cast_nonneg _)

private theorem windowAvgReal_const_mul_local (I : Finset ℕ) (c : ℝ)
    (f : ℕ → ℝ) :
    windowAvgReal I (fun n ↦ c * f n) = c * windowAvgReal I f := by
  unfold windowAvgReal
  rw [← Finset.mul_sum]
  ring

private theorem primeGap_one_le (n : ℕ) : 1 ≤ primeGap n := by
  unfold primeGap
  exact Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt
    (nthPrime_strictMono (Nat.lt_succ_self n)))

private theorem seqWindow_nthPrime_eq_Ico_local (X : ℕ) :
    seqWindow nthPrime X =
      Ico (Nat.primeCounting X) (Nat.primeCounting (2 * X)) := by
  rw [seqWindow_nthPrime_eq_primeIndexBlock, primeIndexBlock_eq_Ico]

/-- The actual bounded `1/d`-root local-tail mean tends to zero using only
the ordinary first-gap tail mean.  The truncation is `L-w`; the fixed
shift by `w` is paid after applying `min 1`, so no `L+w` tail input occurs. -/
theorem tendsto_primeGap_localTailRootMean_zero
    {B d : ℕ} {rho : ℝ} (hB : 2 ≤ B) (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : PeriodicLocal k)
    (w : ℕ) (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    {G : ℕ → ℝ} (hT : GapTailT nthPrime rho G) :
    Tendsto (fun X : ℕ ↦
      windowAvgReal (seqWindow nthPrime X) (fun n ↦
        min 1 (|coreLocalSeriesRemainder B hk r
          (fun q ↦ (primeGap q : ℝ)) F n
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
  have hcardReal : Tendsto
      (fun X : ℕ ↦ ((seqWindow nthPrime X).card : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, seqWindow_nthPrime_card] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
        CorePrimeDensity.tendsto_windowNX_atTop)
  have hedge0 : Tendsto
      (fun X : ℕ ↦ 2 * (w : ℝ) / ((seqWindow nthPrime X).card : ℝ))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hcardReal).const_mul (2 * (w : ℝ))
  let bound : ℕ → ℝ := fun X ↦
    A * C * rho ^ w * (G X * (rho ^ stdProfileL rho (G X))⁻¹) +
      2 * (w : ℝ) / ((seqWindow nthPrime X).card : ℝ)
  have hbound0 : Tendsto bound atTop (nhds 0) := by
    simpa only [zero_add, bound] using hrate0.add hedge0
  refine squeeze_zero' ?_ ?_ hbound0
  · exact Eventually.of_forall fun X ↦
      windowAvgReal_nonneg_local _ fun n _ ↦
        tailMin_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
  · filter_upwards [hL, hTail] with X hLX hTX
    let L := stdProfileL rho (G X)
    let K := L - w
    let q : ℕ → ℝ := fun n ↦
      A * (rho ^ K)⁻¹ * seqGapTail rho nthPrime n
    let f : ℕ → ℝ := fun n ↦ min 1 (q n)
    have hq0 : ∀ n, 0 ≤ q n := fun n ↦
      mul_nonneg (mul_nonneg hA
        (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hrho).le _)))
        (seqGapTail_nonneg hrho nthPrime _)
    have hf0 : ∀ n, 0 ≤ f n := fun n ↦ tailMin_nonneg (hq0 n)
    have hf1 : ∀ n, f n ≤ 1 := fun n ↦ tailMin_le_one _
    have hpoint : ∀ n,
        min 1 (|coreLocalSeriesRemainder B hk r
          (fun q ↦ (primeGap q : ℝ)) F n K| ^
            ((1 : ℝ) / (d : ℝ))) ≤ f (n + K) := by
      intro n
      have hroot := rpow_abs_coreLocalSeriesRemainder_le hrho hB hbase
        hk r F w n K (fun q ↦ (primeGap q : ℝ)) hd0 hw hd
        (fun i ↦ by exact_mod_cast primeGap_one_le i)
        primeGap_hasPolynomialGrowth
        (fun a ↦ summable_seqGap_div_pow hrho hsm a)
      have hwindow := scaledGapTail_localGapWindow_le hrho w n K
        (fun q ↦ (primeGap q : ℝ)) (fun i ↦ Nat.cast_nonneg _)
        (fun a ↦ summable_seqGap_div_pow hrho hsm a)
      have hmajor :
          localTailRootConst (d := d) F *
              scaledGapTail rho (localGapWindow w
                (fun q ↦ (primeGap q : ℝ))) n K ≤ q (n + K) := by
        have hc0 := localTailRootConst_nonneg (d := d) F
        exact (mul_le_mul_of_nonneg_left hwindow hc0).trans_eq (by
          dsimp only [q, A]
          change localTailRootConst (d := d) F *
              ((rho ^ K)⁻¹ * (∑ i ∈ range (w + 1), rho ^ i) *
                seqGapTail rho nthPrime (n + K)) = _
          ring)
      exact min_le_min le_rfl (hroot.trans hmajor)
    have hmono := windowAvgReal_mono_local (seqWindow nthPrime X)
      (fun n _ ↦ hpoint n)
    have hI : Nat.primeCounting X < Nat.primeCounting (2 * X) := by
      have hc : 0 < (Ico (Nat.primeCounting X)
          (Nat.primeCounting (2 * X))).card := by
        rw [← seqWindow_nthPrime_eq_Ico_local]
        exact hTX.1
      rw [Nat.card_Ico] at hc
      omega
    have hshift := windowAvgReal_shift_le_Ico hI (fun n ↦ f (n + K)) w
      (fun n ↦ hf0 _) (fun n ↦ hf1 _)
    rw [← seqWindow_nthPrime_eq_Ico_local] at hshift
    have hKL : K + w = L := by dsimp only [K, L]; omega
    have hwK : w + K = L := by omega
    have htailPoint : ∀ n, f (n + L) ≤
        A * (rho ^ K)⁻¹ * seqGapTail rho nthPrime (n + L) := by
      intro n
      calc
        f (n + L) ≤ q (n + L) := tailMin_le_t _
        _ = A * (rho ^ K)⁻¹ * seqGapTail rho nthPrime (n + L) := rfl
    have hshift' : windowAvgReal (seqWindow nthPrime X) (fun n ↦ f (n + K)) ≤
        windowAvgReal (seqWindow nthPrime X) (fun n ↦ f (n + L)) +
          2 * (w : ℝ) / (seqWindow nthPrime X).card := by
      simpa only [Nat.add_assoc, hwK] using hshift
    have htailMean := windowAvgReal_mono_local (seqWindow nthPrime X)
      (fun n _ ↦ htailPoint n)
    rw [windowAvgReal_const_mul_local] at htailMean
    have hmain : windowAvgReal (seqWindow nthPrime X) (fun n ↦ f (n + L)) ≤
        A * (rho ^ K)⁻¹ * (C * G X) := htailMean.trans
      (mul_le_mul_of_nonneg_left hTX.2
        (mul_nonneg hA (inv_nonneg.mpr (pow_nonneg
          (zero_lt_one.trans hrho).le _))))
    have hpowK : (rho ^ K)⁻¹ = rho ^ w * (rho ^ L)⁻¹ := by
      have hrho0 : rho ≠ 0 := (zero_lt_one.trans hrho).ne'
      have hp : rho ^ L = rho ^ K * rho ^ w := by
        rw [← pow_add, hKL]
      rw [hp]
      field_simp [pow_ne_zero K hrho0, pow_ne_zero w hrho0]
    have hadd := _root_.add_le_add hmain
      (le_refl (2 * (w : ℝ) / (seqWindow nthPrime X).card))
    exact hmono.trans (hshift'.trans (hadd.trans_eq (by
      rw [hpowK]
      dsimp only [bound, L]
      ring)))

end

end PrimeGapNormality.Prime.CoreCyclic
