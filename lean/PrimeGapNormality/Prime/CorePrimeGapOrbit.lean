import PrimeGapNormality.Prime.CorePositiveTail
import PrimeGapNormality.Prime.WindowNXPosFromPNT
import PrimeGapNormality.Prime.PhysicalWindowST

/-! The actual infinite linear gap orbit and its physical windows.
The positive window bound is the one still being proved by the model and
arithmetic branches; this file does not treat it as a proved prime input.
-/

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

noncomputable def corePrimeGapCircleOrbit (B n : ℕ) : AddCircle (1 : ℝ) :=
  (seqGapPolyTail nthPrime (fun _ => Polynomial.X) B n : ℝ)

theorem coreCircle_natCast_eq_zero (m : ℕ) :
    ((m : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  have h := AddCircle.coe_nsmul (p := (1 : ℝ)) (n := m) (x := (1 : ℝ))
  simpa only [nsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using h

theorem corePrimeGapCircleOrbit_recurrence {B : ℕ} (hB : 2 ≤ B) (n : ℕ) :
    corePrimeGapCircleOrbit B (n + 1) = B • corePrimeGapCircleOrbit B n := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hsm := summable_seqGap_div_pow hBr (nthPrime_div_pow_summable hBr) n
  have hrec := seqGapPolyTail_succ (a := nthPrime)
    (P := fun _ => Polynomial.X) (B := B) (n := n) hB
    (by simpa only [Polynomial.eval_X] using hsm)
  unfold corePrimeGapCircleOrbit
  rw [hrec, Polynomial.eval_X, AddCircle.coe_sub, coreCircle_natCast_eq_zero, sub_zero]
  simpa only [nsmul_eq_mul] using
    (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := B)
      (x := seqGapPolyTail nthPrime (fun _ => Polynomial.X) B n))

theorem corePrime_seqWindow_eq_Ico (X : ℕ) :
    seqWindow nthPrime X = Ico (Nat.primeCounting X) (Nat.primeCounting (2 * X)) := by
  rw [seqWindow_nthPrime_eq_primeIndexBlock, primeIndexBlock_eq_Ico]

theorem corePrime_window_positive_average_eq
    (u : ℕ → AddCircle (1 : ℝ)) (f : AddCircle (1 : ℝ) →ᵇ ℝ) (X : ℕ) :
    windowAvgReal (seqWindow nthPrime X) (fun n => f (u n)) =
      coreDigitalWindowAverage u f (Nat.primeCounting X) (windowNX X) := by
  unfold windowAvgReal coreDigitalWindowAverage
  rw [seqWindow_nthPrime_card, corePrime_seqWindow_eq_Ico,
    sum_Ico_eq_sum_range]
  simp only [windowNX, add_comm]

theorem coreCircle_fourier_eq_e (q : ℤ) (x : ℝ) :
    fourier q (x : AddCircle (1 : ℝ)) = e ((q : ℝ) * x) := by
  rw [fourier_coe_apply]
  simp only [e, Complex.ofReal_one, div_one, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

theorem corePrime_window_character_average_eq (B X : ℕ) (q : ℤ) :
    windowAvg (seqWindow nthPrime X)
        (fun n => e ((q : ℝ) * seqGapPolyTail nthPrime (fun _ => Polynomial.X) B n)) =
      (∑ i ∈ range (windowNX X),
        fourier q (corePrimeGapCircleOrbit B (Nat.primeCounting X + i))) /
          (windowNX X : ℂ) := by
  unfold windowAvg
  rw [seqWindow_nthPrime_card, corePrime_seqWindow_eq_Ico, sum_Ico_eq_sum_range]
  simp only [corePrimeGapCircleOrbit, coreCircle_fourier_eq_e, windowNX, add_comm]

theorem corePrime_gapSeries_weyl_of_positive_window_bounds
    {B : ℕ} (hB : 2 ≤ B) (hKuperberg : KuperbergConj13)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
        windowAvgReal (seqWindow nthPrime X)
          (fun n => f (corePrimeGapCircleOrbit B n)) ≤
            A * ∫ x, f x ∂volume + ε) :
    weylCriterion B (seqGapPolySeries nthPrime (fun _ => Polynomial.X) B) := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hsm := summable_seqGap_div_pow hBr (nthPrime_div_pow_summable hBr) 0
  apply weylCriterion_of_tailVanishing hB
    (by simpa only [Polynomial.eval_X, zero_add] using hsm)
    (fun n => ⟨seqGap nthPrime n, by simp⟩)
  intro q hq
  have hNreal := tendsto_windowNX_atTop_of_kuperberg hKuperberg
  have hN : Tendsto windowNX atTop atTop := tendsto_natCast_atTop_iff.mp hNreal
  have hshift := coreDigital_window_character_tendsto_zero_of_lipschitz_bounds hB
    (corePrimeGapCircleOrbit B) (corePrimeGapCircleOrbit_recurrence hB)
    (fun X => Nat.primeCounting (X + 1)) (fun X => windowNX (X + 1))
    (hN.comp (tendsto_add_atTop_nat 1))
    (fun X => windowNX_pos_of_pos (by omega)) hA
    (by
      intro f K hK hf ε hε
      have h := (tendsto_add_atTop_nat 1).eventually (hbound f K hK hf ε hε)
      simpa only [corePrime_window_positive_average_eq] using h)
    hq
  have hw : PhysicalWindowMeanVanishing nthPrime
      (fun n => e ((q : ℝ) * seqGapPolyTail nthPrime (fun _ => Polynomial.X) B n)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [corePrime_window_character_average_eq] using hshift
  have hcount : WindowCountToInfinity nthPrime := by
    simpa only [WindowCountToInfinity, seqWindow_nthPrime_card] using hNreal
  exact windowCountToCesaro nthPrime nthPrime_strictMono hcount _
    (fun n => (norm_e _).le) hw

theorem corePrime_position_weyl_of_positive_window_bounds
    {B : ℕ} (hB : 2 ≤ B) (hKuperberg : KuperbergConj13)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
        windowAvgReal (seqWindow nthPrime X)
          (fun n => f (corePrimeGapCircleOrbit B n)) ≤
            A * ∫ x, f x ∂volume + ε) :
    weylCriterion B (primePosSeries B) := by
  have hW := corePrime_gapSeries_weyl_of_positive_window_bounds hB hKuperberg hA hbound
  have hgap : weylCriterion B (primeGapPowerSeries B 1) := by
    simpa only [seqGapPolySeries, seqGapPolyTail, primeGapPowerSeries, Polynomial.eval_X,
      zero_add, seqGap_nthPrime, pow_one] using hW
  have hadd := weylCriterion_add_int (nthPrime 0 : ℤ) hgap
  apply weylCriterion_of_mul (q := B - 1) (by omega) hB
  have heq : ((B - 1 : ℕ) : ℝ) * primePosSeries B =
      primeGapPowerSeries B 1 + ((nthPrime 0 : ℤ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_one, primeGapPowerSeries_one_eq hB]
    push_cast
    ring
  rwa [heq]

end PrimeGapNormality.Prime
