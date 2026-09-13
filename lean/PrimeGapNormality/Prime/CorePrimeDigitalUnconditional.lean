import PrimeGapNormality.Prime.CorePrimeGapOrbit
import PrimeGapNormality.Prime.CorePrimeDensityBounds

/-!
# Prime-window digital consumer without a PNT assumption

Only the actual positive test domination remains a premise. Actual
dyadic window growth follows from unconditional quantitative Bertrand.
The arithmetic distribution hypothesis is supplied separately downstream.
-/

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace PrimeGapNormality.Prime
theorem corePrime_gapSeries_weyl_of_positive_bounds
    {B : ℕ} (hB : 2 ≤ B)
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
  have hN : Tendsto windowNX atTop atTop := CorePrimeDensity.tendsto_windowNX_atTop
  have hNreal := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hN
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
    simpa only [WindowCountToInfinity, seqWindow_nthPrime_card, Function.comp_def] using hNreal
  exact windowCountToCesaro nthPrime nthPrime_strictMono hcount _
    (fun n => (norm_e _).le) hw

theorem corePrime_position_weyl_of_positive_bounds
    {B : ℕ} (hB : 2 ≤ B)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
        windowAvgReal (seqWindow nthPrime X)
          (fun n => f (corePrimeGapCircleOrbit B n)) ≤
            A * ∫ x, f x ∂volume + ε) :
    weylCriterion B (primePosSeries B) := by
  have hW := corePrime_gapSeries_weyl_of_positive_bounds hB hA hbound
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
