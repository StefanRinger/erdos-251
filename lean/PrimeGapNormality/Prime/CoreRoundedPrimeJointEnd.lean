import PrimeGapNormality.Prime.CoreRoundedPrimeFamily
import PrimeGapNormality.Prime.CorePrimeLocalJointEnd

/-!
# Product-Haar laws for finite rounded prime-gap families

The existing rounded-family `JointWeyl` theorem is exposed here as weak
convergence to product Haar, convergence of every continuous test average,
and literal half-open box frequencies. The coordinates are the actual finite
residue/exponent family `Fin k × I`, and no additional joint hypothesis is
introduced.

Source-only until the separate audit has passed a source-matched kernel build
and its complete types and transitive axiom closures have been inspected.
-/

namespace PrimeGapNormality.Prime.CoreRoundedPrimeJointEnd

open Filter MeasureTheory CoreJointEquidistribution
open CoreRoundedPowerScaling CoreRoundedPrimeFamily
open scoped Topology Classical

noncomputable section

/-- Weak convergence of the literal rounded family under an explicit D input. -/
theorem empirical_tendsto_of_D
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ d0 c : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    Tendsto (empirical (fun _ : Fin k × I ↦ B ^ k)
      (roundedResidueSeries B hk r kind alpha))
      atTop (𝓝 (torusVolume (Fin k × I))) :=
  empirical_tendsto_of_jointWeyl
    (roundedResidue_jointWeyl_of_D hB hk r kind alpha halpha halphaInj
      hκ hd0 hc hD)

/-- Continuous-test form of the same D-supplied product-Haar limit. -/
theorem continuous_test_tendsto_of_D
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ d0 c : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c)
    (f : C(Torus (Fin k × I), ℝ)) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, f (fun p ↦
      ((((B ^ k : ℕ) : ℝ) ^ n *
        roundedResidueSeries B hk r kind alpha p : ℝ) :
          AddCircle (1 : ℝ)))) / N)
      atTop (𝓝 (∫ x : Torus (Fin k × I), f x)) :=
  continuous_test_tendsto_of_jointWeyl
    (roundedResidue_jointWeyl_of_D hB hk r kind alpha halpha halphaInj
      hκ hd0 hc hD) f

/-- Literal simultaneous half-open box frequencies under the D input. -/
theorem box_frequency_of_D
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ d0 c : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c)
    (a b : Fin k × I → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hab : ∀ p, a p ≤ b p)
    (hb : ∀ p, b p ≤ 1) (hw : ∀ p, b p < a p + 1) :
    Tendsto (fun N : ℕ ↦ (((Finset.range N).filter (fun n ↦ ∀ p,
      Int.fract (((B ^ k : ℕ) : ℝ) ^ n *
        roundedResidueSeries B hk r kind alpha p) ∈
          Set.Ico (a p) (b p))).card : ℝ) / N)
      atTop (𝓝 (∏ p, (b p - a p))) :=
  box_frequency_of_jointWeyl
    (roundedResidue_jointWeyl_of_D hB hk r kind alpha halpha halphaInj
      hκ hd0 hc hD) a b ha hab hb hw

/-- Kuperberg-supplied weak convergence of the literal rounded family. -/
theorem empirical_tendsto_of_kuperberg
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hK : KuperbergConj13) :
    Tendsto (empirical (fun _ : Fin k × I ↦ B ^ k)
      (roundedResidueSeries B hk r kind alpha))
      atTop (𝓝 (torusVolume (Fin k × I))) :=
  empirical_tendsto_of_jointWeyl
    (roundedResidue_jointWeyl_of_kuperberg hB hk r kind alpha halpha
      halphaInj hκ hK)

/-- Continuous-test form of the Kuperberg-supplied product-Haar limit. -/
theorem continuous_test_tendsto_of_kuperberg
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hK : KuperbergConj13) (f : C(Torus (Fin k × I), ℝ)) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, f (fun p ↦
      ((((B ^ k : ℕ) : ℝ) ^ n *
        roundedResidueSeries B hk r kind alpha p : ℝ) :
          AddCircle (1 : ℝ)))) / N)
      atTop (𝓝 (∫ x : Torus (Fin k × I), f x)) :=
  continuous_test_tendsto_of_jointWeyl
    (roundedResidue_jointWeyl_of_kuperberg hB hk r kind alpha halpha
      halphaInj hκ hK) f

/-- Literal simultaneous half-open box frequencies under Kuperberg. -/
theorem box_frequency_of_kuperberg
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hK : KuperbergConj13) (a b : Fin k × I → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hab : ∀ p, a p ≤ b p)
    (hb : ∀ p, b p ≤ 1) (hw : ∀ p, b p < a p + 1) :
    Tendsto (fun N : ℕ ↦ (((Finset.range N).filter (fun n ↦ ∀ p,
      Int.fract (((B ^ k : ℕ) : ℝ) ^ n *
        roundedResidueSeries B hk r kind alpha p) ∈
          Set.Ico (a p) (b p))).card : ℝ) / N)
      atTop (𝓝 (∏ p, (b p - a p))) :=
  box_frequency_of_jointWeyl
    (roundedResidue_jointWeyl_of_kuperberg hB hk r kind alpha halpha
      halphaInj hκ hK) a b ha hab hb hw

end

end PrimeGapNormality.Prime.CoreRoundedPrimeJointEnd
