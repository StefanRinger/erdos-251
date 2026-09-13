import PrimeGapNormality.Prime.CoreRoundedInfiniteFamily
import PrimeGapNormality.Prime.CoreRoundedPrimeJointEnd

/-!
# Literal rounded prime-gap headline

This file specializes the existing rounded finite- and infinite-family
theorems to period one, residue zero, and actual floor rounding.  Its public
endpoints use only Kuperberg's conjecture; the degree-one profile
`κ = 1 / log B` is chosen internally.

Source-only until the separate audit has passed a source-matched kernel build
and its complete types and transitive axiom closures have been inspected.
-/

namespace PrimeGapNormality.Prime.CoreRoundedHeadline

open Filter CoreCyclic CoreIntegerGapObservable CoreJointEquidistribution
open CoreRoundedPowerScaling CoreRoundedPrimeFamily CoreRoundedInfiniteFamily
open scoped Topology Classical BigOperators

noncomputable section

abbrev Exponent := Set.Ioc (0 : ℝ) 1

private theorem one_pos : 0 < (1 : ℕ) := by omega

/-- The September 10 post's literal rounded prime-gap number. -/
def Z (B : ℕ) (alpha : Exponent) : ℝ :=
  ∑' n : ℕ, (⌊(primeGap n : ℝ) ^ (alpha : ℝ)⌋ : ℝ) /
    (B : ℝ) ^ (n + 1)

/-- Period one and residue zero reduce the general residue-labelled series
definition to the literal displayed `Z`. -/
theorem Z_eq_roundedResidueSeries
    {I : Type*} (B : ℕ) (alpha : I → Exponent) (i : I) :
    Z B (alpha i) =
      roundedResidueSeries B one_pos (0 : Fin 1) .floor
        (fun j ↦ (alpha j : ℝ)) ((0 : Fin 1), i) := by
  unfold Z roundedResidueSeries observableFullSeries observableSeries
    observableValue basisObservable roundedPower
  apply tsum_congr
  intro n
  have hphase : phaseAt one_pos (0 : Fin 1) n = (0 : Fin 1) :=
    Subsingleton.elim _ _
  simp only [hphase, if_true, Nat.zero_add]

/-- Identification with the already constructed entire rounded family. -/
theorem Z_eq_roundedInfiniteSeries (B : ℕ) (alpha : Exponent) :
    Z B alpha =
      roundedInfiniteSeries B one_pos (0 : Fin 1) .floor
        ((0 : Fin 1), alpha) := by
  unfold roundedInfiniteSeries
  exact Z_eq_roundedResidueSeries B (fun a : Exponent ↦ a) alpha

private def embedExponent : Option Exponent → Option (Fin 1 × Exponent)
  | none => none
  | some alpha => some ((0 : Fin 1), alpha)

private theorem embedExponent_injective : Function.Injective embedExponent := by
  intro x y hxy
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y => simp [embedExponent] at hxy
  | some x =>
      cases y with
      | none => simp [embedExponent] at hxy
      | some y =>
          have h : x = y := by simpa [embedExponent] using hxy
          exact congrArg some h

/-- The literal uncountable floor family is rationally linearly independent
together with `1`.  Every relation is finite by the meaning of
`LinearIndependent`; no infinite-dimensional distribution is asserted. -/
theorem one_Z_linearIndependent_of_kuperberg
    {B : ℕ} (hB : 2 ≤ B) (hK : KuperbergConj13) :
    LinearIndependent ℚ (fun x : Option Exponent ↦ match x with
      | none => (1 : ℝ)
      | some alpha => Z B alpha) := by
  let κ : ℝ := 1 / Real.log (B : ℝ)
  have hfull :=
    one_roundedInfiniteSeries_linearIndependent_of_kuperberg
      hB one_pos (0 : Fin 1) .floor (κ := κ) le_rfl hK
  have hrestricted := hfull.comp embedExponent embedExponent_injective
  convert hrestricted using 1
  funext x
  cases x with
  | none => rfl
  | some alpha =>
      simp only [embedExponent]
      exact Z_eq_roundedInfiniteSeries B alpha

/-- Each literal `Z(B,alpha)` is normal to the actual base `B`. -/
theorem Z_isNormal_of_kuperberg
    {B : ℕ} (hB : 2 ≤ B) (alpha : Exponent) (hK : KuperbergConj13) :
    PrimeGapNormality.BFree.IsNormal B (Z B alpha) := by
  let κ : ℝ := 1 / Real.log (B : ℝ)
  have hκpos : 0 < κ := div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))
  have hnormal := roundedResidue_rationalCombination_isNormal_of_D
    (I := Unit) hB one_pos (0 : Fin 1) .floor
    (fun _ : Unit ↦ (alpha : ℝ)) (fun _ ↦ alpha.2)
    (fun x y _ ↦ Subsingleton.elim x y)
    (κ := κ) le_rfl (by norm_num) (by norm_num)
    (coreLinearD_of_kuperberg hK hκpos)
    (fun _ : Fin 1 × Unit ↦ (1 : ℚ))
    ⟨((0 : Fin 1), ()), by norm_num⟩
  rw [Fintype.sum_prod_type] at hnormal
  simp only [Fintype.sum_unique, Rat.cast_one, one_mul, pow_one] at hnormal
  have hzero : (default : Fin 1) = 0 := Subsingleton.elim _ _
  have hunit : (default : Unit) = () := Subsingleton.elim _ _
  rw [hzero, hunit] at hnormal
  rw [← Z_eq_roundedResidueSeries B (fun _ : Unit ↦ alpha) ()] at hnormal
  exact hnormal

/-- Every finite injective list of admissible exponents has a genuine joint
Weyl law at `B`; the coordinate values are literally `Z B (alpha i)`. -/
theorem finite_Z_jointWeyl_of_kuperberg
    {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} (hB : 2 ≤ B) (alpha : I → Exponent)
    (halphaInj : Function.Injective alpha) (hK : KuperbergConj13) :
    JointWeyl (fun _ : I ↦ B) (fun i ↦ Z B (alpha i)) := by
  let κ : ℝ := 1 / Real.log (B : ℝ)
  have halphaRealInj : Function.Injective (fun i ↦ (alpha i : ℝ)) := by
    intro i j hij
    apply halphaInj
    exact Subtype.ext hij
  have hfull := roundedResidue_jointWeyl_of_kuperberg
    hB one_pos (0 : Fin 1) .floor (fun i ↦ (alpha i : ℝ))
    (fun i ↦ (alpha i).2) halphaRealInj (κ := κ) le_rfl hK
  intro t ht
  let t' : Fin 1 × I → ℤ := fun p ↦ t p.2
  have ht' : ∃ p, t' p ≠ 0 := by
    obtain ⟨i, hi⟩ := ht
    exact ⟨((0 : Fin 1), i), hi⟩
  have hphase (n : ℕ) :
      ∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * Z B (alpha i) =
        ∑ p : Fin 1 × I, (t' p : ℝ) *
          ((B ^ 1 : ℕ) : ℝ) ^ n *
            roundedResidueSeries B one_pos (0 : Fin 1) .floor
              (fun i ↦ (alpha i : ℝ)) p := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_unique, t', pow_one]
    have hzero : (default : Fin 1) = 0 := Subsingleton.elim _ _
    rw [hzero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Z_eq_roundedResidueSeries B alpha i]
  apply (hfull t' ht').congr'
  exact Eventually.of_forall fun N ↦ by
    apply congrArg (fun z : ℂ ↦ z / (N : ℂ))
    apply Finset.sum_congr rfl
    intro n hn
    exact congrArg e (hphase n).symm

/-- Product-Haar weak convergence for every such literal finite family. -/
theorem finite_Z_empirical_tendsto_of_kuperberg
    {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} (hB : 2 ≤ B) (alpha : I → Exponent)
    (halphaInj : Function.Injective alpha) (hK : KuperbergConj13) :
    Tendsto (empirical (fun _ : I ↦ B) (fun i ↦ Z B (alpha i)))
      atTop (𝓝 (torusVolume I)) :=
  empirical_tendsto_of_jointWeyl
    (finite_Z_jointWeyl_of_kuperberg hB alpha halphaInj hK)

end

end PrimeGapNormality.Prime.CoreRoundedHeadline
