import PrimeGapNormality.Prime.CoreRoundedRoughFamily

/-!
# The entire rounded moving-rough exponent family

Every rational linear relation has finite support.  Its finite set of
exponents is handled by `CoreRoundedRoughFamily`, then restricted back along
an injective map.  This proves independence of `1` and the entire family
indexed by `Fin k × Set.Ioc 0 1` for the actual moving-rough gaps.

This is only an algebraic finite-restriction result.  No infinite torus or
infinite-dimensional distribution is asserted.  The whole family shares one
fixed `RoundKind` and one common `κ`.
-/

namespace PrimeGapNormality.Prime.CoreRoundedRoughInfiniteFamily

open Finset CoreCyclic CoreRoundedPowerScaling CoreRoughThreshold
open CoreRoundedRoughFamily
open scoped Classical

noncomputable section

abbrev Exponent := Set.Ioc (0 : ℝ) 1

private def defaultExponent : Exponent := ⟨1, by simp⟩

/-- Literal entire residue/exponent family on the actual moving-rough
sequence. -/
def movingRoughRoundedInfiniteSeries
    (Ψ : ℝ → ℝ) (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (p : Fin k × Exponent) : ℝ :=
  movingRoughRoundedResidueSeries Ψ B hk r kind
    (fun a : Exponent ↦ (a : ℝ)) p

private def exponentOf {k : ℕ}
    (x : Option (Fin k × Exponent)) : Exponent :=
  match x with
  | none => defaultExponent
  | some p => p.2

private def supportExponents {k : ℕ}
    (s : Finset (Option (Fin k × Exponent))) : Finset Exponent :=
  s.image exponentOf

private abbrev FiniteExponent {k : ℕ}
    (s : Finset (Option (Fin k × Exponent))) :=
  {a : Exponent // a ∈ supportExponents s}

private def restrictIndex {k : ℕ}
    (s : Finset (Option (Fin k × Exponent)))
    (x : {x // x ∈ s}) : Option (Fin k × FiniteExponent s) :=
  match h : x.1 with
  | none => none
  | some p => some (p.1, ⟨p.2, by
      apply mem_image.mpr
      exact ⟨x.1, x.2, by simp only [exponentOf, h]⟩⟩)

private def forgetIndex {k : ℕ}
    (s : Finset (Option (Fin k × Exponent))) :
    Option (Fin k × FiniteExponent s) → Option (Fin k × Exponent) :=
  Option.map (fun p => (p.1, p.2.1))

private theorem forgetIndex_restrictIndex {k : ℕ}
    (s : Finset (Option (Fin k × Exponent))) (x : {x // x ∈ s}) :
    forgetIndex s (restrictIndex s x) = x.1 := by
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

private theorem restrictIndex_injective {k : ℕ}
    (s : Finset (Option (Fin k × Exponent))) :
    Function.Injective (restrictIndex s) := by
  intro x y hxy
  apply Subtype.ext
  calc
    x.1 = forgetIndex s (restrictIndex s x) := (forgetIndex_restrictIndex s x).symm
    _ = forgetIndex s (restrictIndex s y) := congrArg (forgetIndex s) hxy
    _ = y.1 := forgetIndex_restrictIndex s y

private theorem finiteExponent_value_injective {k : ℕ}
    (s : Finset (Option (Fin k × Exponent))) :
    Function.Injective (fun a : FiniteExponent s ↦ (a.1 : ℝ)) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact hab

/-- `1` and every residue/exponent member of the entire rounded moving-rough
family are rationally linearly independent.  All analytic inputs are the
actual moving-rough slope and weighted-derivative hypotheses; every finite
restriction uses the same `κ`. -/
theorem one_movingRoughRoundedInfiniteSeries_linearIndependent
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    LinearIndependent ℚ
      (fun x : Option (Fin k × Exponent) ↦ match x with
        | none => (1 : ℝ)
        | some p => movingRoughRoundedInfiniteSeries Ψ B hk r kind p) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let alpha : FiniteExponent s → ℝ := fun a ↦ (a.1 : ℝ)
  have halpha : ∀ a, 0 < alpha a ∧ alpha a ≤ 1 := by
    intro a
    exact ⟨a.1.2.1, a.1.2.2⟩
  have hinj : Function.Injective alpha := finiteExponent_value_injective s
  have hfinite := movingRoughRoundedResidue_one_linearIndependent
    hSlope hC hreg hB hk r kind alpha halpha hinj hκ
  have hcomp := hfinite.comp (restrictIndex s) (restrictIndex_injective s)
  convert hcomp using 1
  funext x
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

end

end PrimeGapNormality.Prime.CoreRoundedRoughInfiniteFamily
