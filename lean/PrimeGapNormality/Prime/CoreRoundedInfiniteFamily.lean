import PrimeGapNormality.Prime.CoreRoundedPrimeFamily

/-!
# The entire rounded exponent family

Every linear relation has finite support.  For such a support we collect
its finite set of exponents, apply the actual finite-family theorem to all
residue labels over that set, and restrict along an injective map.  This
proves Q-linear independence of `1` and the whole family indexed by
`Fin k × Set.Ioc 0 1`.

This is only an algebraic finite-restriction conclusion.  No infinite
product Haar measure or infinite-dimensional joint distribution is claimed.
One fixed `RoundKind` is used throughout, so floors and ceilings remain
separate assertions.
-/

namespace PrimeGapNormality.Prime.CoreRoundedInfiniteFamily

open Finset CoreCyclic CoreRoundedPowerScaling
open CoreRoundedPrimeFamily
open scoped Classical

noncomputable section

abbrev Exponent := Set.Ioc (0 : ℝ) 1

private def defaultExponent : Exponent := ⟨1, by simp⟩

/-- Literal entire residue/exponent family. -/
def roundedInfiniteSeries
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (p : Fin k × Exponent) : ℝ :=
  roundedResidueSeries B hk r kind (fun a : Exponent => (a : ℝ)) p

private def exponentOf {k : ℕ} (x : Option (Fin k × Exponent)) : Exponent :=
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
    Function.Injective (fun a : FiniteExponent s => (a.1 : ℝ)) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact hab

/-- Fixed-D form of independence for `1` and the entire uncountable
residue/exponent family. -/
theorem one_roundedInfiniteSeries_linearIndependent_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) {κ d0 c : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    LinearIndependent ℚ (fun x : Option (Fin k × Exponent) => match x with
      | none => (1 : ℝ)
      | some p => roundedInfiniteSeries B hk r kind p) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let alpha : FiniteExponent s → ℝ := fun a => (a.1 : ℝ)
  have halpha : ∀ a, 0 < alpha a ∧ alpha a ≤ 1 := by
    intro a
    exact ⟨a.1.2.1, a.1.2.2⟩
  have hinj : Function.Injective alpha := finiteExponent_value_injective s
  have hfinite := roundedResidue_one_linearIndependent_of_D
    hB hk r kind alpha halpha hinj hκ hd0 hc hD
  have hcomp := hfinite.comp (restrictIndex s) (restrictIndex_injective s)
  convert hcomp using 1
  funext x
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

/-- Kuperberg supplies the same fixed κ to every finite restriction, hence
to the entire family. -/
theorem one_roundedInfiniteSeries_linearIndependent_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hK : KuperbergConj13) :
    LinearIndependent ℚ (fun x : Option (Fin k × Exponent) => match x with
      | none => (1 : ℝ)
      | some p => roundedInfiniteSeries B hk r kind p) := by
  have hκpos : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  exact one_roundedInfiniteSeries_linearIndependent_of_D hB hk r kind hκ
    (by norm_num) (by norm_num) (coreLinearD_of_kuperberg hK hκpos)

/-- Small-window AHL version, again with one fixed κ for the whole family. -/
theorem one_roundedInfiniteSeries_linearIndependent_of_AHL
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) {κ : ℝ} (hκpos : 0 < κ)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hAHL : ahlSmall_AHL κ 20) :
    LinearIndependent ℚ (fun x : Option (Fin k × Exponent) => match x with
      | none => (1 : ℝ)
      | some p => roundedInfiniteSeries B hk r kind p) :=
  one_roundedInfiniteSeries_linearIndependent_of_D hB hk r kind hκ
    (by norm_num) (by norm_num)
    (CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκpos hAHL)

end

end PrimeGapNormality.Prime.CoreRoundedInfiniteFamily
