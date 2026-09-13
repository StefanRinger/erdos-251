import PrimeGapNormality.Prime.CoreGeneralRoundedFamily

/-! The entire residue/exponent family: every rational relation has finite
support. No infinite-dimensional distribution is asserted. -/
namespace PrimeGapNormality.Prime.CoreGeneralRoundedInfinite
open Finset Filter MeasureTheory CoreCyclic CoreRoundedPowerScaling
open CoreGeneralRoundedFamily CoreGeneralSequenceST CoreSequenceSTMeanTail
open CoreCalibratedMixtureFiniteSupport
open scoped Classical Topology
noncomputable section

abbrev Exponent := Set.Ioc (0 : ℝ) 1
def entireSeries (a : ℕ → ℕ) (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (p : Fin k × Exponent) : ℝ :=
  residueSeries a B hk r kind (fun x : Exponent => (x : ℝ)) p

private def exponentOf {k : ℕ} (x : Option (Fin k × Exponent)) : Exponent :=
  match x with
  | none => ⟨1, by simp⟩
  | some p => p.2
private def supportExponents {k : ℕ} (s : Finset (Option (Fin k × Exponent))) : Finset Exponent :=
  s.image exponentOf
private abbrev FiniteExponent {k : ℕ} (s : Finset (Option (Fin k × Exponent))) :=
  {x : Exponent // x ∈ supportExponents s}
private def restrictIndex {k : ℕ} (s : Finset (Option (Fin k × Exponent)))
    (x : {x // x ∈ s}) : Option (Fin k × FiniteExponent s) :=
  match h : x.1 with
  | none => none
  | some p => some (p.1, ⟨p.2, by
      exact mem_image.2 ⟨x.1, x.2, by simp only [exponentOf, h]⟩⟩)

private def forgetIndex {k : ℕ}
    (s : Finset (Option (Fin k × Exponent))) :
    Option (Fin k × FiniteExponent s) → Option (Fin k × Exponent) :=
  Option.map (fun p => (p.1, p.2.1))

private theorem forgetIndex_restrictIndex {k : ℕ}
    (s : Finset (Option (Fin k × Exponent))) (x : {x // x ∈ s}) :
    forgetIndex s (restrictIndex s x) = x.1 := by
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

private theorem restrictIndex_injective {k : ℕ} (s : Finset (Option (Fin k × Exponent))) :
    Function.Injective (restrictIndex s) := by
  intro x y hxy
  apply Subtype.ext
  calc
    x.1 = forgetIndex s (restrictIndex s x) := (forgetIndex_restrictIndex s x).symm
    _ = forgetIndex s (restrictIndex s y) := congrArg (forgetIndex s) hxy
    _ = y.1 := forgetIndex_restrictIndex s y

theorem one_entireSeries_linearIndependent
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    LinearIndependent ℚ (fun x : Option (Fin k × Exponent) => match x with
      | none => (1 : ℝ)
      | some p => entireSeries a B hk r kind p) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let alpha : FiniteExponent s → ℝ := fun x => (x.1 : ℝ)
  have hα : ∀ x, 0 < alpha x ∧ alpha x ≤ 1 := fun x => x.1.2
  have hinj : Function.Injective alpha := fun x y h => Subtype.ext (Subtype.ext h)
  have hfinite := residue_one_linearIndependent ha hB hk r kind alpha hα hinj hκ hG hω hsum hcal hS hT
  have hcomp := hfinite.comp (restrictIndex s) (restrictIndex_injective s)
  convert hcomp using 1
  funext x
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

theorem one_entireSeries_linearIndependent_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) (μ : ℕ → ProbabilityMeasure ℝ)
    (hcal : CoreGeneralRealCutoff.Calibration μ G) (hS : CoreGeneralRealCutoff.PatternS a κ G μ)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    LinearIndependent ℚ (fun x : Option (Fin k × Exponent) => match x with
      | none => (1 : ℝ)
      | some p => entireSeries a B hk r kind p) :=
  one_entireSeries_linearIndependent ha hB hk r kind hκ hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRealCutoff.patternS_nat hG hcal hS) hT

end
end PrimeGapNormality.Prime.CoreGeneralRoundedInfinite
