import PrimeGapNormality.Prime.CoreRoughIntegerTupleCount
import PrimeGapNormality.Prime.CoreRoughEveryWindow
import PrimeGapNormality.Prime.CoreRoughLocalNormality

/-! One shared choice for the existential constants in the V1 rough appendix.
The paper does not prescribe the smallest possible sieve constant Cβ.  The
choice below keeps its displayed formula literally and supplies both the
million-slope classification and the two-million-slope every-window theorem.
-/
namespace PrimeGapNormality.Prime.CoreRoughConstants

open Filter Finset CoreRoughThreshold CoreRoughIntegerTupleCount
  CoreRoughEveryWindow CoreMovingRoughSequence CoreCyclic
open scoped Topology Classical
noncomputable section

def betaConstant : ℝ := 12500
def crtConstant : ℝ := 10
def momentExponent : ℝ := 5 + 1 + Real.log 5
def paperConstant : ℝ :=
  8 * (max (9 * 20) (betaConstant * 20 + momentExponent) + 3)

theorem paperConstant_ge_everyWindow : 2000000 ≤ paperConstant := by
  have hlog : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hm := le_max_right (9 * 20 : ℝ) (betaConstant * 20 + momentExponent)
  dsimp [paperConstant, betaConstant, momentExponent] at *
  linarith

theorem paperConstant_pos : 0 < paperConstant :=
  lt_of_lt_of_le (by norm_num) paperConstant_ge_everyWindow

/-- The very same enlarged beta witness is valid for the actual finite
integer-interval sieve, with all signed shifts and real cutoffs retained. -/
theorem integer_sieve_bound (E : Finset ℤ) (hE : 1 ≤ E.card)
    {y R : ℝ} (hy : 4 * (E.card : ℝ) < y)
    (hlevel : ((⌊y⌋₊ : ℝ) + 1 / 2) ^ (9 * E.card + 1) ≤ R)
    (a : ℤ) (H : ℕ) :
    |((integerAvoidedIntervalReal E y (a : ℝ) H).card : ℝ) -
        (H : ℝ) * integerTupleSieveProduct E ⌊y⌋₊| ≤
      (H : ℝ) * integerTupleSieveProduct E ⌊y⌋₊ *
        Real.exp (betaConstant * (E.card : ℝ) -
          Real.log R / Real.log ((⌊y⌋₊ : ℝ) + 1 / 2)) +
      Real.exp (crtConstant * (E.card : ℝ)) * R *
        (1 + Real.log R) ^ (E.card - 1) := by
  apply (integerAvoidedInterval_error_realCutoff E hE hy hlevel a H).trans
  dsimp only [crtConstant]
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    dsimp [betaConstant]
    nlinarith [Nat.cast_nonneg (α := ℝ) E.card]
  · apply mul_nonneg (Nat.cast_nonneg H)
    rw [← tupleProduct_normalizedShifts]
    exact finiteTupleSieveProduct_nonneg _ _

theorem slopeBudget_mono {Ψ : ℝ → ℝ} {A A' : ℝ}
    (h : HasSlopeBudget Ψ A) (hA' : 0 < A') (hAA' : A' ≤ A) :
    HasSlopeBudget Ψ A' := by
  refine ⟨hA', h.2.1, ?_⟩
  filter_upwards [h.2.2, h.2.1.eventually_ge_atTop 1] with t ht hΨ
  have hlog : 0 ≤ Real.log (3 * Ψ t) := Real.log_nonneg (by linarith)
  exact (mul_le_mul_of_nonneg_right hAA' hlog).trans ht

/-- Both old endpoint budgets follow from this single paper witness.
The κ and profile are unchanged. -/
theorem paperSlope_to_verified {Ψ : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) :
    HasSlopeBudget Ψ (1000000 * κ) ∧ HasSlopeBudget Ψ (2000000 * κ) := by
  have h2 : 2000000 * κ ≤ paperConstant * κ :=
    mul_le_mul_of_nonneg_right paperConstant_ge_everyWindow hκ.le
  constructor
  · exact slopeBudget_mono hSlope (by positivity) (by linarith)
  · exact slopeBudget_mono hSlope (by positivity) h2

/-- Literal first-M complex prefix comparison for EVERY deterministic paper
window, with the universal constant chosen before κ, M, and the test. -/
theorem every_window {Ψ dΨ : ℝ → ℝ} {κ C D : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (M : ℕ → ℕ) (hD : 0 ≤ D)
    (hM : ∀ᶠ X : ℕ in atTop, |(M X : ℝ) - κ * logGap Ψ X| ≤
      D * Real.sqrt (logGap Ψ X)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ f : Finset ℕ → ℂ,
      (∀ K ∈ (offsetWindow (smallSpan Ψ M X)).powerset.filter (fun K => K.card = M X),
        ‖f K‖ ≤ 1) →
      ‖prefixMean (movingRoughSequence (zPsi Ψ)) X (smallSpan Ψ M X) (M X) f -
        complexMean (smallSpan Ψ M X) (M X)
          (actualRootLaw (zPsi Ψ X) (smallSpan Ψ M X)) f‖ < ε :=
  eventually_prefix_comparison_of_sqrt_error hκ
    (paperSlope_to_verified hκ hSlope).2 hC hreg M hD hM hε

theorem local_classification
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (paperConstant * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k)
    (hκ : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ) :
    (normalForm hB hk F = 0 ∧
      ∃ q : ℚ, coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) F = (q : ℝ)) ∨
    (normalForm hB hk F ≠ 0 ∧
      weylCriterion (B ^ k) (coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal (B ^ k) (coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) F) ∧
      PrimeGapNormality.BFree.IsNormal B (coreCyclicFullSeries B hk phase
        (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) F)) :=
  CoreRoughLocalNormality.movingRough_local_classification hκpos
    (paperSlope_to_verified hκpos hSlope).1 hC hreg hB hk phase F hκ

end
end PrimeGapNormality.Prime.CoreRoughConstants
