import PrimeGapNormality.Prime.CoreRoughLocalNormality
import PrimeGapNormality.Prime.CoreOneGapWeights
import PrimeGapNormality.Prime.CoreRationalAffine

/-!
# The literal moving-rough position series

For an arbitrary increasing sequence `a`, the exact Abel identity is

`gapSeries B a = (B - 1) * positionSeries B a - a 0`.

For the moving-rough enumeration, convergence follows from the proved global
quadratic majorant.  The one-gap tuple in `CoreRoughLocalNormality` gives Weyl
cancellation for the gap series; the displayed rational affine identity then
gives Weyl cancellation, irrationality, and base-`B` normality of the literal
position series.  No prime-only series theorem is used.
-/

namespace PrimeGapNormality.Prime.CoreRoughPositionEnd

open Filter MvPolynomial CoreCyclic
open CoreRoughThreshold CoreRoughSyntheticScale CoreMovingRoughSequence
open CoreMovingRoughPolynomialGrowth CoreSequenceAdjacentWindowTail
open scoped Topology Classical

noncomputable section

private def singletonPhase : Fin 1 := ⟨0, by omega⟩

/-- Literal position series of an arbitrary natural-valued sequence. -/
def sequencePositionSeries (B : ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (a n : ℝ) / (B : ℝ) ^ (n + 1)

/-- Literal first-gap series of an arbitrary natural-valued sequence. -/
def sequenceGapSeries (B : ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (seqGap a n : ℝ) / (B : ℝ) ^ (n + 1)

/-- The actual moving-rough position series requested in the paper. -/
def movingRoughPositionSeries (Ψ : ℝ → ℝ) (B : ℕ) : ℝ :=
  sequencePositionSeries B (movingRoughSequence (zPsi Ψ))

/-- A quadratic position majorant supplies absolute convergence of the
literal position series. -/
theorem sequencePositionSeries_summable_of_quadratic
    {a : ℕ → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ n : ℕ, (a n : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) ^ 2))
    {B : ℕ} (hB : 2 ≤ B) :
    Summable (fun n : ℕ ↦ (a n : ℝ) / (B : ℝ) ^ (n + 1)) := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  have hbase := sequence_div_pow_summable_of_quadratic hC hquad hBreal
  simpa only [Nat.zero_add] using summable_posMass_terms hBreal hbase 0

/-- Exact Abel identity for every strictly increasing natural sequence with
the displayed geometric summability. -/
theorem sequenceGapSeries_eq_mul_position_sub
    {a : ℕ → ℕ} (ha : StrictMono a) {B : ℕ} (hB : 2 ≤ B)
    (hsm : Summable (fun n : ℕ ↦ (a n : ℝ) / (B : ℝ) ^ n)) :
    sequenceGapSeries B a =
      ((B : ℝ) - 1) * sequencePositionSeries B a - (a 0 : ℝ) := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  have hgap : (fun n : ℕ ↦ (seqGap a n : ℝ)) =
      fun n ↦ (a (n + 1) : ℝ) - (a n : ℝ) := by
    funext n
    unfold seqGap
    rw [Nat.cast_sub (ha.monotone (Nat.le_succ n))]
  have hab := posMass_eq_add_gapTail hBreal (fun n ↦ (a n : ℝ)) hsm 0
  rw [← hgap] at hab
  have hab' : sequencePositionSeries B a =
      ((a 0 : ℝ) + sequenceGapSeries B a) / ((B : ℝ) - 1) := by
    simpa only [sequencePositionSeries, sequenceGapSeries, posMass, gapTail,
      Nat.zero_add] using hab
  have hden : (B : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < B := hBreal
    linarith
  rw [eq_div_iff hden] at hab'
  linarith

/-- The concrete one-gap cyclic series is exactly the literal sequence gap
series (period one, coefficient one). -/
theorem coreOneGapSeries_eq_sequenceGapSeries
    (B : ℕ) (a : ℕ → ℕ) :
    coreCyclicFullSeries B (by omega : 0 < 1) singletonPhase
        (fun n ↦ (seqGap a n : ℝ))
        (CoreOneGapWeights.tuple (fun _ : Fin 1 ↦ (1 : ℚ))) =
      sequenceGapSeries B a := by
  rw [CoreOneGapWeights.series_tuple]
  unfold sequenceGapSeries
  apply tsum_congr
  intro n
  simp

/-- The actual moving-rough position series is absolutely summable. -/
theorem movingRoughPositionSeries_summable
    {Ψ : ℝ → ℝ} {A : ℝ} (hSlope : HasSlopeBudget Ψ A)
    {B : ℕ} (hB : 2 ≤ B) :
    Summable (fun n : ℕ ↦
      (movingRoughSequence (zPsi Ψ) n : ℝ) / (B : ℝ) ^ (n + 1)) := by
  obtain ⟨Cnat, hquadNat⟩ := exists_global_quadratic_bound
    hSlope.eventually_zPsi_lt
  apply sequencePositionSeries_summable_of_quadratic (C := (Cnat : ℝ))
    (Nat.cast_nonneg _)
  · intro n
    exact_mod_cast hquadNat n
  · exact hB

/-- The literal moving-rough gap series has Weyl cancellation by the actual
degree-one local theorem. -/
theorem movingRoughGapSeries_weyl
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    weylCriterion B (sequenceGapSeries B (movingRoughSequence (zPsi Ψ))) := by
  let d : Fin 1 → ℚ := fun _ ↦ 1
  let F : PeriodicLocal 1 := CoreOneGapWeights.tuple d
  have hd : d ≠ 0 := by
    intro hz
    have hh := congrFun hz singletonPhase
    simp only [d, Pi.zero_apply, one_ne_zero] at hh
  have hnf : normalForm hB (by omega : 0 < 1) F ≠ 0 := by
    dsimp only [F]
    rw [CoreOneGapWeights.normalForm_tuple hB (by omega : 0 < 1)]
    exact CoreOneGapWeights.ne_zero d hd
  have hdegree : topDegree (normalForm hB (by omega : 0 < 1) F) = 1 := by
    dsimp only [F]
    rw [CoreOneGapWeights.normalForm_tuple hB (by omega : 0 < 1)]
    exact CoreOneGapWeights.degree_eq_one (by omega : 0 < 1) d hd
  have hclass := CoreRoughLocalNormality.movingRough_local_classification
    hκpos hSlope hC hreg hB (by omega : 0 < 1)
    singletonPhase F (by simpa only [hdegree, Nat.cast_one] using hκ)
  have hcore : weylCriterion B
      (coreCyclicFullSeries B (by omega : 0 < 1) singletonPhase
        (fun n ↦ (seqGap (movingRoughSequence (zPsi Ψ)) n : ℝ)) F) := by
    rcases hclass with hzero | hnormal
    · exact False.elim (hnf hzero.1)
    · simpa only [pow_one] using hnormal.2.1
  rw [show F = CoreOneGapWeights.tuple (fun _ : Fin 1 ↦ (1 : ℚ)) by rfl,
    coreOneGapSeries_eq_sequenceGapSeries] at hcore
  exact hcore

/-- Exact Abel identity for the actual moving-rough sequence. -/
theorem movingRoughGapSeries_eq_mul_position_sub
    {Ψ : ℝ → ℝ} {A : ℝ} (hSlope : HasSlopeBudget Ψ A)
    {B : ℕ} (hB : 2 ≤ B) :
    sequenceGapSeries B (movingRoughSequence (zPsi Ψ)) =
      ((B : ℝ) - 1) * movingRoughPositionSeries Ψ B -
        (movingRoughSequence (zPsi Ψ) 0 : ℝ) := by
  let a := movingRoughSequence (zPsi Ψ)
  obtain ⟨Cnat, hquadNat⟩ := exists_global_quadratic_bound
    hSlope.eventually_zPsi_lt
  have hquad : ∀ n : ℕ, (a n : ℝ) ≤
      (Cnat : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    dsimp only [a]
    exact_mod_cast hquadNat n
  have hsm := sequence_div_pow_summable_of_quadratic
    (Nat.cast_nonneg Cnat) hquad
    (show (1 : ℝ) < B by exact_mod_cast (show 1 < B by omega))
  simpa only [a, movingRoughPositionSeries] using
    sequenceGapSeries_eq_mul_position_sub
      (movingRoughSequence_strictMono hSlope.eventually_zPsi_lt) hB hsm

/-- Weyl cancellation for the literal moving-rough position series. -/
theorem movingRoughPositionSeries_weyl
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    weylCriterion B (movingRoughPositionSeries Ψ B) := by
  have hgap := movingRoughGapSeries_weyl hκpos hSlope hC hreg hB hκ
  have hadd := weylCriterion_add_int
    (movingRoughSequence (zPsi Ψ) 0 : ℤ) hgap
  apply weylCriterion_of_mul (q := B - 1) (by omega) hB
  have heq : ((B - 1 : ℕ) : ℝ) * movingRoughPositionSeries Ψ B =
      sequenceGapSeries B (movingRoughSequence (zPsi Ψ)) +
        ((movingRoughSequence (zPsi Ψ) 0 : ℤ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_one,
      movingRoughGapSeries_eq_mul_position_sub hSlope hB]
    push_cast
    ring
  rwa [heq]

theorem movingRoughPositionSeries_irrational
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    Irrational (movingRoughPositionSeries Ψ B) :=
  weylCriterion_irrational
    (movingRoughPositionSeries_weyl hκpos hSlope hC hreg hB hκ)

theorem movingRoughPositionSeries_normal
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ} (hκpos : 0 < κ)
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative
      Ψ dΨ C)
    {B : ℕ} (hB : 2 ≤ B)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    PrimeGapNormality.BFree.IsNormal B (movingRoughPositionSeries Ψ B) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (movingRoughPositionSeries_weyl hκpos hSlope hC hreg hB hκ)

end
end PrimeGapNormality.Prime.CoreRoughPositionEnd
