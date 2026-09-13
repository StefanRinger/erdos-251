import PrimeGapNormality.Prime.CoreGeneralPositiveDensityExclusion
import PrimeGapNormality.Prime.CoreGeneralRealCutoff
import PrimeGapNormality.BFree.Squarefree

/-!
# Positive-density B-free sequences lie outside the diverging-gap criterion

The canonical B-free enumeration has the already proved density `rho F > 0`.
This file identifies its generic `seqCount` exactly with the existing B-free
count on `[1,X]`, then applies the sequence-generic positive-density exclusion.
No tail estimate, B-free normality statement, or density assumption is added.

The final specialization is the literal zero-based enumeration
`Nat.nth Squarefree`; paper index one is Lean index zero.
-/

namespace PrimeGapNormality.Prime.CoreBFreeDensityExclusion

open Filter Finset MeasureTheory
open PrimeGapNormality.BFree
open CoreGeneralSequenceST CoreCalibratedMixtureFiniteSupport
open scoped Classical Topology

noncomputable section

/-- The generic sequence count of the canonical B-free enumeration is exactly
the existing count of B-free integers in `[1,X]`. -/
theorem seqCount_enum_eq_bfree_card (F : AdmissibleFamily) (X : ℕ) :
    seqCount (enum F) X = ((Finset.Icc 1 X).filter (BFree F)).card := by
  apply eq_of_forall_lt_iff
  intro n
  rw [seqCount_lt_iff (enum_strictMono F)]
  have hiff := Nat.lt_nth_iff_count_lt (p := BFree F) (bfree_infinite F)
    (a := n) (b := X + 1)
  rw [count_bfree_succ] at hiff
  simpa only [enum, Nat.lt_succ_iff] using hiff.symm

/-- The actual canonical B-free enumeration has density `rho F` in the
`seqCount` convention used by the general S/T criterion. -/
theorem tendsto_seqCount_enum_div (F : AdmissibleFamily) :
    Tendsto (fun X : ℕ ↦ (seqCount (enum F) X : ℝ) / (X : ℝ))
      atTop (𝓝 (rho F)) := by
  simpa only [seqCount_enum_eq_bfree_card] using tendsto_card_bfree_div F

/-- Every canonical B-free enumeration is excluded from calibrated complex
pattern S at a diverging gap scale. Its positive density is a theorem, not an
endpoint premise. -/
theorem enum_not_complexPatternS
    (F : AdmissibleFamily) {κ : ℝ} (hκ : 0 < κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G) :
    ¬ ComplexPatternS (enum F) κ G ω :=
  CoreGeneralPositiveDensityExclusion.not_complexPatternS_of_positive_density
    (enum_strictMono F) (rho_pos F) (tendsto_seqCount_enum_div F)
    hκ hG hω hsum hcal

/-- The same exclusion for an arbitrary real-cutoff probability family.
The floor pushforward and its finite support are supplied by the actual
real-cutoff adapter; no density or tail premise is added. -/
theorem enum_not_realPatternS
    (F : AdmissibleFamily) {κ : ℝ} (hκ : 0 < κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (mu : ℕ → ProbabilityMeasure ℝ)
    (hcal : CoreGeneralRealCutoff.Calibration mu G) :
    ¬ CoreGeneralRealCutoff.PatternS (enum F) κ G mu := by
  intro hS
  exact (enum_not_complexPatternS F hκ hG
    (ω := CoreGeneralRealCutoff.weights mu)
    (fun X y ↦ CoreCalibratedRealCutoff.real_weights_nonneg (mu X) y)
    (fun X ↦ CoreCalibratedRealCutoff.real_weights_sum (mu X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae mu G hcal))
    (CoreGeneralRealCutoff.patternS_nat hG hcal hS)

/-! ## Literal squarefree specialization -/

private theorem nth_squarefree_eq_enum :
    Nat.nth Squarefree = enum squareModuliFamily := by
  funext n
  exact (enum_squareModuli_eq_nth_squarefree n).symm

/-- Exact squarefree count identity in the generic sequence convention. -/
theorem seqCount_nth_squarefree_eq_card (X : ℕ) :
    seqCount (Nat.nth Squarefree) X =
      ((Finset.Icc 1 X).filter Squarefree).card := by
  rw [nth_squarefree_eq_enum, seqCount_enum_eq_bfree_card,
    bfree_squareModuli_eq_squarefree]
  congr 1
  ext n
  simp only [Finset.mem_filter]

/-- The literal zero-based squarefree enumeration has the proved positive
density `rho squareModuliFamily`. -/
theorem tendsto_seqCount_nth_squarefree_div :
    Tendsto (fun X : ℕ ↦ (seqCount (Nat.nth Squarefree) X : ℝ) / (X : ℝ))
      atTop (𝓝 (rho squareModuliFamily)) := by
  rw [nth_squarefree_eq_enum]
  exact tendsto_seqCount_enum_div squareModuliFamily

/-- The paper's squarefree example cannot satisfy complex pattern S at any
calibrated scale tending to infinity. No tail or density hypothesis survives
in this public specialization. -/
theorem nth_squarefree_not_complexPatternS
    {κ : ℝ} (hκ : 0 < κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G) :
    ¬ ComplexPatternS (Nat.nth Squarefree) κ G ω := by
  have hrho : 0 < rho squareModuliFamily :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans rho_squareModuli_gt_half
  apply CoreGeneralPositiveDensityExclusion.not_complexPatternS_of_positive_density
    (d := rho squareModuliFamily)
  · rw [nth_squarefree_eq_enum]
    exact enum_strictMono squareModuliFamily
  · exact hrho
  · exact tendsto_seqCount_nth_squarefree_div
  · exact hκ
  · exact hG
  · exact hω
  · exact hsum
  · exact hcal

/-- Literal real-cutoff version of the squarefree exclusion. -/
theorem nth_squarefree_not_realPatternS
    {kappa : ℝ} (hkappa : 0 < kappa)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (mu : ℕ → ProbabilityMeasure ℝ)
    (hcal : CoreGeneralRealCutoff.Calibration mu G) :
    ¬ CoreGeneralRealCutoff.PatternS (Nat.nth Squarefree) kappa G mu := by
  rw [nth_squarefree_eq_enum]
  exact enum_not_realPatternS squareModuliFamily hkappa hG mu hcal

end

end PrimeGapNormality.Prime.CoreBFreeDensityExclusion
