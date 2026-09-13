import PrimeGapNormality.Prime.CoreRoughForumThreshold

/-!
# Explicit logarithmic-slope local-polynomial classification

The saved September10 post includes the full local-polynomial rough
classification, not only the position series. Here its literal natural
cutoff is floor(n^(c/log log n)). The common profile budget is fixed by c
before any polynomial or Fourier combination is selected.

The sufficient coefficient 1000000 is conservative, independent of width
and period. It is a vanishing exponent, not fixed-power roughness.
Source pending central compilation.
-/

namespace PrimeGapNormality.Prime.CoreRoughLogSlopeClassification

open CoreCyclic CoreMovingRoughSequence CoreRoughLogSlopeProfile
open CoreRoughLocalNormality
open scoped Classical

noncomputable section

def profileBudget (c : ℝ) : ℝ := 1 / (1000000 * c)

theorem profileBudget_pos {c : ℝ} (hc : 0 < c) : 0 < profileBudget c := by
  unfold profileBudget
  positivity

theorem actual_slope_budget {c : ℝ} (hc : 0 < c) :
    CoreRoughThreshold.HasSlopeBudget (profile c) (1000000 * profileBudget c) := by
  have hA : 0 < 1000000 * profileBudget c :=
    mul_pos (by norm_num) (profileBudget_pos hc)
  have hAc : (1000000 * profileBudget c) * c = 1 := by
    unfold profileBudget
    field_simp [hc.ne']
  exact hasSlopeBudget hc hA (le_of_eq hAc)

theorem degree_budget {B d : ℕ} (hB : 2 ≤ B) {c : ℝ} (hc : 0 < c)
    (hsmall : 1000000 * c * (d : ℝ) ≤ Real.log (B : ℝ)) :
    (d : ℝ) / Real.log (B : ℝ) ≤ profileBudget c := by
  have hlog : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hden : 0 < 1000000 * c := mul_pos (by norm_num) hc
  unfold profileBudget
  apply (div_le_div_iff₀ hlog hden).2
  nlinarith only [hsmall]

/-- Literal series on the explicitly displayed rough threshold. -/
def localSeries (c : ℝ) (B : ℕ) {k : ℕ} (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) : ℝ :=
  coreCyclicFullSeries B hk phase
    (fun n ↦ (seqGap (movingRoughSequence (CoreRoughForumThreshold.cutoff c)) n : ℝ)) F

theorem rational_iff_normalForm_zero
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) {c : ℝ} (hc : 0 < c)
    (hsmall : 1000000 * c * (topDegree (normalForm hB hk F) : ℝ) ≤
      Real.log (B : ℝ)) :
    (∃ q : ℚ, localSeries c B hk phase F = (q : ℝ)) ↔ normalForm hB hk F = 0 := by
  simpa only [localSeries, CoreRoughForumThreshold.cutoff_eq] using
    movingRough_local_rational_iff_normalForm_zero
      (profileBudget_pos hc) (actual_slope_budget hc) (by norm_num : (0 : ℝ) ≤ 1)
      (weightedDerivative hc) hB hk phase F (degree_budget hB hc hsmall)

/-- Exact rational-or-normal classification for the explicit cutoff.
The effective degree, rather than the original syntactic degree, enters
the same fixed slope bound. -/
theorem classification
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) {c : ℝ} (hc : 0 < c)
    (hsmall : 1000000 * c * (topDegree (normalForm hB hk F) : ℝ) ≤
      Real.log (B : ℝ)) :
    (normalForm hB hk F = 0 ∧ ∃ q : ℚ, localSeries c B hk phase F = (q : ℝ)) ∨
      (normalForm hB hk F ≠ 0 ∧
        weylCriterion (B ^ k) (localSeries c B hk phase F) ∧
        PrimeGapNormality.BFree.IsNormal (B ^ k) (localSeries c B hk phase F) ∧
        PrimeGapNormality.BFree.IsNormal B (localSeries c B hk phase F)) := by
  simpa only [localSeries, CoreRoughForumThreshold.cutoff_eq] using
    movingRough_local_classification
      (profileBudget_pos hc) (actual_slope_budget hc) (by norm_num : (0 : ℝ) ≤ 1)
      (weightedDerivative hc) hB hk phase F (degree_budget hB hc hsmall)

/-- One common c-dependent arithmetic budget covers the whole finite
family; only algebraic independence of the normal forms is required. -/
theorem jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I] {B k d : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k) (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hind : LinearIndependent ℚ (fun i ↦ normalForm hB hk (F i)))
    {c : ℝ} (hc : 0 < c)
    (hsmall : 1000000 * c * (d : ℝ) ≤ Real.log (B : ℝ)) :
    JointWeyl (fun _ : I ↦ B ^ k) (fun i ↦ localSeries c B hk phase (F i)) := by
  simpa only [localSeries, CoreRoughForumThreshold.cutoff_eq] using
    movingRough_jointWeyl
      (profileBudget_pos hc) (actual_slope_budget hc) (by norm_num : (0 : ℝ) ≤ 1)
      (weightedDerivative hc) hB hk phase F hdeg hind (degree_budget hB hc hsmall)

end
end PrimeGapNormality.Prime.CoreRoughLogSlopeClassification
