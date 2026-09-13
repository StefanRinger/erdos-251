import PrimeGapNormality.Prime.CoreAHLToD
import PrimeGapNormality.Prime.CorePrimeLocalClassification
import PrimeGapNormality.Prime.CoreLocalRelations
import PrimeGapNormality.Prime.CorePeriodicPositionEnd

/-! Frozen small-window, one-sided averaged prime-tuples input.
These endpoints use its proved D adapter, not a large-window replacement
or an extra normalization/model hypothesis. Acceptance additionally requires
the separately pinned classical PNT import and its transitive axiom audit.
-/

namespace PrimeGapNormality.Prime.CorePrimeLocalAHL
open CoreCyclic
noncomputable section

theorem isNormal {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    {κ : ℝ} (hκ : 0 < κ)
    (hdeg : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hAHL : ahlSmall_AHL κ 20) :
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) :=
  corePrime_local_isNormal_of_D hB hk phase F hF hdeg (by norm_num) (by norm_num)
    (CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκ hAHL)

theorem isNormal_clock {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    {κ : ℝ} (hκ : 0 < κ)
    (hdeg : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hAHL : ahlSmall_AHL κ 20) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F) :=
  corePrime_local_isNormal_clock_of_D hB hk phase F hF hdeg (by norm_num) (by norm_num)
    (CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκ hAHL)

theorem rational_iff {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) {κ : ℝ} (hκ : 0 < κ)
    (hdeg : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hAHL : ahlSmall_AHL κ 20) :
    (∃ q : ℚ, coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) F = (q : ℝ)) ↔
      normalForm hB hk F = 0 :=
  corePrime_local_rational_iff_normalForm_zero_of_D hB hk phase F hdeg
    (by norm_num) (by norm_num) (CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκ hAHL)

theorem jointWeyl {I : Type*} [Fintype I] [DecidableEq I]
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i ↦ normalForm hB hk (F i)))
    {κ : ℝ} (hκ : 0 < κ) (hbudget : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hAHL : ahlSmall_AHL κ 20) :
    JointWeyl (fun _ : I ↦ B ^ k)
      (fun i ↦ coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ)) (F i)) :=
  CoreLocalRelations.jointWeyl_of_independent_normalForms_of_D
    hB hk phase F hdeg hlin hbudget (by norm_num) (by norm_num)
    (CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκ hAHL)

theorem periodicPosition_isNormal {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Function.Periodic c k) (hc0 : c ≠ 0)
    {κ : ℝ} (hκ : 0 < κ) (hbudget : 1 / Real.log (B : ℝ) ≤ κ)
    (hAHL : ahlSmall_AHL κ 20) :
    PrimeGapNormality.BFree.IsNormal B
      (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) :=
  CorePeriodicPositionEnd.primePositionSeries_isNormal_of_D
    hB hk c hc hc0 hbudget (by norm_num) (by norm_num)
    (CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκ hAHL)

end
end PrimeGapNormality.Prime.CorePrimeLocalAHL
