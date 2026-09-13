import PrimeGapNormality.Prime.CoreSequencePatternLaw
import PrimeGapNormality.Prime.ActualRootLaw

/-!
# Finite restriction of a large stopped shape

A smaller first-M test, zero beyond a smaller physical span, is an actual
function of a successful first-L shape whenever M <= L. The lost mass is
only large-shape failure; no small-window concentration is asserted.
The rooted sieve restriction below uses the SAME residue choice at both
physical windows, so it introduces no change of model or calibration.
-/

namespace PrimeGapNormality.Prime.CoreRoughWindowRestriction

open Finset CoreSequencePatternLaw
open scoped Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem firstL_sort (L : ℕ) (U : Finset ℕ) :
    (Stopped.firstL L U).sort (· ≤ ·) = (U.sort (· ≤ ·)).take L := by
  exact (List.toFinset_sort (· ≤ ·)
    ((U.sort_nodup (· ≤ ·)).sublist (List.take_sublist L _))).mpr
      ((pairwise_sort U (· ≤ ·)).take)

theorem firstL_firstL {M L : ℕ} (hML : M ≤ L) (U : Finset ℕ) :
    Stopped.firstL M (Stopped.firstL L U) = Stopped.firstL M U := by
  unfold Stopped.firstL at *
  rw [show (((U.sort (· ≤ ·)).take L).toFinset).sort (· ≤ ·) =
      (U.sort (· ≤ ·)).take L from firstL_sort L U]
  simp only [List.take_take, min_eq_left hML]

theorem firstL_filter_le {M S : ℕ} {U : Finset ℕ}
    (hM : M ≤ (U.filter (fun x => x ≤ S)).card) :
    Stopped.firstL M (U.filter (fun x => x ≤ S)) = Stopped.firstL M U := by
  by_cases hzero : M = 0
  · simp [hzero, Stopped.firstL]
  have hMp : 1 ≤ M := by omega
  let V := U.filter (fun x => x ≤ S)
  let K := Stopped.firstL M V
  have hMU : M ≤ U.card := hM.trans (Finset.card_le_card (filter_subset _ _))
  have hKcard : K.card = M := Stopped.firstL_card hM
  have hK : K.Nonempty := Finset.card_pos.mp (by omega)
  have hVK := (Stopped.firstL_eq_iff hK hMp hM).mp (rfl : Stopped.firstL M V = K)
  have hUK : Stopped.firstL M U = K := (Stopped.firstL_eq_iff hK hMp hMU).mpr
    ⟨hVK.1.trans (filter_subset _ _), hKcard, by
      intro x hx hxlt
      have hmax : K.max' hK ≤ S :=
        (Finset.mem_filter.mp (hVK.1 (Finset.max'_mem K hK))).2
      exact hVK.2.2 x
        (Finset.mem_filter.mpr ⟨hx, hxlt.le.trans hmax⟩) hxlt⟩
  exact hUK.symm

theorem firstL_fits_filter_iff (M S : ℕ) (U : Finset ℕ) :
    M ≤ (U.filter (fun x => x ≤ S)).card ↔
      M ≤ U.card ∧ ∀ x ∈ Stopped.firstL M U, x ≤ S := by
  constructor
  · intro hM
    refine ⟨hM.trans (Finset.card_le_card (filter_subset _ _)), ?_⟩
    intro x hx
    rw [← firstL_filter_le hM] at hx
    exact (Finset.mem_filter.mp (Stopped.firstL_subset hx)).2
  · rintro ⟨hMU, hS⟩
    have hsub : Stopped.firstL M U ⊆ U.filter (fun x => x ≤ S) :=
      fun x hx => Finset.mem_filter.mpr ⟨Stopped.firstL_subset hx, hS x hx⟩
    simpa only [Stopped.firstL_card hMU] using Finset.card_le_card hsub

/-- The actual smaller stopped observable, expressed on any larger set. -/
def cutoffValue (M S : ℕ) (f : Finset ℕ → ℝ) (U : Finset ℕ) : ℝ :=
  if M ≤ U.card ∧ ∀ x ∈ Stopped.firstL M U, x ≤ S then f (Stopped.firstL M U) else 0

theorem cutoffValue_eq_filter (M S : ℕ) (f : Finset ℕ → ℝ) (U : Finset ℕ) :
    cutoffValue M S f U = Stopped.stoppedValue M f (U.filter (fun x => x ≤ S)) := by
  unfold cutoffValue Stopped.stoppedValue
  by_cases hM : M ≤ (U.filter (fun x => x ≤ S)).card
  · have hfit := (firstL_fits_filter_iff M S U).mp hM
    simp only [if_pos hM, if_pos hfit, firstL_filter_le hM]
  · have hfit : ¬ (M ≤ U.card ∧ ∀ x ∈ Stopped.firstL M U, x ≤ S) :=
      fun h => hM ((firstL_fits_filter_iff M S U).mpr h)
    simp only [if_neg hM, if_neg hfit]

theorem cutoffValue_firstL {M L : ℕ} (hML : M ≤ L) (S : ℕ)
    (f : Finset ℕ → ℝ) {U : Finset ℕ} (hLU : L ≤ U.card) :
    cutoffValue M S f (Stopped.firstL L U) = cutoffValue M S f U := by
  simp only [cutoffValue, Stopped.firstL_card hLU, firstL_firstL hML,
    hML, hML.trans hLU, true_and]

theorem cutoffValue_abs_le (M S : ℕ) (f : Finset ℕ → ℝ)
    (hf : ∀ K, |f K| ≤ 1) (U : Finset ℕ) : |cutoffValue M S f U| ≤ 1 := by
  unfold cutoffValue
  split_ifs
  · exact hf _
  · norm_num

/-- Uniform every-smaller-rank comparison from one large stopped shape.
This does not bound failure at the SMALLER window. -/
theorem cutoff_test_abs_sub_le (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ)
    {M L : ℕ} (hML : M ≤ L) (S : ℕ) (f : Finset ℕ → ℝ)
    (hf : ∀ K, |f K| ≤ 1)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U) (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U) :
    |(∑ U ∈ Ω.powerset, μ U * cutoffValue M S f U) -
      (∑ U ∈ Ω.powerset, ν U * cutoffValue M S f U)| ≤
      Stopped.shapeL1 Ω μ ν L + Stopped.failureMass Ω μ L +
        Stopped.failureMass Ω ν L := by
  let q := cutoffValue M S f
  have hq : ∀ U, |q U| ≤ 1 := cutoffValue_abs_le M S f hf
  have hid (U : Finset ℕ) : (if L ≤ U.card then q (Stopped.firstL L U) else q U) = q U := by
    split_ifs with hLU
    · exact cutoffValue_firstL hML S f hLU
    · rfl
  have hleft := Stopped.abs_stopped_eval_sub_le (Ω := Ω) (μ := μ) (ν := ν)
    (L := L) (φ := q) (ψ := q) (fun K _ => hq K) (fun U _ => hq U) hμ
  have hright := Stopped.abs_stopped_eval_sub_le (Ω := Ω) (μ := ν) (ν := ν)
    (L := L) (φ := q) (ψ := q) (fun K _ => hq K) (fun U _ => hq U) hν
  simp_rw [hid] at hleft hright
  have hself : Stopped.shapeL1 Ω ν ν L = 0 := by simp [Stopped.shapeL1]
  rw [hself, zero_add] at hright
  have htri := abs_sub_le (∑ U ∈ Ω.powerset, μ U * q U)
    (∑ K ∈ Ω.powerset.filter (fun K => K.card = L), Stopped.shortShapeMass Ω ν L K * q K)
    (∑ U ∈ Ω.powerset, ν U * q U)
  rw [abs_sub_comm (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
      Stopped.shortShapeMass Ω ν L K * q K)] at htri
  exact htri.trans (add_le_add hleft hright)

theorem sieveSurvivorsFin_filter {s S : ℕ} (hsS : s ≤ S) (y : ℕ)
    (σ : ResidueChoice y) :
    (sieveSurvivorsFin y σ S).filter (fun x => x ≤ s) = sieveSurvivorsFin y σ s := by
  ext x
  simp only [sieveSurvivorsFin, offsetWindow, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hpos, _⟩, hsurv⟩, hsmall⟩
    exact ⟨⟨hpos, hsmall⟩, hsurv⟩
  · rintro ⟨⟨hpos, hsmall⟩, hsurv⟩
    exact ⟨⟨⟨hpos, hsmall.trans hsS⟩, hsurv⟩, hsmall⟩

theorem actualRootLaw_eval (y S : ℕ) (f : Finset ℕ → ℝ) :
    (∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U * f U) =
      (∑ σ : ResidueChoice y, f (sieveSurvivorsFin y σ S)) /
        (Fintype.card (ResidueChoice y) : ℝ) := by
  have hcard (U : Finset ℕ) :
      (((univ : Finset (ResidueChoice y)).filter
        (fun σ => sieveSurvivorsFin y σ S = U)).card : ℝ) =
      ∑ σ : ResidueChoice y, if sieveSurvivorsFin y σ S = U then (1 : ℝ) else 0 := by
    simp only [Finset.sum_boole]
  unfold actualRootLaw
  simp_rw [hcard, div_mul_eq_mul_div, sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [ite_mul, one_mul, zero_mul]
  have hmem : sieveSurvivorsFin y σ S ∈ (offsetWindow S).powerset := by
    apply Finset.mem_powerset.mpr
    exact Finset.filter_subset _ _
  rw [Finset.sum_ite_eq, if_pos hmem]

/-- Exact physical-window restriction, at the same actual cutoff. -/
theorem actualRootLaw_window_restriction {s S : ℕ} (hsS : s ≤ S) (y : ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U *
      f (U.filter (fun x => x ≤ s))) =
    ∑ U ∈ (offsetWindow s).powerset, actualRootLaw y s U * f U := by
  rw [actualRootLaw_eval, actualRootLaw_eval]
  simp_rw [sieveSurvivorsFin_filter hsS]

theorem rootedPattern_filter {s S : ℕ} (hsS : s ≤ S) (a : ℕ → ℕ) (n : ℕ) :
    (CoreSequencePatternLaw.rootedPattern a (offsetWindow S) n).filter (fun x => x ≤ s) =
      CoreSequencePatternLaw.rootedPattern a (offsetWindow s) n := by
  ext x
  simp only [CoreSequencePatternLaw.rootedPattern, CoreSequencePattern.pattern, offsetWindow,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hpos, _⟩, hsurv⟩, hsmall⟩
    exact ⟨⟨hpos, hsmall⟩, hsurv⟩
  · rintro ⟨⟨hpos, hsmall⟩, hsurv⟩
    exact ⟨⟨⟨hpos, hsmall.trans hsS⟩, hsurv⟩, hsmall⟩

/-- Exact physical restriction of the ACTUAL empirical law; the anchor
window and its denominator are unchanged, including an empty window. -/
theorem patternMass_window_restriction {s S : ℕ} (hsS : s ≤ S) (a : ℕ → ℕ) (X : ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ U ∈ (offsetWindow S).powerset, patternMass a X (offsetWindow S) U *
      f (U.filter (fun x => x ≤ s))) =
    ∑ U ∈ (offsetWindow s).powerset, patternMass a X (offsetWindow s) U * f U := by
  rw [patternMass_eval, patternMass_eval]
  simp_rw [rootedPattern_filter hsS]

theorem actualRootLaw_cutoff_test {s S : ℕ} (hsS : s ≤ S) (y M : ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U * cutoffValue M s f U) =
      ∑ U ∈ (offsetWindow s).powerset, actualRootLaw y s U * Stopped.stoppedValue M f U := by
  simp_rw [cutoffValue_eq_filter]
  exact actualRootLaw_window_restriction hsS y (Stopped.stoppedValue M f)

theorem patternMass_cutoff_test {s S : ℕ} (hsS : s ≤ S) (a : ℕ → ℕ) (X M : ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ U ∈ (offsetWindow S).powerset, patternMass a X (offsetWindow S) U *
      cutoffValue M s f U) =
      ∑ U ∈ (offsetWindow s).powerset, patternMass a X (offsetWindow s) U *
        Stopped.stoppedValue M f U := by
  simp_rw [cutoffValue_eq_filter]
  exact patternMass_window_restriction hsS a X (Stopped.stoppedValue M f)

/-- Actual smaller empirical/model tests, with no assumed restriction
identity and no concentration hypothesis for their smaller window. -/
theorem actual_small_test_le_big_shape (a : ℕ → ℕ) (X y : ℕ)
    {M L s S : ℕ} (hML : M ≤ L) (hsS : s ≤ S) (f : Finset ℕ → ℝ)
    (hf : ∀ K, |f K| ≤ 1) :
    |(∑ U ∈ (offsetWindow s).powerset, patternMass a X (offsetWindow s) U *
        Stopped.stoppedValue M f U) -
      (∑ U ∈ (offsetWindow s).powerset, actualRootLaw y s U *
        Stopped.stoppedValue M f U)| ≤
      Stopped.shapeL1 (offsetWindow S) (patternMass a X (offsetWindow S))
          (actualRootLaw y S) L +
        Stopped.failureMass (offsetWindow S) (patternMass a X (offsetWindow S)) L +
        Stopped.failureMass (offsetWindow S) (actualRootLaw y S) L := by
  have hh := cutoff_test_abs_sub_le (offsetWindow S)
    (patternMass a X (offsetWindow S)) (actualRootLaw y S) hML s f hf
    (fun U _ => patternMass_nonneg _ _ _ _) (fun U _ => by
      unfold actualRootLaw
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [patternMass_cutoff_test hsS, actualRootLaw_cutoff_test hsS] at hh
  exact hh

end
end PrimeGapNormality.Prime.CoreRoughWindowRestriction
