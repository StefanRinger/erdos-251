import PrimeGapNormality.Prime.CorePresieveLaw
import PrimeGapNormality.Prime.CrtHLMismatchVanishing
import PrimeGapNormality.Prime.CoreLinearMixtureScales
import PrimeGapNormality.Prime.ExactRootMix

/-!
# Single-site bounds for the actual rooted model

Conditioning on the residues at primes at most `S` leaves a late rooted law.
For a site which survived that presieve, its late inclusion probability is
exactly `lateRetention S y`; if it did not survive, that probability is zero.
Averaging the genuine late fibres therefore gives a singleton inclusion bound
for `actualRootLaw`, without pretending that the early survivors are uniform.

The second part averages this bound with the literal normalized
`finiteRootMix` weights and applies the compiled uniform retention estimate.
This file contains no assertion about an underlying arithmetic sequence.
-/

namespace PrimeGapNormality.Prime.CoreModelSingleSite

open Finset Filter
open scoped BigOperators Classical Topology

noncomputable section

private theorem lateRootLaw_inclusionMass_offsetWindow_eq
    (S y : ℕ) {A H : Finset ℕ} (hA : A ⊆ offsetWindow S) :
    Stopped.inclusionMass (offsetWindow S) (lateRootLaw S y A) H =
      if H ⊆ A then lateInclusionFactor S y H.card else 0 := by
  by_cases hHA : H ⊆ A
  · rw [if_pos hHA]
    have hsub :
        A.powerset.filter (fun U => H ⊆ U) ⊆
          (offsetWindow S).powerset.filter (fun U => H ⊆ U) := by
      intro U hU
      have hu := mem_filter.mp hU
      exact mem_filter.mpr
        ⟨mem_powerset.mpr ((mem_powerset.mp hu.1).trans hA), hu.2⟩
    have hsums :
        ∑ U ∈ A.powerset.filter (fun U => H ⊆ U), lateRootLaw S y A U =
          ∑ U ∈ (offsetWindow S).powerset.filter (fun U => H ⊆ U),
            lateRootLaw S y A U := by
      apply sum_subset hsub
      intro U hU hnot
      apply lateRootLaw_eq_zero_of_not_subset
      intro hUA
      apply hnot
      exact mem_filter.mpr ⟨mem_powerset.mpr hUA, (mem_filter.mp hU).2⟩
    unfold Stopped.inclusionMass
    rw [← hsums]
    exact crtHL_late_inclusionMass_eq_factor S y hA le_rfl hHA
  · rw [if_neg hHA]
    unfold Stopped.inclusionMass
    apply sum_eq_zero
    intro U hU
    apply lateRootLaw_eq_zero_of_not_subset
    intro hUA
    exact hHA ((mem_filter.mp hU).2.trans hUA)

private theorem actualRootLaw_inclusionMass_eq_avg_late
    (S y : ℕ) (hSy : S ≤ y) (H : Finset ℕ) :
    Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) H =
      (∑ σ : ResidueChoice S,
          Stopped.inclusionMass (offsetWindow S)
            (lateRootLaw S y (presieveSurvivors S σ)) H) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  unfold Stopped.inclusionMass
  simp_rw [coreActualRootLaw_eq_avg_presieve S y hSy]
  rw [← sum_div, sum_comm]

/-- A single site of the physical window survives the full rooted law with
probability at most the exact late-prime retention factor. -/
theorem actualRootLaw_singleton_inclusion_le
    {S y d : ℕ} (hS : 2 ≤ S) (hSy : S ≤ y)
    (hd1 : 1 ≤ d) (hdS : d ≤ S) :
    Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) {d} ≤
      lateRetention S y := by
  rw [actualRootLaw_inclusionMass_eq_avg_late S y hSy]
  have hcard : (0 : ℝ) < Fintype.card (ResidueChoice S) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ResidueChoice S))
  rw [div_le_iff₀ hcard]
  calc
    (∑ σ : ResidueChoice S,
        Stopped.inclusionMass (offsetWindow S)
          (lateRootLaw S y (presieveSurvivors S σ)) {d}) ≤
        ∑ _σ : ResidueChoice S, lateRetention S y := by
      apply sum_le_sum
      intro σ _hσ
      rw [lateRootLaw_inclusionMass_offsetWindow_eq S y
        (corePresieveSurvivors_subset_Icc S σ)]
      by_cases hdA : {d} ⊆ presieveSurvivors S σ
      · rw [if_pos hdA, card_singleton, lateInclusionFactor_one]
      · rw [if_neg hdA]
        exact (rootedEulerProdNat_pos hS).le
    _ = lateRetention S y * (Fintype.card (ResidueChoice S) : ℝ) := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      ring

private theorem modelSingleSite_mixZ_pos {X : ℕ} (hX : 1 ≤ X) :
    0 < mixZ X := by
  unfold mixZ
  apply sum_pos'
  · intro t _
    exact mixWeightV_nonneg t
  · refine ⟨2 * X, ?_, ?_⟩
    · simp only [mixScale, mem_Ioc]
      omega
    · exact eulerProdNat_pos (sieveCutoff ((2 * X : ℕ) : ℝ))

private theorem finiteRootMix_inclusionMass_eq_weighted
    (X S : ℕ) (H : Finset ℕ) :
    Stopped.inclusionMass (offsetWindow S) (finiteRootMix X S) H =
      (∑ t ∈ mixScale X, mixWeightV t *
          Stopped.inclusionMass (offsetWindow S)
            (actualRootLaw (sieveCutoff (t : ℝ)) S) H) / mixZ X := by
  unfold Stopped.inclusionMass finiteRootMix
  rw [← sum_div, sum_comm]
  simp only [mul_sum]

/-- Real-valued version of the preceding convex bound, with the scale
majorant left explicit for use with the uniform cutoff estimates. -/
theorem finiteRootMix_singleton_inclusion_le_of_retention
    {X S d : ℕ} {R : ℝ} (hS : 2 ≤ S) (hZ : 0 < mixZ X)
    (hd1 : 1 ≤ d) (hdS : d ≤ S)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ))
    (hR : ∀ t ∈ mixScale X,
      lateRetention S (sieveCutoff (t : ℝ)) ≤ R) :
    Stopped.inclusionMass (offsetWindow S) (finiteRootMix X S) {d} ≤ R := by
  rw [finiteRootMix_inclusionMass_eq_weighted]
  apply (div_le_iff₀ hZ).2
  calc
    (∑ t ∈ mixScale X, mixWeightV t *
        Stopped.inclusionMass (offsetWindow S)
          (actualRootLaw (sieveCutoff (t : ℝ)) S) {d}) ≤
        ∑ t ∈ mixScale X, mixWeightV t * R := by
      apply sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        ((actualRootLaw_singleton_inclusion_le hS (hSy t ht) hd1 hdS).trans
          (hR t ht))
        (mixWeightV_nonneg t)
    _ = mixZ X * R := by
      rw [← sum_mul]
      rfl
    _ ≤ R * mixZ X := le_of_eq (mul_comm _ _)

/-- At the actual small model window, every singleton atom is bounded by
the same `O(log G / G)` quantity, uniformly over the site. -/
theorem eventually_finiteRootMix_singleton_inclusion_le
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, ∀ d : ℕ,
      1 ≤ d → d ≤ ahlSmall_window κ X →
      Stopped.inclusionMass (offsetWindow (ahlSmall_window κ X))
          (finiteRootMix X (ahlSmall_window κ X)) {d} ≤
        ((3 : ℝ) / eulerProdLowerConst) *
          (Real.log (windowG X) / windowG X) := by
  filter_upwards [eventually_coreLinearMixtureScales hκ,
    (eventually_ge_atTop 1 : ∀ᶠ X : ℕ in atTop, 1 ≤ X)] with X hs hX
  intro d hd1 hdS
  have hGpos : 0 < windowG X := zero_lt_one.trans hs.1
  have hratio0 : 0 ≤ Real.log (windowG X) / windowG X :=
    div_nonneg hs.2.1.le hGpos.le
  apply finiteRootMix_singleton_inclusion_le_of_retention
    (show 2 ≤ ahlSmall_window κ X by omega)
    (modelSingleSite_mixZ_pos hX) hd1 hdS
  · intro t ht
    exact (hs.2.2.2.2 t ht).1
  · intro t ht
    have hscaled := (hs.2.2.2.2 t ht).2.2.2.1
    calc
      lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) =
          (lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) *
            windowG X / Real.log (windowG X)) *
              (Real.log (windowG X) / windowG X) := by
        field_simp [hGpos.ne', hs.2.1.ne'] <;> ring
      _ ≤ ((3 : ℝ) / eulerProdLowerConst) *
          (Real.log (windowG X) / windowG X) :=
        mul_le_mul_of_nonneg_right hscaled hratio0

/-- The uniform singleton cap appearing above vanishes. -/
theorem tendsto_modelSingleSite_cap_zero :
    Tendsto
      (fun X : ℕ ↦ ((3 : ℝ) / eulerProdLowerConst) *
        (Real.log (windowG X) / windowG X))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun G : ℝ ↦ Real.log G / G) atTop (nhds 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  simpa only [Function.comp_apply, mul_zero] using
    (hlog.comp tendsto_windowG_atTop).const_mul
      ((3 : ℝ) / eulerProdLowerConst)

end
end PrimeGapNormality.Prime.CoreModelSingleSite
