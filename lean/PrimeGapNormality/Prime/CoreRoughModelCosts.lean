import PrimeGapNormality.Prime.CoreRoughModelLimit
import PrimeGapNormality.Prime.CoreRoughMixtureMoments
import PrimeGapNormality.Prime.CoreRoughRemainderScalar
import PrimeGapNormality.Prime.FiniteRootMixSmallLowerException

/-!
# Failure and unbounded moment costs for the actual rough model

Failure is a bounded configuration event and is transferred by full L1
distance. Factorial moments are instead transferred multiplicatively using
the exact cutoff law. No bounded-TV estimate is applied to growing moments.
-/

namespace PrimeGapNormality.Prime.CoreRoughModelCosts

open Filter Finset CoreRoughSyntheticScale CoreRoughProfileError
open CoreRoughModelLimit CoreRoughMixtureMoments CoreRoughRemainderScalar
open scoped Classical Topology
noncomputable section

set_option maxHeartbeats 1000000

theorem failureMass_abs_sub_le (Ω : Finset ℕ) (μ ν : Finset ℕ → ℝ) (L : ℕ) :
    |Stopped.failureMass Ω μ L - Stopped.failureMass Ω ν L| ≤
      ∑ U ∈ Ω.powerset, |μ U - ν U| := by
  unfold Stopped.failureMass
  rw [← Finset.sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro U hU hn
  exact abs_nonneg _

/-- The old rooted model's failure mass tends to zero at its literal
growing profile, via the same full configuration comparison. -/
theorem tendsto_actual_failureMass_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun z : ℕ => Stopped.failureMass (offsetWindow (roughProfileS κ z))
      (actualRootLaw z (roughProfileS κ z)) (roughProfileL κ z)) atTop (𝓝 0) := by
  have hmix : Tendsto (fun z : ℕ => Stopped.failureMass (offsetWindow (roughProfileS κ z))
      (finiteRootMix (roughSyntheticScale z) (roughProfileS κ z)) (roughProfileL κ z))
      atTop (𝓝 0) := by
    have hh := (tendsto_finiteRootMix_small_failureMass hκ).comp
      CoreRoughScaleLimits.tendsto_roughSyntheticScale_atTop
    apply hh.congr'
    exact Eventually.of_forall fun z => rfl
  have hlim := hmix.add (tendsto_modelMassL1_zero hκ)
  simp only [add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall fun z => by
      unfold Stopped.failureMass
      exact Finset.sum_nonneg fun U hU => actualRootLaw_nonneg _ _ _
  · exact Eventually.of_forall fun z => by
      have hh := failureMass_abs_sub_le (offsetWindow (roughProfileS κ z))
        (actualRootLaw z (roughProfileS κ z))
        (finiteRootMix (roughSyntheticScale z) (roughProfileS κ z)) (roughProfileL κ z)
      have hh' := (le_abs_self _).trans hh
      change _ ≤ modelMassL1 κ z at hh'
      linarith

/-- A finite floor estimate, not another asymptotic growth theorem,
puts the full moment rank inside the physical small window. -/
theorem rank_succ_le_smallWindow {κ : ℝ} {T : ℕ}
    (hL : 1 ≤ profileL κ T) (hG : 32 ≤ windowG T) :
    profileR (profileL κ T) 20 + 1 ≤ ahlSmall_window κ T := by
  let L := profileL κ T
  have hLR : (1 : ℝ) ≤ L := by
    change (1 : ℝ) ≤ (profileL κ T : ℝ)
    exact_mod_cast hL
  have hfloor : (6 / 5 : ℝ) * (L : ℝ) * windowG T < (ahlSmall_window κ T : ℝ) + 1 := by
    simpa only [L, ahlSmall_window_eq] using
      Nat.lt_floor_add_one ((6 / 5 : ℝ) * (profileL κ T : ℝ) * windowG T)
  have hprod := mul_le_mul_of_nonneg_left hG (show 0 ≤ (6 / 5 : ℝ) * (L : ℝ) by positivity)
  have hnat : 20 * L + 2 ≤ ahlSmall_window κ T := by
    have hreal : ((20 * L + 2 : ℕ) : ℝ) ≤ (ahlSmall_window κ T : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hreal
  have hr := (profileR_twenty_bounds L).2
  dsimp only [L] at hnat hr
  omega

theorem eventually_rank_succ_le_cutoff {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ z : ℕ in atTop, profileR (roughProfileL κ z) 20 + 1 ≤ z := by
  have hT := CoreRoughScaleLimits.tendsto_roughSyntheticScale_atTop
  filter_upwards [hT.eventually (eventually_one_le_profileL hκ),
    (tendsto_windowG_atTop.comp hT).eventually_ge_atTop 32,
    CoreRoughSmallWindow.eventually_ahlSmall_window_roughSyntheticScale_lt hκ] with z hL hG hS
  simp only [Function.comp_apply] at hG
  exact (rank_succ_le_smallWindow hL hG).trans hS.le

theorem tendsto_rank_succ_mul_error_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun z : ℕ => ((profileR (roughProfileL κ z) 20 + 1 : ℕ) : ℝ) *
      CoreRoughMixtureComparison.roughMixtureError z) atTop (𝓝 0) := by
  have hh := (tendsto_profileR_twenty_mul_error_zero hκ).add tendsto_roughProfileError_zero
  simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_zero,
    roughProfileError, CoreRoughMixtureComparison.roughMixtureError] using hh

/-- One event works for every j through the full Bonferroni rank plus one.
The only loss is the explicit factor two from the exact moment comparison. -/
theorem eventually_actual_countMoment_le_two_five {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ z : ℕ in atTop, ∀ j : ℕ, j ≤ profileR (roughProfileL κ z) 20 + 1 →
      Stopped.countMoment (offsetWindow (roughProfileS κ z))
        (actualRootLaw z (roughProfileS κ z)) j ≤
          2 * (((5 : ℝ) * (roughProfileL κ z : ℝ)) ^ j / (j.factorial : ℝ)) := by
  have hT := CoreRoughScaleLimits.tendsto_roughSyntheticScale_atTop
  have hsmall := (tendsto_rank_succ_mul_error_zero hκ).eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 4)
  have he := tendsto_roughProfileError_zero.eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [eventually_roughProfile_scales hκ,
    CoreRoughSmallWindow.eventually_ahlSmall_window_roughSyntheticScale_lt hκ,
    eventually_rank_succ_le_cutoff hκ, hsmall, he,
    hT.eventually (finiteRootMix_small_countMoment_le_five hκ)] with z hz hSz hr hsmall he hmoment
  intro j hj
  have he' : CoreRoughMixtureComparison.roughMixtureError z ≤ 1 / 2 := he
  have hh := actual_mixture_countMoment_bounds hz.1 hSz hj hr hz.2.1 he'
  have hm : Stopped.countMoment (offsetWindow (roughProfileS κ z))
      (finiteRootMix (roughSyntheticScale z) (roughProfileS κ z)) j ≤
        ((5 : ℝ) * (roughProfileL κ z : ℝ)) ^ j / (j.factorial : ℝ) := by
    simpa only [roughProfileS, roughProfileL, ahlSmall_omega, offsetWindow] using hmoment j
  have hnonneg : 0 ≤ Stopped.countMoment (offsetWindow (roughProfileS κ z))
      (actualRootLaw z (roughProfileS κ z)) j := by
    unfold Stopped.countMoment
    exact Finset.sum_nonneg fun U hU => mul_nonneg (actualRootLaw_nonneg _ _ _) (Nat.cast_nonneg _)
  have hhalf : (1 / 2 : ℝ) ≤ 1 -
      2 * ((profileR (roughProfileL κ z) 20 + 1 : ℕ) : ℝ) *
        CoreRoughMixtureComparison.roughMixtureError z := by linarith
  have hl := (mul_le_mul_of_nonneg_right hhalf hnonneg).trans hh.1
  simp only [roughProfileS, roughProfileL] at hl hm ⊢
  linarith

/-- The unbounded Bonferroni model cost vanishes for the actual rough law.
It uses the genuine rank-(r+1) moment above and the public scalar envelope. -/
theorem tendsto_actual_modelRemainder_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun z : ℕ => Stopped.modelRemainder (offsetWindow (roughProfileS κ z))
      (actualRootLaw z (roughProfileS κ z)) (roughProfileL κ z)
      (profileR (roughProfileL κ z) 20)) atTop (𝓝 0) := by
  have hL : Tendsto (roughProfileL κ) atTop atTop :=
    (tendsto_profileL_atTop hκ).comp CoreRoughScaleLimits.tendsto_roughSyntheticScale_atTop
  have hs := (tendsto_small_remainder_scalar.comp hL).const_mul 2
  simp only [mul_zero] at hs
  apply squeeze_zero' _ _ hs
  · exact Eventually.of_forall fun z => by
      unfold Stopped.modelRemainder
      exact Finset.sum_nonneg fun U hU => mul_nonneg (actualRootLaw_nonneg _ _ _)
        (crtMixUnnormRem_countEnvelope_nonneg _ _ _)
  · filter_upwards [eventually_actual_countMoment_le_two_five hκ,
      hL.eventually_ge_atTop 1] with z hm hLz
    have hh := Stopped.modelRemainder_le (Ω := offsetWindow (roughProfileS κ z))
      (ν := actualRootLaw z (roughProfileS κ z)) hLz
      (profileR_ge (roughProfileL κ z) 20) (fun U hU => actualRootLaw_nonneg _ _ _)
    have hbound := hh.trans (mul_le_mul_of_nonneg_left (hm _ le_rfl) (Nat.cast_nonneg _))
    exact hbound.trans_eq (by dsimp only [Function.comp_apply]; ring)

end
end PrimeGapNormality.Prime.CoreRoughModelCosts
