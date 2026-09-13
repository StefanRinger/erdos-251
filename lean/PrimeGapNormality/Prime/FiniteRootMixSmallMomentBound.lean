import PrimeGapNormality.Prime.SmallPresieveMeanFive
import PrimeGapNormality.Prime.FiniteRootMixSmallMoments
import PrimeGapNormality.Prime.ModelMoments
import PrimeGapNormality.Prime.CrtFailureMassLimit

/-!
# Factorial-moment bound for the normalized small finite root mix

This file transports the fibrewise mean cap through the exact conditional
laws, the uniform residue average, and the normalized `mixWeightV` average.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

private theorem lateInclusionFactor_le_retention_pow
    {S y j : ℕ} (hS : 2 ≤ S) (hjS : j ≤ S) :
    lateInclusionFactor S y j ≤ lateRetention S y ^ j := by
  have hps : ∀ p ∈ latePrimes S y, 2 ≤ p := by
    intro p hp
    exact (Nat.prime_of_mem_primesLE (sdiff_subset hp)).two_le
  have hjp : ∀ p ∈ latePrimes S y, j ≤ p - 1 := by
    intro p hp
    have hpprime : Nat.Prime p :=
      Nat.prime_of_mem_primesLE (sdiff_subset hp)
    have hpnot : p ∉ Nat.primesLE S := (mem_sdiff.mp hp).2
    have hSp : S < p := by
      by_contra h
      exact hpnot (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt h, hpprime⟩)
    omega
  have h := palmJointSurvivePrimes_le_theta_pow (latePrimes S y) j hps hjp
  simpa [lateInclusionFactor, lateRetention, rootedEulerProdNat,
    palmJointSurvivePrimes, palmJointSurvive, palmThetaPrimes, palmTheta,
    palmHitProb, div_eq_mul_inv] using h

private theorem lateRootLaw_countMoment_le_of_mean
    {S y L j : ℕ} (hS : 2 ≤ S) (hSy : S ≤ y)
    (σ : ResidueChoice S)
    (hmean : ((presieveSurvivors S σ).card : ℝ) * lateRetention S y ≤
      (5 : ℝ) * L) :
    Stopped.countMoment (offsetWindow S)
        (lateRootLaw S y (presieveSurvivors S σ)) j
      ≤ ((5 : ℝ) * L) ^ j / (j.factorial : ℝ) := by
  let A := presieveSurvivors S σ
  have hA : A ⊆ offsetWindow S := presieveSurvivors_subset_Icc_self S σ
  have hAS : A.card ≤ S := by
    have hc := card_le_card hA
    have hI : (offsetWindow S).card = S := by
      unfold offsetWindow
      rw [Nat.card_Icc]
      omega
    exact hc.trans_eq hI
  have hrestrict :
      Stopped.countMoment (offsetWindow S) (lateRootLaw S y A) j =
        ∑ E ∈ A.powerset,
          lateRootLaw S y A E * (Nat.choose E.card j : ℝ) := by
    unfold Stopped.countMoment
    refine (sum_subset (powerset_mono.mpr hA) ?_).symm
    intro E hE hnot
    have hnotA : ¬ E ⊆ A := by
      intro hEA
      exact hnot (mem_powerset.mpr hEA)
    rw [lateRootLaw_eq_zero_of_not_subset hnotA, zero_mul]
  rw [hrestrict]
  by_cases hj : j ≤ A.card
  · have hmom :=
      (exactCountMoments_lateRootLaw S y
        (presieveSurvivors_subset_Icc_self S σ) le_rfl hSy).2.2.1 j hj
    have hcomm :
        ∑ E ∈ A.powerset,
            lateRootLaw S y A E * (Nat.choose E.card j : ℝ) =
          ∑ E ∈ A.powerset,
            (Nat.choose E.card j : ℝ) * lateRootLaw S y A E := by
      exact sum_congr rfl fun E _ => mul_comm _ _
    rw [hcomm, hmom]
    have hfac : lateInclusionFactor S y j ≤ lateRetention S y ^ j :=
      lateInclusionFactor_le_retention_pow hS (hj.trans hAS)
    have hθ0 : 0 ≤ lateRetention S y := (rootedEulerProdNat_pos hS).le
    have hm0 : 0 ≤ (A.card : ℝ) * lateRetention S y :=
      mul_nonneg (Nat.cast_nonneg _) hθ0
    calc
      (Nat.choose A.card j : ℝ) * lateInclusionFactor S y j
          ≤ (Nat.choose A.card j : ℝ) * lateRetention S y ^ j :=
        mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg _)
      _ ≤ ((A.card : ℝ) ^ j / (j.factorial : ℝ)) *
            lateRetention S y ^ j :=
        mul_le_mul_of_nonneg_right (choose_le_pow_div_real A.card j)
          (pow_nonneg hθ0 j)
      _ = (((A.card : ℝ) * lateRetention S y) ^ j) /
            (j.factorial : ℝ) := by
        rw [mul_pow]
        ring
      _ ≤ (((5 : ℝ) * L) ^ j) / (j.factorial : ℝ) :=
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ hm0 hmean j) (Nat.cast_nonneg _)
  · have hj' : A.card < j := Nat.lt_of_not_ge hj
    have hmom :=
      (exactCountMoments_lateRootLaw S y
        (presieveSurvivors_subset_Icc_self S σ) le_rfl hSy).2.2.2 j hj'
    have hcomm :
        ∑ E ∈ A.powerset,
            lateRootLaw S y A E * (Nat.choose E.card j : ℝ) =
          ∑ E ∈ A.powerset,
            (Nat.choose E.card j : ℝ) * lateRootLaw S y A E := by
      exact sum_congr rfl fun E _ => mul_comm _ _
    rw [hcomm, hmom]
    exact div_nonneg (pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) _)
      (Nat.cast_nonneg _)

private theorem finiteRootMixSmall_actual_countMoment_eq_avg
    (κ : ℝ) (X y j : ℕ) (hSy : ahlSmall_window κ X ≤ y) :
    Stopped.countMoment (ahlSmall_omega κ X)
        (actualRootLaw y (ahlSmall_window κ X)) j =
      (∑ σ : ResidueChoice (ahlSmall_window κ X),
          Stopped.countMoment (ahlSmall_omega κ X)
            (lateRootLaw (ahlSmall_window κ X) y
              (presieveSurvivors (ahlSmall_window κ X) σ)) j) /
        (Fintype.card (ResidueChoice (ahlSmall_window κ X)) : ℝ) := by
  let C := (Fintype.card (ResidueChoice (ahlSmall_window κ X)) : ℝ)
  unfold Stopped.countMoment
  have hpoint : ∀ U,
      actualRootLaw y (ahlSmall_window κ X) U * (Nat.choose U.card j : ℝ) =
        (∑ σ : ResidueChoice (ahlSmall_window κ X),
            lateRootLaw (ahlSmall_window κ X) y
              (presieveSurvivors (ahlSmall_window κ X) σ) U *
                (Nat.choose U.card j : ℝ)) / C := by
    intro U
    rw [finiteRootMixSmall_actualRootLaw_eq_avg κ X y hSy U,
      div_mul_eq_mul_div, sum_mul]
  rw [sum_congr rfl fun U _ => hpoint U, ← sum_div]
  refine congrArg (fun z => z / C) ?_
  rw [sum_comm]

private theorem finiteRootMixSmall_actual_countMoment_le_of_mean
    {κ : ℝ} {X y j : ℕ} (hS : 2 ≤ ahlSmall_window κ X)
    (hSy : ahlSmall_window κ X ≤ y)
    (hmean : ∀ σ : ResidueChoice (ahlSmall_window κ X),
      ((presieveSurvivors (ahlSmall_window κ X) σ).card : ℝ) *
          lateRetention (ahlSmall_window κ X) y
        ≤ (5 : ℝ) * profileL κ X) :
    Stopped.countMoment (ahlSmall_omega κ X)
        (actualRootLaw y (ahlSmall_window κ X)) j
      ≤ ((5 : ℝ) * (profileL κ X : ℝ)) ^ j /
          (j.factorial : ℝ) := by
  rw [finiteRootMixSmall_actual_countMoment_eq_avg κ X y j hSy]
  have hCpos : (0 : ℝ) <
      Fintype.card (ResidueChoice (ahlSmall_window κ X)) := by
    exact_mod_cast residueChoice_card_pos (ahlSmall_window κ X)
  apply (div_le_iff₀ hCpos).2
  calc
    ∑ σ : ResidueChoice (ahlSmall_window κ X),
        Stopped.countMoment (ahlSmall_omega κ X)
          (lateRootLaw (ahlSmall_window κ X) y
            (presieveSurvivors (ahlSmall_window κ X) σ)) j
      ≤ ∑ _σ : ResidueChoice (ahlSmall_window κ X),
          (((5 : ℝ) * (profileL κ X : ℝ)) ^ j /
            (j.factorial : ℝ)) := by
        exact sum_le_sum fun σ _ => by
          simpa [ahlSmall_omega, offsetWindow] using
            lateRootLaw_countMoment_le_of_mean hS hSy σ (hmean σ)
    _ = (Fintype.card (ResidueChoice (ahlSmall_window κ X)) : ℝ) *
          (((5 : ℝ) * (profileL κ X : ℝ)) ^ j /
            (j.factorial : ℝ)) := by
      rw [sum_const, nsmul_eq_mul, card_univ]
    _ = (((5 : ℝ) * (profileL κ X : ℝ)) ^ j /
            (j.factorial : ℝ)) *
          (Fintype.card (ResidueChoice (ahlSmall_window κ X)) : ℝ) := by
      rw [mul_comm]

private theorem finiteRootMix_countMoment_eq_weighted
    (X S j : ℕ) :
    Stopped.countMoment (offsetWindow S) (finiteRootMix X S) j =
      (∑ t ∈ mixScale X, mixWeightV t *
          Stopped.countMoment (offsetWindow S)
            (actualRootLaw (sieveCutoff (t : ℝ)) S) j) / mixZ X := by
  unfold Stopped.countMoment finiteRootMix
  have hpoint : ∀ U,
      ((∑ t ∈ mixScale X, mixWeightV t *
          actualRootLaw (sieveCutoff (t : ℝ)) S U) / mixZ X) *
          (Nat.choose U.card j : ℝ) =
        (∑ t ∈ mixScale X, mixWeightV t *
          (actualRootLaw (sieveCutoff (t : ℝ)) S U *
            (Nat.choose U.card j : ℝ))) / mixZ X := by
    intro U
    rw [div_mul_eq_mul_div]
    refine congrArg (fun z => z / mixZ X) ?_
    rw [sum_mul]
    exact sum_congr rfl fun t _ => mul_assoc _ _ _
  rw [sum_congr rfl fun U _ => hpoint U, ← sum_div]
  refine congrArg (fun z => z / mixZ X) ?_
  rw [sum_comm]
  exact sum_congr rfl fun t _ => (mul_sum _ _ _).symm

private theorem eventually_ahlSmall_window_le_mix_cutoff {κ : ℝ}
    (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X,
      ahlSmall_window κ X ≤ sieveCutoff (t : ℝ) := by
  filter_upwards [eventually_profileS_le_sieveCutoff hκ,
    crtNestVR_eventually_exp_sixteen] with X hprofile hX
  intro t ht
  have htI : t ∈ Ioc X (2 * X) := by simpa [mixScale] using ht
  have hXt : (X : ℝ) < (t : ℝ) := Nat.cast_lt.mpr (mem_Ioc.mp htI).1
  have hX1 : (1 : ℝ) < X := by
    exact lt_of_lt_of_le
      (lt_trans (by norm_num : (1 : ℝ) < 2)
        (lt_trans Real.exp_one_gt_two
          (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16)))) hX
  have hprofileNat : profileS κ X ≤ sieveCutoff (X : ℝ) :=
    Nat.cast_le.mp hprofile
  exact (ahlSmall_window_le_profileS κ X).trans
    (hprofileNat.trans (crtNestVR_sieveCutoff_mono hX1 hXt))

theorem finiteRootMix_small_countMoment_le_five_of_euler_tail
    {κ : ℝ} (hκ : 0 < κ)
    (hEuler : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) < eulerProdNat n * Real.log n) :
    ∀ᶠ X : ℕ in atTop, ∀ j : ℕ,
      Stopped.countMoment (ahlSmall_omega κ X)
        (finiteRootMix X (ahlSmall_window κ X)) j
      ≤ ((5 : ℝ) * (profileL κ X : ℝ)) ^ j /
          (j.factorial : ℝ) := by
  filter_upwards [eventually_small_presieve_mean_le_five_of_euler_tail hκ hEuler,
    eventually_ahlSmall_window_le_mix_cutoff hκ,
    (tendsto_ahlSmall_window_atTop hκ).eventually (eventually_ge_atTop 2)] with
      X hmean hcut hS
  intro j
  by_cases hZ : mixZ X = 0
  · have hRHS : 0 ≤ ((5 : ℝ) * (profileL κ X : ℝ)) ^ j /
        (j.factorial : ℝ) := div_nonneg
      (pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) _)
      (Nat.cast_nonneg _)
    simpa [Stopped.countMoment, finiteRootMix, hZ] using hRHS
  · have hZpos : 0 < mixZ X := lt_of_le_of_ne (mixZ_nonneg X) (Ne.symm hZ)
    rw [show ahlSmall_omega κ X = offsetWindow (ahlSmall_window κ X) from rfl,
      finiteRootMix_countMoment_eq_weighted]
    apply (div_le_iff₀ hZpos).2
    calc
      ∑ t ∈ mixScale X, mixWeightV t *
          Stopped.countMoment (offsetWindow (ahlSmall_window κ X))
            (actualRootLaw (sieveCutoff (t : ℝ))
              (ahlSmall_window κ X)) j
        ≤ ∑ t ∈ mixScale X, mixWeightV t *
            (((5 : ℝ) * (profileL κ X : ℝ)) ^ j /
              (j.factorial : ℝ)) := by
          exact sum_le_sum fun t ht =>
            mul_le_mul_of_nonneg_left
              (by
                simpa [ahlSmall_omega, offsetWindow] using
                  finiteRootMixSmall_actual_countMoment_le_of_mean hS
                    (hcut t ht) (fun σ => hmean t ht σ))
              (mixWeightV_nonneg t)
      _ = mixZ X *
          (((5 : ℝ) * (profileL κ X : ℝ)) ^ j /
            (j.factorial : ℝ)) := by
        rw [← sum_mul]
        rfl
      _ = (((5 : ℝ) * (profileL κ X : ℝ)) ^ j /
            (j.factorial : ℝ)) * mixZ X := by
        rw [mul_comm]

end

end PrimeGapNormality.Prime
