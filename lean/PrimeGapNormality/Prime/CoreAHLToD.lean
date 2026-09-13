import PrimeGapNormality.Prime.CoreFrozenAHL
import PrimeGapNormality.Prime.CoreAHLNormalization
import PrimeGapNormality.Prime.CorePrimeNormalityOfD

/-!
# Frozen small-window AHL implies the actual D input

The main theorem takes the paper's small-window one-sided AHL budget at the
fixed cutoff `d0 = 20`.  It uses the classical PNT only for the scalar
normalization `mixZeta → 1`; actual/main Janossy errors are controlled by
the signed AHL budget, never by a pointwise absolute-error assumption.
-/

namespace PrimeGapNormality.Prime.CoreAHLToD

open Finset Filter
open scoped Classical Topology

noncomputable section

private theorem mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos
  · intro t _
    exact eulerProdNat_pos (sieveCutoff (t : ℝ))
  · exact ⟨2 * X, by simp only [mixScale, mem_Ioc]; omega⟩

private theorem max_balance (a b : ℝ) :
    -a + max (a - b) 0 = -b + max (b - a) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring

/-- Rewrite the literal `D(X,1)` so that its positive part has the
main-minus-actual orientation controlled by AHL. -/
theorem corePrimeComparisonQuantity_eq_main_positive
    (X : ℕ) (Ω : Finset ℕ) (L r : ℕ) :
    corePrimeComparisonQuantity X Ω L r 1 =
      1 - (∑ K ∈ Ω.powerset.filter (fun K ↦ K.card = L),
          coreJanossyTransform Ω (rootedMainTerm X) L r K) /
            (windowNX X : ℝ) +
        (∑ K ∈ Ω.powerset.filter (fun K ↦ K.card = L),
          max (coreJanossyTransform Ω (rootedMainTerm X) L r K -
            coreJanossyTransform Ω (fun H ↦ (rootedTupleCount X H : ℝ))
              L r K) 0) / (windowNX X : ℝ) := by
  let I := Ω.powerset.filter (fun K ↦ K.card = L)
  let a : Finset ℕ → ℝ := fun K ↦
    coreJanossyTransform Ω (fun H ↦ (rootedTupleCount X H : ℝ)) L r K
  let b : Finset ℕ → ℝ := fun K ↦
    coreJanossyTransform Ω (rootedMainTerm X) L r K
  have hs :
      -(∑ K ∈ I, a K) + ∑ K ∈ I, max (a K - b K) 0 =
        -(∑ K ∈ I, b K) + ∑ K ∈ I, max (b K - a K) 0 := by
    calc
      -(∑ K ∈ I, a K) + ∑ K ∈ I, max (a K - b K) 0 =
          ∑ K ∈ I, (-a K + max (a K - b K) 0) := by
        rw [sum_add_distrib, sum_neg_distrib]
      _ = ∑ K ∈ I, (-b K + max (b K - a K) 0) := by
        exact sum_congr rfl fun K _ ↦ max_balance (a K) (b K)
      _ = -(∑ K ∈ I, b K) + ∑ K ∈ I, max (b K - a K) 0 := by
        rw [sum_add_distrib, sum_neg_distrib]
  unfold corePrimeComparisonQuantity
  simp only [one_mul]
  change 1 - (∑ K ∈ I, a K) / (windowNX X : ℝ) +
      (∑ K ∈ I, max (a K - b K) 0) / (windowNX X : ℝ) =
    1 - (∑ K ∈ I, b K) / (windowNX X : ℝ) +
      (∑ K ∈ I, max (b K - a K) 0) / (windowNX X : ℝ)
  calc
    1 - (∑ K ∈ I, a K) / (windowNX X : ℝ) +
        (∑ K ∈ I, max (a K - b K) 0) / (windowNX X : ℝ) =
      1 + (-(∑ K ∈ I, a K) + ∑ K ∈ I, max (a K - b K) 0) /
        (windowNX X : ℝ) := by ring
    _ = 1 + (-(∑ K ∈ I, b K) + ∑ K ∈ I, max (b K - a K) 0) /
        (windowNX X : ℝ) := by rw [hs]
    _ = 1 - (∑ K ∈ I, b K) / (windowNX X : ℝ) +
        (∑ K ∈ I, max (b K - a K) 0) / (windowNX X : ℝ) := by ring

/-- Finite AHL comparison at the exact small window and fixed model. -/
theorem corePrimeComparisonQuantity_small_le
    {κ : ℝ} {X : ℕ} (hL : 1 ≤ profileL κ X) (hN : 0 < windowNX X) :
    corePrimeComparisonQuantity X (ahlSmall_omega κ X) (profileL κ X)
        (profileR (profileL κ X) 20) 1 ≤
      |1 - mixZeta X| +
        Stopped.failureMass (ahlSmall_omega κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X)) (profileL κ X) +
        Stopped.modelRemainder (ahlSmall_omega κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X))
          (profileL κ X) (profileR (profileL κ X) 20) +
        coreMixtureJanossyCalibration κ 20 X + ahlSmall_budget κ 20 X := by
  let Ω := ahlSmall_omega κ X
  let L := profileL κ X
  let r := profileR L 20
  let ν : Finset ℕ → ℝ := finiteRootMixUnnorm X (ahlSmall_window κ X)
  let I := Ω.powerset.filter (fun K ↦ K.card = L)
  let JM : Finset ℕ → ℝ := fun K ↦ coreJanossyTransform Ω (rootedMainTerm X) L r K
  let JA : Finset ℕ → ℝ := fun K ↦ coreJanossyTransform Ω
    (fun H ↦ (rootedTupleCount X H : ℝ)) L r K
  let Jν : Finset ℕ → ℝ := fun K ↦ Stopped.janossyTrunc Ω ν L r K
  have hr : L ≤ r := by
    dsimp only [L, r]
    exact profileR_ge (profileL κ X) 20
  have hpar : Odd (r - L) := by
    dsimp only [L, r]
    exact crtMixProf_odd_at κ 20 X
  have hahl :
      (∑ K ∈ I, max (JM K - JA K) 0) / (windowNX X : ℝ) ≤
        ahlSmall_budget κ 20 X := by
    simpa only [I, Ω, L, r, JM, JA] using
      CoreFrozenAHL.small_main_actual_Janossy_pos_le_ahlSmall_budget
        (κ := κ) (d0 := (20 : ℝ)) hL hN
  have hmass : ∑ U ∈ Ω.powerset, ν U = mixZeta X := by
    simpa only [Ω, ν, ahlSmall_omega, offsetWindow] using
      crtMixUnnorm_sum X (ahlSmall_window κ X) hN
  have hpartition :=
    Stopped.shortShapeMass_add_failureMass (Ω := Ω) (μ := ν) (L := L)
  rw [hmass] at hpartition
  have hres := Stopped.modelRemainder_eq_shapeResidual
    (Ω := Ω) (ν := ν) (L := L) (r := r) hL hr hpar
  rw [sum_sub_distrib] at hres
  have hmodelIdentity :
      mixZeta X - ∑ K ∈ I, Jν K =
        Stopped.failureMass Ω ν L + Stopped.modelRemainder Ω ν L r := by
    dsimp only [I, Jν] at hres ⊢
    linarith
  have hcal :
      (∑ K ∈ I, Jν K) - (∑ K ∈ I, JM K) / (windowNX X : ℝ) ≤
        coreMixtureJanossyCalibration κ 20 X := by
    calc
      (∑ K ∈ I, Jν K) - (∑ K ∈ I, JM K) / (windowNX X : ℝ) =
          ∑ K ∈ I, (Jν K - JM K / (windowNX X : ℝ)) := by
        rw [sum_sub_distrib, sum_div]
      _ ≤ ∑ K ∈ I, |Jν K - JM K / (windowNX X : ℝ)| :=
        sum_le_sum fun K _ ↦ le_abs_self _
      _ = coreMixtureJanossyCalibration κ 20 X := by
        unfold coreMixtureJanossyCalibration
        apply sum_congr rfl
        intro K _
        simp only [I, Ω, L, r, JM, Jν, ν, abs_sub_comm]
  have hmain :
      1 - (∑ K ∈ I, JM K) / (windowNX X : ℝ) ≤
        |1 - mixZeta X| + Stopped.failureMass Ω ν L +
          Stopped.modelRemainder Ω ν L r + coreMixtureJanossyCalibration κ 20 X := by
    have habs : 1 - mixZeta X ≤ |1 - mixZeta X| := le_abs_self _
    linarith
  rw [corePrimeComparisonQuantity_eq_main_positive X Ω L r]
  change 1 - (∑ K ∈ I, JM K) / (windowNX X : ℝ) +
      (∑ K ∈ I, max (JM K - JA K) 0) / (windowNX X : ℝ) ≤ _
  exact (add_le_add hmain hahl).trans_eq (by simp only [Ω, L, r, ν])

private theorem tendsto_unnormalized_small_failure
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ ↦
      Stopped.failureMass (ahlSmall_omega κ X)
        (finiteRootMixUnnorm X (ahlSmall_window κ X)) (profileL κ X))
      atTop (𝓝 0) := by
  have htarget := CoreAHLNormalization.classicalMixZetaTendstoOne.mul
    (tendsto_finiteRootMix_small_failureMass hκ)
  simp only [mul_zero] at htarget
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hNX := windowNX_pos (by omega : 0 < X)
  have hZ := mixZ_pos hX
  simpa only [ahlSmall_omega, offsetWindow] using
    (finiteRootMixUnnorm_failureMass_eq_mixZeta_mul hNX hZ
      (ahlSmall_window κ X) (profileL κ X)).symm

private theorem tendsto_unnormalized_small_remainder
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ ↦
      Stopped.modelRemainder (ahlSmall_omega κ X)
        (finiteRootMixUnnorm X (ahlSmall_window κ X))
        (profileL κ X) (profileR (profileL κ X) 20))
      atTop (𝓝 0) := by
  have htarget := CoreAHLNormalization.classicalMixZetaTendstoOne.mul
    (tendsto_finiteRootMix_small_modelRemainder hκ)
  simp only [mul_zero] at htarget
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hNX := windowNX_pos (by omega : 0 < X)
  have hZ := mixZ_pos hX
  simpa only [ahlSmall_omega, offsetWindow] using
    (finiteRootMixUnnorm_modelRemainder_eq_mixZeta_mul hNX hZ
      (ahlSmall_window κ X) (profileL κ X)
      (profileR (profileL κ X) 20)).symm

/-- The frozen paper's small-window AHL hypothesis, at its fixed cutoff
`20`, supplies the actual `D(X,1)` input with the same κ. -/
theorem coreLinearD_of_ahlSmall_AHL
    {κ : ℝ} (hκ : 0 < κ) (hAHL : ahlSmall_AHL κ 20) :
    CoreLinearD κ 20 1 := by
  have hupper : Tendsto (fun X : ℕ ↦
      |1 - mixZeta X| +
        Stopped.failureMass (ahlSmall_omega κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X)) (profileL κ X) +
        Stopped.modelRemainder (ahlSmall_omega κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X))
          (profileL κ X) (profileR (profileL κ X) 20) +
        coreMixtureJanossyCalibration κ 20 X + ahlSmall_budget κ 20 X)
      atTop (𝓝 0) := by
    simpa only [add_zero] using
      ((((CoreAHLNormalization.classicalMixZetaAbsTendstoZero.add
        (tendsto_unnormalized_small_failure hκ)).add
        (tendsto_unnormalized_small_remainder hκ)).add
        (CoreCalibrationUnconditional.tendsto_calibration hκ
          (by norm_num : (0 : ℝ) < 20))).add hAHL)
  have hle : ∀ᶠ X : ℕ in atTop,
      corePrimeComparisonQuantity X (ahlSmall_omega κ X) (profileL κ X)
        (profileR (profileL κ X) 20) 1 ≤
      |1 - mixZeta X| +
        Stopped.failureMass (ahlSmall_omega κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X)) (profileL κ X) +
        Stopped.modelRemainder (ahlSmall_omega κ X)
          (finiteRootMixUnnorm X (ahlSmall_window κ X))
          (profileL κ X) (profileR (profileL κ X) 20) +
        coreMixtureJanossyCalibration κ 20 X + ahlSmall_budget κ 20 X := by
    filter_upwards [eventually_one_le_profileL hκ, eventually_ge_atTop 1]
      with X hL hX
    exact corePrimeComparisonQuantity_small_le hL
      (windowNX_pos (by omega : 0 < X))
  refine squeeze_zero' ?_ hle hupper
  filter_upwards [eventually_one_le_profileL hκ, eventually_ge_atTop 1]
    with X hL hX
  exact corePrimeComparisonQuantity_nonneg
    (windowNX_pos (by omega : 0 < X)) hL
    (crtMixProf_le_at κ 20 X) (crtMixProf_odd_at κ 20 X)

/-- The older large-window AHL is a sufficient, strictly stronger input. -/
theorem coreLinearD_of_AHL {κ : ℝ} (hκ : 0 < κ) (hAHL : AHL κ 20) :
    CoreLinearD κ 20 1 :=
  coreLinearD_of_ahlSmall_AHL hκ (ahlSmall_AHL_of_AHL hAHL)

end

end PrimeGapNormality.Prime.CoreAHLToD
