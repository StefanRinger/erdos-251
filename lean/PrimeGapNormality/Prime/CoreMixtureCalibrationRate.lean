import PrimeGapNormality.Prime.CoreMixtureCalibration

/-!
# Absolute and Janossy rates for the small mixture calibration

The relative calibration coefficient from `CoreMixtureCalibration` is
converted to an absolute error without any singular-series upper bound.
When the coefficient is at most one half, nonnegativity and the elementary
bound `finiteTupleSieveProduct ≤ 1` give `rootedMainTerm ≤ 2X`.
-/

open Filter Finset
open scoped Classical Topology

namespace PrimeGapNormality.Prime

noncomputable section

private theorem finiteTupleSieveProduct_le_one (E : Finset ℕ) (y : ℕ) :
    finiteTupleSieveProduct E y ≤ 1 := by
  unfold finiteTupleSieveProduct
  apply prod_le_one
  · intro p hp
    have hpprime := Nat.prime_of_mem_primesLE hp
    letI : NeZero p := ⟨hpprime.ne_zero⟩
    have hres : residueCount E p ≤ p := by
      unfold residueCount
      simpa only [ZMod.card] using
        card_le_univ (E.image fun n : ℕ => (n : ZMod p))
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpprime.pos
    have hfrac : (residueCount E p : ℝ) / p ≤ 1 :=
      (div_le_one hp0).mpr (Nat.cast_le.mpr hres)
    linarith
  · intro p hp
    have hpprime := Nat.prime_of_mem_primesLE hp
    have hfrac : 0 ≤ (residueCount E p : ℝ) / p :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith

private theorem mixScale_card_eq (X : ℕ) : (mixScale X).card = X := by
  simp [mixScale]
  omega

private theorem finiteRootMixUnnorm_inclusionMass_le_X_div
    {X S : ℕ} {H : Finset ℕ} (hH : H ⊆ offsetWindow S) :
    Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H ≤
      (X : ℝ) / (windowNX X : ℝ) := by
  rw [finiteRootMixUnnorm_inclusionMass_eq_product_sum X S hH]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    (∑ t ∈ mixScale X,
        finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) ≤
        ∑ _t ∈ mixScale X, (1 : ℝ) :=
      sum_le_sum fun t _ => finiteTupleSieveProduct_le_one _ _
    _ = ((mixScale X).card : ℝ) := by simp
    _ = (X : ℝ) := by rw [mixScale_card_eq]

private theorem finiteRootMixUnnorm_inclusionMass_nonneg
    {X S : ℕ} {H : Finset ℕ} (hH : H ⊆ offsetWindow S) :
    0 ≤ Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H := by
  rw [finiteRootMixUnnorm_inclusionMass_eq_product_sum X S hH]
  exact div_nonneg
    (sum_nonneg fun t _ => finiteTupleSieveProduct_nonneg _ _)
    (Nat.cast_nonneg _)

/-- A relative error `δ ≤ 1/2` yields the uniform absolute error
`2 δ X/N_X`.  The proof uses only positivity and `P_t ≤ 1`. -/
theorem finiteRootMixUnnorm_inclusionMass_absolute_error_le
    {X S : ℕ} {H : Finset ℕ} {δ : ℝ}
    (hX : 0 < X) (hH : H ⊆ offsetWindow S)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hrel :
      |Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H -
          rootedMainTerm X H / (windowNX X : ℝ)| ≤
        δ * (rootedMainTerm X H / (windowNX X : ℝ))) :
    |Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H -
        rootedMainTerm X H / (windowNX X : ℝ)| ≤
      2 * δ * (X : ℝ) / (windowNX X : ℝ) := by
  let b := Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H
  let m := rootedMainTerm X H / (windowNX X : ℝ)
  have hδpos : 0 < δ + 1 := by linarith
  have hm0 : 0 ≤ m := by
    have hprod : 0 ≤ (δ + 1) * m := by
      have hb0 : 0 ≤ b := finiteRootMixUnnorm_inclusionMass_nonneg hH
      have hbm : b - m ≤ δ * m :=
        (le_abs_self (b - m)).trans hrel
      nlinarith
    exact nonneg_of_mul_nonneg_right hprod hδpos
  have hb : b ≤ (X : ℝ) / (windowNX X : ℝ) :=
    finiteRootMixUnnorm_inclusionMass_le_X_div hH
  have hmb : m - b ≤ δ * m := by
    calc
      m - b ≤ |m - b| := le_abs_self _
      _ = |b - m| := abs_sub_comm _ _
      _ ≤ δ * m := hrel
  have hδm : δ * m ≤ (1 / 2 : ℝ) * m :=
    mul_le_mul_of_nonneg_right hδ hm0
  have hmle : m ≤ 2 * b := by linarith
  have hmX : m ≤ 2 * ((X : ℝ) / (windowNX X : ℝ)) := hmle.trans
    (mul_le_mul_of_nonneg_left hb (by norm_num))
  calc
    |Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H -
        rootedMainTerm X H / (windowNX X : ℝ)| ≤ δ * m := hrel
    _ ≤ δ * (2 * ((X : ℝ) / (windowNX X : ℝ))) :=
      mul_le_mul_of_nonneg_left hmX hδ0
    _ = 2 * δ * (X : ℝ) / (windowNX X : ℝ) := by
      ring

theorem coreJanossyTransform_inclusionMass_eq_janossyTrunc
    (Ω : Finset ℕ) (ν : Finset ℕ → ℝ) (L r : ℕ) (K : Finset ℕ) :
    coreJanossyTransform Ω (fun H => Stopped.inclusionMass Ω ν H) L r K =
      Stopped.janossyTrunc Ω ν L r K := by
  rfl

/-- Finite summed Janossy calibration at the actual small profile. -/
theorem eventually_coreMixture_small_janossy_calibration_le
    {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    ∀ᶠ X : ℕ in atTop,
      (∑ K ∈ (ahlSmall_omega κ X).powerset.filter
          (fun K => K.card = profileL κ X),
        |coreJanossyTransform (ahlSmall_omega κ X) (rootedMainTerm X)
              (profileL κ X) (profileR (profileL κ X) d0) K /
              (windowNX X : ℝ) -
            Stopped.janossyTrunc (ahlSmall_omega κ X)
              (finiteRootMixUnnorm X (ahlSmall_window κ X))
              (profileL κ X) (profileR (profileL κ X) d0) K|) ≤
        ((((profileR (profileL κ X) d0 + 1) *
          ((ahlSmall_omega κ X).card + 1) ^
            profileR (profileL κ X) d0 : ℕ) : ℝ)) ^ 2 *
          (2 * coreMixtureRelativeError κ d0 X * (X : ℝ) /
            (windowNX X : ℝ)) := by
  filter_upwards [
    eventually_finiteRootMixUnnorm_small_inclusionMass_relative_error_le hκ hd0,
    (tendsto_coreMixtureRelativeError hκ hd0).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop 1] with X hrel hδ hX
  let Ω := ahlSmall_omega κ X
  let L := profileL κ X
  let r := profileR L d0
  let δ := coreMixtureRelativeError κ d0 X
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ, coreMixtureRelativeError]
    positivity
  have hH : ∀ H ⊆ Ω, H.card ≤ r →
      |rootedMainTerm X H / (windowNX X : ℝ) -
          Stopped.inclusionMass Ω (finiteRootMixUnnorm X (ahlSmall_window κ X)) H| ≤
        2 * δ * (X : ℝ) / (windowNX X : ℝ) := by
    intro H hHΩ hHr
    have hHoff : H ⊆ offsetWindow (ahlSmall_window κ X) := by
      simpa only [Ω, ahlSmall_omega, offsetWindow] using hHΩ
    have habs := finiteRootMixUnnorm_inclusionMass_absolute_error_le
      hX hHoff hδ0 hδ (hrel H (by simpa only [Ω] using hHΩ) (by simpa only [r] using hHr))
    simpa only [abs_sub_comm, Ω, ahlSmall_omega, offsetWindow] using habs
  have hsum := coreJanossyTransform_sum_sub_le Ω
    (profileR_ge L d0) (by positivity)
    (a := fun H => rootedMainTerm X H / (windowNX X : ℝ))
    (b := fun H => Stopped.inclusionMass Ω
      (finiteRootMixUnnorm X (ahlSmall_window κ X)) H) hH
  simpa only [Ω, L, r, δ, coreJanossyTransform_div,
    coreJanossyTransform_inclusionMass_eq_janossyTrunc] using hsum

end

end PrimeGapNormality.Prime
