import PrimeGapNormality.Prime.CorePrimeQuantitativeComparison

/-!
# The full quantlinear display with a uniform leading constant

This leaf packages the already proved explicit model estimate and finite
prime comparison with a visible leading coefficient independent of kappa
and c (in fact also of B). Only finite normalization and error collection
are repeated. No arithmetic estimate, PNT, or discrepancy-rate premise is
added. This matches the complete quantlinear display; it is not a new
headline or an enlargement of the accepted range.
-/

namespace PrimeGapNormality.Prime.CorePrimeUniformLeadingConstant

open Filter Finset MeasureTheory CoreLinearQuantitativeModel CorePrimeQuantitativeComparison
open scoped Topology NNReal Classical BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Fixed before B, kappa, c, the physical scale and every test. -/
def leadingConstant : ℝ := 10368 / eulerProdLowerConst

theorem leadingConstant_pos : 0 < leadingConstant :=
  div_pos (by norm_num) eulerProdLowerConst_pos

private theorem mixZ_positive {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos'
  · exact fun t _ => mixWeightV_nonneg t
  · refine ⟨2 * X, ?_, eulerProdNat_pos _⟩
    simp only [mixScale, mem_Ioc]
    omega

private theorem collect_errors {a b d c τ D q e t C K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hc : 0 ≤ c) (hτ : 0 ≤ τ)
    (hD : 0 ≤ D) (hq : 0 ≤ q) (he : 0 ≤ e) (ht : 0 ≤ t)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (heq : e ≤ q) :
    16 * c * (b * e * K + (a * e + d * q) * C) + C * (D + c * q) + τ * t * K ≤
      (16 * c * (a + b + d) + c + τ + 1) * ((D + q) * C + (e + t) * K) := by
  rw [← sub_nonneg]
  have hid :
      (16 * c * (a + b + d) + c + τ + 1) * ((D + q) * C + (e + t) * K) -
        (16 * c * (b * e * K + (a * e + d * q) * C) + C * (D + c * q) + τ * t * K) =
      16 * c * a * (q - e) * C +
        (16 * c * (a + b + d) + c + τ) * D * C +
        (16 * c * b + τ + 1) * q * C +
        (16 * c * (a + d) + c + τ + 1) * e * K +
        (16 * c * (a + b + d) + c + 1) * t * K := by ring
  rw [hid]
  have hqe : 0 ≤ q - e := sub_nonneg.mpr heq
  positivity

/-- The actual prime-gap window estimate with literal fixed coefficient
10368/c_Euler. The scale threshold precedes every test and Lipschitz constant;
the original one-sided discrepancy and all original profiles are retained. -/
theorem corePrimeGap_positive_window_uniform_leading
    (B : ℕ) (hB : 2 ≤ B) {κ c : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hc : 1 ≤ c) :
    ∃ Cerr : ℝ, 0 ≤ Cerr ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0),
        LipschitzWith K f → (∀ x, 0 ≤ f x) →
        windowAvgReal (seqWindow nthPrime X) (fun n => f (corePrimeGapCircleOrbit B n)) ≤
          (10368 / eulerProdLowerConst : ℝ) * c * (∫ x : AddCircle (1 : ℝ), f x) +
            Cerr * (((corePrimeComparisonQuantity X (ahlSmall_omega κ X)
              (profileL κ X) (profileR (profileL κ X) 20) c) +
                (profileL κ X : ℝ)⁻¹) * ‖f‖ +
              (windowG X ^ (-(1 / 2 : ℝ)) +
                windowG X * ((B : ℝ) ^ profileL κ X)⁻¹) * (K : ℝ)) := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hκpos : 0 < κ := (div_pos zero_lt_one (Real.log_pos hBr)).trans_le hκ
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  let a : ℝ := 72 / eulerProdLowerConst
  let b : ℝ := 576 / eulerProdLowerConst * ((B : ℝ) * ((B : ℝ) - 1))
  let d : ℝ := linearCountRateConstant
  let τ : ℝ := CorePrimeGapTailUnconditional.gapTailCoeff (B : ℝ)
  let A : ℝ := 648 / eulerProdLowerConst
  let E : ℝ := 16 * c * (a + b + d) + c + τ + 1
  have ha : 0 ≤ a := div_nonneg (by norm_num) eulerProdLowerConst_pos.le
  have hb : 0 ≤ b := mul_nonneg (div_nonneg (by norm_num) eulerProdLowerConst_pos.le)
    (mul_nonneg (Nat.cast_nonneg B) (sub_nonneg.mpr hBr.le))
  have hd : 0 ≤ d := linearCountRateConstant_pos.le
  have hτ : 0 ≤ τ := CorePrimeGapTailUnconditional.gapTailCoeff_nonneg hBr
  have hA : 0 ≤ A := div_nonneg (by norm_num) eulerProdLowerConst_pos.le
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨E, hE, ?_⟩
  filter_upwards [eventually_coreLinearFiniteRootMean_le_quantitative_explicit B hB hκ,
    eventually_coreMixtureJanossyCalibration_le_inv_profileL hκpos (by norm_num : (0 : ℝ) < 20),
    CorePrimeDensity.eventually_mixZeta_le_sixteen, eventually_corePrime_positiveTail_le B hB hκpos,
    eventually_windowG_rpow_neg_half_le_inv_profileL hκpos, eventually_one_le_profileL hκpos,
    eventually_ge_atTop 1] with X hmodel hcal hζ htail heL hL hX
  intro f K hK hf
  let L := profileL κ X
  let S := ahlSmall_window κ X
  let r := profileR L 20
  let q : ℝ := (L : ℝ)⁻¹
  let e : ℝ := windowG X ^ (-(1 / 2 : ℝ))
  let t : ℝ := windowG X * ((B : ℝ) ^ L)⁻¹
  let D : ℝ := corePrimeComparisonQuantity X (ahlSmall_omega κ X) L r c
  let C : ℝ := ‖f‖
  let I : ℝ := ∫ x : AddCircle (1 : ℝ), f x
  have hN : 0 < windowNX X := windowNX_pos (by omega : 0 < X)
  have hZ : 0 < mixZ X := mixZ_positive hX
  have hq : 0 ≤ q := inv_nonneg.mpr (Nat.cast_nonneg L)
  have he : 0 ≤ e := Real.rpow_nonneg (zero_le_one.trans (crtWindowG_one_le X)) _
  have ht : 0 ≤ t := mul_nonneg (zero_le_one.trans (crtWindowG_one_le X))
    (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg B) _))
  have hD : 0 ≤ D := corePrimeComparisonQuantity_nonneg_general hN hL
    (crtMixProf_le_at κ 20 X) (crtMixProf_odd_at κ 20 X)
  have hC : 0 ≤ C := norm_nonneg f
  have hI : 0 ≤ I := integral_nonneg hf
  by_cases hCeq : C = 0
  · have hfzero : f = 0 := norm_eq_zero.mp (by simpa only [C] using hCeq)
    subst f
    have hr : 0 ≤ (10368 / eulerProdLowerConst : ℝ) * c * 0 +
        E * ((D + q) * 0 + (e + t) * (K : ℝ)) := by
      simp only [mul_zero, add_zero, zero_add]
      exact mul_nonneg hE (mul_nonneg (_root_.add_nonneg he ht) K.coe_nonneg)
    simpa [windowAvgReal, D, q, e, t, L, C] using hr
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCeq)
    have hm : coreLinearStoppedMean B S L (finiteRootMix X S) f ≤
        A * I + (b * e * (K : ℝ) + (a * e + d * q) * C) := by
      simpa only [coreLinearFiniteRootMean, coreLinearStoppedMean, offsetWindow,
        S, L, A, I, a, b, d, q, e, C, div_eq_mul_inv, add_assoc] using hmodel f K hK hf
    have hm0 : 0 ≤ A * I + (b * e * (K : ℝ) + (a * e + d * q) * C) := by positivity
    have hu : coreLinearStoppedMean B S L (finiteRootMixUnnorm X S) f ≤
        16 * (A * I + (b * e * (K : ℝ) + (a * e + d * q) * C)) := by
      rw [coreLinearStoppedMean_finiteRootMixUnnorm_eq_mixZeta_mul hN hZ]
      exact (mul_le_mul_of_nonneg_left hm (crtMixUnnormRem_mixZeta_nonneg X)).trans
        (mul_le_mul_of_nonneg_right hζ hm0)
    have hfull := corePrime_full_positive_window_le_comparisonQuantity
      (B := B) (X := X) (S := S) (L := L) (r := r)
      (ν := finiteRootMixUnnorm X S) (c := c) (C := C)
      hN hL (crtMixProf_le_at κ 20 X) (crtMixProf_odd_at κ 20 X) hc0 hCpos
      (fun U _ => crtMixUnnorm_finiteRootMixUnnorm_nonneg X S U) f hf (fun x => f.apply_le_norm x)
    have hfull' : windowAvgReal (seqWindow nthPrime X) (fun n => f (corePrimeGapCircleOrbit B n)) ≤
        c * coreLinearStoppedMean B S L (finiteRootMixUnnorm X S) f +
          C * (D + c * coreMixtureJanossyCalibration κ 20 X) +
          windowAvgReal (seqWindow nthPrime X) (fun n => |f (corePrimeGapCircleOrbit B n) -
            f (seqGapPolyTailTrunc nthPrime (fun _ => Polynomial.X) B L n : AddCircle (1 : ℝ))|) := by
      simpa only [coreLinearStoppedMean, coreMixtureJanossyCalibration,
        ahlSmall_omega, offsetWindow, S, L, r, D, C, add_assoc] using hfull
    have hcq : C * (D + c * coreMixtureJanossyCalibration κ 20 X) ≤ C * (D + c * q) :=
      mul_le_mul_of_nonneg_left (_root_.add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (by simpa only [q, L] using hcal) hc0)) hC
    have htt : windowAvgReal (seqWindow nthPrime X) (fun n => |f (corePrimeGapCircleOrbit B n) -
        f (seqGapPolyTailTrunc nthPrime (fun _ => Polynomial.X) B L n : AddCircle (1 : ℝ))|) ≤
        τ * t * (K : ℝ) := by simpa only [τ, t, L, mul_assoc] using htail f K hK
    have hraw := hfull'.trans (_root_.add_le_add
      (_root_.add_le_add (mul_le_mul_of_nonneg_left hu hc0) hcq) htt)
    have hcollect := collect_errors ha hb hd hc0 hτ hD hq he ht hC K.coe_nonneg
      (show e ≤ q by simpa only [e, q, L] using heL)
    calc
      _ ≤ c * (16 * (A * I + (b * e * (K : ℝ) + (a * e + d * q) * C))) +
          C * (D + c * q) + τ * t * (K : ℝ) := hraw
      _ = (10368 / eulerProdLowerConst : ℝ) * c * I +
          (16 * c * (b * e * (K : ℝ) + (a * e + d * q) * C) +
            C * (D + c * q) + τ * t * (K : ℝ)) := by dsimp only [A]; ring
      _ ≤ (10368 / eulerProdLowerConst : ℝ) * c * I +
          E * ((D + q) * C + (e + t) * (K : ℝ)) := _root_.add_le_add le_rfl hcollect

end
end PrimeGapNormality.Prime.CorePrimeUniformLeadingConstant
