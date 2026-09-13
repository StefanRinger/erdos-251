import PrimeGapNormality.Prime.CorePresieveTwoSidedLipschitz
import PrimeGapNormality.Prime.CoreCoordinateVarianceFinite
import PrimeGapNormality.Prime.CoreCalibratedMixtureProfile

namespace PrimeGapNormality.Prime.CorePresieveTwoSided
open Finset Filter CorePresieveGlobalCountLimit
open scoped Topology Classical
noncomputable section

theorem middle_two_sided_tail (S w : ℕ) {A : Finset ℕ}
    (hA : A ⊆ Icc 1 S) {u : ℝ} (hu : 0 < u) :
    (((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
      u ≤ |((middlePresieveSurvivors S w A υ).card : ℝ) -
        middlePresieveUniformMean S w A|).card : ℝ) /
      (Fintype.card (MiddleResidueChoice w S) : ℝ) ≤ middleWidthSq S w / u ^ 2 := by
  have h := piCoord_deviation_mass_le_quarter
    (fun _p : MiddlePrime w S => uniformFin)
    (fun υ : MiddleResidueChoice w S => ((middlePresieveSurvivors S w A υ).card : ℝ))
    (fun p : MiddlePrime w S => residueWidth (S : ℝ) p.val)
    (fun _ a => uniformFin_nonneg a)
    (fun p => uniformFin_sum (Nat.sub_pos_of_lt
      (Nat.prime_of_mem_primesLE (sdiff_subset p.property)).one_lt))
    (fun p => residueWidth_nonneg (Nat.cast_nonneg S) (Nat.cast_pos.mpr
      (Nat.prime_of_mem_primesLE (sdiff_subset p.property)).pos))
    (middlePresieve_count_lipschitz S w hA) hu
  have hmass (υ : MiddleResidueChoice w S) :
      (∏ p : MiddlePrime w S, uniformFin (υ p)) =
        (Fintype.card (MiddleResidueChoice w S) : ℝ)⁻¹ := by
    unfold uniformFin
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
    simp only [Fintype.card_fin]
  simp_rw [hmass] at h
  have hE : (∑ υ : MiddleResidueChoice w S,
      (Fintype.card (MiddleResidueChoice w S) : ℝ)⁻¹ *
        ((middlePresieveSurvivors S w A υ).card : ℝ)) =
      middlePresieveUniformMean S w A := by
    rw [← mul_sum]
    simp only [middlePresieveUniformMean, div_eq_mul_inv, mul_comm]
  rw [hE, sum_const, nsmul_eq_mul] at h
  change _ ≤ middleWidthSq S w / (4 * u ^ 2) at h
  have hden : u ^ 2 ≤ 4 * u ^ 2 := by nlinarith [sq_nonneg u]
  have hle := div_le_div_of_nonneg_left (middleWidthSq_nonneg S w)
    (sq_pos_of_pos hu) hden
  calc
    _ ≤ middleWidthSq S w / (4 * u ^ 2) := by
      simpa only [div_eq_mul_inv] using h
    _ ≤ middleWidthSq S w / u ^ 2 := hle

/-- Actual full rooted-presieve TWO-SIDED relative error event. -/
def twoSidedMass (S : ℕ) (ε : ℝ) : ℝ :=
  (((univ : Finset (ResidueChoice S)).filter fun σ =>
    ε * ((S : ℝ) * eulerProdNat S) <
      |((presieveSurvivors S σ).card : ℝ) - (S : ℝ) * eulerProdNat S|).card : ℝ) /
    (Fintype.card (ResidueChoice S) : ℝ)

theorem twoSidedMass_nonneg (S : ℕ) (ε : ℝ) : 0 ≤ twoSidedMass S ε :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem twoSidedMass_le_of_mean (S w : ℕ) (hwS : w ≤ S) {ε u : ℝ} (hu : 0 < u)
    (hmean : ∀ τ : ResidueChoice w,
      |middlePresieveUniformMean S w (earlyPresieveSurvivors S w τ) -
        (S : ℝ) * eulerProdNat S| ≤ ε * ((S : ℝ) * eulerProdNat S) - u) :
    twoSidedMass S ε ≤ middleWidthSq S w / u ^ 2 := by
  let B := middleWidthSq S w / u ^ 2
  have hCearly : (0 : ℝ) < Fintype.card (ResidueChoice w) :=
    Nat.cast_pos.mpr (residueChoice_card_pos w)
  have hCmiddle : (0 : ℝ) < Fintype.card (MiddleResidueChoice w S) := by
    have hnat : 0 < Fintype.card (MiddleResidueChoice w S) := by
      rw [Fintype.card_pi]
      exact prod_pos fun p _ => by
        rw [Fintype.card_fin]
        exact Nat.sub_pos_of_lt
          (Nat.prime_of_mem_primesLE (sdiff_subset p.property)).one_lt
    exact Nat.cast_pos.mpr hnat
  have hpoint : ∀ τ : ResidueChoice w,
      (((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
        ε * ((S : ℝ) * eulerProdNat S) <
          |((presieveSurvivors S (earlyMiddleGlue w S hwS τ υ)).card : ℝ) -
            (S : ℝ) * eulerProdNat S|).card : ℝ) ≤
        (Fintype.card (MiddleResidueChoice w S) : ℝ) * B := by
    intro τ
    have hsub :
        ((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
          ε * ((S : ℝ) * eulerProdNat S) <
            |((presieveSurvivors S (earlyMiddleGlue w S hwS τ υ)).card : ℝ) -
              (S : ℝ) * eulerProdNat S|) ⊆
        ((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
          u ≤ |((middlePresieveSurvivors S w (earlyPresieveSurvivors S w τ) υ).card : ℝ) -
            middlePresieveUniformMean S w (earlyPresieveSurvivors S w τ)|) := by
      intro υ hυ
      have hbad := (mem_filter.mp hυ).2
      rw [presieveSurvivors_earlyMiddleGlue] at hbad
      have htri := abs_sub_le
        ((middlePresieveSurvivors S w (earlyPresieveSurvivors S w τ) υ).card : ℝ)
        (middlePresieveUniformMean S w (earlyPresieveSurvivors S w τ))
        ((S : ℝ) * eulerProdNat S)
      exact mem_filter.mpr ⟨mem_univ _, by linarith [hmean τ]⟩
    have htail := middle_two_sided_tail S w (earlyPresieveSurvivors_subset_Icc S w τ) hu
    have hcount := (div_le_iff₀ hCmiddle).mp htail
    exact (Nat.cast_le.mpr (card_le_card hsub)).trans (by
      simpa only [B, mul_comm] using hcount)
  unfold twoSidedMass
  rw [earlyMiddle_card_filter_eq_sum w S hwS,
    earlyMiddle_residueChoice_card w S hwS, Nat.cast_mul, Nat.cast_sum]
  apply (div_le_iff₀ (mul_pos hCearly hCmiddle)).mpr
  calc
    _ ≤ ∑ _τ : ResidueChoice w,
        (Fintype.card (MiddleResidueChoice w S) : ℝ) * B := sum_le_sum fun τ _ => hpoint τ
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; dsimp only [B]; ring

theorem eventually_twoSidedMass_le_log_sq
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℕ in atTop,
      twoSidedMass S ε ≤
        CorePresieveCountRate.presieveLowerRateConstant ε / Real.log (S : ℝ) ^ 2 := by
  have hc := eulerProdLowerConst_pos
  have hlogGap : Tendsto (fun S : ℕ ↦ Real.log (gap S)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_gap_atTop
  filter_upwards [eventually_middle_mean_abs_sub_any
      (show 0 < ε / 2 by positivity),
    eventually_early_le_window, tendsto_early_atTop.eventually_ge_atTop 1,
    hlogGap.eventually_ge_atTop 2, eventually_ge_atTop 16]
      with S hm hwS hw hlogGap2 hS16
  let V := (S : ℝ) * eulerProdNat S
  let t := Real.log (S : ℝ)
  let q := Real.log (gap S)
  have hSpos : (0 : ℝ) < S := Nat.cast_pos.mpr (by omega)
  have hSone : (1 : ℝ) < S := by exact_mod_cast (show 1 < S by omega)
  have htpos : 0 < t := by
    dsimp only [t]
    exact Real.log_pos hSone
  have hq2 : 2 ≤ q := by simpa only [q, Function.comp_apply] using hlogGap2
  have hqpos : 0 < q := by linarith
  have hV : 0 < V := mul_pos hSpos (eulerProdNat_pos S)
  have hu : 0 < (ε / 2) * V := mul_pos (by positivity) hV
  have hmean : ∀ τ : ResidueChoice (early S),
      |middlePresieveUniformMean S (early S)
          (earlyPresieveSurvivors S (early S) τ) -
        (S : ℝ) * eulerProdNat S| ≤ ε * ((S : ℝ) * eulerProdNat S) - (ε / 2) * V := by
    intro τ
    have hh := hm τ
    dsimp only [V]
    convert hh using 1 <;> ring
  have hmass := twoSidedMass_le_of_mean S (early S) hwS hu hmean
  have hwidth := div_le_div_of_nonneg_right
    (middleWidthSq_le S (early S) hw) (sq_nonneg ((ε / 2) * V))
  have hvariance :
      twoSidedMass S ε ≤
        (64 / ε ^ 2 : ℝ) *
          ((early S : ℝ) * eulerProdNat S ^ 2)⁻¹ := by
    have heq : (16 * (S : ℝ) ^ 2 / early S) / ((ε / 2) * V) ^ 2 =
        (64 / ε ^ 2 : ℝ) *
          ((early S : ℝ) * eulerProdNat S ^ 2)⁻¹ := by
      have hwpos : (0 : ℝ) < early S := Nat.cast_pos.mpr (by omega)
      dsimp only [V]
      field_simp [hε.ne', hSpos.ne', (eulerProdNat_pos S).ne', hwpos.ne'] <;> ring
    rw [heq] at hwidth
    exact hmass.trans hwidth
  have hgapLower : (S : ℝ) ≤ gap S := (gap_bounds (by omega : 1 ≤ S)).1
  have htq : t ≤ q := by
    dsimp only [t, q]
    exact Real.log_le_log hSpos hgapLower
  have hearlyFloor : q ^ (4 : ℕ) < (early S : ℝ) + 1 := by
    simpa only [early, presieveW_eq, q] using
      Nat.lt_floor_add_one (q ^ (4 : ℕ))
  have hq4 : (2 : ℝ) ≤ q ^ (4 : ℕ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hq2 4
    norm_num at hh
    linarith
  have hearlyLower : q ^ (4 : ℕ) / 2 ≤ (early S : ℝ) := by
    nlinarith [sq_nonneg (q ^ 2 - 4)]
  have ht0 : 0 ≤ t := htpos.le
  have htPow : t ^ (4 : ℕ) ≤ q ^ (4 : ℕ) :=
    pow_le_pow_left₀ ht0 htq 4
  have hearlyLog : t ^ (4 : ℕ) / 2 ≤ (early S : ℝ) :=
    (div_le_div_of_nonneg_right htPow (by norm_num : (0 : ℝ) ≤ 2)).trans
      hearlyLower
  have hVlower : eulerProdLowerConst / t ≤ eulerProdNat S := by
    dsimp only [t]
    exact eulerProdNat_ge_mul_inv_log hS16
  have hVlower0 : 0 ≤ eulerProdLowerConst / t :=
    div_nonneg eulerProdLowerConst_pos.le htpos.le
  have hprod := mul_le_mul hearlyLog
    (pow_le_pow_left₀ hVlower0 hVlower 2)
    (sq_nonneg _) (Nat.cast_nonneg (early S))
  have hlower :
      (eulerProdLowerConst ^ 2 / 2) * t ^ 2 ≤
        (early S : ℝ) * eulerProdNat S ^ 2 := by
    have heq : (t ^ (4 : ℕ) / 2) *
        (eulerProdLowerConst / t) ^ 2 =
          (eulerProdLowerConst ^ 2 / 2) * t ^ 2 := by
      field_simp [htpos.ne'] <;> ring
    rwa [heq] at hprod
  have hlowerPos : 0 < (eulerProdLowerConst ^ 2 / 2) * t ^ 2 := by
    positivity
  have hinv :
      ((early S : ℝ) * eulerProdNat S ^ 2)⁻¹ ≤
        ((eulerProdLowerConst ^ 2 / 2) * t ^ 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hlowerPos hlower
  have hscaled := mul_le_mul_of_nonneg_left hinv
    (by positivity : (0 : ℝ) ≤ 64 / ε ^ 2)
  exact hvariance.trans (hscaled.trans_eq (by
    unfold CorePresieveCountRate.presieveLowerRateConstant
    dsimp only [t]
    field_simp [hε.ne', eulerProdLowerConst_pos.ne', htpos.ne'] <;> ring))

/-- The same actual two-sided bound on the paper's physical span, with
its stated logarithmic gap scale and a constant independent of ε and κ.
The profile ratio is weaker than the paper's O(sqrt(log G)) hypothesis. -/
theorem eventually_paper_twoSidedMass_le
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ ε : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      twoSidedMass (CoreCalibratedMixtureProfile.physicalSpan G M X) ε ≤
        128 / (ε ^ 2 * eulerProdLowerConst ^ 2 * Real.log (G X) ^ 2) := by
  have hspan := CoreCalibratedMixtureProfile.tendsto_physicalSpan_atTop hG hκ hM
  filter_upwards [hspan.eventually (eventually_twoSidedMass_le_log_sq hε),
    CoreCalibratedMixtureProfile.eventually_rank_pos hG hκ hM,
    hG.eventually_ge_atTop 5] with X hbound hMpos hG5
  let S := CoreCalibratedMixtureProfile.physicalSpan G M X
  have hG0 : 0 < G X := by linarith
  have hM1 : (1 : ℝ) ≤ M X := by exact_mod_cast hMpos
  have hfloor := Nat.lt_floor_add_one ((6 / 5 : ℝ) * (M X : ℝ) * G X)
  have hcoef := mul_le_mul_of_nonneg_right hM1 hG0.le
  have hGS : G X ≤ (S : ℝ) := by
    change (6 / 5 : ℝ) * (M X : ℝ) * G X < (S : ℝ) + 1 at hfloor
    nlinarith
  have hlog0 : 0 < Real.log (G X) := Real.log_pos (by linarith)
  have hlog : Real.log (G X) ≤ Real.log (S : ℝ) := Real.log_le_log hG0 hGS
  have hsquare : Real.log (G X) ^ 2 ≤ Real.log (S : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlog0.le hlog 2
  have hmono := div_le_div_of_nonneg_left
    (CorePresieveCountRate.presieveLowerRateConstant_pos hε).le
    (sq_pos_of_pos hlog0) hsquare
  exact hbound.trans (hmono.trans_eq (by
    unfold CorePresieveCountRate.presieveLowerRateConstant
    rw [div_div]))

theorem tendsto_twoSidedMass_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun S : ℕ => twoSidedMass S ε) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsq := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog
  have hh := (tendsto_inv_atTop_zero.comp hsq).const_mul
    (CorePresieveCountRate.presieveLowerRateConstant ε)
  have hlim : Tendsto (fun S : ℕ => CorePresieveCountRate.presieveLowerRateConstant ε /
      Real.log (S : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using hh
  exact squeeze_zero' (Eventually.of_forall fun S => twoSidedMass_nonneg S ε)
    (eventually_twoSidedMass_le_log_sq hε) hlim

end
end PrimeGapNormality.Prime.CorePresieveTwoSided
