import PrimeGapNormality.Prime.CorePresieveGlobalCountLimit

/-!
# Quantitative global presieve lower-count mass

For a fixed relative tolerance, the qualitative Brun localization is used
only to put every exposed early fibre above the requested mean. The rate then
comes from the actual finite middle-prime variance, the fourth-power early
cutoff, and the elementary lower bound for the Euler product.

No rate is inferred from a bare `Tendsto` statement.
-/

namespace PrimeGapNormality.Prime.CorePresieveCountRate

open Filter Finset
open CorePresieveGlobalCountLimit
open scoped Topology Classical

noncomputable section

def presieveLowerRateConstant (ε : ℝ) : ℝ :=
  128 / (ε ^ 2 * eulerProdLowerConst ^ 2)

theorem presieveLowerRateConstant_pos {ε : ℝ} (hε : 0 < ε) :
    0 < presieveLowerRateConstant ε := by
  have hc := eulerProdLowerConst_pos
  unfold presieveLowerRateConstant
  positivity

/-- Fixed-tolerance lower-count mass is bounded by an explicit constant over
`(log S)^2`. The threshold may depend on the fixed tolerance, but the bound
holds at every sufficiently large natural window S. -/
theorem eventually_presieve_lower_mass_le_log_sq
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ S : ℕ in atTop,
      presieveSmallGlobalLowerMass S
          ((1 - ε) * ((S : ℝ) * eulerProdNat S)) ≤
        presieveLowerRateConstant ε / Real.log (S : ℝ) ^ 2 := by
  have hc := eulerProdLowerConst_pos
  have hlogGap : Tendsto (fun S : ℕ ↦ Real.log (gap S)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_gap_atTop
  filter_upwards [eventually_middle_mean_ge
      (show 0 < ε / 2 by positivity) (by linarith : ε / 2 ≤ 1),
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
      (1 - ε) * V + (ε / 2) * V ≤
        middlePresieveUniformMean S (early S)
          (earlyPresieveSurvivors S (early S) τ) := by
    intro τ
    have heq : (1 - ε) * V + (ε / 2) * V = (1 - ε / 2) * V := by ring
    rw [heq]
    exact hm τ
  have hmass := presieveSmallGlobalLowerMass_le_of_mean
    S (early S) hwS hu hmean
  have hwidth := div_le_div_of_nonneg_right
    (middleWidthSq_le S (early S) hw) (sq_nonneg ((ε / 2) * V))
  have hvariance :
      presieveSmallGlobalLowerMass S
          ((1 - ε) * ((S : ℝ) * eulerProdNat S)) ≤
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
    unfold presieveLowerRateConstant
    dsimp only [t]
    field_simp [hε.ne', eulerProdLowerConst_pos.ne', htpos.ne'] <;> ring))

/-- The same explicit rate along an arbitrary natural window tending to
infinity. -/
theorem eventually_presieve_lower_mass_le_log_sq_of_tendsto
    {S : ℕ → ℕ} (hS : Tendsto S atTop atTop)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ X : ℕ in atTop,
      presieveSmallGlobalLowerMass (S X)
          ((1 - ε) * ((S X : ℝ) * eulerProdNat (S X))) ≤
        presieveLowerRateConstant ε / Real.log (S X : ℝ) ^ 2 :=
  hS.eventually (eventually_presieve_lower_mass_le_log_sq hε hε1)

end

end PrimeGapNormality.Prime.CorePresieveCountRate
