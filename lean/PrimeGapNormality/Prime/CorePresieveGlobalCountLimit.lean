import PrimeGapNormality.Prime.PresieveSmallGlobalConcentration

/-!
# Global presieve lower concentration at every integer window

The clock ceil(exp S) is used ONLY to reuse the proved elementary Brun
error limits. Its logarithm lies between S and 2S. No model is changed:
the early/middle decomposition and count below are always at the actual S.
-/

namespace PrimeGapNormality.Prime.CorePresieveGlobalCountLimit

open Finset Filter
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1500000

def clock (S : ℕ) : ℕ := ⌈Real.exp (S : ℝ)⌉₊
def gap (S : ℕ) : ℝ := windowG (clock S)
def early (S : ℕ) : ℕ := presieveW (gap S)
def rank (S : ℕ) : ℕ := earlyBrunRank (gap S)
def harmonic (S : ℕ) : ℝ := earlyBrunT (gap S)

theorem tendsto_clock_atTop : Tendsto clock atTop atTop :=
  tendsto_nat_ceil_atTop.comp (Real.tendsto_exp_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem tendsto_gap_atTop : Tendsto gap atTop atTop := tendsto_windowG_atTop.comp tendsto_clock_atTop
theorem tendsto_early_atTop : Tendsto early atTop atTop :=
  tendsto_presieveW_windowG_atTop.comp tendsto_clock_atTop

theorem gap_bounds {S : ℕ} (hS : 1 ≤ S) : (S : ℝ) ≤ gap S ∧ gap S ≤ 2 * (S : ℝ) := by
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hceil : Real.exp (S : ℝ) ≤ (clock S : ℝ) := Nat.le_ceil _
  have hpos : (0 : ℝ) < clock S := (Real.exp_pos _).trans_le hceil
  have hlo : (S : ℝ) ≤ Real.log (clock S : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (S : ℝ)) hceil
  have hupper : (clock S : ℝ) ≤ 2 * Real.exp (S : ℝ) := by
    have hh := Nat.ceil_lt_add_one (Real.exp_nonneg (S : ℝ))
    have he : 1 ≤ Real.exp (S : ℝ) := Real.one_le_exp (Nat.cast_nonneg S)
    change (clock S : ℝ) < _ at hh
    linarith
  have hlogupper := Real.log_le_log hpos hupper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlogupper
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  unfold gap windowG
  exact ⟨hlo.trans (le_max_left _ _), max_le (by linarith) (by linarith)⟩

private theorem log_power_div_zero :
    Tendsto (fun x : ℝ => Real.log x ^ (4 : ℕ) / x) atTop (𝓝 0) := by
  simpa only [one_mul, add_zero] using
    Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 4 (by norm_num)

theorem eventually_early_le_window : ∀ᶠ S : ℕ in atTop, early S ≤ S := by
  filter_upwards [(log_power_div_zero.comp tendsto_gap_atTop).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), eventually_ge_atTop 1] with S hh hS
  simp only [Function.comp_apply] at hh
  have hg : 0 < gap S := zero_lt_one.trans_le (le_max_right _ _)
  have hfloor : (early S : ℝ) ≤ Real.log (gap S) ^ (4 : ℕ) := by
    rw [early, presieveW_eq]
    exact Nat.floor_le (by positivity)
  have hpow := (div_lt_iff₀ hg).mp hh
  have hbound := (gap_bounds hS).2
  have he : (early S : ℝ) ≤ S := by linarith
  exact Nat.cast_le.mp he

def rounding (S : ℕ) : ℝ :=
  (2 * ((rank S : ℝ) + 1) * (((Nat.primesLE (early S)).card : ℝ) + 1) ^ (rank S + 1)) /
    ((S : ℝ) * eulerProdNat (early S))

def roundingMajor (S : ℕ) : ℝ :=
  (2 * ((rank S : ℝ) + 1) * ((early S : ℝ) + 1) ^ (rank S + 1) * Real.log (early S : ℝ)) /
    (gap S * eulerProdLowerConst)

theorem tendsto_roundingMajor_zero : Tendsto roundingMajor atTop (𝓝 0) :=
  tendsto_earlyPresieveBrun_rounding_majorant.comp tendsto_clock_atTop

theorem eventually_rounding_le : ∀ᶠ S : ℕ in atTop, rounding S ≤ 2 * roundingMajor S := by
  filter_upwards [tendsto_early_atTop.eventually_ge_atTop 16, eventually_ge_atTop 1]
    with S hw hS
  have hs : (0 : ℝ) < S := Nat.cast_pos.mpr (by omega)
  have hg : 0 < gap S := hs.trans_le (gap_bounds hS).1
  have hl : 0 < Real.log (early S : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < early S by omega))
  have hc := eulerProdLowerConst_pos
  have hd : (gap S / 2) * (eulerProdLowerConst / Real.log (early S : ℝ)) ≤
      (S : ℝ) * eulerProdNat (early S) :=
    mul_le_mul (by linarith [(gap_bounds hS).2]) (eulerProdNat_ge_mul_inv_log hw)
      (by positivity) (Nat.cast_nonneg S)
  have hn : 2 * ((rank S : ℝ) + 1) * (((Nat.primesLE (early S)).card : ℝ) + 1) ^ (rank S + 1) ≤
      2 * ((rank S : ℝ) + 1) * ((early S : ℝ) + 1) ^ (rank S + 1) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add (Nat.cast_le.mpr (card_primesLE_le_self _)) le_rfl
  unfold rounding roundingMajor
  calc
    _ ≤ (2 * ((rank S : ℝ) + 1) * ((early S : ℝ) + 1) ^ (rank S + 1)) /
        ((S : ℝ) * eulerProdNat (early S)) :=
      div_le_div_of_nonneg_right hn (mul_pos hs (eulerProdNat_pos _)).le
    _ ≤ (2 * ((rank S : ℝ) + 1) * ((early S : ℝ) + 1) ^ (rank S + 1)) /
        ((gap S / 2) * (eulerProdLowerConst / Real.log (early S : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = _ := by field_simp [hg.ne', hc.ne', hl.ne'] <;> ring

theorem tendsto_rounding_zero : Tendsto rounding atTop (𝓝 0) := by
  have hh := tendsto_roundingMajor_zero.const_mul 2
  simp only [mul_zero] at hh
  exact squeeze_zero' (Eventually.of_forall fun S => by
    unfold rounding
    have hv := (eulerProdNat_pos (early S)).le
    positivity) eventually_rounding_le hh

def relativeBrunError (S : ℕ) : ℝ :=
  earlyPresieveBrunError S (early S) (rank S) (harmonic S) /
    ((S : ℝ) * eulerProdNat (early S))

theorem tendsto_relativeBrunError_zero : Tendsto relativeBrunError atTop (𝓝 0) := by
  have ht := (tendsto_earlyPresieveBrun_factorialTail_div_eulerProd
    (κ := 1) (by norm_num)).comp tendsto_clock_atTop
  have hh := tendsto_rounding_zero.add ht
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with S hS
  exact (earlyPresieveBrunError_div_main_eq (by omega : 0 < S)).symm

theorem eventually_early_relative_error {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℕ in atTop, ∀ τ : ResidueChoice (early S),
      |((earlyPresieveSurvivors S (early S) τ).card : ℝ) -
        (S : ℝ) * eulerProdNat (early S)| < ε * ((S : ℝ) * eulerProdNat (early S)) := by
  filter_upwards [(tendsto_order.mp tendsto_relativeBrunError_zero).2 ε hε,
    tendsto_clock_atTop.eventually eventually_earlyBrun_harmonic_le,
    tendsto_clock_atTop.eventually eventually_two_earlyBrunT_le_rank_add_one,
    eventually_ge_atTop 1] with S herr hh hr hS
  intro τ
  have hmain : 0 < (S : ℝ) * eulerProdNat (early S) :=
    mul_pos (Nat.cast_pos.mpr (by omega)) (eulerProdNat_pos _)
  have he := (div_lt_iff₀ hmain).mp herr
  exact (earlyPresieve_survivorCount_abs_sub_main_le_brun S (early S) (rank S) τ
    hh (earlyBrunT_nonneg _) hr).trans_lt he

theorem eventually_middle_mean_ge {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ S : ℕ in atTop, ∀ τ : ResidueChoice (early S),
      (1 - ε) * ((S : ℝ) * eulerProdNat S) ≤
        middlePresieveUniformMean S (early S) (earlyPresieveSurvivors S (early S) τ) := by
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).comp tendsto_early_atTop
  filter_upwards [eventually_early_relative_error (show 0 < ε / 3 by positivity),
    ht.eventually (gt_mem_nhds (show 0 < ε / 3 by positivity)),
    eventually_early_le_window, tendsto_early_atTop.eventually_ge_atTop 2] with S he ht hwS hw
  change (4 : ℝ) / (early S : ℝ) < ε / 3 at ht
  intro τ
  let A := earlyPresieveSurvivors S (early S) τ
  have hVw := eulerProdNat_pos (early S)
  have hVS := eulerProdNat_pos S
  have hδ : 0 ≤ 1 - ε / 3 := by linarith
  have hA : (1 - ε / 3) * ((S : ℝ) * eulerProdNat (early S)) ≤ (A.card : ℝ) := by
    have hh := (abs_lt.mp (he τ)).1
    dsimp only [A]
    nlinarith
  have hroot : (1 - ε / 3) * (eulerProdNat S / eulerProdNat (early S)) ≤
      rootedEulerProdNat (early S) S := by
    have hh := (abs_le.mp (rootedEulerProdNat_rel_div hw hwS)).1
    have hq : 0 ≤ eulerProdNat S / eulerProdNat (early S) := div_nonneg hVS.le hVw.le
    have hm := mul_le_mul_of_nonneg_right ht.le hq
    nlinarith
  have hb := mul_le_mul hA hroot (mul_nonneg hδ (div_nonneg hVS.le hVw.le)) (Nat.cast_nonneg A.card)
  have heq : ((1 - ε / 3) * ((S : ℝ) * eulerProdNat (early S))) *
      ((1 - ε / 3) * (eulerProdNat S / eulerProdNat (early S))) =
        ((1 - ε / 3) * (1 - ε / 3)) * ((S : ℝ) * eulerProdNat S) := by
    field_simp [hVw.ne'] <;> ring
  rw [heq] at hb
  have hcoef : 1 - ε ≤ (1 - ε / 3) * (1 - ε / 3) := by nlinarith
  exact (mul_le_mul_of_nonneg_right hcoef (mul_nonneg (Nat.cast_nonneg S) hVS.le)).trans
    (hb.trans (middlePresieveUniformMean_ge_card_mul_rooted S (early S) A hw))

theorem tendsto_early_mul_euler_sq_atTop :
    Tendsto (fun S : ℕ => (early S : ℝ) * eulerProdNat S ^ 2) atTop atTop := by
  have hc := eulerProdLowerConst_pos
  have hlog := Real.tendsto_log_atTop.comp tendsto_gap_atTop
  have hlower : Tendsto (fun S : ℕ => (eulerProdLowerConst ^ 2 / 2) * Real.log (gap S) ^ 2)
      atTop atTop := by
    exact Filter.Tendsto.const_mul_atTop (by positivity)
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog)
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [eventually_ge_atTop 16, hlog.eventually_ge_atTop 2] with S hS hl
  simp only [Function.comp_apply] at hl
  have hlogS : 0 < Real.log (S : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < S by omega))
  have hlogQ : 0 < Real.log (gap S) := by linarith
  have hsle := (gap_bounds (by omega : 1 ≤ S)).1
  have hlogle : Real.log (S : ℝ) ≤ Real.log (gap S) :=
    Real.log_le_log (Nat.cast_pos.mpr (by omega)) hsle
  have hv : eulerProdLowerConst / Real.log (gap S) ≤ eulerProdNat S :=
    (div_le_div_of_nonneg_left eulerProdLowerConst_pos.le hlogS hlogle).trans
      (eulerProdNat_ge_mul_inv_log hS)
  have hwfloor : Real.log (gap S) ^ (4 : ℕ) < (early S : ℝ) + 1 := by
    simpa only [early, presieveW_eq] using Nat.lt_floor_add_one (Real.log (gap S) ^ (4 : ℕ))
  have hsq : 4 ≤ Real.log (gap S) ^ 2 := by nlinarith [sq_nonneg (Real.log (gap S) - 2)]
  have hw : Real.log (gap S) ^ (4 : ℕ) / 2 ≤ (early S : ℝ) := by
    nlinarith [sq_nonneg (Real.log (gap S) ^ 2 - 4)]
  have hp := mul_le_mul hw (pow_le_pow_left₀ (by positivity) hv 2)
    (sq_nonneg _) (Nat.cast_nonneg _)
  have heq : (Real.log (gap S) ^ (4 : ℕ) / 2) *
      (eulerProdLowerConst / Real.log (gap S)) ^ 2 =
      (eulerProdLowerConst ^ 2 / 2) * Real.log (gap S) ^ 2 := by
    field_simp [hlogQ.ne'] <;> ring
  rwa [heq] at hp

/-- Genuine lower-count concentration for the full rooted presieve at
every natural S. No profile, independent-law replacement, or concentration
predicate is a premise. -/
theorem tendsto_presieve_lower_mass {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Tendsto (fun S : ℕ => presieveSmallGlobalLowerMass S
      ((1 - ε) * ((S : ℝ) * eulerProdNat S))) atTop (𝓝 0) := by
  have hh := (tendsto_inv_atTop_zero.comp tendsto_early_mul_euler_sq_atTop).const_mul (64 / ε ^ 2)
  simp only [mul_zero] at hh
  refine squeeze_zero' (Eventually.of_forall fun S => presieveSmallGlobalLowerMass_nonneg _ _) ?_ hh
  filter_upwards [eventually_middle_mean_ge (show 0 < ε / 2 by positivity) (by linarith : ε / 2 ≤ 1),
    eventually_early_le_window, tendsto_early_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with S hm hwS hw hS
  let V := (S : ℝ) * eulerProdNat S
  have hs : (0 : ℝ) < S := Nat.cast_pos.mpr (by omega)
  have hV : 0 < V := mul_pos hs (eulerProdNat_pos S)
  have hu : 0 < (ε / 2) * V := mul_pos (by positivity) hV
  have hmean : ∀ τ : ResidueChoice (early S),
      (1 - ε) * V + (ε / 2) * V ≤
        middlePresieveUniformMean S (early S) (earlyPresieveSurvivors S (early S) τ) := by
    intro τ
    have heq : (1 - ε) * V + (ε / 2) * V = (1 - ε / 2) * V := by ring
    rw [heq]
    exact hm τ
  have hmass := presieveSmallGlobalLowerMass_le_of_mean S (early S) hwS hu hmean
  have hwidth := div_le_div_of_nonneg_right (middleWidthSq_le S (early S) hw) (sq_nonneg ((ε / 2) * V))
  have heq : (16 * (S : ℝ) ^ 2 / early S) / ((ε / 2) * V) ^ 2 =
      (64 / ε ^ 2 : ℝ) * ((early S : ℝ) * eulerProdNat S ^ 2)⁻¹ := by
    have hwp : (0 : ℝ) < early S := Nat.cast_pos.mpr (by omega)
    dsimp only [V]
    field_simp [hε.ne', hs.ne', (eulerProdNat_pos S).ne', hwp.ne'] <;> ring
  rw [heq] at hwidth
  exact hmass.trans hwidth

end
end PrimeGapNormality.Prime.CorePresieveGlobalCountLimit
