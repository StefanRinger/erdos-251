import PrimeGapNormality.Prime.CoreDyadicPrimeCountingLimit
import PrimeGapNormality.Prime.CrtSieveCutoffEulerProdLeInvLog
import PrimeGapNormality.Prime.ExactRootMix
import PrimeGapNormality.Prime.PrimeSTD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# PNT-free density bounds for the actual dyadic prime window

These are elementary Chebyshev/central-binomial consequences.  In
particular, no Kuperberg or prime-number-theorem premise occurs.  The scalar
root-mixture bound uses only the canonical cutoff inequality
`mixWeightV t ≤ 1 / log t` and the quantitative dyadic count lower bound.
-/

namespace PrimeGapNormality.Prime.CorePrimeDensity

open Filter Finset
open scoped Topology

noncomputable section

/-- Reciprocal of the explicit positive dyadic density constant. -/
def densityReciprocal : ℝ :=
  PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant⁻¹

theorem densityReciprocal_pos : 0 < densityReciprocal :=
  inv_pos.mpr
    PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant_pos

theorem densityReciprocal_le_sixteen : densityReciprocal ≤ 16 := by
  have hlog : (1 : ℝ) ≤ Real.log 4 := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 4))
    simpa only [Real.log_exp] using h
  have hc : (1 / 12 : ℝ) ≤
      PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant := by
    unfold PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant
    linarith
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 12) hc
  unfold densityReciprocal
  calc
    PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant⁻¹ =
        1 / PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant :=
      (one_div _).symm
    _ ≤
        1 / (1 / 12 : ℝ) := hinv
    _ ≤ 16 := by norm_num

private theorem tendsto_nat_div_log :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / Real.log n) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
      simpa only [pow_one, one_mul, add_zero] using
        Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
    exact hreal.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n : ℕ in atTop,
      Real.log n / (n : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact div_pos (Real.log_pos hn1) (by positivity)
  have hwithin : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ)) atTop
      (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hlog, hpos⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hwithin
  refine hinv.congr' (Eventually.of_forall fun n ↦ ?_)
  simp only [Function.comp_apply]
  exact inv_div (Real.log (n : ℝ)) (n : ℝ)

/-- The central-binomial lower bound rewritten for the public window count. -/
theorem eventually_windowNX_ge :
    ∀ᶠ X : ℕ in atTop,
      PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant *
          ((X : ℝ) / Real.log X) ≤ (windowNX X : ℝ) := by
  simpa only [windowNX, mul_div_assoc] using
    PrimeGapNormality.Prime.CoreDyadicPrimeCounting.eventually_primeCounting_sub_ge

/-- Requested exact physical-window form of the same lower bound. -/
theorem eventually_seqWindow_card_ge :
    ∀ᶠ X : ℕ in atTop,
      PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant *
          ((X : ℝ) / Real.log X) ≤ ((seqWindow nthPrime X).card : ℝ) := by
  simpa only [seqWindow_nthPrime_card] using eventually_windowNX_ge

/-- The actual number of primes in `(X,2X]` tends to infinity, without PNT. -/
theorem tendsto_windowNX_atTop : Tendsto windowNX atTop atTop := by
  have hscale : Tendsto
      (fun X : ℕ ↦
        PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant *
          ((X : ℝ) / Real.log X)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop
      PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant_pos
      tendsto_nat_div_log
  have hreal : Tendsto (fun X : ℕ ↦ (windowNX X : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop eventually_windowNX_ge hscale
  exact tendsto_natCast_atTop_iff.mp hreal

/-- Quantitative reciprocal-density estimate used to normalize raw dyadic
errors. -/
theorem eventually_one_div_windowNX_le :
    ∀ᶠ X : ℕ in atTop,
      1 / (windowNX X : ℝ) ≤
        densityReciprocal * Real.log X / (X : ℝ) := by
  filter_upwards [eventually_windowNX_ge, eventually_ge_atTop 3] with X hNX hX
  have hXR : (0 : ℝ) < X := by positivity
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hc :=
    PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant_pos
  have hlower : 0 <
      PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant *
        ((X : ℝ) / Real.log X) :=
    mul_pos hc (div_pos hXR hlog)
  calc
    1 / (windowNX X : ℝ) ≤
        1 / (PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant *
          ((X : ℝ) / Real.log X)) :=
      one_div_le_one_div_of_le hlower hNX
    _ = densityReciprocal * Real.log X / (X : ℝ) := by
      unfold densityReciprocal
      field_simp [hc.ne', hXR.ne', hlog.ne']

/-- Cruder numeric form convenient for clearing a dyadic denominator. -/
theorem eventually_X_div_windowNX_le :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ) / (windowNX X : ℝ) ≤ 16 * Real.log X := by
  filter_upwards [eventually_one_div_windowNX_le,
    eventually_ge_atTop 3] with X hNX hX
  have hXR : (0 : ℝ) < X := by positivity
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < X by omega))).le
  have hmul := mul_le_mul_of_nonneg_left hNX hXR.le
  calc
    (X : ℝ) / (windowNX X : ℝ) =
        (X : ℝ) * (1 / (windowNX X : ℝ)) := by ring
    _ ≤ (X : ℝ) * (densityReciprocal * Real.log X / (X : ℝ)) := hmul
    _ = densityReciprocal * Real.log X := by field_simp [hXR.ne']
    _ ≤ 16 * Real.log X :=
      mul_le_mul_of_nonneg_right densityReciprocal_le_sixteen hlog

private theorem log_four_lt_two : Real.log 4 < 2 := by
  have hlog2 := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  have hfour : Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hfour]
  linarith

/-- Clean unconditional Chebyshev upper bound in the exact form used by the
raw prime-gap tail adapter. -/
theorem eventually_primeCounting_two_mul_le :
    ∀ᶠ X : ℕ in atTop,
      (Nat.primeCounting (2 * X) : ℝ) ≤
        4 * (X : ℝ) / Real.log X := by
  let ε : ℝ := 2 - Real.log 4
  have hε : 0 < ε := sub_pos.mpr log_four_lt_two
  have htwo : Tendsto (fun X : ℕ ↦ 2 * X) atTop atTop :=
    tendsto_atTop_atTop_of_monotone
      (fun _ _ h ↦ Nat.mul_le_mul_left 2 h)
      fun n ↦ ⟨n, Nat.le_mul_of_pos_left n (by omega : 0 < 2)⟩
  have hπ := htwo.eventually (eventually_primeCounting_le_nat hε)
  filter_upwards [hπ, eventually_ge_atTop 3] with X hπ hX
  have hXpos : (0 : ℝ) < X := by positivity
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogle : Real.log (X : ℝ) ≤ Real.log (2 * (X : ℝ)) :=
    Real.log_le_log hXpos (by linarith)
  have hπ' : (Nat.primeCounting (2 * X) : ℝ) ≤
      2 * (2 * (X : ℝ)) / Real.log (2 * (X : ℝ)) := by
    have hcoef : Real.log 4 + ε = 2 := by
      dsimp only [ε]
      ring
    rw [hcoef] at hπ
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hπ
  calc
    (Nat.primeCounting (2 * X) : ℝ) ≤
        2 * (2 * (X : ℝ)) / Real.log (2 * (X : ℝ)) := hπ'
    _ ≤ 2 * (2 * (X : ℝ)) / Real.log (X : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hlogX hlogle
    _ = 4 * (X : ℝ) / Real.log X := by ring

private theorem mixScale_card (X : ℕ) : (mixScale X).card = X := by
  simp [mixScale]
  omega

/-- Every weight in the literal mixture is at most `1/log X`. -/
theorem eventually_mixWeightV_le_inv_log :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X,
      mixWeightV t ≤ 1 / Real.log (X : ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 16)),
    eventually_ge_atTop 3] with X hXexp hX t ht
  have htmem := mem_Ioc.mp (by simpa only [mixScale] using ht)
  have htexp : Real.exp 16 ≤ (t : ℝ) :=
    hXexp.trans (Nat.cast_le.mpr (Nat.le_of_lt htmem.1))
  have hweight : mixWeightV t ≤ 1 / Real.log (t : ℝ) :=
    crtCutV_eulerProdNat_le_inv_log htexp
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogle : Real.log (X : ℝ) ≤ Real.log (t : ℝ) :=
    Real.log_le_log (by positivity) (Nat.cast_le.mpr (Nat.le_of_lt htmem.1))
  exact hweight.trans (one_div_le_one_div_of_le hlogX hlogle)

/-- The mixture numerator has the unconditional calibrated size
`Z_X ≤ X/log X`. -/
theorem eventually_mixZ_le :
    ∀ᶠ X : ℕ in atTop, mixZ X ≤ (X : ℝ) / Real.log X := by
  filter_upwards [eventually_mixWeightV_le_inv_log] with X hweight
  unfold mixZ
  calc
    (∑ t ∈ mixScale X, mixWeightV t) ≤
        ∑ _t ∈ mixScale X, 1 / Real.log (X : ℝ) :=
      sum_le_sum fun t ht ↦ hweight t ht
    _ = ((mixScale X).card : ℝ) * (1 / Real.log (X : ℝ)) := by
      rw [sum_const, nsmul_eq_mul]
    _ = (X : ℝ) / Real.log X := by
      rw [mixScale_card]
      ring

/-- The scalar normalization is eventually bounded; convergence to one is
neither used nor asserted. -/
theorem eventually_mixZeta_le_densityReciprocal :
    ∀ᶠ X : ℕ in atTop, mixZeta X ≤ densityReciprocal := by
  filter_upwards [eventually_mixZ_le, eventually_windowNX_ge,
    eventually_ge_atTop 3] with X hZ hNX hX
  have hXpos : (0 : ℝ) < X := by positivity
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hc :=
    PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant_pos
  have hlower : 0 <
      PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant *
        ((X : ℝ) / Real.log X) := mul_pos hc (div_pos hXpos hlog)
  have hNpos : 0 < (windowNX X : ℝ) := hlower.trans_le hNX
  unfold mixZeta
  calc
    mixZ X / (windowNX X : ℝ) ≤
        ((X : ℝ) / Real.log X) / (windowNX X : ℝ) :=
      div_le_div_of_nonneg_right hZ hNpos.le
    _ ≤ densityReciprocal := by
      apply (div_le_iff₀ hNpos).mpr
      have hscaled := mul_le_mul_of_nonneg_left hNX (inv_nonneg.mpr hc.le)
      unfold densityReciprocal
      calc
        (X : ℝ) / Real.log X =
            PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant⁻¹ *
              (PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant *
                ((X : ℝ) / Real.log X)) := by
          field_simp [hc.ne']
        _ ≤ PrimeGapNormality.Prime.CoreDyadicPrimeCounting.dyadicCountConstant⁻¹ *
            (windowNX X : ℝ) := hscaled

theorem eventually_mixZeta_le_sixteen :
    ∀ᶠ X : ℕ in atTop, mixZeta X ≤ 16 :=
  eventually_mixZeta_le_densityReciprocal.mono fun X hX ↦
    hX.trans densityReciprocal_le_sixteen

theorem eventually_abs_mixZeta_le_densityReciprocal :
    ∀ᶠ X : ℕ in atTop, |mixZeta X| ≤ densityReciprocal := by
  filter_upwards [eventually_mixZeta_le_densityReciprocal] with X hζ
  have hnonneg : 0 ≤ mixZeta X := by
    unfold mixZeta
    exact div_nonneg (mixZ_nonneg X) (Nat.cast_nonneg _)
  simpa only [abs_of_nonneg hnonneg] using hζ

end

end PrimeGapNormality.Prime.CorePrimeDensity
