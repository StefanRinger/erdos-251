import PrimeGapNormality.Prime.CrtLogProfileSDivLogX
import PrimeGapNormality.Prime.CrtNestedCutoffVRatio
import PrimeGapNormality.Prime.CrtPhysicalRetentionToZeroOfLogRatio
import PrimeGapNormality.Prime.PresieveSmallEarlyBrunScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform scales for the positive linear mixture

At the small AHL window

`S_X = ahlSmall_window κ X = floor ((6/5) profileL κ X windowG X)`

this file collects the unconditional scale estimates needed by the positive
linear-model consumer.  Uniformly for `t ∈ mixScale X = (X,2X]`, eventually

* `floor (windowG X) ≤ S_X ≤ sieveCutoff t`;
* `lateRetention S_X (sieveCutoff t) * windowG X / log (windowG X)` is at
  most the fixed absolute constant `3 / eulerProdLowerConst`;
* `(eulerProdNat (sieveCutoff t))⁻¹ / windowG X ≤ 4`.

The constant `3` comes from the elementary eventual estimate
`log S_X ≤ 3 log (windowG X)`.  The last estimate uses the exact cutoff jump
`(15/16) / log t < V(sieveCutoff t)` and `t ≤ 2X`; it does not use a PNT or
an additional Mertens hypothesis.
-/

open Filter Finset
open scoped Topology

namespace PrimeGapNormality.Prime

noncomputable section

/-- The absolute retention constant used by the linear consumer is positive. -/
theorem coreLinearScales_retentionConst_pos :
    0 < (3 : ℝ) / eulerProdLowerConst :=
  div_pos (by norm_num) eulerProdLowerConst_pos

/-- The integer floor of the physical gap scale lies in the small AHL window
eventually. -/
theorem eventually_coreLinearScales_floor_le_small {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      ⌊windowG X⌋₊ ≤ ahlSmall_window κ X := by
  filter_upwards [eventually_windowG_le_ahlSmall_window hκ] with X hGS
  have hfloor : (⌊windowG X⌋₊ : ℝ) ≤ windowG X :=
    Nat.floor_le (ahlSmall_windowG_nonneg X)
  exact Nat.cast_le.mp (hfloor.trans hGS)

/-- The small AHL window eventually contains at least sixteen integers. -/
theorem eventually_coreLinearScales_sixteen_le_small {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, 16 ≤ ahlSmall_window κ X := by
  filter_upwards [eventually_windowG_le_ahlSmall_window hκ,
    tendsto_windowG_atTop.eventually_ge_atTop (16 : ℝ)] with X hGS hG
  exact Nat.cast_le.mp (hG.trans hGS)

/-- Uniformly on the literal finite mixture support, the small AHL window is
below the corresponding least sieve cutoff. -/
theorem eventually_coreLinearScales_small_le_cutoff {κ : ℝ} (hκ : 0 < κ) :
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

/-- Eventually `log S_X ≤ 3 log G_X`.  The numerical constant is independent
of `κ`; only the point at which the estimate starts may depend on `κ`. -/
theorem eventually_coreLinearScales_log_small_le {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (ahlSmall_window κ X : ℝ) ≤
        3 * Real.log (windowG X) := by
  filter_upwards [crtLogSLogX_eventually_profileL_le_log hκ,
    crtWindowG_eventually_eq_log,
    tendsto_windowG_atTop.eventually_ge_atTop (4 : ℝ),
    eventually_coreLinearScales_sixteen_le_small hκ] with
      X hL hGeq hG4 hS16
  let G := windowG X
  have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hG4
  have hLG : (profileL κ X : ℝ) ≤ G := by
    simpa only [G, hGeq] using hL
  have hSprofile : (ahlSmall_window κ X : ℝ) ≤ (profileS κ X : ℝ) :=
    Nat.cast_le.mpr (ahlSmall_window_le_profileS κ X)
  have hSupper : (ahlSmall_window κ X : ℝ) ≤ 4 * G ^ 2 := by
    calc
      (ahlSmall_window κ X : ℝ) ≤ (profileS κ X : ℝ) := hSprofile
      _ ≤ 4 * (profileL κ X : ℝ) * G := by
        simpa only [G] using crtLogSLogX_profileS_le_four κ X
      _ ≤ 4 * G * G :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLG (by norm_num)) hGpos.le
      _ = 4 * G ^ 2 := by ring
  have hSpos : (0 : ℝ) < ahlSmall_window κ X :=
    Nat.cast_pos.mpr (by omega)
  have hlogUpper :
      Real.log (ahlSmall_window κ X : ℝ) ≤ Real.log (4 * G ^ 2) :=
    Real.log_le_log hSpos hSupper
  have hlogForm : Real.log (4 * G ^ 2) = Real.log 4 + 2 * Real.log G := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (pow_ne_zero 2 hGpos.ne'), Real.log_pow]
    norm_num
  have hlog4 : Real.log 4 ≤ Real.log G :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 4) hG4
  rw [hlogForm] at hlogUpper
  linarith

/-- Uniform retention estimate at the concrete small window and every scale
in the finite mixture. -/
theorem eventually_coreLinearScales_retention_bound {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X,
      lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) *
          windowG X / Real.log (windowG X) ≤
        (3 : ℝ) / eulerProdLowerConst := by
  filter_upwards [eventually_coreLinearScales_log_small_le hκ,
    eventually_coreLinearScales_small_le_cutoff hκ,
    eventually_coreLinearScales_sixteen_le_small hκ,
    crtNestVR_eventually_exp_sixteen,
    crtWindowG_eventually_eq_log,
    tendsto_windowG_atTop.eventually_ge_atTop (4 : ℝ)] with
      X hlogS hcut hS16 hXexp hGeq hG4
  intro t ht
  let S := ahlSmall_window κ X
  let G := windowG X
  have htI : t ∈ Ioc X (2 * X) := by simpa [mixScale] using ht
  have hXt : (X : ℝ) < (t : ℝ) := Nat.cast_lt.mpr (mem_Ioc.mp htI).1
  have htexp : Real.exp 16 ≤ (t : ℝ) := hXexp.trans hXt.le
  have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hG4
  have hlogGpos : 0 < Real.log G := Real.log_pos (by linarith)
  have hXpos : (0 : ℝ) < X := (Real.exp_pos 16).trans_le hXexp
  have hX1 : (1 : ℝ) < X :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hXexp
  have ht1 : (1 : ℝ) < t := hX1.trans hXt
  have hlogtpos : 0 < Real.log (t : ℝ) := Real.log_pos ht1
  have hGlelogt : G ≤ Real.log (t : ℝ) := by
    rw [show G = Real.log (X : ℝ) by simpa only [G] using hGeq]
    exact Real.log_le_log hXpos hXt.le
  have hbase :
      lateRetention S (sieveCutoff (t : ℝ)) ≤
        (1 / eulerProdLowerConst) *
          (Real.log (S : ℝ) / Real.log (t : ℝ)) :=
    crtPhysRetZero_le (by omega : 2 ≤ S) hS16 (hcut t ht) htexp
  have hratio :
      Real.log (S : ℝ) / Real.log (t : ℝ) ≤
        3 * Real.log G / G := by
    calc
      Real.log (S : ℝ) / Real.log (t : ℝ) ≤
          (3 * Real.log G) / Real.log (t : ℝ) :=
        div_le_div_of_nonneg_right (by simpa only [S, G] using hlogS)
          hlogtpos.le
      _ ≤ (3 * Real.log G) / G :=
        div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) hlogGpos.le) hGpos hGlelogt
  have htheta :
      lateRetention S (sieveCutoff (t : ℝ)) ≤
        (1 / eulerProdLowerConst) * (3 * Real.log G / G) :=
    hbase.trans (mul_le_mul_of_nonneg_left hratio
      (one_div_nonneg.mpr eulerProdLowerConst_pos.le))
  have hscaled := mul_le_mul_of_nonneg_right htheta
    (div_nonneg hGpos.le hlogGpos.le)
  calc
    lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) *
          windowG X / Real.log (windowG X) =
        lateRetention S (sieveCutoff (t : ℝ)) * (G / Real.log G) := by
      simp only [S, G]
      ring
    _ ≤ ((1 / eulerProdLowerConst) * (3 * Real.log G / G)) *
          (G / Real.log G) := hscaled
    _ = (3 : ℝ) / eulerProdLowerConst := by
      field_simp [eulerProdLowerConst_pos.ne', hGpos.ne', hlogGpos.ne']
      <;> ring

/-- The reciprocal cutoff product is uniformly bounded on the full finite
mixture support.  This is an exact-cutoff consequence, not an asymptotic
Mertens assumption. -/
theorem eventually_coreLinearScales_cutoff_inv_bound :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X,
      (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / windowG X ≤ (4 : ℝ) := by
  filter_upwards [crtNestVR_eventually_exp_sixteen,
    crtWindowG_eventually_eq_log,
    tendsto_windowG_atTop.eventually_ge_atTop (4 : ℝ)] with
      X hXexp hGeq hG4
  intro t ht
  let G := windowG X
  let V := eulerProdNat (sieveCutoff (t : ℝ))
  have htI : t ∈ Ioc X (2 * X) := by simpa [mixScale] using ht
  have hXt : (X : ℝ) < (t : ℝ) := Nat.cast_lt.mpr (mem_Ioc.mp htI).1
  have htUpper : (t : ℝ) ≤ 2 * (X : ℝ) := by
    exact_mod_cast (mem_Ioc.mp htI).2
  have htexp : Real.exp 16 ≤ (t : ℝ) := hXexp.trans hXt.le
  have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hG4
  have hXpos : (0 : ℝ) < X := (Real.exp_pos 16).trans_le hXexp
  have hX1 : (1 : ℝ) < X :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hXexp
  have htpos : (0 : ℝ) < t := hXpos.trans hXt
  have ht1 : (1 : ℝ) < t := hX1.trans hXt
  have hlogtpos : 0 < Real.log (t : ℝ) := Real.log_pos ht1
  have hlogt : Real.log (t : ℝ) ≤ Real.log 2 + G := by
    calc
      Real.log (t : ℝ) ≤ Real.log (2 * (X : ℝ)) :=
        Real.log_le_log htpos htUpper
      _ = Real.log 2 + G := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne']
        simpa only [G] using congrArg (fun z => Real.log 2 + z) hGeq.symm
  have hlog2 : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogtTwo : Real.log (t : ℝ) ≤ 2 * G := by
    linarith
  have hVpos : 0 < V := by
    simpa only [V] using eulerProdNat_pos (sieveCutoff (t : ℝ))
  have hlowerPos : 0 < (15 / 16 : ℝ) / Real.log (t : ℝ) :=
    div_pos (by norm_num) hlogtpos
  have hlower : (15 / 16 : ℝ) / Real.log (t : ℝ) < V := by
    simpa only [V] using
      crtCutV_fifteen_div_sixteen_div_log_lt_eulerProdNat htexp
  have hInv : V⁻¹ ≤ (16 / 15 : ℝ) * Real.log (t : ℝ) := by
    calc
      V⁻¹ ≤ ((15 / 16 : ℝ) / Real.log (t : ℝ))⁻¹ :=
        ((inv_lt_inv₀ hVpos hlowerPos).mpr hlower).le
      _ = (16 / 15 : ℝ) * Real.log (t : ℝ) := by
        field_simp [hlogtpos.ne']
        <;> ring
  calc
    (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / windowG X = V⁻¹ / G := by
      rfl
    _ ≤ ((16 / 15 : ℝ) * Real.log (t : ℝ)) / G :=
      div_le_div_of_nonneg_right hInv hGpos.le
    _ ≤ ((16 / 15 : ℝ) * (2 * G)) / G :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogtTwo (by norm_num)) hGpos.le
    _ = (32 / 15 : ℝ) := by field_simp [hGpos.ne'] <;> ring
    _ ≤ (4 : ℝ) := by norm_num

/-- One bundled interface for the positive linear-model consumer.  It includes
the denominator and Euler-product positivity facts needed to divide by the
displayed scales. -/
theorem eventually_coreLinearMixtureScales {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      1 < windowG X ∧
      0 < Real.log (windowG X) ∧
      16 ≤ ahlSmall_window κ X ∧
      ⌊windowG X⌋₊ ≤ ahlSmall_window κ X ∧
      ∀ t ∈ mixScale X,
        ahlSmall_window κ X ≤ sieveCutoff (t : ℝ) ∧
        0 < eulerProdNat (sieveCutoff (t : ℝ)) ∧
        0 ≤ lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) ∧
        lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) *
            windowG X / Real.log (windowG X) ≤
          (3 : ℝ) / eulerProdLowerConst ∧
        (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / windowG X ≤ (4 : ℝ) := by
  filter_upwards [tendsto_windowG_atTop.eventually (eventually_gt_atTop (4 : ℝ)),
    eventually_coreLinearScales_sixteen_le_small hκ,
    eventually_coreLinearScales_floor_le_small hκ,
    eventually_coreLinearScales_small_le_cutoff hκ,
    eventually_coreLinearScales_retention_bound hκ,
    eventually_coreLinearScales_cutoff_inv_bound] with
      X hG4 hS16 hfloor hcut htheta hV
  have hG1 : 1 < windowG X := by linarith
  refine ⟨hG1, Real.log_pos hG1, hS16, hfloor, ?_⟩
  intro t ht
  exact ⟨hcut t ht, eulerProdNat_pos _,
    (rootedEulerProdNat_pos (show 2 ≤ ahlSmall_window κ X by omega)).le,
    htheta t ht, hV t ht⟩

end

end PrimeGapNormality.Prime
