import PrimeGapNormality.Prime.MixRiemann
import PrimeGapNormality.Prime.SingularSeriesTail
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite tuple calibration at the actual sieve cutoff

The completed singular-series tail compares the literal finite tuple product
with `singularSeries E * V(y)^|E|`.  The cutoff jump and Bernoulli's
inequality replace `V(y)^|E|` by `(log t)^(-|E|)`, at a further relative
cost `|E|/y`.  No admissibility or nonvanishing hypothesis is used.
-/

open Finset
open scoped Classical

namespace PrimeGapNormality.Prime

noncomputable section

private theorem mixLogPow_eq_log_pow_inv (v : ℕ) {t : ℝ} (ht : 1 < t) :
    mixLogPow v t = (Real.log t ^ v)⁻¹ := by
  unfold mixLogPow
  rw [Real.rpow_neg (Real.log_pos ht).le, Real.rpow_natCast]

private theorem eulerProdNat_pow_eq_cutoffFactor_mul_mixLogPow
    (v y : ℕ) {t : ℝ} (ht : 1 < t) :
    eulerProdNat y ^ v =
      (eulerProdNat y * Real.log t) ^ v * mixLogPow v t := by
  rw [mixLogPow_eq_log_pow_inv v ht, mul_pow, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero v (Real.log_pos ht).ne'), mul_one]

/-- The literal singular series is nonnegative under the same finite-tail
hypotheses used by `finiteTupleSieveProduct_relative_error_le`.  This is
derived from the head/tail identity, including the possibility of a zero
finite factor. -/
theorem singularSeries_nonneg_of_completion {E : Finset ℕ} {S y : ℕ}
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < y) (hy : 2 ≤ y)
    (hvy2 : 2 * E.card ^ 2 ≤ y) :
    0 ≤ singularSeries E := by
  have hvquad : E.card ≤ E.card ^ 2 := by
    by_cases hv : E.card = 0
    · simp [hv]
    · have hv1 : 1 ≤ E.card := Nat.one_le_iff_ne_zero.mpr hv
      simpa only [pow_two, mul_one] using Nat.mul_le_mul_left E.card hv1
  have hvy : 2 * E.card ≤ y := (Nat.mul_le_mul_left 2 hvquad).trans hvy2
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (by omega)
  have ha : (E.card : ℝ) ^ 2 / y ≤ 1 / 2 := by
    have hcast : 2 * (E.card : ℝ) ^ 2 ≤ (y : ℝ) := by exact_mod_cast hvy2
    apply (div_le_iff₀ hypos).mpr
    linarith
  have hQ := singularSeriesTail_tprod_bounds hE hSy hvy (by omega)
  have hQhalf : (1 / 2 : ℝ) ≤
      ∏' n : ℕ, singularSeriesTailFactor E y n := by
    linarith [hQ.1]
  have hprod : 0 ≤ singularSeries E * eulerProdNat y ^ E.card := by
    rw [singularSeries_mul_euler_eq_finite_mul_tail hE hSy hvy]
    exact mul_nonneg (finiteTupleSieveProduct_nonneg E y)
      (le_trans (by norm_num) hQhalf)
  exact nonneg_of_mul_nonneg_left hprod (pow_pos (eulerProdNat_pos y) _)

/-- Cutoff calibration for an arbitrary certified sieve cutoff.  The two
relative errors are `2|E|²/y` from the singular-series tail and at most
`|E|/y` from the cutoff jump; the latter is absorbed into `|E|²/y`.
-/
theorem finiteTupleSieveProduct_isSieveCutoff_relative_error_le
    {E : Finset ℕ} {S y : ℕ} {t : ℝ}
    (ht : Real.exp 16 ≤ t) (hy : IsSieveCutoff t y)
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < y)
    (hvy2 : 2 * E.card ^ 2 ≤ y) :
    |finiteTupleSieveProduct E y - singularSeries E * mixLogPow E.card t| ≤
      (3 * (E.card : ℝ) ^ 2 / y) *
        (singularSeries E * mixLogPow E.card t) := by
  have ht1 : 1 < t :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le ht
  have hy16 : 16 ≤ y := isSieveCutoff_ge_sixteen ht hy
  have hy2 : 2 ≤ y := (by omega)
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (by omega)
  have hcut := isSieveCutoff_mul_log ht hy
  rw [eulerProd_coe_nat] at hcut
  let q : ℝ := eulerProdNat y * Real.log t
  have hqpos : 0 < q := by
    dsimp only [q]
    exact mul_pos (eulerProdNat_pos y) (Real.log_pos ht1)
  have hqle : q ≤ 1 := by simpa only [q] using hcut.2
  have hqdef : 1 - q ≤ (y : ℝ)⁻¹ := by
    have hlower : 1 - (y : ℝ)⁻¹ < q := by simpa only [q] using hcut.1
    linarith
  have hbern :
      1 + (E.card : ℝ) * (q - 1) ≤ q ^ E.card :=
    one_add_mul_sub_le_pow (by linarith [hqpos] : (-1 : ℝ) ≤ q) E.card
  have hdefect : 1 - q ^ E.card ≤ (E.card : ℝ) / y := by
    have hfirst : 1 - q ^ E.card ≤ (E.card : ℝ) * (1 - q) := by
      linarith [hbern]
    have hsecond : (E.card : ℝ) * (1 - q) ≤
        (E.card : ℝ) * (y : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hqdef (Nat.cast_nonneg _)
    exact hfirst.trans (hsecond.trans_eq (div_eq_mul_inv _ _).symm)
  have hqpowle : q ^ E.card ≤ 1 := pow_le_one₀ hqpos.le hqle
  have hSS : 0 ≤ singularSeries E :=
    singularSeries_nonneg_of_completion hE hSy hy2 hvy2
  have hB0 : 0 ≤ singularSeries E * mixLogPow E.card t :=
    mul_nonneg hSS (mixLogPow_nonneg E.card ht1)
  have hAeq :
      singularSeries E * eulerProdNat y ^ E.card =
        q ^ E.card * (singularSeries E * mixLogPow E.card t) := by
    rw [eulerProdNat_pow_eq_cutoffFactor_mul_mixLogPow E.card y ht1]
    simp only [q]
    ring
  have hAleB :
      singularSeries E * eulerProdNat y ^ E.card ≤
        singularSeries E * mixLogPow E.card t := by
    rw [hAeq]
    calc
      q ^ E.card * (singularSeries E * mixLogPow E.card t) ≤
          1 * (singularSeries E * mixLogPow E.card t) :=
        mul_le_mul_of_nonneg_right hqpowle hB0
      _ = singularSeries E * mixLogPow E.card t := one_mul _
  have hcal :
      singularSeries E * mixLogPow E.card t -
          singularSeries E * eulerProdNat y ^ E.card ≤
        ((E.card : ℝ) / y) *
          (singularSeries E * mixLogPow E.card t) := by
    rw [hAeq]
    calc
      singularSeries E * mixLogPow E.card t -
          q ^ E.card * (singularSeries E * mixLogPow E.card t) =
          (1 - q ^ E.card) *
            (singularSeries E * mixLogPow E.card t) := by ring
      _ ≤ ((E.card : ℝ) / y) *
          (singularSeries E * mixLogPow E.card t) :=
        mul_le_mul_of_nonneg_right hdefect hB0
  have hcalAbs :
      |singularSeries E * eulerProdNat y ^ E.card -
          singularSeries E * mixLogPow E.card t| ≤
        ((E.card : ℝ) / y) *
          (singularSeries E * mixLogPow E.card t) := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hAleB)]
    exact hcal
  have htail := finiteTupleSieveProduct_relative_error_le hE hSy hy2 hvy2
  have hcoeff0 : 0 ≤ 2 * (E.card : ℝ) ^ 2 / y := by positivity
  have htailB :
      |finiteTupleSieveProduct E y -
          singularSeries E * eulerProdNat y ^ E.card| ≤
        (2 * (E.card : ℝ) ^ 2 / y) *
          (singularSeries E * mixLogPow E.card t) :=
    htail.trans (mul_le_mul_of_nonneg_left hAleB hcoeff0)
  have hvquad : E.card ≤ E.card ^ 2 := by
    by_cases hv : E.card = 0
    · simp [hv]
    · have hv1 : 1 ≤ E.card := Nat.one_le_iff_ne_zero.mpr hv
      simpa only [pow_two, mul_one] using Nat.mul_le_mul_left E.card hv1
  have hvquadR : (E.card : ℝ) ≤ (E.card : ℝ) ^ 2 := by
    exact_mod_cast hvquad
  have hdiv : (E.card : ℝ) / y ≤ (E.card : ℝ) ^ 2 / y :=
    div_le_div_of_nonneg_right hvquadR hypos.le
  have hcoeff :
      2 * (E.card : ℝ) ^ 2 / y + (E.card : ℝ) / y ≤
        3 * (E.card : ℝ) ^ 2 / y := by
    calc
      2 * (E.card : ℝ) ^ 2 / y + (E.card : ℝ) / y ≤
          2 * (E.card : ℝ) ^ 2 / y + (E.card : ℝ) ^ 2 / y :=
        add_le_add le_rfl hdiv
      _ = 3 * (E.card : ℝ) ^ 2 / y := by ring
  have hsplit :
      finiteTupleSieveProduct E y - singularSeries E * mixLogPow E.card t =
        (finiteTupleSieveProduct E y -
          singularSeries E * eulerProdNat y ^ E.card) +
        (singularSeries E * eulerProdNat y ^ E.card -
          singularSeries E * mixLogPow E.card t) := by ring
  rw [hsplit]
  calc
    |(finiteTupleSieveProduct E y -
          singularSeries E * eulerProdNat y ^ E.card) +
        (singularSeries E * eulerProdNat y ^ E.card -
          singularSeries E * mixLogPow E.card t)| ≤
        |finiteTupleSieveProduct E y -
          singularSeries E * eulerProdNat y ^ E.card| +
        |singularSeries E * eulerProdNat y ^ E.card -
          singularSeries E * mixLogPow E.card t| := abs_add_le _ _
    _ ≤ (2 * (E.card : ℝ) ^ 2 / y) *
          (singularSeries E * mixLogPow E.card t) +
        ((E.card : ℝ) / y) *
          (singularSeries E * mixLogPow E.card t) :=
      add_le_add htailB hcalAbs
    _ = (2 * (E.card : ℝ) ^ 2 / y + (E.card : ℝ) / y) *
          (singularSeries E * mixLogPow E.card t) := by ring
    _ ≤ (3 * (E.card : ℝ) ^ 2 / y) *
          (singularSeries E * mixLogPow E.card t) :=
      mul_le_mul_of_nonneg_right hcoeff hB0

/-- The preceding theorem at the concrete least cutoff used by the finite
root mixture. -/
theorem finiteTupleSieveProduct_sieveCutoff_relative_error_le
    {E : Finset ℕ} {S : ℕ} {t : ℝ}
    (ht : Real.exp 16 ≤ t)
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < sieveCutoff t)
    (hvy2 : 2 * E.card ^ 2 ≤ sieveCutoff t) :
    |finiteTupleSieveProduct E (sieveCutoff t) -
        singularSeries E * mixLogPow E.card t| ≤
      (3 * (E.card : ℝ) ^ 2 / sieveCutoff t) *
        (singularSeries E * mixLogPow E.card t) :=
  finiteTupleSieveProduct_isSieveCutoff_relative_error_le ht
    (sieveCutoff_spec
      ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le ht))
    hE hSy hvy2

/-- Mertens' weak cutoff lower bound converts `1/y` into the fixed power
`t^(-eulerProdLowerConst)`.  This is the polynomial-saving form summed in
the mixture calibration. -/
theorem finiteTupleSieveProduct_sieveCutoff_rpow_error_le
    {E : Finset ℕ} {S : ℕ} {t : ℝ}
    (ht : Real.exp 16 ≤ t)
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < sieveCutoff t)
    (hvy2 : 2 * E.card ^ 2 ≤ sieveCutoff t) :
    |finiteTupleSieveProduct E (sieveCutoff t) -
        singularSeries E * mixLogPow E.card t| ≤
      (3 * (E.card : ℝ) ^ 2 * t ^ (-eulerProdLowerConst)) *
        (singularSeries E * mixLogPow E.card t) := by
  have ht1 : 1 < t :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le ht
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hy := sieveCutoff_spec ht1
  have hrpow : t ^ eulerProdLowerConst ≤ (sieveCutoff t : ℝ) :=
    isSieveCutoff_rpow ht hy
  have hinv : ((sieveCutoff t : ℝ))⁻¹ ≤
      (t ^ eulerProdLowerConst)⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos ht0 _) hrpow
  have hinv' : ((sieveCutoff t : ℝ))⁻¹ ≤
      t ^ (-eulerProdLowerConst) := by
    rw [Real.rpow_neg ht0.le]
    exact hinv
  have hcoef :
      3 * (E.card : ℝ) ^ 2 / sieveCutoff t ≤
        3 * (E.card : ℝ) ^ 2 * t ^ (-eulerProdLowerConst) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv'
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hmain0 : 0 ≤ singularSeries E * mixLogPow E.card t := by
    have hy16 := isSieveCutoff_ge_sixteen ht hy
    exact mul_nonneg
      (singularSeries_nonneg_of_completion hE hSy (by omega) hvy2)
      (mixLogPow_nonneg E.card ht1)
  exact (finiteTupleSieveProduct_sieveCutoff_relative_error_le ht hE hSy hvy2).trans
    (mul_le_mul_of_nonneg_right hcoef hmain0)

end

end PrimeGapNormality.Prime
