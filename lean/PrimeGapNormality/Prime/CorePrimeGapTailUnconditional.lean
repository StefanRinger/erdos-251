import PrimeGapNormality.Prime.PhysicalRemainderOfGapTail
import PrimeGapNormality.Prime.CorePrimeDensityBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Unconditional first-gap-tail control on logarithmic scale

The old GapTailLogKuperberg calculation required qualitative PNT only for
two counting bounds. Quantitative Bertrand and Chebyshev now prove those
bounds unconditionally. This module reuses the same first-moment
calculation, with explicit constant 20/c instead of 40. No Kuperberg,
PNT, high-gap-moment, or model hypothesis is assumed.
The elementary profile estimates below are the source-preserving
extraction from GapTailLogKuperberg; that legacy file is unchanged.
-/

open Filter Polynomial
open scoped Topology

namespace PrimeGapNormality.Prime.CorePrimeGapTailUnconditional

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem one_lt_of_two_le {X : ℕ} (hX : 2 ≤ X) : (1 : ℝ) < X :=
  lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (Nat.cast_le.mpr hX)

private theorem X_pos {X : ℕ} (hX : 2 ≤ X) : (0 : ℝ) < X :=
  Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hX)

private theorem one_lt_two_mul_real {X : ℕ} (hX : 2 ≤ X) :
    (1 : ℝ) < 2 * (X : ℝ) :=
  lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 2)
      (one_lt_of_two_le hX).le)

private theorem log_X_pos {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log X :=
  Real.log_pos (one_lt_of_two_le hX)

private theorem log_two_mul_pos {X : ℕ} (hX : 2 ≤ X) :
    0 < Real.log (2 * (X : ℝ)) :=
  Real.log_pos (one_lt_two_mul_real hX)

private theorem one_le_log_of_three_le {X : ℕ} (hX : 3 ≤ X) :
    (1 : ℝ) ≤ Real.log X := by
  have h3 : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
    rwa [Real.log_exp] at h
  have hle : Real.log 3 ≤ Real.log X :=
    Real.log_le_log (by positivity : (0 : ℝ) < 3) (by exact_mod_cast hX)
  exact h3.trans hle

private theorem sqrt_le_add {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ x + 1 := by
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hnn : 0 ≤ (Real.sqrt x - 1) ^ 2 := sq_nonneg _
  have hexp : (Real.sqrt x - 1) ^ 2 =
      Real.sqrt x ^ 2 - 2 * Real.sqrt x + 1 := by
    ring
  have : 0 ≤ x - 2 * Real.sqrt x + 1 := by
    rwa [hexp, hsq] at hnn
  have h2 : 2 * Real.sqrt x ≤ x + 1 := by linarith
  have h0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  linarith

private theorem windowG_eq_log {X : ℕ} (hX : 3 ≤ X) :
    windowG X = Real.log X :=
  max_eq_left (one_le_log_of_three_le hX)

private theorem tendsto_windowG_atTop : Tendsto windowG atTop atTop :=
  tendsto_atTop_mono (fun X ↦ le_max_left (Real.log (X : ℝ)) (1 : ℝ))
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))

private theorem add_sqrt_le {x : ℝ} (hx : 0 ≤ x) :
    x + Real.sqrt x ≤ 2 * x + 1 := by
  linarith [sqrt_le_add hx]

private theorem stdProfileL_cast_le {ρ G : ℝ} (hG : 0 ≤ logρ ρ G) :
    (stdProfileL ρ G : ℝ) ≤ logρ ρ G + Real.sqrt (logρ ρ G) + 1 := by
  have ha : 0 ≤ logρ ρ G + Real.sqrt (logρ ρ G) :=
    add_nonneg hG (Real.sqrt_nonneg _)
  simpa [stdProfileL] using (Nat.ceil_lt_add_one (R := ℝ) ha).le

private theorem logρ_log_nonneg {ρ : ℝ} {X : ℕ} (hρ : 1 < ρ) (hX : 3 ≤ X) :
    0 ≤ logρ ρ (Real.log X) :=
  div_nonneg (Real.log_nonneg (one_le_log_of_three_le hX)) (Real.log_pos hρ).le

private theorem tendsto_log_div_self :
    Tendsto (fun X : ℕ => Real.log X / X) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  exact (h0.comp tendsto_natCast_atTop_atTop).congr fun X => by
    rw [Function.comp_apply]

private theorem tendsto_log_sq_div_self :
    Tendsto (fun X : ℕ => Real.log X ^ 2 / X) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (𝓝 0) := by
    simpa [one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 2 (by norm_num)
  exact (h0.comp tendsto_natCast_atTop_atTop).congr fun X => by
    rw [Function.comp_apply]

private theorem tendsto_log_log_div_log :
    Tendsto (fun X : ℕ => Real.log (Real.log X) / Real.log X)
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  exact (h0.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).congr
    fun X => by
      rw [Function.comp_apply, Function.comp_apply]

private theorem tendsto_log_log_mul_log_div_self :
    Tendsto (fun X : ℕ => Real.log (Real.log X) * Real.log X / X)
      atTop (𝓝 0) := by
  have hfun :
      (fun X : ℕ => Real.log (Real.log X) * Real.log X / X) =ᶠ[atTop]
        fun X =>
          (Real.log (Real.log X) / Real.log X) * (Real.log X ^ 2 / X) := by
    filter_upwards [eventually_ge_atTop 3] with X hX
    have hlog : Real.log X ≠ 0 :=
      (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3)
        (by exact_mod_cast hX))).ne'
    have hx0 : (X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hlog, hx0]
  have hmul : Tendsto (fun X : ℕ =>
      (Real.log (Real.log X) / Real.log X) * (Real.log X ^ 2 / X))
      atTop (𝓝 (0 * 0)) :=
    tendsto_log_log_div_log.mul tendsto_log_sq_div_self
  have hmul0 : Tendsto (fun X : ℕ =>
      (Real.log (Real.log X) / Real.log X) * (Real.log X ^ 2 / X))
      atTop (𝓝 0) := by
    simpa using hmul
  exact hmul0.congr' hfun.symm

private theorem eventually_stdProfileL_windowG_le {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      (stdProfileL ρ (windowG X) : ℝ) + 1 ≤ (X : ℝ) / Real.log X := by
  have hnum : Tendsto (fun X : ℕ =>
      (2 * Real.log (Real.log X) / Real.log ρ + 3) * Real.log X / X)
      atTop (𝓝 0) := by
    have hfun :
        (fun X : ℕ =>
            (2 * Real.log (Real.log X) / Real.log ρ + 3) * Real.log X / X) =
          (fun X : ℕ =>
            (2 / Real.log ρ) * (Real.log (Real.log X) * Real.log X / X) +
              3 * (Real.log X / X)) := by
      funext X
      ring
    rw [hfun]
    have hsum :
        Tendsto (fun X : ℕ =>
            (2 / Real.log ρ) * (Real.log (Real.log X) * Real.log X / X) +
              3 * (Real.log X / X))
          atTop (𝓝 ((2 / Real.log ρ) * 0 + 3 * 0)) :=
      (tendsto_log_log_mul_log_div_self.const_mul (2 / Real.log ρ)).add
        (tendsto_log_div_self.const_mul (3 : ℝ))
    simpa using hsum
  have hsmall : ∀ᶠ X : ℕ in atTop,
      (2 * Real.log (Real.log X) / Real.log ρ + 3) * Real.log X / X < 1 :=
    hnum.eventually_lt_const (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop 3] with X hlt hX
  have hG : windowG X = Real.log X := windowG_eq_log hX
  rw [hG]
  have hx : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hX)
  have hx0 : (0 : ℝ) < X := lt_trans (by norm_num) hx
  have hlogX : 0 < Real.log X := Real.log_pos hx
  have hlogρ0 : 0 ≤ logρ ρ (Real.log X) := logρ_log_nonneg hρ hX
  have hL := stdProfileL_cast_le hlogρ0
  have hL2 : (stdProfileL ρ (Real.log X) : ℝ) ≤
      2 * logρ ρ (Real.log X) + 2 := by
    have h1 :
        logρ ρ (Real.log X) + Real.sqrt (logρ ρ (Real.log X)) + 1 ≤
          2 * logρ ρ (Real.log X) + 1 + 1 :=
      _root_.add_le_add (add_sqrt_le hlogρ0) (le_rfl : (1 : ℝ) ≤ 1)
    have heq : 2 * logρ ρ (Real.log X) + 1 + 1 =
        2 * logρ ρ (Real.log X) + 2 := by
      ring
    exact hL.trans (h1.trans_eq heq)
  have hbound : (stdProfileL ρ (Real.log X) : ℝ) + 1 ≤
      2 * Real.log (Real.log X) / Real.log ρ + 3 := by
    have h1 : (stdProfileL ρ (Real.log X) : ℝ) + 1 ≤
        2 * logρ ρ (Real.log X) + 2 + 1 :=
      _root_.add_le_add hL2 (le_rfl : (1 : ℝ) ≤ 1)
    have heq : 2 * logρ ρ (Real.log X) + 2 + 1 =
        2 * Real.log (Real.log X) / Real.log ρ + 3 := by
      simp only [logρ, mul_div_assoc]
      ring
    exact h1.trans_eq heq
  have hmul :
      ((stdProfileL ρ (Real.log X) : ℝ) + 1) * Real.log X / X ≤
        (2 * Real.log (Real.log X) / Real.log ρ + 3) * Real.log X / X :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbound hlogX.le) hx0.le
  have hprod :
      ((stdProfileL ρ (Real.log X) : ℝ) + 1) * Real.log X / X < 1 :=
    lt_of_le_of_lt hmul hlt
  have hmul' : ((stdProfileL ρ (Real.log X) : ℝ) + 1) * Real.log X < X :=
    (div_lt_one hx0).mp hprod
  exact le_of_lt ((lt_div_iff₀ hlogX).mpr hmul')

noncomputable def gapTailCoeff (ρ : ℝ) : ℝ :=
  (20 / CoreDyadicPrimeCounting.dyadicCountConstant) * posMassChebyshevCoeff ρ

theorem gapTailCoeff_nonneg {ρ : ℝ} (hρ : 1 < ρ) :
    0 ≤ gapTailCoeff ρ :=
  mul_nonneg
    (div_nonneg (by norm_num) CoreDyadicPrimeCounting.dyadicCountConstant_pos.le)
    (posMassChebyshevCoeff_nonneg hρ)

private theorem log_six_add_one_le :
    Real.log 6 + 1 ≤ 3 * Real.log 3 := by
  have h1 : (1 : ℝ) ≤ Real.log 3 :=
    one_le_log_of_three_le (le_rfl : (3 : ℕ) ≤ 3)
  have h18 : Real.log 6 + 1 ≤ Real.log 6 + Real.log 3 :=
    _root_.add_le_add le_rfl h1
  have hmul : Real.log 6 + Real.log 3 = Real.log (18 : ℝ) := by
    have h := Real.log_mul (by norm_num : (6 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0)
    have h18 : (6 : ℝ) * 3 = 18 := by norm_num
    rw [h18] at h
    exact h.symm
  have h18_27 : Real.log (18 : ℝ) ≤ Real.log (27 : ℝ) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 18) (by norm_num : (18 : ℝ) ≤ 27)
  have h27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    have hpow : (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [hpow, Real.log_pow]
    norm_cast
  exact (h18.trans_eq hmul).trans (h18_27.trans_eq h27)

theorem eventually_gapTail_avg_windowG
    {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      0 < (seqWindow nthPrime X).card ∧
        windowAvgReal (seqWindow nthPrime X)
            (fun n => seqGapTail ρ nthPrime
              (n + stdProfileL ρ (windowG X))) ≤
          gapTailCoeff ρ * windowG X := by
  have hπ2 := CorePrimeDensity.eventually_primeCounting_two_mul_le
  have hL := eventually_stdProfileL_windowG_le hρ
  have hden := CorePrimeDensity.eventually_seqWindow_card_ge
  filter_upwards [hπ2, hL, hden, eventually_ge_atTop 3] with
    X hπbd hLle hcardge hX
  have hm : 0 < (seqWindow nthPrime X).card :=
    card_seqWindow_nthPrime_pos (lt_of_lt_of_le (by omega : 0 < 3) hX)
  refine ⟨hm, ?_⟩
  have hx : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hX)
  have hx0 : (0 : ℝ) < X := lt_trans (by norm_num) hx
  have hlogX : 0 < Real.log X := Real.log_pos hx
  have hlogge1 : (1 : ℝ) ≤ Real.log X := one_le_log_of_three_le hX
  have hG : windowG X = Real.log X := windowG_eq_log hX
  have h2X : (1 : ℝ) < 2 * (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 2) hx.le)
  have hlog2X : 0 < Real.log (2 * (X : ℝ)) := Real.log_pos h2X
  have hlog_mono : Real.log X ≤ Real.log (2 * (X : ℝ)) :=
    Real.log_le_log hx0
      (le_mul_of_one_le_left hx0.le (by norm_num : (1 : ℝ) ≤ 2))
  set L := stdProfileL ρ (windowG X)
  set N : ℕ := Nat.primeCounting (2 * X) + L
  have hT : windowAvgReal (seqWindow nthPrime X)
        (fun n => seqGapTail ρ nthPrime (n + L)) ≤
      posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
          (Real.log ((N + 2 : ℕ) : ℝ) + 1) /
        ((seqWindow nthPrime X).card : ℝ) := by
    simpa [seqWindowMul_two, N] using
      (conditionT_seqWindowMul_nthPrime_chebyshev_log hρ 2 X L
        (by simpa [seqWindowMul_two] using hm))
  have hN1 : ((N + 1 : ℕ) : ℝ) =
      (Nat.primeCounting (2 * X) : ℝ) + (L : ℝ) + 1 := by
    dsimp only [N]
    rw [Nat.cast_add_one (Nat.primeCounting (2 * X) + L), Nat.cast_add]
  have hπ4 : (Nat.primeCounting (2 * X) : ℝ) ≤
      4 * (X : ℝ) / Real.log X := hπbd
  have hL1 : (L : ℝ) + 1 ≤ (X : ℝ) / Real.log X := hLle
  have hNbd : ((N + 1 : ℕ) : ℝ) ≤ 5 * (X : ℝ) / Real.log X := by
    have hadd := _root_.add_le_add hπ4 hL1
    have hsum :
        4 * (X : ℝ) / Real.log X + (X : ℝ) / Real.log X =
          5 * (X : ℝ) / Real.log X := by
      ring
    have hassoc : (Nat.primeCounting (2 * X) : ℝ) + (L : ℝ) + 1 =
        (Nat.primeCounting (2 * X) : ℝ) + ((L : ℝ) + 1) := by
      ring
    rw [hN1, hassoc]
    exact hadd.trans_eq hsum
  have hN2le : ((N + 2 : ℕ) : ℝ) ≤ 6 * (X : ℝ) := by
    have hN2 : ((N + 2 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) + 1 :=
      Nat.cast_add_one (N + 1)
    have h5 : ((N + 1 : ℕ) : ℝ) ≤ 5 * (X : ℝ) :=
      hNbd.trans (div_le_self
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hx0.le) hlogge1)
    have hmid : ((N + 1 : ℕ) : ℝ) + 1 ≤ 5 * (X : ℝ) + 1 :=
      _root_.add_le_add h5 (le_rfl : (1 : ℝ) ≤ 1)
    have h6 : 5 * (X : ℝ) + 1 ≤ 6 * (X : ℝ) := by
      linarith [hx]
    rw [hN2]
    exact hmid.trans h6
  have hlogN : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤ 4 * Real.log X := by
    have hpos : (0 : ℝ) < (N + 2 : ℕ) := by
      exact_mod_cast (Nat.succ_pos (N + 1))
    have h1 : Real.log ((N + 2 : ℕ) : ℝ) ≤ Real.log (6 * (X : ℝ)) :=
      Real.log_le_log hpos hN2le
    have hlog6X : Real.log (6 * (X : ℝ)) = Real.log 6 + Real.log X :=
      Real.log_mul (by norm_num) hx0.ne'
    have hcomb : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤
        Real.log 6 + Real.log X + 1 :=
      _root_.add_le_add (h1.trans_eq hlog6X) (le_rfl : (1 : ℝ) ≤ 1)
    have h61X : Real.log 6 + Real.log X + 1 ≤
        3 * Real.log 3 + Real.log X := by
      have heq : Real.log 6 + Real.log X + 1 =
          (Real.log 6 + 1) + Real.log X := by
        ring
      exact (le_of_eq heq).trans
        (_root_.add_le_add log_six_add_one_le (le_rfl : Real.log X ≤ Real.log X))
    have h3 : 3 * Real.log 3 ≤ 3 * Real.log X :=
      mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity : (0 : ℝ) < 3)
          (by exact_mod_cast hX)) (by norm_num : (0 : ℝ) ≤ 3)
    have h4 : 3 * Real.log 3 + Real.log X ≤ 4 * Real.log X := by
      have : 3 * Real.log X + Real.log X = 4 * Real.log X := by ring
      exact (_root_.add_le_add h3 (le_rfl : Real.log X ≤ Real.log X)).trans_eq
        this
    exact hcomb.trans (h61X.trans h4)
  have hprod :
      ((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤
        20 * (X : ℝ) := by
    have h1 := mul_le_mul hNbd hlogN
      (add_nonneg (Real.log_natCast_nonneg _) (by norm_num))
      (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hx0.le) hlogX.le)
    have h2 : (5 * (X : ℝ) / Real.log X) * (4 * Real.log X) =
        20 * (X : ℝ) := by
      have h0 : Real.log X ≠ 0 := hlogX.ne'
      field_simp [h0]
      norm_num
    exact h1.trans (le_of_eq h2)
  have hFnum :
      posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
          (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤
        posMassChebyshevCoeff ρ * 20 * (X : ℝ) := by
    have hassoc :
        posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
            (Real.log ((N + 2 : ℕ) : ℝ) + 1) =
          posMassChebyshevCoeff ρ *
            (((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1)) := by
      ring
    have hmul :=
      mul_le_mul_of_nonneg_left hprod (posMassChebyshevCoeff_nonneg hρ)
    have hRHS :
        posMassChebyshevCoeff ρ * (20 * (X : ℝ)) =
          posMassChebyshevCoeff ρ * 20 * (X : ℝ) := by
      ring
    exact hassoc.trans_le (hmul.trans_eq hRHS)
  have hmR : (0 : ℝ) < (seqWindow nthPrime X).card := by
    exact_mod_cast hm
  have hhalfpos : 0 < CoreDyadicPrimeCounting.dyadicCountConstant * ((X : ℝ) / Real.log X) :=
    mul_pos CoreDyadicPrimeCounting.dyadicCountConstant_pos (div_pos hx0 hlogX)
  have havg :
      windowAvgReal (seqWindow nthPrime X)
          (fun n => seqGapTail ρ nthPrime (n + L)) ≤
        posMassChebyshevCoeff ρ * 20 * (X : ℝ) /
          ((seqWindow nthPrime X).card : ℝ) := by
    have hden' : 0 ≤ ((seqWindow nthPrime X).card : ℝ) := Nat.cast_nonneg _
    exact hT.trans (div_le_div_of_nonneg_right hFnum hden')
  have hinv : 1 / ((seqWindow nthPrime X).card : ℝ) ≤
      1 / (CoreDyadicPrimeCounting.dyadicCountConstant * ((X : ℝ) / Real.log X)) :=
    one_div_le_one_div_of_le hhalfpos hcardge
  have hquot :
      posMassChebyshevCoeff ρ * 20 * (X : ℝ) /
          ((seqWindow nthPrime X).card : ℝ) ≤
        posMassChebyshevCoeff ρ * 20 * (X : ℝ) *
          (1 / (CoreDyadicPrimeCounting.dyadicCountConstant * ((X : ℝ) / Real.log X))) := by
    have hnn : 0 ≤ posMassChebyshevCoeff ρ * 20 * (X : ℝ) :=
      mul_nonneg (mul_nonneg (posMassChebyshevCoeff_nonneg hρ)
        (by norm_num : (0 : ℝ) ≤ 20)) hx0.le
    have : posMassChebyshevCoeff ρ * 20 * (X : ℝ) /
          ((seqWindow nthPrime X).card : ℝ) =
        (posMassChebyshevCoeff ρ * 20 * (X : ℝ)) *
          (1 / ((seqWindow nthPrime X).card : ℝ)) := by
      field_simp [hmR.ne']
    rw [this]
    exact mul_le_mul_of_nonneg_left hinv hnn
  have hsimp :
      posMassChebyshevCoeff ρ * 20 * (X : ℝ) *
          (1 / (CoreDyadicPrimeCounting.dyadicCountConstant * ((X : ℝ) / Real.log X))) =
        gapTailCoeff ρ * Real.log X := by
    have hx0' : (X : ℝ) ≠ 0 := hx0.ne'
    have hL' : Real.log X ≠ 0 := hlogX.ne'
    unfold gapTailCoeff
    field_simp [hx0', hL', CoreDyadicPrimeCounting.dyadicCountConstant_pos.ne']
  have hfinal :
      posMassChebyshevCoeff ρ * 20 * (X : ℝ) /
          ((seqWindow nthPrime X).card : ℝ) ≤
        gapTailCoeff ρ * windowG X := by
    rw [hG]
    exact hquot.trans_eq hsimp
  exact havg.trans hfinal

/-- The actual logarithmic first-gap-tail hypothesis, now unconditional. -/
theorem gapTailT_nthPrime_windowG {ρ : ℝ} (hρ : 1 < ρ) :
    GapTailT nthPrime ρ windowG :=
  ⟨hρ, tendsto_windowG_atTop, nthPrime_div_pow_summable hρ,
    ⟨gapTailCoeff ρ, gapTailCoeff_nonneg hρ,
      eventually_gapTail_avg_windowG hρ⟩⟩

end PrimeGapNormality.Prime.CorePrimeGapTailUnconditional
