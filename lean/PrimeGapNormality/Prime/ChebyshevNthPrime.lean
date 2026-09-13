import PrimeGapNormality.Prime.PrimeSeries
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Basic

/-!
# Chebyshev inversion for `nthPrime`

Mathlib Chebyshev supplies `π(x) ≫ x / log x` (`pi_ge` / `pi_ge'`) and
the eventual matching upper bound `eventually_primeCounting_le`. Galois
inversion `nthPrime_le_iff_succ_le_pi` turns the lower bound into an
explicit `p_n ≪ n log n` estimate, which Condition T needs in place of
the polynomial `nthPrime_le_succ_sq` (`p_n ≤ 144 (n+1)²`).

The constant `4` is elementary from `log 2 ≥ 11/16` and `e < 3`; it is
larger than the Chebyshev-optimal `1 / log 2 ≈ 1.45` only by a fixed
factor. No prime-number theorem.

Indexing: Lean `nthPrime 0 = 2` is paper `p_1`.

Source: mathlib `Chebyshev.pi_ge`, `pi_ge'`,
`eventually_primeCounting_le`; `PrimeSeries.nthPrime_le_iff_succ_le_pi`;
Condition T comment after `posMass_nthPrime_le`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Filter

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ### Logarithm bounds -/

private theorem log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by positivity : (0 : ℝ) < 2)
  have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by
    rw [one_div]
  rw [hinv] at h
  linarith

private theorem log_two_ge_eleven_div_sixteen : (11 / 16 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  have : (11 / 16 : ℝ) < 0.6931471803 := by norm_num
  linarith

private theorem log_two_pos : 0 < Real.log 2 :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) log_two_ge_half

private theorem log_three_ge_one : (1 : ℝ) ≤ Real.log 3 := by
  have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
  rwa [Real.log_exp] at h

private theorem log_four_eq_two_log_two : Real.log 4 = 2 * Real.log 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, Real.log_pow]
  norm_cast

/-! ### Core comparison for `t ≥ 2` -/

private theorem two_le_L {t : ℝ} (ht : 2 ≤ t) :
    (2 : ℝ) ≤ Real.log (t + 1) + 1 := by
  have ht3 : (3 : ℝ) ≤ t + 1 := by linarith
  have hlog : Real.log 3 ≤ Real.log (t + 1) :=
    Real.log_le_log (by positivity : (0 : ℝ) < 3) ht3
  linarith [log_three_ge_one, hlog]

private theorem log_le_two_sqrt_sub {L : ℝ} (hL0 : 0 < L) :
    Real.log L ≤ 2 * (Real.sqrt L - 1) := by
  have hsqrt0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hlog : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 :=
    Real.log_le_sub_one_of_pos hsqrt0
  have hrew : Real.log L = 2 * Real.log (Real.sqrt L) := by
    rw [Real.log_sqrt hL0.le]
    ring
  linarith

private theorem two_mul_sqrt_sub_le {L : ℝ} (hL2 : 2 ≤ L) :
    2 * (Real.sqrt L - 1) ≤ (5 / 6) * (L - 1) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hL2
  have hsqL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hdiff : L - 1 = (Real.sqrt L - 1) * (Real.sqrt L + 1) := by
    calc
      L - 1 = Real.sqrt L ^ 2 - 1 := by rw [hsqL]
      _ = (Real.sqrt L - 1) * (Real.sqrt L + 1) := by ring
  have h1lt : (1 : ℝ) < Real.sqrt L := by
    have h1L : (1 : ℝ) < L := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hL2
    have hsqrt : Real.sqrt 1 < Real.sqrt L :=
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) h1L
    simpa [Real.sqrt_one] using hsqrt
  have hLge : (49 / 25 : ℝ) ≤ L :=
    le_trans (by norm_num : (49 / 25 : ℝ) ≤ 2) hL2
  have hsqrt7 : Real.sqrt (49 / 25 : ℝ) = (7 / 5 : ℝ) := by
    rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
  have hs : (7 / 5 : ℝ) ≤ Real.sqrt L := by
    have := Real.sqrt_le_sqrt hLge
    rwa [hsqrt7] at this
  have hcoeff : (2 : ℝ) ≤ (5 / 6) * (Real.sqrt L + 1) := by
    have hmul : (5 / 6 : ℝ) * (7 / 5 + 1) ≤ (5 / 6) * (Real.sqrt L + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hs 1) (by norm_num)
    have heq : (5 / 6 : ℝ) * (7 / 5 + 1) = 2 := by norm_num
    linarith
  have hpos : 0 ≤ Real.sqrt L - 1 := le_of_lt (sub_pos.mpr h1lt)
  have hprod :
      2 * (Real.sqrt L - 1) ≤
        ((5 / 6) * (Real.sqrt L + 1)) * (Real.sqrt L - 1) :=
    mul_le_mul_of_nonneg_right hcoeff hpos
  have hrew :
      ((5 / 6) * (Real.sqrt L + 1)) * (Real.sqrt L - 1) = (5 / 6) * (L - 1) := by
    rw [hdiff]
    ring
  rwa [hrew] at hprod

private theorem three_halves_log_L_le {L : ℝ} (hL2 : 2 ≤ L) :
    (3 / 2) * Real.log L ≤ (5 / 4) * (L - 1) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hL2
  have h1 := log_le_two_sqrt_sub hL0
  have h2 := two_mul_sqrt_sub_le hL2
  have h12 : Real.log L ≤ (5 / 6) * (L - 1) := h1.trans h2
  have hmul :
      (3 / 2) * Real.log L ≤ (3 / 2) * ((5 / 6) * (L - 1)) :=
    mul_le_mul_of_nonneg_left h12 (by norm_num)
  have hrew : (3 / 2 : ℝ) * ((5 / 6) * (L - 1)) = (5 / 4) * (L - 1) := by ring
  rwa [hrew] at hmul

private theorem four_log_two_sub_three_halves_ge :
    (5 / 4 : ℝ) ≤ 4 * Real.log 2 - 3 / 2 := by
  have h := log_two_ge_eleven_div_sixteen
  linarith

/-- Analytic comparison behind `p_n ≤ 4 (n+1) (log(n+2)+1)` for `n ≥ 1`. -/
private theorem inversion_core {t L x : ℝ} (ht : 2 ≤ t)
    (hL : L = Real.log (t + 1) + 1) (hx : x = 4 * t * L) :
    t * Real.log x + Real.log (x + 2) ≤ (x - 1) * Real.log 2 := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht
  have hL2 : (2 : ℝ) ≤ L := by
    rw [hL]
    exact two_le_L ht
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hL2
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have hxpos : 0 < x := by
    rw [hx]
    exact mul_pos (mul_pos h4pos htpos) hLpos
  have hx2 : (2 : ℝ) ≤ x := by
    have h16 : (16 : ℝ) ≤ 4 * t * L := by
      have hmul : (2 : ℝ) * 2 ≤ t * L :=
        mul_le_mul ht hL2 (by norm_num : (0 : ℝ) ≤ 2) htpos.le
      have h4nn : (0 : ℝ) ≤ 4 := h4pos.le
      have hmul4 : (4 : ℝ) * (2 * 2) ≤ 4 * (t * L) :=
        mul_le_mul_of_nonneg_left hmul h4nn
      have hleft : (4 : ℝ) * (2 * 2) = 16 := by norm_num
      have hright : (4 : ℝ) * (t * L) = 4 * t * L := by rw [mul_assoc]
      rwa [hleft, hright] at hmul4
    rw [hx]
    linarith
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hx2
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx1
  have hxsub : t * (4 * L - 1 / 2) ≤ x - 1 := by
    rw [hx]
    linarith
  have hlogx : Real.log x = 2 * Real.log 2 + Real.log t + Real.log L := by
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    have ht0 : t ≠ 0 := htpos.ne'
    have hL0 : L ≠ 0 := hLpos.ne'
    have hsplit : Real.log x = Real.log 4 + Real.log t + Real.log L := by
      rw [hx, mul_assoc, Real.log_mul h4 (mul_ne_zero ht0 hL0),
        Real.log_mul ht0 hL0, add_assoc]
    rw [hsplit, log_four_eq_two_log_two]
  have hlog_succ : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
    have hx2x : x + 2 ≤ 2 * x := by linarith
    have hle : Real.log (x + 2) ≤ Real.log (2 * x) :=
      Real.log_le_log (add_pos_of_pos_of_nonneg hxpos (by norm_num)) hx2x
    have hmul : Real.log (2 * x) = Real.log 2 + Real.log x :=
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne'
    exact hle.trans_eq hmul
  have hquot :
      Real.log (x + 2) / t ≤ (Real.log 2 + Real.log x) / 2 := by
    have hnn : 0 ≤ Real.log (x + 2) :=
      Real.log_nonneg (le_trans (by norm_num : (1 : ℝ) ≤ 2) (by linarith))
    have hnn' : 0 ≤ Real.log 2 + Real.log x :=
      add_nonneg (le_of_lt log_two_pos) hlogx_pos.le
    have h1 : Real.log (x + 2) / t ≤ (Real.log 2 + Real.log x) / t :=
      div_le_div_of_nonneg_right hlog_succ htpos.le
    have h2 : (Real.log 2 + Real.log x) / t ≤ (Real.log 2 + Real.log x) / 2 :=
      div_le_div_of_nonneg_left hnn' (by norm_num : (0 : ℝ) < 2) ht
    exact h1.trans h2
  have hsum :
      Real.log x + Real.log (x + 2) / t ≤
        (7 / 2) * Real.log 2 + (3 / 2) * Real.log t + (3 / 2) * Real.log L := by
    have :
        Real.log x + (Real.log 2 + Real.log x) / 2 =
          (7 / 2) * Real.log 2 + (3 / 2) * Real.log t + (3 / 2) * Real.log L := by
      rw [hlogx]
      ring
    linarith [hquot]
  have hlogt : Real.log t ≤ L - 1 := by
    have hle : Real.log t ≤ Real.log (t + 1) :=
      Real.log_le_log htpos (by linarith : t ≤ t + 1)
    have hrew : Real.log (t + 1) = L - 1 := by
      rw [hL]
      ring
    rwa [hrew] at hle
  have hred :
      (7 / 2) * Real.log 2 + (3 / 2) * Real.log t + (3 / 2) * Real.log L ≤
        (4 * L - 1 / 2) * Real.log 2 := by
    have hLlog := three_halves_log_L_le hL2
    have ha := four_log_two_sub_three_halves_ge
    have hL1 : 0 ≤ L - 1 :=
      sub_nonneg.mpr (le_trans (by norm_num : (1 : ℝ) ≤ 2) hL2)
    have hsmall : (3 / 2) * Real.log L ≤ (4 * Real.log 2 - 3 / 2) * (L - 1) :=
      hLlog.trans (mul_le_mul_of_nonneg_right ha hL1)
    have htL : (3 / 2) * Real.log t ≤ (3 / 2) * (L - 1) :=
      mul_le_mul_of_nonneg_left hlogt (by norm_num)
    linarith [hsmall, htL]
  have hdivd :
      Real.log x + Real.log (x + 2) / t ≤ (4 * L - 1 / 2) * Real.log 2 :=
    hsum.trans hred
  have hmul :
      t * (Real.log x + Real.log (x + 2) / t) ≤
        t * ((4 * L - 1 / 2) * Real.log 2) :=
    mul_le_mul_of_nonneg_left hdivd htpos.le
  have hleft : t * (Real.log x + Real.log (x + 2) / t) =
      t * Real.log x + Real.log (x + 2) := by
    field_simp [htpos.ne']
  have hright :
      t * ((4 * L - 1 / 2) * Real.log 2) ≤ (x - 1) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hxsub (le_of_lt log_two_pos)
    simpa [mul_assoc] using this
  rw [hleft] at hmul
  exact hmul.trans hright

/-! ### Global upper bound -/

private theorem nthPrime_zero_le_succ_mul_log :
    (nthPrime 0 : ℝ) ≤
      4 * ((0 + 1 : ℕ) : ℝ) * (Real.log ((0 + 2 : ℕ) : ℝ) + 1) := by
  have hnth : (nthPrime 0 : ℝ) = 2 := by simp [nthPrime_zero]
  have hcast : ((0 + 1 : ℕ) : ℝ) = 1 := by simp
  have hlog : ((0 + 2 : ℕ) : ℝ) = 2 := by simp
  rw [hnth, hcast, hlog]
  have : (2 : ℝ) ≤ 4 * (Real.log 2 + 1) := by
    have hL : (1 / 2 : ℝ) + 1 ≤ Real.log 2 + 1 := add_le_add_left log_two_ge_half 1
    have hnum : (2 : ℝ) ≤ 4 * ((1 / 2 : ℝ) + 1) := by norm_num
    linarith
  simpa using this

private theorem nthPrime_succ_le_succ_mul_log {n : ℕ} (hn : 1 ≤ n) :
    (nthPrime n : ℝ) ≤
      4 * ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1) := by
  set t : ℝ := ((n + 1 : ℕ) : ℝ)
  set L : ℝ := Real.log ((n + 2 : ℕ) : ℝ) + 1
  set x : ℝ := 4 * t * L
  have ht : (2 : ℝ) ≤ t := by
    have hn1 : (2 : ℕ) ≤ n + 1 := Nat.succ_le_succ hn
    have htR : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hn1
    dsimp only [t]
    exact htR
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht
  have hLdef : L = Real.log (t + 1) + 1 := by
    dsimp only [L, t]
    rw [show n + 2 = n + 1 + 1 from rfl, Nat.cast_add_one]
  have hL2 : (2 : ℝ) ≤ L := by
    rw [hLdef]
    exact two_le_L ht
  have hx2 : (2 : ℝ) ≤ x := by
    have hmul : (2 : ℝ) * 2 ≤ t * L :=
      mul_le_mul ht hL2 (by norm_num : (0 : ℝ) ≤ 2) htpos.le
    have h4nn : (0 : ℝ) ≤ 4 := by positivity
    have hmul4 : (4 : ℝ) * (2 * 2) ≤ 4 * (t * L) :=
      mul_le_mul_of_nonneg_left hmul h4nn
    have hleft : (4 : ℝ) * (2 * 2) = 16 := by norm_num
    have hright : (4 : ℝ) * (t * L) = 4 * t * L := by rw [mul_assoc]
    have : (16 : ℝ) ≤ 4 * t * L := by
      rwa [hleft, hright] at hmul4
    dsimp only [x]
    exact le_trans (by norm_num : (2 : ℝ) ≤ 16) this
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx2
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hx2
  have hcore := inversion_core ht hLdef rfl
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hnum : t * Real.log x ≤ (x - 1) * Real.log 2 - Real.log (x + 2) := by
    linarith [hcore]
  have hdiv : t ≤ ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x :=
    (le_div_iff₀ hlogx).mpr (by linarith [hnum])
  have hm2 : 2 ≤ ⌊x⌋₊ :=
    (Nat.le_floor_iff (le_trans (by norm_num : (0 : ℝ) ≤ 2) hx2)).2 hx2
  have hmR : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hm2
  have hlogm : 0 < Real.log ⌊x⌋₊ :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hmR)
  have hm_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hxm : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hsucc_le : (⌊x⌋₊ : ℝ) + 1 ≤ x + 2 := by linarith [hm_le]
  have hlog_succ_m :
      Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (x + 2) := by
    have hpos : (0 : ℝ) < (⌊x⌋₊ : ℝ) + 1 :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg ⌊x⌋₊) zero_lt_one
    have hcast : ((⌊x⌋₊ + 1 : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) + 1 :=
      Nat.cast_add_one ⌊x⌋₊
    rw [hcast]
    exact Real.log_le_log hpos hsucc_le
  have hBnn : 0 ≤ (x - 1) * Real.log 2 - Real.log (x + 2) := by
    have : 0 ≤ t * Real.log x := mul_nonneg (le_of_lt htpos) hlogx.le
    linarith [hnum]
  have hnum_m :
      (x - 1) * Real.log 2 - Real.log (x + 2) ≤
        (⌊x⌋₊ : ℝ) * Real.log 2 - Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    have h1 : (x - 1) * Real.log 2 ≤ (⌊x⌋₊ : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hxm (le_of_lt log_two_pos)
    linarith [h1, hlog_succ_m]
  have hlogm_le : Real.log ⌊x⌋₊ ≤ Real.log x :=
    Real.log_le_log (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hmR) hm_le
  have hfrac :
      ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x ≤
        ((⌊x⌋₊ : ℝ) * Real.log 2 - Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ)) /
          Real.log ⌊x⌋₊ := by
    have h1 :
        ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x ≤
          ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log ⌊x⌋₊ :=
      div_le_div_of_nonneg_left hBnn hlogm hlogm_le
    have h2 :
        ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log ⌊x⌋₊ ≤
          ((⌊x⌋₊ : ℝ) * Real.log 2 - Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ)) /
            Real.log ⌊x⌋₊ :=
      div_le_div_of_nonneg_right hnum_m hlogm.le
    exact h1.trans h2
  have hge := Chebyshev.pi_ge ⌊x⌋₊
  have hgeCast :
      ((⌊x⌋₊ : ℝ) * Real.log 2 - Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ)) /
          Real.log ⌊x⌋₊ ≤
        (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    simpa only [Nat.cast_add_one] using hge
  have hπ : t ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) :=
    hdiv.trans (hfrac.trans hgeCast)
  have hsucc : n + 1 ≤ Nat.primeCounting ⌊x⌋₊ := by
    have htcast : t = ((n + 1 : ℕ) : ℝ) := rfl
    rw [htcast] at hπ
    exact Nat.cast_le.mp hπ
  have hnth : nthPrime n ≤ ⌊x⌋₊ := (nthPrime_le_iff_succ_le_pi n ⌊x⌋₊).2 hsucc
  exact (Nat.cast_le.mpr hnth).trans hm_le

/-- Chebyshev inversion: `p_n ≤ 4 (n+1) (log(n+2)+1)` for every `n`. -/
theorem nthPrime_le_succ_mul_log (n : ℕ) :
    (nthPrime n : ℝ) ≤
      4 * ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact nthPrime_zero_le_succ_mul_log
  · exact nthPrime_succ_le_succ_mul_log hn

/-- Integer form of `nthPrime_le_succ_mul_log`. -/
theorem nthPrime_le_floor_succ_mul_log (n : ℕ) :
    nthPrime n ≤
      ⌊4 * ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1)⌋₊ := by
  have hx : 0 ≤ 4 * ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1) := by
    have hlog : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    positivity
  exact (Nat.le_floor_iff hx).2 (nthPrime_le_succ_mul_log n)

/-! ### Eventual matching lower bound -/

private theorem tendsto_nthPrime_atTop : Tendsto nthPrime atTop atTop :=
  tendsto_atTop_atTop_of_monotone nthPrime_mono fun b =>
    ⟨b, (Nat.le_add_right b 2).trans (nthPrime_ge_add_two b)⟩

private theorem primeCounting_nthPrime (n : ℕ) :
    Nat.primeCounting (nthPrime n) = n + 1 := by
  have hle : n + 1 ≤ Nat.primeCounting (nthPrime n) :=
    (nthPrime_le_iff_succ_le_pi n (nthPrime n)).1 le_rfl
  have hlt : Nat.primeCounting (nthPrime n) < n + 2 := by
    rw [← not_le]
    intro h
    have : nthPrime (n + 1) ≤ nthPrime n :=
      (nthPrime_le_iff_succ_le_pi (n + 1) (nthPrime n)).2 h
    exact (nthPrime_strictMono (Nat.lt_succ_self n)).not_ge this
  omega

private theorem eventually_primeCounting_le_one :
    ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤
        (Real.log 4 + 1) * n / Real.log n := by
  have h :=
    (Chebyshev.eventually_primeCounting_le (by positivity : (0 : ℝ) < 1)).natCast_atTop
  filter_upwards [h, eventually_ge_atTop 2] with n hn hn2
  have hfloor : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  simpa [hfloor] using hn

/-- Chebyshev inversion in the other direction: eventually
`(n+1) log(n+2) / (log 4 + 1) ≤ p_n`. Uses `π(p_n) = n+1` and
`eventually_primeCounting_le`. -/
theorem eventually_succ_log_le_nthPrime :
    ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) /
          (Real.log 4 + 1) ≤
        (nthPrime n : ℝ) := by
  have hC : 0 < Real.log 4 + 1 :=
    add_pos_of_pos_of_nonneg (Real.log_pos (by norm_num : (1 : ℝ) < 4))
      zero_le_one
  filter_upwards [tendsto_nthPrime_atTop.eventually eventually_primeCounting_le_one]
    with n hπ
  have hp2 : (2 : ℕ) ≤ nthPrime n := by
    have hge := nthPrime_ge_add_two n
    rw [Nat.add_comm] at hge
    exact (Nat.le_add_right 2 n).trans hge
  have hpR : (2 : ℝ) ≤ nthPrime n := by exact_mod_cast hp2
  have hlogp : 0 < Real.log (nthPrime n : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hpR)
  have hπid : (Nat.primeCounting (nthPrime n) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
    simp [primeCounting_nthPrime]
  rw [hπid] at hπ
  have hmul :
      ((n + 1 : ℕ) : ℝ) * Real.log (nthPrime n : ℝ) ≤
        (Real.log 4 + 1) * (nthPrime n : ℝ) :=
    (le_div_iff₀ hlogp).mp hπ
  have hlogn : Real.log ((n + 2 : ℕ) : ℝ) ≤ Real.log (nthPrime n : ℝ) := by
    have hn2 : (0 : ℝ) < (n + 2 : ℕ) := by exact_mod_cast (Nat.succ_pos (n + 1))
    exact Real.log_le_log hn2 (Nat.cast_le.mpr (nthPrime_ge_add_two n))
  have hnum :
      ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) ≤
        (Real.log 4 + 1) * (nthPrime n : ℝ) := by
    have hn1 : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    exact (mul_le_mul_of_nonneg_left hlogn hn1).trans hmul
  rw [div_le_iff₀ hC, mul_comm (nthPrime n : ℝ)]
  exact hnum

end PrimeGapNormality.Prime
