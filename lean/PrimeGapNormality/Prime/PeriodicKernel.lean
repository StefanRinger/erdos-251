import PrimeGapNormality.Prime.JointLift
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Periodic position-series algebra and positive class/`q`-lift

Finite/algebraic kernel for R101/01 §§3,6,8, audited R101/03, specified
in `rounds/round101/04_common_proof_specification_v1.md` (algebra only)
and released incrementally by R101/02 Fortschreibung / R102/03 item 3.

Implemented here:

* recursion `Γ_r(n+k) = B Γ_r(n) - a_(n+r)` (`B = b^k`);
* root centering for `n ≥ 1`, no `a_0`;
* exact positive offset-tail identity;
* one-point position-shape coefficient;
* localised test comparison on a good span (finite inequality);
* combined positive rank-class / `q`-lift costing `s/H`;
* integer-mode orbit identification and integer diagonal scaling.

Rational leftover denominators use the existing scalar
`weylCriterion_of_mul`. Equal-base `q_i = b_i-1` orbit lifting reuses
`jointWeyl_of_scaled`. This module does **not** assemble S/T/D, does
not prove that primes are normal, and does not claim Q-independence
for distinct bases or `1, α_2, α_4`.

No global first-offset-mean hypothesis: bad-span mass is paid in full;
on the good span the existing tail bound `T` is enough.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §§3,6,8;
`rounds/round101/03_gpt_periodic_weights_second_read.md`;
`rounds/round101/04_common_proof_specification_v1.md`;
`rounds/round101/02_grok_multibase_common_clock_update.md` Fortschreibung.
Contract: API
Audit: GREEN
-/

open Finset
open Filter (Tendsto atTop)
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 2000000

/-! ### Circle character helpers (public `e`) -/

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem e_zero : e 0 = 1 := by
  unfold e
  simp [Complex.exp_zero]

private theorem e_int (n : ℤ) : e n = 1 := by
  unfold e
  simp only [Complex.ofReal_intCast]
  have h : (2 * Real.pi * Complex.I * (n : ℂ)) = n * (2 * Real.pi * Complex.I) := by
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private theorem two_pi_I_mul (x : ℝ) :
    (2 * Real.pi * Complex.I * (x : ℂ) : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) := by
  simp [mul_comm, mul_left_comm, Complex.ofReal_mul]

private theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [two_pi_I_mul, Complex.norm_exp_I_mul_ofReal]

private theorem star_e (x : ℝ) : star (e x) = e (-x) := by
  have hx : e x ≠ 0 := by
    have hn : ‖e x‖ = 1 := norm_e x
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  apply mul_right_cancel₀ hx
  have hstar : star (e x) * e x = ‖e x‖ ^ 2 := by
    rw [mul_comm]
    change e x * starRingEnd ℂ (e x) = ‖e x‖ ^ 2
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [hstar, norm_e]
  simp
  rw [← e_add, neg_add_cancel, e_zero]

private theorem norm_e_sub_one_le (δ : ℝ) : ‖e δ - 1‖ ≤ 2 * Real.pi * |δ| := by
  unfold e
  rw [two_pi_I_mul]
  have hle := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * δ)
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg Real.pi_pos.le, mul_comm, mul_left_comm,
    mul_assoc] using hle

private theorem norm_e_sub_e (s t : ℝ) : ‖e t - e s‖ ≤ 2 * Real.pi * |t - s| := by
  have h : e t - e s = e s * (e (t - s) - 1) := by
    calc
      e t - e s = e (s + (t - s)) - e s := by
        congr 1
        ring
      _ = e s * e (t - s) - e s := by rw [e_add]
      _ = e s * (e (t - s) - 1) := by rw [mul_sub, mul_one]
  rw [h, norm_mul, norm_e, one_mul]
  exact norm_e_sub_one_le (t - s)

private theorem base_ne_zero {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
    (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hB))

private theorem base_pos {B : ℕ} (hB : 2 ≤ B) : (0 : ℝ) < B :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (Nat.cast_le.mpr hB)

private theorem one_lt_base {B : ℕ} (hB : 2 ≤ B) : (1 : ℝ) < B :=
  lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (Nat.cast_le.mpr hB)

private theorem base_sub_one_ne_zero {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) - 1 ≠ 0 :=
  sub_ne_zero.mpr (one_lt_base hB).ne'

private theorem one_div_base_lt_one {B : ℕ} (hB : 2 ≤ B) : (1 : ℝ) / B < 1 :=
  (div_lt_one (base_pos hB)).mpr (one_lt_base hB)

/-! ### Residue arithmetic `j = k m + r`, paper `1 ≤ r ≤ k` -/

/-- Quotient `m = (j-1)/k` in `j = k m + r`. Requires `1 ≤ j`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §3.
Contract: API
Audit: GREEN -/
def periodQuotient (k j : ℕ) : ℕ :=
  (j - 1) / k

/-- Residue `r = (j-1) % k + 1` in `j = k m + r`. Requires `1 ≤ j` and `0 < k`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §3.
Contract: API
Audit: GREEN -/
def periodResidue (k j : ℕ) : ℕ :=
  (j - 1) % k + 1

/-- Paper splitting `j = k·periodQuotient + periodResidue` for `j ≥ 1`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §3.
Contract: API
Audit: GREEN -/
theorem period_div_mod {k j : ℕ} (hk : 0 < k) (hj : 1 ≤ j) :
    j = k * periodQuotient k j + periodResidue k j ∧
      1 ≤ periodResidue k j ∧ periodResidue k j ≤ k := by
  have hsplit : j - 1 = k * ((j - 1) / k) + (j - 1) % k :=
    (Nat.div_add_mod (j - 1) k).symm
  have hr : (j - 1) % k < k := Nat.mod_lt (j - 1) hk
  refine ⟨?_, Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_of_lt hr⟩
  have hdef : k * periodQuotient k j + periodResidue k j =
      k * ((j - 1) / k) + ((j - 1) % k + 1) := rfl
  rw [hdef, ← Nat.add_assoc, ← hsplit, Nat.sub_add_cancel hj]

/-! ### Truncated and infinite periodic tails `Γ_r(n)` -/

/-- Finite tail `Γ_r^M(n) = ∑_{m<M} a_(n+k m+r) B^(-(m+1))`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (3.1).
Contract: API
Audit: GREEN -/
noncomputable def periodicPositionTailTrunc (a : ℕ → ℝ) (B k r n M : ℕ) : ℝ :=
  ∑ m ∈ range M, a (n + k * m + r) / (B : ℝ) ^ (m + 1)

/-- Infinite tail `Γ_r(n) = ∑_m a_(n+k m+r) B^(-(m+1))`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (3.1).
Contract: API
Audit: GREEN -/
noncomputable def periodicPositionTail (a : ℕ → ℝ) (B k r n : ℕ) : ℝ :=
  ∑' m : ℕ, a (n + k * m + r) / (B : ℝ) ^ (m + 1)

/-- Exact finite recursion with a one-step window shift:
`Γ_r^M(n+k) = B Γ_r^(M+1)(n) - a_(n+r)`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (3.1).
Contract: API
Audit: GREEN -/
theorem periodicPositionTailTrunc_shift
    (a : ℕ → ℝ) {B k r n M : ℕ} (hB : 2 ≤ B) :
    periodicPositionTailTrunc a B k r (n + k) M
      = (B : ℝ) * periodicPositionTailTrunc a B k r n (M + 1) - a (n + r) := by
  have hb0 := base_ne_zero hB
  unfold periodicPositionTailTrunc
  have hidx : ∀ m, n + k + k * m + r = n + k * (m + 1) + r := by
    intro m
    ring
  have hLHS :
      ∑ m ∈ range M, a (n + k + k * m + r) / (B : ℝ) ^ (m + 1)
        = ∑ m ∈ range M, a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 1) :=
    sum_congr rfl fun m _ => by rw [hidx m]
  have hpow : ∀ m, (B : ℝ) ^ (m + 2) = (B : ℝ) ^ (m + 1) * B :=
    fun m => pow_succ _ _
  have hterm : ∀ m,
      a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 1)
        = (B : ℝ) * (a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 2)) := by
    intro m
    have hBpow : (B : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ hb0
    calc
      a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 1)
          = (B * a (n + k * (m + 1) + r)) / ((B : ℝ) ^ (m + 1) * B) := by
            rw [mul_comm ((B : ℝ) ^ (m + 1)), mul_div_mul_left _ _ hb0]
      _ = (B : ℝ) * (a (n + k * (m + 1) + r) / ((B : ℝ) ^ (m + 1) * B)) := by
            rw [mul_div_assoc]
      _ = (B : ℝ) * (a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 2)) := by
            rw [hpow m]
  have hscale :
      ∑ m ∈ range M, a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 1)
        = (B : ℝ) *
          ∑ m ∈ range M, a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 2) := by
    simp_rw [hterm, ← mul_sum]
  have hsucc :
      ∑ m ∈ range (M + 1), a (n + k * m + r) / (B : ℝ) ^ (m + 1)
        = a (n + r) / B +
          ∑ m ∈ range M, a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 2) := by
    rw [sum_range_succ']
    have h0 : a (n + k * 0 + r) / (B : ℝ) ^ (0 + 1) = a (n + r) / B := by
      simp
    rw [h0, add_comm]
  rw [hLHS, hscale, hsucc]
  have hcancel :
      (B : ℝ) * ∑ m ∈ range M, a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 2)
        = (B : ℝ) * (a (n + r) / B +
            ∑ m ∈ range M, a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 2))
          - a (n + r) := by
    have : (B : ℝ) * (a (n + r) / B) = a (n + r) :=
      mul_div_cancel₀ _ hb0
    linarith
  exact hcancel

/-- Equal-window finite recursion with explicit remainder:
`Γ_r^M(n+k) = B Γ_r^M(n) - a_(n+r) + a_(n+k M+r) B^(-M)`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (3.1).
Contract: API
Audit: GREEN -/
theorem periodicPositionTailTrunc_shift_remainder
    (a : ℕ → ℝ) {B k r n M : ℕ} (hB : 2 ≤ B) :
    periodicPositionTailTrunc a B k r (n + k) M
      = (B : ℝ) * periodicPositionTailTrunc a B k r n M - a (n + r)
        + a (n + k * M + r) / (B : ℝ) ^ M := by
  have hmain := periodicPositionTailTrunc_shift a hB (k := k) (r := r) (n := n) (M := M)
  have hlast :
      periodicPositionTailTrunc a B k r n (M + 1)
        = periodicPositionTailTrunc a B k r n M
          + a (n + k * M + r) / (B : ℝ) ^ (M + 1) := by
    unfold periodicPositionTailTrunc
    rw [sum_range_succ]
  rw [hlast] at hmain
  have hb0 := base_ne_zero hB
  have hpow : (B : ℝ) ^ (M + 1) = (B : ℝ) ^ M * B := pow_succ _ _
  have hbpow : (B : ℝ) ^ M ≠ 0 := pow_ne_zero _ hb0
  rw [hmain]
  field_simp [hb0, hbpow, hpow]
  ring

/-- Geometric identity `∑_m B^(-(m+1)) = 1/(B-1)`, so `q ∑ = 1` for `q = B-1`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (3.2).
Contract: API
Audit: GREEN -/
theorem tsum_inv_pow_succ {B : ℕ} (hB : 2 ≤ B) :
    ∑' m : ℕ, (1 : ℝ) / (B : ℝ) ^ (m + 1) = ((B : ℝ) - 1)⁻¹ := by
  have hr0 : 0 ≤ (1 : ℝ) / B := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hr1 := one_div_base_lt_one hB
  have hb0 := base_ne_zero hB
  have hterm : ∀ m, (1 : ℝ) / (B : ℝ) ^ (m + 1) = ((1 : ℝ) / B) ^ (m + 1) := by
    intro m
    rw [div_pow, one_pow]
  simp_rw [hterm, pow_succ']
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hden : (1 : ℝ) - 1 / B = (B - 1) / B := by
    rw [← div_self hb0, sub_div]
  rw [hden, inv_div, ← one_div, div_mul_div_comm, one_mul]
  have : (B : ℝ) / (B * (B - 1)) = (1 : ℝ) / (B - 1) := by
    rw [div_mul_eq_div_div, div_self hb0]
  exact this

private theorem geom_inv_pow_succ_sum {B M : ℕ} (hB : 2 ≤ B) :
    ∑ m ∈ range M, (1 : ℝ) / (B : ℝ) ^ (m + 1)
      = (1 - ((1 : ℝ) / B) ^ M) / ((B : ℝ) - 1) := by
  have hb0 := base_ne_zero hB
  have hr : (1 : ℝ) / B ≠ 1 := ne_of_lt (one_div_base_lt_one hB)
  have hterm : ∀ m ∈ range M,
      (1 : ℝ) / (B : ℝ) ^ (m + 1) = ((1 : ℝ) / B) ^ (m + 1) := by
    intro m _
    rw [div_pow, one_pow]
  rw [sum_congr rfl hterm]
  simp_rw [pow_succ']
  rw [← mul_sum, geom_sum_eq hr]
  have hden : (1 : ℝ) / B - 1 = (1 - (B : ℝ)) / B := by
    rw [div_sub_one hb0]
  rw [hden]
  have hx :
      ((((1 : ℝ) / B) ^ M - 1) / ((1 - (B : ℝ)) / B))
        = (((1 : ℝ) / B) ^ M - 1) * B / (1 - (B : ℝ)) := by
    rw [div_eq_mul_inv, inv_div, mul_div_assoc]
  rw [hx]
  have hassoc :
      ((1 : ℝ) / B) * ((((1 : ℝ) / B) ^ M - 1) * B / (1 - (B : ℝ)))
        = (((1 : ℝ) / B) * ((((1 : ℝ) / B) ^ M - 1) * B)) / (1 - (B : ℝ)) :=
    (mul_div_assoc _ _ _).symm
  rw [hassoc]
  have hsimp :
      ((1 : ℝ) / B) * ((((1 : ℝ) / B) ^ M - 1) * B)
        = ((1 : ℝ) / B) ^ M - 1 := by
    rw [mul_comm (((1 : ℝ) / B) ^ M - 1) B, ← mul_assoc,
      mul_comm ((1 : ℝ) / B) B, mul_one_div_cancel hb0, one_mul]
  rw [hsimp]
  have hneg : (1 - (B : ℝ)) = - ((B : ℝ) - 1) := by ring
  have hneg' : ((1 : ℝ) / B) ^ M - 1 = - (1 - ((1 : ℝ) / B) ^ M) := by ring
  rw [hneg, hneg', neg_div_neg_eq]

/-- Finite root centering: `q Γ_r^M(n) = a_n (1 - B^(-M)) + q ∑ x_(km+r) B^(-(m+1))`.
Used for `n ≥ 1`; no `a_0` appears.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (3.2).
Contract: API
Audit: GREEN -/
theorem periodicPositionTailTrunc_center
    (a : ℕ → ℝ) {B k r n M : ℕ} (hB : 2 ≤ B) :
    ((B : ℝ) - 1) * periodicPositionTailTrunc a B k r n M
      = a n * (1 - ((1 : ℝ) / B) ^ M)
        + ((B : ℝ) - 1) *
          ∑ m ∈ range M,
            (a (n + k * m + r) - a n) / (B : ℝ) ^ (m + 1) := by
  have hgeom := geom_inv_pow_succ_sum (B := B) (M := M) hB
  unfold periodicPositionTailTrunc
  have hsplit :
      ∑ m ∈ range M, a (n + k * m + r) / (B : ℝ) ^ (m + 1)
        = ∑ m ∈ range M, a n / (B : ℝ) ^ (m + 1)
          + ∑ m ∈ range M,
            (a (n + k * m + r) - a n) / (B : ℝ) ^ (m + 1) := by
    have hterm : ∀ m ∈ range M,
        a (n + k * m + r) / (B : ℝ) ^ (m + 1)
          = a n / (B : ℝ) ^ (m + 1)
            + (a (n + k * m + r) - a n) / (B : ℝ) ^ (m + 1) := by
      intro m _
      ring
    rw [sum_congr rfl hterm, sum_add_distrib]
  rw [hsplit, mul_add]
  have hconst :
      ∑ m ∈ range M, a n / (B : ℝ) ^ (m + 1)
        = a n * ∑ m ∈ range M, (1 : ℝ) / (B : ℝ) ^ (m + 1) := by
    have hpt : ∀ m ∈ range M,
        a n / (B : ℝ) ^ (m + 1) = a n * ((1 : ℝ) / (B : ℝ) ^ (m + 1)) :=
      fun m _ => (mul_one_div (a n) _).symm
    rw [sum_congr rfl hpt, ← mul_sum]
  rw [hconst, hgeom]
  have hne := base_sub_one_ne_zero hB
  have hcancel :
      ((B : ℝ) - 1) * (a n * ((1 - ((1 : ℝ) / B) ^ M) / ((B : ℝ) - 1)))
        = a n * (1 - ((1 : ℝ) / B) ^ M) := by
    rw [← mul_assoc, mul_comm ((B : ℝ) - 1), mul_assoc, mul_div_cancel₀ _ hne]
  rw [hcancel]

/-- Infinite root centering (3.2): `q Γ_r(n) = a_n + q ∑_m x_(km+r)(n) B^(-(m+1))`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (3.2).
Contract: API
Audit: GREEN -/
theorem periodicPositionTail_center
    (a : ℕ → ℝ) {B k r n : ℕ} (hB : 2 ≤ B)
    (hs : Summable fun m : ℕ => a (n + k * m + r) / (B : ℝ) ^ (m + 1)) :
    ((B : ℝ) - 1) * periodicPositionTail a B k r n
      = a n
        + ((B : ℝ) - 1) *
          ∑' m : ℕ, (a (n + k * m + r) - a n) / (B : ℝ) ^ (m + 1) := by
  have hgeo := tsum_inv_pow_succ hB
  have hgeomSm : Summable fun m : ℕ => (1 : ℝ) / (B : ℝ) ^ (m + 1) := by
    have hterm : (fun m : ℕ => (1 : ℝ) / (B : ℝ) ^ (m + 1))
        = fun m => ((1 : ℝ) / B) ^ (m + 1) := by
      funext m
      rw [div_pow, one_pow]
    rw [hterm]
    simp_rw [pow_succ']
    exact (summable_geometric_of_lt_one
      (div_nonneg zero_le_one (Nat.cast_nonneg _)) (one_div_base_lt_one hB)).mul_left _
  have hconst : Summable fun m : ℕ => a n / (B : ℝ) ^ (m + 1) := by
    have hterm : (fun m : ℕ => a n / (B : ℝ) ^ (m + 1))
        = fun m => a n * ((1 : ℝ) / (B : ℝ) ^ (m + 1)) := by
      funext m
      rw [mul_one_div]
    rw [hterm]
    exact hgeomSm.mul_left (a n)
  have hdiff : Summable fun m : ℕ =>
      (a (n + k * m + r) - a n) / (B : ℝ) ^ (m + 1) := by
    have hterm :
        (fun m : ℕ => (a (n + k * m + r) - a n) / (B : ℝ) ^ (m + 1))
          = (fun m : ℕ => a (n + k * m + r) / (B : ℝ) ^ (m + 1))
            - fun m : ℕ => a n / (B : ℝ) ^ (m + 1) := by
      funext m
      change (a (n + k * m + r) - a n) / (B : ℝ) ^ (m + 1)
        = a (n + k * m + r) / (B : ℝ) ^ (m + 1)
          - a n / (B : ℝ) ^ (m + 1)
      exact sub_div (a (n + k * m + r)) (a n) ((B : ℝ) ^ (m + 1))
    rw [hterm]
    exact hs.sub hconst
  have hsplit :
      periodicPositionTail a B k r n
        = ∑' m : ℕ, a n / (B : ℝ) ^ (m + 1)
          + ∑' m : ℕ, (a (n + k * m + r) - a n) / (B : ℝ) ^ (m + 1) := by
    unfold periodicPositionTail
    have hadd := hconst.hasSum.add hdiff.hasSum
    have hadd' : HasSum (fun m : ℕ => a (n + k * m + r) / (B : ℝ) ^ (m + 1))
        (∑' m : ℕ, a n / (B : ℝ) ^ (m + 1)
          + ∑' m : ℕ, (a (n + k * m + r) - a n) / (B : ℝ) ^ (m + 1)) := by
      convert hadd using 1
      funext m
      have hnum : a n + (a (n + k * m + r) - a n) = a (n + k * m + r) := by
        ring
      have hadd_div' :=
        add_div (a n) (a (n + k * m + r) - a n) ((B : ℝ) ^ (m + 1))
      rw [hnum] at hadd_div'
      exact hadd_div'
    exact hadd'.tsum_eq
  rw [hsplit, mul_add]
  have hconst' :
      ∑' m : ℕ, a n / (B : ℝ) ^ (m + 1)
        = a n * ∑' m : ℕ, (1 : ℝ) / (B : ℝ) ^ (m + 1) := by
    have hterm : (fun m : ℕ => a n / (B : ℝ) ^ (m + 1))
        = fun m => a n * ((1 : ℝ) / (B : ℝ) ^ (m + 1)) := by
      funext m
      rw [mul_one_div]
    rw [hterm, tsum_mul_left]
  rw [hconst', hgeo]
  have hne := base_sub_one_ne_zero hB
  have hcancel :
      ((B : ℝ) - 1) * (a n * ((B : ℝ) - 1)⁻¹) = a n := by
    rw [mul_comm ((B : ℝ) - 1), mul_assoc, inv_mul_cancel₀ hne, mul_one]
  rw [hcancel]

/-- Infinite recursion (3.1).

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (3.1).
Contract: API
Audit: GREEN -/
theorem periodicPositionTail_shift
    (a : ℕ → ℝ) {B k r n : ℕ} (hB : 2 ≤ B)
    (hs : Summable fun m : ℕ => a (n + k * m + r) / (B : ℝ) ^ (m + 1)) :
    periodicPositionTail a B k r (n + k)
      = (B : ℝ) * periodicPositionTail a B k r n - a (n + r) := by
  have hb0 := base_ne_zero hB
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hhead :
      ∑ i ∈ range 1, a (n + k * i + r) / (B : ℝ) ^ (i + 1)
        = a (n + r) / B := by
    simp [range_one, sum_singleton, pow_one]
  have htail :
      ∑' m : ℕ, a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 1 + 1)
        = (1 / (B : ℝ)) * periodicPositionTail a B k r (n + k) := by
    have hterm : ∀ m,
        a (n + k * (m + 1) + r) / (B : ℝ) ^ (m + 1 + 1)
          = (1 / (B : ℝ)) * (a ((n + k) + k * m + r) / (B : ℝ) ^ (m + 1)) := by
      intro m
      have hidx : n + k * (m + 1) + r = (n + k) + k * m + r := by ring
      have hpow : (B : ℝ) ^ (m + 1 + 1) = (B : ℝ) ^ (m + 1) * B := pow_succ _ _
      have hbpow : (B : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ hb0
      rw [hidx, hpow]
      have : a ((n + k) + k * m + r) / ((B : ℝ) ^ (m + 1) * B)
          = (1 / (B : ℝ)) * (a ((n + k) + k * m + r) / (B : ℝ) ^ (m + 1)) := by
        rw [div_mul_eq_div_div, div_eq_mul_one_div, mul_comm]
      rw [this]
    simp_rw [hterm]
    rw [tsum_mul_left]
    rfl
  have hsum :
      a (n + r) / B + (1 / (B : ℝ)) * periodicPositionTail a B k r (n + k)
        = periodicPositionTail a B k r n := by
    unfold periodicPositionTail
    have hsplit' := hsplit
    rw [hhead] at hsplit'
    convert hsplit' using 2
    exact htail.symm
  have hmul :
      a (n + r) + periodicPositionTail a B k r (n + k)
        = (B : ℝ) * periodicPositionTail a B k r n := by
    have := congrArg (fun z => (B : ℝ) * z) hsum
    have hBne : (B : ℝ) ≠ 0 := hb0
    have hrew :
        (B : ℝ) * (a (n + r) / B + (1 / (B : ℝ)) * periodicPositionTail a B k r (n + k))
          = a (n + r) + periodicPositionTail a B k r (n + k) := by
      rw [mul_add, mul_div_cancel₀ _ hBne, ← mul_assoc, mul_one_div_cancel hBne,
        one_mul]
    rw [hrew] at this
    exact this
  linarith

/-! ### Offsets, gaps, and the positive remainder identity -/

/-- Offset `x_j(n) = a_(n+j) - a_n`. In particular `x_0 = 0`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §3.
Contract: API
Audit: GREEN -/
def positionOffset (a : ℕ → ℝ) (n j : ℕ) : ℝ :=
  a (n + j) - a n

/-- Forward gap `g_n = a_(n+1) - a_n`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §6.
Contract: API
Audit: GREEN -/
def positionGap (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a (n + 1) - a n

theorem positionOffset_zero (a : ℕ → ℝ) (n : ℕ) : positionOffset a n 0 = 0 := by
  simp [positionOffset]

theorem positionOffset_succ (a : ℕ → ℝ) (n j : ℕ) :
    positionOffset a n (j + 1)
      = positionOffset a n j + positionGap a (n + j) := by
  simp [positionOffset, positionGap]
  ring

/-- Finite gap tail `T_n^[H] = ∑_{h<H} g_(n+h) b^(-(h+1))`.

Named `offsetGapTailTrunc` (not `gapTailTrunc`) so this module can
share an environment with `TailMass.gapTailTrunc` — needed to import
`PrimeShortS` and `StatisticalPack` together.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §6.
Contract: API
Audit: GREEN -/
noncomputable def offsetGapTailTrunc (a : ℕ → ℝ) (b n H : ℕ) : ℝ :=
  ∑ h ∈ range H, positionGap a (n + h) / (b : ℝ) ^ (h + 1)

/-- Infinite gap tail `T_n`.

Named `offsetGapTail` (not `gapTail`) so this module can share an
environment with `TailMass.gapTail`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §6.
Contract: API
Audit: GREEN -/
noncomputable def offsetGapTail (a : ℕ → ℝ) (b n : ℕ) : ℝ :=
  ∑' h : ℕ, positionGap a (n + h) / (b : ℝ) ^ (h + 1)

/-- Finite offset tail `∑_{h<H} x_(L+1+h)(n) b^(-(L+1+h))`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (6.1).
Contract: API
Audit: GREEN -/
noncomputable def offsetTailTrunc (a : ℕ → ℝ) (b n L H : ℕ) : ℝ :=
  ∑ h ∈ range H,
    positionOffset a n (L + h + 1) / (b : ℝ) ^ (L + h + 1)

/-- Infinite offset tail `∑_{j>L} x_j(n) b^(-j)`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (6.1).
Contract: API
Audit: GREEN -/
noncomputable def offsetTail (a : ℕ → ℝ) (b n L : ℕ) : ℝ :=
  ∑' h : ℕ, positionOffset a n (L + h + 1) / (b : ℝ) ^ (L + h + 1)

/-- Exact finite identity (6.1) with terminal correction:
`∑_{h<H} x_(L+1+h) b^(-(L+1+h))
  = b^(-L)/(b-1) [x_L + b T_(n+L)^[H] - x_(L+H) b^(-H)]`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (6.1).
Contract: API
Audit: GREEN -/
theorem offsetTailTrunc_eq_offsetGapTailTrunc
    (a : ℕ → ℝ) {b n L H : ℕ} (hb : 2 ≤ b) :
    offsetTailTrunc a b n L H
      = ((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1)
          * (positionOffset a n L + (b : ℝ) * offsetGapTailTrunc a b (n + L) H
              - positionOffset a n (L + H) / (b : ℝ) ^ H) := by
  induction H with
  | zero =>
    unfold offsetTailTrunc offsetGapTailTrunc
    simp [positionOffset_zero]
  | succ H ih =>
    have hb0 := base_ne_zero hb
    have hne := base_sub_one_ne_zero hb
    have hbpowL : (b : ℝ) ^ L ≠ 0 := pow_ne_zero L hb0
    have hbpowH : (b : ℝ) ^ H ≠ 0 := pow_ne_zero H hb0
    have hinc :
        offsetTailTrunc a b n L (H + 1)
          = offsetTailTrunc a b n L H
            + positionOffset a n (L + H + 1) / (b : ℝ) ^ (L + H + 1) := by
      unfold offsetTailTrunc
      rw [sum_range_succ]
    have hTinc :
        offsetGapTailTrunc a b (n + L) (H + 1)
          = offsetGapTailTrunc a b (n + L) H
            + positionGap a (n + L + H) / (b : ℝ) ^ (H + 1) := by
      unfold offsetGapTailTrunc
      rw [sum_range_succ]
    have hx : positionOffset a n (L + (H + 1))
        = positionOffset a n (L + H) + positionGap a (n + L + H) := by
      simpa [Nat.add_assoc] using positionOffset_succ a n (L + H)
    set C := ((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1)
    have hpowH1 : (b : ℝ) ^ (H + 1) = (b : ℝ) ^ H * b := pow_succ _ _
    have hpowLH : (b : ℝ) ^ (L + H + 1) = (b : ℝ) ^ L * (b : ℝ) ^ (H + 1) := by
      rw [← pow_add]
      ring_nf
    have hgH :
        (b : ℝ) * (positionGap a (n + L + H) / (b : ℝ) ^ (H + 1))
          = positionGap a (n + L + H) / (b : ℝ) ^ H := by
      rw [hpowH1]
      field_simp [hb0, hbpowH]
    have hgeom :
        (1 : ℝ) / (b : ℝ) ^ H - (1 : ℝ) / (b : ℝ) ^ (H + 1)
          = ((b : ℝ) - 1) / (b : ℝ) ^ (H + 1) := by
      rw [hpowH1]
      field_simp [hb0, hbpowH]
    have hx1 :
        positionOffset a n (L + H + 1)
          = positionOffset a n (L + H) + positionGap a (n + L + H) := by
      simpa [Nat.add_assoc] using hx
    have hdelta :
        (b : ℝ) * (positionGap a (n + L + H) / (b : ℝ) ^ (H + 1))
          - positionOffset a n (L + (H + 1)) / (b : ℝ) ^ (H + 1)
          + positionOffset a n (L + H) / (b : ℝ) ^ H
          = positionOffset a n (L + H + 1) *
              ((1 : ℝ) / (b : ℝ) ^ H - 1 / (b : ℝ) ^ (H + 1)) := by
      rw [hx, hgH, hx1]
      have hA : (b : ℝ) ^ (H + 1) ≠ 0 := pow_ne_zero _ hb0
      have hxH :
          positionOffset a n (L + H) / (b : ℝ) ^ H
            = positionOffset a n (L + H) * ((1 : ℝ) / (b : ℝ) ^ H) := by
        rw [mul_one_div]
      have hxH1 :
          (positionOffset a n (L + H) + positionGap a (n + L + H)) /
              (b : ℝ) ^ (H + 1)
            = (positionOffset a n (L + H) + positionGap a (n + L + H)) *
                ((1 : ℝ) / (b : ℝ) ^ (H + 1)) := by
        rw [mul_one_div]
      have hgH' :
          positionGap a (n + L + H) / (b : ℝ) ^ H
            = positionGap a (n + L + H) * ((1 : ℝ) / (b : ℝ) ^ H) := by
        rw [mul_one_div]
      rw [hxH, hxH1, hgH']
      ring
    have hCmul :
        C * (positionOffset a n (L + H + 1) *
              (((b : ℝ) - 1) / (b : ℝ) ^ (H + 1)))
          = positionOffset a n (L + H + 1) / (b : ℝ) ^ (L + H + 1) := by
      have hfrac :
          C * (((b : ℝ) - 1) / (b : ℝ) ^ (H + 1))
            = ((b : ℝ) ^ L)⁻¹ / (b : ℝ) ^ (H + 1) := by
        have hprod :
            (((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1)) * ((b : ℝ) - 1)
              = ((b : ℝ) ^ L)⁻¹ :=
          div_mul_cancel₀ _ hne
        calc
          C * (((b : ℝ) - 1) / (b : ℝ) ^ (H + 1))
              = (C * ((b : ℝ) - 1)) / (b : ℝ) ^ (H + 1) := by
                rw [mul_div_assoc]
          _ = ((b : ℝ) ^ L)⁻¹ / (b : ℝ) ^ (H + 1) := by
                rw [show C * ((b : ℝ) - 1) = ((b : ℝ) ^ L)⁻¹ from hprod]
      have hpowinv :
          ((b : ℝ) ^ L)⁻¹ / (b : ℝ) ^ (H + 1)
            = (1 : ℝ) / (b : ℝ) ^ (L + H + 1) := by
        rw [hpowLH, inv_div_left]
        simp [div_eq_mul_inv, mul_comm, mul_left_comm]
      calc
        C * (positionOffset a n (L + H + 1) *
              (((b : ℝ) - 1) / (b : ℝ) ^ (H + 1)))
            = positionOffset a n (L + H + 1) *
                (C * (((b : ℝ) - 1) / (b : ℝ) ^ (H + 1))) := by
              ring
        _ = positionOffset a n (L + H + 1) *
              (((b : ℝ) ^ L)⁻¹ / (b : ℝ) ^ (H + 1)) := by
              rw [hfrac]
        _ = positionOffset a n (L + H + 1) / (b : ℝ) ^ (L + H + 1) := by
              rw [hpowinv, mul_one_div]
    rw [hinc, ih]
    have hRHS :
        C * (positionOffset a n L + (b : ℝ) * offsetGapTailTrunc a b (n + L) (H + 1)
              - positionOffset a n (L + (H + 1)) / (b : ℝ) ^ (H + 1))
          = C * (positionOffset a n L + (b : ℝ) * offsetGapTailTrunc a b (n + L) H
              - positionOffset a n (L + H) / (b : ℝ) ^ H)
            + positionOffset a n (L + H + 1) / (b : ℝ) ^ (L + H + 1) := by
      have hsplit :
          positionOffset a n L + (b : ℝ) * offsetGapTailTrunc a b (n + L) (H + 1)
              - positionOffset a n (L + (H + 1)) / (b : ℝ) ^ (H + 1)
            = (positionOffset a n L + (b : ℝ) * offsetGapTailTrunc a b (n + L) H
                - positionOffset a n (L + H) / (b : ℝ) ^ H)
              + ((b : ℝ) * (positionGap a (n + L + H) / (b : ℝ) ^ (H + 1))
                  - positionOffset a n (L + (H + 1)) / (b : ℝ) ^ (H + 1)
                  + positionOffset a n (L + H) / (b : ℝ) ^ H) := by
        rw [hTinc]
        ring
      rw [hsplit, mul_add, hdelta, hgeom, hCmul]
    exact hRHS.symm

/-- Infinite positive offset-tail identity (6.1). The remainder
`x_(L+H) b^(-H)` vanishes as a shifted term of a summable series.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (6.1);
`rounds/round101/03_gpt_periodic_weights_second_read.md` §4.
Contract: API
Audit: GREEN -/
theorem offsetTail_eq_offsetGapTail
    (a : ℕ → ℝ) {b n L : ℕ} (hb : 2 ≤ b)
    (hsT : Summable fun h : ℕ => positionGap a (n + L + h) / (b : ℝ) ^ (h + 1))
    (hsX : Summable fun h : ℕ =>
      positionOffset a n (L + h + 1) / (b : ℝ) ^ (L + h + 1)) :
    offsetTail a b n L
      = ((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1)
          * (positionOffset a n L + (b : ℝ) * offsetGapTail a b (n + L)) := by
  have hb0 := base_ne_zero hb
  have hne := base_sub_one_ne_zero hb
  have hbpowL : (b : ℝ) ^ L ≠ 0 := pow_ne_zero L hb0
  have hT : Tendsto (fun H : ℕ => offsetGapTailTrunc a b (n + L) H) atTop
      (𝓝 (offsetGapTail a b (n + L))) :=
    hsT.hasSum.tendsto_sum_nat
  have hX : Tendsto (fun H : ℕ => offsetTailTrunc a b n L H) atTop
      (𝓝 (offsetTail a b n L)) :=
    hsX.hasSum.tendsto_sum_nat
  have hterm0 :
      Tendsto (fun h : ℕ =>
        positionOffset a n (L + h + 1) / (b : ℝ) ^ (L + h + 1)) atTop (𝓝 0) :=
    hsX.tendsto_atTop_zero
  have hident : ∀ h,
      positionOffset a n (L + (h + 1)) / (b : ℝ) ^ (h + 1)
        = (b : ℝ) ^ L *
          (positionOffset a n (L + h + 1) / (b : ℝ) ^ (L + h + 1)) := by
    intro h
    have hp : (b : ℝ) ^ (L + h + 1) = (b : ℝ) ^ L * (b : ℝ) ^ (h + 1) := by
      rw [← pow_add]
      ring_nf
    have hb1 : (b : ℝ) ^ (h + 1) ≠ 0 := pow_ne_zero _ hb0
    field_simp [hbpowL, hb1, hp]
    ring
  have hshift :
      Tendsto (fun h : ℕ =>
        positionOffset a n (L + (h + 1)) / (b : ℝ) ^ (h + 1)) atTop (𝓝 0) := by
    have hm := tendsto_const_nhds (x := ((b : ℝ) ^ L)).mul hterm0
    have heq :
        (fun h : ℕ =>
          (b : ℝ) ^ L * (positionOffset a n (L + h + 1) / (b : ℝ) ^ (L + h + 1)))
          = fun h : ℕ => positionOffset a n (L + (h + 1)) / (b : ℝ) ^ (h + 1) := by
      funext h
      exact (hident h).symm
    have hm0 : Tendsto
        (fun h : ℕ =>
          (b : ℝ) ^ L * (positionOffset a n (L + h + 1) / (b : ℝ) ^ (L + h + 1)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hm
    rwa [heq] at hm0
  have hrem :
      Tendsto (fun H : ℕ => positionOffset a n (L + H) / (b : ℝ) ^ H) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    have hshift_ev := hshift.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hshift_ev
    refine Filter.eventually_atTop.mpr ⟨N + 1, fun H hH => ?_⟩
    have h1 : 1 ≤ H := le_trans (Nat.succ_le_succ (Nat.zero_le N)) hH
    have hN' : N ≤ H - 1 := by omega
    have hrew : H = H - 1 + 1 := (Nat.sub_add_cancel h1).symm
    have hball := hN (H - 1) hN'
    have hterm :
        positionOffset a n (L + H) / (b : ℝ) ^ H
          = positionOffset a n (L + ((H - 1) + 1)) / (b : ℝ) ^ ((H - 1) + 1) := by
      rw [← hrew]
    change dist (positionOffset a n (L + H) / (b : ℝ) ^ H) 0 < ε
    rw [hterm]
    simpa [Real.dist_eq] using hball
  have hRHS :
      Tendsto (fun H : ℕ =>
        ((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1)
          * (positionOffset a n L + (b : ℝ) * offsetGapTailTrunc a b (n + L) H
              - positionOffset a n (L + H) / (b : ℝ) ^ H))
        atTop
        (𝓝 (((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1)
          * (positionOffset a n L + (b : ℝ) * offsetGapTail a b (n + L)))) := by
    have hconst : Tendsto (fun _ : ℕ => ((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1))
        atTop (𝓝 (((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1))) :=
      tendsto_const_nhds
    have hinner :
        Tendsto (fun H : ℕ =>
          positionOffset a n L + (b : ℝ) * offsetGapTailTrunc a b (n + L) H
            - positionOffset a n (L + H) / (b : ℝ) ^ H)
          atTop
          (𝓝 (positionOffset a n L + (b : ℝ) * offsetGapTail a b (n + L) - 0)) :=
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hT)).sub hrem
    simpa using hconst.mul hinner
  have hfin : ∀ H,
      offsetTailTrunc a b n L H
        = ((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1)
          * (positionOffset a n L + (b : ℝ) * offsetGapTailTrunc a b (n + L) H
              - positionOffset a n (L + H) / (b : ℝ) ^ H) :=
    fun H => offsetTailTrunc_eq_offsetGapTailTrunc a hb
  have hX' :
      Tendsto (fun H : ℕ =>
        ((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1)
          * (positionOffset a n L + (b : ℝ) * offsetGapTailTrunc a b (n + L) H
              - positionOffset a n (L + H) / (b : ℝ) ^ H))
        atTop (𝓝 (offsetTail a b n L)) := by
    have heq :
        (fun H : ℕ => offsetTailTrunc a b n L H)
          = fun H =>
            ((b : ℝ) ^ L)⁻¹ / ((b : ℝ) - 1)
              * (positionOffset a n L + (b : ℝ) * offsetGapTailTrunc a b (n + L) H
                  - positionOffset a n (L + H) / (b : ℝ) ^ H) := by
      funext H
      exact hfin H
    rwa [← heq]
  exact tendsto_nhds_unique hX' hRHS

/-! ### Finite position shape and one-point coefficient -/

/-- Finite centered position shape (4.1):
`Φ_(t,L)(x) = q ∑_{1≤j≤L} t_r B^(-(m+1)) x_j`, `j = k m + r`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (4.1).
Contract: API
Audit: GREEN -/
noncomputable def periodicPositionShape (B k L : ℕ) (t : ℕ → ℤ) (x : ℕ → ℝ) : ℝ :=
  ((B : ℝ) - 1) *
    ∑ j ∈ Icc 1 L,
      (t (periodResidue k j) : ℝ) * x j / (B : ℝ) ^ (periodQuotient k j + 1)

/-- Changing only rank `j` (paper `1 ≤ j ≤ L`) multiplies the displacement
by `c_j = q t_r B^(-(m+1))`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (4.2).
Contract: API
Audit: GREEN -/
theorem periodicPositionShape_insertCoefficient
    {B k L j : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (hj0 : 1 ≤ j) (hjL : j ≤ L)
    (t : ℕ → ℤ) (x : ℕ → ℝ) (u u' : ℝ) :
    periodicPositionShape B k L t (Function.update x j u)
      - periodicPositionShape B k L t (Function.update x j u')
    = ((B : ℝ) - 1) * (t (periodResidue k j) : ℝ) * (u - u')
        / (B : ℝ) ^ (periodQuotient k j + 1) := by
  have hj : j ∈ Icc 1 L := mem_Icc.mpr ⟨hj0, hjL⟩
  unfold periodicPositionShape
  rw [← mul_sub, ← sum_sub_distrib]
  have hterm : ∀ i ∈ Icc 1 L,
      (t (periodResidue k i) : ℝ) * Function.update x j u i
          / (B : ℝ) ^ (periodQuotient k i + 1)
        - (t (periodResidue k i) : ℝ) * Function.update x j u' i
          / (B : ℝ) ^ (periodQuotient k i + 1)
      = if i = j then
          (t (periodResidue k j) : ℝ) * (u - u')
            / (B : ℝ) ^ (periodQuotient k j + 1)
        else 0 := by
    intro i hi
    by_cases hij : i = j
    · subst hij
      simp [Function.update_self]
      ring
    · have hui : Function.update x j u i = x i := Function.update_of_ne hij _ _
      have hui' : Function.update x j u' i = x i := Function.update_of_ne hij _ _
      simp [hij, hui, hui']
  rw [sum_congr rfl hterm, sum_ite_eq', if_pos hj]
  ring

/-- `B^(m+1) = b^(j + (k-r)) ≥ b^j` when `B = b^k`, hence
`B^(-(m+1)) ≤ b^(-j)`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §6.
Contract: API
Audit: GREEN -/
theorem period_base_pow_le
    {b k j : ℕ} (hb : 2 ≤ b) (hk : 0 < k) (hj : 1 ≤ j) :
    (b : ℝ) ^ j ≤ (b : ℝ) ^ (k * (periodQuotient k j + 1)) := by
  have ⟨hsplit, hr0, hrk⟩ := period_div_mod hk hj
  have hidx : k * (periodQuotient k j + 1) = j + (k - periodResidue k j) := by
    have hrle : periodResidue k j ≤ k := hrk
    have : k * periodQuotient k j + k = j + (k - periodResidue k j) := by
      have : k * periodQuotient k j + periodResidue k j = j := hsplit.symm
      have hsub : k - periodResidue k j + periodResidue k j = k :=
        Nat.sub_add_cancel hrle
      omega
    simpa [Nat.mul_add, Nat.mul_one] using this
  have hle : j ≤ k * (periodQuotient k j + 1) := by
    rw [hidx]
    exact Nat.le_add_right _ _
  have hb1 : (1 : ℝ) ≤ b :=
    le_trans (by norm_num : (1 : ℝ) ≤ 2) (Nat.cast_le.mpr hb)
  exact pow_le_pow_right₀ hb1 hle

/-! ### Localised finite test comparison -/

/-- Finite comparison of a full character against a good-span truncated
test. Bad mass is paid in full (`|e|=1`); on the good set the Lipschitz
bound `|e(u)-e(v)| ≤ 2π |u-v|` is used. No global first-offset mean.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (6.4).
Contract: API
Audit: GREEN -/
theorem localizedTest_error {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (good : ι → Prop) [DecidablePred good]
    (φ ψ : ι → ℝ) :
    ‖(∑ i ∈ I, e (φ i)) / (I.card : ℂ)
      - (∑ i ∈ I, (if good i then e (ψ i) else 0)) / (I.card : ℂ)‖
      ≤ ((I.filter (fun i => ¬ good i)).card : ℝ) / I.card
        + (2 * Real.pi) *
          (∑ i ∈ I.filter good, |φ i - ψ i|) / I.card := by
  by_cases hI : I.card = 0
  · simp [hI]
  · have hIpos : (0 : ℝ) < I.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hI)
    have hI0 : (I.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hI
    have hsplit :
        (∑ i ∈ I, e (φ i)) - ∑ i ∈ I, (if good i then e (ψ i) else 0)
          = ∑ i ∈ I.filter good, (e (φ i) - e (ψ i))
            + ∑ i ∈ I.filter (fun i => ¬ good i), e (φ i) := by
      have hG : I.filter good ⊆ I := filter_subset _ _
      have hB : I.filter (fun i => ¬ good i) ⊆ I := filter_subset _ _
      have hunion :
          (I.filter good) ∪ I.filter (fun i => ¬ good i) = I := by
        ext i
        constructor
        · intro hi
          rcases mem_union.mp hi with h | h
          · exact (mem_filter.mp h).1
          · exact (mem_filter.mp h).1
        · intro hi
          by_cases hg : good i
          · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hi, hg⟩))
          · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hi, hg⟩))
      have hdisj :
          Disjoint (I.filter good) (I.filter (fun i => ¬ good i)) := by
        refine disjoint_left.mpr ?_
        intro i hiG hiB
        exact (mem_filter.mp hiB).2 (mem_filter.mp hiG).2
      have hφ :
          ∑ i ∈ I, e (φ i)
            = ∑ i ∈ I.filter good, e (φ i)
              + ∑ i ∈ I.filter (fun i => ¬ good i), e (φ i) := by
        rw [← sum_union hdisj, hunion]
      have hψ :
          ∑ i ∈ I, (if good i then e (ψ i) else 0)
            = ∑ i ∈ I.filter good, e (ψ i) :=
        (sum_filter (p := good) (f := fun i => e (ψ i))).symm
      rw [hφ, hψ]
      calc
        (∑ i ∈ I.filter good, e (φ i)
            + ∑ i ∈ I.filter (fun i => ¬ good i), e (φ i))
            - ∑ i ∈ I.filter good, e (ψ i)
            = ∑ i ∈ I.filter good, e (φ i) - ∑ i ∈ I.filter good, e (ψ i)
              + ∑ i ∈ I.filter (fun i => ¬ good i), e (φ i) := by
          ring
        _ = ∑ i ∈ I.filter good, (e (φ i) - e (ψ i))
              + ∑ i ∈ I.filter (fun i => ¬ good i), e (φ i) := by
          rw [sum_sub_distrib]
    rw [← sub_div, hsplit, add_div]
    have hB :
        ‖(∑ i ∈ I.filter (fun i => ¬ good i), e (φ i)) / (I.card : ℂ)‖
          ≤ ((I.filter (fun i => ¬ good i)).card : ℝ) / I.card := by
      rw [norm_div]
      have hN : ‖(I.card : ℂ)‖ = I.card := by simp
      rw [hN]
      have hsum :
          ‖∑ i ∈ I.filter (fun i => ¬ good i), e (φ i)‖
            ≤ ((I.filter (fun i => ¬ good i)).card : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        have h1 : ∑ i ∈ I.filter (fun i => ¬ good i), ‖e (φ i)‖
            ≤ ∑ i ∈ I.filter (fun i => ¬ good i), (1 : ℝ) :=
          sum_le_sum fun _ _ => (norm_e _).le
        have hcard : (∑ i ∈ I.filter (fun i => ¬ good i), (1 : ℝ))
            = (I.filter (fun i => ¬ good i)).card := by
          simp [sum_const]
        exact h1.trans_eq hcard
      exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
    have hG :
        ‖(∑ i ∈ I.filter good, (e (φ i) - e (ψ i))) / (I.card : ℂ)‖
          ≤ (2 * Real.pi) * (∑ i ∈ I.filter good, |φ i - ψ i|) / I.card := by
      rw [norm_div]
      have hN : ‖(I.card : ℂ)‖ = I.card := by simp
      rw [hN]
      have hsum :
          ‖∑ i ∈ I.filter good, (e (φ i) - e (ψ i))‖
            ≤ 2 * Real.pi * ∑ i ∈ I.filter good, |φ i - ψ i| := by
        refine (norm_sum_le _ _).trans ?_
        have hpt : ∀ i ∈ I.filter good,
            ‖e (φ i) - e (ψ i)‖ ≤ 2 * Real.pi * |φ i - ψ i| :=
          fun i _ => norm_e_sub_e (ψ i) (φ i)
        have := sum_le_sum hpt
        have hfact :
            ∑ i ∈ I.filter good, (2 * Real.pi * |φ i - ψ i|)
              = 2 * Real.pi * ∑ i ∈ I.filter good, |φ i - ψ i| := by
          simp [← mul_sum]
        exact this.trans_eq hfact
      have : (2 * Real.pi * ∑ i ∈ I.filter good, |φ i - ψ i|) / I.card
          = (2 * Real.pi) * (∑ i ∈ I.filter good, |φ i - ψ i|) / I.card := by
        ring
      exact (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans_eq this
    refine (norm_add_le _ _).trans ?_
    exact (add_le_add hG hB).trans_eq (add_comm _ _)

/-- Specialisation of the localised comparison: on the good span the
phase remainder is `≤ K (S + b T)`, tails are nonnegative so the
restricted tail mean is at most the full tail mean, and the bad mass
is paid separately. No global mean of `x_L` is assumed.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (6.3)–(6.4);
`rounds/round101/02_grok_multibase_common_clock_update.md` Fortschreibung.
Contract: API
Audit: GREEN -/
theorem localizedPositionPhase_error {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (good : ι → Prop) [DecidablePred good]
    (φ ψ spanBound tail : ι → ℝ) {K S bPow : ℝ}
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hbPow : 0 < bPow)
    (hspan : ∀ i ∈ I, good i → 0 ≤ spanBound i ∧ spanBound i ≤ S)
    (htail : ∀ i ∈ I, 0 ≤ tail i)
    (hrest : ∀ i ∈ I, good i → |φ i - ψ i| ≤ K * (spanBound i + tail i) / bPow) :
    ‖(∑ i ∈ I, e (φ i)) / (I.card : ℂ)
      - (∑ i ∈ I, (if good i then e (ψ i) else 0)) / (I.card : ℂ)‖
      ≤ ((I.filter (fun i => ¬ good i)).card : ℝ) / I.card
        + (2 * Real.pi) * K * (S + (∑ i ∈ I, tail i) / I.card) / bPow := by
  have hloc := localizedTest_error I good φ ψ
  refine hloc.trans ?_
  by_cases hI : I.card = 0
  · have hIempty : I = ∅ := Finset.card_eq_zero.mp hI
    simp [hIempty]
    have hpi : (0 : ℝ) ≤ 2 * Real.pi :=
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le
    exact div_nonneg (mul_nonneg (mul_nonneg hpi hK) hS) hbPow.le
  · have hIpos : (0 : ℝ) < I.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hI)
    have hpt : ∀ i ∈ I.filter good,
        |φ i - ψ i| ≤ K * (S + tail i) / bPow := by
      intro i hi
      have ⟨hiI, hgood⟩ := mem_filter.mp hi
      have ⟨hspan0, hspanS⟩ := hspan i hiI hgood
      have hresti := hrest i hiI hgood
      have htaili := htail i hiI
      have hsum : spanBound i + tail i ≤ S + tail i := by linarith
      have hmul : K * (spanBound i + tail i) / bPow ≤ K * (S + tail i) / bPow := by
        have := mul_le_mul_of_nonneg_left hsum hK
        exact div_le_div_of_nonneg_right this hbPow.le
      exact hresti.trans hmul
    have hsum :
        ∑ i ∈ I.filter good, |φ i - ψ i|
          ≤ ∑ i ∈ I.filter good, K * (S + tail i) / bPow :=
      sum_le_sum hpt
    have hfact :
        ∑ i ∈ I.filter good, K * (S + tail i) / bPow
          = K / bPow * ∑ i ∈ I.filter good, (S + tail i) := by
      have hterm : ∀ i ∈ I.filter good,
          K * (S + tail i) / bPow = K / bPow * (S + tail i) := by
        intro i _
        field_simp [hbPow.ne']
      rw [sum_congr rfl hterm, ← mul_sum]
    have hGsub : I.filter good ⊆ I := filter_subset _ _
    have hSsum :
        ∑ i ∈ I.filter good, (S + tail i)
          ≤ ∑ i ∈ I, (S + tail i) := by
      refine sum_le_sum_of_subset_of_nonneg hGsub ?_
      intro i hi _
      exact add_nonneg hS (htail i hi)
    have hStail :
        ∑ i ∈ I, (S + tail i) = (I.card : ℝ) * S + ∑ i ∈ I, tail i := by
      simp [sum_add_distrib, sum_const, nsmul_eq_mul, mul_comm]
    have hnn2 : 0 ≤ 2 * Real.pi :=
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le
    have hKdiv : 0 ≤ K / bPow := div_nonneg hK hbPow.le
    have hscale :
        (2 * Real.pi) * (∑ i ∈ I.filter good, |φ i - ψ i|) / I.card
          ≤ (2 * Real.pi) * K * (S + (∑ i ∈ I, tail i) / I.card) / bPow := by
      have hrew :
          (2 * Real.pi) * (K / bPow * ∑ i ∈ I, (S + tail i)) / I.card
            = (2 * Real.pi) * K * (S + (∑ i ∈ I, tail i) / I.card) / bPow := by
        have havg :
            ((I.card : ℝ) * S + ∑ i ∈ I, tail i) / I.card
              = S + (∑ i ∈ I, tail i) / I.card := by
          rw [add_div, mul_div_cancel_left₀ _ hIpos.ne']
        rw [hStail]
        have hL :
            (2 * Real.pi) *
                (K / bPow * ((I.card : ℝ) * S + ∑ i ∈ I, tail i)) / I.card
              = (2 * Real.pi) * K *
                  (((I.card : ℝ) * S + ∑ i ∈ I, tail i) / I.card) / bPow := by
          field_simp [hbPow.ne', hIpos.ne']
        rw [hL, havg]
      have h1 :
          (2 * Real.pi) * (∑ i ∈ I.filter good, |φ i - ψ i|) / I.card
            ≤ (2 * Real.pi) * (K / bPow * ∑ i ∈ I.filter good, (S + tail i))
              / I.card :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hsum.trans_eq hfact) hnn2)
          (Nat.cast_nonneg _)
      have h2 :
          (2 * Real.pi) * (K / bPow * ∑ i ∈ I.filter good, (S + tail i)) / I.card
            ≤ (2 * Real.pi) * (K / bPow * ∑ i ∈ I, (S + tail i)) / I.card :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hSsum hKdiv) hnn2)
          (Nat.cast_nonneg _)
      exact h1.trans (h2.trans_eq hrew)
    exact add_le_add_right hscale _

/-! ### Combined positive rank-class / `q`-lift (R101/01 §8) -/

/-- Integer-frequency Weyl criterion for a sequence of vectors: Cesàro
means of `e(⟨t,θ_n⟩)` vanish for every nonzero integer mode.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §8.
Contract: API
Audit: GREEN -/
def SequenceWeyl {I : Type*} [Fintype I] [DecidableEq I]
    (θ : ℕ → I → ℝ) : Prop :=
  ∀ t : I → ℤ, (∃ i, t i ≠ 0) →
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, e (∑ i : I, (t i : ℝ) * θ n i)) / N)
      atTop (𝓝 0)

/-- Integer shift covariance `θ_(n+s) - B θ_n ∈ ℤ^d`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §8.
Contract: API
Audit: GREEN -/
def IntegerShiftCov {I : Type*} [Fintype I]
    (B s : ℕ) (θ : ℕ → I → ℝ) : Prop :=
  ∀ n i, ∃ z : ℤ, θ (n + s) i - (B : ℝ) * θ n i = (z : ℝ)

/-- Length-`H` geometric clock kernel
`U_H(x) = H⁻¹ ∑_{h<H} e(B^h ⟨t,x⟩)`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (8.1).
Contract: API
Audit: GREEN -/
noncomputable def clockKernel {I : Type*} [Fintype I]
    (B : ℕ) (t : I → ℤ) (H : ℕ) (x : I → ℝ) : ℂ :=
  (∑ h ∈ range H, e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * x i)) / H

/-- Squared kernel `F_H = |U_H|²`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (8.1).
Contract: API
Audit: GREEN -/
noncomputable def clockKernelSq {I : Type*} [Fintype I]
    (B : ℕ) (t : I → ℤ) (H : ℕ) (x : I → ℝ) : ℝ :=
  ‖clockKernel B t H x‖ ^ 2

private theorem sub_one_dvd_pow_sub_one (x : ℤ) (n : ℕ) : x - 1 ∣ x ^ n - 1 := by
  rw [← geom_sum_mul x n]
  exact dvd_mul_left _ _

private theorem sub_one_dvd_pow_sub_pow (x : ℤ) (m n : ℕ) :
    x - 1 ∣ x ^ m - x ^ n := by
  have hm := sub_one_dvd_pow_sub_one x m
  have hn := sub_one_dvd_pow_sub_one x n
  have hsub : (x ^ m - 1) - (x ^ n - 1) = x ^ m - x ^ n := by ring
  rw [← hsub]
  exact dvd_sub hm hn

private theorem int_pow_right_inj {b : ℕ} (hb : 2 ≤ b) {h l : ℕ}
    (heq : (b : ℤ) ^ h = (b : ℤ) ^ l) : h = l := by
  have hb1 : 1 < b := lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hb
  have hnat : b ^ h = b ^ l := by
    have hcast : ((b ^ h : ℕ) : ℤ) = ((b ^ l : ℕ) : ℤ) := by
      rw [Nat.cast_pow, Nat.cast_pow, heq]
    exact Nat.cast_inj.mp hcast
  exact Nat.pow_right_injective hb1 hnat

/-- Off-diagonal integer mode `((B^h-B^l)/q) t`. Requires `q ∣ (B^h-B^l)`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (8.1).
Contract: API
Audit: GREEN -/
private def dividedMode {I : Type*} (B q : ℕ) (t : I → ℤ) (h l : ℕ) (i : I) : ℤ :=
  t i * (((B : ℤ) ^ h - (B : ℤ) ^ l) / q)

private theorem q_dvd_pow_sub_pow {B q h l : ℕ}
    (hqdvd : (q : ℤ) ∣ ((B : ℤ) - 1)) :
    (q : ℤ) ∣ (B : ℤ) ^ h - (B : ℤ) ^ l :=
  dvd_trans hqdvd (sub_one_dvd_pow_sub_pow _ _ _)

private theorem dividedMode_mul {I : Type*} (B q : ℕ) (t : I → ℤ) (h l : ℕ)
    (i : I) (hqdvd : (q : ℤ) ∣ ((B : ℤ) - 1)) :
    (dividedMode B q t h l i : ℝ) * (q : ℝ) =
      (t i : ℝ) * ((B : ℝ) ^ h - (B : ℝ) ^ l) := by
  unfold dividedMode
  have hx := q_dvd_pow_sub_pow (B := B) (q := q) (h := h) (l := l) hqdvd
  have hR :
      ((((B : ℤ) ^ h - (B : ℤ) ^ l) / q : ℤ) : ℝ) * (q : ℝ) =
        (B : ℝ) ^ h - (B : ℝ) ^ l := by
    have hqR : (q : ℝ) = ((q : ℤ) : ℝ) := by simp
    rw [hqR, ← Int.cast_mul, Int.ediv_mul_cancel hx]
    simp [Int.cast_pow]
  push_cast
  rw [mul_assoc, hR]

private theorem dividedMode_exists_ne_zero {I : Type*}
    {B q : ℕ} {t : I → ℤ} {h l : ℕ}
    (hB : 2 ≤ B) (hq : 0 < q) (hqdvd : (q : ℤ) ∣ ((B : ℤ) - 1))
    (ht : ∃ i, t i ≠ 0) (hhl : h ≠ l) :
    ∃ i, dividedMode B q t h l i ≠ 0 := by
  obtain ⟨i, hi⟩ := ht
  refine ⟨i, ?_⟩
  unfold dividedMode
  refine mul_ne_zero hi ?_
  intro hz
  have hmul := Int.ediv_mul_cancel
    (q_dvd_pow_sub_pow (B := B) (q := q) (h := h) (l := l) hqdvd)
  rw [hz, zero_mul] at hmul
  exact hhl (int_pow_right_inj hB (sub_eq_zero.mp hmul.symm))

private theorem integerShiftCov_phase {I : Type*} [Fintype I]
    {B s : ℕ} {θ : ℕ → I → ℝ} {t : I → ℤ}
    (hcov : IntegerShiftCov B s θ) (n : ℕ) :
    e (∑ i : I, (t i : ℝ) * θ (n + s) i)
      = e (∑ i : I, (t i : ℝ) * (B : ℝ) * θ n i) := by
  classical
  let z : I → ℤ := fun i => Classical.choose (hcov n i)
  have hz : ∀ i, θ (n + s) i - (B : ℝ) * θ n i = (z i : ℝ) :=
    fun i => Classical.choose_spec (hcov n i)
  have hsplit :
      ∑ i : I, (t i : ℝ) * θ (n + s) i
        = ∑ i : I, (t i : ℝ) * (B : ℝ) * θ n i
          + ∑ i : I, (t i : ℝ) * (z i : ℝ) := by
    have hterm : ∀ i : I,
        (t i : ℝ) * θ (n + s) i
          = (t i : ℝ) * (B : ℝ) * θ n i + (t i : ℝ) * (z i : ℝ) := by
      intro i
      have hzi : θ (n + s) i = (B : ℝ) * θ n i + (z i : ℝ) := by
        linarith [hz i]
      rw [hzi]
      ring
    rw [sum_congr rfl fun i _ => hterm i, sum_add_distrib]
  have hint :
      ∑ i : I, (t i : ℝ) * (z i : ℝ)
        = ((∑ i : I, t i * z i : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    refine sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [hsplit, e_add, hint, e_int, mul_one]

private theorem integerShiftCov_iterate_int {I : Type*} [Fintype I]
    {B s : ℕ} {θ : ℕ → I → ℝ} {t : I → ℤ}
    (hcov : IntegerShiftCov B s θ) (n h : ℕ) :
    ∃ z : ℤ,
      ∑ i : I, (t i : ℝ) * θ (n + s * h) i
        - ∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * θ n i = (z : ℝ) := by
  induction h generalizing n with
  | zero =>
    refine ⟨0, ?_⟩
    simp
  | succ h ih =>
    classical
    obtain ⟨w, hw⟩ := ih n
    let z : I → ℤ := fun i => Classical.choose (hcov (n + s * h) i)
    have hz : ∀ i,
        θ (n + s * h + s) i - (B : ℝ) * θ (n + s * h) i = (z i : ℝ) :=
      fun i => Classical.choose_spec (hcov (n + s * h) i)
    have hidx : n + s * (h + 1) = n + s * h + s := by ring
    refine ⟨∑ i : I, t i * z i + (B : ℤ) * w, ?_⟩
    have hterm :
        ∑ i : I, (t i : ℝ) * θ (n + s * (h + 1)) i
          = (B : ℝ) * ∑ i : I, (t i : ℝ) * θ (n + s * h) i
            + ∑ i : I, (t i : ℝ) * (z i : ℝ) := by
      rw [hidx]
      have hpt : ∀ i : I,
          (t i : ℝ) * θ (n + s * h + s) i
            = (t i : ℝ) * (B : ℝ) * θ (n + s * h) i
              + (t i : ℝ) * (z i : ℝ) := by
        intro i
        have hzi : θ (n + s * h + s) i
            = (B : ℝ) * θ (n + s * h) i + (z i : ℝ) := by
          linarith [hz i]
        rw [hzi]
        ring
      rw [sum_congr rfl fun i _ => hpt i, sum_add_distrib, mul_sum]
      refine congrArg₂ _ (sum_congr rfl fun i _ => by ring) rfl
    have hint :
        ∑ i : I, (t i : ℝ) * (z i : ℝ)
          = ((∑ i : I, t i * z i : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      push_cast
      ring
    have hpow :
        ∑ i : I, (t i : ℝ) * (B : ℝ) ^ (h + 1) * θ n i
          = (B : ℝ) * ∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * θ n i := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [pow_succ]
      ring
    have hw' :
        ∑ i : I, (t i : ℝ) * θ (n + s * h) i
          = ∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * θ n i + (w : ℝ) := by
      linarith [hw]
    rw [hterm, hpow, hint, hw']
    push_cast
    ring

private theorem integerShiftCov_iterate {I : Type*} [Fintype I]
    {B s : ℕ} {θ : ℕ → I → ℝ} {t : I → ℤ}
    (hcov : IntegerShiftCov B s θ) (n h : ℕ) :
    e (∑ i : I, (t i : ℝ) * θ (n + s * h) i)
      = e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * θ n i) := by
  obtain ⟨z, hz⟩ := integerShiftCov_iterate_int (t := t) hcov n h
  have hsum :
      ∑ i : I, (t i : ℝ) * θ (n + s * h) i
        = ∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * θ n i + (z : ℝ) := by
    linarith
  rw [hsum, e_add, e_int, mul_one]

/-- Recursion (3.1) supplies integer shift-`k` covariance when coefficients
are integer-valued.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (3.1), §8.
Contract: API
Audit: GREEN -/
theorem periodicPositionTail_integerShiftCov
    (a : ℕ → ℝ) {B k : ℕ} {I : Type*} [Fintype I]
    (r : I → ℕ) (hB : 2 ≤ B)
    (ha : ∀ n, ∃ z : ℤ, a n = (z : ℝ))
    (hsm : ∀ n i, Summable fun m : ℕ =>
      a (n + k * m + r i) / (B : ℝ) ^ (m + 1)) :
    IntegerShiftCov B k (fun n i => periodicPositionTail a B k (r i) n) := by
  intro n i
  have hshift := periodicPositionTail_shift a hB (hsm n i)
  obtain ⟨z, hz⟩ := ha (n + r i)
  refine ⟨-z, ?_⟩
  dsimp
  rw [hshift, hz, Int.cast_neg]
  ring

private theorem sum_range_natCast (K : ℕ) :
    ∑ h ∈ range K, (h : ℝ) = (K : ℝ) * ((K : ℝ) - 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    simp only [Nat.cast_succ]
    ring

private theorem cesaro_shift_sub_of_pos (a : ℕ → ℂ) (j : ℕ) {N : ℕ}
    (hN : 0 < N) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ‖(∑ n ∈ range N, a (n + j)) / N - (∑ n ∈ range N, a n) / N‖
      ≤ (2 * j : ℝ) / N := by
  have hswap : ∑ n ∈ range N, a (n + j) = ∑ n ∈ range N, a (j + n) :=
    sum_congr rfl fun n _ => by rw [add_comm]
  have h1 := sum_range_add a j N
  have h2 := sum_range_add a N j
  have hdiff :
      ∑ n ∈ range N, a (j + n) - ∑ n ∈ range N, a n =
        ∑ n ∈ range j, a (N + n) - ∑ n ∈ range j, a n := by
    have hNj : N + j = j + N := Nat.add_comm _ _
    have hlong1 : ∑ n ∈ range (N + j), a n =
        ∑ n ∈ range j, a n + ∑ n ∈ range N, a (j + n) := by
      simpa [hNj] using h1
    have hlong2 : ∑ n ∈ range (N + j), a n =
        ∑ n ∈ range N, a n + ∑ n ∈ range j, a (N + n) := h2
    have hleft :
        ∑ n ∈ range N, a (j + n) =
          ∑ n ∈ range (N + j), a n - ∑ n ∈ range j, a n := by
      rw [hlong1]
      abel
    have hright :
        ∑ n ∈ range N, a n =
          ∑ n ∈ range (N + j), a n - ∑ n ∈ range j, a (N + n) := by
      rw [hlong2]
      abel
    rw [hleft, hright]
    abel
  have hbd :
      ‖∑ n ∈ range N, a (j + n) - ∑ n ∈ range N, a n‖ ≤ (2 * j : ℝ) := by
    rw [hdiff]
    have hA : ‖∑ n ∈ range j, a (N + n)‖ ≤ j := by
      have := norm_sum_le (range j) fun n => a (N + n)
      have h1' : ∑ n ∈ range j, ‖a (N + n)‖ ≤ ∑ n ∈ range j, (1 : ℝ) :=
        sum_le_sum fun n _ => ha _
      have hcard : (∑ n ∈ range j, (1 : ℝ)) = j := by simp [sum_const]
      exact this.trans (h1'.trans_eq hcard)
    have hB : ‖∑ n ∈ range j, a n‖ ≤ j := by
      have := norm_sum_le (range j) a
      have h1' : ∑ n ∈ range j, ‖a n‖ ≤ ∑ n ∈ range j, (1 : ℝ) :=
        sum_le_sum fun n _ => ha _
      have hcard : (∑ n ∈ range j, (1 : ℝ)) = j := by simp [sum_const]
      exact this.trans (h1'.trans_eq hcard)
    have hsub :=
      (norm_sub_le (∑ n ∈ range j, a (N + n)) (∑ n ∈ range j, a n)).trans
        (add_le_add hA hB)
    have h2j : (j : ℝ) + j = 2 * j := by ring
    exact hsub.trans_eq h2j
  rw [hswap, ← sub_div, norm_div]
  have hNnorm : ‖(N : ℂ)‖ = N := by simp
  rw [hNnorm]
  exact div_le_div_of_nonneg_right hbd (Nat.cast_nonneg N)

private theorem abs_cesaro_sub_blockAvg (a : ℕ → ℂ) {N K : ℕ}
    (hN : 0 < N) (hK : 0 < K) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ‖(∑ n ∈ range N, a n) / N
        - (∑ n ∈ range N, (∑ h ∈ range K, a (n + h)) / K) / N‖
      ≤ ((K : ℝ) - 1) / N := by
  have hK0 : (K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hK)
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hswap :
      (∑ n ∈ range N, (∑ h ∈ range K, a (n + h)) / K) / N
        = (∑ h ∈ range K, (∑ n ∈ range N, a (n + h)) / N) / K := by
    have h1 :
        ∑ n ∈ range N, (∑ h ∈ range K, a (n + h)) / K =
          (∑ n ∈ range N, ∑ h ∈ range K, a (n + h)) / K := by
      simp_rw [div_eq_mul_inv, ← sum_mul]
    rw [h1, sum_comm]
    have h2 :
        (∑ h ∈ range K, ∑ n ∈ range N, a (n + h)) / K / N =
          (∑ h ∈ range K, ∑ n ∈ range N, a (n + h)) / N / K := by
      field_simp [hK0, Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)]
    rw [h2]
    have h3 :
        (∑ h ∈ range K, ∑ n ∈ range N, a (n + h)) / N =
          ∑ h ∈ range K, (∑ n ∈ range N, a (n + h)) / N := by
      simp_rw [div_eq_mul_inv, sum_mul]
    rw [h3]
  rw [hswap]
  have havg :
      (∑ n ∈ range N, a n) / N -
          (∑ h ∈ range K, (∑ n ∈ range N, a (n + h)) / N) / K =
        (∑ h ∈ range K,
            ((∑ n ∈ range N, a n) / N -
              (∑ n ∈ range N, a (n + h)) / N)) / K := by
    set c := (∑ n ∈ range N, a n) / N
    set u := fun h : ℕ => (∑ n ∈ range N, a (n + h)) / N
    have hsumc : ∑ h ∈ range K, c = (K : ℂ) * c := by
      simp [c, sum_const, nsmul_eq_mul]
    have hKc : (K : ℂ) * c / K = c := by
      field_simp [hK0]
    calc
      c - (∑ h ∈ range K, u h) / K
          = (K : ℂ) * c / K - (∑ h ∈ range K, u h) / K := by
            congr 1
            exact hKc.symm
      _ = ((K : ℂ) * c - ∑ h ∈ range K, u h) / K := by rw [sub_div]
      _ = (∑ h ∈ range K, c - ∑ h ∈ range K, u h) / K := by rw [hsumc]
      _ = (∑ h ∈ range K, (c - u h)) / K := by rw [sum_sub_distrib]
  rw [havg, norm_div]
  have hKnorm : ‖(K : ℂ)‖ = K := by simp
  rw [hKnorm]
  have hpt : ∀ h ∈ range K,
      ‖(∑ n ∈ range N, a n) / N - (∑ n ∈ range N, a (n + h)) / N‖ ≤
        (2 * (h : ℝ)) / N := by
    intro h _
    simpa [norm_sub_rev] using cesaro_shift_sub_of_pos a h hN ha
  have hsumle :
      ‖∑ h ∈ range K,
          ((∑ n ∈ range N, a n) / N -
            (∑ n ∈ range N, a (n + h)) / N)‖ ≤
        ∑ h ∈ range K, (2 * (h : ℝ)) / N :=
    (norm_sum_le _ _).trans (sum_le_sum hpt)
  have hsumh :
      ∑ h ∈ range K, (2 * (h : ℝ)) / N =
        (K : ℝ) * ((K : ℝ) - 1) / N := by
    have hN0 : (N : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
    have hfact : ∀ h ∈ range K, (2 * (h : ℝ)) / N = (2 / (N : ℝ)) * h := by
      intro h _; ring
    rw [sum_congr rfl hfact, ← mul_sum, sum_range_natCast]
    field_simp [hN0]
  have hdiv :
      (∑ h ∈ range K, (2 * (h : ℝ)) / N) / K = ((K : ℝ) - 1) / N := by
    rw [hsumh]
    field_simp [hKpos.ne']
  exact (div_le_div_of_nonneg_right hsumle (Nat.cast_nonneg K)).trans_eq hdiv

private theorem abs_blockAvg_sq_le (z : ℕ → ℂ) {N : ℕ} (hN : 0 < N) :
    ‖(∑ n ∈ range N, z n) / N‖ ^ 2 ≤
      (∑ n ∈ range N, ‖z n‖ ^ 2) / N := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hz : ‖∑ n ∈ range N, z n‖ ≤ ∑ n ∈ range N, ‖z n‖ :=
    norm_sum_le _ _
  have hcs : (∑ n ∈ range N, ‖z n‖) ^ 2 ≤
      (range N).card * ∑ n ∈ range N, ‖z n‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcard : ((range N).card : ℝ) = N := by simp
  have hsq : ‖∑ n ∈ range N, z n‖ ^ 2 ≤
      (N : ℝ) * ∑ n ∈ range N, ‖z n‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hz 2
    refine this.trans ?_
    simpa [hcard] using hcs
  rw [norm_div]
  have hNnorm : ‖(N : ℂ)‖ = N := by simp
  rw [hNnorm, div_pow]
  have hden : (N : ℝ) ^ 2 = N * N := by ring
  rw [hden]
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  field_simp [hNne]
  exact hsq

/-- Finite (8.3): class Cesàro versus stride-`s` window energy.
Shift edge `(H-1)/M`, Cauchy–Schwarz, and nonnegative class restriction
costing `s`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (8.3);
`rounds/round101/03_gpt_periodic_weights_second_read.md` §5.
Contract: API
Audit: GREEN -/
theorem positiveProgressionShiftBound
    (a : ℕ → ℂ) {s M H r : ℕ}
    (hs : 0 < s) (hM : 0 < M) (hH : 0 < H) (hr : r < s)
    (ha : ∀ n, ‖a n‖ ≤ 1) :
    ‖(∑ m ∈ range M, a (r + s * m)) / M‖
      ≤ ((H : ℝ) - 1) / M
        + Real.sqrt (s *
            (∑ n ∈ range (s * M),
              ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2) / (s * M)) := by
  let b : ℕ → ℂ := fun m => a (r + s * m)
  have hb : ∀ m, ‖b m‖ ≤ 1 := fun m => ha _
  have hshift :
      ‖(∑ m ∈ range M, b m) / M
          - (∑ m ∈ range M, (∑ h ∈ range H, b (m + h)) / H) / M‖
        ≤ ((H : ℝ) - 1) / M :=
    abs_cesaro_sub_blockAvg b hM hH hb
  have hclass :
      (∑ m ∈ range M, b m) / M = (∑ m ∈ range M, a (r + s * m)) / M := rfl
  have hsmooth :
      (∑ m ∈ range M, (∑ h ∈ range H, b (m + h)) / H) / M
        = (∑ m ∈ range M, (∑ h ∈ range H, a (r + s * (m + h))) / H) / M := by
    rfl
  have hidx : ∀ m h, r + s * (m + h) = (r + s * m) + s * h := by
    intro m h
    ring
  have hsmooth' :
      (∑ m ∈ range M, (∑ h ∈ range H, a (r + s * (m + h))) / H)
        = ∑ m ∈ range M, (∑ h ∈ range H, a ((r + s * m) + s * h)) / H :=
    sum_congr rfl fun m _ => by
      congr 1
      exact sum_congr rfl fun h _ => by rw [hidx m h]
  have hz : ∀ m,
      (∑ h ∈ range H, a ((r + s * m) + s * h)) / H
        = (∑ h ∈ range H, a ((r + s * m) + s * h)) / H :=
    fun _ => rfl
  have hCS :
      ‖(∑ m ∈ range M,
            (∑ h ∈ range H, a ((r + s * m) + s * h)) / H) / M‖ ^ 2
        ≤ (∑ m ∈ range M,
            ‖(∑ h ∈ range H, a ((r + s * m) + s * h)) / H‖ ^ 2) / M :=
    abs_blockAvg_sq_le (fun m =>
      (∑ h ∈ range H, a ((r + s * m) + s * h)) / H) hM
  have hF : ∀ n, 0 ≤ ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2 :=
    fun n => sq_nonneg _
  have himg : (range M).image (fun m => r + s * m) ⊆ range (s * M) := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    have hmM := mem_range.mp hm
    have hlt : r + s * m < s * M :=
      calc
        r + s * m < s + s * m := Nat.add_lt_add_right hr _
        _ = s * (m + 1) := by rw [Nat.mul_succ, Nat.add_comm]
        _ ≤ s * M := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hmM)
    exact mem_range.mpr hlt
  have hinj : Set.InjOn (fun m => r + s * m) (range M) := by
    intro x _ y _ heq
    have hx : r + s * x = r + s * y := heq
    have : s * x = s * y := Nat.add_left_cancel hx
    exact Nat.eq_of_mul_eq_mul_left hs this
  have hsum_img :
      ∑ n ∈ (range M).image (fun m => r + s * m),
          ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2
        = ∑ m ∈ range M, ‖(∑ h ∈ range H, a ((r + s * m) + s * h)) / H‖ ^ 2 :=
    sum_image hinj
  have hrestrict :
      ∑ m ∈ range M, ‖(∑ h ∈ range H, a ((r + s * m) + s * h)) / H‖ ^ 2
        ≤ ∑ n ∈ range (s * M), ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2 := by
    rw [← hsum_img]
    exact sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => hF _
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hspos : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hclassE :
      (∑ m ∈ range M,
          ‖(∑ h ∈ range H, a ((r + s * m) + s * h)) / H‖ ^ 2) / M
        ≤ s * (∑ n ∈ range (s * M),
            ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2) / (s * M) := by
    have hfull :
        s * (∑ n ∈ range (s * M),
            ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2) / (s * M)
          = (∑ n ∈ range (s * M),
              ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2) / M := by
      have hsM : (s * M : ℝ) = s * M := by push_cast; ring
      have hsM0 : (s * M : ℝ) ≠ 0 :=
        mul_ne_zero hspos.ne' hMpos.ne'
      field_simp [hspos.ne', hMpos.ne', hsM0]
    have : (∑ m ∈ range M,
          ‖(∑ h ∈ range H, a ((r + s * m) + s * h)) / H‖ ^ 2) / M
        ≤ (∑ n ∈ range (s * M),
            ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2) / M :=
      div_le_div_of_nonneg_right hrestrict (Nat.cast_nonneg _)
    exact this.trans_eq hfull.symm
  have hnnE : 0 ≤
      s * (∑ n ∈ range (s * M),
        ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2) / (s * M) := by
    have hsum : 0 ≤ ∑ n ∈ range (s * M),
        ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2 :=
      sum_nonneg fun _ _ => hF _
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg s) hsum)
      (mul_nonneg (Nat.cast_nonneg s) (Nat.cast_nonneg M))
  have hsqrt :
      ‖(∑ m ∈ range M,
            (∑ h ∈ range H, a ((r + s * m) + s * h)) / H) / M‖
        ≤ Real.sqrt (s *
            (∑ n ∈ range (s * M),
              ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2) / (s * M)) := by
    have hsq := hCS.trans hclassE
    have hnnL : 0 ≤
        ‖(∑ m ∈ range M,
            (∑ h ∈ range H, a ((r + s * m) + s * h)) / H) / M‖ :=
      norm_nonneg _
    exact (Real.le_sqrt_of_sq_le hsq)
  have hdecomp :
      (∑ m ∈ range M, a (r + s * m)) / M
        = ((∑ m ∈ range M, b m) / M
            - (∑ m ∈ range M, (∑ h ∈ range H, b (m + h)) / H) / M)
          + (∑ m ∈ range M, (∑ h ∈ range H, b (m + h)) / H) / M := by
    abel
  have hnorm := norm_add_le
    ((∑ m ∈ range M, b m) / M
      - (∑ m ∈ range M, (∑ h ∈ range H, b (m + h)) / H) / M)
    ((∑ m ∈ range M, (∑ h ∈ range H, b (m + h)) / H) / M)
  have hsmooth_idx :
      (∑ m ∈ range M, (∑ h ∈ range H, b (m + h)) / H) / M
        = (∑ m ∈ range M,
            (∑ h ∈ range H, a ((r + s * m) + s * h)) / H) / M := by
    rw [hsmooth, hsmooth']
  rw [hclass, hdecomp]
  refine hnorm.trans (add_le_add hshift ?_)
  rw [hsmooth_idx]
  exact hsqrt

private theorem ofReal_norm_sq (w : ℂ) :
    ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  rfl

private theorem clockKernel_mul_star {I : Type*} [Fintype I]
    (B : ℕ) (t : I → ℤ) {H : ℕ} (hH : 0 < H) (x : I → ℝ) :
    clockKernel B t H x * star (clockKernel B t H x) =
      ((1 : ℂ) / (H : ℂ) ^ 2) *
        ∑ h ∈ range H, ∑ l ∈ range H,
          e (∑ i : I, (t i : ℝ) * ((B : ℝ) ^ h - (B : ℝ) ^ l) * x i) := by
  have hH0 : (H : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hH)
  unfold clockKernel
  have hstarH : star (H : ℂ) = (H : ℂ) := by simp
  rw [star_div₀, hstarH, div_mul_div_comm]
  have hden : (H : ℂ) * H = (H : ℂ) ^ 2 := by ring
  rw [hden]
  have hst :
      star (∑ h ∈ range H, e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * x i)) =
        ∑ h ∈ range H, star (e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * x i)) :=
    map_sum (starAddEquiv : ℂ ≃+ ℂ)
      (fun h : ℕ => e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * x i)) (range H)
  rw [hst]
  have hterm : ∀ h l : ℕ,
      e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * x i) *
          star (e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ l * x i)) =
        e (∑ i : I, (t i : ℝ) * ((B : ℝ) ^ h - (B : ℝ) ^ l) * x i) := by
    intro h l
    rw [star_e, ← e_add]
    congr 1
    rw [← sub_eq_add_neg, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [sum_mul_sum]
  simp_rw [hterm]
  rw [div_eq_inv_mul, one_div]

private theorem dividedMode_phase {I : Type*} [Fintype I]
    (B q : ℕ) (t : I → ℤ) (h l : ℕ) (x : I → ℝ)
    (hqdvd : (q : ℤ) ∣ ((B : ℤ) - 1)) :
    ∑ i : I, (t i : ℝ) * ((B : ℝ) ^ h - (B : ℝ) ^ l) * x i
      = ∑ i : I, (dividedMode B q t h l i : ℝ) * (q : ℝ) * x i := by
  refine sum_congr rfl fun i _ => ?_
  rw [← dividedMode_mul B q t h l i hqdvd]

private theorem tendsto_finset_sum_nhds {ι : Type*} (s : Finset ι)
    (f : ι → ℕ → ℂ) (a : ι → ℂ)
    (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (a i))) :
    Tendsto (fun N => ∑ i ∈ s, f i N) atTop (𝓝 (∑ i ∈ s, a i)) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using tendsto_const_nhds (x := (0 : ℂ))
  · intro i t hit ih hf
    have hi : Tendsto (f i) atTop (𝓝 (a i)) := hf i (mem_insert_self i t)
    have ht : ∀ j ∈ t, Tendsto (f j) atTop (𝓝 (a j)) :=
      fun j hj => hf j (mem_insert_of_mem hj)
    simp_rw [sum_insert hit]
    exact hi.add (ih ht)

private theorem tendsto_one_div_nat :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (1 : ℂ)) / N) atTop (𝓝 1) := by
  have heq :
      (fun N : ℕ => (∑ n ∈ range N, (1 : ℂ)) / N) =ᶠ[atTop]
        fun _ => (1 : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
    simp [sum_const, nsmul_eq_mul, hN0]
  exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

private theorem tendsto_clock_pair {I : Type*} [Fintype I] [DecidableEq I]
    {B q : ℕ} {θ : ℕ → I → ℝ} {t : I → ℤ}
    (hB : 2 ≤ B) (hq : 0 < q) (hqdvd : (q : ℤ) ∣ ((B : ℤ) - 1))
    (hW : SequenceWeyl (fun n i => (q : ℝ) * θ n i))
    (ht : ∃ i, t i ≠ 0) (h l : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
        e (∑ i : I, (t i : ℝ) * ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i)) / N)
      atTop (𝓝 (if h = l then 1 else 0)) := by
  by_cases hhl : h = l
  · subst hhl
    have hterm : ∀ n,
        e (∑ i : I, (t i : ℝ) * ((B : ℝ) ^ h - (B : ℝ) ^ h) * θ n i) = 1 := by
      intro n
      simp [sub_self, e_zero]
    have hfun :
        (fun N : ℕ =>
          (∑ n ∈ range N,
            e (∑ i : I, (t i : ℝ) * ((B : ℝ) ^ h - (B : ℝ) ^ h) * θ n i)) / N)
          = fun N => (∑ n ∈ range N, (1 : ℂ)) / N := by
      funext N
      congr 1
      exact sum_congr rfl fun n _ => hterm n
    rw [hfun]
    simpa using tendsto_one_div_nat
  · have hs := dividedMode_exists_ne_zero hB hq hqdvd ht hhl
    have hmode := hW (dividedMode B q t h l) hs
    have hrew : ∀ n,
        e (∑ i : I, (t i : ℝ) * ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i)
          = e (∑ i : I, (dividedMode B q t h l i : ℝ) * (q : ℝ) * θ n i) := by
      intro n
      rw [dividedMode_phase B q t h l (θ n) hqdvd]
    have hfun :
        (fun N : ℕ =>
          (∑ n ∈ range N,
            e (∑ i : I, (t i : ℝ) * ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i)) / N)
          = fun N =>
            (∑ n ∈ range N,
              e (∑ i : I, (dividedMode B q t h l i : ℝ) *
                ((q : ℝ) * θ n i))) / N := by
      funext N
      congr 1
      refine sum_congr rfl fun n _ => ?_
      rw [hrew n]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      ring
    rw [hfun]
    simpa [hhl] using hmode

private theorem ofReal_clockKernelSq {I : Type*} [Fintype I]
    (B : ℕ) (t : I → ℤ) {H : ℕ} (hH : 0 < H) (x : I → ℝ) :
    ((clockKernelSq B t H x : ℝ) : ℂ) =
      clockKernel B t H x * star (clockKernel B t H x) := by
  unfold clockKernelSq
  exact ofReal_norm_sq _

private theorem tendsto_clockKernelSq_mean {I : Type*} [Fintype I] [DecidableEq I]
    {B q : ℕ} {θ : ℕ → I → ℝ} {t : I → ℤ} {H : ℕ}
    (hB : 2 ≤ B) (hq : 0 < q) (hqdvd : (q : ℤ) ∣ ((B : ℤ) - 1))
    (hW : SequenceWeyl (fun n i => (q : ℝ) * θ n i))
    (ht : ∃ i, t i ≠ 0) (hH : 0 < H) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, clockKernelSq B t H (θ n)) / N)
      atTop (𝓝 ((1 : ℝ) / H)) := by
  have hH0 : (H : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hH)
  have hC :
      Tendsto (fun N : ℕ =>
        ((∑ n ∈ range N, clockKernelSq B t H (θ n)) / N : ℂ))
        atTop (𝓝 ((1 : ℂ) / H)) := by
    have hrew : ∀ N,
        ((∑ n ∈ range N, clockKernelSq B t H (θ n)) / N : ℂ) =
          ((1 : ℂ) / (H : ℂ) ^ 2) *
            ∑ h ∈ range H, ∑ l ∈ range H,
              (∑ n ∈ range N,
                e (∑ i : I, (t i : ℝ) *
                  ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i)) / N := by
      intro N
      rw [Complex.ofReal_sum]
      have hpt : ∀ n ∈ range N,
          ((clockKernelSq B t H (θ n) : ℝ) : ℂ) =
            ((1 : ℂ) / (H : ℂ) ^ 2) *
              ∑ h ∈ range H, ∑ l ∈ range H,
                e (∑ i : I, (t i : ℝ) *
                  ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i) := by
        intro n _
        rw [ofReal_clockKernelSq B t hH (θ n),
          clockKernel_mul_star B t hH (θ n)]
      have hsum :
          ∑ n ∈ range N, ((clockKernelSq B t H (θ n) : ℝ) : ℂ) =
            ∑ n ∈ range N,
              ((1 : ℂ) / (H : ℂ) ^ 2) *
                ∑ h ∈ range H, ∑ l ∈ range H,
                  e (∑ i : I, (t i : ℝ) *
                    ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i) :=
        sum_congr rfl hpt
      rw [hsum, ← mul_sum]
      have hcomm :
          ∑ n ∈ range N, ∑ h ∈ range H, ∑ l ∈ range H,
              e (∑ i : I, (t i : ℝ) *
                ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i) =
            ∑ h ∈ range H, ∑ l ∈ range H, ∑ n ∈ range N,
              e (∑ i : I, (t i : ℝ) *
                ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i) := by
        rw [sum_comm]
        refine sum_congr rfl fun h _ => sum_comm
      rw [hcomm]
      simp_rw [div_eq_mul_inv]
      rw [mul_assoc]
      congr 1
      rw [sum_mul]
      refine sum_congr rfl fun h _ => ?_
      rw [sum_mul]
    have hpairs :=
      tendsto_finset_sum_nhds (range H)
        (fun h N => ∑ l ∈ range H,
          (∑ n ∈ range N,
            e (∑ i : I, (t i : ℝ) *
              ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i)) / N)
        (fun h => ∑ l ∈ range H, (if h = l then (1 : ℂ) else 0))
        (fun h _ =>
          tendsto_finset_sum_nhds (range H)
            (fun l N =>
              (∑ n ∈ range N,
                e (∑ i : I, (t i : ℝ) *
                  ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i)) / N)
            (fun l => if h = l then (1 : ℂ) else 0)
            (fun l _ => tendsto_clock_pair hB hq hqdvd hW ht h l))
    have hdiag :
        ∑ h ∈ range H, ∑ l ∈ range H, (if h = l then (1 : ℂ) else 0) = H := by
      have hpt : ∀ h ∈ range H,
          ∑ l ∈ range H, (if h = l then (1 : ℂ) else 0) = 1 := by
        intro h hh
        rw [sum_ite_eq, if_pos hh]
      rw [sum_congr rfl hpt, sum_const, card_range, nsmul_eq_mul, mul_one]
    have hscale :=
      tendsto_const_nhds (x := ((1 : ℂ) / (H : ℂ) ^ 2)).mul hpairs
    have hval : ((1 : ℂ) / (H : ℂ) ^ 2) * (H : ℂ) = (1 : ℂ) / H := by
      field_simp [hH0]
    have hcoe :
        (fun N : ℕ =>
          ((∑ n ∈ range N, clockKernelSq B t H (θ n)) / N : ℂ))
          = fun N =>
            ((1 : ℂ) / (H : ℂ) ^ 2) *
              ∑ h ∈ range H, ∑ l ∈ range H,
                (∑ n ∈ range N,
                  e (∑ i : I, (t i : ℝ) *
                    ((B : ℝ) ^ h - (B : ℝ) ^ l) * θ n i)) / N := by
      funext N
      exact hrew N
    rw [hcoe]
    have hlim := hdiag ▸ hscale
    exact hval ▸ hlim
  have hlim : ((1 : ℂ) / H) = ↑((1 : ℝ) / H) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  have hfun :
      (fun N : ℕ => ↑((∑ n ∈ range N, clockKernelSq B t H (θ n)) / N))
        = fun N => ((∑ n ∈ range N, clockKernelSq B t H (θ n)) / N : ℂ) := by
    funext N
    exact Complex.ofReal_div _ _
  exact Filter.tendsto_ofReal_iff.1 (hfun.symm ▸ (hlim ▸ hC))

/-- Combined positive rank-class / `q`-lift: integer covariance
`θ_(n+s)-Bθ_n∈ℤ^d` and vanishing integer Cesàro means of
`e(q⟨u,θ_n⟩)` imply that every residue class `θ_(r+sm)` is
sequence-Weyl. Finite loss `limsup |class avg|² ≤ s/H`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §8;
`rounds/round101/03_gpt_periodic_weights_second_read.md` §5;
`rounds/round101/04_common_proof_specification_v1.md` §3.4.
Contract: API
Audit: GREEN -/
theorem commonClock_centeredLift
    {I : Type*} [Fintype I] [DecidableEq I]
    {B s q : ℕ} {θ : ℕ → I → ℝ}
    (hB : 2 ≤ B) (hs : 0 < s) (hq : 0 < q)
    (hqdvd : (q : ℤ) ∣ ((B : ℤ) - 1))
    (hcov : IntegerShiftCov B s θ)
    (hW : SequenceWeyl (fun n i => (q : ℝ) * θ n i))
    {r : ℕ} (hr : r < s) :
    SequenceWeyl (fun m i => θ (r + s * m) i) := by
  intro t ht
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨H0, hH0⟩ := exists_nat_gt (4 * (s : ℝ) / ε ^ 2)
  let H := H0 + 1
  have hH : 0 < H := Nat.succ_pos _
  have hHεsq : (s : ℝ) / H < (ε / 2) ^ 2 := by
    have hHgt : 4 * (s : ℝ) / ε ^ 2 < H :=
      hH0.trans (Nat.cast_lt.mpr (Nat.lt_succ_self H0))
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hHpos : (0 : ℝ) < H := Nat.cast_pos.mpr hH
    have : (s : ℝ) / H < ε ^ 2 / 4 := by
      rw [div_lt_div_iff₀ hHpos (by norm_num : (0 : ℝ) < 4)]
      have hmul := mul_lt_mul_of_pos_right hHgt hεsq
      have hcancel : 4 * (s : ℝ) / ε ^ 2 * ε ^ 2 = 4 * s := by
        field_simp [hεsq.ne']
      rw [hcancel] at hmul
      convert hmul using 1
      · ring
      · ring
    have hsq : ε ^ 2 / 4 = (ε / 2) ^ 2 := by ring
    rwa [hsq] at this
  have hsqrtH : Real.sqrt ((s : ℝ) / H) < ε / 2 := by
    have hx : 0 ≤ (s : ℝ) / H :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hy : 0 ≤ ε / 2 := div_nonneg hε.le (by norm_num)
    exact (Real.sqrt_lt hx hy).mpr hHεsq
  let a : ℕ → ℂ := fun n => e (∑ i : I, (t i : ℝ) * θ n i)
  have ha1 : ∀ n, ‖a n‖ ≤ 1 := fun n => (norm_e _).le
  have hident : ∀ n h : ℕ,
      e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ h * θ n i) = a (n + s * h) := by
    intro n h
    exact (integerShiftCov_iterate (t := t) hcov n h).symm
  have hker : ∀ n,
      clockKernel B t H (θ n) = (∑ h ∈ range H, a (n + s * h)) / H := by
    intro n
    unfold clockKernel a
    congr 1
    exact sum_congr rfl fun h _ => hident n h
  have hFeq : ∀ n,
      clockKernelSq B t H (θ n)
        = ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2 := by
    intro n
    unfold clockKernelSq
    rw [hker n]
  have hD := tendsto_clockKernelSq_mean hB hq hqdvd hW ht hH
  have hsM : Tendsto (fun M : ℕ => s * M) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun N => ?_
    refine ⟨N, fun M hM => ?_⟩
    exact le_trans hM (Nat.le_mul_of_pos_left (m := M) hs)
  have hDs : Tendsto (fun M : ℕ =>
      (∑ n ∈ range (s * M), clockKernelSq B t H (θ n)) / (s * M : ℝ))
      atTop (𝓝 ((1 : ℝ) / H)) := by
    have hfun :
        (fun M : ℕ =>
          (∑ n ∈ range (s * M), clockKernelSq B t H (θ n)) / (s * M : ℝ))
          = (fun N : ℕ =>
              (∑ n ∈ range N, clockKernelSq B t H (θ n)) / N) ∘
            fun M => s * M := by
      funext M
      simp [Function.comp_apply, Nat.cast_mul]
    rw [hfun]
    exact hD.comp hsM
  set gapVal : ℝ := (ε / 2) ^ 2 - (s : ℝ) / H
  have hgap : (0 : ℝ) < gapVal := sub_pos.mpr hHεsq
  have hspos : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hδ : (0 : ℝ) < gapVal / s := div_pos hgap hspos
  have hshift0 :=
    tendsto_const_div_atTop_nhds_zero_nat ((H : ℝ) - 1)
  filter_upwards [Filter.eventually_ge_atTop 1,
    hDs.eventually (Metric.ball_mem_nhds ((1 : ℝ) / H) hδ),
    hshift0.eventually (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))] with
    M hM1 hDclose hshiftM
  have hM : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hM1
  have hbound :=
    positiveProgressionShiftBound a hs hM hH hr ha1
  have hrewF :
      (∑ n ∈ range (s * M),
          ‖(∑ h ∈ range H, a (n + s * h)) / H‖ ^ 2)
        = ∑ n ∈ range (s * M), clockKernelSq B t H (θ n) :=
    sum_congr rfl fun n _ => (hFeq n).symm
  rw [hrewF] at hbound
  set havg : ℝ :=
    (∑ n ∈ range (s * M), clockKernelSq B t H (θ n)) / (s * M : ℝ)
  have havg_lt : havg * s < (ε / 2) ^ 2 := by
    have habs : |havg - (1 : ℝ) / H| < gapVal / s := by
      simpa [Real.dist_eq, havg] using hDclose
    have hle : havg - (1 : ℝ) / H ≤ |havg - (1 : ℝ) / H| := le_abs_self _
    have hlt : havg - (1 : ℝ) / H < gapVal / s := lt_of_le_of_lt hle habs
    have : havg < (1 : ℝ) / H + gapVal / s := by linarith
    have hmul : s * havg < s * ((1 : ℝ) / H) + gapVal := by
      have := mul_lt_mul_of_pos_left this hspos
      have hdistrib : s * ((1 : ℝ) / H + gapVal / s) = s * (1 / H) + gapVal := by
        rw [mul_add, mul_div_cancel₀ _ hspos.ne']
      rwa [hdistrib] at this
    have : s * ((1 : ℝ) / H) + gapVal = (ε / 2) ^ 2 := by
      simp [gapVal]
      ring
    have hcomm : havg * s = s * havg := mul_comm _ _
    rw [hcomm]
    exact hmul.trans_eq this
  have hnnAvg : 0 ≤ havg := by
    refine div_nonneg (sum_nonneg fun n _ => ?_)
      (mul_nonneg (Nat.cast_nonneg s) (Nat.cast_nonneg M))
    exact sq_nonneg _
  have hsqrt :
      Real.sqrt (s * havg) < ε / 2 := by
    have hx : 0 ≤ s * havg := mul_nonneg (Nat.cast_nonneg _) hnnAvg
    have hy : 0 ≤ ε / 2 := div_nonneg hε.le (by norm_num)
    have : s * havg < (ε / 2) ^ 2 := by
      rw [mul_comm]
      exact havg_lt
    exact (Real.sqrt_lt hx hy).mpr this
  have hshiftlt : ((H : ℝ) - 1) / M < ε / 2 := by
    have hK1 : 1 ≤ H := Nat.succ_le_iff.mpr hH
    have hnn : (0 : ℝ) ≤ (H : ℝ) - 1 := by
      have hcast : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
        rw [Nat.cast_sub hK1, Nat.cast_one]
      rw [← hcast]
      exact Nat.cast_nonneg _
    have habs : |((H : ℝ) - 1) / M| < ε / 2 := by
      have hNabs : |(M : ℝ)| = M := abs_of_nonneg (Nat.cast_nonneg M)
      rw [abs_div, hNabs]
      simpa [Real.dist_eq] using hshiftM
    rwa [abs_of_nonneg (div_nonneg hnn (Nat.cast_nonneg M))] at habs
  have hclass :
      ‖(∑ m ∈ range M, a (r + s * m)) / M‖ < ε := by
    have hsqrt' :
        Real.sqrt (s *
            (∑ n ∈ range (s * M), clockKernelSq B t H (θ n)) / (s * M))
          < ε / 2 := by
      convert hsqrt using 2
      rw [mul_div_assoc]
    have hε2 : ε / 2 + ε / 2 = ε := by ring
    exact hbound.trans_lt ((add_lt_add hshiftlt hsqrt').trans_eq hε2)
  simpa [a, dist_zero_right] using hclass

/-- The geometric `B`-orbit is sequence-Weyl iff the fixed vector is
common-clock `JointWeyl`.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §8–9.
Contract: API
Audit: GREEN -/
theorem sequenceWeyl_powOrbit_iff_jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I] {B : ℕ} {θ : I → ℝ} :
    SequenceWeyl (fun n i => (B : ℝ) ^ n * θ i)
      ↔ JointWeyl (fun _ : I => B) θ := by
  constructor
  · intro h t ht
    have hfun :
        (fun N : ℕ =>
          (∑ n ∈ range N,
            e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * θ i)) / N)
          = fun N =>
            (∑ n ∈ range N,
              e (∑ i : I, (t i : ℝ) * ((B : ℝ) ^ n * θ i))) / N := by
      funext N
      congr 1
      refine sum_congr rfl fun n _ => ?_
      congr 1
      refine sum_congr rfl fun i _ => ?_
      ring
    rw [hfun]
    exact h t ht
  · intro h t ht
    have hfun :
        (fun N : ℕ =>
          (∑ n ∈ range N,
            e (∑ i : I, (t i : ℝ) * ((B : ℝ) ^ n * θ i))) / N)
          = fun N =>
            (∑ n ∈ range N,
              e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * θ i)) / N := by
      funext N
      congr 1
      refine sum_congr rfl fun n _ => ?_
      congr 1
      refine sum_congr rfl fun i _ => ?_
      ring
    rw [hfun]
    exact h t ht

/-- Orbit `q = B-1` case: reuse the existing diagonal lift
`jointWeyl_of_scaled` rather than repeating the Wall argument.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §8;
`rounds/round101/02_grok_multibase_common_clock_update.md` §3.
Contract: API
Audit: GREEN -/
theorem jointWeyl_of_scaled_sequence
    {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} {θ : I → ℝ} (hB : 2 ≤ B)
    (h : SequenceWeyl (fun n i => ((B : ℝ) - 1) * ((B : ℝ) ^ n * θ i))) :
    JointWeyl (fun _ : I => B) θ := by
  have hJ : JointWeyl (fun _ : I => B) (fun i => ((B : ℝ) - 1) * θ i) := by
    refine (sequenceWeyl_powOrbit_iff_jointWeyl (B := B)
      (θ := fun i => ((B : ℝ) - 1) * θ i)).mp ?_
    intro t ht
    have hfun :
        (fun N : ℕ =>
          (∑ n ∈ range N,
            e (∑ i : I, (t i : ℝ) *
              ((B : ℝ) ^ n * (((B : ℝ) - 1) * θ i)))) / N)
          = fun N =>
            (∑ n ∈ range N,
              e (∑ i : I, (t i : ℝ) *
                (((B : ℝ) - 1) * ((B : ℝ) ^ n * θ i)))) / N := by
      funext N
      congr 1
      refine sum_congr rfl fun n _ => ?_
      congr 1
      refine sum_congr rfl fun i _ => ?_
      ring
    rw [hfun]
    exact h t ht
  exact jointWeyl_of_scaled (fun _ => hB) hJ

/-- Nonzero integer coordinate scaling preserves common-clock `JointWeyl`.
Modes `t_i` become `t_i c_i`; vanishing coordinates are excluded.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (9.2).
Contract: API
Audit: GREEN -/
theorem jointWeyl_mul_int
    {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} {θ : I → ℝ} {c : I → ℤ}
    (h : JointWeyl (fun _ : I => B) θ) (hc : ∀ i, c i ≠ 0) :
    JointWeyl (fun _ : I => B) (fun i => (c i : ℝ) * θ i) := by
  intro t ht
  have ht' : ∃ i, t i * c i ≠ 0 := by
    obtain ⟨i, hi⟩ := ht
    exact ⟨i, mul_ne_zero hi (hc i)⟩
  have hphase : ∀ n : ℕ,
      ∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * ((c i : ℝ) * θ i)
        = ∑ i : I, ((t i * c i : ℤ) : ℝ) * (B : ℝ) ^ n * θ i := by
    intro n
    refine sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have hfun :
      (fun N : ℕ =>
        (∑ n ∈ range N,
          e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * ((c i : ℝ) * θ i))) / N)
        = fun N =>
          (∑ n ∈ range N,
            e (∑ i : I, ((t i * c i : ℤ) : ℝ) * (B : ℝ) ^ n * θ i)) / N := by
    funext N
    congr 1
    exact sum_congr rfl fun n _ => by rw [hphase n]
  rw [hfun]
  exact h (fun i => t i * c i) ht'

/-- Adding an integer vector does not change common-clock characters.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` (9.1).
Contract: API
Audit: GREEN -/
theorem jointWeyl_add_int
    {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} {θ : I → ℝ} (z : I → ℤ)
    (h : JointWeyl (fun _ : I => B) θ) :
    JointWeyl (fun _ : I => B) (fun i => θ i + (z i : ℝ)) := by
  intro t ht
  have hrew : ∀ n : ℕ,
      e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * (θ i + (z i : ℝ)))
        = e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * θ i) := by
    intro n
    have hsplit :
        ∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * (θ i + (z i : ℝ))
          = ∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * θ i
            + ∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * (z i : ℝ) := by
      simp_rw [mul_add, sum_add_distrib]
    have hint :
        ∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * (z i : ℝ)
          = ((∑ i : I, t i * (B : ℤ) ^ n * z i : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [hsplit, e_add, hint, e_int, mul_one]
  have hfun :
      (fun N : ℕ =>
        (∑ n ∈ range N,
          e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * (θ i + (z i : ℝ)))) / N)
        = fun N =>
          (∑ n ∈ range N,
            e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * θ i)) / N := by
    funext N
    congr 1
    exact sum_congr rfl fun n _ => hrew n
  rw [hfun]
  exact h t ht

/-- Rational periodic weights of a common-clock jointly Weyl vector are
themselves Weyl-normal. Denominators are removed by the existing scalar
Wall lift `weylCriterion_of_mul`, not by the special `q | (B-1)` lemma.

Source: `rounds/round101/01_gpt_periodic_weights_normality.md` §9;
`rounds/round101/03_gpt_periodic_weights_second_read.md` §6.
Contract: API
Audit: GREEN -/
theorem weylCriterion_periodicWeights
    {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} (hB : 2 ≤ B) {θ : I → ℝ} {q : I → ℚ}
    (h : JointWeyl (fun _ : I => B) θ) (hq : ∃ i, q i ≠ 0) :
    weylCriterion B (∑ i, (q i : ℝ) * θ i) :=
  weylCriterion_linearCombination hB h hq

end PrimeGapNormality.Prime
