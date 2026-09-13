import PrimeGapNormality.Prime.GapAbel
import PrimeGapNormality.Prime.PrimeSeries
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Order.Filter.IsBounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Infinite periodic Abel: position weights beyond `c ≡ 1`

Paper (prop:abel) / (11.3): for `k`-periodic real or rational position
weights `c` and Abel gap weights
`d_j = periodicGapWeight c B k j`,

`∑' n, c_{n+1} p_n B^{-(n+1)}
  = p_0 · d_0 + ∑' n, d_{n+1} g_n B^{-(n+1)}`.

The finite identity is `finite_gap_abel`; the terminal `a_N d_N / B^N`
vanishes by polynomial growth `nthPrime n ≤ 144 (n+1)^2` and
boundedness of periodic `d`. The weight map is inverted by
`c_{j+1} = recGapWeight B d j` without a determinant.

Affine (degree `≤ 1`) periodic gap polynomials split into this Abel
series plus a periodic constant geometric series. Degree `≥ 2`
position polynomials `∑ P(p_n) B^{-n}` are **not** an Abel identity.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` prop:abel;
`rounds/round103/01_gpt_gap_polynomial_normality.md` (11.1)–(11.3);
`GapAbel.finite_gap_abel`; `PrimeSeries.nthPrime_le_succ_sq`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Filter Polynomial
open Function hiding eval
open scoped Topology

set_option maxHeartbeats 800000

/-! ### Weighted series -/

/-- Paper `∑_{n≥1} c_n a_n B^{-n}`. Lean `n` is 0-based, so the
summand uses `c (n+1)` and `nthPrime n`. -/
noncomputable def primePosWeightedSeries (c : ℕ → ℝ) (B : ℕ) : ℝ :=
  ∑' n : ℕ, c (n + 1) * (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)

/-- Paper `∑_{j≥1} d_j g_j B^{-j}`. Lean `n` uses `d (n+1)` and
`primeGap n`. -/
noncomputable def primeGapWeightedSeries (d : ℕ → ℝ) (B : ℕ) : ℝ :=
  ∑' n : ℕ, d (n + 1) * (primeGap n : ℝ) / (B : ℝ) ^ (n + 1)

/-- Periodic (or arbitrary) constant series `∑ β_n B^{-(n+1)}`. -/
noncomputable def geomWeightSeries (β : ℕ → ℝ) (B : ℕ) : ℝ :=
  ∑' n : ℕ, β n / (B : ℝ) ^ (n + 1)

/-- Rational periodic Abel weight, same cyclic sum as
`periodicGapWeight` over `ℚ`. -/
noncomputable def periodicGapWeightQ (c : ℕ → ℚ) (B k j : ℕ) : ℚ :=
  (∑ ℓ ∈ range k, c (j + ℓ + 1) * (B : ℚ) ^ (k - 1 - ℓ)) / ((B : ℚ) ^ k - 1)

/-- Linear coefficient of a periodic affine family, wrapped so that
`d (n+1) = (P n).coeff 1`. Requires `1 ≤ k`. -/
noncomputable def affinePeriodicGapWeight (P : ℕ → ℝ[X]) (k j : ℕ) : ℝ :=
  (P (j + (k - 1))).coeff 1

/-! ### Base and periodicity -/

private theorem one_lt_cast_of_two_le {B : ℕ} (hB : 2 ≤ B) : (1 : ℝ) < B := by
  have : (2 : ℝ) ≤ B := Nat.cast_le.mpr hB
  linarith

private theorem base_cast_pos {B : ℕ} (hB : 2 ≤ B) : (0 : ℝ) < B :=
  lt_trans (by norm_num) (one_lt_cast_of_two_le hB)

private theorem base_cast_ne_zero {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) ≠ 0 :=
  (base_cast_pos hB).ne'

private theorem base_pow_sub_one_ne_zero {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) :
    (B : ℝ) ^ k - 1 ≠ 0 := by
  have hBpos : (1 : ℝ) < B := one_lt_cast_of_two_le hB
  have hpow : (1 : ℝ) < (B : ℝ) ^ k :=
    one_lt_pow₀ hBpos (Nat.pos_iff_ne_zero.mp hk)
  exact sub_ne_zero.mpr hpow.ne'

theorem base_pow_sub_one_ne_zero_rat {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) :
    (B : ℚ) ^ k - 1 ≠ 0 := by
  have hBpos : (1 : ℚ) < B :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hB)
  have hpow : (1 : ℚ) < (B : ℚ) ^ k :=
    one_lt_pow₀ hBpos (Nat.pos_iff_ne_zero.mp hk)
  exact sub_ne_zero.mpr hpow.ne'

private theorem periodic_add_mul {α : Type*} {f : ℕ → α} {k : ℕ}
    (hf : Periodic f k) (m x : ℕ) : f (x + k * m) = f x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, ← add_assoc, hf, ih]

private theorem periodic_eq_mod {α : Type*} {f : ℕ → α} {k n : ℕ}
    (hf : Periodic f k) (_hk : 0 < k) : f n = f (n % k) := by
  have hdiv : n = n % k + k * (n / k) := by
    rw [Nat.add_comm, Nat.div_add_mod]
  conv_lhs => rw [hdiv]
  exact periodic_add_mul hf _ _

theorem abs_le_sum_of_periodic {k : ℕ} (hk : 1 ≤ k) {f : ℕ → ℝ}
    (hf : Periodic f k) (n : ℕ) :
    |f n| ≤ ∑ j ∈ range k, |f j| := by
  have hk0 : 0 < k := Nat.succ_le_iff.mp hk
  rw [periodic_eq_mod hf hk0]
  have hmem : n % k ∈ range k := mem_range.mpr (Nat.mod_lt n hk0)
  exact single_le_sum (f := fun j => |f j|) (fun _ _ => abs_nonneg _) hmem

theorem recGapWeight_periodic {B k : ℕ} (d : ℕ → ℝ) (hd : Periodic d k) :
    Periodic (recGapWeight B d) k := by
  intro j
  unfold recGapWeight
  have h0 : d (j + k) = d j := hd j
  have h1 : d (j + 1 + k) = d (j + 1) := hd (j + 1)
  have : j + k + 1 = j + 1 + k := by omega
  rw [h0, this, h1]

theorem periodicGapWeight_periodic' {B k : ℕ} (c : ℕ → ℝ)
    (hc : Periodic c k) :
    Periodic (periodicGapWeight c B k) k :=
  fun j => periodicGapWeight_periodic c B k j hc

/-! ### Rational Abel weights -/

theorem periodicGapWeight_eq_rat {B k j : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (c : ℕ → ℚ) :
    periodicGapWeight (fun n => (c n : ℝ)) B k j =
      (periodicGapWeightQ c B k j : ℝ) := by
  have := base_pow_sub_one_ne_zero_rat hB hk
  unfold periodicGapWeight periodicGapWeightQ
  have hpow (m : ℕ) : Rat.cast ((B : ℚ) ^ m : ℚ) = (B : ℝ) ^ m := by
    rw [show ((B : ℚ) ^ m : ℚ) = ((B ^ m : ℕ) : ℚ) from (Nat.cast_pow B m).symm]
    rw [show (B : ℝ) ^ m = ((B ^ m : ℕ) : ℝ) from (Nat.cast_pow B m).symm]
    norm_cast
  have hnum :
      ((∑ ℓ ∈ range k, c (j + ℓ + 1) * (B : ℚ) ^ (k - 1 - ℓ) : ℚ) : ℝ) =
        ∑ ℓ ∈ range k, (c (j + ℓ + 1) : ℝ) * (B : ℝ) ^ (k - 1 - ℓ) := by
    rw [Rat.cast_sum]
    refine sum_congr rfl fun ℓ _ => ?_
    rw [Rat.cast_mul, hpow]
  have hden : (((B : ℚ) ^ k - 1 : ℚ) : ℝ) = (B : ℝ) ^ k - 1 := by
    rw [Rat.cast_sub, Rat.cast_one, hpow]
  rw [Rat.cast_div, hnum, hden]

theorem periodic_cast_rat {c : ℕ → ℚ} {k : ℕ} (hc : Periodic c k) :
    Periodic (fun n : ℕ => (c n : ℝ)) k :=
  fun n => congrArg (fun q : ℚ => (q : ℝ)) (hc n)

/-! ### Inverse of the periodic Abel map -/

private theorem periodicGapWeightNum_of_rec {B k j : ℕ} (hk : 1 ≤ k)
    (d : ℕ → ℝ) (hd : Periodic d k) :
    periodicGapWeightNum (fun n => recGapWeight B d (n - 1)) B k j =
      d j * ((B : ℝ) ^ k - 1) := by
  unfold periodicGapWeightNum
  have hterm :
      ∑ ℓ ∈ range k,
          recGapWeight B d (j + ℓ + 1 - 1) * (B : ℝ) ^ (k - 1 - ℓ) =
        ∑ ℓ ∈ range k,
          recGapWeight B d (j + ℓ) * (B : ℝ) ^ (k - 1 - ℓ) := by
    refine sum_congr rfl fun ℓ _ => ?_
    have : j + ℓ + 1 - 1 = j + ℓ := by omega
    rw [this]
  rw [hterm]
  unfold recGapWeight
  have hsplit :
      ∑ ℓ ∈ range k,
          ((B : ℝ) * d (j + ℓ) - d (j + ℓ + 1)) * (B : ℝ) ^ (k - 1 - ℓ) =
        ∑ ℓ ∈ range k, d (j + ℓ) * (B : ℝ) ^ (k - ℓ) -
          ∑ ℓ ∈ range k, d (j + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun ℓ hl => ?_
    have hℓ : ℓ < k := mem_range.mp hl
    have hpow : (B : ℝ) * (B : ℝ) ^ (k - 1 - ℓ) = (B : ℝ) ^ (k - ℓ) := by
      have : k - ℓ = k - 1 - ℓ + 1 := by omega
      rw [this, pow_succ]
      ring
    calc
      ((B : ℝ) * d (j + ℓ) - d (j + ℓ + 1)) * (B : ℝ) ^ (k - 1 - ℓ)
          = (B : ℝ) * d (j + ℓ) * (B : ℝ) ^ (k - 1 - ℓ) -
              d (j + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ) := by ring
      _ = d (j + ℓ) * ((B : ℝ) * (B : ℝ) ^ (k - 1 - ℓ)) -
            d (j + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ) := by ring
      _ = d (j + ℓ) * (B : ℝ) ^ (k - ℓ) -
            d (j + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ) := by rw [hpow]
  rw [hsplit]
  have hrange : range k = range (k - 1 + 1) := by rw [Nat.sub_add_cancel hk]
  have hS1 :
      ∑ ℓ ∈ range k, d (j + ℓ) * (B : ℝ) ^ (k - ℓ) =
        d j * (B : ℝ) ^ k +
          ∑ ℓ ∈ range (k - 1), d (j + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ) := by
    rw [hrange, sum_range_succ' (fun ℓ => d (j + ℓ) * (B : ℝ) ^ (k - ℓ)) (k - 1),
      add_comm]
    have hexp0 : k - 0 = k := by omega
    rw [hexp0]
    refine congrArg (d j * (B : ℝ) ^ k + ·) (sum_congr rfl fun ℓ hl => ?_)
    have hℓ : ℓ < k - 1 := mem_range.mp hl
    have hexp : k - (ℓ + 1) = k - 1 - ℓ := by omega
    have hidx : j + (ℓ + 1) = j + ℓ + 1 := by omega
    rw [hexp, hidx]
  have hS2 :
      ∑ ℓ ∈ range k, d (j + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ) =
        ∑ ℓ ∈ range (k - 1), d (j + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ) +
          d (j + k) := by
    rw [hrange,
      sum_range_succ (fun ℓ => d (j + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ)) (k - 1)]
    have hlast_idx : j + (k - 1) + 1 = j + k := by omega
    have hlast_exp : k - 1 - (k - 1) = 0 := Nat.sub_self _
    rw [hlast_idx, hlast_exp, pow_zero, mul_one]
  rw [hS1, hS2]
  have hper : d (j + k) = d j := hd j
  rw [hper]
  ring

/-- Geometric inversion: a periodic gap weight is recovered from the
induced position recurrence. Paper inverse `c_j = B d_{j-1} - d_j`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` prop:abel.
Contract: API
Audit: GREEN -/
theorem periodicGapWeight_of_rec {B k j : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (d : ℕ → ℝ) (hd : Periodic d k) :
    periodicGapWeight (fun n => recGapWeight B d (n - 1)) B k j = d j := by
  have hden := base_pow_sub_one_ne_zero hB hk
  rw [periodicGapWeight_eq_div, periodicGapWeightNum_of_rec hk d hd]
  exact mul_div_cancel_right₀ _ hden

/-! ### Summability of bounded / periodic weights -/

private theorem abs_mul_pos_div {B n : ℕ} (w : ℝ) :
    |w * (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)| =
      |w| * (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) := by
  have hp : 0 ≤ (nthPrime n : ℝ) := Nat.cast_nonneg _
  have hBn : 0 ≤ (B : ℝ) := Nat.cast_nonneg _
  rw [abs_div, abs_mul, abs_of_nonneg hp, abs_pow, abs_of_nonneg hBn]

private theorem abs_mul_gap_div {B n : ℕ} (w : ℝ) :
    |w * (primeGap n : ℝ) / (B : ℝ) ^ (n + 1)| =
      |w| * (primeGap n : ℝ) / (B : ℝ) ^ (n + 1) := by
  have hp : 0 ≤ (primeGap n : ℝ) := Nat.cast_nonneg _
  have hBn : 0 ≤ (B : ℝ) := Nat.cast_nonneg _
  rw [abs_div, abs_mul, abs_of_nonneg hp, abs_pow, abs_of_nonneg hBn]

private theorem abs_div_pow {B n : ℕ} (w : ℝ) :
    |w / (B : ℝ) ^ (n + 1)| = |w| / (B : ℝ) ^ (n + 1) := by
  have hBn : 0 ≤ (B : ℝ) := Nat.cast_nonneg _
  rw [abs_div, abs_pow, abs_of_nonneg hBn]

theorem primePosWeightedSeries_summable_of_bound {B : ℕ} (hB : 2 ≤ B)
    (c : ℕ → ℝ) {M : ℝ} (hM : ∀ n, |c (n + 1)| ≤ M) :
    Summable fun n : ℕ =>
      c (n + 1) * (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) := by
  have hpos := primePosSeries_summable hB
  have hdom :
      Summable fun n : ℕ =>
        M * ((nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)) :=
    hpos.mul_left M
  refine Summable.of_norm_bounded (g := fun n =>
      M * ((nthPrime n : ℝ) / (B : ℝ) ^ (n + 1))) hdom fun n => ?_
  have hnn : 0 ≤ (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) :=
    pos_term_nonneg B n
  rw [Real.norm_eq_abs, abs_mul_pos_div]
  have : |c (n + 1)| * (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) =
      |c (n + 1)| * ((nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (hM n) hnn

theorem primeGapWeightedSeries_summable_of_bound {B : ℕ} (hB : 2 ≤ B)
    (d : ℕ → ℝ) {M : ℝ} (hM : ∀ n, |d (n + 1)| ≤ M) :
    Summable fun n : ℕ =>
      d (n + 1) * (primeGap n : ℝ) / (B : ℝ) ^ (n + 1) := by
  have hgap := primeGapPowerSeries_summable (B := B) (d := 1) hB
  have hfun :
      (fun n : ℕ => (primeGap n : ℝ) ^ 1 / (B : ℝ) ^ (n + 1)) =
        fun n => (primeGap n : ℝ) / (B : ℝ) ^ (n + 1) := by
    funext n
    rw [pow_one]
  rw [hfun] at hgap
  have hdom :
      Summable fun n : ℕ =>
        M * ((primeGap n : ℝ) / (B : ℝ) ^ (n + 1)) :=
    hgap.mul_left M
  refine Summable.of_norm_bounded hdom fun n => ?_
  have hnn : 0 ≤ (primeGap n : ℝ) / (B : ℝ) ^ (n + 1) :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  rw [Real.norm_eq_abs, abs_mul_gap_div]
  have : |d (n + 1)| * (primeGap n : ℝ) / (B : ℝ) ^ (n + 1) =
      |d (n + 1)| * ((primeGap n : ℝ) / (B : ℝ) ^ (n + 1)) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (hM n) hnn

theorem geomWeightSeries_summable_of_bound {B : ℕ} (hB : 2 ≤ B)
    (β : ℕ → ℝ) {M : ℝ} (hM : ∀ n, |β n| ≤ M) :
    Summable fun n : ℕ => β n / (B : ℝ) ^ (n + 1) := by
  have hgeo := primeGapPowerSeries_summable (B := B) (d := 0) hB
  have hfun :
      (fun n : ℕ => (primeGap n : ℝ) ^ 0 / (B : ℝ) ^ (n + 1)) =
        fun n => (1 : ℝ) / (B : ℝ) ^ (n + 1) := by
    funext n
    rw [pow_zero]
  rw [hfun] at hgeo
  have hdom :
      Summable fun n : ℕ => M * ((1 : ℝ) / (B : ℝ) ^ (n + 1)) :=
    hgeo.mul_left M
  refine Summable.of_norm_bounded hdom fun n => ?_
  have hnn : 0 ≤ (1 : ℝ) / (B : ℝ) ^ (n + 1) :=
    div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _)
  rw [Real.norm_eq_abs, abs_div_pow]
  have : |β n| / (B : ℝ) ^ (n + 1) = |β n| * ((1 : ℝ) / (B : ℝ) ^ (n + 1)) := by
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (hM n) hnn

theorem primePosWeightedSeries_summable {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (c : ℕ → ℝ) (hc : Periodic c k) :
    Summable fun n : ℕ =>
      c (n + 1) * (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) :=
  primePosWeightedSeries_summable_of_bound hB c
    (fun n => abs_le_sum_of_periodic hk hc (n + 1))

theorem primeGapWeightedSeries_summable {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (d : ℕ → ℝ) (hd : Periodic d k) :
    Summable fun n : ℕ =>
      d (n + 1) * (primeGap n : ℝ) / (B : ℝ) ^ (n + 1) :=
  primeGapWeightedSeries_summable_of_bound hB d
    (fun n => abs_le_sum_of_periodic hk hd (n + 1))

theorem geomWeightSeries_summable {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (β : ℕ → ℝ) (hβ : Periodic β k) :
    Summable fun n : ℕ => β n / (B : ℝ) ^ (n + 1) :=
  geomWeightSeries_summable_of_bound hB β
    (fun n => abs_le_sum_of_periodic hk hβ n)

/-! ### Terminal vanishing via polynomial growth -/

/-- `a_N d_N / B^N → 0` for periodic (hence bounded) `d`, using
`nthPrime n ≤ 144 (n+1)^2`. -/
theorem tendsto_nthPrime_mul_periodic_div_pow {B k : ℕ} (hB : 2 ≤ B)
    (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : Periodic d k) :
    Tendsto (fun n : ℕ =>
      (nthPrime n : ℝ) * d (n + 1) / (B : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
  let M : ℝ := ∑ j ∈ range k, |d j|
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => ‖d (n + 1)‖) :=
    isBoundedUnder_of_eventually_le (a := M)
      (Eventually.of_forall fun n => by
        simpa [Real.norm_eq_abs] using abs_le_sum_of_periodic hk hd (n + 1))
  have hfun :
      (fun n : ℕ =>
          (nthPrime n : ℝ) * d (n + 1) / (B : ℝ) ^ (n + 1)) =
        fun n => d (n + 1) * ((nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)) := by
    funext n
    ring
  rw [hfun]
  exact isBoundedUnder_le_mul_tendsto_zero
    (f := fun n : ℕ => d (n + 1))
    (g := fun n : ℕ => (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1))
    hbdd (tendsto_nthPrime_div_pow_succ hB)

/-! ### Finite Abel for arbitrary / periodic weights -/

/-- Finite Abel for `nthPrime` with an arbitrary recurrence weight `d`.
Lean `i ∈ range N` is paper `n = i+1`. -/
theorem finite_primePos_rec_abel {B N : ℕ} (hB : 2 ≤ B) (hN : 1 ≤ N)
    (d : ℕ → ℝ) :
    ∑ i ∈ range N,
        recGapWeight B d i * (nthPrime i : ℝ) / (B : ℝ) ^ (i + 1) =
      (nthPrime 0 : ℝ) * d 0 +
        ∑ i ∈ range (N - 1),
          d (i + 1) * (primeGap i : ℝ) / (B : ℝ) ^ (i + 1) -
        (nthPrime (N - 1) : ℝ) * d N / (B : ℝ) ^ N := by
  let a : ℕ → ℝ := fun t => (nthPrime (t - 1) : ℝ)
  have habel := finite_gap_abel (B := B) (a := a) (d := d) hB hN
  have hLHS :
      ∑ i ∈ range N, recGapWeight B d i * a (i + 1) / (B : ℝ) ^ (i + 1) =
        ∑ i ∈ range N,
          recGapWeight B d i * (nthPrime i : ℝ) / (B : ℝ) ^ (i + 1) := by
    refine sum_congr rfl fun i _ => ?_
    have : i + 1 - 1 = i := Nat.add_sub_cancel i 1
    simp [a, this]
  have hRHS_gap :
      ∑ i ∈ range (N - 1),
          d (i + 1) * (a (i + 2) - a (i + 1)) / (B : ℝ) ^ (i + 1) =
        ∑ i ∈ range (N - 1),
          d (i + 1) * (primeGap i : ℝ) / (B : ℝ) ^ (i + 1) := by
    refine sum_congr rfl fun i _ => ?_
    have hi1 : i + 2 - 1 = i + 1 := by omega
    have hi0 : i + 1 - 1 = i := by omega
    have hg : a (i + 2) - a (i + 1) = (primeGap i : ℝ) := by
      simp [a, hi1, hi0, primeGap_cast]
    rw [hg]
  have ha1 : a 1 = nthPrime 0 := by simp [a]
  have haN : a N = nthPrime (N - 1) := rfl
  rw [hLHS] at habel
  rw [habel, ha1, haN, hRHS_gap]

/-- Finite Abel for periodic position weights, `d = periodicGapWeight c`. -/
theorem finite_primePos_weighted_abel {B k N : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (hN : 1 ≤ N) (c : ℕ → ℝ) (hc : Periodic c k) :
    ∑ i ∈ range N, c (i + 1) * (nthPrime i : ℝ) / (B : ℝ) ^ (i + 1) =
      (nthPrime 0 : ℝ) * periodicGapWeight c B k 0 +
        ∑ i ∈ range (N - 1),
          periodicGapWeight c B k (i + 1) * (primeGap i : ℝ) /
            (B : ℝ) ^ (i + 1) -
        (nthPrime (N - 1) : ℝ) * periodicGapWeight c B k N /
          (B : ℝ) ^ N := by
  have hrec : ∀ i,
      recGapWeight B (periodicGapWeight c B k) i = c (i + 1) :=
    fun i => periodicGapWeight_rec hB hk c hc
  have hfin := finite_primePos_rec_abel (B := B) (N := N) hB hN
    (periodicGapWeight c B k)
  simp_rw [hrec] at hfin
  exact hfin

/-! ### Infinite Abel -/

/-- Infinite Abel for an arbitrary periodic gap weight `d`: the induced
position series is `recGapWeight B d`. Terminal vanishes by polynomial
growth of `nthPrime`.

Exact identity:
`∑' n, (B d_n - d_{n+1}) p_n B^{-(n+1)}
  = p_0 · d_0 + ∑' n, d_{n+1} g_n B^{-(n+1)}`. -/
theorem recPosWeight_tsum_eq_gapAbel {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (d : ℕ → ℝ) (hd : Periodic d k) :
    primePosWeightedSeries (fun n => recGapWeight B d (n - 1)) B =
      (nthPrime 0 : ℝ) * d 0 + primeGapWeightedSeries d B := by
  have hpos :
      Summable fun n : ℕ =>
        recGapWeight B d n * (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) := by
    have hrec : Periodic (recGapWeight B d) k := recGapWeight_periodic d hd
    refine primePosWeightedSeries_summable_of_bound (M :=
        ∑ j ∈ range k, |recGapWeight B d j|) hB
      (fun n => recGapWeight B d (n - 1)) fun n => ?_
    have : n + 1 - 1 = n := Nat.add_sub_cancel n 1
    simpa [this] using abs_le_sum_of_periodic hk hrec n
  have hgap := primeGapWeightedSeries_summable hB hk d hd
  let f : ℕ → ℝ := fun n =>
    recGapWeight B d n * (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)
  let g : ℕ → ℝ := fun n =>
    d (n + 1) * (primeGap n : ℝ) / (B : ℝ) ^ (n + 1)
  have hf : Summable f := hpos
  have hg : Summable g := hgap
  have hfin (n : ℕ) :
      ∑ i ∈ range (n + 1), f i =
        (nthPrime 0 : ℝ) * d 0 + ∑ i ∈ range n, g i -
          (nthPrime n : ℝ) * d (n + 1) / (B : ℝ) ^ (n + 1) := by
    simpa [f, g, Nat.add_sub_cancel] using
      finite_primePos_rec_abel (B := B) (N := n + 1) hB
        (Nat.succ_le_succ (Nat.zero_le n)) d
  have hST : Tendsto (fun n : ℕ => ∑ i ∈ range (n + 1), f i) atTop
      (𝓝 (∑' n, f n)) :=
    hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hGT : Tendsto (fun n : ℕ => ∑ i ∈ range n, g i) atTop
      (𝓝 (∑' n, g n)) :=
    hg.hasSum.tendsto_sum_nat
  have hRT := tendsto_nthPrime_mul_periodic_div_pow hB hk d hd
  have htarget :
      Tendsto (fun n : ℕ =>
        (nthPrime 0 : ℝ) * d 0 + ∑ i ∈ range n, g i -
          (nthPrime n : ℝ) * d (n + 1) / (B : ℝ) ^ (n + 1)) atTop
        (𝓝 ((nthPrime 0 : ℝ) * d 0 + ∑' n, g n)) := by
    have hadd :=
      tendsto_const_nhds (x := (nthPrime 0 : ℝ) * d 0) |>.add hGT
    simpa using hadd.sub hRT
  have hS' :
      Tendsto (fun n : ℕ => ∑ i ∈ range (n + 1), f i) atTop
        (𝓝 ((nthPrime 0 : ℝ) * d 0 + ∑' n, g n)) :=
    htarget.congr fun n => (hfin n).symm
  have huniq := tendsto_nhds_unique hST hS'
  have hrew :
      primePosWeightedSeries (fun n => recGapWeight B d (n - 1)) B =
        ∑' n, f n := by
    unfold primePosWeightedSeries
    refine tsum_congr fun n => ?_
    have : n + 1 - 1 = n := Nat.add_sub_cancel n 1
    simp [f, this]
  simpa [hrew, primeGapWeightedSeries, g] using huniq

/-- Infinite Abel for `k`-periodic position weights. Exact tsum identity
of paper (eq:abel) / (11.3), Lean 0-based:

`∑' n, c (n+1) · nthPrime n · B^{-(n+1)}
  = nthPrime 0 · d 0
    + ∑' n, d (n+1) · primeGap n · B^{-(n+1)}`

with `d = periodicGapWeight c B k`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:abel).
Contract: API
Audit: GREEN -/
theorem primePosWeightedSeries_eq_gapAbel {B k : ℕ} (hB : 2 ≤ B)
    (hk : 1 ≤ k) (c : ℕ → ℝ) (hc : Periodic c k) :
    primePosWeightedSeries c B =
      (nthPrime 0 : ℝ) * periodicGapWeight c B k 0 +
        primeGapWeightedSeries (periodicGapWeight c B k) B := by
  let d : ℕ → ℝ := periodicGapWeight c B k
  have hd : Periodic d k := periodicGapWeight_periodic' c hc
  have hcore := recPosWeight_tsum_eq_gapAbel hB hk d hd
  have hrew :
      primePosWeightedSeries (fun n => recGapWeight B d (n - 1)) B =
        primePosWeightedSeries c B := by
    unfold primePosWeightedSeries
    refine tsum_congr fun n => ?_
    have : n + 1 - 1 = n := Nat.add_sub_cancel n 1
    have hrec : recGapWeight B d n = c (n + 1) :=
      periodicGapWeight_rec hB hk c hc
    simp [d, this, hrec]
  rw [← hrew]
  simpa [d] using hcore

/-- Rational-coefficient form of the infinite Abel identity. -/
theorem primePosWeightedSeries_eq_gapAbel_rat {B k : ℕ} (hB : 2 ≤ B)
    (hk : 1 ≤ k) (c : ℕ → ℚ) (hc : Periodic c k) :
    primePosWeightedSeries (fun n => (c n : ℝ)) B =
      (nthPrime 0 : ℝ) * (periodicGapWeightQ c B k 0 : ℝ) +
        primeGapWeightedSeries (fun j => (periodicGapWeightQ c B k j : ℝ)) B := by
  have hR := primePosWeightedSeries_eq_gapAbel hB hk
    (fun n => (c n : ℝ)) (periodic_cast_rat hc)
  have hd :
      periodicGapWeight (fun n => (c n : ℝ)) B k =
        fun j => (periodicGapWeightQ c B k j : ℝ) := by
    funext j
    exact periodicGapWeight_eq_rat hB hk c
  simpa [hd] using hR

theorem primePosWeightedSeries_one (B : ℕ) :
    primePosWeightedSeries (fun _ => (1 : ℝ)) B = primePosSeries B := by
  unfold primePosWeightedSeries primePosSeries
  simp

/-! ### Affine (degree ≤ 1) periodic gap polynomials -/

theorem eval_natDegree_le_one (P : ℝ[X]) (hP : natDegree P ≤ 1) (x : ℝ) :
    eval x P = P.coeff 0 + P.coeff 1 * x := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hP]
  rw [eval_add, eval_C_mul, eval_X, eval_C]
  ring

theorem eval_mapRatPoly_natDegree_le_one (P : ℚ[X])
    (hP : natDegree P ≤ 1) (x : ℝ) :
    eval x (mapRatPoly P) = (P.coeff 0 : ℝ) + (P.coeff 1 : ℝ) * x := by
  unfold mapRatPoly
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hP]
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_C, eval_add, eval_C_mul, eval_X, eval_C]
  simp [add_comm]

theorem affinePeriodicGapWeight_apply {P : ℕ → ℝ[X]} {k n : ℕ}
    (hk : 1 ≤ k) (hP : Periodic P k) :
    affinePeriodicGapWeight P k (n + 1) = (P n).coeff 1 := by
  unfold affinePeriodicGapWeight
  have : n + 1 + (k - 1) = n + k := by omega
  rw [this, hP]

theorem affinePeriodicGapWeight_periodic {P : ℕ → ℝ[X]} {k : ℕ}
    (hP : Periodic P k) :
    Periodic (affinePeriodicGapWeight P k) k := by
  intro j
  unfold affinePeriodicGapWeight
  have : j + k + (k - 1) = j + (k - 1) + k := by omega
  rw [this, hP]

theorem coeff_periodic (P : ℕ → ℝ[X]) {k : ℕ} (hP : Periodic P k)
    (i : ℕ) : Periodic (fun n => (P n).coeff i) k :=
  hP.comp (fun p => p.coeff i)

/-- Degree-`≤ 1` periodic gap polynomials split into a weighted gap
Abel series plus a periodic constant series. -/
theorem gapPolySeries_natDegree_le_one {P : ℕ → ℝ[X]} {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hP : Periodic P k)
    (hdeg : ∀ n, natDegree (P n) ≤ 1) :
    gapPolySeries P B =
      primeGapWeightedSeries (affinePeriodicGapWeight P k) B +
        geomWeightSeries (fun n => (P n).coeff 0) B := by
  have hlin : Periodic (affinePeriodicGapWeight P k) k :=
    affinePeriodicGapWeight_periodic hP
  have hcst : Periodic (fun n => (P n).coeff 0) k := coeff_periodic P hP 0
  have hf := primeGapWeightedSeries_summable hB hk
    (affinePeriodicGapWeight P k) hlin
  have hg := geomWeightSeries_summable hB hk (fun n => (P n).coeff 0) hcst
  unfold gapPolySeries primeGapWeightedSeries geomWeightSeries
  have hterm : ∀ n : ℕ,
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1) =
        affinePeriodicGapWeight P k (n + 1) * (primeGap n : ℝ) /
            (B : ℝ) ^ (n + 1) +
          (P n).coeff 0 / (B : ℝ) ^ (n + 1) := by
    intro n
    have heval := eval_natDegree_le_one (P n) (hdeg n) (primeGap n)
    have hlin' := affinePeriodicGapWeight_apply (P := P) (k := k) (n := n)
      hk hP
    rw [heval, hlin', add_div]
    ring
  simp_rw [hterm]
  exact hf.tsum_add hg

/-- Affine periodic gap-poly series as a combination of the infinite
Abel position series and a periodic constant geometric series.

`∑' n, P_n(g_n) B^{-(n+1)}
  = ∑' n, c_{n+1} p_n B^{-(n+1)} - p_0 d_0
    + ∑' n, (P_n).coeff 0 · B^{-(n+1)}`

with `d_j = (P_{j+k-1}).coeff 1` and `c_{n+1} = B d_n - d_{n+1}`. -/
theorem gapPolySeries_affine_eq_abel {P : ℕ → ℝ[X]} {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hP : Periodic P k)
    (hdeg : ∀ n, natDegree (P n) ≤ 1) :
    gapPolySeries P B =
      primePosWeightedSeries
          (fun n => recGapWeight B (affinePeriodicGapWeight P k) (n - 1)) B -
        (nthPrime 0 : ℝ) * affinePeriodicGapWeight P k 0 +
        geomWeightSeries (fun n => (P n).coeff 0) B := by
  have hsplit := gapPolySeries_natDegree_le_one hB hk hP hdeg
  have hd : Periodic (affinePeriodicGapWeight P k) k :=
    affinePeriodicGapWeight_periodic hP
  have habel := recPosWeight_tsum_eq_gapAbel hB hk
    (affinePeriodicGapWeight P k) hd
  have hlin :
      primeGapWeightedSeries (affinePeriodicGapWeight P k) B =
        primePosWeightedSeries
            (fun n => recGapWeight B (affinePeriodicGapWeight P k) (n - 1)) B -
          (nthPrime 0 : ℝ) * affinePeriodicGapWeight P k 0 := by
    exact eq_sub_of_add_eq' habel.symm
  rw [hsplit, hlin]

private theorem periodic_coeff_rat {P : ℕ → ℚ[X]} {k : ℕ} (hP : Periodic P k)
    (i : ℕ) : Periodic (fun n => ((P n).coeff i : ℝ)) k :=
  fun n => congrArg (fun q : ℚ => (q : ℝ))
    (congrArg (fun p => p.coeff i) (hP n))

/-- Rational affine form: `P_n ∈ ℚ[X]`, `deg ≤ 1`, period `k`. -/
theorem gapRatPolySeries_affine_eq_abel {P : ℕ → ℚ[X]} {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hP : Periodic P k)
    (hdeg : ∀ n, natDegree (P n) ≤ 1) :
    gapRatPolySeries P B =
      primePosWeightedSeries
          (fun n =>
            recGapWeight B (fun j => ((P (j + (k - 1))).coeff 1 : ℝ))
              (n - 1)) B -
        (nthPrime 0 : ℝ) * ((P (k - 1)).coeff 1 : ℝ) +
        geomWeightSeries (fun n => ((P n).coeff 0 : ℝ)) B := by
  let d : ℕ → ℝ := fun j => ((P (j + (k - 1))).coeff 1 : ℝ)
  have hd : Periodic d k := by
    intro j
    have : j + k + (k - 1) = j + (k - 1) + k := by omega
    simp only [d]
    rw [this]
    exact congrArg (fun q : ℚ => (q : ℝ))
      (congrArg (fun p => p.coeff 1) (hP (j + (k - 1))))
  have hlinP : ∀ n, d (n + 1) = ((P n).coeff 1 : ℝ) := by
    intro n
    have : n + 1 + (k - 1) = n + k := by omega
    simp only [d]
    rw [this]
    exact congrArg (fun q : ℚ => (q : ℝ))
      (congrArg (fun p => p.coeff 1) (hP n))
  have hcst : Periodic (fun n => ((P n).coeff 0 : ℝ)) k :=
    periodic_coeff_rat hP 0
  have hf : Summable fun n : ℕ =>
      d (n + 1) * (primeGap n : ℝ) / (B : ℝ) ^ (n + 1) :=
    primeGapWeightedSeries_summable hB hk d hd
  have hg :=
    geomWeightSeries_summable hB hk (fun n => ((P n).coeff 0 : ℝ)) hcst
  have hsplit : gapRatPolySeries P B =
      primeGapWeightedSeries d B +
        geomWeightSeries (fun n => ((P n).coeff 0 : ℝ)) B := by
    unfold gapRatPolySeries gapPolySeries primeGapWeightedSeries
      geomWeightSeries
    have hterm : ∀ n : ℕ,
        eval (primeGap n : ℝ) (mapRatPoly (P n)) / (B : ℝ) ^ (n + 1) =
          d (n + 1) * (primeGap n : ℝ) / (B : ℝ) ^ (n + 1) +
            ((P n).coeff 0 : ℝ) / (B : ℝ) ^ (n + 1) := by
      intro n
      have heval :=
        eval_mapRatPoly_natDegree_le_one (P n) (hdeg n) (primeGap n)
      rw [heval, hlinP n, add_div]
      ring
    simp_rw [hterm]
    exact hf.tsum_add hg
  have habel := recPosWeight_tsum_eq_gapAbel hB hk d hd
  have hlin :
      primeGapWeightedSeries d B =
        primePosWeightedSeries (fun n => recGapWeight B d (n - 1)) B -
          (nthPrime 0 : ℝ) * d 0 := by
    exact eq_sub_of_add_eq' habel.symm
  have hd0 : d 0 = ((P (k - 1)).coeff 1 : ℝ) := by
    simp [d]
  rw [hsplit, hlin, hd0]

end PrimeGapNormality.Prime
