import PrimeGapNormality.Prime.EndAPI
import PrimeGapNormality.Prime.PrimeSeries
import PrimeGapNormality.Prime.Components
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Summability of one-gap polynomial series

A real polynomial is a finite linear combination of monomials. Each
monomial series `∑ g_n^i B^{-(n+1)}` is summable for `B ≥ 2` by
`primeGapPowerSeries_summable`, so `|P(g_n)| B^{-(n+1)}` is summable
by comparison. The same bound, applied uniformly in `n`, gives
summability for families of bounded degree and coefficient size, and
for periodic families (finitely many `P_r`). Rational series reduce
through `mapRatPoly`, with denominators cleared by
`eval_mapRatPoly_clearDenoms`.

Indexing: Lean `nthPrime 0 = 2` is paper `p_1`. Series start at
`/ B^(n+1)`.

Source: `EndAPI.gapPolySeries`; `PrimeSeries.primeGapPowerSeries_summable`;
`Components.eval_mapRatPoly_clearDenoms`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Polynomial
open Function (Periodic)

set_option maxHeartbeats 800000

/-! ### Evaluation bounds -/

private theorem abs_eval_le_sum_abs_mul_pow (P : ℝ[X]) (x : ℝ) :
    |eval x P| ≤ ∑ i ∈ range (P.natDegree + 1), |P.coeff i| * |x| ^ i := by
  rw [eval_eq_sum_range x]
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  refine sum_congr rfl fun i _ => ?_
  rw [abs_mul, abs_pow]

private theorem abs_eval_le_sum_abs_mul_pow_of_natDegree_le {P : ℝ[X]} {D : ℕ}
    (hD : P.natDegree ≤ D) (x : ℝ) :
    |eval x P| ≤ ∑ i ∈ range (D + 1), |P.coeff i| * |x| ^ i := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hD) x]
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  refine sum_congr rfl fun i _ => ?_
  rw [abs_mul, abs_pow]

private theorem abs_eval_div_le_sum_monomial (P : ℝ[X]) (B n : ℕ) :
    |eval (primeGap n : ℝ) P| / (B : ℝ) ^ (n + 1) ≤
      ∑ i ∈ range (P.natDegree + 1),
        |P.coeff i| * ((primeGap n : ℝ) ^ i / (B : ℝ) ^ (n + 1)) := by
  have hx : 0 ≤ (primeGap n : ℝ) := Nat.cast_nonneg _
  have hden : 0 ≤ (B : ℝ) ^ (n + 1) := pow_nonneg (Nat.cast_nonneg _) _
  have hbound :
      |eval (primeGap n : ℝ) P| ≤
        ∑ i ∈ range (P.natDegree + 1), |P.coeff i| * (primeGap n : ℝ) ^ i := by
    have h := abs_eval_le_sum_abs_mul_pow P (primeGap n : ℝ)
    refine h.trans_eq ?_
    refine sum_congr rfl fun i _ => ?_
    rw [abs_of_nonneg hx]
  have := div_le_div_of_nonneg_right hbound hden
  refine this.trans_eq ?_
  rw [sum_div]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_div_assoc]

private theorem abs_eval_div_le_sum_monomial_of_natDegree_le
    {P : ℝ[X]} {D B n : ℕ} (hD : P.natDegree ≤ D) :
    |eval (primeGap n : ℝ) P| / (B : ℝ) ^ (n + 1) ≤
      ∑ i ∈ range (D + 1),
        |P.coeff i| * ((primeGap n : ℝ) ^ i / (B : ℝ) ^ (n + 1)) := by
  have hx : 0 ≤ (primeGap n : ℝ) := Nat.cast_nonneg _
  have hden : 0 ≤ (B : ℝ) ^ (n + 1) := pow_nonneg (Nat.cast_nonneg _) _
  have hbound :
      |eval (primeGap n : ℝ) P| ≤
        ∑ i ∈ range (D + 1), |P.coeff i| * (primeGap n : ℝ) ^ i := by
    have h := abs_eval_le_sum_abs_mul_pow_of_natDegree_le hD (primeGap n : ℝ)
    refine h.trans_eq ?_
    refine sum_congr rfl fun i _ => ?_
    rw [abs_of_nonneg hx]
  have := div_le_div_of_nonneg_right hbound hden
  refine this.trans_eq ?_
  rw [sum_div]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_div_assoc]

private theorem summable_of_abs_eval_div {P : ℕ → ℝ[X]} {B : ℕ}
    (h : Summable fun n : ℕ =>
      |eval (primeGap n : ℝ) (P n)| / (B : ℝ) ^ (n + 1)) :
    Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1) := by
  refine Summable.of_abs ?_
  have hfun :
      (fun n : ℕ => |eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1)|) =
        fun n => |eval (primeGap n : ℝ) (P n)| / (B : ℝ) ^ (n + 1) := by
    funext n
    have hden : |(B : ℝ) ^ (n + 1)| = (B : ℝ) ^ (n + 1) :=
      abs_of_nonneg (pow_nonneg (Nat.cast_nonneg B) (n + 1))
    rw [abs_div, hden]
  rwa [hfun]

/-! ### Single real polynomial -/

/-- Absolute summability of a fixed real polynomial along prime gaps:
each monomial is summable by `primeGapPowerSeries_summable`, and a
polynomial has finite degree.

Source: `PrimeSeries.primeGapPowerSeries_summable`.
Contract: API
Audit: GREEN -/
theorem gapPoly_eval_abs_summable (P : ℝ[X]) {B : ℕ} (hB : 2 ≤ B) :
    Summable fun n : ℕ =>
      |eval (primeGap n : ℝ) P| / (B : ℝ) ^ (n + 1) := by
  have hdom :
      Summable fun n : ℕ =>
        ∑ i ∈ range (P.natDegree + 1),
          |P.coeff i| * ((primeGap n : ℝ) ^ i / (B : ℝ) ^ (n + 1)) :=
    summable_sum fun i _ =>
      (primeGapPowerSeries_summable (B := B) (d := i) hB).mul_left |P.coeff i|
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
    (fun n => abs_eval_div_le_sum_monomial P B n) hdom

/-- The constant family `fun _ => P` is (absolutely) summable, so
`gapPolySeries (fun _ => P) B` is a genuine tsum.

Source: `EndAPI.gapPolySeries`.
Contract: API
Audit: GREEN -/
theorem gapPolySeries_const_summable (P : ℝ[X]) {B : ℕ} (hB : 2 ≤ B) :
    Summable fun n : ℕ =>
      eval (primeGap n : ℝ) P / (B : ℝ) ^ (n + 1) :=
  summable_of_abs_eval_div (P := fun _ => P) (gapPoly_eval_abs_summable P hB)

/-- `gapPolySeries` of a constant family is the sum of that series.

Source: `EndAPI.gapPolySeries`.
Contract: API
Audit: GREEN -/
theorem hasSum_gapPolySeries_const (P : ℝ[X]) {B : ℕ} (hB : 2 ≤ B) :
    HasSum (fun n : ℕ => eval (primeGap n : ℝ) P / (B : ℝ) ^ (n + 1))
      (gapPolySeries (fun _ => P) B) :=
  (gapPolySeries_const_summable P hB).hasSum

/-- A constant real polynomial series is the corresponding linear
combination of integer-power gap series.

Source: `Components.gapRatPolySeries_eq_linearCombination` (real analogue).
Contract: API
Audit: GREEN -/
theorem gapPolySeries_const_eq_linearCombination (P : ℝ[X]) {B : ℕ} (hB : 2 ≤ B) :
    gapPolySeries (fun _ => P) B =
      ∑ i ∈ range (P.natDegree + 1), P.coeff i * primeGapPowerSeries B i := by
  unfold gapPolySeries primeGapPowerSeries
  have hterm : ∀ n : ℕ,
      eval (primeGap n : ℝ) P / (B : ℝ) ^ (n + 1) =
        ∑ i ∈ range (P.natDegree + 1),
          P.coeff i * ((primeGap n : ℝ) ^ i / (B : ℝ) ^ (n + 1)) := by
    intro n
    rw [eval_eq_sum_range (primeGap n : ℝ), sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_div_assoc]
  simp_rw [hterm]
  have hf : ∀ i ∈ range (P.natDegree + 1),
      Summable fun n : ℕ =>
        P.coeff i * ((primeGap n : ℝ) ^ i / (B : ℝ) ^ (n + 1)) :=
    fun i _ => (primeGapPowerSeries_summable (B := B) (d := i) hB).mul_left _
  rw [Summable.tsum_finsetSum hf]
  refine sum_congr rfl fun i _ => ?_
  exact (primeGapPowerSeries_summable (B := B) (d := i) hB).tsum_mul_left _

/-! ### Uniformly bounded families -/

/-- Absolute summability for a family with uniformly bounded degree and
coefficient size.

Source: `PrimeSeries.primeGapPowerSeries_summable`.
Contract: API
Audit: GREEN -/
theorem gapPoly_eval_abs_summable_of_uniformBound
    {P : ℕ → ℝ[X]} {B D : ℕ} {M : ℝ} (hB : 2 ≤ B)
    (hD : ∀ n, (P n).natDegree ≤ D) (hM : ∀ n i, |(P n).coeff i| ≤ M) :
    Summable fun n : ℕ =>
      |eval (primeGap n : ℝ) (P n)| / (B : ℝ) ^ (n + 1) := by
  have hdom :
      Summable fun n : ℕ =>
        ∑ i ∈ range (D + 1),
          M * ((primeGap n : ℝ) ^ i / (B : ℝ) ^ (n + 1)) :=
    summable_sum fun i _ =>
      (primeGapPowerSeries_summable (B := B) (d := i) hB).mul_left M
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
    (fun n => ?_) hdom
  have h1 :=
    abs_eval_div_le_sum_monomial_of_natDegree_le (P := P n) (D := D) (B := B) (n := n)
      (hD n)
  refine h1.trans ?_
  refine sum_le_sum fun i _ => ?_
  have hpow :
      (0 : ℝ) ≤ (primeGap n : ℝ) ^ i / (B : ℝ) ^ (n + 1) :=
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _)
  exact mul_le_mul_of_nonneg_right (hM n i) hpow

/-- Signed summability under a uniform degree and coefficient bound, so
`gapPolySeries P B` is a genuine tsum.

Source: `EndAPI.gapPolySeries`.
Contract: API
Audit: GREEN -/
theorem gapPolySeries_summable_of_uniformBound
    {P : ℕ → ℝ[X]} {B D : ℕ} {M : ℝ} (hB : 2 ≤ B)
    (hD : ∀ n, (P n).natDegree ≤ D) (hM : ∀ n i, |(P n).coeff i| ≤ M) :
    Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1) :=
  summable_of_abs_eval_div
    (gapPoly_eval_abs_summable_of_uniformBound hB hD hM)

/-- `gapPolySeries` of a uniformly bounded family is the sum of that series.

Source: `EndAPI.gapPolySeries`.
Contract: API
Audit: GREEN -/
theorem hasSum_gapPolySeries_of_uniformBound
    {P : ℕ → ℝ[X]} {B D : ℕ} {M : ℝ} (hB : 2 ≤ B)
    (hD : ∀ n, (P n).natDegree ≤ D) (hM : ∀ n i, |(P n).coeff i| ≤ M) :
    HasSum (fun n : ℕ => eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
      (gapPolySeries P B) :=
  (gapPolySeries_summable_of_uniformBound hB hD hM).hasSum

/-! ### Periodic families -/

private theorem periodic_nsmul {α : Type*} {f : ℕ → α} {k : ℕ}
    (hf : Periodic f k) (x q : ℕ) : f (x + k * q) = f x := by
  induction q with
  | zero =>
    rw [mul_zero, add_zero]
  | succ q ih =>
    rw [Nat.mul_succ, ← add_assoc]
    exact (hf (x + k * q)).trans ih

private theorem periodic_mod {α : Type*} {f : ℕ → α} {k : ℕ}
    (hf : Periodic f k) (n : ℕ) : f n = f (n % k) := by
  have hn : n = n % k + k * (n / k) := by
    rw [Nat.add_comm, Nat.div_add_mod n k]
  rw [hn]
  refine Eq.trans (periodic_nsmul hf (n % k) (n / k)) ?_
  have hmod : (n % k + k * (n / k)) % k = n % k := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  rw [hmod]

/-- A `k`-periodic family is dominated by the finite sum of the residue
polynomials `P_0,…,P_{k-1}`, each of finite degree.

Source: `EndAPI.gapPolySeries` (periodicity as a hypothesis).
Contract: API
Audit: GREEN -/
theorem gapPoly_eval_abs_summable_periodic {P : ℕ → ℝ[X]} {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hP : Periodic P k) :
    Summable fun n : ℕ =>
      |eval (primeGap n : ℝ) (P n)| / (B : ℝ) ^ (n + 1) := by
  have hkpos : 0 < k := Nat.succ_le_iff.mp hk
  have hdom :
      Summable fun n : ℕ =>
        ∑ r ∈ range k,
          |eval (primeGap n : ℝ) (P r)| / (B : ℝ) ^ (n + 1) :=
    summable_sum fun r _ => gapPoly_eval_abs_summable (P r) hB
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
    (fun n => ?_) hdom
  have hmem : n % k ∈ range k := mem_range.mpr (Nat.mod_lt n hkpos)
  have hden : 0 ≤ (B : ℝ) ^ (n + 1) := pow_nonneg (Nat.cast_nonneg _) _
  have heq : P n = P (n % k) := periodic_mod hP n
  have hsingle :
      |eval (primeGap n : ℝ) (P n)| ≤
        ∑ r ∈ range k, |eval (primeGap n : ℝ) (P r)| := by
    rw [heq]
    exact single_le_sum
      (f := fun r : ℕ => |eval (primeGap n : ℝ) (P r)|)
      (fun r _ => (abs_nonneg (eval (primeGap n : ℝ) (P r)) : (0 : ℝ) ≤ _))
      hmem
  have hdiv := div_le_div_of_nonneg_right hsingle hden
  rwa [sum_div] at hdiv

/-- Periodic families yield a well-defined `gapPolySeries` tsum.

Source: `EndAPI.gapPolySeries`.
Contract: API
Audit: GREEN -/
theorem gapPolySeries_periodic_summable {P : ℕ → ℝ[X]} {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hP : Periodic P k) :
    Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1) :=
  summable_of_abs_eval_div (gapPoly_eval_abs_summable_periodic hB hk hP)

/-- `gapPolySeries` of a periodic family is the sum of that series.

Source: `EndAPI.gapPolySeries`.
Contract: API
Audit: GREEN -/
theorem hasSum_gapPolySeries_periodic {P : ℕ → ℝ[X]} {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hP : Periodic P k) :
    HasSum (fun n : ℕ => eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
      (gapPolySeries P B) :=
  (gapPolySeries_periodic_summable hB hk hP).hasSum

/-! ### Rational polynomials -/

/-- Coefficient-denominator product is a positive natural.

Source: `Components.ratPolyDenProd`.
Contract: API
Audit: GREEN -/
theorem ratPolyDenProd_pos (P : ℚ[X]) : 0 < ratPolyDenProd P := by
  unfold ratPolyDenProd
  exact prod_pos fun i _ => (P.coeff i).den_pos

/-- Clearing denominators bounds a rational polynomial evaluation by a
finite integer combination of monomials.

Source: `Components.eval_mapRatPoly_clearDenoms`.
Contract: API
Audit: GREEN -/
theorem abs_eval_mapRatPoly_clearDenoms (P : ℚ[X]) (x : ℝ) :
    (ratPolyDenProd P : ℝ) * |eval x (mapRatPoly P)| ≤
      ∑ i ∈ range (P.natDegree + 1),
        |(((P.coeff i).num *
            (∏ j ∈ (range (P.natDegree + 1)).erase i, (P.coeff j).den : ℕ) : ℤ) : ℝ)| *
          |x| ^ i := by
  have hs := eval_mapRatPoly_clearDenoms P x
  have hden0 : 0 ≤ (ratPolyDenProd P : ℝ) := Nat.cast_nonneg _
  have habs :
      |(ratPolyDenProd P : ℝ) * eval x (mapRatPoly P)| =
        (ratPolyDenProd P : ℝ) * |eval x (mapRatPoly P)| := by
    rw [abs_mul, abs_of_nonneg hden0]
  rw [← habs, hs]
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  refine sum_congr rfl fun i _ => ?_
  rw [abs_mul, abs_pow]

/-- Absolute summability of a fixed rational polynomial along prime
gaps, via `mapRatPoly` and the real monomial comparison. The
denominator identity `eval_mapRatPoly_clearDenoms` is recorded in
`abs_eval_mapRatPoly_clearDenoms`.

Source: `EndAPI.mapRatPoly`; `Components.eval_mapRatPoly_clearDenoms`.
Contract: API
Audit: GREEN -/
theorem gapRatPoly_eval_abs_summable (P : ℚ[X]) {B : ℕ} (hB : 2 ≤ B) :
    Summable fun n : ℕ =>
      |eval (primeGap n : ℝ) (mapRatPoly P)| / (B : ℝ) ^ (n + 1) :=
  gapPoly_eval_abs_summable (mapRatPoly P) hB

/-- The constant rational family is summable.

Source: `EndAPI.gapRatPolySeries`.
Contract: API
Audit: GREEN -/
theorem gapRatPolySeries_const_summable (P : ℚ[X]) {B : ℕ} (hB : 2 ≤ B) :
    Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (mapRatPoly P) / (B : ℝ) ^ (n + 1) :=
  gapPolySeries_const_summable (mapRatPoly P) hB

/-- `gapRatPolySeries` of a constant family is the sum of that series.

Source: `EndAPI.gapRatPolySeries`.
Contract: API
Audit: GREEN -/
theorem hasSum_gapRatPolySeries_const (P : ℚ[X]) {B : ℕ} (hB : 2 ≤ B) :
    HasSum (fun n : ℕ => eval (primeGap n : ℝ) (mapRatPoly P) / (B : ℝ) ^ (n + 1))
      (gapRatPolySeries (fun _ => P) B) :=
  (gapRatPolySeries_const_summable P hB).hasSum

/-- Unconditional form of `gapRatPolySeries_eq_linearCombination` for
`B ≥ 2`: every monomial gap series is summable.

Source: `Components.gapRatPolySeries_eq_linearCombination`;
`PrimeSeries.primeGapPowerSeries_summable`.
Contract: API
Audit: GREEN -/
theorem gapRatPolySeries_eq_linearCombination_of_two_le (P : ℚ[X]) {B : ℕ}
    (hB : 2 ≤ B) :
    gapRatPolySeries (fun _ => P) B =
      ∑ i ∈ range (P.natDegree + 1),
        (P.coeff i : ℝ) * primeGapPowerSeries B i :=
  gapRatPolySeries_eq_linearCombination P B fun i _ =>
    primeGapPowerSeries_summable (B := B) (d := i) hB

private theorem mapRatPoly_natDegree_le (P : ℚ[X]) :
    (mapRatPoly P).natDegree ≤ P.natDegree := by
  unfold mapRatPoly
  exact natDegree_map_le

/-- Absolute summability for a rational family with uniformly bounded
degree and coerced coefficient size.

Source: `EndAPI.mapRatPoly`.
Contract: API
Audit: GREEN -/
theorem gapRatPoly_eval_abs_summable_of_uniformBound
    {P : ℕ → ℚ[X]} {B D : ℕ} {M : ℝ} (hB : 2 ≤ B)
    (hD : ∀ n, (P n).natDegree ≤ D)
    (hM : ∀ n i, |((P n).coeff i : ℝ)| ≤ M) :
    Summable fun n : ℕ =>
      |eval (primeGap n : ℝ) (mapRatPoly (P n))| / (B : ℝ) ^ (n + 1) := by
  have hD' : ∀ n, (mapRatPoly (P n)).natDegree ≤ D := fun n =>
    (mapRatPoly_natDegree_le (P n)).trans (hD n)
  have hM' : ∀ n i, |(mapRatPoly (P n)).coeff i| ≤ M := fun n i => by
    rw [mapRatPoly_coeff]
    exact hM n i
  exact gapPoly_eval_abs_summable_of_uniformBound hB hD' hM'

/-- Signed summability for a uniformly bounded rational family.

Source: `EndAPI.gapRatPolySeries`.
Contract: API
Audit: GREEN -/
theorem gapRatPolySeries_summable_of_uniformBound
    {P : ℕ → ℚ[X]} {B D : ℕ} {M : ℝ} (hB : 2 ≤ B)
    (hD : ∀ n, (P n).natDegree ≤ D)
    (hM : ∀ n i, |((P n).coeff i : ℝ)| ≤ M) :
    Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (mapRatPoly (P n)) / (B : ℝ) ^ (n + 1) :=
  summable_of_abs_eval_div (P := fun n => mapRatPoly (P n))
    (gapRatPoly_eval_abs_summable_of_uniformBound hB hD hM)

/-- `gapRatPolySeries` of a uniformly bounded family is the sum of that
series.

Source: `EndAPI.gapRatPolySeries`.
Contract: API
Audit: GREEN -/
theorem hasSum_gapRatPolySeries_of_uniformBound
    {P : ℕ → ℚ[X]} {B D : ℕ} {M : ℝ} (hB : 2 ≤ B)
    (hD : ∀ n, (P n).natDegree ≤ D)
    (hM : ∀ n i, |((P n).coeff i : ℝ)| ≤ M) :
    HasSum
      (fun n : ℕ => eval (primeGap n : ℝ) (mapRatPoly (P n)) / (B : ℝ) ^ (n + 1))
      (gapRatPolySeries P B) :=
  (gapRatPolySeries_summable_of_uniformBound hB hD hM).hasSum

private theorem periodic_mapRatPoly {P : ℕ → ℚ[X]} {k : ℕ} (hP : Periodic P k) :
    Periodic (fun n => mapRatPoly (P n)) k :=
  fun n => congrArg mapRatPoly (hP n)

/-- Absolute summability of a periodic rational family, via `mapRatPoly`.

Source: `EndAPI.mapRatPoly`; `EndAPI.gapRatPolySeries`.
Contract: API
Audit: GREEN -/
theorem gapRatPoly_eval_abs_summable_periodic {P : ℕ → ℚ[X]} {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hP : Periodic P k) :
    Summable fun n : ℕ =>
      |eval (primeGap n : ℝ) (mapRatPoly (P n))| / (B : ℝ) ^ (n + 1) :=
  gapPoly_eval_abs_summable_periodic hB hk (periodic_mapRatPoly hP)

/-- Periodic rational families yield a well-defined `gapRatPolySeries`
tsum.

Source: `EndAPI.gapRatPolySeries`.
Contract: API
Audit: GREEN -/
theorem gapRatPolySeries_periodic_summable {P : ℕ → ℚ[X]} {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hP : Periodic P k) :
    Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (mapRatPoly (P n)) / (B : ℝ) ^ (n + 1) :=
  gapPolySeries_periodic_summable hB hk (periodic_mapRatPoly hP)

/-- `gapRatPolySeries` of a periodic family is the sum of that series.

Source: `EndAPI.gapRatPolySeries`.
Contract: API
Audit: GREEN -/
theorem hasSum_gapRatPolySeries_periodic {P : ℕ → ℚ[X]} {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hP : Periodic P k) :
    HasSum
      (fun n : ℕ => eval (primeGap n : ℝ) (mapRatPoly (P n)) / (B : ℝ) ^ (n + 1))
      (gapRatPolySeries P B) :=
  (gapRatPolySeries_periodic_summable hB hk hP).hasSum

end PrimeGapNormality.Prime
