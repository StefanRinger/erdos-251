import PrimeGapNormality.Prime.EndAPI
import PrimeGapNormality.Prime.GapAbel
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prime position and gap-power series: summability and infinite Abel

Polynomial Chebyshev inversion `nthPrime n ≤ 144 * (n+1)^2` for all `n`
gives geometric summability in every base `B ≥ 2` (exponential `2^n`
bounds are useless at `B = 2`). Infinite Abel for the degree-1 gap
series is the `N → ∞` limit of `finite_gap_abel` with constant
position weights `c ≡ 1`, inverted to period-`1` Abel weights
`d ≡ 1/(B-1)`.

Indexing: Lean `nthPrime 0 = 2` is paper `p_1`. GapAbel `a 1` is
`nthPrime 0`; the finite identity is applied to
`a t = nthPrime (t-1)` so `a(i+1) = nthPrime i`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` §§1–2; EndAPI series
signatures; `GapAbel.finite_gap_abel`; Mathlib `Chebyshev.pi_ge`;
geometric comparison as in BFree `Series` (technique only).
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Filter Function
open scoped Topology

set_option maxHeartbeats 800000

/-! ### Base lemmas -/

private theorem one_lt_cast_of_two_le {B : ℕ} (hB : 2 ≤ B) : (1 : ℝ) < B := by
  have : (2 : ℝ) ≤ B := Nat.cast_le.mpr hB
  linarith

private theorem base_cast_pos {B : ℕ} (hB : 2 ≤ B) : (0 : ℝ) < B :=
  lt_trans (by norm_num) (one_lt_cast_of_two_le hB)

private theorem base_cast_ne_zero {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) ≠ 0 :=
  (base_cast_pos hB).ne'

private theorem base_sub_one_ne_zero {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) - 1 ≠ 0 :=
  sub_ne_zero.mpr (one_lt_cast_of_two_le hB).ne'

private theorem inv_base_norm_lt_one {B : ℕ} (hB : 2 ≤ B) : ‖((B : ℝ)⁻¹)‖ < 1 := by
  have hB1 := one_lt_cast_of_two_le hB
  rw [norm_inv, Real.norm_eq_abs, abs_of_pos (base_cast_pos hB)]
  exact inv_lt_one_of_one_lt₀ hB1

private theorem log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by positivity : (0 : ℝ) < 2)
  have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by
    rw [one_div]
  rw [hinv] at h
  linarith

private theorem log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_rpow_div hx (by positivity : (0 : ℝ) < 1 / 2)
  have hrpow : x ^ ((1 : ℝ) / 2) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  have hrew : x ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) = 2 * Real.sqrt x := by
    rw [hrpow, div_eq_mul_inv]
    have : ((1 : ℝ) / 2)⁻¹ = (2 : ℝ) := by norm_num
    rw [this, mul_comm]
  exact h.trans_eq hrew

/-- Geometric comparison: `C * m / B^(n+1) = (C/B) * (m * B⁻¹^n)`. -/
private theorem scaled_geom (C : ℝ) {B : ℕ} (hB : 2 ≤ B) (n : ℕ) (m : ℝ) :
    C * m / (B : ℝ) ^ (n + 1) = (C / B) * (m * (B : ℝ)⁻¹ ^ n) := by
  have hb0 := base_cast_ne_zero hB
  rw [pow_succ, div_mul_eq_div_div, div_eq_mul_inv, inv_pow]
  field_simp [hb0]

/-- `n ↦ (n+a)^k * B⁻ⁿ` is summable for `B ≥ 2`. -/
private theorem summable_nat_add_pow_geometric {B k a : ℕ} (hB : 2 ≤ B) :
    Summable fun n : ℕ => ((n + a : ℕ) : ℝ) ^ k * (B : ℝ)⁻¹ ^ n := by
  have hr := inv_base_norm_lt_one hB
  have hpow := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hr
  have hshift :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ k * (B : ℝ)⁻¹ ^ n) a).2 hpow
  refine (hshift.mul_left ((B : ℝ) ^ a)).congr fun n => ?_
  have hb0 := base_cast_ne_zero hB
  have hpow_a : (B : ℝ) ^ a * (B : ℝ)⁻¹ ^ a = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hb0, one_pow]
  have hn : ((n + a : ℕ) : ℝ) = (n : ℝ) + a := by simp
  rw [hn]
  calc
    (B : ℝ) ^ a * (((n : ℝ) + a) ^ k * (B : ℝ)⁻¹ ^ (n + a))
        = ((n : ℝ) + a) ^ k * ((B : ℝ) ^ a * (B : ℝ)⁻¹ ^ (n + a)) := by ring
    _ = ((n : ℝ) + a) ^ k * ((B : ℝ) ^ a * ((B : ℝ)⁻¹ ^ n * (B : ℝ)⁻¹ ^ a)) := by
          rw [pow_add]
    _ = ((n : ℝ) + a) ^ k * ((B : ℝ)⁻¹ ^ n * ((B : ℝ) ^ a * (B : ℝ)⁻¹ ^ a)) := by ring
    _ = ((n : ℝ) + a) ^ k * ((B : ℝ)⁻¹ ^ n * 1) := by rw [hpow_a]
    _ = ((n : ℝ) + a) ^ k * (B : ℝ)⁻¹ ^ n := by ring

/-! ### Prime enumeration -/

theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem nthPrime_mono : Monotone nthPrime :=
  nthPrime_strictMono.monotone

theorem nthPrime_zero : nthPrime 0 = 2 :=
  Nat.nth_prime_zero_eq_two

theorem nthPrime_ge_add_two (n : ℕ) : n + 2 ≤ nthPrime n :=
  Nat.add_two_le_nth_prime n

theorem primeGap_le_nthPrime_succ (n : ℕ) : primeGap n ≤ nthPrime (n + 1) :=
  Nat.sub_le _ _

theorem primeGap_cast (n : ℕ) :
    (primeGap n : ℝ) = (nthPrime (n + 1) : ℝ) - nthPrime n := by
  have hle : nthPrime n ≤ nthPrime (n + 1) := nthPrime_mono (Nat.le_succ n)
  rw [primeGap, Nat.cast_sub hle]

theorem pos_term_nonneg (B n : ℕ) :
    0 ≤ (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) :=
  div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

theorem gap_term_nonneg (B d n : ℕ) :
    0 ≤ (primeGap n : ℝ) ^ d / (B : ℝ) ^ (n + 1) :=
  div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _)

/-- Galois inversion: `nthPrime n ≤ x ↔ n+1 ≤ π(x)`. -/
theorem nthPrime_le_iff_succ_le_pi (n x : ℕ) :
    nthPrime n ≤ x ↔ n + 1 ≤ Nat.primeCounting x := by
  have hiff :=
    Nat.lt_nth_iff_count_lt (p := Nat.Prime) Nat.infinite_setOfPred_prime
      (a := n) (b := x + 1)
  constructor
  · intro h
    exact Nat.succ_le_iff.mpr (hiff.mpr (Nat.lt_succ_of_le h))
  · intro h
    exact Nat.le_of_lt_succ (hiff.mp (Nat.succ_le_iff.mp h))

/-! ### Polynomial Chebyshev bound -/

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num

private theorem sqrt_144 : Real.sqrt 144 = 12 := by
  rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num

/-- Chebyshev `π` lower bound inverted: `p_n ≤ 144 (n+1)^2` for every `n`. -/
theorem nthPrime_le_succ_sq (n : ℕ) :
    nthPrime n ≤ 144 * (n + 1) ^ 2 := by
  set m := 144 * (n + 1) ^ 2
  have hm1 : 1 < m := by
    have hsq : 0 < (n + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos n)
    have : 1 ≤ (n + 1) ^ 2 := Nat.succ_le_of_lt hsq
    have : 144 ≤ 144 * (n + 1) ^ 2 := Nat.mul_le_mul_left 144 this
    omega
  rw [nthPrime_le_iff_succ_le_pi]
  have hπ := Chebyshev.pi_ge m
  have hmR : (m : ℝ) = 144 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    simp [m, Nat.cast_mul, Nat.cast_pow]
  let t : ℝ := (n + 1 : ℕ)
  have ht0 : 0 ≤ t := by positivity
  have ht1 : (1 : ℝ) ≤ t := by
    have hn : (1 : ℕ) ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hcast : ((1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hn
    simpa [t] using hcast
  have ht_sq : t ≤ t ^ 2 := by
    have hmul : 0 ≤ t * (t - 1) := mul_nonneg ht0 (sub_nonneg.mpr ht1)
    have : t * (t - 1) = t ^ 2 - t := by ring
    rw [this] at hmul
    linarith
  have hmR_def : (m : ℝ) = 144 * t ^ 2 := by
    simpa [t] using hmR
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hlogm_pos : 0 < Real.log m :=
    Real.log_pos (Nat.one_lt_cast.mpr hm1)
  have hsqrt : Real.sqrt (m : ℝ) = 12 * t := by
    rw [hmR_def, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 144) (t ^ 2),
      sqrt_144, Real.sqrt_sq ht0]
  have hm144 : (144 : ℝ) ≤ m := by
    have htsq1 : (1 : ℝ) ≤ t ^ 2 := le_trans ht1 ht_sq
    have := mul_le_mul_of_nonneg_left htsq1 (by positivity : (0 : ℝ) ≤ 144)
    simpa [hmR_def] using this
  have h4 : (m : ℝ) + 1 ≤ 4 * m := by
    have : (1 : ℝ) ≤ 3 * m := by linarith
    linarith
  have hsqrt_succ : Real.sqrt ((m : ℝ) + 1) ≤ 2 * Real.sqrt (m : ℝ) := by
    have hsq := Real.sqrt_le_sqrt h4
    have h4s : Real.sqrt (4 * (m : ℝ)) = 2 * Real.sqrt (m : ℝ) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4) (m : ℝ), sqrt_four]
    exact hsq.trans_eq h4s
  have hLHS :
      t * Real.log m + Real.log ((m : ℝ) + 1)
        ≤ (m : ℝ) * Real.log 2 := by
    have h1 : t * Real.log m ≤ t * (2 * Real.sqrt (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (log_le_two_sqrt hm0) ht0
    have h2 : Real.log ((m : ℝ) + 1) ≤ 2 * Real.sqrt ((m : ℝ) + 1) :=
      log_le_two_sqrt (add_nonneg hm0 zero_le_one)
    have hsum :
        t * Real.log m + Real.log ((m : ℝ) + 1)
          ≤ t * (2 * Real.sqrt (m : ℝ)) + 2 * Real.sqrt ((m : ℝ) + 1) :=
      add_le_add h1 h2
    have hA : t * (2 * Real.sqrt (m : ℝ)) = 24 * t ^ 2 := by
      rw [hsqrt]
      ring
    have hBnd : 2 * Real.sqrt ((m : ℝ) + 1) ≤ 48 * t := by
      have := mul_le_mul_of_nonneg_left hsqrt_succ (by positivity : (0 : ℝ) ≤ 2)
      have : 2 * (2 * Real.sqrt (m : ℝ)) = 4 * Real.sqrt (m : ℝ) := by ring
      have h4s : 4 * Real.sqrt (m : ℝ) = 48 * t := by
        rw [hsqrt]
        ring
      linarith
    have hpoly : 24 * t ^ 2 + 48 * t ≤ 72 * t ^ 2 := by
      have : 48 * t ≤ 48 * t ^ 2 :=
        mul_le_mul_of_nonneg_left ht_sq (by positivity : (0 : ℝ) ≤ 48)
      linarith
    have hhalf : 72 * t ^ 2 = (m : ℝ) / 2 := by
      rw [hmR_def]
      ring
    have hlog2 : (m : ℝ) / 2 ≤ (m : ℝ) * Real.log 2 := by
      have : (m : ℝ) * (1 / 2) ≤ (m : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left log_two_ge_half hm0
      have hdiv : (m : ℝ) / 2 = (m : ℝ) * (1 / 2) := by ring
      rwa [hdiv]
    refine hsum.trans ?_
    rw [hA]
    have : 24 * t ^ 2 + 2 * Real.sqrt ((m : ℝ) + 1) ≤ 24 * t ^ 2 + 48 * t := by
      linarith [hBnd]
    exact this.trans (hpoly.trans_eq hhalf |>.trans hlog2)
  have hnum : t * Real.log m ≤ (m : ℝ) * Real.log 2 - Real.log ((m : ℝ) + 1) := by
    linarith [hLHS]
  have hdiv : t ≤ ((m : ℝ) * Real.log 2 - Real.log ((m : ℝ) + 1)) / Real.log m :=
    (le_div_iff₀ hlogm_pos).mpr hnum
  have hleπ : t ≤ (Nat.primeCounting m : ℝ) := hdiv.trans hπ
  exact Nat.cast_le.mp (by simpa [t] using hleπ)

/-! ### Summability of the position series -/

theorem primePosSeries_summable {B : ℕ} (hB : 2 ≤ B) :
    Summable fun n : ℕ => (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) := by
  have hdom :
      Summable fun n : ℕ =>
        ((144 : ℝ) / B) * (((n + 1 : ℕ) : ℝ) ^ 2 * (B : ℝ)⁻¹ ^ n) :=
    (summable_nat_add_pow_geometric (B := B) (k := 2) (a := 1) hB).mul_left
      ((144 : ℝ) / B)
  refine Summable.of_nonneg_of_le (fun n => pos_term_nonneg B n) (fun n => ?_) hdom
  have hbound : (nthPrime n : ℝ) ≤ 144 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := nthPrime_le_succ_sq n
    have hcast : ((144 * (n + 1) ^ 2 : ℕ) : ℝ) = 144 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
      simp [Nat.cast_mul, Nat.cast_pow]
    exact (Nat.cast_le.mpr this).trans_eq hcast
  have hle :
      (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) ≤
        144 * ((n + 1 : ℕ) : ℝ) ^ 2 / (B : ℝ) ^ (n + 1) :=
    div_le_div_of_nonneg_right hbound (pow_nonneg (Nat.cast_nonneg _) _)
  exact hle.trans_eq (scaled_geom 144 hB n (((n + 1 : ℕ) : ℝ) ^ 2))

/-! ### Gap-power summability -/

theorem primeGap_pow_le (n d : ℕ) :
    (primeGap n : ℝ) ^ d ≤ (144 * ((n + 2 : ℕ) : ℝ) ^ 2) ^ d := by
  have h0 : (0 : ℝ) ≤ primeGap n := Nat.cast_nonneg _
  have hgap : (primeGap n : ℝ) ≤ nthPrime (n + 1) := by
    exact_mod_cast primeGap_le_nthPrime_succ n
  have hnth : (nthPrime (n + 1) : ℝ) ≤ 144 * ((n + 2 : ℕ) : ℝ) ^ 2 := by
    have := nthPrime_le_succ_sq (n + 1)
    have hidx : n + 1 + 1 = n + 2 := by omega
    rw [hidx] at this
    have hcast : ((144 * (n + 2) ^ 2 : ℕ) : ℝ) = 144 * ((n + 2 : ℕ) : ℝ) ^ 2 := by
      simp [Nat.cast_mul, Nat.cast_pow]
    exact (Nat.cast_le.mpr this).trans_eq hcast
  exact pow_le_pow_left₀ h0 (hgap.trans hnth) d

theorem primeGapPowerSeries_summable {B d : ℕ} (hB : 2 ≤ B) :
    Summable fun n : ℕ => (primeGap n : ℝ) ^ d / (B : ℝ) ^ (n + 1) := by
  have hdom :
      Summable fun n : ℕ =>
        (((144 : ℝ) ^ d) / B) * (((n + 2 : ℕ) : ℝ) ^ (2 * d) * (B : ℝ)⁻¹ ^ n) :=
    (summable_nat_add_pow_geometric (B := B) (k := 2 * d) (a := 2) hB).mul_left
      (((144 : ℝ) ^ d) / B)
  refine Summable.of_nonneg_of_le (fun n => gap_term_nonneg B d n) (fun n => ?_) hdom
  have hpow :
      (144 * ((n + 2 : ℕ) : ℝ) ^ 2) ^ d =
        (144 : ℝ) ^ d * ((n + 2 : ℕ) : ℝ) ^ (2 * d) := by
    rw [mul_pow, ← pow_mul]
  have hle :
      (primeGap n : ℝ) ^ d / (B : ℝ) ^ (n + 1) ≤
        (144 : ℝ) ^ d * ((n + 2 : ℕ) : ℝ) ^ (2 * d) / (B : ℝ) ^ (n + 1) := by
    have := primeGap_pow_le n d
    rw [hpow] at this
    exact div_le_div_of_nonneg_right this (pow_nonneg (Nat.cast_nonneg _) _)
  have hsc := scaled_geom ((144 : ℝ) ^ d) hB n (((n + 2 : ℕ) : ℝ) ^ (2 * d))
  exact hle.trans_eq hsc

/-! ### Terminal vanishing -/

private theorem tendsto_succ_sq_div_pow {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 / (B : ℝ) ^ n) atTop (𝓝 0) := by
  have hB1 := one_lt_cast_of_two_le hB
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt (k := 2) hB1
  have hshift := h2.comp (tendsto_add_atTop_nat 1)
  have hb0 := base_cast_ne_zero hB
  have hfun :
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 / (B : ℝ) ^ n) =
        fun n : ℕ => (B : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2 / (B : ℝ) ^ (n + 1)) := by
    funext n
    have hp : (B : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero (n + 1) hb0
    have hp' : (B : ℝ) ^ n ≠ 0 := pow_ne_zero n hb0
    rw [pow_succ]
    field_simp [hb0, hp, hp']
    ring
  rw [hfun]
  have hshift' :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 / (B : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    change Tendsto ((fun n : ℕ => (n : ℝ) ^ 2 / (B : ℝ) ^ n) ∘ fun n => n + 1)
      atTop (𝓝 0)
    exact hshift
  simpa using hshift'.const_mul (B : ℝ)

/-- Polynomial over exponential: `p_N / B^N → 0`. -/
theorem tendsto_nthPrime_div_pow {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N : ℕ => (nthPrime N : ℝ) / (B : ℝ) ^ N) atTop (𝓝 0) := by
  have hle : ∀ N,
      (nthPrime N : ℝ) / (B : ℝ) ^ N ≤
        144 * (((N + 1 : ℕ) : ℝ) ^ 2 / (B : ℝ) ^ N) := by
    intro N
    have hbound : (nthPrime N : ℝ) ≤ 144 * ((N + 1 : ℕ) : ℝ) ^ 2 := by
      have := nthPrime_le_succ_sq N
      have hcast : ((144 * (N + 1) ^ 2 : ℕ) : ℝ) = 144 * ((N + 1 : ℕ) : ℝ) ^ 2 := by
        simp [Nat.cast_mul, Nat.cast_pow]
      exact (Nat.cast_le.mpr this).trans_eq hcast
    have hden : 0 ≤ (B : ℝ) ^ N := pow_nonneg (Nat.cast_nonneg _) _
    have := div_le_div_of_nonneg_right hbound hden
    simpa [mul_div_assoc] using this
  have hmul :
      Tendsto (fun N : ℕ => 144 * (((N + 1 : ℕ) : ℝ) ^ 2 / (B : ℝ) ^ N)) atTop (𝓝 0) := by
    simpa using (tendsto_succ_sq_div_pow hB).const_mul (144 : ℝ)
  refine squeeze_zero (fun N => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
    hle hmul

theorem tendsto_nthPrime_div_pow_succ {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N : ℕ => (nthPrime N : ℝ) / (B : ℝ) ^ (N + 1)) atTop (𝓝 0) := by
  have hb0 := base_cast_ne_zero hB
  have hfun :
      (fun N : ℕ => (nthPrime N : ℝ) / (B : ℝ) ^ (N + 1)) =
        fun N => ((nthPrime N : ℝ) / (B : ℝ) ^ N) / B := by
    funext N
    rw [pow_succ, div_div]
  rw [hfun]
  simpa using (tendsto_nthPrime_div_pow hB).div_const (B : ℝ)

/-! ### Constant Abel weights (period 1, `c ≡ 1`) -/

theorem periodicGapWeight_const_one (B j : ℕ) :
    periodicGapWeight (fun _ => (1 : ℝ)) B 1 j = 1 / ((B : ℝ) - 1) := by
  unfold periodicGapWeight
  rw [sum_range_one]
  simp [pow_zero, pow_one]

theorem recGapWeight_const_one {B j : ℕ} (hB : 2 ≤ B) :
    recGapWeight B (periodicGapWeight (fun _ => (1 : ℝ)) B 1) j = 1 :=
  periodicGapWeight_rec hB (by omega : 1 ≤ 1) (fun _ => (1 : ℝ)) (fun _ => rfl)

/-! ### Finite Abel for prime positions -/

/-- Finite Abel for `nthPrime`, matching `finite_gap_abel` with
`a t = nthPrime (t-1)` and constant `c ≡ 1`. Lean `i ∈ range N` is
paper `n = i+1`. Terminal index `a N = nthPrime (N-1)`. -/
theorem finite_primePos_abel {B N : ℕ} (hB : 2 ≤ B) (hN : 1 ≤ N) :
    ∑ i ∈ range N, (nthPrime i : ℝ) / (B : ℝ) ^ (i + 1) =
      (nthPrime 0 : ℝ) * periodicGapWeight (fun _ => (1 : ℝ)) B 1 0 +
        ∑ i ∈ range (N - 1),
          periodicGapWeight (fun _ => (1 : ℝ)) B 1 (i + 1) *
            (primeGap i : ℝ) / (B : ℝ) ^ (i + 1) -
        (nthPrime (N - 1) : ℝ) * periodicGapWeight (fun _ => (1 : ℝ)) B 1 N /
          (B : ℝ) ^ N := by
  let a : ℕ → ℝ := fun t => (nthPrime (t - 1) : ℝ)
  let d : ℕ → ℝ := periodicGapWeight (fun _ => (1 : ℝ)) B 1
  have habel := finite_gap_abel (B := B) (a := a) (d := d) hB hN
  have hLHS :
      ∑ i ∈ range N, recGapWeight B d i * a (i + 1) / (B : ℝ) ^ (i + 1) =
        ∑ i ∈ range N, (nthPrime i : ℝ) / (B : ℝ) ^ (i + 1) := by
    refine sum_congr rfl fun i _ => ?_
    rw [recGapWeight_const_one hB, one_mul]
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
    have hg : a (i + 2) - a (i + 1) = primeGap i := by
      simp [a, hi1, hi0, primeGap_cast]
    rw [hg]
  have ha1 : a 1 = nthPrime 0 := by simp [a]
  have haN : a N = nthPrime (N - 1) := rfl
  rw [hLHS] at habel
  simpa [d, ha1, haN, hRHS_gap] using habel

/-! ### Infinite Abel -/

private theorem tendsto_abel_remainder {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun n : ℕ =>
        (nthPrime n : ℝ) * periodicGapWeight (fun _ => (1 : ℝ)) B 1 (n + 1) /
          (B : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
  have hfun :
      (fun n : ℕ =>
          (nthPrime n : ℝ) * periodicGapWeight (fun _ => (1 : ℝ)) B 1 (n + 1) /
            (B : ℝ) ^ (n + 1)) =
        fun n =>
          (1 / ((B : ℝ) - 1)) * ((nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)) := by
    funext n
    rw [periodicGapWeight_const_one]
    ring
  rw [hfun]
  simpa using (tendsto_nthPrime_div_pow_succ hB).const_mul (1 / ((B : ℝ) - 1))

/-- Infinite Abel for the prime position series: constant position
weights invert to period-`1` gap weights `d ≡ 1/(B-1)`.

Exact identity:
`∑' n, p_n B^{-(n+1)}
  = p_0 · d_0 + ∑' n, d_{n+1} g_n B^{-(n+1)}`
with `d = periodicGapWeight (fun _ => 1) B 1`. -/
theorem primePosSeries_eq_gapAbel {B : ℕ} (hB : 2 ≤ B) :
    primePosSeries B =
      (nthPrime 0 : ℝ) * periodicGapWeight (fun _ => (1 : ℝ)) B 1 0 +
        ∑' n : ℕ,
          periodicGapWeight (fun _ => (1 : ℝ)) B 1 (n + 1) *
            (primeGap n : ℝ) / (B : ℝ) ^ (n + 1) := by
  have hpos := primePosSeries_summable hB
  have hgap1 := primeGapPowerSeries_summable (B := B) (d := 1) hB
  let d : ℕ → ℝ := periodicGapWeight (fun _ => (1 : ℝ)) B 1
  let f : ℕ → ℝ := fun n => (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)
  let g : ℕ → ℝ := fun n => d (n + 1) * (primeGap n : ℝ) / (B : ℝ) ^ (n + 1)
  have hg : Summable g := by
    have hfun : g = fun n => (1 / ((B : ℝ) - 1)) * ((primeGap n : ℝ) / (B : ℝ) ^ (n + 1)) := by
      funext n
      simp only [g, d, periodicGapWeight_const_one]
      ring
    rw [hfun]
    simpa using hgap1.mul_left (1 / ((B : ℝ) - 1))
  have hfin (n : ℕ) :
      ∑ i ∈ range (n + 1), f i =
        (nthPrime 0 : ℝ) * d 0 + ∑ i ∈ range n, g i -
          (nthPrime n : ℝ) * d (n + 1) / (B : ℝ) ^ (n + 1) := by
    simpa [f, g, d, Nat.add_sub_cancel] using
      finite_primePos_abel (B := B) (N := n + 1) hB (Nat.succ_le_succ (Nat.zero_le n))
  have hST : Tendsto (fun n : ℕ => ∑ i ∈ range (n + 1), f i) atTop (𝓝 (∑' n, f n)) :=
    hpos.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hGT : Tendsto (fun n : ℕ => ∑ i ∈ range n, g i) atTop (𝓝 (∑' n, g n)) :=
    hg.hasSum.tendsto_sum_nat
  have hRT := tendsto_abel_remainder hB
  have htarget :
      Tendsto (fun n : ℕ =>
        (nthPrime 0 : ℝ) * d 0 + ∑ i ∈ range n, g i -
          (nthPrime n : ℝ) * d (n + 1) / (B : ℝ) ^ (n + 1)) atTop
        (𝓝 ((nthPrime 0 : ℝ) * d 0 + ∑' n, g n)) := by
    have hadd := tendsto_const_nhds (x := (nthPrime 0 : ℝ) * d 0) |>.add hGT
    simpa using hadd.sub hRT
  have hS' :
      Tendsto (fun n : ℕ => ∑ i ∈ range (n + 1), f i) atTop
        (𝓝 ((nthPrime 0 : ℝ) * d 0 + ∑' n, g n)) :=
    htarget.congr fun n => (hfin n).symm
  have huniq := tendsto_nhds_unique hST hS'
  simpa [primePosSeries, f, g, d] using huniq

/-- Degree-1 gap corollary: `∑ g_n B^{-(n+1)} = (B-1) ∑ p_n B^{-(n+1)} - p_0`. -/
theorem primeGapPowerSeries_one_eq {B : ℕ} (hB : 2 ≤ B) :
    primeGapPowerSeries B 1 =
      ((B : ℝ) - 1) * primePosSeries B - nthPrime 0 := by
  have habel := primePosSeries_eq_gapAbel hB
  have hd0 : periodicGapWeight (fun _ => (1 : ℝ)) B 1 0 = 1 / ((B : ℝ) - 1) :=
    periodicGapWeight_const_one B 0
  have hdw :
      (fun n : ℕ =>
          periodicGapWeight (fun _ => (1 : ℝ)) B 1 (n + 1) *
            (primeGap n : ℝ) / (B : ℝ) ^ (n + 1)) =
        fun n => (1 / ((B : ℝ) - 1)) * ((primeGap n : ℝ) ^ 1 / (B : ℝ) ^ (n + 1)) := by
    funext n
    rw [periodicGapWeight_const_one, pow_one]
    ring
  have hsum := primeGapPowerSeries_summable (B := B) (d := 1) hB
  have htsum :
      ∑' n : ℕ,
          periodicGapWeight (fun _ => (1 : ℝ)) B 1 (n + 1) *
            (primeGap n : ℝ) / (B : ℝ) ^ (n + 1) =
        (1 / ((B : ℝ) - 1)) * primeGapPowerSeries B 1 := by
    rw [hdw, tsum_mul_left]
    rfl
  have hden := base_sub_one_ne_zero hB
  have hform :
      primePosSeries B =
        (nthPrime 0 : ℝ) * (1 / ((B : ℝ) - 1)) +
          (1 / ((B : ℝ) - 1)) * primeGapPowerSeries B 1 := by
    rw [habel, hd0, htsum]
  have hmul := congrArg (fun x => ((B : ℝ) - 1) * x) hform
  have hcancel :
      ((B : ℝ) - 1) *
          ((nthPrime 0 : ℝ) * (1 / ((B : ℝ) - 1)) +
            (1 / ((B : ℝ) - 1)) * primeGapPowerSeries B 1) =
        (nthPrime 0 : ℝ) + primeGapPowerSeries B 1 := by
    field_simp [hden]
  have hmul' :
      ((B : ℝ) - 1) * primePosSeries B =
        (nthPrime 0 : ℝ) + primeGapPowerSeries B 1 := by
    rw [← hcancel]
    exact hmul
  linarith

/-! ### Residue gap-power tails `gapPowerTheta` -/

private theorem two_le_base_pow {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) : 2 ≤ B ^ k := by
  have hB1 : 1 ≤ B := le_trans (by omega : 1 ≤ 2) hB
  have hpow : B ≤ B ^ k := le_self_pow hB1 (by omega)
  exact le_trans hB hpow

private theorem theta_index_le (n k r m : ℕ) :
    n + k * m + r + 2 ≤ (n + r + k + 2) * (m + 1) := by
  have h1 : n + r + 2 ≤ n + r + k + 2 := by omega
  have h2 : k ≤ n + r + k + 2 := by omega
  have h2m : k * m ≤ (n + r + k + 2) * m := Nat.mul_le_mul_right m h2
  have hsum : n + r + 2 + k * m ≤ n + r + k + 2 + (n + r + k + 2) * m :=
    Nat.add_le_add h1 h2m
  have hL : n + k * m + r + 2 = n + r + 2 + k * m := by ring
  have hR : (n + r + k + 2) * (m + 1) = n + r + k + 2 + (n + r + k + 2) * m := by
    rw [Nat.mul_add_one]
    ring
  rw [hL, hR]
  exact hsum

theorem gapPowerTheta_summable {B k r d n : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) :
    Summable fun m : ℕ =>
      (primeGap (n + k * m + r) : ℝ) ^ d / (B : ℝ) ^ (k * (m + 1)) := by
  have hBk : 2 ≤ B ^ k := two_le_base_pow hB hk
  let Cnat : ℕ := n + r + k + 2
  let C : ℝ := Cnat
  have hdom :
      Summable fun m : ℕ =>
        ((144 : ℝ) ^ d * C ^ (2 * d) / (B ^ k : ℕ)) *
          (((m + 1 : ℕ) : ℝ) ^ (2 * d) * ((B ^ k : ℕ) : ℝ)⁻¹ ^ m) :=
    (summable_nat_add_pow_geometric (B := B ^ k) (k := 2 * d) (a := 1) hBk).mul_left
      ((144 : ℝ) ^ d * C ^ (2 * d) / (B ^ k : ℕ))
  refine Summable.of_nonneg_of_le (fun m =>
      div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _))
    (fun m => ?_) hdom
  have hidx : n + k * m + r + 2 ≤ Cnat * (m + 1) := by
    simpa [Cnat] using theta_index_le n k r m
  have hidxR : ((n + k * m + r + 2 : ℕ) : ℝ) ≤ C * ((m + 1 : ℕ) : ℝ) := by
    have hcast : ((Cnat * (m + 1) : ℕ) : ℝ) = C * ((m + 1 : ℕ) : ℝ) := by
      simp [C, Cnat, Nat.cast_mul]
    exact (Nat.cast_le.mpr hidx).trans_eq hcast
  have hnth : (primeGap (n + k * m + r) : ℝ) ^ d ≤
      (144 * ((n + k * m + r + 2 : ℕ) : ℝ) ^ 2) ^ d :=
    primeGap_pow_le (n + k * m + r) d
  have hsq : ((n + k * m + r + 2 : ℕ) : ℝ) ^ 2 ≤ (C * ((m + 1 : ℕ) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hidxR 2
  have h144 :
      (144 * ((n + k * m + r + 2 : ℕ) : ℝ) ^ 2) ^ d ≤
        (144 * (C * ((m + 1 : ℕ) : ℝ)) ^ 2) ^ d :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hsq (by positivity)) d
  have hexp : (144 * (C * ((m + 1 : ℕ) : ℝ)) ^ 2) ^ d =
      (144 : ℝ) ^ d * C ^ (2 * d) * ((m + 1 : ℕ) : ℝ) ^ (2 * d) := by
    rw [mul_pow, ← pow_mul, mul_pow, mul_assoc]
  have hnum := (hnth.trans h144).trans_eq hexp
  have hden : (B : ℝ) ^ (k * (m + 1)) = ((B ^ k : ℕ) : ℝ) ^ (m + 1) := by
    rw [Nat.cast_pow, pow_mul]
  have hle :
      (primeGap (n + k * m + r) : ℝ) ^ d / (B : ℝ) ^ (k * (m + 1)) ≤
        (144 : ℝ) ^ d * C ^ (2 * d) * ((m + 1 : ℕ) : ℝ) ^ (2 * d) /
          ((B ^ k : ℕ) : ℝ) ^ (m + 1) := by
    rw [hden]
    exact div_le_div_of_nonneg_right hnum (pow_nonneg (Nat.cast_nonneg _) _)
  have hsc :=
    scaled_geom ((144 : ℝ) ^ d * C ^ (2 * d)) hBk m (((m + 1 : ℕ) : ℝ) ^ (2 * d))
  exact hle.trans_eq hsc

/-- Paper recurrence for residue tails: shifting the start index by the
period `k` peels off the `m = 0` gap power. True identity, Lean 0-based
`r` and `n`. Requires `1 ≤ k` so the geometric ratio `B^{-k}` is `< 1`. -/
theorem gapPowerTheta_add_k {B k r d n : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) :
    gapPowerTheta B k r d (n + k) =
      (B : ℝ) ^ k * gapPowerTheta B k r d n - (primeGap (n + r) : ℝ) ^ d := by
  have hb0 := base_cast_ne_zero hB
  have hBk0 : (B : ℝ) ^ k ≠ 0 := pow_ne_zero k hb0
  let f : ℕ → ℝ := fun m =>
    (primeGap (n + k * m + r) : ℝ) ^ d / (B : ℝ) ^ (k * (m + 1))
  have hf : Summable f := gapPowerTheta_summable (B := B) (k := k) (r := r)
      (d := d) (n := n) hB hk
  have hsplit : f 0 + ∑' m, f (m + 1) = ∑' m, f m := by
    simpa [sum_range_one] using hf.sum_add_tsum_nat_add 1
  have hf0 : f 0 = (primeGap (n + r) : ℝ) ^ d / (B : ℝ) ^ k := by
    have : k * (0 + 1) = k := by omega
    simp [f, this]
  have hshift :
      (fun m => f (m + 1)) =
        fun m =>
          ((primeGap (n + k + k * m + r) : ℝ) ^ d / (B : ℝ) ^ (k * (m + 1))) /
            (B : ℝ) ^ k := by
    funext m
    have hidx : n + k * (m + 1) + r = n + k + k * m + r := by ring
    have hpow : k * (m + 2) = k * (m + 1) + k := by ring
    simp only [f]
    rw [hidx, hpow, pow_add]
    field_simp [hBk0]
  have htail : ∑' m, f (m + 1) = gapPowerTheta B k r d (n + k) / (B : ℝ) ^ k := by
    rw [hshift, tsum_div_const]
    rfl
  have htheta : gapPowerTheta B k r d n = ∑' m, f m := rfl
  have hform :
      gapPowerTheta B k r d n =
        (primeGap (n + r) : ℝ) ^ d / (B : ℝ) ^ k +
          gapPowerTheta B k r d (n + k) / (B : ℝ) ^ k := by
    rw [htheta, ← hsplit, hf0, htail]
  have hmul := congrArg (fun x => (B : ℝ) ^ k * x) hform
  have hsimp :
      (B : ℝ) ^ k *
          ((primeGap (n + r) : ℝ) ^ d / (B : ℝ) ^ k +
            gapPowerTheta B k r d (n + k) / (B : ℝ) ^ k) =
        (primeGap (n + r) : ℝ) ^ d + gapPowerTheta B k r d (n + k) := by
    field_simp [hBk0]
  rw [hsimp] at hmul
  linarith

end PrimeGapNormality.Prime
