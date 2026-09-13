import PrimeGapNormality.Prime.JointWeyl
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Diagonal `q_i`-lifting for `JointWeyl`

From `JointWeyl(b, (q_i θ_i)_i)` with `q_i = b_i - 1` conclude
`JointWeyl(b, θ)`. Bases may be equal. Distinctness is not required.

Finite difference `|A_N - C_{N,K}| ≤ (K-1)/N` (for `N ≥ 1`) and the
Cauchy–Schwarz square bound are separate from the limit. Integer
differences `b_i^h - b_i^l` are formed in `ℤ`; no `Nat` subtraction
when `h < l` and no rounded division. This replaces the product-Wall
root sum `(∏ q_i)/K` by `1/K` in the multi-base proof, not a new
arithmetic range. Scalar `weylCriterion_of_mul` is unchanged.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §3;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(does not replace scalar Wall).
Contract: API
Audit: GREEN
-/

set_option maxHeartbeats 1200000

open Finset
open Filter (Tendsto atTop)
open scoped Topology

namespace PrimeGapNormality.Prime

/-! ### Circle-character identities (public `e`) -/

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem e_zero : e 0 = 1 := by
  unfold e
  simp [Complex.exp_zero]

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

/-! ### Integer geometric divisibility (`ℤ` differences, no `Nat` subtraction) -/

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

/-- Off-diagonal integer mode
`s_i = t_i ((b_i : ℤ)^h - (b_i : ℤ)^l) / ((b_i : ℤ) - 1)`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §3.
Contract: API
Audit: GREEN -/
private def liftMode {I : Type*} (b : I → ℕ) (t : I → ℤ) (h l : ℕ) (i : I) : ℤ :=
  t i * (((b i : ℤ) ^ h - (b i : ℤ) ^ l) / ((b i : ℤ) - 1))

private theorem liftMode_mul {I : Type*} (b : I → ℕ) (t : I → ℤ) (h l : ℕ)
    (i : I) (_hb : 2 ≤ b i) :
    (liftMode b t h l i : ℝ) * ((b i : ℝ) - 1) =
      (t i : ℝ) * ((b i : ℝ) ^ h - (b i : ℝ) ^ l) := by
  unfold liftMode
  have hx : ((b i : ℤ) - 1) ∣ (b i : ℤ) ^ h - (b i : ℤ) ^ l :=
    sub_one_dvd_pow_sub_pow _ _ _
  have hR :
      ((((b i : ℤ) ^ h - (b i : ℤ) ^ l) / ((b i : ℤ) - 1) : ℤ) : ℝ) *
          ((b i : ℝ) - 1) =
        (b i : ℝ) ^ h - (b i : ℝ) ^ l := by
    have hb1 : ((b i : ℝ) - 1) = (((b i : ℤ) - 1 : ℤ) : ℝ) := by simp
    rw [hb1, ← Int.cast_mul, Int.ediv_mul_cancel hx]
    simp [Int.cast_pow]
  push_cast
  rw [mul_assoc, hR]

private theorem liftMode_exists_ne_zero {I : Type*}
    {b : I → ℕ} {t : I → ℤ} {h l : ℕ}
    (hb : ∀ i, 2 ≤ b i) (ht : ∃ i, t i ≠ 0) (hhl : h ≠ l) :
    ∃ i, liftMode b t h l i ≠ 0 := by
  obtain ⟨i, hi⟩ := ht
  refine ⟨i, ?_⟩
  unfold liftMode
  refine mul_ne_zero hi ?_
  intro hz
  have hmul := Int.ediv_mul_cancel (sub_one_dvd_pow_sub_pow (b i : ℤ) h l)
  rw [hz, zero_mul] at hmul
  exact hhl (int_pow_right_inj (hb i) (sub_eq_zero.mp hmul.symm))

/-! ### Joint characters and finite Cesàro / block averages -/

private noncomputable def jointChar {I : Type*} [Fintype I]
    (b : I → ℕ) (θ : I → ℝ) (t : I → ℤ) (n : ℕ) : ℂ :=
  e (∑ i : I, (t i : ℝ) * (b i : ℝ) ^ n * θ i)

private theorem norm_jointChar {I : Type*} [Fintype I]
    (b : I → ℕ) (θ : I → ℝ) (t : I → ℤ) (n : ℕ) :
    ‖jointChar b θ t n‖ = 1 := by
  unfold jointChar
  exact norm_e _

private theorem jointChar_mul_star {I : Type*} [Fintype I]
    (b : I → ℕ) (θ : I → ℝ) (t : I → ℤ) (n h l : ℕ)
    (hb : ∀ i, 2 ≤ b i) :
    jointChar b θ t (n + h) * star (jointChar b θ t (n + l)) =
      jointChar b (fun i => ((b i : ℝ) - 1) * θ i) (liftMode b t h l) n := by
  unfold jointChar
  rw [star_e, ← e_add]
  congr 1
  rw [← sub_eq_add_neg, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  have hpowh : (b i : ℝ) ^ (n + h) = (b i : ℝ) ^ n * (b i : ℝ) ^ h :=
    pow_add _ _ _
  have hpowl : (b i : ℝ) ^ (n + l) = (b i : ℝ) ^ n * (b i : ℝ) ^ l :=
    pow_add _ _ _
  have hmul := liftMode_mul b t h l i (hb i)
  calc
    (t i : ℝ) * (b i : ℝ) ^ (n + h) * θ i -
        (t i : ℝ) * (b i : ℝ) ^ (n + l) * θ i
        = (t i : ℝ) * ((b i : ℝ) ^ (n + h) - (b i : ℝ) ^ (n + l)) * θ i := by
          ring
    _ = (t i : ℝ) * ((b i : ℝ) ^ n * ((b i : ℝ) ^ h - (b i : ℝ) ^ l)) * θ i := by
          rw [hpowh, hpowl]
          ring
    _ = (t i : ℝ) * ((b i : ℝ) ^ h - (b i : ℝ) ^ l) * (b i : ℝ) ^ n * θ i := by
          ring
    _ = (liftMode b t h l i : ℝ) * ((b i : ℝ) - 1) * (b i : ℝ) ^ n * θ i := by
          rw [← hmul]
    _ = (liftMode b t h l i : ℝ) * (b i : ℝ) ^ n *
          (((b i : ℝ) - 1) * θ i) := by
          ring

private noncomputable def cesaroMean (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ range N, a n) / N

private noncomputable def blockAvg (a : ℕ → ℂ) (N K : ℕ) : ℂ :=
  (∑ n ∈ range N, (∑ h ∈ range K, a (n + h)) / K) / N

private theorem sum_range_natCast (K : ℕ) :
    ∑ h ∈ range K, (h : ℝ) = (K : ℝ) * ((K : ℝ) - 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    simp only [Nat.cast_succ]
    ring

/-- Shifted Cesàro means of unimodular sequences differ by `O(j/N)`
for `N ≥ 1`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §3;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3.
Contract: API
Audit: GREEN -/
private theorem cesaro_shift_sub_of_pos (a : ℕ → ℂ) (j : ℕ) {N : ℕ}
    (hN : 0 < N) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ‖(∑ n ∈ range N, a (n + j)) / N - (∑ n ∈ range N, a n) / N‖
      ≤ (2 * j : ℝ) / N := by
  have hN0 : (N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
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

private theorem blockAvg_eq_avg_shift (a : ℕ → ℂ) {N K : ℕ}
    (hN : 0 < N) (hK : 0 < K) :
    blockAvg a N K =
      (∑ h ∈ range K, (∑ n ∈ range N, a (n + h)) / N) / K := by
  have hN0 : (N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  have hK0 : (K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hK)
  unfold blockAvg
  have h1 :
      ∑ n ∈ range N, (∑ h ∈ range K, a (n + h)) / K =
        (∑ n ∈ range N, ∑ h ∈ range K, a (n + h)) / K := by
    simp_rw [div_eq_mul_inv, ← sum_mul]
  rw [h1, sum_comm]
  have h2 :
      (∑ h ∈ range K, ∑ n ∈ range N, a (n + h)) / K / N =
        (∑ h ∈ range K, ∑ n ∈ range N, a (n + h)) / N / K := by
    field_simp [hK0, hN0]
  rw [h2]
  have h3 :
      (∑ h ∈ range K, ∑ n ∈ range N, a (n + h)) / N =
        ∑ h ∈ range K, (∑ n ∈ range N, a (n + h)) / N := by
    simp_rw [div_eq_mul_inv, sum_mul]
  rw [h3]

/-- Finite smoothing bound `|A_N - C_{N,K}| ≤ (K-1)/N` for `N ≥ 1`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §3.
Contract: API
Audit: GREEN -/
private theorem abs_cesaro_sub_blockAvg (a : ℕ → ℂ) {N K : ℕ}
    (hN : 0 < N) (hK : 0 < K) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ‖cesaroMean a N - blockAvg a N K‖ ≤ ((K : ℝ) - 1) / N := by
  have hK0 : (K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hK)
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  rw [blockAvg_eq_avg_shift a hN hK]
  unfold cesaroMean
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

/-- Jensen/Cauchy–Schwarz: `|C_{N,K}|^2 ≤ (1/N) ∑_n |(1/K) ∑_h a_{n+h}|^2`
for `N ≥ 1`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §3.
Contract: API
Audit: GREEN -/
private theorem abs_blockAvg_sq_le (a : ℕ → ℂ) {N K : ℕ}
    (hN : 0 < N) (_hK : 0 < K) :
    ‖blockAvg a N K‖ ^ 2 ≤
      (∑ n ∈ range N, ‖(∑ h ∈ range K, a (n + h)) / K‖ ^ 2) / N := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let z : ℕ → ℂ := fun n => (∑ h ∈ range K, a (n + h)) / K
  have hblock : blockAvg a N K = (∑ n ∈ range N, z n) / N := rfl
  rw [hblock]
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

private theorem ofReal_norm_sq (w : ℂ) :
    ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  rfl

private theorem ofReal_window_sq (a : ℕ → ℂ) {K : ℕ} (hK : 0 < K) (n : ℕ) :
    ((‖(∑ h ∈ range K, a (n + h)) / K‖ ^ 2 : ℝ) : ℂ) =
      ((1 : ℂ) / (K : ℂ) ^ 2) *
        ∑ h ∈ range K, ∑ l ∈ range K, a (n + h) * star (a (n + l)) := by
  have hK0 : (K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hK)
  set z := ∑ h ∈ range K, a (n + h)
  rw [ofReal_norm_sq, star_div₀]
  have hstarK : star (K : ℂ) = (K : ℂ) := by simp
  rw [hstarK]
  have hquot : (z / K) * (star z / K) = (z * star z) / (K : ℂ) ^ 2 := by
    field_simp [hK0]
  have hscale : (z * star z) / (K : ℂ) ^ 2 =
      ((1 : ℂ) / (K : ℂ) ^ 2) * (z * star z) := by
    field_simp [hK0]
  have hstarz : star z = ∑ l ∈ range K, star (a (n + l)) :=
    star_sum (range K) fun h => a (n + h)
  have hprod : z * star z =
      ∑ h ∈ range K, ∑ l ∈ range K, a (n + h) * star (a (n + l)) := by
    rw [hstarz, sum_mul_sum]
  rw [hquot, hscale, hprod]

private theorem ofReal_avg_window_sq (a : ℕ → ℂ) (N : ℕ) {K : ℕ}
    (hK : 0 < K) :
    (((∑ n ∈ range N, ‖(∑ h ∈ range K, a (n + h)) / K‖ ^ 2) / N : ℝ) : ℂ) =
      ((1 : ℂ) / (K : ℂ) ^ 2) *
        ∑ h ∈ range K, ∑ l ∈ range K,
          (∑ n ∈ range N, a (n + h) * star (a (n + l))) / N := by
  rw [Complex.ofReal_div, Complex.ofReal_sum]
  have hpt : ∀ n ∈ range N,
      ((‖(∑ h ∈ range K, a (n + h)) / K‖ ^ 2 : ℝ) : ℂ) =
        ((1 : ℂ) / (K : ℂ) ^ 2) *
          ∑ h ∈ range K, ∑ l ∈ range K, a (n + h) * star (a (n + l)) :=
    fun n _ => ofReal_window_sq a hK n
  have hrew :
      ∑ n ∈ range N,
          ((‖(∑ h ∈ range K, a (n + h)) / K‖ ^ 2 : ℝ) : ℂ) =
        ∑ n ∈ range N,
          ((1 : ℂ) / (K : ℂ) ^ 2) *
            ∑ h ∈ range K, ∑ l ∈ range K, a (n + h) * star (a (n + l)) :=
    sum_congr rfl hpt
  rw [hrew, ← mul_sum]
  have hcomm :
      ∑ n ∈ range N, ∑ h ∈ range K, ∑ l ∈ range K,
          a (n + h) * star (a (n + l)) =
        ∑ h ∈ range K, ∑ l ∈ range K, ∑ n ∈ range N,
          a (n + h) * star (a (n + l)) := by
    have h1 :
        ∑ n ∈ range N, ∑ h ∈ range K, ∑ l ∈ range K,
            a (n + h) * star (a (n + l)) =
          ∑ h ∈ range K, ∑ n ∈ range N, ∑ l ∈ range K,
            a (n + h) * star (a (n + l)) := by
      rw [sum_comm]
    have h2 :
        ∑ h ∈ range K, ∑ n ∈ range N, ∑ l ∈ range K,
            a (n + h) * star (a (n + l)) =
          ∑ h ∈ range K, ∑ l ∈ range K, ∑ n ∈ range N,
            a (n + h) * star (a (n + l)) := by
      refine sum_congr rfl fun h _ => sum_comm
    rw [h1, h2]
  rw [hcomm]
  simp_rw [div_eq_mul_inv]
  rw [mul_assoc]
  congr 1
  rw [sum_mul]
  refine sum_congr rfl fun h _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun l _ => ?_
  rfl

/-! ### Limit of the window-square mean -/

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

private theorem tendsto_shift_pair {I : Type*} [Fintype I] [DecidableEq I]
    {b : I → ℕ} {θ : I → ℝ} {t : I → ℤ}
    (hb : ∀ i, 2 ≤ b i)
    (hW : JointWeyl b (fun i => ((b i : ℝ) - 1) * θ i))
    (ht : ∃ i, t i ≠ 0) (h l : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
          jointChar b θ t (n + h) * star (jointChar b θ t (n + l))) / N)
      atTop (𝓝 (if h = l then 1 else 0)) := by
  by_cases hhl : h = l
  · subst hhl
    have hterm : ∀ n,
        jointChar b θ t (n + h) * star (jointChar b θ t (n + h)) = 1 := by
      intro n
      unfold jointChar
      rw [star_e, ← e_add, add_neg_cancel, e_zero]
    have hfun :
        (fun N : ℕ =>
          (∑ n ∈ range N,
              jointChar b θ t (n + h) * star (jointChar b θ t (n + h))) / N) =
          fun N => (∑ n ∈ range N, (1 : ℂ)) / N := by
      funext N
      congr 1
      exact sum_congr rfl fun n _ => hterm n
    rw [hfun]
    simpa using tendsto_one_div_nat
  · have hs := liftMode_exists_ne_zero hb ht hhl
    have hmode := hW (liftMode b t h l) hs
    have hrew : ∀ n,
        jointChar b θ t (n + h) * star (jointChar b θ t (n + l)) =
          jointChar b (fun i => ((b i : ℝ) - 1) * θ i)
            (liftMode b t h l) n :=
      fun n => jointChar_mul_star b θ t n h l hb
    have hfun :
        (fun N : ℕ =>
          (∑ n ∈ range N,
              jointChar b θ t (n + h) * star (jointChar b θ t (n + l))) / N) =
          fun N =>
            (∑ n ∈ range N,
                jointChar b (fun i => ((b i : ℝ) - 1) * θ i)
                  (liftMode b t h l) n) / N := by
      funext N
      congr 1
      exact sum_congr rfl fun n _ => hrew n
    rw [hfun]
    simpa [jointChar, hhl] using hmode

private theorem tendsto_avg_window_sq {I : Type*} [Fintype I] [DecidableEq I]
    {b : I → ℕ} {θ : I → ℝ} {t : I → ℤ}
    (hb : ∀ i, 2 ≤ b i)
    (hW : JointWeyl b (fun i => ((b i : ℝ) - 1) * θ i))
    (ht : ∃ i, t i ≠ 0) {K : ℕ} (hK : 0 < K) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
          ‖(∑ h ∈ range K, jointChar b θ t (n + h)) / K‖ ^ 2) / N)
      atTop (𝓝 ((1 : ℝ) / K)) := by
  have hC :
      Tendsto (fun N : ℕ =>
        (((∑ n ∈ range N,
            ‖(∑ h ∈ range K, jointChar b θ t (n + h)) / K‖ ^ 2) / N : ℝ) : ℂ))
        atTop (𝓝 (((1 : ℝ) / K : ℝ) : ℂ)) := by
    simp_rw [ofReal_avg_window_sq (jointChar b θ t) _ hK]
    have hpairs :=
      tendsto_finset_sum_nhds (range K)
        (fun h N => ∑ l ∈ range K,
          (∑ n ∈ range N,
              jointChar b θ t (n + h) *
                star (jointChar b θ t (n + l))) / N)
        (fun h => ∑ l ∈ range K, (if h = l then (1 : ℂ) else 0))
        (fun h _ =>
          tendsto_finset_sum_nhds (range K)
            (fun l N =>
              (∑ n ∈ range N,
                  jointChar b θ t (n + h) *
                    star (jointChar b θ t (n + l))) / N)
            (fun l => if h = l then (1 : ℂ) else 0)
            (fun l _ => tendsto_shift_pair hb hW ht h l))
    have hdiag :
        (∑ h ∈ range K, ∑ l ∈ range K, (if h = l then (1 : ℂ) else 0)) =
          K := by
      have hinner : ∀ h ∈ range K,
          (∑ l ∈ range K, (if h = l then (1 : ℂ) else 0)) = 1 := by
        intro h hh
        rw [sum_ite_eq]
        simp [hh]
      simp_rw [sum_congr rfl hinner, sum_const, nsmul_eq_mul, card_range,
        mul_one]
    have hscale :
        Tendsto (fun N =>
          ((1 : ℂ) / (K : ℂ) ^ 2) *
            ∑ h ∈ range K, ∑ l ∈ range K,
              (∑ n ∈ range N,
                  jointChar b θ t (n + h) *
                    star (jointChar b θ t (n + l))) / N)
          atTop (𝓝 (((1 : ℂ) / (K : ℂ) ^ 2) * (K : ℂ))) :=
      tendsto_const_nhds.mul (hdiag ▸ hpairs)
    have hval : ((1 : ℂ) / (K : ℂ) ^ 2) * (K : ℂ) = (1 : ℂ) / K := by
      have hK0 : (K : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hK)
      field_simp [hK0]
    have hcoe : ((1 : ℂ) / K) = ↑((1 : ℝ) / K) := by
      rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    exact hcoe ▸ (hval ▸ hscale)
  exact Filter.tendsto_ofReal_iff.1 hC

/-! ### Public lifting -/

/-- Diagonal `q_i`-lift: `JointWeyl(b, ((b_i-1) θ_i)_i)` implies
`JointWeyl(b, θ)`. Finite `|A_N-C_{N,K}| ≤ (K-1)/N` and the square
bound are the lemmas above; the limit takes `N → ∞` then `K → ∞`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §3;
`rounds/round97/05_gpt_normality_second_read_and_finite_wall.md` §3
(does not replace scalar Wall).
Contract: API
Audit: GREEN -/
theorem jointWeyl_of_scaled
    {I : Type*} [Fintype I] [DecidableEq I] {b : I → ℕ} {θ : I → ℝ}
    (hb : ∀ i, 2 ≤ b i)
    (h : JointWeyl b (fun i => ((b i : ℝ) - 1) * θ i)) :
    JointWeyl b θ := by
  intro t ht
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨K0, hK0⟩ := exists_nat_gt (4 / ε ^ 2)
  let K := K0 + 1
  have hK : 0 < K := Nat.succ_pos _
  have hKε : (1 : ℝ) / K < (ε / 2) ^ 2 := by
    have hKgt : 4 / ε ^ 2 < K :=
      hK0.trans (Nat.cast_lt.mpr (Nat.lt_succ_self K0))
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
    have : (1 : ℝ) / K < ε ^ 2 / 4 := by
      rw [div_lt_div_iff₀ hKpos (by norm_num : (0 : ℝ) < 4)]
      have hmul := mul_lt_mul_of_pos_right hKgt hεsq
      have hcancel : 4 / ε ^ 2 * ε ^ 2 = (4 : ℝ) := by
        field_simp [hεsq.ne']
      rw [hcancel] at hmul
      linarith
    have hsq : ε ^ 2 / 4 = (ε / 2) ^ 2 := by ring
    rwa [hsq] at this
  let a : ℕ → ℂ := jointChar b θ t
  have ha1 : ∀ n, ‖a n‖ ≤ 1 := fun n => (norm_jointChar b θ t n).le
  have hD := tendsto_avg_window_sq hb h ht hK
  have hδ : (0 : ℝ) < (ε / 2) ^ 2 - 1 / K := sub_pos.mpr hKε
  have hshift :=
    tendsto_const_div_atTop_nhds_zero_nat ((K : ℝ) - 1)
  filter_upwards [Filter.eventually_ge_atTop 1,
    hD.eventually (Metric.ball_mem_nhds ((1 : ℝ) / K) hδ),
    hshift.eventually (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))] with
    N hN1 hDclose hshiftN
  have hN : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN1
  have hAC : ‖cesaroMean a N - blockAvg a N K‖ ≤ ((K : ℝ) - 1) / N :=
    abs_cesaro_sub_blockAvg a hN hK ha1
  have hCSsq : ‖blockAvg a N K‖ ^ 2 ≤
      (∑ n ∈ range N, ‖(∑ h ∈ range K, a (n + h)) / K‖ ^ 2) / N :=
    abs_blockAvg_sq_le a hN hK
  have hDlt :
      (∑ n ∈ range N, ‖(∑ h ∈ range K, a (n + h)) / K‖ ^ 2) / N <
        (ε / 2) ^ 2 := by
    set avg :=
      (∑ n ∈ range N, ‖(∑ h ∈ range K, a (n + h)) / K‖ ^ 2) / N
    have habs : |avg - (1 : ℝ) / K| < (ε / 2) ^ 2 - 1 / K := by
      simpa [Real.dist_eq, avg] using hDclose
    have hle : avg - (1 : ℝ) / K ≤ |avg - (1 : ℝ) / K| := le_abs_self _
    have hlt : avg - (1 : ℝ) / K < (ε / 2) ^ 2 - 1 / K :=
      lt_of_le_of_lt hle habs
    linarith [hlt]
  have hC2 : ‖blockAvg a N K‖ ^ 2 < (ε / 2) ^ 2 :=
    hCSsq.trans_lt hDlt
  have hC : ‖blockAvg a N K‖ < ε / 2 :=
    (sq_lt_sq₀ (norm_nonneg _) (div_nonneg hε.le (by norm_num))).1 hC2
  have hAClt : ‖cesaroMean a N - blockAvg a N K‖ < ε / 2 := by
    have hK1 : 1 ≤ K := Nat.succ_le_iff.mpr hK
    have hnn : (0 : ℝ) ≤ (K : ℝ) - 1 := by
      have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
        rw [Nat.cast_sub hK1, Nat.cast_one]
      rw [← hcast]
      exact Nat.cast_nonneg _
    have : ((K : ℝ) - 1) / N < ε / 2 := by
      have habs : |((K : ℝ) - 1) / N| < ε / 2 := by
        have hNabs : |(N : ℝ)| = N := abs_of_nonneg (Nat.cast_nonneg N)
        rw [abs_div, hNabs]
        simpa [Real.dist_eq] using hshiftN
      rwa [abs_of_nonneg (div_nonneg hnn (Nat.cast_nonneg N))] at habs
    exact lt_of_le_of_lt hAC this
  have hA : ‖cesaroMean a N‖ < ε := by
    have :=
      (norm_add_le (cesaroMean a N - blockAvg a N K) (blockAvg a N K)).trans_lt
        (add_lt_add hAClt hC)
    have hdecomp :
        (cesaroMean a N - blockAvg a N K) + blockAvg a N K =
          cesaroMean a N := by
      abel
    simpa [hdecomp] using this
  simpa [cesaroMean, a, jointChar, dist_zero_right] using hA

end PrimeGapNormality.Prime
