import PrimeGapNormality.Prime.Fourier
import PrimeGapNormality.Prime.JointWeyl
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic

/-!
# Abstract Weyl-mean assembly (paper orbit passage)

Local means of `e(truncated phase)` pass to Cesàro means of
`e(τ C^n θ)` by Lipschitz of the circle character, uniform truncation
error, and block averaging with an `O(H/N)` incomplete-block remainder.
No primes and no S/T/D.

Source: `rounds/round104/13_gpt_paper_v0_3.tex`
section "From local means to the common orbit".
Contract: API
Audit: GREEN
-/

open Finset Filter
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000

/-! ### Circle-character Lipschitz -/

private theorem two_pi_I_mul (x : ℝ) :
    (2 * Real.pi * Complex.I * (x : ℂ) : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) := by
  simp [mul_comm, mul_left_comm, Complex.ofReal_mul]

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [two_pi_I_mul, Complex.norm_exp_I_mul_ofReal]

private theorem norm_e_sub_one_le (δ : ℝ) :
    ‖e δ - 1‖ ≤ 2 * Real.pi * |δ| := by
  unfold e
  rw [two_pi_I_mul]
  have hle := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * δ)
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg Real.pi_pos.le, mul_comm,
    mul_left_comm, mul_assoc] using hle

/-- Lipschitz of `e`: `‖e t - e s‖ ≤ 2π |t - s|`. -/
theorem norm_e_lipschitz (s t : ℝ) :
    ‖e t - e s‖ ≤ 2 * Real.pi * |t - s| := by
  have h : e t - e s = e s * (e (t - s) - 1) := by
    calc
      e t - e s = e ((t - s) + s) - e s := by rw [sub_add_cancel]
      _ = e (t - s) * e s - e s := by rw [e_add]
      _ = e s * (e (t - s) - 1) := by
        rw [mul_comm (e (t - s)), mul_sub, mul_one]
  rw [h, norm_mul, norm_e, one_mul]
  exact norm_e_sub_one_le (t - s)

/-- Truncation of a linear phase: `‖e(τ φ) - e(τ ψ)‖ ≤ 2π |τ| |φ - ψ|`. -/
theorem norm_e_mul_sub (τ : ℤ) (φ ψ : ℝ) :
    ‖e ((τ : ℝ) * φ) - e ((τ : ℝ) * ψ)‖ ≤
      2 * Real.pi * |(τ : ℝ)| * |φ - ψ| := by
  have h := norm_e_lipschitz ((τ : ℝ) * ψ) ((τ : ℝ) * φ)
  have hmul : |((τ : ℝ) * φ) - ((τ : ℝ) * ψ)| = |(τ : ℝ)| * |φ - ψ| := by
    rw [← mul_sub, abs_mul]
  have : 2 * Real.pi * |((τ : ℝ) * φ) - ((τ : ℝ) * ψ)| =
      2 * Real.pi * |(τ : ℝ)| * |φ - ψ| := by
    rw [hmul]
    ring
  exact h.trans_eq this

/-! ### Cesàro means of bounded sequences -/

/-- Cesàro mean. `N = 0` uses field division `z / 0 = 0`. -/
noncomputable def cesaroMean (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ range N, a n) / N

private theorem norm_sum_unimodular (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (s : Finset ℕ) : ‖∑ n ∈ s, a n‖ ≤ (s.card : ℝ) := by
  have hsum := norm_sum_le s a
  have h1 : ∑ n ∈ s, ‖a n‖ ≤ ∑ n ∈ s, (1 : ℝ) :=
    sum_le_sum fun n _ => ha n
  have hcard : (∑ n ∈ s, (1 : ℝ)) = s.card := by simp [sum_const]
  exact hsum.trans (h1.trans_eq hcard)

theorem norm_cesaroMean_le_one (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (N : ℕ) : ‖cesaroMean a N‖ ≤ 1 := by
  unfold cesaroMean
  by_cases hN : N = 0
  · subst hN
    simp
  · have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hsum := norm_sum_unimodular a ha (range N)
    have hcard : ((range N).card : ℝ) = N := by simp
    rw [norm_div]
    have hnn : ‖(N : ℂ)‖ = N := by simp
    rw [hnn]
    rw [hcard] at hsum
    exact (div_le_one hpos).mpr hsum

/-- Cesàro distance is at most the average of pointwise norms. -/
theorem cesaroMean_dist_le_avg (a b : ℕ → ℂ) (N : ℕ) (_hN : 0 < N) :
    ‖cesaroMean a N - cesaroMean b N‖ ≤
      (∑ n ∈ range N, ‖a n - b n‖) / N := by
  unfold cesaroMean
  rw [← sub_div, norm_div]
  have hnn : ‖(N : ℂ)‖ = N := by simp
  rw [hnn]
  have hsum :
      ‖∑ n ∈ range N, a n - ∑ n ∈ range N, b n‖ ≤
        ∑ n ∈ range N, ‖a n - b n‖ := by
    rw [← sum_sub_distrib]
    exact norm_sum_le _ _
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)

/-- Uniform phase error passes to Cesàro means. -/
theorem cesaroMean_dist_of_uniform {a b : ℕ → ℂ} {ε : ℝ}
    (h : ∀ n, ‖a n - b n‖ ≤ ε) (N : ℕ) (hN : 0 < N) :
    ‖cesaroMean a N - cesaroMean b N‖ ≤ ε := by
  have havg := cesaroMean_dist_le_avg a b N hN
  have hsum :
      ∑ n ∈ range N, ‖a n - b n‖ ≤ ∑ n ∈ range N, ε :=
    sum_le_sum fun n _ => h n
  have hdiv :
      (∑ n ∈ range N, ‖a n - b n‖) / N ≤ (∑ n ∈ range N, ε) / N :=
    div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
  have hsimp : (∑ n ∈ range N, ε) / N = ε := by
    simp [sum_const, nsmul_eq_mul, Nat.cast_ne_zero.mpr hN.ne']
  exact havg.trans (hdiv.trans_eq hsimp)

/-- Lipschitz truncation of Cesàro means of `e(τ ·)`. -/
theorem cesaroMean_e_trunc (τ : ℤ) (φ U : ℕ → ℝ) {ε : ℝ}
    (h : ∀ n, |φ n - U n| ≤ ε) (N : ℕ) (hN : 0 < N) :
    ‖cesaroMean (fun n => e ((τ : ℝ) * φ n)) N -
        cesaroMean (fun n => e ((τ : ℝ) * U n)) N‖ ≤
      2 * Real.pi * |(τ : ℝ)| * ε := by
  refine cesaroMean_dist_of_uniform (fun n => ?_) N hN
  have hlip := norm_e_mul_sub τ (φ n) (U n)
  have hnn : 0 ≤ 2 * Real.pi * |(τ : ℝ)| :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (abs_nonneg _)
  exact hlip.trans (mul_le_mul_of_nonneg_left (h n) hnn)

/-! ### Block averages -/

private theorem sum_range_mul (a : ℕ → ℂ) (q H : ℕ) :
    ∑ n ∈ range (q * H), a n =
      ∑ k ∈ range q, ∑ i ∈ range H, a (k * H + i) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit := sum_range_add a (q * H) H
    have hmul : q.succ * H = q * H + H := Nat.succ_mul q H
    rw [hmul, hsplit, ih, sum_range_succ]

/-- If every complete length-`H` block has mean of norm `≤ ε`, then the
Cesàro mean is `≤ ε + H/N`. -/
theorem cesaroMean_of_block_means (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (H : ℕ) (hH : 0 < H) (ε : ℝ) (hε : 0 ≤ ε)
    (hblk : ∀ k,
      ‖(∑ i ∈ range H, a (k * H + i)) / (H : ℂ)‖ ≤ ε)
    (N : ℕ) :
    ‖cesaroMean a N‖ ≤ ε + (H : ℝ) / N := by
  unfold cesaroMean
  by_cases hN : N = 0
  · subst hN
    simp [hε]
  · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    let q := N / H
    let r := N % H
    have hqr : q * H + r = N := by
      rw [Nat.mul_comm q H]
      exact Nat.div_add_mod N H
    have hsum :
        ∑ n ∈ range N, a n =
          (∑ k ∈ range q, ∑ i ∈ range H, a (k * H + i)) +
            ∑ i ∈ range r, a (q * H + i) := by
      have hsplit := sum_range_add a (q * H) r
      rw [← hqr, hsplit, sum_range_mul]
    have hHpos : (0 : ℝ) < H := Nat.cast_pos.mpr hH
    have hblk' : ∀ k, ‖∑ i ∈ range H, a (k * H + i)‖ ≤ ε * H := by
      intro k
      have hk := hblk k
      rw [norm_div] at hk
      have hnn : ‖(H : ℂ)‖ = H := by simp
      rw [hnn] at hk
      exact (div_le_iff₀ hHpos).mp hk
    have hblocks :
        ‖∑ k ∈ range q, ∑ i ∈ range H, a (k * H + i)‖ ≤ ε * q * H := by
      have hsumk :=
        norm_sum_le (range q) fun k => ∑ i ∈ range H, a (k * H + i)
      have h1 :
          ∑ k ∈ range q, ‖∑ i ∈ range H, a (k * H + i)‖ ≤
            ∑ k ∈ range q, (ε * H) :=
        sum_le_sum fun k _ => hblk' k
      have hcard : (∑ k ∈ range q, (ε * H)) = ε * q * H := by
        simp [sum_const, nsmul_eq_mul]
        ring
      exact hsumk.trans (h1.trans_eq hcard)
    have hrem : ‖∑ i ∈ range r, a (q * H + i)‖ ≤ (r : ℝ) := by
      have h :=
        norm_sum_unimodular (fun i => a (q * H + i))
          (fun i => ha (q * H + i)) (range r)
      simpa [card_range] using h
    have hrH : (r : ℝ) ≤ H := by
      have : r < H := Nat.mod_lt N hH
      exact Nat.cast_le.mpr this.le
    have htot : ‖∑ n ∈ range N, a n‖ ≤ ε * N + H := by
      rw [hsum]
      have hadd :=
        (norm_add_le
            (∑ k ∈ range q, ∑ i ∈ range H, a (k * H + i))
            (∑ i ∈ range r, a (q * H + i))).trans
          (add_le_add hblocks (hrem.trans hrH))
      have hqH : (q * H : ℝ) ≤ N := by
        have : q * H ≤ N := by
          rw [Nat.mul_comm]
          exact Nat.mul_div_le N H
        exact_mod_cast this
      have : ε * q * H + H ≤ ε * N + H := by
        linarith [mul_le_mul_of_nonneg_left hqH hε]
      exact hadd.trans this
    rw [norm_div]
    have hnn : ‖(N : ℂ)‖ = N := by simp
    rw [hnn]
    have hdiv := div_le_div_of_nonneg_right htot (Nat.cast_nonneg N)
    have : (ε * N + H) / N = ε + (H : ℝ) / N := by
      field_simp [hNpos.ne']
    exact hdiv.trans_eq this

/-- Uniform vanishing of all length-`H` block means implies Cesàro → 0. -/
theorem tendsto_cesaroMean_of_uniform_blocks (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (h : ∀ ε : ℝ, 0 < ε → ∃ H : ℕ, 0 < H ∧
      ∀ k, ‖(∑ i ∈ range H, a (k * H + i)) / (H : ℂ)‖ ≤ ε) :
    Tendsto (fun N : ℕ => cesaroMean a N) atTop (nhds 0) := by
  refine Metric.tendsto_atTop.mpr fun δ hδ => ?_
  have hδ2 : 0 < δ / 2 := half_pos hδ
  obtain ⟨H, hH, hblk⟩ := h (δ / 2) hδ2
  refine ⟨⌊(2 * H : ℝ) / δ⌋₊ + 1, fun N hN => ?_⟩
  have hNpos : 0 < N :=
    lt_of_lt_of_le (Nat.succ_pos _) hN
  have hbound :=
    cesaroMean_of_block_means a ha H hH (δ / 2) hδ2.le hblk N
  have hHN : (H : ℝ) / N < δ / 2 := by
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
    have hx : (2 * H : ℝ) / δ < (N : ℝ) := by
      have hfloor := Nat.lt_floor_add_one ((2 * H : ℝ) / δ)
      have hle : ((⌊(2 * H : ℝ) / δ⌋₊ : ℝ) + 1) ≤ (N : ℝ) := by
        have hN' : (⌊(2 * H : ℝ) / δ⌋₊ + 1 : ℕ) ≤ N := hN
        have hcast :
            ((⌊(2 * H : ℝ) / δ⌋₊ : ℝ) + 1) =
              ((⌊(2 * H : ℝ) / δ⌋₊ + 1 : ℕ) : ℝ) :=
          (Nat.cast_add_one _).symm
        exact hcast.trans_le (Nat.cast_le.mpr hN')
      linarith
    rw [div_lt_div_iff₀ hN0 (by positivity : (0 : ℝ) < 2)]
    linarith [(div_lt_iff₀ hδ).mp hx]
  have hsum : δ / 2 + (H : ℝ) / N < δ := by linarith [hHN]
  have : ‖cesaroMean a N - 0‖ < δ := by
    simpa [sub_zero] using hbound.trans_lt hsum
  simpa [dist_eq_norm] using this

/-! ### Prefix / dyadic remainder -/

/-- Dropping a prefix of length `M` costs at most `M/N` in Cesàro. -/
theorem cesaroMean_prefix_err (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (M N : ℕ) (hMN : M ≤ N) (hN : 0 < N) :
    ‖cesaroMean a N - (∑ n ∈ Ico M N, a n) / N‖ ≤ (M : ℝ) / N := by
  unfold cesaroMean
  have hunion : range N = range M ∪ Ico M N := by
    rw [range_eq_Ico, range_eq_Ico M]
    exact (Ico_union_Ico_eq_Ico (Nat.zero_le M) hMN).symm
  have hdisj : Disjoint (range M) (Ico M N) := by
    rw [range_eq_Ico]
    exact Ico_disjoint_Ico_consecutive 0 M N
  have hsplit : ∑ n ∈ range N, a n =
      ∑ n ∈ range M, a n + ∑ n ∈ Ico M N, a n := by
    rw [hunion, sum_union hdisj]
  rw [hsplit, add_div, add_sub_cancel_right, norm_div]
  have hnn : ‖(N : ℂ)‖ = N := by simp
  rw [hnn]
  have hsum := norm_sum_unimodular a ha (range M)
  have hcard : ((range M).card : ℝ) = M := by simp
  exact div_le_div_of_nonneg_right (hsum.trans_eq hcard) (Nat.cast_nonneg N)

/-- Dyadic prefix `N / 2^q` costs at most `2^{-q}` in Cesàro. -/
theorem cesaroMean_dyadic_prefix (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (N q : ℕ) (hN : 0 < N) :
    ‖cesaroMean a N - (∑ n ∈ Ico (N / 2 ^ q) N, a n) / N‖ ≤
      (1 : ℝ) / 2 ^ q := by
  have hM : N / 2 ^ q ≤ N := Nat.div_le_self _ _
  have herr := cesaroMean_prefix_err a ha (N / 2 ^ q) N hM hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpow : (0 : ℝ) < 2 ^ q := by positivity
  have hle : ((N / 2 ^ q : ℕ) : ℝ) / N ≤ (1 : ℝ) / 2 ^ q := by
    have hdiv : ((N / 2 ^ q : ℕ) : ℝ) ≤ (N : ℝ) / 2 ^ q := by
      have hcast : ((N / 2 ^ q : ℕ) : ℝ) ≤ (N : ℝ) / (2 ^ q : ℕ) :=
        Nat.cast_div_le
      rwa [Nat.cast_pow] at hcast
    have : ((N / 2 ^ q : ℕ) : ℝ) / N ≤ ((N : ℝ) / 2 ^ q) / N :=
      div_le_div_of_nonneg_right hdiv hN0.le
    have hsimp : ((N : ℝ) / 2 ^ q) / N = (1 : ℝ) / 2 ^ q := by
      field_simp [hN0.ne', hpow.ne']
    exact this.trans_eq hsimp
  exact herr.trans hle

/-! ### Passage to `weylCriterion` -/

/-- If every integer frequency admits arbitrarily tight uniform
truncations whose Cesàro means vanish, the orbit is Weyl-normal. -/
theorem weylCriterion_of_uniform_truncation {b : ℕ} {θ : ℝ}
    (h : ∀ τ : ℤ, τ ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → ℝ,
        (∀ n, |((b : ℝ) ^ n * θ) - U n| ≤ ε) ∧
        Tendsto (fun N : ℕ =>
          cesaroMean (fun n => e ((τ : ℝ) * U n)) N) atTop (nhds 0)) :
    weylCriterion b θ := by
  intro τ hτ
  refine Metric.tendsto_atTop.mpr fun δ hδ => ?_
  have hτ0 : (τ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hτ
  have hcoef : 0 < 2 * Real.pi * |(τ : ℝ)| := by positivity
  let ε : ℝ := (δ / 2) / (2 * Real.pi * |(τ : ℝ)|)
  have hε : 0 < ε := div_pos (half_pos hδ) hcoef
  obtain ⟨U, happrox, hU⟩ := h τ hτ ε hε
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hU (δ / 2) (half_pos hδ)
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right N0 1) hN
  have hNpos : 0 < N := Nat.succ_le_iff.mp hN1
  have htrunc :=
    cesaroMean_e_trunc τ (fun n => (b : ℝ) ^ n * θ) U happrox N hNpos
  have hεeq : 2 * Real.pi * |(τ : ℝ)| * ε = δ / 2 := by
    change 2 * Real.pi * |(τ : ℝ)| *
        ((δ / 2) / (2 * Real.pi * |(τ : ℝ)|)) = δ / 2
    field_simp [hcoef.ne']
  have hUclose :
      ‖cesaroMean (fun n => e ((τ : ℝ) * U n)) N - 0‖ < δ / 2 := by
    have := hN0 N (le_trans (le_max_left N0 1) hN)
    simpa [dist_eq_norm] using this
  have horb :
      cesaroMean (fun n => e ((τ : ℝ) * ((b : ℝ) ^ n * θ))) N =
        (∑ n ∈ range N, e ((τ : ℝ) * (b : ℝ) ^ n * θ)) / N := by
    unfold cesaroMean
    congr 1
    refine sum_congr rfl fun n _ => ?_
    simp [mul_assoc]
  have htri :
      dist ((∑ n ∈ range N, e ((τ : ℝ) * (b : ℝ) ^ n * θ)) / N) 0 < δ := by
    have hlip :
        ‖cesaroMean (fun n => e ((τ : ℝ) * ((b : ℝ) ^ n * θ))) N -
            cesaroMean (fun n => e ((τ : ℝ) * U n)) N‖ ≤ δ / 2 := by
      simpa [hεeq] using htrunc
    have hU' : ‖cesaroMean (fun n => e ((τ : ℝ) * U n)) N‖ < δ / 2 := by
      simpa [sub_zero] using hUclose
    have hnorm :
        ‖cesaroMean (fun n => e ((τ : ℝ) * ((b : ℝ) ^ n * θ))) N‖ < δ := by
      have hadd :=
        norm_add_le
          (cesaroMean (fun n => e ((τ : ℝ) * ((b : ℝ) ^ n * θ))) N -
            cesaroMean (fun n => e ((τ : ℝ) * U n)) N)
          (cesaroMean (fun n => e ((τ : ℝ) * U n)) N)
      have hrew :
          cesaroMean (fun n => e ((τ : ℝ) * ((b : ℝ) ^ n * θ))) N -
                cesaroMean (fun n => e ((τ : ℝ) * U n)) N +
              cesaroMean (fun n => e ((τ : ℝ) * U n)) N =
            cesaroMean (fun n => e ((τ : ℝ) * ((b : ℝ) ^ n * θ))) N := by
        abel
      rw [hrew] at hadd
      linarith
    simpa [horb, dist_eq_norm] using hnorm
  exact htri

end PrimeGapNormality.Prime
