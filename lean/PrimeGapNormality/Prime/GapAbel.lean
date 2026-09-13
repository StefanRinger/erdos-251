import PrimeGapNormality.Prime.RankDelete
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Periodic gap Abel identity and max-norm non-cancellation

Finite identity (paper 1-based, Lean `range N` for `n = 1..N`):

`∑_{n=1}^{N} c_n a_n B^{-n}
  = a_1 d_0 + ∑_{j=1}^{N-1} d_j g_j B^{-j} - a_N d_N B^{-N}`

under the recurrence `c_{j+1} = B d_j - d_{j+1}`. The periodic weight

`d_j = (∑_{ℓ=1}^{k} c_{j+ℓ} B^{k-ℓ}) / (B^k - 1)`

inverts the recurrence on `k`-periodic sequences. Max-norm: for a
maximizer `r` on residues `1..k`, both signs satisfy
`|a_r ± a_{r+1}/B| ≥ (1-1/B) |a_r|`. No determinant, no cycle proof.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` (11.2);
`rounds/round103/03_grok_gap_polynomial_implementation_update.md` P1.C.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Function

set_option maxHeartbeats 800000

private theorem base_cast_ne_zero {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

private theorem base_pow_sub_one_ne_zero {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) :
    (B : ℝ) ^ k - 1 ≠ 0 := by
  have hBpos : (1 : ℝ) < B :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : 1 < 2) hB)
  have hpow : (1 : ℝ) < (B : ℝ) ^ k := one_lt_pow₀ hBpos (Nat.pos_iff_ne_zero.mp hk)
  exact sub_ne_zero.mpr hpow.ne'

private theorem periodic_add {α : Type*} {f : ℕ → α} {k x y : ℕ}
    (hf : Periodic f k) (hxy : x = y + k) : f x = f y := by
  rw [hxy]
  exact hf y

/-- Recurrence weight `c_{j+1} = B d_j - d_{j+1}`.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` (11.1).
Contract: API
Audit: GREEN -/
noncomputable def recGapWeight (B : ℕ) (d : ℕ → ℝ) (j : ℕ) : ℝ :=
  (B : ℝ) * d j - d (j + 1)

/-- Periodic Abel weight `d_j`. Lean sum `ℓ ∈ range k` is paper `ℓ = 1..k`.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` (11.1).
Contract: API
Audit: GREEN -/
noncomputable def periodicGapWeight (c : ℕ → ℝ) (B k j : ℕ) : ℝ :=
  (∑ ℓ ∈ range k, c (j + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ)) / ((B : ℝ) ^ k - 1)

/-- Numerator of `periodicGapWeight` (undivided cyclic sum). -/
noncomputable def periodicGapWeightNum (c : ℕ → ℝ) (B k j : ℕ) : ℝ :=
  ∑ ℓ ∈ range k, c (j + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ)

theorem periodicGapWeight_eq_div (c : ℕ → ℝ) (B k j : ℕ) :
    periodicGapWeight c B k j =
      periodicGapWeightNum c B k j / ((B : ℝ) ^ k - 1) :=
  rfl

/-- Finite Abel identity with terminal remainder. Lean `i ∈ range N` is
paper index `n = i+1`. Gaps are `g_j = a_{j+1} - a_j`.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` (11.2).
Contract: API
Audit: GREEN -/
theorem finite_gap_abel {B : ℕ} (hB : 2 ≤ B) (a d : ℕ → ℝ) {N : ℕ}
    (hN : 1 ≤ N) :
    ∑ i ∈ range N,
        recGapWeight B d i * a (i + 1) / (B : ℝ) ^ (i + 1) =
      a 1 * d 0 +
        ∑ i ∈ range (N - 1),
          d (i + 1) * (a (i + 2) - a (i + 1)) / (B : ℝ) ^ (i + 1) -
        a N * d N / (B : ℝ) ^ N := by
  have hb0 := base_cast_ne_zero hB
  have hterm (i : ℕ) :
      recGapWeight B d i * a (i + 1) / (B : ℝ) ^ (i + 1) =
        d i * a (i + 1) / (B : ℝ) ^ i -
          d (i + 1) * a (i + 1) / (B : ℝ) ^ (i + 1) := by
    unfold recGapWeight
    have hpow : (B : ℝ) ^ (i + 1) = (B : ℝ) ^ i * B := pow_succ _ _
    have hbpow : (B : ℝ) ^ i ≠ 0 := pow_ne_zero i hb0
    field_simp [hb0, hbpow, hpow]
    ring
  have hsplit :
      ∑ i ∈ range N, recGapWeight B d i * a (i + 1) / (B : ℝ) ^ (i + 1) =
        ∑ i ∈ range N, d i * a (i + 1) / (B : ℝ) ^ i -
          ∑ i ∈ range N, d (i + 1) * a (i + 1) / (B : ℝ) ^ (i + 1) := by
    simp_rw [hterm]
    rw [sum_sub_distrib]
  have hnrew : N = N - 1 + 1 := (Nat.sub_add_cancel hN).symm
  have hhead :
      ∑ i ∈ range N, d i * a (i + 1) / (B : ℝ) ^ i =
        d 0 * a 1 +
          ∑ i ∈ range (N - 1), d (i + 1) * a (i + 2) / (B : ℝ) ^ (i + 1) := by
    conv_lhs => rw [hnrew]
    rw [sum_range_succ' (fun i => d i * a (i + 1) / (B : ℝ) ^ i) (N - 1)]
    rw [pow_zero, div_one, add_comm]
  have htail :
      ∑ i ∈ range N, d (i + 1) * a (i + 1) / (B : ℝ) ^ (i + 1) =
        ∑ i ∈ range (N - 1), d (i + 1) * a (i + 1) / (B : ℝ) ^ (i + 1) +
          d N * a N / (B : ℝ) ^ N := by
    conv_lhs => rw [hnrew]
    rw [sum_range_succ (fun i => d (i + 1) * a (i + 1) / (B : ℝ) ^ (i + 1))
      (N - 1), Nat.sub_add_cancel hN]
  have hcomb :
      ∑ i ∈ range (N - 1), d (i + 1) * a (i + 2) / (B : ℝ) ^ (i + 1) -
          ∑ i ∈ range (N - 1), d (i + 1) * a (i + 1) / (B : ℝ) ^ (i + 1) =
        ∑ i ∈ range (N - 1),
          d (i + 1) * (a (i + 2) - a (i + 1)) / (B : ℝ) ^ (i + 1) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, hhead, htail]
  have hrearr :
      d 0 * a 1 +
          ∑ i ∈ range (N - 1), d (i + 1) * a (i + 2) / (B : ℝ) ^ (i + 1) -
          (∑ i ∈ range (N - 1), d (i + 1) * a (i + 1) / (B : ℝ) ^ (i + 1) +
            d N * a N / (B : ℝ) ^ N) =
        a 1 * d 0 +
          (∑ i ∈ range (N - 1), d (i + 1) * a (i + 2) / (B : ℝ) ^ (i + 1) -
            ∑ i ∈ range (N - 1), d (i + 1) * a (i + 1) / (B : ℝ) ^ (i + 1)) -
          a N * d N / (B : ℝ) ^ N := by
    ring
  rw [hrearr, hcomb]

private theorem periodicGapWeightNum_succ_zero {B k m : ℕ} (hk : 1 ≤ k)
    (c : ℕ → ℝ) :
    periodicGapWeightNum c B k m =
      c (m + 1) * (B : ℝ) ^ (k - 1) +
        ∑ ℓ ∈ range (k - 1), c (m + ℓ + 2) * (B : ℝ) ^ (k - 2 - ℓ) := by
  unfold periodicGapWeightNum
  have hrange : range k = range (k - 1 + 1) := by rw [Nat.sub_add_cancel hk]
  rw [hrange, sum_range_succ' (fun ℓ => c (m + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ))
    (k - 1), add_comm]
  have hzero : m + 0 + 1 = m + 1 := by omega
  have hexp0 : k - 1 - 0 = k - 1 := by omega
  rw [hzero, hexp0]
  refine congrArg (c (m + 1) * (B : ℝ) ^ (k - 1) + ·) (sum_congr rfl fun ℓ hl => ?_)
  have hℓ : ℓ < k - 1 := mem_range.mp hl
  have hexp : k - 1 - (ℓ + 1) = k - 2 - ℓ := by omega
  have hidx : m + (ℓ + 1) + 1 = m + ℓ + 2 := by omega
  rw [hexp, hidx]

private theorem periodicGapWeightNum_succ_last {B k j : ℕ} (hk : 1 ≤ k)
    (c : ℕ → ℝ) :
    periodicGapWeightNum c B k (j + 1) =
      ∑ ℓ ∈ range (k - 1), c (j + ℓ + 2) * (B : ℝ) ^ (k - 1 - ℓ) +
        c (j + k + 1) := by
  unfold periodicGapWeightNum
  have hrange : range k = range (k - 1 + 1) := by rw [Nat.sub_add_cancel hk]
  rw [hrange, sum_range_succ (fun ℓ => c (j + 1 + ℓ + 1) * (B : ℝ) ^ (k - 1 - ℓ))
    (k - 1)]
  have hlast_idx : j + 1 + (k - 1) + 1 = j + k + 1 := by omega
  have hlast_exp : k - 1 - (k - 1) = 0 := Nat.sub_self _
  rw [hlast_idx, hlast_exp, pow_zero, mul_one]
  refine congrArg (· + c (j + k + 1)) (sum_congr rfl fun ℓ _ => ?_)
  have : j + 1 + ℓ + 1 = j + ℓ + 2 := by omega
  rw [this]

private theorem periodicGapWeightNum_mul_base {B k j : ℕ} (hk : 1 ≤ k)
    (c : ℕ → ℝ) :
    (B : ℝ) * periodicGapWeightNum c B k j =
      c (j + 1) * (B : ℝ) ^ k +
        ∑ ℓ ∈ range (k - 1), c (j + ℓ + 2) * (B : ℝ) ^ (k - 1 - ℓ) := by
  rw [periodicGapWeightNum_succ_zero hk, mul_add, mul_sum]
  have hpow : (B : ℝ) * (B : ℝ) ^ (k - 1) = (B : ℝ) ^ k := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hk]
  congr 1
  · calc
      (B : ℝ) * (c (j + 1) * (B : ℝ) ^ (k - 1))
        = c (j + 1) * ((B : ℝ) * (B : ℝ) ^ (k - 1)) := by ring
      _ = c (j + 1) * (B : ℝ) ^ k := by rw [hpow]
  · refine sum_congr rfl fun ℓ hl => ?_
    have hℓ : ℓ < k - 1 := mem_range.mp hl
    have hexp : k - 1 - ℓ = k - 2 - ℓ + 1 := by omega
    calc
      (B : ℝ) * (c (j + ℓ + 2) * (B : ℝ) ^ (k - 2 - ℓ))
        = c (j + ℓ + 2) * ((B : ℝ) * (B : ℝ) ^ (k - 2 - ℓ)) := by ring
      _ = c (j + ℓ + 2) * (B : ℝ) ^ (k - 1 - ℓ) := by
          rw [hexp, pow_succ]
          ring

/-- The periodic weight inverts the recurrence.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` (11.1).
Contract: API
Audit: GREEN -/
theorem periodicGapWeight_rec {B k j : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (c : ℕ → ℝ) (hc : Periodic c k) :
    recGapWeight B (periodicGapWeight c B k) j = c (j + 1) := by
  have hden := base_pow_sub_one_ne_zero hB hk
  have hper : c (j + k + 1) = c (j + 1) :=
    periodic_add hc (by omega)
  have hnum :
      (B : ℝ) * periodicGapWeightNum c B k j -
          periodicGapWeightNum c B k (j + 1) =
        c (j + 1) * ((B : ℝ) ^ k - 1) := by
    rw [periodicGapWeightNum_mul_base hk, periodicGapWeightNum_succ_last hk, hper]
    ring
  unfold recGapWeight
  rw [periodicGapWeight_eq_div, periodicGapWeight_eq_div]
  have hquot :
      (B : ℝ) * (periodicGapWeightNum c B k j / ((B : ℝ) ^ k - 1)) -
          periodicGapWeightNum c B k (j + 1) / ((B : ℝ) ^ k - 1) =
        ((B : ℝ) * periodicGapWeightNum c B k j -
          periodicGapWeightNum c B k (j + 1)) / ((B : ℝ) ^ k - 1) := by
    field_simp [hden]
  rw [hquot, hnum]
  exact mul_div_cancel_right₀ _ hden

theorem periodicGapWeight_periodic (c : ℕ → ℝ) (B k j : ℕ)
    (hc : Periodic c k) :
    periodicGapWeight c B k (j + k) = periodicGapWeight c B k j := by
  unfold periodicGapWeight
  refine congrArg (· / ((B : ℝ) ^ k - 1)) (sum_congr rfl fun ℓ _ => ?_)
  have : c (j + k + ℓ + 1) = c (j + ℓ + 1) :=
    periodic_add hc (by omega)
  rw [this]

/-- Nonzero periodic position weights give nonzero periodic gap weights.

Source: `rounds/round103/01_gpt_gap_polynomial_normality.md` §11.1.
Contract: API
Audit: GREEN -/
theorem periodicGapWeight_exists_ne_zero {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (c : ℕ → ℝ) (hc : Periodic c k)
    (hc0 : ∃ n ∈ Icc 1 k, c n ≠ 0) :
    ∃ j, periodicGapWeight c B k j ≠ 0 := by
  by_contra h
  have hzero : ∀ j, periodicGapWeight c B k j = 0 := fun j =>
    by_contra fun hj => h ⟨j, hj⟩
  obtain ⟨n, hn, hcn⟩ := hc0
  have hrec := periodicGapWeight_rec (B := B) (k := k) (j := n - 1) hB hk c hc
  have hrec0 : recGapWeight B (periodicGapWeight c B k) (n - 1) = 0 := by
    unfold recGapWeight
    simp [hzero]
  rw [hrec, Nat.sub_add_cancel (mem_Icc.mp hn).1] at hrec0
  exact hcn hrec0

private theorem abs_add_ge_sub (x y : ℝ) : |x| - |y| ≤ |x + y| := by
  have h : |x| ≤ |x + y| + |y| := by
    simpa [abs_neg, add_neg_cancel_right] using abs_add_le (x + y) (-y)
  linarith

private theorem abs_next_le_of_max {k r : ℕ} (hk : 1 ≤ k) (a : ℕ → ℝ)
    (ha : Periodic a k) (hr : r ∈ Icc 1 k)
    (hmax : ∀ i ∈ Icc 1 k, |a i| ≤ |a r|) :
    |a (r + 1)| ≤ |a r| := by
  have hrcc := mem_Icc.mp hr
  by_cases hlt : r < k
  · have hr1 : r + 1 ∈ Icc 1 k := by
      rw [mem_Icc] at hr ⊢
      omega
    exact hmax _ hr1
  · have hrk : r = k := le_antisymm hrcc.2 (le_of_not_gt hlt)
    have h1 : 1 ∈ Icc 1 k := mem_Icc.mpr ⟨le_rfl, hk⟩
    have : a (r + 1) = a 1 := by
      rw [hrk]
      exact periodic_add ha (by omega)
    rw [this]
    exact hmax 1 h1

/-- Max-norm two-term bound: both signs, any maximizer. Paper (6.1).

Source: `rounds/round103/02_gpt_gap_polynomial_second_read.md` (6.1);
`rounds/round103/03_grok_gap_polynomial_implementation_update.md` P1.C.
Contract: API
Audit: GREEN -/
theorem maxNorm_twoTerm_ge {B k r : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (a : ℕ → ℝ) (ha : Periodic a k) (hr : r ∈ Icc 1 k)
    (hmax : ∀ i ∈ Icc 1 k, |a i| ≤ |a r|) :
    (1 - (1 : ℝ) / B) * |a r| ≤ |a r + a (r + 1) / B| ∧
      (1 - (1 : ℝ) / B) * |a r| ≤ |a r - a (r + 1) / B| := by
  have hBpos : (0 : ℝ) < B :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (Nat.cast_le.mpr hB)
  have hnext := abs_next_le_of_max hk a ha hr hmax
  have hscale : |a (r + 1) / B| ≤ |a r| / B := by
    rw [abs_div, abs_of_pos hBpos]
    exact div_le_div_of_nonneg_right hnext hBpos.le
  have hfac : (1 - (1 : ℝ) / B) * |a r| = |a r| - |a r| / B := by ring
  refine ⟨?_, ?_⟩
  · rw [hfac]
    have hle : |a r| - |a r| / B ≤ |a r| - |a (r + 1) / B| := by linarith [hscale]
    exact hle.trans (abs_add_ge_sub (a r) (a (r + 1) / B))
  · rw [hfac, sub_eq_add_neg]
    have hle : |a r| - |a r| / B ≤ |a r| - |-(a (r + 1) / B)| := by
      simpa [abs_neg] using (by linarith [hscale] :
        |a r| - |a r| / B ≤ |a r| - |a (r + 1) / B|)
    exact hle.trans (abs_add_ge_sub (a r) (-(a (r + 1) / B)))

theorem exists_maxNorm_residue {k : ℕ} (hk : 1 ≤ k) (a : ℕ → ℝ) :
    ∃ r ∈ Icc 1 k, ∀ i ∈ Icc 1 k, |a i| ≤ |a r| :=
  exists_max_image (Icc 1 k) (fun i => |a i|) (nonempty_Icc.mpr hk)

/-- If the max residue mass is positive, a two-term gap coefficient is
strictly nonzero.

Source: `rounds/round103/02_gpt_gap_polynomial_second_read.md` (6.1).
Contract: API
Audit: GREEN -/
theorem maxNorm_twoTerm_ne_zero {B k r : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (a : ℕ → ℝ) (ha : Periodic a k) (hr : r ∈ Icc 1 k)
    (hmax : ∀ i ∈ Icc 1 k, |a i| ≤ |a r|) (hM : a r ≠ 0) :
    a r + a (r + 1) / B ≠ 0 ∧ a r - a (r + 1) / B ≠ 0 := by
  have hB1 : (1 : ℝ) < B :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : 1 < 2) hB)
  have hfac : 0 < 1 - (1 : ℝ) / B := by
    have : (1 : ℝ) / B < 1 :=
      (div_lt_one (lt_trans (by norm_num : (0 : ℝ) < 1) hB1)).mpr hB1
    linarith
  have hpos : 0 < (1 - (1 : ℝ) / B) * |a r| :=
    mul_pos hfac (abs_pos.mpr hM)
  obtain ⟨h1, h2⟩ := maxNorm_twoTerm_ge hB hk a ha hr hmax
  exact ⟨abs_pos.mp (hpos.trans_le h1), abs_pos.mp (hpos.trans_le h2)⟩

end PrimeGapNormality.Prime
