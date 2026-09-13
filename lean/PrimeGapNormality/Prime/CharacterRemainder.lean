import PrimeGapNormality.Prime.Fourier
import PrimeGapNormality.Prime.GapPowerTail
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Bounded character remainder without real `1/d` powers

Paper remainder (R105/01 §3): if a positive-degree Fourier phase satisfies
`|Φ-Φ_L| ≤ ∑_d A_d s^d` with `A_d ≥ 0` and `1 ≤ d`, then

  `‖e(Φ)-e(Φ_L)‖ ≤ (2 + 2π ∑_d A_d) s`.

The comparison splits only on `s ≤ 1` versus `s ≥ 1`. No real root
`B^(1/d)` appears. Finite gap-power windows compare by natural powers
and `sum_pow_le_pow_sum`; the convergent series is the `N → ∞` limit.

Degree 0 is excluded: `s^0 = 1` would not force a vanishing remainder
at `s = 0`. This file does not average over `GapTailT`.

Source: `rounds/round105/01_gpt_endchain_audit.md` §3;
`rounds/round105/00_grok_repair_priorities.md` B.
Contract: API
Audit: GREEN
-/

open Finset

namespace PrimeGapNormality.Prime

/-! ### Circle-character Lipschitz (local; `Fourier.norm_e` is private) -/

private theorem two_pi_I_mul (x : ℝ) :
    (2 * Real.pi * Complex.I * (x : ℂ) : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) := by
  simp [mul_comm, mul_left_comm, Complex.ofReal_mul]

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem character_norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [two_pi_I_mul, Complex.norm_exp_I_mul_ofReal]

private theorem character_norm_e_sub_one_le (δ : ℝ) :
    ‖e δ - 1‖ ≤ 2 * Real.pi * |δ| := by
  unfold e
  rw [two_pi_I_mul]
  have hle := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * δ)
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg Real.pi_pos.le, mul_comm,
    mul_left_comm, mul_assoc] using hle

private theorem character_norm_e_sub_e (s t : ℝ) :
    ‖e t - e s‖ ≤ 2 * Real.pi * |t - s| := by
  have h : e t - e s = e s * (e (t - s) - 1) := by
    calc
      e t - e s = e ((t - s) + s) - e s := by rw [sub_add_cancel]
      _ = e (t - s) * e s - e s := by rw [e_add]
      _ = e s * (e (t - s) - 1) := by
        rw [mul_comm (e (t - s)), mul_sub, mul_one]
  rw [h, norm_mul, character_norm_e, one_mul]
  exact character_norm_e_sub_one_le (t - s)

private theorem two_pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi :=
  mul_nonneg (by norm_num) Real.pi_pos.le

private theorem character_norm_e_sub_le_two (u v : ℝ) : ‖e u - e v‖ ≤ 2 := by
  calc
    ‖e u - e v‖ ≤ ‖e u‖ + ‖e v‖ := norm_sub_le _ _
    _ = 1 + 1 := by rw [character_norm_e, character_norm_e]
    _ = 2 := by norm_num

/-! ### `s^d ≤ s` for `0 ≤ s ≤ 1` and positive degree -/

private theorem pow_le_self_of_le_one {s : ℝ} {d : ℕ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (hd : 1 ≤ d) : s ^ d ≤ s :=
  pow_le_of_le_one hs0 hs1 (Nat.succ_le_iff.mp hd).ne'

private theorem sum_mul_natPower_le_sum_mul {ι : Type*} (sA : Finset ι)
    (A : ι → ℝ) (d : ι → ℕ) {s : ℝ}
    (hA : ∀ i ∈ sA, 0 ≤ A i) (hd : ∀ i ∈ sA, 1 ≤ d i)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑ i ∈ sA, A i * s ^ d i ≤ (∑ i ∈ sA, A i) * s := by
  have hterm : ∀ i ∈ sA, A i * s ^ d i ≤ A i * s := fun i hi =>
    mul_le_mul_of_nonneg_left (pow_le_self_of_le_one hs0 hs1 (hd i hi)) (hA i hi)
  have hsum := sum_le_sum hterm
  have hfactor : ∑ i ∈ sA, A i * s = (∑ i ∈ sA, A i) * s := (sum_mul sA A s).symm
  exact hsum.trans_eq hfactor

/-! ### Character remainder (T2) -/

/-- Finset form of the bounded character remainder. Positive degrees only.

Source: `rounds/round105/01_gpt_endchain_audit.md` §3 (T2).
Contract: API
Audit: GREEN -/
theorem norm_e_sub_le_linear_of_natPower_bound_finset
    {ι : Type*} (sA : Finset ι) (A : ι → ℝ) (d : ι → ℕ) {s u v : ℝ}
    (hA : ∀ i ∈ sA, 0 ≤ A i) (hd : ∀ i ∈ sA, 1 ≤ d i) (hs : 0 ≤ s)
    (huv : |u - v| ≤ ∑ i ∈ sA, A i * s ^ d i) :
    ‖e u - e v‖ ≤ (2 + 2 * Real.pi * ∑ i ∈ sA, A i) * s := by
  have hA0 : 0 ≤ ∑ i ∈ sA, A i := sum_nonneg fun i hi => hA i hi
  have hπA : 0 ≤ 2 * Real.pi * ∑ i ∈ sA, A i := mul_nonneg two_pi_nonneg hA0
  have hrelax :
      (2 * Real.pi * ∑ i ∈ sA, A i) * s ≤
        (2 + 2 * Real.pi * ∑ i ∈ sA, A i) * s :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)) hs
  have hrelax2 :
      (2 : ℝ) * s ≤ (2 + 2 * Real.pi * ∑ i ∈ sA, A i) * s :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hπA) hs
  by_cases hs1 : s ≤ 1
  · have hsum := sum_mul_natPower_le_sum_mul sA A d hA hd hs hs1
    have huv' : |u - v| ≤ (∑ i ∈ sA, A i) * s := huv.trans hsum
    have hlip : ‖e u - e v‖ ≤ 2 * Real.pi * |u - v| :=
      character_norm_e_sub_e v u
    have hmid : 2 * Real.pi * |u - v| ≤ (2 * Real.pi * ∑ i ∈ sA, A i) * s := by
      have h1 : 2 * Real.pi * |u - v| ≤ 2 * Real.pi * ((∑ i ∈ sA, A i) * s) :=
        mul_le_mul_of_nonneg_left huv' two_pi_nonneg
      have h2 : 2 * Real.pi * ((∑ i ∈ sA, A i) * s) =
          (2 * Real.pi * ∑ i ∈ sA, A i) * s := by ring
      exact h1.trans_eq h2
    exact hlip.trans (hmid.trans hrelax)
  · have hs1' : 1 ≤ s := (not_le.mp hs1).le
    have h2s : (2 : ℝ) ≤ 2 * s := by
      have : (2 : ℝ) * 1 ≤ 2 * s :=
        mul_le_mul_of_nonneg_left hs1' (by norm_num)
      simpa using this
    exact (character_norm_e_sub_le_two u v).trans (h2s.trans hrelax2)

/-- Bounded character remainder for a finite family of positive natural
powers. If `|u-v| ≤ ∑_i A_i s^{d_i}` with `A_i ≥ 0` and `1 ≤ d_i`, then
`‖e u - e v‖ ≤ (2 + 2π ∑_i A_i) s`.

Source: `rounds/round105/01_gpt_endchain_audit.md` §3 (T2).
Contract: API
Audit: GREEN -/
theorem norm_e_sub_le_linear_of_natPower_bound
    {I : Type*} [Fintype I]
    {A : I → ℝ} {d : I → ℕ} {s u v : ℝ}
    (hA : ∀ i, 0 ≤ A i) (hd : ∀ i, 1 ≤ d i) (hs : 0 ≤ s)
    (huv : |u - v| ≤ ∑ i, A i * s ^ d i) :
    ‖e u - e v‖ ≤ (2 + 2 * Real.pi * ∑ i, A i) * s :=
  norm_e_sub_le_linear_of_natPower_bound_finset univ A d
    (fun i _ => hA i) (fun i _ => hd i) hs huv

/-- Paper form on degrees `{1,…,D}`.

Source: `rounds/round105/01_gpt_endchain_audit.md` §3 (T2).
Contract: API
Audit: GREEN -/
theorem norm_e_sub_le_linear_of_natPower_bound_Icc
    {A : ℕ → ℝ} {s u v : ℝ} {D : ℕ}
    (hA : ∀ k, 0 ≤ A k) (hs : 0 ≤ s)
    (huv : |u - v| ≤ ∑ k ∈ Icc 1 D, A k * s ^ k) :
    ‖e u - e v‖ ≤ (2 + 2 * Real.pi * ∑ k ∈ Icc 1 D, A k) * s :=
  norm_e_sub_le_linear_of_natPower_bound_finset (Icc 1 D) A id
    (fun k _ => hA k) (fun _ hk => (mem_Icc.mp hk).1) hs huv

/-! ### Finite `R_d ≤ s^d` by natural powers (T1) -/

private theorem rho_pos {ρ : ℝ} (hρ : 1 < ρ) : 0 < ρ :=
  lt_trans (by norm_num : (0 : ℝ) < 1) hρ

private theorem base_cast_pos {B : ℕ} (hB : 2 ≤ B) : (0 : ℝ) < B :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (Nat.cast_le.mpr hB)

private theorem base_cast_ne_zero {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) ≠ 0 :=
  (base_cast_pos hB).ne'

/-- `ρ^{d(j+1)} ≤ B^{j+1}` from `1 ≤ d ≤ D` and `ρ^D ≤ B`. Natural powers only. -/
private theorem rho_natPow_le_base_pow {ρ : ℝ} {B D d j : ℕ}
    (hρ : 1 < ρ) (hBD : ρ ^ D ≤ (B : ℝ)) (_hd : 1 ≤ d) (hdD : d ≤ D) :
    ρ ^ (d * (j + 1)) ≤ (B : ℝ) ^ (j + 1) := by
  have hρ0 : 0 ≤ ρ := (rho_pos hρ).le
  have hρ1 : 1 ≤ ρ := hρ.le
  have hmid : (ρ ^ d) ^ (j + 1) ≤ (ρ ^ D) ^ (j + 1) :=
    pow_le_pow_left₀ (pow_nonneg hρ0 _) (pow_le_pow_right₀ hρ1 hdD) (j + 1)
  have hright : (ρ ^ D) ^ (j + 1) ≤ (B : ℝ) ^ (j + 1) :=
    pow_le_pow_left₀ (pow_nonneg hρ0 _) hBD (j + 1)
  calc
    ρ ^ (d * (j + 1)) = (ρ ^ d) ^ (j + 1) := pow_mul _ _ _
    _ ≤ (ρ ^ D) ^ (j + 1) := hmid
    _ ≤ (B : ℝ) ^ (j + 1) := hright

/-- One-term comparison: `g^d / B^{j+1} ≤ (g / ρ^{j+1})^d`. -/
private theorem gapPow_term_le_linear_pow {ρ : ℝ} {B D d j : ℕ} {g : ℝ}
    (hρ : 1 < ρ) (_hB : 2 ≤ B) (hBD : ρ ^ D ≤ (B : ℝ))
    (hd : 1 ≤ d) (hdD : d ≤ D) (hg : 0 ≤ g) :
    g ^ d / (B : ℝ) ^ (j + 1) ≤ (g / ρ ^ (j + 1)) ^ d := by
  have hident : (g / ρ ^ (j + 1)) ^ d = g ^ d / ρ ^ (d * (j + 1)) := by
    rw [div_pow, ← pow_mul, mul_comm (j + 1) d]
  have hnn : 0 ≤ g ^ d := pow_nonneg hg d
  have hden : 0 < ρ ^ (d * (j + 1)) := pow_pos (rho_pos hρ) _
  have hle := rho_natPow_le_base_pow (j := j) hρ hBD hd hdD
  have hdiv :
      g ^ d / (B : ℝ) ^ (j + 1) ≤ g ^ d / ρ ^ (d * (j + 1)) :=
    div_le_div_of_nonneg_left hnn hden hle
  exact hdiv.trans_eq hident.symm

/-- Finite-set (T1): `∑ g_j^d B^{-(j+1)} ≤ (∑ g_j ρ^{-(j+1)})^d`.

Source: `rounds/round105/01_gpt_endchain_audit.md` §3 (T1).
Contract: API
Audit: GREEN -/
theorem sum_gapPow_le_pow_linear {ρ : ℝ} {B D d : ℕ}
    (s : Finset ℕ) (g : ℕ → ℝ)
    (hρ : 1 < ρ) (hB : 2 ≤ B) (hBD : ρ ^ D ≤ (B : ℝ))
    (hd : 1 ≤ d) (hdD : d ≤ D) (hg : ∀ j, 0 ≤ g j) :
    ∑ j ∈ s, g j ^ d / (B : ℝ) ^ (j + 1)
      ≤ (∑ j ∈ s, g j / ρ ^ (j + 1)) ^ d := by
  have hterm :
      ∀ j ∈ s, g j ^ d / (B : ℝ) ^ (j + 1) ≤ (g j / ρ ^ (j + 1)) ^ d :=
    fun j _ => gapPow_term_le_linear_pow hρ hB hBD hd hdD (hg j)
  have hsum := sum_le_sum hterm
  have hann : ∀ j ∈ s, 0 ≤ g j / ρ ^ (j + 1) := fun j _ =>
    div_nonneg (hg j) (pow_nonneg (rho_pos hρ).le _)
  exact hsum.trans (sum_pow_le_pow_sum s (fun j => g j / ρ ^ (j + 1)) hd hann)

/-- Finite remainder window `∑_{L ≤ j < H} g_{n+j}^d / B^{j+1}`.

Paper `R_{d,L}` includes the left endpoint `j = L`. This is not the
`Ioc` window of `gapPowerTailTrunc`. -/
noncomputable def gapPowerRemainderTrunc (g : ℕ → ℝ) (B d n L H : ℕ) : ℝ :=
  ∑ j ∈ Ico L H, g (n + j) ^ d / (B : ℝ) ^ (j + 1)

/-- Finite linear tail window matching `s_{n,L}` partial sums. -/
noncomputable def linearGapTailTrunc (ρ : ℝ) (g : ℕ → ℝ) (n L H : ℕ) : ℝ :=
  ∑ j ∈ Ico L H, g (n + j) / ρ ^ (j + 1)

/-- Finite (T1) on a paper remainder window.

Source: `rounds/round105/01_gpt_endchain_audit.md` §3 (T1).
Contract: API
Audit: GREEN -/
theorem gapPowerRemainderTrunc_le_pow_linearGapTailTrunc
    (g : ℕ → ℝ) {ρ : ℝ} {B D d : ℕ} (n L H : ℕ)
    (hρ : 1 < ρ) (hB : 2 ≤ B) (hBD : ρ ^ D ≤ (B : ℝ))
    (hd : 1 ≤ d) (hdD : d ≤ D) (hg : ∀ j, 0 ≤ g j) :
    gapPowerRemainderTrunc g B d n L H ≤ linearGapTailTrunc ρ g n L H ^ d :=
  sum_gapPow_le_pow_linear (Ico L H) (fun j => g (n + j))
    hρ hB hBD hd hdD (fun _ => hg _)

private theorem inv_mul_gapPowerTailTrunc_eq (g : ℕ → ℝ) {B L H : ℕ}
    (hB : 2 ≤ B) (d : ℕ) :
    (1 / (B : ℝ)) * gapPowerTailTrunc g B d L H =
      ∑ j ∈ Ioc L H, g j ^ d / (B : ℝ) ^ (j + 1) := by
  unfold gapPowerTailTrunc
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hB0 := base_cast_ne_zero hB
  have hj : (B : ℝ) ^ j ≠ 0 := pow_ne_zero j hB0
  rw [pow_succ]
  field_simp [hB0, hj] <;> ring

/-- `Ioc` form of (T1), matching `GapPowerTail.gapPowerTailTrunc` after `1/B`.

Source: `rounds/round105/01_gpt_endchain_audit.md` §3 (T1);
`GapPowerTail.gapPowerTailTrunc`.
Contract: API
Audit: GREEN -/
theorem inv_mul_gapPowerTailTrunc_le_pow_linear
    (g : ℕ → ℝ) {ρ : ℝ} {B D d L H : ℕ}
    (hρ : 1 < ρ) (hB : 2 ≤ B) (hBD : ρ ^ D ≤ (B : ℝ))
    (hd : 1 ≤ d) (hdD : d ≤ D) (hg : ∀ j, 0 ≤ g j) :
    (1 / (B : ℝ)) * gapPowerTailTrunc g B d L H
      ≤ (∑ j ∈ Ioc L H, g j / ρ ^ (j + 1)) ^ d := by
  rw [inv_mul_gapPowerTailTrunc_eq (d := d) g hB]
  exact sum_gapPow_le_pow_linear (Ioc L H) g hρ hB hBD hd hdD hg

/-! ### Convergent tails: `R_d ≤ s^d` -/

/-- Infinite remainder `R_{d,L}(n) = ∑_{j≥0} g_{n+L+j}^d / B^{L+j+1}`. -/
noncomputable def gapPowerRemainder (g : ℕ → ℝ) (B d n L : ℕ) : ℝ :=
  ∑' j : ℕ, g (n + L + j) ^ d / (B : ℝ) ^ (L + j + 1)

/-- Paper `s_{n,L} = ρ^{-L} T_ρ(n+L)` as a shifted linear tail. -/
noncomputable def scaledGapTail (ρ : ℝ) (g : ℕ → ℝ) (n L : ℕ) : ℝ :=
  (ρ ^ L)⁻¹ * ∑' j : ℕ, g (n + L + j) / ρ ^ (j + 1)

private theorem linear_term_shift {ρ : ℝ} (hρ : 1 < ρ) (g : ℕ → ℝ)
    (n L j : ℕ) :
    g (n + L + j) / ρ ^ (L + j + 1) =
      (ρ ^ L)⁻¹ * (g (n + L + j) / ρ ^ (j + 1)) := by
  have hρ0 : ρ ≠ 0 := (rho_pos hρ).ne'
  have hL : ρ ^ L ≠ 0 := pow_ne_zero L hρ0
  have hj : ρ ^ (j + 1) ≠ 0 := pow_ne_zero _ hρ0
  rw [add_assoc, pow_add]
  field_simp [hL, hj] <;> ring

private theorem gapPowerRemainderTrunc_sum_range (g : ℕ → ℝ)
    (B d n L N : ℕ) :
    gapPowerRemainderTrunc g B d n L (L + N) =
      ∑ k ∈ range N, g (n + L + k) ^ d / (B : ℝ) ^ (L + k + 1) := by
  unfold gapPowerRemainderTrunc
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine sum_congr rfl fun k _ => ?_
  simp only [add_assoc]

private theorem linearGapTailTrunc_sum_range (ρ : ℝ) (g : ℕ → ℝ)
    (n L N : ℕ) :
    linearGapTailTrunc ρ g n L (L + N) =
      ∑ k ∈ range N, g (n + L + k) / ρ ^ (L + k + 1) := by
  unfold linearGapTailTrunc
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine sum_congr rfl fun k _ => ?_
  simp only [add_assoc]

private theorem summable_linear_shift {ρ : ℝ} {g : ℕ → ℝ} {n L : ℕ}
    (hρ : 1 < ρ)
    (hsm : Summable fun j : ℕ => g (n + L + j) / ρ ^ (j + 1)) :
    Summable fun j : ℕ => g (n + L + j) / ρ ^ (L + j + 1) := by
  have hfun :
      (fun j : ℕ => (ρ ^ L)⁻¹ * (g (n + L + j) / ρ ^ (j + 1))) =
        fun j => g (n + L + j) / ρ ^ (L + j + 1) :=
    funext fun j => (linear_term_shift hρ g n L j).symm
  exact hfun ▸ hsm.mul_left (ρ ^ L)⁻¹

theorem scaledGapTail_eq_linear_tsum {ρ : ℝ} {g : ℕ → ℝ} {n L : ℕ}
    (hρ : 1 < ρ)
    (hsm : Summable fun j : ℕ => g (n + L + j) / ρ ^ (j + 1)) :
    scaledGapTail ρ g n L =
      ∑' j : ℕ, g (n + L + j) / ρ ^ (L + j + 1) := by
  unfold scaledGapTail
  rw [← hsm.tsum_mul_left]
  refine tsum_congr fun j => ?_
  exact (linear_term_shift hρ g n L j).symm

/-- Infinite (T1): `R_{d,L}(n) ≤ s_{n,L}^d` after the finite comparison.

Source: `rounds/round105/01_gpt_endchain_audit.md` §3 (T1).
Contract: API
Audit: GREEN -/
theorem gapPowerRemainder_le_pow_scaledGapTail
    (g : ℕ → ℝ) {ρ : ℝ} {B D d n L : ℕ}
    (hρ : 1 < ρ) (hB : 2 ≤ B) (hBD : ρ ^ D ≤ (B : ℝ))
    (hd : 1 ≤ d) (hdD : d ≤ D) (hg : ∀ j, 0 ≤ g j)
    (hsm : Summable fun j : ℕ => g (n + L + j) / ρ ^ (j + 1)) :
    gapPowerRemainder g B d n L ≤ scaledGapTail ρ g n L ^ d := by
  set rem : ℕ → ℝ := fun k =>
    g (n + L + k) ^ d / (B : ℝ) ^ (L + k + 1)
  set lin : ℕ → ℝ := fun k =>
    g (n + L + k) / ρ ^ (L + k + 1)
  have hrem0 : ∀ k, 0 ≤ rem k := fun k =>
    div_nonneg (pow_nonneg (hg _) _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hlin0 : ∀ k, 0 ≤ lin k := fun k =>
    div_nonneg (hg _) (pow_nonneg (rho_pos hρ).le _)
  have hsmLin := summable_linear_shift hρ hsm
  have hsEq := scaledGapTail_eq_linear_tsum (g := g) (n := n) (L := L) hρ hsm
  have hbound : ∀ N : ℕ, ∑ k ∈ range N, rem k ≤ scaledGapTail ρ g n L ^ d := by
    intro N
    have htrunc :=
      gapPowerRemainderTrunc_le_pow_linearGapTailTrunc g (n : ℕ) (L : ℕ) (L + N)
        hρ hB hBD hd hdD hg
    have hReq := gapPowerRemainderTrunc_sum_range g B d n L N
    have hLeq := linearGapTailTrunc_sum_range ρ g n L N
    have hlin_le :
        ∑ k ∈ range N, lin k ≤ ∑' k : ℕ, lin k :=
      hsmLin.sum_le_tsum (range N) fun k _ => hlin0 k
    have htrunc_le :
        linearGapTailTrunc ρ g n L (L + N) ≤ scaledGapTail ρ g n L := by
      rw [hLeq, hsEq]
      exact hlin_le
    have hnn : 0 ≤ linearGapTailTrunc ρ g n L (L + N) :=
      sum_nonneg fun j _ =>
        div_nonneg (hg _) (pow_nonneg (rho_pos hρ).le _)
    have hpow := pow_le_pow_left₀ hnn htrunc_le d
    rw [← hReq]
    exact htrunc.trans hpow
  change ∑' k : ℕ, rem k ≤ scaledGapTail ρ g n L ^ d
  exact Real.tsum_le_of_sum_range_le hrem0 hbound

end PrimeGapNormality.Prime
