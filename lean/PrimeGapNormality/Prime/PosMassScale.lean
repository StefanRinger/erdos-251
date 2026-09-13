import PrimeGapNormality.Prime.TailMass
import PrimeGapNormality.Prime.PrimeSeries
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Scale of the prime position mass `F_ρ(n)`

Paper T wants `F_ρ(n) ≪_ρ p_n`, so that `F/m_X ≪ G` if `m_X ≍ X/G`.
This module does **not** claim that density, and it does **not** claim
`F_ρ(n) ≪_ρ p_n`. Chebyshev inversion `p_n ≤ 144 (n+1)^2` still yields
only `F_ρ(n) = O_ρ(n^2)`.

What compiles:

1. Geometric domination
   `∑_j (n+j+1)^2 ρ^{-j-1} = O_ρ(n^2)` with explicit coefficient
   `ρ(ρ+1)/(ρ-1)^3`, which is `O(1/(ρ-1)^3)` as `ρ ↓ 1`.
2. Comparison `F_ρ(n) ≤ 144 ∑_j (n+j+1)^2 ρ^{-j-1}`.
3. Exact Abel scale `F_ρ(n) = (p_n + T_ρ(n))/(ρ-1)`. Hence
   `p_n/(ρ-1) ≤ F_ρ(n)` and `F_ρ ≪_ρ p_n` reduces to `T_ρ ≪_ρ p_n`.
4. Head/tail split `F_ρ(n) = F^{<J}(n) + ρ^{-J} F_ρ(n+J)`, with the
   finite head controlled by `p_{n+J}` and the tail by the polynomial
   geometric bound.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` after `lem:tailmass`;
`TailMass`; `PrimeSeries.nthPrime_le_succ_sq`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 800000

private theorem rho_pos {ρ : ℝ} (hρ : 1 < ρ) : 0 < ρ :=
  lt_trans (by norm_num) hρ

private theorem rho_ne_zero {ρ : ℝ} (hρ : 1 < ρ) : ρ ≠ 0 :=
  (rho_pos hρ).ne'

private theorem rho_sub_one_pos {ρ : ℝ} (hρ : 1 < ρ) : 0 < ρ - 1 :=
  sub_pos.mpr hρ

private theorem rho_sub_one_ne_zero {ρ : ℝ} (hρ : 1 < ρ) : ρ - 1 ≠ 0 :=
  (rho_sub_one_pos hρ).ne'

private theorem inv_rho_nonneg {ρ : ℝ} (hρ : 1 < ρ) : 0 ≤ ρ⁻¹ :=
  inv_nonneg.mpr (rho_pos hρ).le

private theorem inv_rho_lt_one {ρ : ℝ} (hρ : 1 < ρ) : ρ⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ hρ

private theorem inv_rho_ne_one {ρ : ℝ} (hρ : 1 < ρ) : ρ⁻¹ ≠ 1 :=
  (inv_rho_lt_one hρ).ne

private theorem inv_rho_norm_lt_one {ρ : ℝ} (hρ : 1 < ρ) : ‖ρ⁻¹‖ < 1 := by
  rw [norm_inv, Real.norm_eq_abs, abs_of_pos (rho_pos hρ)]
  exact inv_rho_lt_one hρ

private theorem one_sub_inv_rho {ρ : ℝ} (hρ : 1 < ρ) :
    (1 : ℝ) - ρ⁻¹ = (ρ - 1) / ρ := by
  have h0 := rho_ne_zero hρ
  rw [inv_eq_one_div]
  field_simp [h0]

private theorem one_sub_inv_rho_ne {ρ : ℝ} (hρ : 1 < ρ) : (1 : ℝ) - ρ⁻¹ ≠ 0 :=
  sub_ne_zero.mpr (inv_rho_lt_one hρ).ne'

private theorem div_pow_succ {ρ : ℝ} (hρ : 1 < ρ) (A : ℝ) (j : ℕ) :
    A / ρ ^ (j + 1) = (A / ρ) * ρ⁻¹ ^ j := by
  have h0 := rho_ne_zero hρ
  rw [pow_succ, div_mul_eq_div_div, div_eq_mul_inv, inv_pow]
  field_simp [h0]

private theorem two_mul_choose_two (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    have hdiv : 2 ∣ (n + 1) * n := by
      simpa [Nat.mul_comm] using Nat.two_dvd_mul_add_one n
    rw [Nat.choose_two_right, Nat.succ_sub_one, Nat.mul_div_cancel' hdiv]

private theorem nat_sq_eq_choose (j : ℕ) :
    (j : ℝ) ^ 2 = 2 * ((j + 2).choose 2 : ℝ) - 3 * (j : ℝ) - 2 := by
  have hN : 2 * (j + 2).choose 2 = (j + 2) * (j + 1) := by
    simpa using two_mul_choose_two (j + 2)
  have hL : (2 : ℝ) * ((j + 2).choose 2 : ℝ) =
      ((j + 2 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast hN
  have hR : ((j + 2 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) =
      (j : ℝ) ^ 2 + 3 * (j : ℝ) + 2 := by
    have hj2 : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by simp
    have hj1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by simp
    rw [hj2, hj1]
    ring
  linarith

private theorem nthPrime_cast_le_succ_sq (k : ℕ) :
    (nthPrime k : ℝ) ≤ 144 * ((k + 1 : ℕ) : ℝ) ^ 2 := by
  have := nthPrime_le_succ_sq k
  have hcast :
      ((144 * (k + 1) ^ 2 : ℕ) : ℝ) = 144 * ((k + 1 : ℕ) : ℝ) ^ 2 := by
    simp [Nat.cast_mul, Nat.cast_pow]
  exact (Nat.cast_le.mpr this).trans_eq hcast

private theorem one_le_succ_cast (n : ℕ) : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
  exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))

/-- `n+1 ≤ p_n` from `p_n ≥ n+2`. -/
theorem succ_le_nthPrime (n : ℕ) : n + 1 ≤ nthPrime n :=
  (Nat.le_succ (n + 1)).trans (nthPrime_ge_add_two n)

/-! ### Geometric moments with explicit `(ρ-1)^{-3}` coefficient -/

/-- Explicit factor in `∑_j (n+j+1)^2 ρ^{-j-1} ≤ C(ρ) (n+1)^2`.
Equals `1/(ρ-1) + 2/(ρ-1)^2 + (ρ+1)/(ρ-1)^3`, hence
`O(1/(ρ-1)^3)` as `ρ ↓ 1`. -/
noncomputable def posMassGeomCoeff (ρ : ℝ) : ℝ :=
  ρ * (ρ + 1) / (ρ - 1) ^ 3

theorem posMassGeomCoeff_nonneg {ρ : ℝ} (hρ : 1 < ρ) : 0 ≤ posMassGeomCoeff ρ := by
  unfold posMassGeomCoeff
  have hpos := rho_sub_one_pos hρ
  positivity

theorem posMassGeomCoeff_eq_parts {ρ : ℝ} (hρ : 1 < ρ) :
    posMassGeomCoeff ρ =
      1 / (ρ - 1) + 2 / (ρ - 1) ^ 2 + (ρ + 1) / (ρ - 1) ^ 3 := by
  unfold posMassGeomCoeff
  have hd := rho_sub_one_ne_zero hρ
  field_simp [hd]
  ring

/-- Combined Chebyshev–geometric coefficient: `F_ρ(n) ≤ C(ρ) (n+1)^2`. -/
noncomputable def posMassScaleCoeff (ρ : ℝ) : ℝ :=
  144 * posMassGeomCoeff ρ

theorem posMassScaleCoeff_nonneg {ρ : ℝ} (hρ : 1 < ρ) : 0 ≤ posMassScaleCoeff ρ :=
  mul_nonneg (by norm_num : (0 : ℝ) ≤ 144) (posMassGeomCoeff_nonneg hρ)

theorem tsum_one_div_pow_succ {ρ : ℝ} (hρ : 1 < ρ) :
    ∑' j : ℕ, (1 : ℝ) / ρ ^ (j + 1) = 1 / (ρ - 1) := by
  have hfun :
      (fun j : ℕ => (1 : ℝ) / ρ ^ (j + 1)) = fun j : ℕ => ρ⁻¹ * ρ⁻¹ ^ j := by
    funext j
    rw [div_pow_succ hρ (1 : ℝ) j, one_div]
  have hgeo := tsum_geometric_of_lt_one (inv_rho_nonneg hρ) (inv_rho_lt_one hρ)
  rw [hfun, tsum_mul_left, hgeo, one_sub_inv_rho hρ]
  have h0 := rho_ne_zero hρ
  have hd := rho_sub_one_ne_zero hρ
  field_simp [h0, hd]

theorem tsum_nat_div_pow_succ {ρ : ℝ} (hρ : 1 < ρ) :
    ∑' j : ℕ, (j : ℝ) / ρ ^ (j + 1) = 1 / (ρ - 1) ^ 2 := by
  set r : ℝ := ρ⁻¹
  have hr := inv_rho_norm_lt_one hρ
  have hfun :
      (fun j : ℕ => (j : ℝ) / ρ ^ (j + 1)) =
        fun j : ℕ => r * ((j : ℝ) * r ^ j) := by
    funext j
    calc
      (j : ℝ) / ρ ^ (j + 1) = ((j : ℝ) / ρ) * r ^ j :=
        div_pow_succ hρ (j : ℝ) j
      _ = r * ((j : ℝ) * r ^ j) := by
          rw [div_eq_mul_inv]
          ring
  have hnat : ∑' j : ℕ, (j : ℝ) * r ^ j = r / (1 - r) ^ 2 := by
    simpa using tsum_coe_mul_geometric_of_norm_lt_one (r := r) hr
  rw [hfun, tsum_mul_left, hnat]
  have hd := one_sub_inv_rho_ne hρ
  have h0 := rho_ne_zero hρ
  have hρd := rho_sub_one_ne_zero hρ
  simp only [r, one_sub_inv_rho hρ]
  field_simp [h0, hρd, hd]

private theorem tsum_sq_mul_inv_rho {ρ : ℝ} (hρ : 1 < ρ) :
    ∑' j : ℕ, (j : ℝ) ^ 2 * ρ⁻¹ ^ j =
      ρ⁻¹ * (1 + ρ⁻¹) / (1 - ρ⁻¹) ^ 3 := by
  set r : ℝ := ρ⁻¹
  have hr0 := inv_rho_nonneg hρ
  have hr := inv_rho_norm_lt_one hρ
  have hr1 := inv_rho_lt_one hρ
  have hd : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.ne'
  have hch : ∑' j : ℕ, ((j + 2).choose 2 : ℝ) * r ^ j = 1 / (1 - r) ^ 3 := by
    simpa [show (2 : ℕ) + 1 = 3 from rfl] using
      tsum_choose_mul_geometric_of_norm_lt_one (k := 2) (r := r) hr
  have hnat : ∑' j : ℕ, (j : ℝ) * r ^ j = r / (1 - r) ^ 2 := by
    simpa using tsum_coe_mul_geometric_of_norm_lt_one (r := r) hr
  have hgeo : ∑' j : ℕ, r ^ j = (1 - r)⁻¹ :=
    tsum_geometric_of_lt_one hr0 hr1
  have hsch : Summable fun j : ℕ => ((j + 2).choose 2 : ℝ) * r ^ j :=
    summable_choose_mul_geometric_of_norm_lt_one (k := 2) (r := r) hr
  have hsnat : Summable fun j : ℕ => (j : ℝ) * r ^ j :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr).congr fun j => by
      rw [pow_one]
  have hsgeo : Summable fun j : ℕ => r ^ j :=
    summable_geometric_of_lt_one hr0 hr1
  have hfun :
      (fun j : ℕ => (j : ℝ) ^ 2 * r ^ j) =
        fun j : ℕ =>
          (2 : ℝ) * (((j + 2).choose 2 : ℝ) * r ^ j) -
            ((3 : ℝ) * ((j : ℝ) * r ^ j) + (2 : ℝ) * r ^ j) := by
    funext j
    have hj := nat_sq_eq_choose j
    calc
      (j : ℝ) ^ 2 * r ^ j
          = (2 * ((j + 2).choose 2 : ℝ) - 3 * (j : ℝ) - 2) * r ^ j := by
            rw [hj]
      _ = (2 * ((j + 2).choose 2 : ℝ) - (3 * (j : ℝ) + 2)) * r ^ j := by
            ring
      _ = 2 * (((j + 2).choose 2 : ℝ) * r ^ j) -
            (3 * ((j : ℝ) * r ^ j) + 2 * r ^ j) := by
            ring
  have hA := hsch.mul_left (2 : ℝ)
  have hB := (hsnat.mul_left (3 : ℝ)).add (hsgeo.mul_left (2 : ℝ))
  rw [hfun, hA.tsum_sub hB, tsum_mul_left, hch,
    Summable.tsum_add (hsnat.mul_left (3 : ℝ)) (hsgeo.mul_left (2 : ℝ)),
    tsum_mul_left, tsum_mul_left, hnat]
  have hgeo' : ∑' j : ℕ, r ^ j = 1 / (1 - r) := by
    rw [hgeo, inv_eq_one_div]
  rw [hgeo']
  have :
      (2 : ℝ) * (1 / (1 - r) ^ 3) -
          (3 * (r / (1 - r) ^ 2) + 2 * (1 / (1 - r))) =
        r * (1 + r) / (1 - r) ^ 3 := by
    field_simp [hd]
    ring
  simpa [r] using this

theorem tsum_nat_sq_div_pow_succ {ρ : ℝ} (hρ : 1 < ρ) :
    ∑' j : ℕ, (j : ℝ) ^ 2 / ρ ^ (j + 1) = (ρ + 1) / (ρ - 1) ^ 3 := by
  have hfun :
      (fun j : ℕ => (j : ℝ) ^ 2 / ρ ^ (j + 1)) =
        fun j : ℕ => ρ⁻¹ * ((j : ℝ) ^ 2 * ρ⁻¹ ^ j) := by
    funext j
    calc
      (j : ℝ) ^ 2 / ρ ^ (j + 1) = ((j : ℝ) ^ 2 / ρ) * ρ⁻¹ ^ j :=
        div_pow_succ hρ ((j : ℝ) ^ 2) j
      _ = ρ⁻¹ * ((j : ℝ) ^ 2 * ρ⁻¹ ^ j) := by
          rw [div_eq_mul_inv]
          ring
  rw [hfun, tsum_mul_left, tsum_sq_mul_inv_rho hρ]
  have hd := one_sub_inv_rho_ne hρ
  have h0 := rho_ne_zero hρ
  have hρd := rho_sub_one_ne_zero hρ
  rw [one_sub_inv_rho hρ]
  field_simp [h0, hρd, hd]

theorem summable_one_div_pow_succ {ρ : ℝ} (hρ : 1 < ρ) :
    Summable fun j : ℕ => (1 : ℝ) / ρ ^ (j + 1) := by
  have hfun :
      (fun j : ℕ => (1 : ℝ) / ρ ^ (j + 1)) = fun j : ℕ => ρ⁻¹ * ρ⁻¹ ^ j := by
    funext j
    rw [div_pow_succ hρ (1 : ℝ) j, one_div]
  rw [hfun]
  exact (summable_geometric_of_lt_one (inv_rho_nonneg hρ)
      (inv_rho_lt_one hρ)).mul_left ρ⁻¹

theorem summable_nat_div_pow_succ {ρ : ℝ} (hρ : 1 < ρ) :
    Summable fun j : ℕ => (j : ℝ) / ρ ^ (j + 1) := by
  have hfun :
      (fun j : ℕ => (j : ℝ) / ρ ^ (j + 1)) =
        fun j : ℕ => ρ⁻¹ * ((j : ℝ) * ρ⁻¹ ^ j) := by
    funext j
    calc
      (j : ℝ) / ρ ^ (j + 1) = ((j : ℝ) / ρ) * ρ⁻¹ ^ j :=
        div_pow_succ hρ (j : ℝ) j
      _ = ρ⁻¹ * ((j : ℝ) * ρ⁻¹ ^ j) := by
          rw [div_eq_mul_inv]
          ring
  rw [hfun]
  have hs : Summable fun j : ℕ => (j : ℝ) * ρ⁻¹ ^ j :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (inv_rho_norm_lt_one hρ)).congr fun j => by
      rw [pow_one]
  exact hs.mul_left ρ⁻¹

theorem summable_nat_sq_div_pow_succ {ρ : ℝ} (hρ : 1 < ρ) :
    Summable fun j : ℕ => (j : ℝ) ^ 2 / ρ ^ (j + 1) := by
  have hfun :
      (fun j : ℕ => (j : ℝ) ^ 2 / ρ ^ (j + 1)) =
        fun j : ℕ => ρ⁻¹ * ((j : ℝ) ^ 2 * ρ⁻¹ ^ j) := by
    funext j
    calc
      (j : ℝ) ^ 2 / ρ ^ (j + 1) = ((j : ℝ) ^ 2 / ρ) * ρ⁻¹ ^ j :=
        div_pow_succ hρ ((j : ℝ) ^ 2) j
      _ = ρ⁻¹ * ((j : ℝ) ^ 2 * ρ⁻¹ ^ j) := by
          rw [div_eq_mul_inv]
          ring
  rw [hfun]
  exact (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
      (inv_rho_norm_lt_one hρ)).mul_left ρ⁻¹

private theorem succ_add_cast (n j : ℕ) :
    ((n + j + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + (j : ℝ) := by
  simp [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]

theorem summable_succ_sq_div_pow {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    Summable fun j : ℕ => ((n + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1) := by
  set s : ℝ := ((n + 1 : ℕ) : ℝ)
  have hfun :
      (fun j : ℕ => ((n + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1)) =
        fun j : ℕ =>
          s ^ 2 * ((1 : ℝ) / ρ ^ (j + 1)) +
            (2 * s) * ((j : ℝ) / ρ ^ (j + 1)) +
            ((j : ℝ) ^ 2 / ρ ^ (j + 1)) := by
    funext j
    have hidx := succ_add_cast n j
    have hsq : ((n + j + 1 : ℕ) : ℝ) ^ 2 =
        s ^ 2 + 2 * s * (j : ℝ) + (j : ℝ) ^ 2 := by
      rw [hidx]
      ring
    rw [hsq]
    have hden : ρ ^ (j + 1) ≠ 0 := pow_ne_zero _ (rho_ne_zero hρ)
    field_simp [hden]
  rw [hfun]
  exact ((summable_one_div_pow_succ hρ).mul_left (s ^ 2)).add
      ((summable_nat_div_pow_succ hρ).mul_left (2 * s)) |>.add
      (summable_nat_sq_div_pow_succ hρ)

/-- Exact geometric square sum at the shifted index. -/
theorem tsum_succ_sq_div_pow {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    ∑' j : ℕ, ((n + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1) =
      ((n + 1 : ℕ) : ℝ) ^ 2 / (ρ - 1) +
        2 * ((n + 1 : ℕ) : ℝ) / (ρ - 1) ^ 2 +
        (ρ + 1) / (ρ - 1) ^ 3 := by
  set s : ℝ := ((n + 1 : ℕ) : ℝ)
  have hfun :
      (fun j : ℕ => ((n + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1)) =
        fun j : ℕ =>
          s ^ 2 * ((1 : ℝ) / ρ ^ (j + 1)) +
            (2 * s) * ((j : ℝ) / ρ ^ (j + 1)) +
            ((j : ℝ) ^ 2 / ρ ^ (j + 1)) := by
    funext j
    have hidx := succ_add_cast n j
    have hsq : ((n + j + 1 : ℕ) : ℝ) ^ 2 =
        s ^ 2 + 2 * s * (j : ℝ) + (j : ℝ) ^ 2 := by
      rw [hidx]
      ring
    rw [hsq]
    have hden : ρ ^ (j + 1) ≠ 0 := pow_ne_zero _ (rho_ne_zero hρ)
    field_simp [hden]
  have h1 := (summable_one_div_pow_succ hρ).mul_left (s ^ 2)
  have h2 := (summable_nat_div_pow_succ hρ).mul_left (2 * s)
  have h3 := summable_nat_sq_div_pow_succ hρ
  rw [hfun, Summable.tsum_add (h1.add h2) h3, Summable.tsum_add h1 h2,
    tsum_mul_left, tsum_mul_left, tsum_one_div_pow_succ hρ,
    tsum_nat_div_pow_succ hρ, tsum_nat_sq_div_pow_succ hρ]
  ring

/-- Geometric domination: `∑_j (n+j+1)^2 ρ^{-j-1} ≤ C(ρ) (n+1)^2`. -/
theorem tsum_succ_sq_div_pow_le {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    ∑' j : ℕ, ((n + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1) ≤
      posMassGeomCoeff ρ * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  set s : ℝ := ((n + 1 : ℕ) : ℝ)
  have hs1 := one_le_succ_cast n
  have hs2 : (1 : ℝ) ≤ s ^ 2 := one_le_pow₀ hs1
  have hpos := rho_sub_one_pos hρ
  have heq := tsum_succ_sq_div_pow hρ n
  have hparts := posMassGeomCoeff_eq_parts hρ
  have hs : s ≤ s ^ 2 := by
    rw [pow_two]
    exact le_mul_of_one_le_right (le_trans zero_le_one hs1) hs1
  have hmid : 2 * s / (ρ - 1) ^ 2 ≤ 2 * s ^ 2 / (ρ - 1) ^ 2 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity))
      (pow_nonneg hpos.le _)
  have hlast : (ρ + 1) / (ρ - 1) ^ 3 ≤ ((ρ + 1) / (ρ - 1) ^ 3) * s ^ 2 :=
    le_mul_of_one_le_right (by positivity) hs2
  have hsum :
      s ^ 2 / (ρ - 1) + 2 * s / (ρ - 1) ^ 2 + (ρ + 1) / (ρ - 1) ^ 3 ≤
        posMassGeomCoeff ρ * s ^ 2 := by
    have hL : s ^ 2 / (ρ - 1) = (1 / (ρ - 1)) * s ^ 2 := by
      field_simp [rho_sub_one_ne_zero hρ]
    have hM : 2 * s ^ 2 / (ρ - 1) ^ 2 = (2 / (ρ - 1) ^ 2) * s ^ 2 := by
      field_simp [rho_sub_one_ne_zero hρ]
    rw [hparts, add_mul, add_mul, hL]
    have hstep :
        (1 / (ρ - 1)) * s ^ 2 + 2 * s / (ρ - 1) ^ 2 ≤
          (1 / (ρ - 1)) * s ^ 2 + (2 / (ρ - 1) ^ 2) * s ^ 2 :=
      add_le_add le_rfl (hM ▸ hmid)
    refine (add_le_add hstep hlast).trans_eq ?_
    ring
  exact heq.trans_le (by simpa [s] using hsum)

/-! ### Chebyshev comparison for `F_ρ` -/

theorem summable_posMass_terms {ρ : ℝ} (hρ : 1 < ρ) {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => a n / ρ ^ n) (k : ℕ) :
    Summable fun j : ℕ => a (k + j) / ρ ^ (j + 1) := by
  have hshift : Summable fun j : ℕ => a (j + k) / ρ ^ (j + k) :=
    (summable_nat_add_iff (f := fun n : ℕ => a n / ρ ^ n) k).mpr ha
  have hshift' : Summable fun j : ℕ => a (k + j) / ρ ^ (k + j) := by
    simpa [add_comm k] using hshift
  have hρ0 : ρ ≠ 0 := rho_ne_zero hρ
  refine (hshift'.mul_left (ρ ^ k / ρ)).congr fun j => ?_
  have hk : ρ ^ (k + j) = ρ ^ k * ρ ^ j := pow_add _ _ _
  have hj : ρ ^ (j + 1) = ρ ^ j * ρ := pow_succ _ _
  field_simp [hρ0, hk, hj, pow_ne_zero k hρ0, pow_ne_zero j hρ0]
  ring

theorem summable_posMass_nthPrime {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    Summable fun j : ℕ => (nthPrime (n + j) : ℝ) / ρ ^ (j + 1) :=
  summable_posMass_terms hρ (nthPrime_div_pow_summable hρ) n

/-- Direct Chebyshev comparison, constant `144` independent of `ρ`. -/
theorem posMass_nthPrime_le_sq_tsum {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    posMass ρ (fun k => (nthPrime k : ℝ)) n ≤
      144 * ∑' j : ℕ, ((n + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1) := by
  have hterm : ∀ j : ℕ,
      (nthPrime (n + j) : ℝ) / ρ ^ (j + 1) ≤
        144 * (((n + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1)) := fun j => by
    have hnum := nthPrime_cast_le_succ_sq (n + j)
    have hden : 0 ≤ ρ ^ (j + 1) := pow_nonneg (rho_pos hρ).le _
    have := div_le_div_of_nonneg_right hnum hden
    simpa [mul_div_assoc] using this
  have hdom : Summable fun j : ℕ =>
      144 * (((n + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1)) :=
    (summable_succ_sq_div_pow hρ n).mul_left 144
  have hf := summable_posMass_nthPrime hρ n
  have hle := hf.tsum_le_tsum hterm hdom
  rw [posMass, ← tsum_mul_left]
  exact hle

/-- Polynomial bound of the same shape as `posMass_nthPrime_le`, with
coefficient `144 ρ(ρ+1)/(ρ-1)^3`. -/
theorem posMass_nthPrime_le_mul_sq {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    posMass ρ (fun k => (nthPrime k : ℝ)) n ≤
      posMassScaleCoeff ρ * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have h1 := posMass_nthPrime_le_sq_tsum hρ n
  have h2 := tsum_succ_sq_div_pow_le hρ n
  have hmul := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 144)
  unfold posMassScaleCoeff
  exact h1.trans (hmul.trans_eq (by ring))

/-- `F_ρ(n) ≤ C(ρ) (n+1) (p_n+1)` from `n+1 ≤ p_n`. -/
theorem posMass_nthPrime_le_mul_nthPrime {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    posMass ρ (fun k => (nthPrime k : ℝ)) n ≤
      posMassScaleCoeff ρ * ((n + 1 : ℕ) : ℝ) * ((nthPrime n : ℝ) + 1) := by
  have hF := posMass_nthPrime_le_mul_sq hρ n
  have hn : ((n + 1 : ℕ) : ℝ) ≤ (nthPrime n : ℝ) + 1 := by
    have hle : (n + 1 : ℕ) ≤ nthPrime n := succ_le_nthPrime n
    have : ((n + 1 : ℕ) : ℝ) ≤ (nthPrime n : ℝ) := Nat.cast_le.mpr hle
    linarith
  have hsq :
      ((n + 1 : ℕ) : ℝ) ^ 2 ≤
        ((n + 1 : ℕ) : ℝ) * ((nthPrime n : ℝ) + 1) := by
    have hnn : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    simpa [pow_two] using mul_le_mul_of_nonneg_left hn hnn
  have hC := posMassScaleCoeff_nonneg hρ
  have hmul := mul_le_mul_of_nonneg_left hsq hC
  have hassoc :
      posMassScaleCoeff ρ * ((n + 1 : ℕ) : ℝ) * ((nthPrime n : ℝ) + 1) =
        posMassScaleCoeff ρ *
          (((n + 1 : ℕ) : ℝ) * ((nthPrime n : ℝ) + 1)) := by
    ring
  exact hF.trans (hmul.trans_eq hassoc.symm)

/-! ### Exact one-step recurrence and Abel scale -/

/-- Peeling: `ρ F_ρ(n) = a_n + F_ρ(n+1)`. -/
theorem posMass_mul_rho {ρ : ℝ} (hρ : 1 < ρ) (a : ℕ → ℝ)
    (ha : Summable fun n : ℕ => a n / ρ ^ n) (n : ℕ) :
    ρ * posMass ρ a n = a n + posMass ρ a (n + 1) := by
  have hf := summable_posMass_terms hρ ha n
  have hsplit := hf.tsum_eq_zero_add
  have h0 : (a (n + 0) / ρ ^ (0 + 1)) = a n / ρ := by
    simp [pow_one]
  have hfun :
      (fun j : ℕ => a (n + (j + 1)) / ρ ^ (j + 1 + 1)) =
        fun j : ℕ => (a (n + 1 + j) / ρ ^ (j + 1)) / ρ := by
    funext j
    have hidx : n + (j + 1) = n + 1 + j := by omega
    have hpow : ρ ^ (j + 1 + 1) = ρ ^ (j + 1) * ρ := pow_succ _ _
    rw [hidx, hpow]
    have hρ0 := rho_ne_zero hρ
    have hp : ρ ^ (j + 1) ≠ 0 := pow_ne_zero _ hρ0
    field_simp [hρ0, hp]
  have htail :
      ∑' j : ℕ, a (n + (j + 1)) / ρ ^ (j + 1 + 1) =
        posMass ρ a (n + 1) / ρ := by
    rw [hfun, tsum_div_const]
    rfl
  have heq : posMass ρ a n = a n / ρ + posMass ρ a (n + 1) / ρ := by
    rw [posMass, hsplit, h0, htail]
  have hρ0 := rho_ne_zero hρ
  calc
    ρ * posMass ρ a n
        = ρ * (a n / ρ + posMass ρ a (n + 1) / ρ) := by rw [heq]
    _ = a n + posMass ρ a (n + 1) := by field_simp [hρ0]

/-- Exact Abel scale: `F_ρ(n) = (a_n + T_ρ(n))/(ρ-1)`. -/
theorem posMass_eq_add_gapTail {ρ : ℝ} (hρ : 1 < ρ) (a : ℕ → ℝ)
    (ha : Summable fun n : ℕ => a n / ρ ^ n) (n : ℕ) :
    posMass ρ a n =
      (a n + gapTail ρ (fun k => a (k + 1) - a k) n) / (ρ - 1) := by
  have hρF := posMass_mul_rho hρ a ha n
  have hT := gapTail_eq_sub hρ a ha n
  have hd := rho_sub_one_ne_zero hρ
  have hlin :
      gapTail ρ (fun k => a (k + 1) - a k) n =
        (ρ - 1) * posMass ρ a n - a n := by
    rw [hT]
    linarith
  rw [eq_div_iff_mul_eq hd]
  linarith

theorem posMass_nthPrime_eq {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    posMass ρ (fun k => (nthPrime k : ℝ)) n =
      ((nthPrime n : ℝ) +
          gapTail ρ (fun k => (primeGap k : ℝ)) n) / (ρ - 1) := by
  have hfun : (fun k : ℕ => (primeGap k : ℝ)) =
      fun k => (nthPrime (k + 1) : ℝ) - nthPrime k := by
    funext k
    exact_mod_cast primeGap_cast k
  rw [hfun]
  exact posMass_eq_add_gapTail hρ (fun k => (nthPrime k : ℝ))
    (nthPrime_div_pow_summable hρ) n

theorem gapTail_prime_nonneg {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    0 ≤ gapTail ρ (fun k => (primeGap k : ℝ)) n :=
  tsum_nonneg fun _h =>
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (rho_pos hρ).le _)

/-- Matching lower bound of order `p_n`: `p_n/(ρ-1) ≤ F_ρ(n)`. -/
theorem nthPrime_div_sub_one_le_posMass {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    (nthPrime n : ℝ) / (ρ - 1) ≤
      posMass ρ (fun k => (nthPrime k : ℝ)) n := by
  have heq := posMass_nthPrime_eq hρ n
  have hT := gapTail_prime_nonneg hρ n
  have hden := (rho_sub_one_pos hρ).le
  have hnum : (nthPrime n : ℝ) ≤
      (nthPrime n : ℝ) + gapTail ρ (fun k => (primeGap k : ℝ)) n :=
    le_add_of_nonneg_right hT
  rw [heq]
  exact div_le_div_of_nonneg_right hnum hden

theorem posMass_nthPrime_le_add_gapTail {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    posMass ρ (fun k => (nthPrime k : ℝ)) n ≤
      (nthPrime n : ℝ) / (ρ - 1) +
        gapTail ρ (fun k => (primeGap k : ℝ)) n / (ρ - 1) := by
  have heq := posMass_nthPrime_eq hρ n
  simpa [add_div] using (le_of_eq heq)

/-- `F_ρ(n) ≪_ρ p_n` reduces to `T_ρ(n) ≪_ρ p_n`. No density claim. -/
theorem posMass_nthPrime_le_of_gapTail_le {ρ : ℝ} (hρ : 1 < ρ) {n : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hT : gapTail ρ (fun k => (primeGap k : ℝ)) n ≤ C * (nthPrime n : ℝ)) :
    posMass ρ (fun k => (nthPrime k : ℝ)) n ≤
      (1 + C) / (ρ - 1) * (nthPrime n : ℝ) := by
  have heq := posMass_nthPrime_eq hρ n
  have hden := (rho_sub_one_pos hρ).le
  have hnum :
      (nthPrime n : ℝ) + gapTail ρ (fun k => (primeGap k : ℝ)) n ≤
        (1 + C) * (nthPrime n : ℝ) := by
    have := add_le_add
      (le_rfl : (nthPrime n : ℝ) ≤ (nthPrime n : ℝ)) hT
    have hrew : (nthPrime n : ℝ) + C * (nthPrime n : ℝ) =
        (1 + C) * (nthPrime n : ℝ) := by ring
    exact this.trans_eq hrew
  have hdiv := div_le_div_of_nonneg_right hnum hden
  have hform : ((1 + C) * (nthPrime n : ℝ)) / (ρ - 1) =
      (1 + C) / (ρ - 1) * (nthPrime n : ℝ) :=
    (div_mul_eq_mul_div (1 + C) (ρ - 1) (nthPrime n : ℝ)).symm
  rw [heq]
  exact hdiv.trans_eq hform

theorem nthPrime_eq_add_sum_primeGap (n j : ℕ) :
    nthPrime (n + j) = nthPrime n + ∑ i ∈ range j, primeGap (n + i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hidx : n + (j + 1) = n + j + 1 := by omega
    rw [hidx, sum_range_succ, ← add_assoc, ← ih]
    have hle : nthPrime (n + j) ≤ nthPrime (n + j + 1) :=
      nthPrime_mono (Nat.le_succ (n + j))
    simp [primeGap, Nat.add_sub_of_le hle]

/-! ### Finite head plus geometrically decaying tail -/

theorem posMass_eq_trunc_add {ρ : ℝ} (hρ : 1 < ρ) (a : ℕ → ℝ)
    (ha : Summable fun n : ℕ => a n / ρ ^ n) (n J : ℕ) :
    posMass ρ a n =
      posMassTrunc ρ a n J + ρ⁻¹ ^ J * posMass ρ a (n + J) := by
  have hf := summable_posMass_terms hρ ha n
  have hsplit := hf.sum_add_tsum_nat_add J
  have hfun :
      (fun i : ℕ => a (n + (i + J)) / ρ ^ (i + J + 1)) =
        fun i : ℕ => ρ⁻¹ ^ J * (a (n + J + i) / ρ ^ (i + 1)) := by
    funext i
    have hidx : n + (i + J) = n + J + i := by omega
    have hpow : ρ ^ (i + J + 1) = ρ ^ J * ρ ^ (i + 1) := by
      have : i + J + 1 = J + (i + 1) := by omega
      rw [this, pow_add]
    rw [hidx, hpow, inv_pow]
    have hρ0 := rho_ne_zero hρ
    have hJ : ρ ^ J ≠ 0 := pow_ne_zero J hρ0
    have hi : ρ ^ (i + 1) ≠ 0 := pow_ne_zero _ hρ0
    field_simp [hρ0, hJ, hi]
  unfold posMass posMassTrunc
  rw [← hsplit, hfun, tsum_mul_left]

theorem sum_inv_rho_pow_succ {ρ : ℝ} (hρ : 1 < ρ) (J : ℕ) :
    ∑ j ∈ range J, (1 : ℝ) / ρ ^ (j + 1) = (1 - ρ⁻¹ ^ J) / (ρ - 1) := by
  have h0 := rho_ne_zero hρ
  have hr : ρ⁻¹ ≠ 1 := inv_rho_ne_one hρ
  have hfun :
      ∀ j, (1 : ℝ) / ρ ^ (j + 1) = ρ⁻¹ * ρ⁻¹ ^ j := fun j => by
    rw [div_pow_succ hρ (1 : ℝ) j, one_div]
  have hcalc :
      ∑ j ∈ range J, (1 : ℝ) / ρ ^ (j + 1) =
        ρ⁻¹ * ∑ j ∈ range J, ρ⁻¹ ^ j := by
    rw [sum_congr rfl fun j _ => hfun j, ← mul_sum]
  have hneg :
      (ρ⁻¹ ^ J - 1) / (ρ⁻¹ - 1) = (1 - ρ⁻¹ ^ J) / (1 - ρ⁻¹) := by
    have h1 : -(ρ⁻¹ ^ J - 1) = 1 - ρ⁻¹ ^ J := by ring
    have h2 : -(ρ⁻¹ - 1) = 1 - ρ⁻¹ := by ring
    rw [← neg_div_neg_eq, h1, h2]
  have hd := rho_sub_one_ne_zero hρ
  rw [hcalc, geom_sum_eq hr J, hneg, one_sub_inv_rho hρ]
  field_simp [h0, hd]

theorem posMassTrunc_le_of_monotone {ρ : ℝ} (hρ : 1 < ρ) (a : ℕ → ℝ)
    (hmon : Monotone a) (n J : ℕ) :
    posMassTrunc ρ a n J ≤
      a (n + J) * ((1 - ρ⁻¹ ^ J) / (ρ - 1)) := by
  have hterm : ∀ j ∈ range J,
      a (n + j) / ρ ^ (j + 1) ≤ a (n + J) / ρ ^ (j + 1) := fun j hj => by
    have hj' : n + j ≤ n + J :=
      Nat.add_le_add_left (Nat.le_of_lt (mem_range.mp hj)) n
    exact div_le_div_of_nonneg_right (hmon hj') (pow_nonneg (rho_pos hρ).le _)
  have hfactor :
      ∑ j ∈ range J, a (n + J) / ρ ^ (j + 1) =
        a (n + J) * ∑ j ∈ range J, (1 : ℝ) / ρ ^ (j + 1) := by
    simp [div_eq_mul_inv, mul_sum]
  unfold posMassTrunc
  refine (sum_le_sum hterm).trans_eq ?_
  rw [hfactor, sum_inv_rho_pow_succ hρ]

theorem posMassTrunc_nthPrime_le {ρ : ℝ} (hρ : 1 < ρ) (n J : ℕ) :
    posMassTrunc ρ (fun k => (nthPrime k : ℝ)) n J ≤
      (nthPrime (n + J) : ℝ) * ((1 - ρ⁻¹ ^ J) / (ρ - 1)) := by
  refine posMassTrunc_le_of_monotone hρ (fun k => (nthPrime k : ℝ)) ?_ n J
  intro i j hij
  exact Nat.cast_le.mpr (nthPrime_mono hij)

/-- Head `j < J` by monotonicity in `p_{n+J}`; tail by `O_ρ((n+J)^2) ρ^{-J}`. -/
theorem posMass_nthPrime_split_le {ρ : ℝ} (hρ : 1 < ρ) (n J : ℕ) :
    posMass ρ (fun k => (nthPrime k : ℝ)) n ≤
      (nthPrime (n + J) : ℝ) * ((1 - ρ⁻¹ ^ J) / (ρ - 1)) +
        ρ⁻¹ ^ J * (posMassScaleCoeff ρ * ((n + J + 1 : ℕ) : ℝ) ^ 2) := by
  have hsplit := posMass_eq_trunc_add hρ (fun k => (nthPrime k : ℝ))
    (nthPrime_div_pow_summable hρ) n J
  have hhead := posMassTrunc_nthPrime_le hρ n J
  have htailF := posMass_nthPrime_le_mul_sq hρ (n + J)
  have hinv : 0 ≤ ρ⁻¹ ^ J := pow_nonneg (inv_rho_nonneg hρ) J
  have htail := mul_le_mul_of_nonneg_left htailF hinv
  linarith

/-! ### Gap-tail remainder bounds (still polynomial) -/

theorem gapTail_prime_le_posMass_succ {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    gapTail ρ (fun k => (primeGap k : ℝ)) n ≤
      posMass ρ (fun k => (nthPrime k : ℝ)) (n + 1) := by
  have hterm : ∀ h : ℕ,
      (primeGap (n + h) : ℝ) / ρ ^ (h + 1) ≤
        (nthPrime (n + 1 + h) : ℝ) / ρ ^ (h + 1) := fun h => by
    have hle : primeGap (n + h) ≤ nthPrime (n + h + 1) :=
      primeGap_le_nthPrime_succ (n + h)
    have hidx : n + h + 1 = n + 1 + h := by omega
    have hcast : (primeGap (n + h) : ℝ) ≤ (nthPrime (n + 1 + h) : ℝ) := by
      rw [← hidx]
      exact Nat.cast_le.mpr hle
    exact div_le_div_of_nonneg_right hcast (pow_nonneg (rho_pos hρ).le _)
  have hf : Summable fun h : ℕ =>
      (primeGap (n + h) : ℝ) / ρ ^ (h + 1) := by
    have hfun :
        (fun h : ℕ => (primeGap (n + h) : ℝ) / ρ ^ (h + 1)) =
          fun h : ℕ =>
            (nthPrime (n + h + 1) : ℝ) / ρ ^ (h + 1) -
              (nthPrime (n + h) : ℝ) / ρ ^ (h + 1) := by
      funext h
      rw [primeGap_cast, sub_div]
    rw [hfun]
    have hsucc' : Summable fun h : ℕ =>
        (nthPrime (n + h + 1) : ℝ) / ρ ^ (h + 1) :=
      (summable_posMass_nthPrime hρ (n + 1)).congr fun h => by
        have : n + 1 + h = n + h + 1 := by omega
        simp [this]
    exact hsucc'.sub (summable_posMass_nthPrime hρ n)
  have hg := summable_posMass_nthPrime hρ (n + 1)
  have hle := hf.tsum_le_tsum hterm hg
  simpa [gapTail, posMass] using hle

theorem gapTail_prime_le_sq_tsum {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    gapTail ρ (fun k => (primeGap k : ℝ)) n ≤
      144 * ∑' h : ℕ, ((n + h + 2 : ℕ) : ℝ) ^ 2 / ρ ^ (h + 1) := by
  have hF := gapTail_prime_le_posMass_succ hρ n
  have hsq := posMass_nthPrime_le_sq_tsum hρ (n + 1)
  have hidx : ∀ h : ℕ,
      ((n + 1 + h + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (h + 1) =
        ((n + h + 2 : ℕ) : ℝ) ^ 2 / ρ ^ (h + 1) := fun h => by
    have : n + 1 + h + 1 = n + h + 2 := by omega
    simp [this]
  refine hF.trans (hsq.trans_eq ?_)
  congr 1
  exact tsum_congr hidx

theorem gapTail_prime_le_mul_sq {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    gapTail ρ (fun k => (primeGap k : ℝ)) n ≤
      posMassScaleCoeff ρ * ((n + 2 : ℕ) : ℝ) ^ 2 := by
  have h1 := gapTail_prime_le_posMass_succ hρ n
  have h2 := posMass_nthPrime_le_mul_sq hρ (n + 1)
  have hidx : n + 1 + 1 = n + 2 := by omega
  have : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by
    simp [hidx]
  exact h1.trans (by simpa [this] using h2)

/-- Closest compiled stand-in for `F ≪_ρ p_n`: a genuine `p_n` term plus
a Chebyshev remainder `O_ρ(n^2)`. Not `m_X ≍ X/log X`. -/
theorem posMass_nthPrime_le_nthPrime_add_poly {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    posMass ρ (fun k => (nthPrime k : ℝ)) n ≤
      (nthPrime n : ℝ) / (ρ - 1) +
        posMassScaleCoeff ρ * ((n + 2 : ℕ) : ℝ) ^ 2 / (ρ - 1) := by
  have heq := posMass_nthPrime_le_add_gapTail hρ n
  have hT := gapTail_prime_le_mul_sq hρ n
  have hden := (rho_sub_one_pos hρ).le
  have hdiv := div_le_div_of_nonneg_right hT hden
  linarith

end PrimeGapNormality.Prime
