import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.WellFounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Weak two-sided Euler-product bounds (no Mertens–γ)

Paper `V(y)` (v0.2, after (eq:stdprofile) and Appendix calibration) is
`∏_{p ≤ y} (1 - 1/p)`, **not** `∏ (1 - 1/(p-1))`. The latter vanishes at
`p = 2`. Rooted Bernoulli retention is the cut product
`rootedEulerProdNat z y = ∏_{z < p ≤ y} (1 - 1/(p-1))`, paper `ϑ_y`.

Weak bounds `c / log y ≤ V(y) ≤ C / log y` for large `y` suffice for
polylog error budgets (R104/07 §4b). Full Mertens with Euler–Mascheroni
is not used. Chebyshev `ψ = O(x)` enters only through `log n!`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` `V(y)`, (eq:rho),
Appendix calibration; `rounds/round104/07_grok_full_normality_implementation_order.md` §4b;
mathlib `Chebyshev.psi_le_const_mul_self`, `pi_ge`, `theta`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset
open scoped ArithmeticFunction Interval

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### Definitions -/

/-- Paper `V` on naturals: `∏_{p ≤ n} (1 - 1/p)`. Empty product is `1`. -/
noncomputable def eulerProdNat (n : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE n, (1 - (p : ℝ)⁻¹)

/-- Paper `V(y) = ∏_{p ≤ y} (1 - 1/p)`, evaluated at `⌊y⌋`. -/
noncomputable def eulerProd (y : ℝ) : ℝ :=
  eulerProdNat ⌊y⌋₊

/-- Rooted retention `∏_{z < p ≤ y} (1 - 1/(p-1))`. Paper `ϑ` from a
presieve cut `z`. The factor at `p = 2` is `0`. -/
noncomputable def rootedEulerProdNat (z y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y \ Nat.primesLE z, (1 - ((p : ℝ) - 1)⁻¹)

/-- Real-argument form of `rootedEulerProdNat`. -/
noncomputable def rootedEulerProd (z y : ℝ) : ℝ :=
  rootedEulerProdNat ⌊z⌋₊ ⌊y⌋₊

/-- Multiplicative `n ↦ n⁻¹`, for the Euler-product identification. -/
noncomputable def natInvHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by
    simp
    ring

/-- Least prime `y` with `V(y) ≤ 1 / log t`. -/
def IsSieveCutoff (t : ℝ) (y : ℕ) : Prop :=
  Nat.Prime y ∧
    eulerProd y ≤ 1 / Real.log t ∧
    ∀ p : ℕ, Nat.Prime p → p < y → 1 / Real.log t < eulerProd p

/-- Absolute constant in `eulerProdLowerConst / log y ≤ V(y)` for `y ≥ 16`.
Calibration remaining: replace by `e^{-γ}` after a Mertens import. -/
noncomputable def eulerProdLowerConst : ℝ :=
  Real.exp (-(30 : ℝ))

/-! ### Elementary factor lemmas -/

theorem one_sub_inv_ne_zero {p : ℕ} (hp : Nat.Prime p) :
    1 - (p : ℝ)⁻¹ ≠ 0 := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  linarith

theorem one_sub_inv_pos {p : ℕ} (hp : Nat.Prime p) :
    0 < 1 - (p : ℝ)⁻¹ := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  linarith

theorem eulerProdNat_ne_zero (n : ℕ) : eulerProdNat n ≠ 0 :=
  prod_ne_zero_iff.mpr fun p hp =>
    one_sub_inv_ne_zero (Nat.prime_of_mem_primesLE hp)

theorem eulerProdNat_pos (n : ℕ) : 0 < eulerProdNat n :=
  prod_pos fun p hp => one_sub_inv_pos (Nat.prime_of_mem_primesLE hp)

theorem eulerProd_pos (y : ℝ) : 0 < eulerProd y :=
  eulerProdNat_pos _

theorem eulerProd_eq_eulerProdNat (y : ℝ) :
    eulerProd y = eulerProdNat ⌊y⌋₊ :=
  rfl

theorem eulerProdNat_mono {m n : ℕ} (hmn : m ≤ n) :
    eulerProdNat n ≤ eulerProdNat m := by
  have hsub : Nat.primesLE m ⊆ Nat.primesLE n := Nat.primesLE_mono hmn
  have h01 : ∀ p ∈ Nat.primesLE n, 0 ≤ 1 - (p : ℝ)⁻¹ := fun p hp =>
    (one_sub_inv_pos (Nat.prime_of_mem_primesLE hp)).le
  have hle : ∀ p ∈ Nat.primesLE n, 1 - (p : ℝ)⁻¹ ≤ 1 := fun p hp =>
    sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    eulerProdNat n
        = (∏ p ∈ Nat.primesLE n \ Nat.primesLE m, (1 - (p : ℝ)⁻¹)) *
            eulerProdNat m := by
          rw [eulerProdNat, eulerProdNat, prod_sdiff hsub]
    _ ≤ 1 * eulerProdNat m := by
        refine mul_le_mul_of_nonneg_right ?_ (eulerProdNat_pos m).le
        exact prod_le_one (fun p hp => h01 p (sdiff_subset hp))
          (fun p hp => hle p (sdiff_subset hp))
    _ = eulerProdNat m := one_mul _

theorem eulerProd_anti {x y : ℝ} (hxy : x ≤ y) (hx : 0 ≤ x) :
    eulerProd y ≤ eulerProd x :=
  eulerProdNat_mono (Nat.floor_le_floor hxy)

/-- Exact finite quotient: `V(y) / V(z)` is the product over `(z, y]`. -/
theorem eulerProdNat_div {z y : ℕ} (hzy : z ≤ y) :
    eulerProdNat y / eulerProdNat z =
      ∏ p ∈ Nat.primesLE y \ Nat.primesLE z, (1 - (p : ℝ)⁻¹) := by
  have hsub : Nat.primesLE z ⊆ Nat.primesLE y := Nat.primesLE_mono hzy
  have hz : eulerProdNat z ≠ 0 := eulerProdNat_ne_zero z
  have hprod :
      eulerProdNat y =
        (∏ p ∈ Nat.primesLE y \ Nat.primesLE z, (1 - (p : ℝ)⁻¹)) *
          eulerProdNat z := by
    rw [eulerProdNat, eulerProdNat, prod_sdiff hsub]
  rw [hprod, mul_div_cancel_right₀ _ hz]

theorem eulerProd_div {z y : ℝ} (hzy : z ≤ y) (hz : 0 ≤ z) :
    eulerProd y / eulerProd z =
      ∏ p ∈ Nat.primesLE ⌊y⌋₊ \ Nat.primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹) :=
  eulerProdNat_div (Nat.floor_le_floor hzy)

/-- Algebraic identity used in paper (eq:rho):
`(1-1/(p-1)) = (1-1/p) (1 - 1/(p-1)^2)`. -/
theorem rootedFactor_eq {p : ℕ} (hp : 2 ≤ p) :
    1 - ((p : ℝ) - 1)⁻¹ =
      (1 - (p : ℝ)⁻¹) * (1 - ((p : ℝ) - 1)⁻¹ ^ 2) := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hp)
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hp1)
  field_simp [hden, hp0]
  ring

/-- Exact identity relating rooted retention to paper `V`. -/
theorem rootedEulerProdNat_eq {z y : ℕ} (hzy : z ≤ y) :
    rootedEulerProdNat z y =
      eulerProdNat y / eulerProdNat z *
        ∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
          (1 - ((p : ℝ) - 1)⁻¹ ^ 2) := by
  have hsub : Nat.primesLE z ⊆ Nat.primesLE y := Nat.primesLE_mono hzy
  have hz : eulerProdNat z ≠ 0 := eulerProdNat_ne_zero z
  have hfac :
      ∀ p ∈ Nat.primesLE y \ Nat.primesLE z,
        1 - ((p : ℝ) - 1)⁻¹ =
          (1 - (p : ℝ)⁻¹) * (1 - ((p : ℝ) - 1)⁻¹ ^ 2) := by
    intro p hp
    have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
    exact rootedFactor_eq hp'.two_le
  calc
    rootedEulerProdNat z y
        = ∏ p ∈ Nat.primesLE y \ Nat.primesLE z, (1 - ((p : ℝ) - 1)⁻¹) :=
          rfl
    _ = ∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
          ((1 - (p : ℝ)⁻¹) * (1 - ((p : ℝ) - 1)⁻¹ ^ 2)) :=
          prod_congr rfl hfac
    _ = (∏ p ∈ Nat.primesLE y \ Nat.primesLE z, (1 - (p : ℝ)⁻¹)) *
          ∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
            (1 - ((p : ℝ) - 1)⁻¹ ^ 2) :=
          prod_mul_distrib
    _ = eulerProdNat y / eulerProdNat z *
          ∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
            (1 - ((p : ℝ) - 1)⁻¹ ^ 2) := by
          rw [eulerProdNat_div hzy]

/-! ### Telescoping comparison `1/n ≤ V(n)` -/

private theorem prod_one_sub_inv_Icc (n : ℕ) (hn : 1 ≤ n) :
    ∏ k ∈ Icc 2 n, (1 - (k : ℝ)⁻¹) = (n : ℝ)⁻¹ := by
  refine Nat.le_induction ?base ?step n hn
  · simp
  · intro n hn ih
    have hmem : n + 1 ∉ Icc 2 n := by
      simp [mem_Icc]
    have hinsert :
        Icc 2 (n + 1) = insert (n + 1) (Icc 2 n) :=
      (insert_Icc_right_eq_Icc_add_one
        (show 2 ≤ n + 1 by omega)).symm
    have hn0 : (n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (Nat.succ_le_iff.mp hn))
    have hn1 : (n + 1 : ℝ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := Nat.cast_succ n
    have hfac : 1 - ((n + 1 : ℕ) : ℝ)⁻¹ = (n : ℝ) / (n + 1) := by
      rw [hcast]
      field_simp [hn1]
      ring
    rw [hinsert, prod_insert hmem, ih, hfac, hcast]
    field_simp [hn0, hn1]

theorem eulerProdNat_ge_inv (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ)⁻¹ ≤ eulerProdNat n := by
  have hsub : Nat.primesLE n ⊆ Icc 2 n := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    exact mem_Icc.mpr ⟨hp'.2.two_le, hp'.1⟩
  have h01 : ∀ k ∈ Icc 2 n, 0 ≤ 1 - (k : ℝ)⁻¹ := fun k hk => by
    have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
    have : (k : ℝ)⁻¹ ≤ 1 := Nat.cast_inv_le_one k
    linarith
  have hle : ∀ k ∈ Icc 2 n, 1 - (k : ℝ)⁻¹ ≤ 1 := fun k _ =>
    sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hprod :
      ∏ k ∈ Icc 2 n, (1 - (k : ℝ)⁻¹) =
        (∏ k ∈ Icc 2 n \ Nat.primesLE n, (1 - (k : ℝ)⁻¹)) *
          eulerProdNat n := by
    rw [eulerProdNat, prod_sdiff hsub]
  have hcomp :
      ∏ k ∈ Icc 2 n \ Nat.primesLE n, (1 - (k : ℝ)⁻¹) ≤ 1 :=
    prod_le_one (fun k hk => h01 k (sdiff_subset hk))
      (fun k hk => hle k (sdiff_subset hk))
  have htel := prod_one_sub_inv_Icc n hn
  have hpos : 0 ≤ eulerProdNat n := (eulerProdNat_pos n).le
  have : (n : ℝ)⁻¹ ≤ 1 * eulerProdNat n := by
    rw [← htel, hprod]
    exact mul_le_mul_of_nonneg_right hcomp hpos
  simpa using this

/-! ### Upper bound via harmonic numbers (no Chebyshev) -/

private theorem mem_factored_of_mem_Icc {n k : ℕ} (hk : k ∈ Icc 1 n) :
    k ∈ Nat.factoredNumbers (Nat.primesLE n) := by
  rw [Nat.mem_factoredNumbers']
  intro p hp hpk
  have hkpos : 0 < k := by
    have := (mem_Icc.mp hk).1
    omega
  have hple : p ≤ k := Nat.le_of_dvd hkpos hpk
  exact Nat.mem_primesLE.mpr ⟨hple.trans (mem_Icc.mp hk).2, hp⟩

private theorem natInvHom_norm_lt_one {p : ℕ} (hp : Nat.Prime p) :
    ‖natInvHom p‖ < 1 := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  simp only [natInvHom, MonoidHom.coe_mk, OneHom.coe_mk, Real.norm_eq_abs, abs_inv]
  rw [abs_of_nonneg (Nat.cast_nonneg p)]
  exact inv_lt_one_of_one_lt₀ hp1

private theorem harmonic_le_inv_eulerProdNat (n : ℕ) :
    (harmonic n : ℝ) ≤ (eulerProdNat n)⁻¹ := by
  have hinv :
      (eulerProdNat n)⁻¹ =
        ∏ p ∈ Nat.primesLE n, (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [eulerProdNat, prod_inv_distrib]
  rw [hinv]
  have hgeom :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := natInvHom) (fun {p} hp => natInvHom_norm_lt_one hp) (Nat.primesLE n)
  have hfilter :
      {p ∈ Nat.primesLE n | Nat.Prime p} = Nat.primesLE n :=
    filter_true_of_mem fun p hp => (Nat.mem_primesLE.mp hp).2
  have hprod :
      ∏ p ∈ Nat.primesLE n, (1 - (p : ℝ)⁻¹)⁻¹ =
        ∏ p ∈ {p ∈ Nat.primesLE n | Nat.Prime p}, (1 - natInvHom p)⁻¹ := by
    rw [hfilter]
    refine prod_congr rfl fun p hp => ?_
    simp [natInvHom]
  have hhas : HasSum (fun m : Nat.factoredNumbers (Nat.primesLE n) => (m : ℝ)⁻¹)
      (∏ p ∈ Nat.primesLE n, (1 - (p : ℝ)⁻¹)⁻¹) := by
    have h1 : HasSum (fun m : Nat.factoredNumbers (Nat.primesLE n) => natInvHom m)
        (∏ p ∈ Nat.primesLE n, (1 - (p : ℝ)⁻¹)⁻¹) := by
      rw [hprod]
      exact hgeom.2
    exact h1.congr_fun fun m => by simp [natInvHom]
  let P : ℕ → Prop := fun m => m ∈ Nat.factoredNumbers (Nat.primesLE n)
  let t := (Icc 1 n).subtype P
  have hsum_le :
      ∑ x ∈ t, (x : ℝ)⁻¹ ≤ ∏ p ∈ Nat.primesLE n, (1 - (p : ℝ)⁻¹)⁻¹ :=
    sum_le_hasSum t (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hhas
  have hmem : ∀ k ∈ Icc 1 n, P k := fun k hk => mem_factored_of_mem_Icc hk
  have hmap :
      t.map (Function.Embedding.subtype P) = Icc 1 n :=
    Finset.subtype_map_of_mem hmem
  have hharm :
      (harmonic n : ℝ) = ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    refine sum_congr rfl fun k _ => ?_
    simp
  have hrew :
      ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ = ∑ x ∈ t, (x : ℝ)⁻¹ := by
    rw [← hmap, sum_map]
    rfl
  rw [hharm, hrew]
  exact hsum_le

private theorem eulerProdNat_le_inv_harmonic (n : ℕ)
    (hH : 0 < (harmonic n : ℝ)) :
    eulerProdNat n ≤ (harmonic n : ℝ)⁻¹ := by
  have hV := eulerProdNat_pos n
  have h := harmonic_le_inv_eulerProdNat n
  rwa [le_inv_comm₀ hH hV] at h

/-- Paper-scale upper bound: `V(y) ≤ 1 / log y` for `y ≥ 2`. -/
theorem eulerProd_le_inv_log {y : ℝ} (hy : 2 ≤ y) :
    eulerProd y ≤ 1 / Real.log y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hy
  have hlogy : 0 < Real.log y :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hy)
  have hlog : Real.log y ≤ (harmonic ⌊y⌋₊ : ℝ) :=
    log_le_harmonic_floor y hy0.le
  have hHpos : 0 < (harmonic ⌊y⌋₊ : ℝ) := lt_of_lt_of_le hlogy hlog
  calc
    eulerProd y = eulerProdNat ⌊y⌋₊ := rfl
    _ ≤ (harmonic ⌊y⌋₊ : ℝ)⁻¹ := eulerProdNat_le_inv_harmonic _ hHpos
    _ ≤ (Real.log y)⁻¹ := inv_anti₀ hlogy hlog
    _ = 1 / Real.log y := inv_eq_one_div _

/-! ### `log n!` and `∑ Λ(d)/d` -/

private theorem prod_Icc_one_eq_factorial (n : ℕ) :
    ∏ k ∈ Icc 1 n, k = Nat.factorial n := by
  rw [Nat.factorial_eq_prod_range_add_one]
  have hmap :
      (range n).map ⟨fun i => i + 1, add_left_injective 1⟩ = Icc 1 n := by
    ext k
    simp only [mem_map, mem_range, mem_Icc, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Nat.succ_le_succ (Nat.zero_le i), Nat.succ_le_of_lt hi⟩
    · intro hk
      refine ⟨k - 1, ?_, ?_⟩
      · omega
      · omega
  rw [← hmap, prod_map]
  simp

private theorem log_factorial_eq_sum_log (n : ℕ) :
    Real.log (Nat.factorial n) = ∑ k ∈ Icc 1 n, Real.log k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← prod_Icc_one_eq_factorial, Nat.cast_prod, Real.log_prod]
  intro k hk
  exact Nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hk).1))

private theorem log_factorial_le_mul_log {n : ℕ} (hn : 0 < n) :
    Real.log (Nat.factorial n) ≤ n * Real.log n := by
  rw [log_factorial_eq_sum_log]
  have hpt : ∀ k ∈ Icc 1 n, Real.log k ≤ Real.log n := fun k hk =>
    Real.log_le_log (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hk).1))
      (Nat.cast_le.mpr (mem_Icc.mp hk).2)
  calc
    ∑ k ∈ Icc 1 n, Real.log k ≤ ∑ k ∈ Icc 1 n, Real.log n := sum_le_sum hpt
    _ = #(Icc 1 n) * Real.log n := by rw [sum_const, nsmul_eq_mul]
    _ = n * Real.log n := by simp [Nat.card_Icc]

private theorem Icc_one_eq_Ioc_zero (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext k
  simp [Nat.succ_le_iff]

private theorem card_Icc_one_filter_dvd (n d : ℕ) :
    #{k ∈ Icc 1 n | d ∣ k} = n / d := by
  rw [Icc_one_eq_Ioc_zero, Nat.Ioc_filter_dvd_card_eq_div]

private theorem divisors_eq_filter_Icc {k n : ℕ} (hk : k ∈ Icc 1 n) :
    k.divisors = (Icc 1 n).filter (fun d => d ∣ k) := by
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · intro h
    have hkpos : 0 < k := Nat.pos_of_ne_zero h.2
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos h.1 hkpos
    have hdle : d ≤ k := Nat.le_of_dvd hkpos h.1
    exact ⟨⟨Nat.succ_le_of_lt hdpos, hdle.trans (mem_Icc.mp hk).2⟩, h.1⟩
  · intro h
    exact ⟨h.2, ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hk).1)⟩

private theorem sum_log_eq_sum_vonMangoldt_mul_div (n : ℕ) :
    ∑ k ∈ Icc 1 n, Real.log (k : ℝ) =
      ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
  have hlog : ∑ k ∈ Icc 1 n, Real.log k = ∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, Λ d :=
    sum_congr rfl fun k _ => (ArithmeticFunction.vonMangoldt_sum).symm
  rw [hlog]
  have hdiv : ∀ k ∈ Icc 1 n,
      ∑ d ∈ k.divisors, Λ d = ∑ d ∈ Icc 1 n, (if d ∣ k then Λ d else 0) := by
    intro k hk
    rw [divisors_eq_filter_Icc hk, sum_filter]
  rw [sum_congr rfl hdiv]
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have :
      ∑ k ∈ Icc 1 n, (if d ∣ k then Λ d else 0) =
        Λ d * (#{k ∈ Icc 1 n | d ∣ k} : ℝ) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  rw [this, card_Icc_one_filter_dvd]

private theorem cast_div_ge_sub_one {n d : ℕ} (hd : 0 < d) :
    (n : ℝ) / d - 1 ≤ ((n / d : ℕ) : ℝ) := by
  have hmod := Nat.div_add_mod n d
  have hcast : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, hmod]
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hsplit : (n : ℝ) / d = ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) / d := by
    rw [hcast, add_div, mul_div_cancel_left₀ _ hdpos.ne']
  have hlt : ((n % d : ℕ) : ℝ) / d < 1 := by
    rw [div_lt_one hdpos]
    exact_mod_cast Nat.mod_lt n hd
  linarith

private theorem psi_eq_sum_Icc_one (n : ℕ) :
    Chebyshev.psi n = ∑ d ∈ Icc 1 n, Λ d := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hI : Icc (0 : ℕ) n = insert 0 (Icc 1 n) := by
    ext k
    simp [mem_Icc, mem_insert]
    omega
  have h0 : 0 ∉ Icc 1 n := by simp
  rw [hI, sum_insert h0]
  have hΛ0 : Λ 0 = 0 := ArithmeticFunction.map_zero (f := Λ)
  rw [hΛ0, zero_add]

private theorem sum_vonMangoldt_div_le {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ Icc 1 n, Λ d / d ≤ Real.log n + Real.log 4 + 4 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog := log_factorial_eq_sum_log n
  have hid := sum_log_eq_sum_vonMangoldt_mul_div n
  have hfac : Real.log (Nat.factorial n) = ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
    rw [hlog, hid]
  have hle : ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) ≤
      ∑ d ∈ Icc 1 n, Λ d * ((n : ℝ) / d) := by
    refine sum_le_sum fun d hd => ?_
    have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd).1
    have hdiv := Nat.cast_div_le (α := ℝ) (m := n) (n := d)
    exact mul_le_mul_of_nonneg_left hdiv ArithmeticFunction.vonMangoldt_nonneg
  have hrw : ∑ d ∈ Icc 1 n, Λ d * ((n : ℝ) / d) =
      n * ∑ d ∈ Icc 1 n, Λ d / d := by
    have hpt : ∀ d ∈ Icc 1 n, Λ d * ((n : ℝ) / d) = (n : ℝ) * (Λ d / d) :=
      fun d hd => by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_left_comm (Λ d) (n : ℝ) (d : ℝ)⁻¹
    rw [sum_congr rfl hpt, ← mul_sum]
  have hψ : Chebyshev.psi n ≤ (Real.log 4 + 4) * n :=
    Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
  have hupper : Real.log (Nat.factorial n) ≤ n * ∑ d ∈ Icc 1 n, Λ d / d := by
    rw [hfac]
    have := hle
    rw [hrw] at this
    exact this
  -- Use `log n! ≥ n ∑ Λ/d - ψ(n)` for the matching upper bound of the sum.
  have hfloor :
      n * ∑ d ∈ Icc 1 n, Λ d / d - Chebyshev.psi n ≤ Real.log (Nat.factorial n) := by
    have hpt : ∀ d ∈ Icc 1 n, (n : ℝ) / d - 1 ≤ ((n / d : ℕ) : ℝ) := fun d hd =>
      cast_div_ge_sub_one (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd).1)
    have hsum :
        ∑ d ∈ Icc 1 n, Λ d * ((n : ℝ) / d - 1) ≤
          ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) :=
      sum_le_sum fun d hd =>
        mul_le_mul_of_nonneg_left (hpt d hd) ArithmeticFunction.vonMangoldt_nonneg
    have hleft :
        ∑ d ∈ Icc 1 n, Λ d * ((n : ℝ) / d - 1) =
          n * ∑ d ∈ Icc 1 n, Λ d / d - Chebyshev.psi n := by
      have hpt' : ∀ d ∈ Icc 1 n,
          Λ d * ((n : ℝ) / d - 1) = Λ d * ((n : ℝ) / d) - Λ d :=
        fun d hd => by rw [mul_sub, mul_one]
      rw [sum_congr rfl hpt', sum_sub_distrib, hrw, psi_eq_sum_Icc_one]
    have : n * ∑ d ∈ Icc 1 n, Λ d / d - Chebyshev.psi n ≤
        ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
      rwa [← hleft]
    exact this.trans (le_of_eq hfac.symm)
  have : ∑ d ∈ Icc 1 n, Λ d / d ≤ (Real.log (Nat.factorial n) + Chebyshev.psi n) / n := by
    have := hfloor
    rw [le_div_iff₀ hnR]
    linarith
  have hlogn : Real.log (Nat.factorial n) / n ≤ Real.log n := by
    have := log_factorial_le_mul_log hn
    rw [div_le_iff₀ hnR]
    simpa [mul_comm] using this
  have hψn : Chebyshev.psi n / n ≤ Real.log 4 + 4 := by
    rw [div_le_iff₀ hnR]
    simpa [mul_comm] using hψ
  calc
    ∑ d ∈ Icc 1 n, Λ d / d ≤ (Real.log (Nat.factorial n) + Chebyshev.psi n) / n := this
    _ = Real.log (Nat.factorial n) / n + Chebyshev.psi n / n := add_div _ _ _
    _ ≤ Real.log n + (Real.log 4 + 4) := add_le_add hlogn hψn
    _ = Real.log n + Real.log 4 + 4 := by ring

/-! ### Prime reciprocal sum via discrete Abel -/

/-- Weighted prime sum `∑_{p ≤ n} (log p)/p`. -/
noncomputable def chebyshevA (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n, Real.log p / p

private theorem chebyshevA_succ (n : ℕ) :
    chebyshevA (n + 1) =
      chebyshevA n +
        if Nat.Prime (n + 1) then
          Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)
        else 0 := by
  rw [chebyshevA, chebyshevA, Nat.primesLE_succ]
  split_ifs with hp
  · rw [sum_insert (Nat.notMem_primesLE n)]
    exact add_comm _ _
  · rw [add_zero]

private theorem chebyshevA_zero : chebyshevA 0 = 0 := by
  simp [chebyshevA]

private theorem chebyshevA_one : chebyshevA 1 = 0 := by
  simp [chebyshevA]

private theorem chebyshevA_nonneg (n : ℕ) : 0 ≤ chebyshevA n :=
  sum_nonneg fun p hp =>
    div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr
      (Nat.Prime.one_le (Nat.prime_of_mem_primesLE hp))))
      (Nat.cast_nonneg _)

private theorem chebyshevA_le_sum_vonMangoldt (n : ℕ) :
    chebyshevA n ≤ ∑ d ∈ Icc 1 n, Λ d / d := by
  rw [chebyshevA, Nat.primesLE_eq_filter_Icc_one, sum_filter]
  refine sum_le_sum fun d hd => ?_
  split_ifs with hp
  · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

private theorem chebyshevA_le_log_add {n : ℕ} (hn : 0 < n) :
    chebyshevA n ≤ Real.log n + Real.log 4 + 4 :=
  (chebyshevA_le_sum_vonMangoldt n).trans (sum_vonMangoldt_div_le hn)

private theorem chebyshevA_diff {k : ℕ} (hk : 2 ≤ k) :
    chebyshevA k - chebyshevA (k - 1) =
      if Nat.Prime k then Real.log k / k else 0 := by
  have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel (Nat.le_trans (by norm_num : (1 : ℕ) ≤ 2) hk)).symm
  rw [hk', chebyshevA_succ]
  simp

private theorem sum_prime_inv_eq_abel {n : ℕ} (hn : 2 ≤ n) :
    ∑ p ∈ Nat.primesLE n, (p : ℝ)⁻¹ =
      chebyshevA n / Real.log n +
        ∑ k ∈ Icc 2 (n - 1),
          chebyshevA k * (1 / Real.log k - 1 / Real.log (k + 1)) := by
  have hlogn : Real.log n ≠ 0 :=
    (Real.log_pos (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hn))).ne'
  have hterm : ∀ k : ℕ, 2 ≤ k → k ≤ n →
      (if Nat.Prime k then (k : ℝ)⁻¹ else 0) =
        (chebyshevA k - chebyshevA (k - 1)) / Real.log k := by
    intro k hk2 hkn
    have hlogk : Real.log k ≠ 0 :=
      (Real.log_pos (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hk2))).ne'
    rw [chebyshevA_diff hk2]
    split_ifs with hp
    · field_simp [hlogk]
    · simp
  have hprimes :
      ∑ p ∈ Nat.primesLE n, (p : ℝ)⁻¹ =
        ∑ k ∈ Icc 2 n, (if Nat.Prime k then (k : ℝ)⁻¹ else 0) := by
    rw [Nat.primesLE_eq_filter_Icc_two, sum_filter]
  rw [hprimes]
  have hdiff :
      ∑ k ∈ Icc 2 n, (if Nat.Prime k then (k : ℝ)⁻¹ else 0) =
        ∑ k ∈ Icc 2 n, (chebyshevA k - chebyshevA (k - 1)) / Real.log k :=
    sum_congr rfl fun k hk => by
      have hk' := mem_Icc.mp hk
      exact hterm k hk'.1 hk'.2
  rw [hdiff]
  have hn1 : 1 ≤ n - 1 := by omega
  have hsplit :
      ∑ k ∈ Icc 2 n, (chebyshevA k - chebyshevA (k - 1)) / Real.log k =
        ∑ k ∈ Icc 2 n, chebyshevA k / Real.log k -
          ∑ k ∈ Icc 2 n, chebyshevA (k - 1) / Real.log k := by
    simp_rw [sub_div, sum_sub_distrib]
  rw [hsplit]
  have hshift :
      ∑ k ∈ Icc 2 n, chebyshevA (k - 1) / Real.log k =
        ∑ k ∈ Icc 1 (n - 1), chebyshevA k / Real.log (k + 1) := by
    refine sum_nbij (fun k => k - 1) ?_ ?_ ?_ ?_
    · intro k hk
      have hk' := mem_Icc.mp hk
      refine mem_Icc.mpr ⟨Nat.le_sub_of_add_le (by omega), Nat.sub_le_sub_right hk'.2 1⟩
    · intro a ha b hb h
      have ha2 : 1 ≤ a := le_trans (by norm_num : (1 : ℕ) ≤ 2) (mem_Icc.mp ha).1
      have hb2 : 1 ≤ b := le_trans (by norm_num : (1 : ℕ) ≤ 2) (mem_Icc.mp hb).1
      exact
        (Nat.sub_add_cancel ha2).symm.trans
          ((congrArg (fun t => t + 1) h).trans (Nat.sub_add_cancel hb2))
    · intro k hk
      have hk' := mem_Icc.mp hk
      refine ⟨k + 1, mem_Icc.mpr ⟨by omega, by omega⟩, Nat.add_sub_cancel k 1⟩
    · intro k hk
      have hk' := mem_Icc.mp hk
      have hk1 : 1 ≤ k := le_trans (by norm_num : (1 : ℕ) ≤ 2) hk'.1
      have hcast : ((k - 1 : ℕ) : ℝ) + 1 = k := by
        exact_mod_cast Nat.sub_add_cancel hk1
      simp [hcast]
  rw [hshift]
  have hA1 : chebyshevA 1 = 0 := chebyshevA_one
  have hI :
      Icc 1 (n - 1) = insert 1 (Icc 2 (n - 1)) := by
    have : 1 ≤ n - 1 := hn1
    exact (insert_Icc_add_one_left_eq_Icc this).symm
  have h1mem : 1 ∉ Icc 2 (n - 1) := by simp
  rw [hI, sum_insert h1mem, hA1, zero_div, zero_add]
  have hlast : Icc 2 n = insert n (Icc 2 (n - 1)) := by
    have hn' : n = n - 1 + 1 :=
      (Nat.sub_add_cancel (Nat.le_trans (by norm_num : (1 : ℕ) ≤ 2) hn)).symm
    rw [hn']
    exact (insert_Icc_right_eq_Icc_add_one
      (show 2 ≤ n - 1 + 1 by omega)).symm
  have hnmem : n ∉ Icc 2 (n - 1) := by simp [mem_Icc]; omega
  rw [hlast, sum_insert hnmem]
  have hmid :
      ∑ k ∈ Icc 2 (n - 1), chebyshevA k / Real.log k -
          ∑ k ∈ Icc 2 (n - 1), chebyshevA k / Real.log (k + 1) =
        ∑ k ∈ Icc 2 (n - 1),
          chebyshevA k * (1 / Real.log k - 1 / Real.log (k + 1)) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, one_div, one_div]
  linarith

private theorem log_two_lt_one : Real.log 2 < 1 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr Real.exp_one_gt_two

private theorem log_four_lt_two : Real.log 4 < 2 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
    ring
  linarith [log_two_lt_one]

private theorem antitoneOn_inv_mul_log :
    AntitoneOn (fun t : ℝ => (t * Real.log t)⁻¹) (Set.Ici 2) := by
  intro x hx y hy hxy
  have hx2 : (2 : ℝ) ≤ x := hx
  have hy2 : (2 : ℝ) ≤ y := hy
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx2
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hy2
  have hlogx : 0 < Real.log x :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hx2)
  have hlogy : 0 < Real.log y :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hy2)
  have hmul : x * Real.log x ≤ y * Real.log y :=
    mul_le_mul hxy (Real.log_le_log hx0 hxy) hlogx.le hy0.le
  have hden : 0 < x * Real.log x := mul_pos hx0 hlogx
  exact inv_anti₀ hden hmul

private theorem sum_Ico_telescope (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, (f k - f (k + 1)) = f m - f n := by
  refine Nat.le_induction ?base ?step n hmn
  · simp
  · intro n hmn ih
    rw [sum_Ico_succ_top hmn, ih]
    ring

private theorem inv_mul_log_eq {t : ℝ} (ht : 1 < t) :
    (t * Real.log t)⁻¹ = t⁻¹ / Real.log t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) ht)
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  field_simp [ht0, hlog]

private theorem inv_log_two_lt_two : (Real.log 2)⁻¹ < 2 := by
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [inv_lt_comm₀ hpos (by norm_num : (0 : ℝ) < 2)]
  have := Real.log_two_gt_d9
  linarith

private theorem inv_two_mul_log_two_le_one :
    ((2 : ℝ) * Real.log 2)⁻¹ ≤ 1 := by
  have hpos : 1 ≤ 2 * Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  exact inv_le_one_of_one_le₀ hpos

private theorem neg_log_log_two_le_one : -Real.log (Real.log 2) ≤ 1 := by
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv : (Real.log 2)⁻¹ ≤ 2 := inv_log_two_lt_two.le
  have : Real.log ((Real.log 2)⁻¹) ≤ Real.log 2 :=
    Real.log_le_log (inv_pos.mpr hpos) hinv
  have : -Real.log (Real.log 2) = Real.log ((Real.log 2)⁻¹) :=
    (Real.log_inv (Real.log 2)).symm
  linarith [log_two_lt_one]

private theorem log_ge_two_of_le_sixteen {n : ℕ} (hn : 16 ≤ n) :
    (2 : ℝ) ≤ Real.log n := by
  have hn16 : (16 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
    ring
  have h2 : (2 : ℝ) ≤ Real.log 16 := by
    rw [h16]
    have := Real.log_two_gt_d9
    linarith
  exact le_trans h2 (Real.log_le_log (by positivity) hn16)

private theorem chebyshevConst_lt_six : Real.log 4 + 4 < 6 := by
  linarith [log_four_lt_two]

private theorem delta_nonneg {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ 1 / Real.log k - 1 / Real.log ((k : ℝ) + 1) := by
  have hk1 : (0 : ℝ) < k :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hk)
  have hlogk : 0 < Real.log k :=
    Real.log_pos (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hk))
  have hlt : (1 : ℝ) < (k : ℝ) + 1 := by
    have : (1 : ℝ) < k := Nat.one_lt_cast.mpr
      (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hk)
    linarith
  have hlogk1 : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos hlt
  have hle : Real.log k ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_le_log hk1 (by linarith)
  simpa [one_div] using sub_nonneg.mpr (inv_anti₀ hlogk hle)

private theorem log_mul_delta_le {k : ℕ} (hk : 2 ≤ k) :
    Real.log k * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) ≤
      (k * Real.log k : ℝ)⁻¹ := by
  have hkpos : (0 : ℝ) < k :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hk)
  have hlogk : 0 < Real.log k :=
    Real.log_pos (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hk))
  have hlt : (1 : ℝ) < (k : ℝ) + 1 := by
    have : (1 : ℝ) < k := Nat.one_lt_cast.mpr
      (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hk)
    linarith
  have hlogk1 : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos hlt
  have hdiff :
      Real.log k * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) =
        Real.log (1 + (k : ℝ)⁻¹) / Real.log ((k : ℝ) + 1) := by
    have hlogkne : Real.log k ≠ 0 := hlogk.ne'
    have hlogk1ne : Real.log ((k : ℝ) + 1) ≠ 0 := hlogk1.ne'
    have h1 : Real.log k * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) =
        1 - Real.log k / Real.log ((k : ℝ) + 1) := by
      field_simp [hlogkne]
    have h2 : 1 - Real.log k / Real.log ((k : ℝ) + 1) =
        (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1) := by
      field_simp [hlogk1ne]
    have h3 : Real.log ((k : ℝ) + 1) - Real.log k =
        Real.log (((k : ℝ) + 1) / k) :=
      (Real.log_div (by positivity) hkpos.ne').symm
    have h4 : (((k : ℝ) + 1) / k) = 1 + (k : ℝ)⁻¹ := by
      field_simp [hkpos.ne']
    rw [h1, h2, h3, h4]
  have hlog1 : Real.log (1 + (k : ℝ)⁻¹) ≤ (k : ℝ)⁻¹ := by
    have := Real.log_le_sub_one_of_pos
      (add_pos (by norm_num : (0 : ℝ) < 1) (inv_pos.mpr hkpos))
    simpa using this
  have hden : Real.log k ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_le_log hkpos (by linarith)
  have h1 :
      Real.log (1 + (k : ℝ)⁻¹) / Real.log ((k : ℝ) + 1) ≤
        (k : ℝ)⁻¹ / Real.log ((k : ℝ) + 1) :=
    div_le_div_of_nonneg_right hlog1 hlogk1.le
  have h2 :
      (k : ℝ)⁻¹ / Real.log ((k : ℝ) + 1) ≤ (k : ℝ)⁻¹ / Real.log k :=
    div_le_div_of_nonneg_left (inv_nonneg.mpr hkpos.le) hlogk hden
  have h3 : (k : ℝ)⁻¹ / Real.log k = (k * Real.log k)⁻¹ := by
    field_simp [hkpos.ne', hlogk.ne']
  calc
    Real.log k * (1 / Real.log k - 1 / Real.log ((k : ℝ) + 1)) =
        Real.log (1 + (k : ℝ)⁻¹) / Real.log ((k : ℝ) + 1) := hdiff
    _ ≤ (k : ℝ)⁻¹ / Real.log k := h1.trans h2
    _ = (k * Real.log k)⁻¹ := h3

private theorem sum_inv_mul_log_le {n : ℕ} (hn : 16 ≤ n) :
    ∑ k ∈ Icc 2 (n - 1), (k * Real.log k : ℝ)⁻¹ ≤
      Real.log (Real.log n) + 2 := by
  have hn1 : 3 ≤ n - 1 := by omega
  have h2le : (2 : ℕ) ≤ n - 1 := le_trans (by norm_num : (2 : ℕ) ≤ 3) hn1
  have hI : Icc 2 (n - 1) = insert 2 (Icc 3 (n - 1)) :=
    (insert_Icc_add_one_left_eq_Icc h2le).symm
  have h2mem : 2 ∉ Icc 3 (n - 1) := by simp
  have hanti :
      AntitoneOn (fun t : ℝ => (t * Real.log t)⁻¹)
        (Set.Icc (2 : ℝ) ((n - 1 : ℕ) : ℝ)) :=
    antitoneOn_inv_mul_log.mono fun t ht => ht.1
  have htail :=
    AntitoneOn.sum_le_integral_Ico (a := 2) (b := n - 1) (f := fun t : ℝ => (t * Real.log t)⁻¹)
      h2le hanti
  have hmap :
      ∑ i ∈ Ico 2 (n - 1), ((i + 1 : ℕ) * Real.log (i + 1 : ℕ) : ℝ)⁻¹ =
        ∑ k ∈ Icc 3 (n - 1), (k * Real.log k : ℝ)⁻¹ := by
    refine sum_nbij (fun i => i + 1) ?_ ?_ ?_ ?_
    · intro i hi
      have hi' := mem_Ico.mp hi
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a _ha b _hb h
      exact Nat.succ_injective h
    · intro k hk
      have hk' := mem_Icc.mp hk
      refine ⟨k - 1, mem_Ico.mpr ⟨by omega, by omega⟩, Nat.sub_add_cancel (by omega)⟩
    · intro i _hi
      rfl
  have hb : (1 : ℝ) < (n - 1 : ℕ) :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hn1)
  have hint :
      (∫ t in (2 : ℝ)..((n - 1 : ℕ) : ℝ), (t * Real.log t)⁻¹) =
        Real.log (Real.log ((n - 1 : ℕ) : ℝ)) - Real.log (Real.log 2) := by
    have hcongr :
        ∀ t ∈ [[(2 : ℝ), ((n - 1 : ℕ) : ℝ)]],
          (t * Real.log t)⁻¹ = t⁻¹ / Real.log t := by
      intro t ht
      have hminmax :
          [[(2 : ℝ), ((n - 1 : ℕ) : ℝ)]] =
            Set.Icc (2 : ℝ) ((n - 1 : ℕ) : ℝ) :=
        Set.uIcc_of_le (Nat.cast_le.mpr h2le)
      rw [hminmax] at ht
      exact inv_mul_log_eq (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ht.1)
    rw [intervalIntegral.integral_congr hcongr]
    exact integral_inv_div_log (by norm_num) hb
  have hll :
      Real.log (Real.log ((n - 1 : ℕ) : ℝ)) ≤ Real.log (Real.log n) := by
    have hn1pos : (0 : ℝ) < (n - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
    have hle : ((n - 1 : ℕ) : ℝ) ≤ n := Nat.cast_le.mpr (Nat.sub_le _ _)
    have hlog1 : 0 < Real.log ((n - 1 : ℕ) : ℝ) :=
      Real.log_pos (Nat.one_lt_cast.mpr
        (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hn1))
    exact Real.log_le_log hlog1 (Real.log_le_log hn1pos hle)
  have hsum3 :
      ∑ k ∈ Icc 3 (n - 1), (k * Real.log k : ℝ)⁻¹ ≤
        Real.log (Real.log n) + 1 := by
    calc
      ∑ k ∈ Icc 3 (n - 1), (k * Real.log k : ℝ)⁻¹ ≤
          ∫ t in (2 : ℝ)..((n - 1 : ℕ) : ℝ), (t * Real.log t)⁻¹ := by
        rw [← hmap]; exact htail
      _ = Real.log (Real.log ((n - 1 : ℕ) : ℝ)) - Real.log (Real.log 2) := hint
      _ ≤ Real.log (Real.log n) + 1 := by
        linarith [hll, neg_log_log_two_le_one]
  have h2term : ((2 : ℝ) * Real.log 2)⁻¹ ≤ 1 := inv_two_mul_log_two_le_one
  rw [hI, sum_insert h2mem]
  linarith

private theorem sum_prime_inv_le_log_log {n : ℕ} (hn : 16 ≤ n) :
    ∑ p ∈ Nat.primesLE n, (p : ℝ)⁻¹ ≤ Real.log (Real.log n) + 25 := by
  have hn2 : 2 ≤ n := le_trans (by norm_num : (2 : ℕ) ≤ 16) hn
  have hn16 : (16 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hlogn : 0 < Real.log n :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) hn16)
  have habel := sum_prime_inv_eq_abel hn2
  have hΔpos : ∀ k ∈ Icc 2 (n - 1),
      0 ≤ 1 / Real.log k - 1 / Real.log (k + 1) := fun k hk =>
    delta_nonneg (mem_Icc.mp hk).1
  have hAn' : chebyshevA n / Real.log n ≤ 8 := by
    have hA := chebyshevA_le_log_add (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2)
    have hC0 : (0 : ℝ) ≤ Real.log 4 + 4 := by
      have : 0 < Real.log 4 := Real.log_pos (by norm_num)
      linarith
    have hC : Real.log 4 + 4 ≤ 6 := chebyshevConst_lt_six.le
    have hlogn_ge := log_ge_two_of_le_sixteen hn
    have hdiv : (Real.log 4 + 4) / Real.log n ≤ 6 / 2 :=
      (div_le_div_of_nonneg_left hC0 (by norm_num : (0 : ℝ) < 2) hlogn_ge).trans
        (div_le_div_of_nonneg_right hC (by norm_num : (0 : ℝ) ≤ 2))
    have hA' : chebyshevA n ≤ Real.log n + (Real.log 4 + 4) := by linarith [hA]
    have : chebyshevA n / Real.log n ≤
        (Real.log n + (Real.log 4 + 4)) / Real.log n :=
      div_le_div_of_nonneg_right hA' hlogn.le
    have hrw : (Real.log n + (Real.log 4 + 4)) / Real.log n =
        1 + (Real.log 4 + 4) / Real.log n := by
      field_simp [hlogn.ne']
    linarith
  have hΔsum :
      ∑ k ∈ Icc 2 (n - 1), (1 / Real.log k - 1 / Real.log (k + 1)) =
        1 / Real.log 2 - 1 / Real.log n := by
    have hI : Icc 2 (n - 1) = Ico 2 n := by
      ext k
      simp [mem_Icc, mem_Ico]
      omega
    rw [hI]
    simpa using sum_Ico_telescope (fun t => 1 / Real.log t) hn2
  have hΔbound :
      ∑ k ∈ Icc 2 (n - 1), (1 / Real.log k - 1 / Real.log (k + 1)) ≤ 2 := by
    rw [hΔsum]
    have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : 1 / Real.log 2 ≤ 2 := by
      rw [one_div]
      exact inv_log_two_lt_two.le
    have : 0 ≤ 1 / Real.log n := div_nonneg zero_le_one hlogn.le
    linarith
  have hAΔ :
      ∑ k ∈ Icc 2 (n - 1),
          chebyshevA k * (1 / Real.log k - 1 / Real.log (k + 1)) ≤
        Real.log (Real.log n) + 14 := by
    have hpt : ∀ k ∈ Icc 2 (n - 1),
        chebyshevA k * (1 / Real.log k - 1 / Real.log (k + 1)) ≤
          (Real.log k + 6) * (1 / Real.log k - 1 / Real.log (k + 1)) := by
      intro k hk
      have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) (mem_Icc.mp hk).1
      have hA : chebyshevA k ≤ Real.log k + 6 := by
        linarith [chebyshevA_le_log_add hk0, chebyshevConst_lt_six]
      exact mul_le_mul_of_nonneg_right hA (hΔpos k hk)
    have hsum := sum_le_sum hpt
    have hsplit :
        ∑ k ∈ Icc 2 (n - 1),
            (Real.log k + 6) * (1 / Real.log k - 1 / Real.log (k + 1)) =
          ∑ k ∈ Icc 2 (n - 1),
              Real.log k * (1 / Real.log k - 1 / Real.log (k + 1)) +
            6 * ∑ k ∈ Icc 2 (n - 1), (1 / Real.log k - 1 / Real.log (k + 1)) := by
      simp_rw [add_mul, sum_add_distrib, mul_sum]
    have hlogs :
        ∑ k ∈ Icc 2 (n - 1),
            Real.log k * (1 / Real.log k - 1 / Real.log (k + 1)) ≤
          ∑ k ∈ Icc 2 (n - 1), (k * Real.log k : ℝ)⁻¹ :=
      sum_le_sum fun k hk => log_mul_delta_le (mem_Icc.mp hk).1
    have h6 : 6 * ∑ k ∈ Icc 2 (n - 1), (1 / Real.log k - 1 / Real.log (k + 1)) ≤ 12 := by
      have : (6 : ℝ) * 2 = 12 := by norm_num
      have := mul_le_mul_of_nonneg_left hΔbound (by norm_num : (0 : ℝ) ≤ 6)
      linarith
    have hinv := sum_inv_mul_log_le hn
    linarith
  calc
    ∑ p ∈ Nat.primesLE n, (p : ℝ)⁻¹ =
        chebyshevA n / Real.log n +
          ∑ k ∈ Icc 2 (n - 1),
            chebyshevA k * (1 / Real.log k - 1 / Real.log (k + 1)) := habel
    _ ≤ 8 + (Real.log (Real.log n) + 14) := add_le_add hAn' hAΔ
    _ = Real.log (Real.log n) + 22 := by ring
    _ ≤ Real.log (Real.log n) + 25 := by linarith

private theorem inv_mul_pred_eq {p : ℕ} (hp : 2 ≤ p) :
    ((p : ℝ) - 1)⁻¹ = (p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
  have hp0 : (p : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hp))
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p :=
      Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hp)
    linarith
  field_simp [hp0, hp1]
  ring

private theorem sum_inv_mul_pred_Icc (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 2 n, ((k : ℝ) * ((k : ℝ) - 1))⁻¹ = 1 - (n : ℝ)⁻¹ := by
  have hpart : ∀ k ∈ Icc 2 n,
      ((k : ℝ) * ((k : ℝ) - 1))⁻¹ = ((k : ℝ) - 1)⁻¹ - (k : ℝ)⁻¹ := by
    intro k hk
    have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
    have hk0 : (k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr
        (Nat.ne_zero_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hk2))
    have hk1 : (k : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < k :=
        Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hk2)
      linarith
    field_simp [hk0, hk1]
    ring
  have hI : Icc 2 n = (Ico 1 n).map ⟨fun j => j + 1, add_left_injective 1⟩ := by
    ext k
    simp [mem_Icc, mem_Ico, mem_map]
    constructor
    · intro hk
      refine ⟨k - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  have htel := sum_Ico_telescope (fun j => (j : ℝ)⁻¹) hn
  calc
    ∑ k ∈ Icc 2 n, ((k : ℝ) * ((k : ℝ) - 1))⁻¹ =
        ∑ k ∈ Icc 2 n, (((k : ℝ) - 1)⁻¹ - (k : ℝ)⁻¹) :=
      sum_congr rfl hpart
    _ = ∑ j ∈ Ico 1 n, ((j : ℝ)⁻¹ - ((j + 1 : ℝ)⁻¹)) := by
      rw [hI, sum_map]
      refine sum_congr rfl fun j hj => ?_
      simp
    _ = (1 : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
      simpa using htel
    _ = 1 - (n : ℝ)⁻¹ := by simp

private theorem sum_prime_inv_sub_one_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ p ∈ Nat.primesLE n, ((p : ℝ) - 1)⁻¹ ≤
      ∑ p ∈ Nat.primesLE n, (p : ℝ)⁻¹ + 1 := by
  have hpt : ∀ p ∈ Nat.primesLE n,
      ((p : ℝ) - 1)⁻¹ = (p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := fun p hp =>
    inv_mul_pred_eq (Nat.prime_of_mem_primesLE hp).two_le
  have hsum :
      ∑ p ∈ Nat.primesLE n, ((p : ℝ) - 1)⁻¹ =
        ∑ p ∈ Nat.primesLE n, (p : ℝ)⁻¹ +
          ∑ p ∈ Nat.primesLE n, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
    rw [sum_congr rfl hpt, sum_add_distrib]
  have hsub : Nat.primesLE n ⊆ Icc 2 n := by
    intro p hp
    exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).two_le,
      (Nat.mem_primesLE.mp hp).1⟩
  have hpos : ∀ k ∈ Icc 2 n, 0 ≤ ((k : ℝ) * ((k : ℝ) - 1))⁻¹ := fun k hk => by
    have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k :=
      Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hk2)
    have hk1 : (0 : ℝ) < k - 1 := by
      have : (1 : ℝ) < k :=
        Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hk2)
      linarith
    exact inv_nonneg.mpr (mul_nonneg hk0.le hk1.le)
  have hcomp :
      ∑ p ∈ Nat.primesLE n, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ ≤
        ∑ k ∈ Icc 2 n, ((k : ℝ) * ((k : ℝ) - 1))⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => hpos k hk
  have htel := sum_inv_mul_pred_Icc n (le_trans (by norm_num : (1 : ℕ) ≤ 2) hn)
  have : ∑ k ∈ Icc 2 n, ((k : ℝ) * ((k : ℝ) - 1))⁻¹ ≤ 1 := by
    rw [htel]
    have : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    linarith
  linarith

private theorem log_one_sub_inv_ge {p : ℕ} (hp : Nat.Prime p) :
    -((p : ℝ) - 1)⁻¹ ≤ Real.log (1 - (p : ℝ)⁻¹) := by
  have hx : 0 < 1 - (p : ℝ)⁻¹ := one_sub_inv_pos hp
  have h := Real.one_sub_inv_le_log_of_pos hx
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hp1)
  have hden : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hp1)
  have hinv : (1 - (p : ℝ)⁻¹)⁻¹ = p / (p - 1) := by
    field_simp [hp0, hden]
  have hid : 1 - (1 - (p : ℝ)⁻¹)⁻¹ = -((p : ℝ) - 1)⁻¹ := by
    rw [hinv]
    field_simp [hden]
    ring
  rwa [hid] at h

private theorem log_eulerProdNat_eq (n : ℕ) :
    Real.log (eulerProdNat n) =
      ∑ p ∈ Nat.primesLE n, Real.log (1 - (p : ℝ)⁻¹) := by
  rw [eulerProdNat, Real.log_prod]
  intro p hp
  exact one_sub_inv_ne_zero (Nat.prime_of_mem_primesLE hp)

private theorem log_eulerProdNat_ge {n : ℕ} (hn : 16 ≤ n) :
    Real.log (Real.log n) + 30 ≥ -Real.log (eulerProdNat n) := by
  have hn2 : 2 ≤ n := le_trans (by norm_num : (2 : ℕ) ≤ 16) hn
  have hlog :
      Real.log (eulerProdNat n) ≥
        -∑ p ∈ Nat.primesLE n, ((p : ℝ) - 1)⁻¹ := by
    rw [log_eulerProdNat_eq]
    have hpt : ∀ p ∈ Nat.primesLE n,
        -((p : ℝ) - 1)⁻¹ ≤ Real.log (1 - (p : ℝ)⁻¹) := fun p hp =>
      log_one_sub_inv_ge (Nat.prime_of_mem_primesLE hp)
    have := sum_le_sum hpt
    simpa [sum_neg_distrib] using this
  have hsum1 := sum_prime_inv_sub_one_le hn2
  have hsum2 := sum_prime_inv_le_log_log hn
  have : -Real.log (eulerProdNat n) ≤
      ∑ p ∈ Nat.primesLE n, ((p : ℝ) - 1)⁻¹ := by
    linarith
  linarith

/-- Weak Mertens lower bound: `e^{-30} / log n ≤ V(n)` for `n ≥ 16`. -/
theorem eulerProdNat_ge_mul_inv_log {n : ℕ} (hn : 16 ≤ n) :
    eulerProdLowerConst / Real.log n ≤ eulerProdNat n := by
  have hn16 : (16 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hlogn : 0 < Real.log n :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) hn16)
  have hV : 0 < eulerProdNat n := eulerProdNat_pos n
  have hlogV := log_eulerProdNat_ge hn
  have hcmp : Real.log (eulerProdLowerConst / Real.log n) ≤ Real.log (eulerProdNat n) := by
    have : Real.log (eulerProdLowerConst / Real.log n) =
        -((30 : ℝ) + Real.log (Real.log n)) := by
      rw [eulerProdLowerConst, Real.log_div (ne_of_gt (Real.exp_pos _)) hlogn.ne',
        Real.log_exp]
      ring
    linarith [log_eulerProdNat_ge hn]
  exact (Real.log_le_log_iff (div_pos (Real.exp_pos _) hlogn) hV).mp hcmp

/-- Paper-scale lower bound: `e^{-30} / log y ≤ V(y)` for `y ≥ 16`. -/
theorem eulerProd_ge_mul_inv_log {y : ℝ} (hy : 16 ≤ y) :
    eulerProdLowerConst / Real.log y ≤ eulerProd y := by
  have hy0 : 0 ≤ y := le_trans (by norm_num : (0 : ℝ) ≤ 16) hy
  have hfl : 16 ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy0).mpr hy
  have hlogy : 0 < Real.log y :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) hy)
  have hlogfl : 0 < Real.log (⌊y⌋₊ : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr
      (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 16) hfl))
  have hle : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y :=
    Real.log_le_log (Nat.cast_pos.mpr
      (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 16) hfl)) (Nat.floor_le hy0)
  calc
    eulerProdLowerConst / Real.log y ≤
        eulerProdLowerConst / Real.log (⌊y⌋₊ : ℝ) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hlogfl hle
    _ ≤ eulerProdNat ⌊y⌋₊ := eulerProdNat_ge_mul_inv_log hfl
    _ = eulerProd y := rfl

/-- Weak two-sided bound sufficient for polylog error budgets. `C = 1`. -/
theorem eulerProd_two_sided {y : ℝ} (hy : 16 ≤ y) :
    eulerProdLowerConst / Real.log y ≤ eulerProd y ∧
      eulerProd y ≤ 1 / Real.log y :=
  ⟨eulerProd_ge_mul_inv_log hy,
    eulerProd_le_inv_log (le_trans (by norm_num : (2 : ℝ) ≤ 16) hy)⟩

theorem eulerProd_coe_nat (n : ℕ) : eulerProd n = eulerProdNat n := by
  simp [eulerProd, Nat.floor_natCast]

theorem eulerProdNat_prime {y : ℕ} (hy : Nat.Prime y) :
    eulerProdNat y = eulerProdNat (y - 1) * (1 - (y : ℝ)⁻¹) := by
  have hy' : y = y - 1 + 1 := (Nat.sub_add_cancel hy.one_le).symm
  have hP : Nat.Prime (y - 1 + 1) := by rwa [← hy']
  rw [hy', eulerProdNat, eulerProdNat, Nat.primesLE_succ, if_pos hP,
    prod_insert (Nat.notMem_primesLE (y - 1))]
  simp [← hy']
  ring

private theorem one_lt_of_exp_sixteen_le {t : ℝ} (ht : Real.exp 16 ≤ t) :
    1 < t :=
  lt_of_lt_of_le
    (lt_trans (by norm_num : (1 : ℝ) < 2)
      (lt_trans Real.exp_one_gt_two
        (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16))))
    ht

private theorem log_t_ge_sixteen {t : ℝ} (ht : Real.exp 16 ≤ t) :
    (16 : ℝ) ≤ Real.log t := by
  have := Real.log_le_log (Real.exp_pos _) ht
  rwa [Real.log_exp] at this

/-- Jump at the paper cutoff: minimality forces
`(1-1/y)/log t < V(y) ≤ 1/log t`. -/
theorem isSieveCutoff_jump {t : ℝ} {y : ℕ} (ht : Real.exp 16 ≤ t)
    (hy : IsSieveCutoff t y) :
    (1 - (y : ℝ)⁻¹) / Real.log t < eulerProd y := by
  have ht1 := one_lt_of_exp_sixteen_le ht
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hyP : Nat.Prime y := hy.1
  have hVy : eulerProd y = eulerProdNat (y - 1) * (1 - (y : ℝ)⁻¹) := by
    rw [eulerProd_coe_nat, eulerProdNat_prime hyP]
  have hy2 : 2 ≤ y := hyP.two_le
  have hprev : 1 / Real.log t < eulerProdNat (y - 1) := by
    rcases eq_or_lt_of_le hy2 with hyeq | hygt
    · have hyeq' : y = 2 := hyeq.symm
      subst hyeq'
      have h1 : eulerProdNat 1 = 1 := by simp [eulerProdNat]
      have hlt : 1 / Real.log t < 1 :=
        (div_lt_one hlogt).mpr (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16)
          (log_t_ge_sixteen ht))
      rwa [h1]
    · have hne : (Nat.primesLE (y - 1)).Nonempty :=
        ⟨2, Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩⟩
      let p := (Nat.primesLE (y - 1)).max' hne
      have hpmem := (Nat.primesLE (y - 1)).max'_mem hne
      have hp : Nat.Prime p := Nat.prime_of_mem_primesLE hpmem
      have hple : p ≤ y - 1 := (Nat.mem_primesLE.mp hpmem).1
      have hplt : p < y := by omega
      have hset : Nat.primesLE (y - 1) = Nat.primesLE p := by
        apply le_antisymm
        · intro q hq
          exact Nat.mem_primesLE.mpr
            ⟨(isGreatest_max' (Nat.primesLE (y - 1)) hne).2 hq,
              Nat.prime_of_mem_primesLE hq⟩
        · exact Nat.primesLE_mono hple
      have hVp : eulerProdNat (y - 1) = eulerProd p := by
        rw [eulerProd_coe_nat, eulerProdNat, eulerProdNat, hset]
      have := hy.2.2 p hp hplt
      rwa [hVp]
  have hfac : 0 < 1 - (y : ℝ)⁻¹ := one_sub_inv_pos hyP
  have hmul := mul_lt_mul_of_pos_right hprev hfac
  have hrew : (1 - (y : ℝ)⁻¹) / Real.log t =
      (1 / Real.log t) * (1 - (y : ℝ)⁻¹) := by
    field_simp
  rw [hVy, hrew]
  exact hmul

/-- A prime with `V(p) ≤ 1/log t` exists for every `t > 1`. -/
theorem exists_isSieveCutoff {t : ℝ} (ht : 1 < t) :
    ∃ y, IsSieveCutoff t y := by
  have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht
  have hlogt : 0 < Real.log t := Real.log_pos ht
  let s : Set ℕ := {p | Nat.Prime p ∧ eulerProd p ≤ 1 / Real.log t}
  have hne : s.Nonempty := by
    obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max 2 ⌈t⌉₊)
    have hp2 : 2 ≤ p := le_trans (le_max_left _ _) hpN
    have hpt : t ≤ p := by
      have : ⌈t⌉₊ ≤ p := le_trans (le_max_right _ _) hpN
      exact le_trans (Nat.le_ceil t) (Nat.cast_le.mpr this)
    have h2p : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp2
    have hVp : eulerProd p ≤ 1 / Real.log p := eulerProd_le_inv_log h2p
    have hlogp : Real.log t ≤ Real.log p := Real.log_le_log ht0 hpt
    have hinv : 1 / Real.log p ≤ 1 / Real.log t :=
      one_div_le_one_div_of_le hlogt hlogp
    exact ⟨p, hp, hVp.trans hinv⟩
  let y := wellFounded_lt.min s hne
  have hymem : y ∈ s := wellFounded_lt.min_mem s hne
  refine ⟨y, hymem.1, hymem.2, ?_⟩
  intro p hp hplt
  refine lt_of_not_ge ?_
  intro hle
  have hpS : p ∈ s := ⟨hp, hle⟩
  exact wellFounded_lt.notMem_of_lt_min hplt hpS

/-- If `t ≥ e^{16}` then the cutoff satisfies `y ≥ 16`, hence the weak
lower bound on `V` applies. -/
theorem isSieveCutoff_ge_sixteen {t : ℝ} {y : ℕ} (ht : Real.exp 16 ≤ t)
    (hy : IsSieveCutoff t y) : 16 ≤ y := by
  by_contra hlt
  have hy15 : y ≤ 15 := Nat.lt_succ_iff.mp (Nat.not_le.mp hlt)
  have hyP : Nat.Prime y := hy.1
  have hy1 : 1 ≤ y := hyP.one_le
  have hVy : (y : ℝ)⁻¹ ≤ eulerProd y := by
    rw [eulerProd_coe_nat]
    exact eulerProdNat_ge_inv y hy1
  have hypos : (0 : ℝ) < y :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hy1)
  have h15 : (15 : ℝ)⁻¹ ≤ (y : ℝ)⁻¹ :=
    inv_anti₀ hypos (Nat.cast_le.mpr hy15)
  have hlog := log_t_ge_sixteen ht
  have hcut : eulerProd y ≤ 1 / Real.log t := hy.2.1
  have h16 : 1 / Real.log t ≤ 1 / 16 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlog
  have : (15 : ℝ)⁻¹ ≤ 1 / 16 :=
    (h15.trans hVy).trans (hcut.trans h16)
  norm_num at this

/-- Cutoff power: `y ≥ t^{e^{-30}}`. (`σ = 1/2` is not claimed.) -/
theorem isSieveCutoff_rpow {t : ℝ} {y : ℕ} (ht : Real.exp 16 ≤ t)
    (hy : IsSieveCutoff t y) :
    t ^ eulerProdLowerConst ≤ (y : ℝ) := by
  have ht1 := one_lt_of_exp_sixteen_le ht
  have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht1
  have hy16 := isSieveCutoff_ge_sixteen ht hy
  have hyR : (16 : ℝ) ≤ y := Nat.cast_le.mpr hy16
  have hlogy : 0 < Real.log y :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) hyR)
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have htwo := eulerProd_two_sided hyR
  have hV : eulerProdLowerConst / Real.log y ≤ 1 / Real.log t :=
    htwo.1.trans hy.2.1
  have hmul : eulerProdLowerConst * Real.log t ≤ Real.log y := by
    rw [div_le_div_iff₀ hlogy hlogt] at hV
    simpa using hV
  have hy0 : (0 : ℝ) < y :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 16) hy16)
  have : Real.log (t ^ eulerProdLowerConst) ≤ Real.log y := by
    rw [Real.log_rpow ht0]
    exact hmul
  exact (Real.log_le_log_iff (Real.rpow_pos_of_pos ht0 _) hy0).mp this

theorem eulerProdLowerConst_pos : 0 < eulerProdLowerConst :=
  Real.exp_pos _

private theorem rootedFactor_pos {p : ℕ} (hp : 3 ≤ p) :
    0 < 1 - ((p : ℝ) - 1)⁻¹ := by
  have hp3 : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp
  have : (1 : ℝ) < p - 1 := by linarith
  have : ((p : ℝ) - 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
  linarith

private theorem prime_sdiff_ge_three {z y p : ℕ} (hz : 2 ≤ z)
    (hp : p ∈ Nat.primesLE y \ Nat.primesLE z) : 3 ≤ p := by
  have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have hnotin : p ∉ Nat.primesLE z := (mem_sdiff.mp hp).2
  have : ¬ p ≤ z := fun hle => hnotin (Nat.mem_primesLE.mpr ⟨hle, hp'⟩)
  omega

theorem rootedEulerProdNat_pos {z y : ℕ} (hz : 2 ≤ z) :
    0 < rootedEulerProdNat z y :=
  prod_pos fun p hp => rootedFactor_pos (prime_sdiff_ge_three hz hp)

/-- Extra Euler factor `∏ (1 - (p-1)^{-2})` is in `(0, 1]`, so rooted
retention is at most the paper quotient `V(y)/V(z)`. -/
theorem rootedEulerProdNat_le_div {z y : ℕ} (hzy : z ≤ y) (hz : 2 ≤ z) :
    rootedEulerProdNat z y ≤ eulerProdNat y / eulerProdNat z := by
  rw [rootedEulerProdNat_eq hzy]
  have hpos : 0 ≤ eulerProdNat y / eulerProdNat z :=
    div_nonneg (eulerProdNat_pos y).le (eulerProdNat_pos z).le
  have hfac : ∀ p ∈ Nat.primesLE y \ Nat.primesLE z,
      0 ≤ 1 - ((p : ℝ) - 1)⁻¹ ^ 2 ∧
        1 - ((p : ℝ) - 1)⁻¹ ^ 2 ≤ 1 := by
    intro p hp
    have hp3 := prime_sdiff_ge_three hz hp
    have hp3R : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
    have hden : (1 : ℝ) ≤ p - 1 := by linarith
    have hinv : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have hinv1 : ((p : ℝ) - 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
    have hsq : ((p : ℝ) - 1)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ hinv hinv1
    constructor
    · exact sub_nonneg.mpr hsq
    · exact sub_le_self _ (pow_nonneg hinv 2)
  have hprod :
      (∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
          (1 - ((p : ℝ) - 1)⁻¹ ^ 2)) ≤ 1 :=
    prod_le_one (fun p hp => (hfac p hp).1) (fun p hp => (hfac p hp).2)
  exact mul_le_of_le_one_right hpos hprod

end PrimeGapNormality.Prime
