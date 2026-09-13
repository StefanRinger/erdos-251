import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.RingTheory.Radical.NatInt

/-!
# Finite harmonic lower bound for Selberg `J(R)`

Paper / R117/07 §1.4: group `n ≤ R` by radical `d`. Then
`∑_{rad n = d} 1/n ≤ 1/φ(d) = μ(d)²/φ(d)` for squarefree `d`,
and every `n ∈ Icc 1 R` has squarefree radical `≤ n ≤ R`. Hence

    J(R) = ∑_{1 ≤ d ≤ R} μ(d)² / φ(d) ≥ ∑_{n ≤ R} 1/n = harmonic R.

Denominators are `φ(d)` for `d ≥ 1` (`Nat.totient_pos`). Honest rounding:
`n ≤ R` on `ℕ` is `n ∈ Icc 1 R`; for real `R` it is `n ≤ ⌊R⌋` (Mathlib
`Nat.le_floor_iff'`). Mathlib `harmonic` / `harmonic_eq_sum_Icc`.

This leaf is **not** the Selberg interval cap, CRT error, `V log > 1/2`,
`E choose(N^circ, j) ≤ (5L)^j/j!`, stop comparison, or kernel. Mathlib
`BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`,
`upperMoebius_lambdaSquared`, `mainSum_lambdaSquared_eq_sum_mul_sum_sq`
are diagonalization only — not imported here.

Does **not** import `EulerProd`, `ModelMoments`, MixZeta, or SingletonLi.

**Compiled.**
1. `selbergJR` / `selbergJR_term` with positive totient for `d ≥ 1`.
2. Finite geometric `∑_{a=1}^R p^{-a} ≤ 1/(p-1)`.
3. Fiber `rad n = d` ≤ `1/φ(d)` (squarefree `d`).
4. `J(R) ≥ ∑_{n ∈ Icc 1 R} n⁻¹ = (harmonic R : ℝ)`.
5. `J(R) ≥ 1 > 0` for `R ≥ 1`.
6. `J(R) ≥ log(R+1)`; floor form on `ℝ`.

**Not compiled.** Full Selberg interval hull. CRT interval error.
`|λ_d| ≤ 1`. `V(S^circ) log S^circ > 1/2`. Inner `5L` moments.
Stop comparison. Kernel close.

**Remaining hyps.** Binder `1 ≤ R` only for positivity / `J ≥ 1`.
The harmonic comparison is unconditioned. Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `J(R) ≥ ∑_{n ≤ R} 1/n` (`ℕ`) | theorem (`selbergJR_ge_sum_inv`) |
| same as `(harmonic R : ℝ)` | theorem (`selbergJR_ge_harmonic`) |
| `J(R) ≥ 1 > 0` (`1 ≤ R`) | theorem (`selbergJR_ge_one`, `selbergJR_pos`) |
| `log(R+1) ≤ J(R)` | theorem (`selbergJR_ge_log_add_one`) |
| real floor / `n ≤ ⌊R⌋` | theorem (`selbergJR_ge_*_floor`) |
| interval cap `|A| ≤ s/J(R)+R^2` | not claimed |
| CRT error / `|λ_d| ≤ 1` | not claimed |
| `V log > 1/2` / `5L` | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round117/08_selberg_lean_cost_review.md` §3 point 2;
`rounds/round117/07_selberg_rewrite_redteam.md` §1.4;
`rounds/round118/09_grok_v012_delta.md` P3.
Contract: API
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace PrimeGapNormality.Prime

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- Selberg diagonal mass `μ(d)² / φ(d)`. For `d ≥ 1` the totient is a
positive natural, so the real inverse is the honest reciprocal. -/
def selbergJR_term (d : ℕ) : ℝ :=
  (μ d : ℝ) ^ 2 * (d.totient : ℝ)⁻¹

/-- Finite Selberg `J(R) = ∑_{1 ≤ d ≤ R} μ(d)² / φ(d)`. Empty at `R = 0`. -/
def selbergJR (R : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 R, selbergJR_term d

theorem selbergJR_eq (R : ℕ) :
    selbergJR R = ∑ d ∈ Icc 1 R, (μ d : ℝ) ^ 2 * (d.totient : ℝ)⁻¹ :=
  rfl

theorem selbergJR_term_eq (d : ℕ) :
    selbergJR_term d = (μ d : ℝ) ^ 2 * (d.totient : ℝ)⁻¹ :=
  rfl

private theorem selbergJR_one_le_of_mem_Icc {R d : ℕ} (hd : d ∈ Icc 1 R) : 1 ≤ d :=
  (mem_Icc.mp hd).1

private theorem selbergJR_pos_of_mem_Icc {R d : ℕ} (hd : d ∈ Icc 1 R) : 0 < d :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (selbergJR_one_le_of_mem_Icc hd)

theorem selbergJR_totient_pos_of_mem {R d : ℕ} (hd : d ∈ Icc 1 R) :
    0 < d.totient :=
  Nat.totient_pos.mpr (selbergJR_pos_of_mem_Icc hd)

theorem selbergJR_term_nonneg {d : ℕ} (hd : 0 < d) : 0 ≤ selbergJR_term d := by
  have hφ : 0 < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)
  exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hφ.le)

theorem selbergJR_nonneg (R : ℕ) : 0 ≤ selbergJR R :=
  sum_nonneg fun d hd => selbergJR_term_nonneg (selbergJR_pos_of_mem_Icc hd)

private theorem selbergJR_moebius_sq_cast (d : ℕ) :
    (μ d : ℝ) ^ 2 = ((μ d ^ 2 : ℤ) : ℝ) :=
  (Int.cast_pow (μ d) 2).symm

theorem selbergJR_term_eq_inv_totient {d : ℕ} (hd : Squarefree d) :
    selbergJR_term d = (d.totient : ℝ)⁻¹ := by
  have hμ : (μ d : ℝ) ^ 2 = 1 := by
    rw [selbergJR_moebius_sq_cast, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hd]
    simp
  simp [selbergJR_term, hμ]

theorem selbergJR_term_eq_zero_of_not_squarefree {d : ℕ} (hd : ¬ Squarefree d) :
    selbergJR_term d = 0 := by
  have hμ : (μ d : ℝ) ^ 2 = 0 := by
    have h0 : μ d = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd
    rw [h0]
    simp
  simp [selbergJR_term, hμ]

/-- Squarefree totient: `φ(d) = ∏_{p ∣ d} (p-1)`. -/
theorem selbergJR_totient_eq_prod_pred {d : ℕ} (hd : Squarefree d) :
    d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hd,
    Nat.div_self hd0, one_mul]

theorem selbergJR_harmonic_eq_sum_inv (R : ℕ) :
    (harmonic R : ℝ) = ∑ n ∈ Icc 1 R, (n : ℝ)⁻¹ := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  refine sum_congr rfl fun n _ => ?_
  simp

/-- Honest `ℕ`-rounding: `n ≤ R` as positive integers is membership in `Icc 1 R`. -/
theorem selbergJR_mem_Icc_iff {R n : ℕ} :
    n ∈ Icc 1 R ↔ 1 ≤ n ∧ n ≤ R :=
  mem_Icc

/-- Honest real rounding: for `n ≠ 0`, `n ≤ ⌊R⌋` iff `(n : ℝ) ≤ R`. -/
theorem selbergJR_le_floor_iff {R : ℝ} {n : ℕ} (hn : n ≠ 0) :
    n ≤ ⌊R⌋₊ ↔ (n : ℝ) ≤ R :=
  Nat.le_floor_iff' hn

theorem selbergJR_mem_Icc_floor_iff {R : ℝ} {n : ℕ} :
    n ∈ Icc 1 ⌊R⌋₊ ↔ 1 ≤ n ∧ (n : ℝ) ≤ R := by
  constructor
  · intro hn
    have h := mem_Icc.mp hn
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp h.1
    exact ⟨h.1, (selbergJR_le_floor_iff hn0).mp h.2⟩
  · intro h
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp h.1
    exact mem_Icc.mpr ⟨h.1, (selbergJR_le_floor_iff hn0).mpr h.2⟩

/-! ### Finite geometric bound `∑_{a=1}^R p^{-a} ≤ 1/(p-1)` -/

private theorem selbergJR_Ico_succ_eq_Icc (R : ℕ) :
    Ico 1 (R + 1) = Icc 1 R :=
  Ico_add_one_right_eq_Icc 1 R

/-- Geometric tail with positive denominator `p-1`. -/
theorem selbergJR_geom_le {p R : ℕ} (hp : Nat.Prime p) :
    ∑ a ∈ Icc 1 R, ((p : ℝ)⁻¹) ^ a ≤ ((p - 1 : ℕ) : ℝ)⁻¹ := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp1)
  have hinv_lt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hinv_nn : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hsplit : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by
    calc
      (1 : ℝ) - (p : ℝ)⁻¹ = p / p - 1 / p := by
        rw [div_self hp0, inv_eq_one_div]
      _ = (p - 1) / p := (sub_div (p : ℝ) (1 : ℝ) p).symm
  have hid : (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) = ((p - 1 : ℕ) : ℝ)⁻¹ := by
    have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.le_of_lt hp.one_lt), Nat.cast_one]
    rw [hsplit, div_div_eq_mul_div, inv_mul_cancel₀ hp0, one_div, hsub]
  have hgeom :
      ∑ a ∈ Ico 1 (R + 1), ((p : ℝ)⁻¹) ^ a ≤
        ((p : ℝ)⁻¹) ^ 1 / (1 - (p : ℝ)⁻¹) :=
    geom_sum_Ico_le_of_lt_one hinv_nn hinv_lt
  rw [selbergJR_Ico_succ_eq_Icc, pow_one] at hgeom
  exact hgeom.trans (le_of_eq hid)

/-! ### Radical fibers -/

private theorem selbergJR_radical_mem_Icc {R n : ℕ} (hn : n ∈ Icc 1 R) :
    UniqueFactorizationMonoid.radical n ∈ Icc 1 R := by
  have h1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp h1
  have hrad1 : 1 ≤ UniqueFactorizationMonoid.radical n :=
    Nat.succ_le_iff.mpr (Nat.radical_pos n)
  have hradn : UniqueFactorizationMonoid.radical n ≤ n :=
    Nat.radical_le_self_iff.mpr hn0
  exact mem_Icc.mpr ⟨hrad1, hradn.trans (mem_Icc.mp hn).2⟩

private theorem selbergJR_primeFactors_of_rad {n d : ℕ}
    (h : UniqueFactorizationMonoid.radical n = d) :
    n.primeFactors = d.primeFactors := by
  rw [← Nat.primeFactors_radical, h]

private theorem selbergJR_factorization_mem_Icc {R n p : ℕ}
    (hn : n ∈ Icc 1 R) (hp : p ∈ n.primeFactors) :
    n.factorization p ∈ Icc 1 R := by
  have h1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp h1
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hlo : 1 ≤ n.factorization p :=
    (hpp.dvd_iff_one_le_factorization hn0).mp hpd
  have hfac : n.factorization p = padicValNat p n := Nat.factorization_def n hpp
  have hup : n.factorization p ≤ n := by
    rw [hfac]
    exact Nat.padicValNat_le_self (p := p) n
  exact mem_Icc.mpr ⟨hlo, hup.trans (mem_Icc.mp hn).2⟩

private theorem selbergJR_inv_eq_prod_pow {n d : ℕ}
    (hn0 : n ≠ 0) (hrad : UniqueFactorizationMonoid.radical n = d) :
    (n : ℝ)⁻¹ =
      ∏ p : ↥d.primeFactors, ((p : ℕ) : ℝ)⁻¹ ^ n.factorization (p : ℕ) := by
  have hpf : n.primeFactors = d.primeFactors :=
    selbergJR_primeFactors_of_rad hrad
  have hn_eq : n = ∏ p ∈ d.primeFactors, p ^ n.factorization p :=
    calc
      n = n.factorization.prod (· ^ ·) :=
        (Nat.prod_factorization_pow_eq_self hn0).symm
      _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        Nat.prod_factorization_eq_prod_primeFactors fun p k => p ^ k
      _ = ∏ p ∈ d.primeFactors, p ^ n.factorization p := by
        rw [hpf]
  have hn_cast :
      (n : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) ^ n.factorization p := by
    calc
      (n : ℝ) = ((∏ p ∈ d.primeFactors, p ^ n.factorization p : ℕ) : ℝ) :=
        congrArg Nat.cast hn_eq
      _ = ∏ p ∈ d.primeFactors, ((p ^ n.factorization p : ℕ) : ℝ) := by
        rw [Nat.cast_prod]
      _ = ∏ p ∈ d.primeFactors, (p : ℝ) ^ n.factorization p := by
        refine prod_congr rfl fun p _ => ?_
        exact Nat.cast_pow p _
  have hinv :
      (n : ℝ)⁻¹ =
        ∏ p ∈ d.primeFactors, ((p : ℝ)⁻¹) ^ n.factorization p := by
    rw [hn_cast, ← prod_inv_distrib]
    refine prod_congr rfl fun p _ => ?_
    rw [inv_pow]
  rw [hinv]
  exact (prod_coe_sort d.primeFactors
    (fun p : ℕ => ((p : ℝ)⁻¹) ^ n.factorization p)).symm

private theorem selbergJR_fiber_empty_of_not_squarefree {R d : ℕ}
    (hd : ¬ Squarefree d) :
    (Icc 1 R).filter (fun n => UniqueFactorizationMonoid.radical n = d) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hrad : UniqueFactorizationMonoid.radical n = d := (mem_filter.mp hn).2
  exact hd (hrad ▸ UniqueFactorizationMonoid.squarefree_radical)

/-- Finite radical fiber is at most `1/φ(d)` for squarefree `d`. -/
theorem selbergJR_sum_rad_le_inv_totient (R d : ℕ) (hd : Squarefree d) :
    ∑ n ∈ (Icc 1 R).filter (fun n => UniqueFactorizationMonoid.radical n = d),
        (n : ℝ)⁻¹
      ≤ (d.totient : ℝ)⁻¹ := by
  classical
  let P : Type := ↥d.primeFactors
  let fiber : Finset ℕ :=
    (Icc 1 R).filter (fun n => UniqueFactorizationMonoid.radical n = d)
  let exponents : ℕ → P → ℕ := fun n p => n.factorization (p : ℕ)
  let g : (P → ℕ) → ℝ := fun f => ∏ p : P, ((p : ℕ) : ℝ)⁻¹ ^ f p
  have hφ : (d.totient : ℝ)⁻¹ = ∏ p : P, ((p.val - 1 : ℕ) : ℝ)⁻¹ := by
    have hprod : d.totient = ∏ p ∈ d.primeFactors, (p - 1) :=
      selbergJR_totient_eq_prod_pred hd
    have hcast :
        (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p - 1 : ℕ) : ℝ) := by
      rw [hprod, Nat.cast_prod]
    rw [hcast, ← prod_inv_distrib]
    exact (prod_coe_sort d.primeFactors
      (fun p : ℕ => ((p - 1 : ℕ) : ℝ)⁻¹)).symm
  have hgeomP :
      ∀ p : P, ∑ a ∈ Icc 1 R, ((p : ℕ) : ℝ)⁻¹ ^ a ≤ ((p.val - 1 : ℕ) : ℝ)⁻¹ :=
    fun p => selbergJR_geom_le (Nat.prime_of_mem_primeFactors p.property)
  have hsum_nn : ∀ p : P, 0 ≤ ∑ a ∈ Icc 1 R, ((p : ℕ) : ℝ)⁻¹ ^ a :=
    fun p => sum_nonneg fun a _ => pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _
  have hprod_le :
      (∏ p : P, ∑ a ∈ Icc 1 R, ((p : ℕ) : ℝ)⁻¹ ^ a) ≤
        ∏ p : P, ((p.val - 1 : ℕ) : ℝ)⁻¹ :=
    prod_le_prod (fun p _ => hsum_nn p) (fun p _ => hgeomP p)
  have hpi :
      ∑ f ∈ Fintype.piFinset fun _ : P => Icc 1 R, g f =
        ∏ p : P, ∑ a ∈ Icc 1 R, ((p : ℕ) : ℝ)⁻¹ ^ a :=
    sum_prod_piFinset (Icc 1 R)
      (fun (p : P) (a : ℕ) => ((p : ℕ) : ℝ)⁻¹ ^ a)
  have hg_nn : ∀ f, 0 ≤ g f := fun f =>
    prod_nonneg fun p _ => pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _
  have him : fiber.image exponents ⊆ Fintype.piFinset fun _ : P => Icc 1 R := by
    intro f hf
    rcases mem_image.mp hf with ⟨n, hn, rfl⟩
    have hnI : n ∈ Icc 1 R := (mem_filter.mp hn).1
    have hrad : UniqueFactorizationMonoid.radical n = d := (mem_filter.mp hn).2
    have hpf : n.primeFactors = d.primeFactors :=
      selbergJR_primeFactors_of_rad hrad
    rw [Fintype.mem_piFinset]
    intro p
    have hp' : (p : ℕ) ∈ n.primeFactors := by
      rw [hpf]
      exact p.property
    simpa [exponents] using selbergJR_factorization_mem_Icc hnI hp'
  have hinj : Set.InjOn exponents fiber := by
    intro n hn n' hn' hf
    have hnI : n ∈ Icc 1 R := (mem_filter.mp hn).1
    have hnI' : n' ∈ Icc 1 R := (mem_filter.mp hn').1
    have hrad : UniqueFactorizationMonoid.radical n = d := (mem_filter.mp hn).2
    have hrad' : UniqueFactorizationMonoid.radical n' = d := (mem_filter.mp hn').2
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hnI).1
    have hn0' : n' ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hnI').1
    have hpf : n.primeFactors = d.primeFactors :=
      selbergJR_primeFactors_of_rad hrad
    have hpf' : n'.primeFactors = d.primeFactors :=
      selbergJR_primeFactors_of_rad hrad'
    apply Nat.eq_of_factorization_eq hn0 hn0'
    intro q
    by_cases hq : q ∈ d.primeFactors
    · have := congr_fun hf ⟨q, hq⟩
      simpa [exponents] using this
    · have hq1 : q ∉ n.primeFactors := by
        rw [hpf]
        exact hq
      have hq2 : q ∉ n'.primeFactors := by
        rw [hpf']
        exact hq
      have h0 : n.factorization q = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hq1
      have h0' : n'.factorization q = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hq2
      rw [h0, h0']
  have hsum_g : ∑ n ∈ fiber, (n : ℝ)⁻¹ = ∑ f ∈ fiber.image exponents, g f := by
    have hrew : ∀ n ∈ fiber, (n : ℝ)⁻¹ = g (exponents n) := by
      intro n hn
      have hnI : n ∈ Icc 1 R := (mem_filter.mp hn).1
      have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hnI).1
      have hrad : UniqueFactorizationMonoid.radical n = d := (mem_filter.mp hn).2
      exact selbergJR_inv_eq_prod_pow hn0 hrad
    rw [sum_image hinj]
    exact sum_congr rfl hrew
  have hle_pi :
      ∑ f ∈ fiber.image exponents, g f ≤
        ∑ f ∈ Fintype.piFinset fun _ : P => Icc 1 R, g f :=
    sum_le_sum_of_subset_of_nonneg him fun f _ _ => hg_nn f
  calc
    ∑ n ∈ fiber, (n : ℝ)⁻¹ = ∑ f ∈ fiber.image exponents, g f := hsum_g
    _ ≤ ∑ f ∈ Fintype.piFinset fun _ : P => Icc 1 R, g f := hle_pi
    _ = ∏ p : P, ∑ a ∈ Icc 1 R, ((p : ℕ) : ℝ)⁻¹ ^ a := hpi
    _ ≤ ∏ p : P, ((p.val - 1 : ℕ) : ℝ)⁻¹ := hprod_le
    _ = (d.totient : ℝ)⁻¹ := hφ.symm

theorem selbergJR_sum_rad_le_term (R d : ℕ) :
    ∑ n ∈ (Icc 1 R).filter (fun n => UniqueFactorizationMonoid.radical n = d),
        (n : ℝ)⁻¹
      ≤ selbergJR_term d := by
  by_cases hsq : Squarefree d
  · rw [selbergJR_term_eq_inv_totient hsq]
    exact selbergJR_sum_rad_le_inv_totient R d hsq
  · rw [selbergJR_fiber_empty_of_not_squarefree hsq, Finset.sum_empty,
      selbergJR_term_eq_zero_of_not_squarefree hsq]

/-! ### `J(R)` versus the harmonic sum -/

theorem selbergJR_ge_sum_inv (R : ℕ) :
    ∑ n ∈ Icc 1 R, (n : ℝ)⁻¹ ≤ selbergJR R := by
  have hmaps : ∀ n ∈ Icc 1 R, UniqueFactorizationMonoid.radical n ∈ Icc 1 R :=
    fun n hn => selbergJR_radical_mem_Icc hn
  have hsplit :
      ∑ n ∈ Icc 1 R, (n : ℝ)⁻¹ =
        ∑ d ∈ Icc 1 R,
          ∑ n ∈ (Icc 1 R).filter (fun n => UniqueFactorizationMonoid.radical n = d),
            (n : ℝ)⁻¹ :=
    (sum_fiberwise_of_maps_to hmaps fun n => (n : ℝ)⁻¹).symm
  rw [hsplit, selbergJR]
  exact sum_le_sum fun d _ => selbergJR_sum_rad_le_term R d

theorem selbergJR_ge_harmonic (R : ℕ) :
    (harmonic R : ℝ) ≤ selbergJR R := by
  rw [selbergJR_harmonic_eq_sum_inv]
  exact selbergJR_ge_sum_inv R

theorem selbergJR_ge_one {R : ℕ} (hR : 1 ≤ R) : (1 : ℝ) ≤ selbergJR R := by
  have hmem : 1 ∈ Icc 1 R := mem_Icc.mpr ⟨le_rfl, hR⟩
  have hterm : selbergJR_term 1 = 1 := by
    rw [selbergJR_term, ArithmeticFunction.moebius_apply_one, Nat.totient_one]
    simp
  have hnn : ∀ d ∈ Icc 1 R, 0 ≤ selbergJR_term d := fun d hd =>
    selbergJR_term_nonneg (selbergJR_pos_of_mem_Icc hd)
  calc
    (1 : ℝ) = selbergJR_term 1 := hterm.symm
    _ ≤ ∑ d ∈ Icc 1 R, selbergJR_term d := single_le_sum hnn hmem
    _ = selbergJR R := rfl

theorem selbergJR_pos {R : ℕ} (hR : 1 ≤ R) : 0 < selbergJR R :=
  lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) (selbergJR_ge_one hR)

theorem selbergJR_ge_log_add_one (R : ℕ) :
    Real.log (R + 1 : ℝ) ≤ selbergJR R := by
  have hlog : Real.log ((R + 1 : ℕ) : ℝ) ≤ selbergJR R :=
    (log_add_one_le_harmonic R).trans (selbergJR_ge_harmonic R)
  simpa [Nat.cast_add_one] using hlog

theorem selbergJR_ge_sum_inv_floor (R : ℝ) :
    ∑ n ∈ Icc 1 ⌊R⌋₊, (n : ℝ)⁻¹ ≤ selbergJR ⌊R⌋₊ :=
  selbergJR_ge_sum_inv ⌊R⌋₊

theorem selbergJR_ge_harmonic_floor (R : ℝ) :
    (harmonic ⌊R⌋₊ : ℝ) ≤ selbergJR ⌊R⌋₊ :=
  selbergJR_ge_harmonic ⌊R⌋₊

theorem selbergJR_ge_log_floor {R : ℝ} (hR : 0 ≤ R) :
    Real.log R ≤ selbergJR ⌊R⌋₊ :=
  (log_le_harmonic_floor R hR).trans (selbergJR_ge_harmonic ⌊R⌋₊)

theorem selbergJR_ge_log_add_one_floor (R : ℝ) :
    Real.log (⌊R⌋₊ + 1 : ℝ) ≤ selbergJR ⌊R⌋₊ :=
  selbergJR_ge_log_add_one ⌊R⌋₊

end

end PrimeGapNormality.Prime
