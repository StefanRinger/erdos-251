import PrimeGapNormality.Prime.CyclicLocalNormalForm
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
Finite chain division for the frozen paper, §2. The shift and telescope act
on the actual `MvPolynomial ℕ ℚ` tuples. The geometric primitive below is
explicit and finite. No choice of a complementary vector space is used.

This module supplies the chain calculation; identifying all nonconstant
monomials with their unique rooted chains is a separate step.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open MvPolynomial
open scoped BigOperators

noncomputable section

/-- The paper's combined shift: advance the component before shifting gaps. -/
def shift {k : ℕ} (hk : 0 < k) : PeriodicLocal k →ₗ[ℚ] PeriodicLocal k :=
  LinearMap.pi fun r ↦
    (rename Nat.succ).toLinearMap.comp
      (LinearMap.proj (cyclicSucc hk r) : PeriodicLocal k →ₗ[ℚ] LocalPoly)

@[simp] theorem shift_apply {k : ℕ} (hk : 0 < k)
    (F : PeriodicLocal k) (r : Fin k) :
    shift hk F r = rename Nat.succ (F (cyclicSucc hk r)) := rfl

theorem telescope_eq {k : ℕ} (B : ℕ) (hk : 0 < k) (F : PeriodicLocal k) :
    cyclicTelescope B hk F = (B : ℚ) • F - shift hk F := by
  ext r
  simp [cyclicTelescope_apply, smul_eq_C_mul]

/-- Iterated combined shift as a linear map, with a convenient successor rule. -/
def shiftPower {k : ℕ} (hk : 0 < k) : ℕ → PeriodicLocal k →ₗ[ℚ] PeriodicLocal k
  | 0 => LinearMap.id
  | j + 1 => (shift hk).comp (shiftPower hk j)

@[simp] theorem shiftPower_zero {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k) :
    shiftPower hk 0 F = F := rfl

@[simp] theorem shiftPower_succ {k : ℕ} (hk : 0 < k) (j : ℕ)
    (F : PeriodicLocal k) :
    shiftPower hk (j + 1) F = shift hk (shiftPower hk j F) := rfl

/-- `Σᵢ<ⱼ B^(j-1-i) A^i F`, written recursively without truncated subtraction. -/
def geometricPrimitive (B : ℕ) {k : ℕ} (hk : 0 < k) :
    ℕ → PeriodicLocal k →ₗ[ℚ] PeriodicLocal k
  | 0 => 0
  | j + 1 => (B : ℚ) • geometricPrimitive B hk j + shiftPower hk j

@[simp] theorem geometricPrimitive_zero (B : ℕ) {k : ℕ} (hk : 0 < k)
    (F : PeriodicLocal k) : geometricPrimitive B hk 0 F = 0 := rfl

@[simp] theorem geometricPrimitive_succ (B : ℕ) {k : ℕ} (hk : 0 < k)
    (j : ℕ) (F : PeriodicLocal k) :
    geometricPrimitive B hk (j + 1) F =
      (B : ℚ) • geometricPrimitive B hk j F + shiftPower hk j F := rfl

/-- Finite geometric division on an actual local-polynomial chain. -/
theorem telescope_geometricPrimitive (B : ℕ) {k : ℕ} (hk : 0 < k)
    (j : ℕ) (F : PeriodicLocal k) :
    cyclicTelescope B hk (geometricPrimitive B hk j F) =
      (B : ℚ) ^ j • F - shiftPower hk j F := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [geometricPrimitive_succ, map_add, map_smul, ih,
      telescope_eq, shiftPower_succ, pow_succ]
    module

/-- Every shifted chain generator reduces to its weighted root modulo telescopes. -/
theorem shiftPower_decomposition (B : ℕ) {k : ℕ} (hk : 0 < k)
    (j : ℕ) (F : PeriodicLocal k) :
    shiftPower hk j F = (B : ℚ) ^ j • F +
      cyclicTelescope B hk (-geometricPrimitive B hk j F) := by
  rw [map_neg, telescope_geometricPrimitive]
  abel

/-- The same division simultaneously for any finite collection of chains. -/
theorem finite_chain_decomposition (B : ℕ) {k ι : ℕ} (hk : 0 < k)
    (a : Fin ι → ℚ) (j : Fin ι → ℕ) (F : Fin ι → PeriodicLocal k) :
    (∑ i, a i • shiftPower hk (j i) (F i)) =
      (∑ i, (a i * (B : ℚ) ^ j i) • F i) +
      cyclicTelescope B hk
        (-∑ i, a i • geometricPrimitive B hk (j i) (F i)) := by
  simp_rw [shiftPower_decomposition B hk, smul_add, ← mul_smul]
  rw [Finset.sum_add_distrib]
  congr 1
  simp [map_neg, map_sum, map_smul, smul_neg]

/-- Actual constant polynomial tuples. -/
def constantTuple {k : ℕ} (c : Fin k → ℚ) : PeriodicLocal k := fun r ↦ C (c r)

theorem shiftPower_constantTuple {k : ℕ} (hk : 0 < k) (j : ℕ)
    (c : Fin k → ℚ) (r : Fin k) :
    shiftPower hk j (constantTuple c) r =
      C (c ((cyclicSucc hk)^[j] r)) := by
  induction j generalizing r with
  | zero => rfl
  | succ j ih =>
    rw [shiftPower_succ, shift_apply, ih, rename_C,
      Function.iterate_succ_apply]

theorem cyclicSucc_period {k : ℕ} (hk : 0 < k) (r : Fin k) :
    (cyclicSucc hk)^[k] r = r := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hs : cyclicSucc hk = fun s : Fin k ↦ s + 1 := rfl
  have hval (n : ℕ) : ((n • (1 : Fin k) : Fin k) : ℕ) = n % k := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul, Fin.val_add, ih, Fin.val_one']
      simp only [Nat.add_mod, Nat.mod_mod]
  have hz : k • (1 : Fin k) = 0 := by
    apply Fin.ext
    rw [hval]
    simp
  rw [hs, add_right_iterate_apply]
  rw [hz, add_zero]

theorem shiftPower_period_constantTuple {k : ℕ} (hk : 0 < k)
    (c : Fin k → ℚ) :
    shiftPower hk k (constantTuple c) = constantTuple c := by
  ext r
  rw [shiftPower_constantTuple, cyclicSucc_period]
  rfl

/-- The explicit inverse of the telescope on constants from the paper. -/
def constantPrimitive (B : ℕ) {k : ℕ} (hk : 0 < k) (c : Fin k → ℚ) :
    PeriodicLocal k :=
  ((B : ℚ) ^ k - 1)⁻¹ • geometricPrimitive B hk k (constantTuple c)

theorem telescope_constantPrimitive {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : Fin k → ℚ) :
    cyclicTelescope B hk (constantPrimitive B hk c) = constantTuple c := by
  have hb : (1 : ℚ) < B := Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide) hB)
  have hden : (B : ℚ) ^ k - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_pow₀ hb (Nat.ne_of_gt hk)).ne'
  rw [constantPrimitive, map_smul, telescope_geometricPrimitive,
    shiftPower_period_constantTuple]
  have hs : (B : ℚ) ^ k • constantTuple c - constantTuple c =
      ((B : ℚ) ^ k - 1) • constantTuple c := by module
  rw [hs, smul_smul, inv_mul_cancel₀ hden, one_smul]

/-- Polynomial division on a single chain, with the paper's `B-z` sign. -/
def chainQuotient (B : ℚ) (p : Polynomial ℚ) : Polynomial ℚ :=
  -(p /ₘ (Polynomial.X - Polynomial.C B))

theorem chain_division (B : ℚ) (p : Polynomial ℚ) :
    p = Polynomial.C (p.eval B) +
      (Polynomial.C B - Polynomial.X) * chainQuotient B p := by
  have h := Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C B)
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
  rw [chainQuotient]
  linear_combination -h

/-- Evaluation at `B` is exactly the obstruction to finite chain division. -/
theorem chain_eval_zero_iff (B : ℚ) (p : Polynomial ℚ) :
    p.eval B = 0 ↔ ∃ q : Polynomial ℚ,
      p = (Polynomial.C B - Polynomial.X) * q := by
  constructor
  · intro h
    refine ⟨chainQuotient B p, ?_⟩
    simpa [h] using chain_division B p
  · rintro ⟨q, rfl⟩
    simp

/-- The primitive on a chain is unique; finite support prevents an infinite tail. -/
theorem chain_primitive_unique (B : ℚ) (p q₁ q₂ : Polynomial ℚ)
    (h₁ : p = Polynomial.C (p.eval B) + (Polynomial.C B - Polynomial.X) * q₁)
    (h₂ : p = Polynomial.C (p.eval B) + (Polynomial.C B - Polynomial.X) * q₂) :
    q₁ = q₂ := by
  have hn : Polynomial.C B - Polynomial.X ≠ (0 : Polynomial ℚ) := by
    intro h
    exact Polynomial.X_sub_C_ne_zero B (by linear_combination -h)
  exact mul_left_cancel₀ hn (add_left_cancel (h₁.symm.trans h₂))

end

end PrimeGapNormality.Prime.CoreCyclic
