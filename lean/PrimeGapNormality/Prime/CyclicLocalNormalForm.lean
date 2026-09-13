import PrimeGapNormality.Prime.CycShiftRename
import PrimeGapNormality.Prime.HomogLeadTerm
import PrimeGapNormality.Prime.HomogDegNF
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi

/-!
# Cyclic local telescopes and an abstract linear normal form

This file isolates the linear-algebraic part of the cyclic local normal-form
construction.  In particular, telescopes form the `ℚ`-linear subspace
`LinearMap.range (cyclicTelescope B hk)`; they are not treated as an ideal.

The normal form below is an honest `PeriodicLocal k →ₗ[ℚ] PeriodicLocal k`:
we choose a vector-space complement of the telescope range and project onto
it.  Consequently its kernel is exactly the telescope range, and every tuple
splits as a telescope plus its normal form.

This abstract projection deliberately does not claim to be the paper's
computable labelled-monomial representative.  The remaining local-algebra
edge is to replace the chosen complement by the explicit chain representative

`N (e_r (S^j Mᵇ)) = B^j e_(r+j) Mᵇ`

for `u₀ ∣ Mᵇ`, and then prove that this explicit representative does not
increase tuple degree or variable width.  An arbitrary basis complement does
not justify such a degree assertion.  The telescope map itself is proved
coordinatewise degree-nonincreasing below.

No analytic, prime-distribution, AHL, or Weyl assumptions occur here.
-/

namespace PrimeGapNormality.Prime

open MvPolynomial
open scoped BigOperators

noncomputable section

/-- The polynomial algebra in the local gap variables `u₀, u₁, ...`. -/
abbrev LocalPoly := MvPolynomial ℕ ℚ

/-- A period-`k` tuple of local polynomials. -/
abbrev PeriodicLocal (k : ℕ) := Fin k → LocalPoly

/-! ## Cyclic indices -/

/-- Addition by one on `Fin k`, packaged as the cyclic permutation.

The hypothesis excludes `k = 0` and supplies the `NeZero k` instance needed
for the additive group structure on `Fin k`.
-/
def cyclicSuccEquiv {k : ℕ} (hk : 0 < k) : Fin k ≃ Fin k := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  exact Equiv.addRight (1 : Fin k)

/-- The cyclic successor of a period label. -/
def cyclicSucc {k : ℕ} (hk : 0 < k) (r : Fin k) : Fin k :=
  cyclicSuccEquiv hk r

/-- Reindexing a finite sum by cyclic successor does not change it. -/
theorem sum_cyclicSucc {k : ℕ} (hk : 0 < k) {A : Type*}
    [AddCommMonoid A] (f : Fin k → A) :
    (∑ r, f (cyclicSucc hk r)) = ∑ r, f r :=
  (cyclicSuccEquiv hk).sum_comp f

/-! ## The cyclic telescope linear map -/

/-- The local cyclic telescope operator `B - A`.

At component `r`, the action `A` first takes the cyclic successor component
and then shifts every polynomial variable by `Nat.succ`.
-/
def cyclicTelescope (B : ℕ) {k : ℕ} (hk : 0 < k) :
    PeriodicLocal k →ₗ[ℚ] PeriodicLocal k :=
  LinearMap.pi fun r ↦
    (B : ℚ) • (LinearMap.proj r : PeriodicLocal k →ₗ[ℚ] LocalPoly) -
      (rename Nat.succ).toLinearMap.comp
        (LinearMap.proj (cyclicSucc hk r) : PeriodicLocal k →ₗ[ℚ] LocalPoly)

/-- Pointwise formula for `cyclicTelescope`. -/
@[simp]
theorem cyclicTelescope_apply (B k : ℕ) (hk : 0 < k)
    (H : PeriodicLocal k) (r : Fin k) :
    cyclicTelescope B hk H r =
      C (B : ℚ) * H r - rename Nat.succ (H (cyclicSucc hk r)) := by
  simp [cyclicTelescope, smul_eq_C_mul]

/-- The cyclic shift does not increase the coordinatewise total-degree bound
of a telescope.  This statement is independent of the later choice of a
normal-form complement. -/
theorem cyclicTelescope_totalDegree_le (B k : ℕ) (hk : 0 < k)
    (H : PeriodicLocal k) (r : Fin k) :
    (cyclicTelescope B hk H r).totalDegree ≤
      max (H r).totalDegree (H (cyclicSucc hk r)).totalDegree := by
  have hleft :
      (C (B : ℚ) * H r).totalDegree ≤ (H r).totalDegree := by
    rw [← smul_eq_C_mul]
    exact totalDegree_smul_le (B : ℚ) (H r)
  have hright :
      (rename Nat.succ (H (cyclicSucc hk r))).totalDegree =
        (H (cyclicSucc hk r)).totalDegree :=
    cycSh_totalDegree _
  rw [cyclicTelescope_apply]
  exact (totalDegree_sub _ _).trans (max_le_max hleft hright.le)

/-- The sum over one full period of a telescope is a single shifted
polynomial difference.  This is the finite algebraic identity used before
specializing the local variables to a finite digit/gap block. -/
theorem sum_cyclicTelescope (B k : ℕ) (hk : 0 < k)
    (H : PeriodicLocal k) :
    (∑ r, cyclicTelescope B hk H r) =
      C (B : ℚ) * (∑ r, H r) - rename Nat.succ (∑ r, H r) := by
  have hshift :
      (∑ r, H (cyclicSucc hk r)) = ∑ r, H r :=
    sum_cyclicSucc hk H
  have hrename :
      (∑ r, rename Nat.succ (H (cyclicSucc hk r))) =
        rename Nat.succ (∑ r, H r) := by
    rw [← map_sum, hshift]
  simp_rw [cyclicTelescope_apply]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hrename]

/-! ## Complement and normal form -/

/-- A classically chosen vector-space complement of the telescope range. -/
def cyclicTelescopeComplement (B : ℕ) {k : ℕ} (hk : 0 < k) :
    Submodule ℚ (PeriodicLocal k) :=
  Classical.choose (LinearMap.range (cyclicTelescope B hk)).exists_isCompl

/-- The chosen subspace really complements the telescope range. -/
theorem cyclicTelescope_isCompl (B : ℕ) {k : ℕ} (hk : 0 < k) :
    IsCompl (LinearMap.range (cyclicTelescope B hk))
      (cyclicTelescopeComplement B hk) :=
  Classical.choose_spec (LinearMap.range (cyclicTelescope B hk)).exists_isCompl

/-- The cyclic normal form, realized as projection onto a chosen linear
complement of the telescope range.  Its codomain remains `PeriodicLocal k`,
so later homogeneous-component and one-point consumers can apply directly to
its component polynomials. -/
def cyclicNormalForm (B : ℕ) {k : ℕ} (hk : 0 < k) :
    PeriodicLocal k →ₗ[ℚ] PeriodicLocal k :=
  (cyclicTelescopeComplement B hk).projection
    (LinearMap.range (cyclicTelescope B hk))
    (cyclicTelescope_isCompl B hk).symm

/-- The image of the abstract normal form is precisely the chosen complement. -/
theorem cyclicNormalForm_range (B k : ℕ) (hk : 0 < k) :
    LinearMap.range (cyclicNormalForm B hk) =
      cyclicTelescopeComplement B hk := by
  simp [cyclicNormalForm]

/-- Exact kernel/image statement, expressed as equality of `ℚ`-linear
subspaces. -/
theorem cyclicNormalForm_ker (B k : ℕ) (hk : 0 < k) :
    LinearMap.ker (cyclicNormalForm B hk) =
      LinearMap.range (cyclicTelescope B hk) := by
  simp [cyclicNormalForm]

/-- Requested elementwise kernel/image criterion in the paper range `B ≥ 2`.
The linear-algebraic statement is actually valid for every `B`; `hB` records
the intended downstream base regime. -/
theorem cyclicNormalForm_eq_zero_iff_range (B k : ℕ) (hB : 2 ≤ B)
    (hk : 0 < k) (F : PeriodicLocal k) :
    cyclicNormalForm B hk F = 0 ↔
      F ∈ LinearMap.range (cyclicTelescope B hk) := by
  rw [← LinearMap.mem_ker, cyclicNormalForm_ker]

/-- Every periodic local polynomial tuple is a telescope plus its normal form. -/
theorem cyclicNormalForm_decomposition (B k : ℕ) (hk : 0 < k)
    (F : PeriodicLocal k) :
    ∃ H : PeriodicLocal k,
      F = cyclicTelescope B hk H + cyclicNormalForm B hk F := by
  let p := LinearMap.range (cyclicTelescope B hk)
  let q := cyclicTelescopeComplement B hk
  let hpq : IsCompl p q := cyclicTelescope_isCompl B hk
  have hmem : p.projection q hpq F ∈ p :=
    p.projection_apply_mem hpq F
  rcases hmem with ⟨H, hH⟩
  refine ⟨H, ?_⟩
  rw [hH]
  exact (p.projection_add_projection_eq_self hpq F).symm

/-- Equivalently, subtracting the normal form always lands in the telescope
subspace. -/
theorem sub_cyclicNormalForm_mem_range (B k : ℕ) (hk : 0 < k)
    (F : PeriodicLocal k) :
    F - cyclicNormalForm B hk F ∈
      LinearMap.range (cyclicTelescope B hk) := by
  rcases cyclicNormalForm_decomposition B k hk F with ⟨H, hH⟩
  refine ⟨H, ?_⟩
  exact (eq_sub_iff_add_eq).2 hH.symm

/-- Adding a telescope does not change the chosen normal representative. -/
theorem cyclicNormalForm_add_telescope (B k : ℕ) (hk : 0 < k)
    (F H : PeriodicLocal k) :
    cyclicNormalForm B hk (F + cyclicTelescope B hk H) =
      cyclicNormalForm B hk F := by
  rw [map_add]
  have hzero :
      cyclicNormalForm B hk (cyclicTelescope B hk H) = 0 := by
    rw [← LinearMap.mem_ker, cyclicNormalForm_ker]
    exact LinearMap.mem_range_self (cyclicTelescope B hk) H
  rw [hzero, add_zero]

/-- The chosen normal form is idempotent. -/
theorem cyclicNormalForm_idempotent (B k : ℕ) (hk : 0 < k)
    (F : PeriodicLocal k) :
    cyclicNormalForm B hk (cyclicNormalForm B hk F) =
      cyclicNormalForm B hk F := by
  exact Submodule.projection_apply_of_mem_left
    (cyclicTelescope_isCompl B hk).symm
    (Submodule.projection_apply_mem
      (cyclicTelescope_isCompl B hk).symm F)

end

end PrimeGapNormality.Prime
