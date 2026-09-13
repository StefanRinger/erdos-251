import PrimeGapNormality.Prime.CoreCyclicCanonical
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Counting the actual rooted normal monomials

For H variables and degree at most D, remove exactly one factor of u₀.
An explicit slack-coordinate equivalence then counts the remaining degree
at most D-1 exponents by stars and bars. The polynomial space has the
actual restricted monomial basis, not a postulated dimension.

The final dimension here is the finite canonical algebra with one rational
constant coordinate. Identifying its image with the span of actual series
is a separate arithmetic consumer.
-/

namespace PrimeGapNormality.Prime.CoreNormalMonomialDimension

open Finset MvPolynomial
noncomputable section

set_option maxHeartbeats 600000

def origin {H : ℕ} (hH : 0 < H) : Fin H := ⟨0, hH⟩

def RootExponent {H : ℕ} (hH : 0 < H) (D : ℕ) :=
  {m : Fin H →₀ ℕ // 0 < m (origin hH) ∧ m.degree ≤ D}

def BoundedExponent (H E : ℕ) := {m : Fin H →₀ ℕ // m.degree ≤ E}

/-- Remove one copy of the distinguished root variable, with exact inverse
given by adding it back. -/
def removeRootEquiv {H D : ℕ} (hH : 0 < H) (hD : 0 < D) :
    RootExponent hH D ≃ BoundedExponent H (D - 1) where
  toFun m := ⟨m.1 - Finsupp.single (origin hH) 1, by
    have hle : Finsupp.single (origin hH) 1 ≤ m.1 :=
      Finsupp.single_le_iff.mpr (Nat.succ_le_of_lt m.2.1)
    have heq := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
    simp only [map_add, Finsupp.degree_single] at heq
    have hm := m.2.2
    omega⟩
  invFun m := ⟨m.1 + Finsupp.single (origin hH) 1, by
    constructor
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · rw [map_add, Finsupp.degree_single]
      have hm := m.2
      omega⟩
  left_inv m := by
    apply Subtype.ext
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.succ_le_of_lt m.2.1))
  right_inv m := by
    apply Subtype.ext
    exact add_tsub_cancel_right _ _

/-- A slack coordinate changes a bound on total degree into an equality.
This handles zero variables as well, for the intermediate counting lemma. -/
def slackEquiv (H E : ℕ) :
    {f : Fin H → ℕ // ∑ i, f i ≤ E} ≃
      {g : Option (Fin H) → ℕ // ∑ i, g i = E} where
  toFun f := ⟨fun i => match i with | none => E - ∑ j, f.1 j | some i => f.1 i, by
    rw [Fintype.sum_option]
    exact Nat.sub_add_cancel f.2⟩
  invFun g := ⟨fun i => g.1 (some i), by
    have hg : g.1 none + (∑ i : Fin H, g.1 (some i)) = E := by
      simpa only [Fintype.sum_option] using g.2
    change (∑ i : Fin H, g.1 (some i)) ≤ E
    exact (Nat.le_add_left _ _).trans_eq hg⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      have hg := g.2
      rw [Fintype.sum_option] at hg
      dsimp only
      omega
    | some i => rfl

/-- The bounded exponent set is explicitly equivalent to a symmetric
power over H variables plus the slack symbol. -/
def boundedExponentEquivSym (H E : ℕ) :
    BoundedExponent H E ≃ Sym (Option (Fin H)) E :=
  ((Finsupp.equivFunOnFinite.subtypeEquiv (fun m => by
    change m.degree ≤ E ↔ (∑ i, m i) ≤ E
    rw [Finsupp.degree_eq_sum])).trans (slackEquiv H E)).trans
      (Sym.equivNatSumOfFintype (Option (Fin H)) E).symm

theorem card_boundedExponent (H E : ℕ) :
    Nat.card (BoundedExponent H E) = (H + E).choose E := by
  rw [Nat.card_congr (boundedExponentEquivSym H E), Sym.natCard_sym_eq_choose]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]
  congr 1
  omega

/-- The paper's single-label normal-monomial count. -/
theorem card_rootExponent {H D : ℕ} (hH : 0 < H) (hD : 0 < D) :
    Nat.card (RootExponent hH D) = (H + D - 1).choose (D - 1) := by
  rw [Nat.card_congr (removeRootEquiv hH hD), card_boundedExponent]
  congr 1
  omega

theorem card_labelled_rootExponent {H D : ℕ} (hH : 0 < H) (hD : 0 < D) (k : ℕ) :
    Nat.card (Fin k × RootExponent hH D) = k * (H + D - 1).choose (D - 1) := by
  rw [Nat.card_prod, card_rootExponent hH hD]
  simp

def rootedSpace {H : ℕ} (hH : 0 < H) (D : ℕ) : Submodule ℚ (MvPolynomial (Fin H) ℚ) :=
  restrictSupport ℚ {m | 0 < m (origin hH) ∧ m.degree ≤ D}

/-- These are literal monomials containing u₀, not an arbitrary complement. -/
theorem rootedSpace_eq_span {H : ℕ} (hH : 0 < H) (D : ℕ) :
    rootedSpace hH D = Submodule.span ℚ
      ((fun m : Fin H →₀ ℕ => monomial m (1 : ℚ)) ''
        {m | 0 < m (origin hH) ∧ m.degree ≤ D}) :=
  restrictSupport_eq_span ℚ _

def rootedBasis {H : ℕ} (hH : 0 < H) (D : ℕ) :
    Module.Basis (RootExponent hH D) ℚ (rootedSpace hH D) :=
  basisRestrictSupport ℚ _

def rootedExponentFintype {H D : ℕ} (hH : 0 < H) (hD : 0 < D) :
    Fintype (RootExponent hH D) :=
  Fintype.ofEquiv (Sym (Option (Fin H)) (D - 1))
    ((removeRootEquiv hH hD).trans (boundedExponentEquivSym H (D - 1))).symm

theorem finrank_rootedSpace {H D : ℕ} (hH : 0 < H) (hD : 0 < D) :
    Module.finrank ℚ (rootedSpace hH D) = (H + D - 1).choose (D - 1) := by
  letI : Fintype (RootExponent hH D) := rootedExponentFintype hH hD
  rw [Module.finrank_eq_card_basis (rootedBasis hH D)]
  simpa only [Nat.card_eq_fintype_card] using card_rootExponent hH hD

/-- One rational boundary coordinate and k independent labelled copies
have exactly the dimension displayed in the frozen paper. -/
theorem finrank_constant_and_labelled_rootedSpace
    {H D : ℕ} (hH : 0 < H) (hD : 0 < D) (k : ℕ) :
    Module.finrank ℚ (ℚ × (Fin k → rootedSpace hH D)) =
      1 + k * (H + D - 1).choose (D - 1) := by
  letI : Fintype (RootExponent hH D) := rootedExponentFintype hH hD
  letI : Module.Finite ℚ (rootedSpace hH D) := Module.Finite.of_basis (rootedBasis hH D)
  rw [Module.finrank_prod, Module.finrank_self,
    Module.finrank_pi_fintype (R := ℚ) (ι := Fin k) (M := fun _ : Fin k => rootedSpace hH D)]
  simp only [finrank_rootedSpace hH hD, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id]

/-- Each counted labelled monomial is fixed by the actual canonical
normal form after the genuine finite-variable embedding into gap indices. -/
theorem normalForm_labelled_rootExponent
    {B k H D : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (hH : 0 < H)
    (r : Fin k) (m : RootExponent hH D) :
    CoreCyclic.normalForm hB hk
      (CoreCyclic.labelled r (rename Fin.val (monomial m.1 (1 : ℚ)))) =
      CoreCyclic.labelled r (rename Fin.val (monomial m.1 (1 : ℚ))) := by
  rw [rename_monomial]
  apply CoreCyclic.normalForm_of_rooted
  apply CoreCyclic.labelled_monomial_rooted
  have hm : (m.1.mapDomain Fin.val) 0 = m.1 (origin hH) := by
    simpa only [origin] using Finsupp.mapDomain_apply Fin.val_injective m.1 (origin hH)
  rw [hm]
  exact m.2.1.ne'

end
end PrimeGapNormality.Prime.CoreNormalMonomialDimension
