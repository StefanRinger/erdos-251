import PrimeGapNormality.Prime.CoreCyclicInsertionEvaluation
import PrimeGapNormality.Prime.SubsetSpacing
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Int.Interval

/-!
# The genuine finite exterior frame of a cyclic action

The action has signed variables in `[-w-1,w]`; removing the moving
coordinate `-1` leaves exactly `2w+1` coordinates. The finite real
coefficient below is obtained from the actual exterior derivative
coefficient, with a proved rename-back identity. Its nonzeroness is a
consequence, not an extra assumption on a proposed representative.
-/

namespace PrimeGapNormality.Prime.CoreCyclic.OnePoint.FiniteExterior

open MvPolynomial Finset
open scoped Classical BigOperators

noncomputable section

private theorem vars_smul_subset (p : SignedPoly) (c : ℚ) :
    (c • p).vars ⊆ p.vars := by
  rw [smul_eq_C_mul]
  simpa only [vars_C, empty_union] using vars_mul (C c) p

theorem preAction_vars_bounds (B : ℕ) {k : ℕ} (hk : 0 < k) (w : ℕ)
    (s : Fin k) (F : PeriodicLocal k)
    (hw : ∀ r i, i ∈ (F r).vars → i ≤ w)
    {i : ℤ} (hi : i ∈ (preAction B hk w s F).vars) :
    -(w : ℤ) - 1 ≤ i ∧ i ≤ (w : ℤ) := by
  unfold preAction at hi
  obtain ⟨j, hj, hij⟩ := mem_biUnion.mp (vars_sum_subset _ _ hi)
  have his := vars_smul_subset _ ((B : ℚ) ^ j) hij
  change i ∈ (rename (fun n : ℕ => (n : ℤ) - (j : ℤ))
    (F ((predecessor hk)^[j] (cyclicSucc hk s)))).vars at his
  obtain ⟨n, hn, hni⟩ := mem_vars_rename _ _ his
  have hnw := hw _ n hn
  have hjw := mem_range.mp hj
  change (n : ℤ) - (j : ℤ) = i at hni
  omega

theorem moveSubst_vars_bounds (w : ℕ) (p : SignedPoly)
    (hp : ∀ i ∈ p.vars, -(w : ℤ) - 1 ≤ i ∧ i ≤ (w : ℤ))
    {i : ℤ} (hi : i ∈ (moveSubst p).vars) :
    -(w : ℤ) - 1 ≤ i ∧ i ≤ (w : ℤ) := by
  unfold moveSubst at hi
  rw [aeval_eq_bind₁] at hi
  obtain ⟨j, hj, hij⟩ := mem_vars_bind₁ _ _ hi
  by_cases hj0 : j = 0
  · simp only [hj0, if_pos rfl] at hij
    have hmem := vars_sub_subset (p := (X 0 : SignedPoly)) (q := X (-1)) hij
    simp only [vars_X, mem_union, mem_singleton] at hmem
    rcases hmem with rfl | rfl <;> omega
  · simp only [if_neg hj0, vars_X, mem_singleton] at hij
    simpa only [hij] using hp j hj

theorem action_vars_bounds (B : ℕ) {k : ℕ} (hk : 0 < k) (w : ℕ)
    (s : Fin k) (F : PeriodicLocal k)
    (hw : ∀ r i, i ∈ (F r).vars → i ≤ w)
    {i : ℤ} (hi : i ∈ (action B hk w s F).vars) :
    -(w : ℤ) - 1 ≤ i ∧ i ≤ (w : ℤ) :=
  moveSubst_vars_bounds w _ (fun _ hi => preAction_vars_bounds B hk w s F hw hi) hi

/-- Partial differentiation cannot introduce a new variable. -/
theorem vars_pderiv_subset (p : SignedPoly) (a : ℤ) :
    (pderiv a p).vars ⊆ p.vars := by
  intro i hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).1 hi
  have hcoeff := mem_support_iff.1 hm
  rw [coeff_pderiv] at hcoeff
  have hp : coeff (m + Finsupp.single a 1) p ≠ 0 :=
    (mul_ne_zero_iff.1 hcoeff).1
  apply (mem_vars_iff_mem_support i).2
  refine ⟨m + Finsupp.single a 1, mem_support_iff.2 hp, ?_⟩
  apply Finsupp.mem_support_iff.2
  have hmpos : m i ≠ 0 := Finsupp.mem_support_iff.1 hmi
  simp only [Finsupp.add_apply]
  omega

/-- Splitting off the moving variable does not create exterior variables. -/
theorem splitMoving_coeff_vars (p : SignedPoly) (n : ℕ) {i : ExteriorIndex}
    (hi : i ∈ ((splitMoving p).coeff n).vars) : (i : ℤ) ∈ p.vars := by
  change i ∈ ((optionEquivLeft ℚ ExteriorIndex
    (rename (Equiv.optionSubtypeNe (-1 : ℤ)).symm p)).coeff n).vars at hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).1 hi
  have hm' : m.optionElim n ∈
      (rename (Equiv.optionSubtypeNe (-1 : ℤ)).symm p).support :=
    (MvPolynomial.mem_support_coeff_optionEquivLeft ℚ).mp hm
  have hsome : some i ∈ (rename (Equiv.optionSubtypeNe (-1 : ℤ)).symm p).vars := by
    apply (mem_vars_iff_mem_support (some i)).2
    refine ⟨m.optionElim n, hm', ?_⟩
    apply Finsupp.mem_support_iff.2
    simpa only [Finsupp.optionElim_apply_some] using (Finsupp.mem_support_iff.1 hmi)
  obtain ⟨j, hj, hji⟩ := mem_vars_rename _ _ hsome
  have hval : j = (i : ℤ) := by
    have h := congrArg (Equiv.optionSubtypeNe (-1 : ℤ)) hji
    simpa only [Equiv.apply_symm_apply, Equiv.optionSubtypeNe_some] using h
  exact hval ▸ hj

theorem exteriorDerivativeCoeff_vars (p : SignedPoly) (n : ℕ) {i : ExteriorIndex}
    (hi : i ∈ (exteriorDerivativeCoeff p n).vars) : (i : ℤ) ∈ p.vars :=
  vars_pderiv_subset p (-1) (splitMoving_coeff_vars (pderiv (-1) p) n hi)

def box (w : ℕ) : Finset ℤ := (Icc (-(w : ℤ) - 1) (w : ℤ)).erase (-1)

theorem mem_box {w : ℕ} {i : ℤ} :
    i ∈ box w ↔ i ≠ -1 ∧ -(w : ℤ) - 1 ≤ i ∧ i ≤ (w : ℤ) := by
  simp only [box, mem_erase, mem_Icc]

theorem box_card (w : ℕ) : (box w).card = 2 * w + 1 := by
  have hmem : (-1 : ℤ) ∈ Icc (-(w : ℤ) - 1) (w : ℤ) :=
    mem_Icc.mpr ⟨by omega, by omega⟩
  rw [box, card_erase_of_mem hmem, Int.card_Icc]
  omega

/-- Increasing enumeration of the actual finite exterior coordinates. -/
def embedding (w : ℕ) : Fin (2 * w + 1) ↪ ExteriorIndex where
  toFun i := ⟨(box w).orderEmbOfFin (box_card w) i,
    (mem_box.1 ((box w).orderEmbOfFin_mem (box_card w) i)).1⟩
  inj' := by
    intro i j h
    have hv := congrArg (fun x : ExteriorIndex => (x : ℤ)) h
    change (box w).orderEmbOfFin (box_card w) i =
      (box w).orderEmbOfFin (box_card w) j at hv
    exact ((box w).orderEmbOfFin (box_card w)).injective hv

theorem embedding_bounds (w : ℕ) (i : Fin (2 * w + 1)) :
    -(w : ℤ) - 1 ≤ (embedding w i : ℤ) ∧ (embedding w i : ℤ) ≤ (w : ℤ) :=
  (mem_box.1 ((box w).orderEmbOfFin_mem (box_card w) i)).2

theorem mem_range_embedding_iff (w : ℕ) (i : ExteriorIndex) :
    i ∈ Set.range (embedding w) ↔ -(w : ℤ) - 1 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (w : ℤ) := by
  constructor
  · rintro ⟨j, rfl⟩
    exact embedding_bounds w j
  · intro hi
    have hmem : (i : ℤ) ∈ box w := mem_box.2 ⟨i.property, hi⟩
    refine ⟨((box w).orderIsoOfFin (box_card w)).symm ⟨i.val, hmem⟩, ?_⟩
    apply Subtype.ext
    have hv := congrArg (fun x : ↥(box w) => (x : ℤ))
      (((box w).orderIsoOfFin (box_card w)).apply_symm_apply ⟨i.val, hmem⟩)
    change (box w).orderEmbOfFin (box_card w)
      (((box w).orderIsoOfFin (box_card w)).symm ⟨i.val, hmem⟩) = i.val at hv ⊢
    exact hv

/-- The literal finite restriction, before changing rational coefficients. -/
def restrictCoeff (w : ℕ) (p : MvPolynomial ExteriorIndex ℚ) :
    MvPolynomial (Fin (2 * w + 1)) ℚ := killCompl (embedding w).injective p

theorem rename_restrictCoeff (w : ℕ) (p : MvPolynomial ExteriorIndex ℚ)
    (hp : ∀ i ∈ p.vars, -(w : ℤ) - 1 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (w : ℤ)) :
    rename (embedding w) (restrictCoeff w p) = p := by
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range p (embedding w)
    (embedding w).injective (fun i hi => (mem_range_embedding_iff w i).2 (hp i hi))
  rw [← hq, restrictCoeff, killCompl_rename_app]

def realCoeff (w : ℕ) (p : MvPolynomial ExteriorIndex ℚ) :
    MvPolynomial (Fin (2 * w + 1)) ℝ :=
  MvPolynomial.map (algebraMap ℚ ℝ) (restrictCoeff w p)

theorem realCoeff_ne_zero (w : ℕ) (p : MvPolynomial ExteriorIndex ℚ)
    (hp : ∀ i ∈ p.vars, -(w : ℤ) - 1 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (w : ℤ))
    (hp0 : p ≠ 0) : realCoeff w p ≠ 0 := by
  intro hz
  change MvPolynomial.map (algebraMap ℚ ℝ) (restrictCoeff w p) = 0 at hz
  have hr : restrictCoeff w p = 0 := by
    apply MvPolynomial.map_injective (algebraMap ℚ ℝ)
      (FaithfulSMul.algebraMap_injective ℚ ℝ)
    rw [map_zero]
    exact hz
  apply hp0
  rw [← rename_restrictCoeff w p hp, hr, map_zero]

theorem realCoeff_eval (w : ℕ) (p : MvPolynomial ExteriorIndex ℚ)
    (hp : ∀ i ∈ p.vars, -(w : ℤ) - 1 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (w : ℤ))
    (y : ExteriorIndex → ℝ) :
    eval (fun i => y (embedding w i)) (realCoeff w p) =
      eval₂ (algebraMap ℚ ℝ) y p := by
  rw [realCoeff, ← eval₂_eq_eval_map]
  have h := congrArg (eval₂ (algebraMap ℚ ℝ) y) (rename_restrictCoeff w p hp)
  rw [eval₂_rename] at h
  exact h

theorem action_exteriorDerivativeCoeff_bounds (B : ℕ) {k : ℕ}
    (hk : 0 < k) (w : ℕ) (s : Fin k) (F : PeriodicLocal k)
    (hw : ∀ r i, i ∈ (F r).vars → i ≤ w) (n : ℕ)
    {i : ExteriorIndex} (hi : i ∈ (exteriorDerivativeCoeff (action B hk w s F) n).vars) :
    -(w : ℤ) - 1 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (w : ℤ) :=
  action_vars_bounds B hk w s F hw (exteriorDerivativeCoeff_vars _ n hi)

/-- An actual nonzero moving action exposes a nonzero polynomial in
exactly `2w+1` real frame coordinates, with the exact evaluation identity. -/
theorem exists_nonzero_finite_coefficient (B : ℕ) {k : ℕ}
    (hk : 0 < k) (w : ℕ) (s : Fin k) (F : PeriodicLocal k)
    (hw : ∀ r i, i ∈ (F r).vars → i ≤ w)
    (ha : pderiv (-1) (action B hk w s F) ≠ 0) :
    ∃ n : ℕ, realCoeff w (exteriorDerivativeCoeff (action B hk w s F) n) ≠ 0 ∧
      ∀ y : ExteriorIndex → ℝ,
        eval (fun i => y (embedding w i))
          (realCoeff w (exteriorDerivativeCoeff (action B hk w s F) n)) =
            exteriorEval y (exteriorDerivativeCoeff (action B hk w s F) n) := by
  obtain ⟨n, hn⟩ := exists_exteriorDerivativeCoeff_ne_zero ha
  have hb : ∀ i : ExteriorIndex,
      i ∈ (exteriorDerivativeCoeff (action B hk w s F) n).vars →
        -(w : ℤ) - 1 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (w : ℤ) :=
    fun i hi => action_exteriorDerivativeCoeff_bounds B hk w s F hw n hi
  exact ⟨n, realCoeff_ne_zero w _ hb hn, fun y => realCoeff_eval w _ hb y⟩

/-! ### Actual contiguous deleted-frame gap ranks -/

/-- Signed coordinates left of the moving gap retain rank `j+i`.
Coordinates `0,1,...` have rank `j+i-1` after deletion; in particular
coordinate zero is the merged gap at rank `j-1`. -/
def deletedRank (j : ℕ) (i : ExteriorIndex) : ℕ :=
  (if (i : ℤ) ≤ -2 then (j : ℤ) + i else (j : ℤ) + i - 1).toNat

theorem deletedRank_int_eq (w j : ℕ) (hj : w + 1 ≤ j) (i : ExteriorIndex)
    (hi : -(w : ℤ) - 1 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (w : ℤ)) :
    (deletedRank j i : ℤ) =
      if (i : ℤ) ≤ -2 then (j : ℤ) + i else (j : ℤ) + i - 1 := by
  have hne := i.property
  unfold deletedRank
  split_ifs <;> omega

theorem deletedRank_zero (j : ℕ) (hj : 1 ≤ j) :
    deletedRank j ⟨0, by decide⟩ = j - 1 := by
  simp only [deletedRank, show ¬(0 : ℤ) ≤ -2 by decide, if_false, add_zero]
  omega

def frameRank (w j : ℕ) (i : Fin (2 * w + 1)) : ℕ :=
  deletedRank j (embedding w i)

theorem frameRank_injective (w j : ℕ) (hj : w + 1 ≤ j) :
    Function.Injective (frameRank w j) := by
  intro a b hab
  have hab' := congrArg (fun n : ℕ => (n : ℤ)) hab
  change (deletedRank j (embedding w a) : ℤ) =
    (deletedRank j (embedding w b) : ℤ) at hab'
  rw [deletedRank_int_eq w j hj _ (embedding_bounds w a),
    deletedRank_int_eq w j hj _ (embedding_bounds w b)] at hab'
  apply (embedding w).injective
  apply Subtype.ext
  have ha := (embedding w a).property
  have hb := (embedding w b).property
  split_ifs at hab' <;> omega

theorem frameRank_valid {w j L : ℕ} (hj : w + 1 ≤ j) (hL : j + w < L)
    (i : Fin (2 * w + 1)) : frameRank w j i + 1 < L := by
  have hi := embedding_bounds w i
  have he := deletedRank_int_eq w j hj (embedding w i) hi
  have hne := (embedding w i).property
  unfold frameRank
  split_ifs at he <;> omega

/-- This is the actual finite collection of distinct physical gap ranks
to which the original-law first-moment and rectangle estimates apply. -/
def frameRanks (w j : ℕ) : Finset ℕ := univ.image (frameRank w j)

theorem frameRanks_card (w j : ℕ) (hj : w + 1 ≤ j) :
    (frameRanks w j).card = 2 * w + 1 := by
  rw [frameRanks, card_image_of_injective _ (frameRank_injective w j hj)]
  simp only [card_univ, Fintype.card_fin]

theorem frameRanks_valid {w j L : ℕ} (hj : w + 1 ≤ j) (hL : j + w < L)
    {i : ℕ} (hi : i ∈ frameRanks w j) : i + 1 < L := by
  obtain ⟨a, _, rfl⟩ := mem_image.1 hi
  exact frameRank_valid hj hL a

set_option maxHeartbeats 800000 in
/-- Exact finite-polynomial evaluation on the contiguous deleted frame. -/
theorem realCoeff_eval_deletedGaps (w : ℕ) (p : MvPolynomial ExteriorIndex ℚ)
    (hp : ∀ i ∈ p.vars, -(w : ℤ) - 1 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (w : ℤ))
    (j : ℕ) (U : Finset ℕ) :
    eval (fun i => (subsetGap U (frameRank w j i) : ℝ)) (realCoeff w p) =
      exteriorEval (fun i => (subsetGap U (deletedRank j i) : ℝ)) p := by
  change eval (fun i => (subsetGap U (deletedRank j (embedding w i)) : ℝ))
      (realCoeff w p) =
    eval₂ (algebraMap ℚ ℝ) (fun i => (subsetGap U (deletedRank j i) : ℝ)) p
  exact realCoeff_eval w p hp (fun i => (subsetGap U (deletedRank j i) : ℝ))

end

end PrimeGapNormality.Prime.CoreCyclic.OnePoint.FiniteExterior
