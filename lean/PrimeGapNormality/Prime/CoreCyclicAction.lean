import PrimeGapNormality.Prime.CoreCyclicOnePoint

/-!
The one-point test for arbitrary nonzero canonical normal tuples. The degree
and highest homogeneous piece are extracted from the actual input; no
homogeneity hypothesis is imposed on the final action theorem.
-/

namespace PrimeGapNormality.Prime.CoreCyclic.OnePoint

open MvPolynomial
open scoped BigOperators

noncomputable section

def tupleDegree {k : ℕ} (F : PeriodicLocal k) : ℕ :=
  Finset.univ.sup fun r : Fin k ↦ (F r).totalDegree

theorem homogeneousComponent_totalDegree_ne_zero {σ : Type*}
    (p : MvPolynomial σ ℚ) (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨m, hm, hd⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
    (fun m : σ →₀ ℕ ↦ m.degree)
  change p.totalDegree = m.degree at hd
  intro hzero
  have hc := congrArg (MvPolynomial.coeff m) hzero
  rw [coeff_homogeneousComponent, if_pos hd.symm, coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.1 hm) hc

theorem totalDegree_pos_of_rooted (p : LocalPoly) (hp : p ≠ 0)
    (hroot : ∀ m : ℕ →₀ ℕ, m 0 = 0 → p.coeff m = 0) :
    0 < p.totalDegree := by
  by_contra hnot
  have hd : p.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have heq := totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : p.coeff 0 = 0 := hroot 0 rfl
  exact hp (by simpa [hc] using heq)

theorem tupleDegree_pos_of_rooted {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k)
    (hroot : drop hk F = 0) (hF : F ≠ 0) : 0 < tupleDegree F := by
  obtain ⟨r, hr⟩ : ∃ r, F r ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hF (funext hn)
  exact (totalDegree_pos_of_rooted (F r) hr ((drop_eq_zero_iff_rooted hk F).1 hroot r)).trans_le
    (Finset.le_sup (f := fun r : Fin k ↦ (F r).totalDegree) (Finset.mem_univ r))

/-- An actual nonzero component attains the highest tuple degree. -/
theorem exists_top_component {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k)
    (hroot : drop hk F = 0) (hF : F ≠ 0) :
    ∃ r : Fin k, (F r).totalDegree = tupleDegree F ∧ F r ≠ 0 := by
  have hpos := tupleDegree_pos_of_rooted hk F hroot hF
  have hu : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup Finset.univ hu
    (fun r : Fin k ↦ (F r).totalDegree)
  refine ⟨r, hr.symm, ?_⟩
  intro hz
  have hd : tupleDegree F = 0 := by
    calc
      tupleDegree F = (F r).totalDegree := hr
      _ = 0 := by rw [hz]; exact totalDegree_zero
  omega

theorem topTuple_ne_zero {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k)
    (hroot : drop hk F = 0) (hF : F ≠ 0) :
    (fun r ↦ homogeneousComponent (tupleDegree F) (F r)) ≠ 0 := by
  obtain ⟨r, hr, hnonzero⟩ := exists_top_component hk F hroot hF
  intro hz
  have hcomp := congrFun hz r
  apply homogeneousComponent_totalDegree_ne_zero (F r) hnonzero
  simpa [hr] using hcomp

theorem vars_homogeneousComponent_subset {σ : Type*} (d : ℕ)
    (p : MvPolynomial σ ℚ) : (homogeneousComponent d p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).1 hi
  rw [support_homogeneousComponent] at hm
  exact (mem_vars_iff_mem_support i).2 ⟨m, (Finset.mem_filter.1 hm).1, hmi⟩

/-- The invertible point-movement substitution is linear in the variables,
so it commutes with each homogeneous projection. -/
theorem homogeneousComponent_moveSubst (d : ℕ) (p : SignedPoly) :
    homogeneousComponent d (moveSubst p) = moveSubst (homogeneousComponent d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    have hp : (monomial m c : SignedPoly).IsHomogeneous m.degree :=
      isHomogeneous_monomial c rfl
    have hm := moveSubst_isHomogeneous (monomial m c) m.degree hp
    rw [homogeneousComponent_of_mem hm, homogeneousComponent_of_mem hp]
    split_ifs <;> simp
  | add p q hp hq => simp [map_add, hp, hq]

theorem homogeneousComponent_preAction (B : ℕ) {k : ℕ} (hk : 0 < k)
    (w : ℕ) (s : Fin k) (F : PeriodicLocal k) (d : ℕ) :
    homogeneousComponent d (preAction B hk w s F) =
      preAction B hk w s (fun r ↦ homogeneousComponent d (F r)) := by
  unfold preAction
  simp only [map_sum, map_smul, signedShift, ← rename_homogeneousComponent]

theorem homogeneousComponent_action (B : ℕ) {k : ℕ} (hk : 0 < k)
    (w : ℕ) (s : Fin k) (F : PeriodicLocal k) (d : ℕ) :
    homogeneousComponent d (action B hk w s F) =
      action B hk w s (fun r ↦ homogeneousComponent d (F r)) := by
  simp only [action, homogeneousComponent_moveSubst, homogeneousComponent_preAction]

/-- A moving homogeneous component forces the whole polynomial to move;
the proof compares actual derivative coefficients. -/
theorem pderiv_ne_zero_of_homogeneousComponent {σ : Type*}
    (p : MvPolynomial σ ℚ) (i : σ) (d : ℕ)
    (hp : pderiv i (homogeneousComponent d p) ≠ 0) : pderiv i p ≠ 0 := by
  classical
  intro hz
  apply hp
  ext m
  rw [coeff_pderiv, coeff_homogeneousComponent, coeff_zero]
  split_ifs
  · have hc := congrArg (MvPolynomial.coeff m) hz
    simpa [coeff_pderiv] using hc
  · simp

/-- The top-degree part of some actual local action is nonconstant in the
moving coordinate, for every nonzero normal tuple. -/
theorem exists_top_action_of_normal {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (w : ℕ) (F : PeriodicLocal k) (hroot : drop hk F = 0) (hF : F ≠ 0)
    (hw : ∀ r i, i ∈ (F r).vars → i ≤ w) :
    ∃ s : Fin k,
      pderiv (-1) (homogeneousComponent (tupleDegree F) (action B hk w s F)) ≠ 0 := by
  let P : PeriodicLocal k := fun r ↦ homogeneousComponent (tupleDegree F) (F r)
  have hP0 : P ≠ 0 := topTuple_ne_zero hk F hroot hF
  have hProot : drop hk P = 0 := rooted_homogeneousComponent hk F hroot _
  have hPhom : ∀ r, (P r).IsHomogeneous (tupleDegree F) :=
    fun r ↦ homogeneousComponent_isHomogeneous _ _
  have hPw : ∀ r i, i ∈ (P r).vars → i ≤ w := by
    intro r i hi
    exact hw r i (vars_homogeneousComponent_subset _ _ hi)
  obtain ⟨s, hs⟩ := exists_action_of_normal_homogeneous hB hk w (tupleDegree F) P hProot hP0 hPhom hPw
  refine ⟨s, ?_⟩
  rw [homogeneousComponent_action]
  exact hs

/-- Nonhomogeneous final API: no homogeneity assumption on `F`. -/
theorem exists_action_of_normal {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (w : ℕ) (F : PeriodicLocal k) (hroot : drop hk F = 0) (hF : F ≠ 0)
    (hw : ∀ r i, i ∈ (F r).vars → i ≤ w) :
    ∃ s : Fin k, pderiv (-1) (action B hk w s F) ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_top_action_of_normal hB hk w F hroot hF hw
  exact ⟨s, pderiv_ne_zero_of_homogeneousComponent _ (-1) (tupleDegree F) hs⟩

/-- The same endpoint expressed using the paper's canonical fixed-point
condition `F = N F`, rather than the equivalent rooted support condition. -/
theorem exists_top_action_of_normalForm_fixed {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (w : ℕ) (F : PeriodicLocal k) (hF : F ≠ 0) (hnormal : F = normalForm hB hk F)
    (hw : ∀ r i, i ∈ (F r).vars → i ≤ w) :
    ∃ s : Fin k,
      pderiv (-1) (homogeneousComponent (tupleDegree F) (action B hk w s F)) ≠ 0 := by
  apply exists_top_action_of_normal hB hk w F _ hF hw
  exact (congrArg (drop hk) hnormal).trans (drop_normalForm hB hk F)

end

end PrimeGapNormality.Prime.CoreCyclic.OnePoint
