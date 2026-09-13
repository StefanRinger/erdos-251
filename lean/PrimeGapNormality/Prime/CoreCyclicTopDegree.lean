import PrimeGapNormality.Prime.CoreCyclicAction

/-!
# The genuine top-degree moving component

For a nonzero rooted cyclic tuple, this file isolates the homogeneous piece
at the maximum total degree over all cyclic labels.  That piece remains
nonzero, rooted, and within the original width, so the homogeneous
one-point theorem supplies a moving derivative at this exact top degree.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Finset MvPolynomial

noncomputable section

/-- Maximum total degree among the finitely many cyclic components. -/
def topDegree {k : ℕ} (N : PeriodicLocal k) : ℕ :=
  Finset.univ.sup fun r : Fin k ↦ (N r).totalDegree

theorem topDegree_eq_tupleDegree {k : ℕ} (N : PeriodicLocal k) :
    topDegree N = OnePoint.tupleDegree N :=
  rfl

/-- The degree-`topDegree N` homogeneous part, component by component. -/
def topHomogeneousTuple {k : ℕ} (N : PeriodicLocal k) : PeriodicLocal k :=
  fun r ↦ homogeneousComponent (topDegree N) (N r)

theorem topDegree_pos_of_rooted {k : ℕ} (hk : 0 < k)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0) :
    0 < topDegree N := by
  simpa only [topDegree_eq_tupleDegree] using
    OnePoint.tupleDegree_pos_of_rooted hk N hroot hN

theorem one_le_topDegree_of_rooted {k : ℕ} (hk : 0 < k)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0) :
    1 ≤ topDegree N :=
  Nat.one_le_iff_ne_zero.mpr (topDegree_pos_of_rooted hk N hroot hN).ne'

theorem topHomogeneousTuple_ne_zero {k : ℕ} (hk : 0 < k)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0) :
    topHomogeneousTuple N ≠ 0 := by
  change (fun r ↦ homogeneousComponent (topDegree N) (N r)) ≠ 0
  rw [topDegree_eq_tupleDegree]
  exact OnePoint.topTuple_ne_zero hk N hroot hN

theorem topHomogeneousTuple_rooted {k : ℕ} (hk : 0 < k)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) :
    drop hk (topHomogeneousTuple N) = 0 := by
  change drop hk (fun r ↦ homogeneousComponent (topDegree N) (N r)) = 0
  exact OnePoint.rooted_homogeneousComponent hk N hroot (topDegree N)

theorem topHomogeneousTuple_isHomogeneous {k : ℕ} (N : PeriodicLocal k)
    (r : Fin k) :
    (topHomogeneousTuple N r).IsHomogeneous (topDegree N) :=
  homogeneousComponent_isHomogeneous _ _

/-- Passing to the top homogeneous part introduces no new gap variable. -/
theorem topHomogeneousTuple_width {k w : ℕ} (N : PeriodicLocal k)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w) :
    ∀ r i, i ∈ (topHomogeneousTuple N r).vars → i ≤ w := by
  intro r i hi
  exact hw r i (OnePoint.vars_homogeneousComponent_subset _ _ hi)

/-- The homogeneous one-point theorem applied at the actual maximum degree,
not at an unspecified nonzero degree. -/
theorem exists_action_topHomogeneousTuple_of_rooted
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w) :
    ∃ s : Fin k,
      pderiv (-1)
        (OnePoint.action B hk w s (topHomogeneousTuple N)) ≠ 0 := by
  exact OnePoint.exists_action_of_normal_homogeneous hB hk w (topDegree N)
    (topHomogeneousTuple N) (topHomogeneousTuple_rooted hk N hroot)
    (topHomogeneousTuple_ne_zero hk N hroot hN)
    (topHomogeneousTuple_isHomogeneous N)
    (topHomogeneousTuple_width N hw)

/-- Equivalent action-level form: the top homogeneous component of an
actual action of `N` has nonzero moving derivative. -/
theorem exists_topDegree_movingDerivative_of_rooted
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w) :
    ∃ s : Fin k,
      pderiv (-1)
        (homogeneousComponent (topDegree N) (OnePoint.action B hk w s N)) ≠ 0 := by
  obtain ⟨s, hs⟩ :=
    exists_action_topHomogeneousTuple_of_rooted hB hk w N hroot hN hw
  refine ⟨s, ?_⟩
  rw [OnePoint.homogeneousComponent_action]
  exact hs

/-- Canonical fixed-point formulation used after cyclic normal-form
reduction. -/
theorem exists_topDegree_movingDerivative_of_normalForm_fixed
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (w : ℕ)
    (N : PeriodicLocal k) (hN : N ≠ 0)
    (hnormal : N = normalForm hB hk N)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w) :
    ∃ s : Fin k,
      pderiv (-1)
        (homogeneousComponent (topDegree N) (OnePoint.action B hk w s N)) ≠ 0 := by
  apply exists_topDegree_movingDerivative_of_rooted hB hk w N _ hN hw
  exact (congrArg (drop hk) hnormal).trans (drop_normalForm hB hk N)

end

end PrimeGapNormality.Prime.CoreCyclic
