import PrimeGapNormality.Prime.CoreCyclicInsertionEvaluation
import PrimeGapNormality.Prime.CoreLinearInsertionAction
import PrimeGapNormality.Prime.CoreLocalSeriesRecurrence

/-!
# The formal cyclic action as an actual finite gap insertion

The formal signed action is evaluated on a real complete frame.  Relative
emission index `e` uses weight `B^(-(e+1))`; moving the point of rank `j`
splits the adjacent gaps at indices `j-1` and `j`.  This file keeps the
relative label clock explicit.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Finset MvPolynomial
open scoped BigOperators

noncomputable section

/-- The literal first-`K` local-polynomial phase on a real gap array. -/
def coreCyclicFinitePhase (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : PeriodicLocal k) (K : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ e ∈ range K,
    eval₂ (algebraMap ℚ ℝ) (fun i ↦ g (e + i)) (F (phaseAt hk r e)) /
      (B : ℝ) ^ (e + 1)

/-- Insert a moving split into a signed complete frame.  Signed coordinate
`-1` is the left new gap, coordinate `0` is the right new gap, and all
other coordinates are exterior gaps. -/
def actionGapArray (y : OnePoint.ExteriorIndex → ℝ) (v : ℝ)
    (j q : ℕ) : ℝ :=
  OnePoint.movedGapAssignment (OnePoint.movingAssignment y v)
    ((q : ℤ) - (j : ℤ))

@[simp] theorem actionGapArray_left
    (y : OnePoint.ExteriorIndex → ℝ) (v : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    actionGapArray y v j (j - 1) = v := by
  have hcast : ((j - 1 : ℕ) : ℤ) - (j : ℤ) = -1 := by
    rw [Nat.cast_sub hj]
    norm_num
  rw [actionGapArray, hcast]
  simp [OnePoint.movedGapAssignment]

@[simp] theorem actionGapArray_right
    (y : OnePoint.ExteriorIndex → ℝ) (v : ℝ) (j : ℕ) :
    actionGapArray y v j j = y ⟨0, by norm_num⟩ - v := by
  simp [actionGapArray, OnePoint.movedGapAssignment, OnePoint.movingAssignment]

theorem actionGapArray_eq_exterior
    (y : OnePoint.ExteriorIndex → ℝ) (v : ℝ) {j q : ℕ}
    (hleft : q ≠ j - 1) (hright : q ≠ j) :
    actionGapArray y v j q =
      y ⟨(q : ℤ) - (j : ℤ), by
        intro h
        have : q = j - 1 := by
          omega
        exact hleft this⟩ := by
  unfold actionGapArray OnePoint.movedGapAssignment OnePoint.movingAssignment
  have hzero : (q : ℤ) - (j : ℤ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hright)
  have hneg : (q : ℤ) - (j : ℤ) ≠ -1 := by
    intro h
    apply hleft
    omega
  simp [hzero, hneg]

/-- Moving backwards through the cyclic labels undoes the same number of
forward relative emissions. -/
theorem predecessor_iterate_phaseAt_sub
    {k : ℕ} (hk : 0 < k) (r : Fin k) {j t : ℕ} (ht : t ≤ j) :
    (predecessor hk)^[t] (phaseAt hk r j) = phaseAt hk r (j - t) := by
  induction t generalizing j with
  | zero => simp
  | succ t ih =>
      have htj : t ≤ j := (Nat.le_succ t).trans ht
      have hpos : 0 < j - t := by omega
      rw [Function.iterate_succ_apply', ih htj]
      have hstep := congrArg (predecessor hk)
        (phaseAt_succ hk r (j - t - 1))
      rw [predecessor_successor] at hstep
      have hsucc : j - t - 1 + 1 = j - t := by omega
      have hsub : j - (t + 1) = j - t - 1 := by omega
      rw [hsucc] at hstep
      rw [hsub]
      exact hstep

theorem cyclicSucc_phaseAt_pred
    {k : ℕ} (hk : 0 < k) (r : Fin k) {j : ℕ} (hj : 1 ≤ j) :
    cyclicSucc hk (phaseAt hk r (j - 1)) = phaseAt hk r j := by
  have hstep := phaseAt_succ hk r (j - 1)
  rw [Nat.sub_add_cancel hj] at hstep
  exact hstep.symm

theorem action_label_eq_phaseAt
    {k : ℕ} (hk : 0 < k) (r : Fin k) {j t : ℕ}
    (hj : 1 ≤ j) (ht : t ≤ j) :
    (predecessor hk)^[t] (cyclicSucc hk (phaseAt hk r (j - 1))) =
      phaseAt hk r (j - t) := by
  rw [cyclicSucc_phaseAt_pred hk r hj]
  exact predecessor_iterate_phaseAt_sub hk r ht

/-- A summand in the formal action is the literal local evaluation at
emission `j-t` in the split gap array. -/
theorem action_summand_eq_local
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : PeriodicLocal k)
    (y : OnePoint.ExteriorIndex → ℝ) (v : ℝ) {j t : ℕ}
    (hj : 1 ≤ j) (ht : t ≤ j) :
    eval₂ (algebraMap ℚ ℝ)
        (fun i : ℕ ↦ OnePoint.movedGapAssignment
          (OnePoint.movingAssignment y v) ((i : ℤ) - (t : ℤ)))
        (F ((predecessor hk)^[t]
          (cyclicSucc hk (phaseAt hk r (j - 1))))) =
      eval₂ (algebraMap ℚ ℝ)
        (fun i : ℕ ↦ actionGapArray y v j (j - t + i))
        (F (phaseAt hk r (j - t))) := by
  rw [action_label_eq_phaseAt hk r hj ht]
  congr 1
  funext i
  unfold actionGapArray
  congr 1
  have hcast : (((j - t + i : ℕ) : ℤ) - (j : ℤ)) =
      (i : ℤ) - (t : ℤ) := by
    rw [Nat.cast_add, Nat.cast_sub ht]
    ring
  exact hcast.symm

/-- Exact evaluation of the formal action by the `w+2` affected physical
local-polynomial summands. -/
theorem movingAction_eval_eq_affected
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : PeriodicLocal k) (w j : ℕ) (hwj : w + 1 ≤ j)
    (y : OnePoint.ExteriorIndex → ℝ) (v : ℝ) :
    Polynomial.eval v
        (OnePoint.movingSpecialization
          (OnePoint.action B hk w (phaseAt hk r (j - 1)) F) y) =
      ∑ t ∈ range (w + 2), (B : ℝ) ^ t *
        eval₂ (algebraMap ℚ ℝ)
          (fun i : ℕ ↦ actionGapArray y v j (j - t + i))
          (F (phaseAt hk r (j - t))) := by
  rw [OnePoint.movingSpecialization_action_eval]
  apply sum_congr rfl
  intro t ht
  congr 1
  exact action_summand_eq_local hk r F y v (by omega) (by
    have := mem_range.mp ht
    omega)

/-- The physically weighted part of the finite phase whose local windows
meet the moving split. -/
def coreCyclicAffectedPhase
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : PeriodicLocal k) (w j : ℕ)
    (y : OnePoint.ExteriorIndex → ℝ) (v : ℝ) : ℝ :=
  ∑ t ∈ range (w + 2),
    eval₂ (algebraMap ℚ ℝ)
        (fun i : ℕ ↦ actionGapArray y v j (j - t + i))
        (F (phaseAt hk r (j - t))) /
      (B : ℝ) ^ (j - t + 1)

/-- The common physical factor is exactly `B^(-(j+1))`; no asymptotic
approximation enters this identity. -/
theorem coreCyclicAffectedPhase_sub
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : PeriodicLocal k) (w j : ℕ) (hwj : w + 1 ≤ j)
    (y : OnePoint.ExteriorIndex → ℝ) (u v : ℝ) :
    coreCyclicAffectedPhase B hk r F w j y u -
        coreCyclicAffectedPhase B hk r F w j y v =
      (Polynomial.eval u
          (OnePoint.movingSpecialization
            (OnePoint.action B hk w (phaseAt hk r (j - 1)) F) y) -
        Polynomial.eval v
          (OnePoint.movingSpecialization
            (OnePoint.action B hk w (phaseAt hk r (j - 1)) F) y)) /
        (B : ℝ) ^ (j + 1) := by
  have hu := movingAction_eval_eq_affected B hk r F w j hwj y u
  have hv := movingAction_eval_eq_affected B hk r F w j hwj y v
  unfold coreCyclicAffectedPhase
  rw [← sum_sub_distrib, hu, hv, ← sum_sub_distrib, Finset.sum_div]
  apply sum_congr rfl
  intro t ht
  have htj : t ≤ j := by
    have := mem_range.mp ht
    omega
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  have hpow : (B : ℝ) ^ (j + 1) =
      (B : ℝ) ^ (j - t + 1) * (B : ℝ) ^ t := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp [hB0]

private theorem coreCyclic_eval_eq_of_emission_unaffected
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : PeriodicLocal k)
    (w j e : ℕ) (hwj : w + 1 ≤ j)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (y : OnePoint.ExteriorIndex → ℝ) (u v : ℝ)
    (he : e ∉ Ico (j - w - 1) (j + 1)) :
    eval₂ (algebraMap ℚ ℝ)
        (fun i : ℕ ↦ actionGapArray y u j (e + i))
        (F (phaseAt hk r e)) =
      eval₂ (algebraMap ℚ ℝ)
        (fun i : ℕ ↦ actionGapArray y v j (e + i))
        (F (phaseAt hk r e)) := by
  apply eval₂_congr
  intro i m hi hm
  have hiv : i ∈ (F (phaseAt hk r e)).vars :=
    (mem_vars_iff_mem_support i).2 ⟨m, by
      exact mem_support_iff.mpr hm, hi⟩
  have hiw := hw (phaseAt hk r e) i hiv
  have hleft : e + i ≠ j - 1 := by
    intro h
    apply he
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hright : e + i ≠ j := by
    intro h
    apply he
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  rw [actionGapArray_eq_exterior y u hleft hright,
    actionGapArray_eq_exterior y v hleft hright]

/-- Every unaffected emission cancels, and the remaining interval is the
reversal `e=j-t`, `0≤t≤w+1`. -/
theorem coreCyclicFinitePhase_sub_eq_affected
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : PeriodicLocal k) (K w j : ℕ)
    (hwj : w + 1 ≤ j) (hjK : j < K)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (y : OnePoint.ExteriorIndex → ℝ) (u v : ℝ) :
    coreCyclicFinitePhase B hk r F K (actionGapArray y u j) -
        coreCyclicFinitePhase B hk r F K (actionGapArray y v j) =
      coreCyclicAffectedPhase B hk r F w j y u -
        coreCyclicAffectedPhase B hk r F w j y v := by
  unfold coreCyclicFinitePhase coreCyclicAffectedPhase
  rw [← sum_sub_distrib, ← sum_sub_distrib]
  let term : ℕ → ℝ := fun e ↦
    eval₂ (algebraMap ℚ ℝ)
        (fun i : ℕ ↦ actionGapArray y u j (e + i))
        (F (phaseAt hk r e)) / (B : ℝ) ^ (e + 1) -
      eval₂ (algebraMap ℚ ℝ)
        (fun i : ℕ ↦ actionGapArray y v j (e + i))
        (F (phaseAt hk r e)) / (B : ℝ) ^ (e + 1)
  change (∑ e ∈ range K, term e) =
    ∑ t ∈ range (w + 2), term (j - t)
  have hsub : Ico (j - w - 1) (j + 1) ⊆ range K := by
    intro e he
    exact mem_range.mpr ((mem_Ico.mp he).2.trans_le (Nat.succ_le_iff.mpr hjK))
  have hrestrict :
      (∑ e ∈ range K, term e) =
        ∑ e ∈ Ico (j - w - 1) (j + 1), term e := by
    apply (sum_subset hsub ?_).symm
    intro e heK he
    unfold term
    rw [coreCyclic_eval_eq_of_emission_unaffected hk r F w j e hwj hw y u v he,
      sub_self]
  rw [hrestrict]
  have href := sum_Ico_reflect term 0 (m := w + 2) (n := j) (by omega)
  have hlower : j + 1 - (w + 2) = j - w - 1 := by omega
  rw [hlower, Nat.Ico_zero_eq_range, Nat.sub_zero] at href
  exact href.symm

/-- Complete finite real gap-array insertion identity. -/
theorem coreCyclicFinitePhase_insert_sub
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : PeriodicLocal k) (K w j : ℕ)
    (hwj : w + 1 ≤ j) (hjK : j < K)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (y : OnePoint.ExteriorIndex → ℝ) (u v : ℝ) :
    coreCyclicFinitePhase B hk r F K (actionGapArray y u j) -
        coreCyclicFinitePhase B hk r F K (actionGapArray y v j) =
      (Polynomial.eval u
          (OnePoint.movingSpecialization
            (OnePoint.action B hk w (phaseAt hk r (j - 1)) F) y) -
        Polynomial.eval v
          (OnePoint.movingSpecialization
            (OnePoint.action B hk w (phaseAt hk r (j - 1)) F) y)) /
        (B : ℝ) ^ (j + 1) := by
  rw [coreCyclicFinitePhase_sub_eq_affected B hk r F K w j hwj hjK hw y u v]
  exact coreCyclicAffectedPhase_sub hB hk r F w j hwj y u v

end

end PrimeGapNormality.Prime.CoreCyclic
