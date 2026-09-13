import PrimeGapNormality.Prime.CoreCyclicLabels
import PrimeGapNormality.Prime.CoreCyclicOrbitIdentification
import PrimeGapNormality.Prime.CoreCyclicTopDegree

/-! Exact common-period refinement. Any common positive multiple may be
used, hence in particular an LCM. Neither the series nor its effective
degree changes. This file contains no equidistribution assumption. -/

namespace PrimeGapNormality.Prime.CorePeriodRefinement
open CoreCyclic MvPolynomial
noncomputable section

def reduceLabel {k l : ℕ} (hk : 0 < k) (r : Fin l) : Fin k :=
  ⟨r.val % k, Nat.mod_lt _ hk⟩

theorem reduce_successor {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k ∣ l) (r : Fin l) :
    reduceLabel hk (cyclicSucc hl r) = cyclicSucc hk (reduceLabel hk r) := by
  apply Fin.ext
  have hval {a : ℕ} (ha : 0 < a) (s : Fin a) :
      (cyclicSucc ha s).val = (s.val + 1) % a := by
    simpa [phaseAt] using phaseAt_val ha s 1
  change (cyclicSucc hl r).val % k = (cyclicSucc hk (reduceLabel hk r)).val
  rw [hval hl, hval hk, Nat.mod_mod_of_dvd _ hkl]
  simp [reduceLabel, Nat.add_mod]

theorem reduce_predecessor {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k ∣ l) (r : Fin l) :
    reduceLabel hk (predecessor hl r) = predecessor hk (reduceLabel hk r) := by
  apply (cyclicSuccEquiv hk).injective
  change cyclicSucc hk _ = cyclicSucc hk _
  rw [← reduce_successor hk hl hkl, successor_predecessor, successor_predecessor]

def repeatTuple {k l : ℕ} (hk : 0 < k) : PeriodicLocal k →ₗ[ℚ] PeriodicLocal l where
  toFun F r := F (reduceLabel hk r)
  map_add' F H := rfl
  map_smul' q F := rfl

@[simp] theorem repeat_apply {k l : ℕ} (hk : 0 < k)
    (F : PeriodicLocal k) (r : Fin l) : repeatTuple hk F r = F (reduceLabel hk r) := rfl

theorem reduce_surjective {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (hkl : k ∣ l) :
    Function.Surjective (reduceLabel (l := l) hk) := by
  intro r
  refine ⟨⟨r.val, r.isLt.trans_le (Nat.le_of_dvd hl hkl)⟩, ?_⟩
  apply Fin.ext
  exact Nat.mod_eq_of_lt r.isLt

theorem repeat_injective {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (hkl : k ∣ l) :
    Function.Injective (repeatTuple (l := l) hk) := by
  intro F H he
  funext r
  obtain ⟨s, hs⟩ := reduce_surjective hk hl hkl r
  simpa [repeat_apply, hs] using congrFun he s

theorem repeat_shift {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k ∣ l) (F : PeriodicLocal k) :
    repeatTuple hk (shift hk F) = shift hl (repeatTuple hk F) := by
  ext r
  simp [shift_apply, reduce_successor hk hl hkl]

theorem repeat_drop {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k ∣ l) (F : PeriodicLocal k) :
    repeatTuple hk (drop hk F) = drop hl (repeatTuple hk F) := by
  ext r
  simp [drop_apply, reduce_predecessor hk hl hkl]

theorem repeat_telescope (B : ℕ) {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k ∣ l) (F : PeriodicLocal k) :
    repeatTuple hk (cyclicTelescope B hk F) = cyclicTelescope B hl (repeatTuple hk F) := by
  simp [telescope_eq, map_sub, map_smul, repeat_shift hk hl hkl]

theorem repeat_normalForm {B k l : ℕ} (hB : 2 ≤ B)
    (hk : 0 < k) (hl : 0 < l) (hkl : k ∣ l) (F : PeriodicLocal k) :
    normalForm hB hl (repeatTuple hk F) = repeatTuple hk (normalForm hB hk F) := by
  apply normalForm_eq_of_decomposition hB hl _ _ (repeatTuple hk (primitive hB hk F))
  · rw [← repeat_drop hk hl hkl, drop_normalForm, map_zero]
  · rw [← repeat_telescope B hk hl hkl, ← map_add, ← decomposition hB hk F]

theorem repeat_topDegree {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k ∣ l) (F : PeriodicLocal k) :
    topDegree (repeatTuple (l := l) hk F) = topDegree F := by
  apply le_antisymm
  · apply Finset.sup_le
    intro s hs
    exact Finset.le_sup (f := fun r ↦ (F r).totalDegree) (Finset.mem_univ _)
  · apply Finset.sup_le
    intro r hr
    obtain ⟨s, hs⟩ := reduce_surjective hk hl hkl r
    have h := Finset.le_sup (f := fun s : Fin l ↦ (repeatTuple hk F s).totalDegree)
      (Finset.mem_univ s)
    simpa [topDegree, repeat_apply, hs] using h

theorem reduce_phaseAt {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k ∣ l) (r : Fin l) (n : ℕ) :
    reduceLabel hk (phaseAt hl r n) = phaseAt hk (reduceLabel hk r) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [phaseAt_succ, phaseAt_succ, reduce_successor hk hl hkl, ih]

theorem repeat_localValue {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k ∣ l) (r : Fin l) (g : ℕ → ℝ) (F : PeriodicLocal k) (n : ℕ) :
    localValue hl r g (repeatTuple hk F) n =
      localValue hk (reduceLabel hk r) g F n := by
  simp [localValue, reduce_phaseAt hk hl hkl]

theorem repeat_series (B : ℕ) {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k ∣ l) (r : Fin l) (g : ℕ → ℝ) (F : PeriodicLocal k) :
    coreCyclicFullSeries B hl r g (repeatTuple hk F) =
      coreCyclicFullSeries B hk (reduceLabel hk r) g F := by
  simp [coreCyclicFullSeries, repeat_localValue hk hl hkl]

end
end PrimeGapNormality.Prime.CorePeriodRefinement
