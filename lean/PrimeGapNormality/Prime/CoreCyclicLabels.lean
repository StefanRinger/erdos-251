import PrimeGapNormality.Prime.CoreCyclicPhysicalInsertion
import PrimeGapNormality.Prime.CoreLocalCriticalRank

/-! Matching the algebraically chosen action label to the literal resampling
rank, without spending additional arithmetic depth. -/

namespace PrimeGapNormality.Prime.CoreCyclic
open Finset
open scoped Topology
noncomputable section

theorem phaseAt_val {k : ℕ} (hk : 0 < k) (r : Fin k) (n : ℕ) :
    (phaseAt hk r n).val = (r.val + n) % k := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hs : cyclicSucc hk = fun s : Fin k ↦ s + 1 := rfl
  have hval (m : ℕ) : ((m • (1 : Fin k) : Fin k) : ℕ) = m % k := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [succ_nsmul, Fin.val_add, ih, Fin.val_one']
      simp only [Nat.add_mod, Nat.mod_mod]
  unfold phaseAt
  rw [hs, add_right_iterate_apply, Fin.val_add, hval]
  simp only [Nat.add_mod, Nat.mod_mod]

theorem phaseAt_eq_of_modEq {k n m : ℕ} (hk : 0 < k) (r : Fin k)
    (h : Nat.ModEq k n m) : phaseAt hk r n = phaseAt hk r m := by
  apply Fin.ext
  rw [phaseAt_val, phaseAt_val]
  rw [Nat.add_mod r.val n, Nat.add_mod r.val m, h]

/-- Every action label has a representative among the one-based ranks 1..k. -/
theorem exists_insertion_residue {k : ℕ} (hk : 0 < k) (r s : Fin k) :
    ∃ a ∈ Icc 1 k, ∀ j : ℕ, 1 ≤ j → Nat.ModEq k j a →
      phaseAt hk r (j - 1) = s := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let n : Fin k := s - r
  have htarget : phaseAt hk r n.val = s := by
    apply Fin.ext
    rw [phaseAt_val]
    have heq : r + n = s := by dsimp only [n]; abel
    simpa only [Fin.val_add] using congrArg Fin.val heq
  refine ⟨n.val + 1, mem_Icc.mpr ⟨by omega, by have := n.isLt; omega⟩, ?_⟩
  intro j hj hmod
  have hphase := phaseAt_eq_of_modEq hk r hmod
  have hpred := congrArg (predecessor hk) hphase
  have hpj := predecessor_iterate_phaseAt_sub hk r (j := j) (t := 1) hj
  have hpa := predecessor_iterate_phaseAt_sub hk r (j := n.val + 1) (t := 1) (by omega)
  simp only [Function.iterate_one] at hpj hpa
  rw [hpj, hpa, Nat.add_sub_cancel] at hpred
  exact hpred.trans htarget

/-- The critical rank can be selected with the exact algebraic action label
and both finite-width margins at the nonstrict degree/base threshold. -/
theorem eventually_critical_rank_with_label
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (hd : 1 ≤ d)
    (r s : Fin k) (w : ℕ) {κ : ℝ}
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    ∀ᶠ X : ℕ in Filter.atTop, ∃ j : ℕ,
      w + 1 ≤ j ∧ j + w < profileL κ X ∧ phaseAt hk r (j - 1) = s ∧
      1 ≤ windowG X ^ d / (B : ℝ) ^ (j + 1) ∧
      windowG X ^ d / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k := by
  obtain ⟨a, ha, hlabel⟩ := exists_insertion_residue hk r s
  filter_upwards [CoreLocalCriticalRank.eventually_critical_rank_profile
    hB hk hd ha w hκ] with X hX
  obtain ⟨j, hj, hLj, hmod, hlo, hhi⟩ := hX
  exact ⟨j, hj, hLj, hlabel j (by omega) hmod, hlo, hhi⟩

end
end PrimeGapNormality.Prime.CoreCyclic
