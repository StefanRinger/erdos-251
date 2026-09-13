import PrimeGapNormality.Prime.CoreCyclicCanonical

/-!
Finite variable support in the concrete cyclic division algorithm. The
primitive loses one variable of width; width zero means a constant tuple.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open MvPolynomial

noncomputable section

def UsesBelow {k : ℕ} (F : PeriodicLocal k) (n : ℕ) : Prop :=
  ∀ r i, i ∈ (F r).vars → i < n

theorem vars_subset_of_support_subset {p q : LocalPoly}
    (h : p.support ⊆ q.support) : p.vars ⊆ q.vars := by
  intro i hi
  obtain ⟨m, hm, him⟩ := (mem_vars_iff_mem_support i).1 hi
  exact (mem_vars_iff_mem_support i).2 ⟨m, h hm, him⟩

theorem usesBelow_mono {k n m : ℕ} {F : PeriodicLocal k}
    (hF : UsesBelow F n) (hn : n ≤ m) : UsesBelow F m :=
  fun r i hi ↦ (hF r i hi).trans_le hn

theorem usesBelow_zero {k n : ℕ} : UsesBelow (0 : PeriodicLocal k) n := by
  intro r i hi
  simp at hi

theorem usesBelow_constantTuple {k n : ℕ} (c : Fin k → ℚ) :
    UsesBelow (constantTuple c) n := by
  intro r i hi
  simp [constantTuple] at hi

theorem usesBelow_add {k n : ℕ} {F G : PeriodicLocal k}
    (hF : UsesBelow F n) (hG : UsesBelow G n) : UsesBelow (F + G) n := by
  intro r i hi
  rcases Finset.mem_union.1 (vars_add_subset _ _ hi) with hi | hi
  · exact hF r i hi
  · exact hG r i hi

theorem usesBelow_sub {k n : ℕ} {F G : PeriodicLocal k}
    (hF : UsesBelow F n) (hG : UsesBelow G n) : UsesBelow (F - G) n := by
  intro r i hi
  rcases Finset.mem_union.1 (vars_sub_subset (p := F r) (q := G r) hi) with hi | hi
  · exact hF r i hi
  · exact hG r i hi

theorem usesBelow_smul {k n : ℕ} {F : PeriodicLocal k}
    (a : ℚ) (hF : UsesBelow F n) : UsesBelow (a • F) n := by
  intro r i hi
  exact hF r i (vars_subset_of_support_subset support_smul hi)

theorem mem_vars_stripPoly_one {p : LocalPoly} {i : ℕ}
    (hi : i ∈ (stripPoly 1 p).vars) : i + 1 ∈ p.vars := by
  obtain ⟨m, hm, him⟩ := (mem_vars_iff_mem_support i).1 hi
  have hc : p.coeff (m.mapDomain Nat.succ) ≠ 0 := by
    simpa only [mem_support_iff, stripPoly_one_eq_killCompl, coeff_killCompl] using hm
  apply (mem_vars_iff_mem_support (i + 1)).2
  refine ⟨m.mapDomain Nat.succ, mem_support_iff.2 hc, ?_⟩
  simpa only [Finsupp.mem_support_iff, Finsupp.mapDomain_apply Nat.succ_injective] using
    Finsupp.mem_support_iff.1 him

theorem usesBelow_drop {k n : ℕ} (hk : 0 < k) {F : PeriodicLocal k}
    (hF : UsesBelow F (n + 1)) : UsesBelow (drop hk F) n := by
  intro r i hi
  have h := hF (predecessor hk r) (i + 1) (mem_vars_stripPoly_one hi)
  omega

theorem rootPart_vars_subset {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k)
    (r : Fin k) : (rootPart hk F r).vars ⊆ (F r).vars := by
  apply vars_subset_of_support_subset
  have hp : rootPart hk F r = F r - rename Nat.succ (stripPoly 1 (F r)) := by
    simp [rootPart_apply]
  rw [hp]
  exact (support_sub (σ := ℕ) (p := F r)
    (q := rename Nat.succ (stripPoly 1 (F r)))).trans
    (Finset.union_subset (Finset.Subset.refl _)
    (by simpa only [stripPoly_one_eq_killCompl] using
      (support_rename_killCompl_subset (p := F r) Nat.succ_injective)))

theorem usesBelow_rootPart {k n : ℕ} (hk : 0 < k) {F : PeriodicLocal k}
    (hF : UsesBelow F n) : UsesBelow (rootPart hk F) n :=
  fun r i hi ↦ hF r i (rootPart_vars_subset hk F r hi)

theorem eq_constantTuple_of_usesBelow_zero {k : ℕ} {F : PeriodicLocal k}
    (hF : UsesBelow F 0) : F = constantTuple (fun r ↦ (F r).coeff 0) := by
  funext r
  apply vars_eq_empty_iff_eq_C.1
  exact Finset.eq_empty_iff_forall_notMem.2 fun i hi ↦ (Nat.not_lt_zero i) (hF r i hi)

theorem usesBelow_constantPrimitive (B : ℕ) {k n : ℕ} (hk : 0 < k)
    (c : Fin k → ℚ) : UsesBelow (constantPrimitive B hk c) n := by
  unfold constantPrimitive
  apply usesBelow_smul
  suffices ∀ j, UsesBelow (geometricPrimitive B hk j (constantTuple c)) n from this k
  intro j
  induction j with
  | zero => simpa using (usesBelow_zero (k := k) (n := n))
  | succ j ih =>
    rw [geometricPrimitive_succ]
    apply usesBelow_add (usesBelow_smul _ ih)
    intro r i hi
    simp only [shiftPower_constantTuple, vars_C, Finset.notMem_empty] at hi

/-- The division algorithm preserves the remainder's width and strictly
reduces the primitive's width, including the constant boundary case. -/
theorem exists_rooted_decomposition_width {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (n : ℕ) (F : PeriodicLocal k) (hF : UsesBelow F n) :
    ∃ R H : PeriodicLocal k, drop hk R = 0 ∧
      F = R + cyclicTelescope B hk H ∧ UsesBelow R n ∧ UsesBelow H (n - 1) := by
  induction n generalizing F with
  | zero =>
    let c : Fin k → ℚ := fun r ↦ (F r).coeff 0
    refine ⟨0, constantPrimitive B hk c, by simp, ?_, usesBelow_zero,
      usesBelow_constantPrimitive B hk c⟩
    simpa only [zero_add, telescope_constantPrimitive hB hk] using
      eq_constantTuple_of_usesBelow_zero hF
  | succ n ih =>
    obtain ⟨R, H, hR, hD, hRw, hHw⟩ := ih (drop hk F) (usesBelow_drop hk hF)
    refine ⟨rootPart hk F + (B : ℚ) • R, (B : ℚ) • H - drop hk F,
      by simp [hR], ?_, ?_, ?_⟩
    · calc
        F = rootPart hk F + (B : ℚ) • drop hk F -
            cyclicTelescope B hk (drop hk F) := one_step_decomposition B hk F
        _ = rootPart hk F + (B : ℚ) • R +
            cyclicTelescope B hk ((B : ℚ) • H - drop hk F) := by
          rw [map_sub, map_smul, hD]
          module
    · exact usesBelow_add (usesBelow_rootPart hk hF)
        (usesBelow_smul _ (usesBelow_mono hRw (Nat.le_succ n)))
    · simpa only [Nat.add_sub_cancel] using
        usesBelow_sub (usesBelow_smul (B : ℚ) (usesBelow_mono hHw (Nat.sub_le n 1)))
          (usesBelow_drop hk hF)

theorem normalForm_usesBelow {B k n : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) (hF : UsesBelow F n) : UsesBelow (normalForm hB hk F) n := by
  obtain ⟨R, H, hR, hD, hRw, _⟩ := exists_rooted_decomposition_width hB hk n F hF
  rwa [normalForm_eq_of_decomposition hB hk F R H hR hD]

theorem primitive_usesBelow {B k n : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) (hF : UsesBelow F n) : UsesBelow (primitive hB hk F) (n - 1) := by
  obtain ⟨R, H, hR, hD, _, hHw⟩ := exists_rooted_decomposition_width hB hk n F hF
  have hNF := normalForm_eq_of_decomposition hB hk F R H hR hD
  have hdecomp := decomposition hB hk F
  rw [hNF] at hdecomp
  have hH : primitive hB hk F = H :=
    telescope_injective hB hk (add_left_cancel (hdecomp.symm.trans hD))
  rwa [hH]

end

end PrimeGapNormality.Prime.CoreCyclic
