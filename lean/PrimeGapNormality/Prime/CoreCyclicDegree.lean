import PrimeGapNormality.Prime.CoreCyclicWidth

/-!
Both maps in concrete cyclic division preserve total degree. The normal-form
bound was proved in `CoreCyclicCanonical`; here the same finite elimination
also tracks the uniquely determined primitive.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open MvPolynomial

noncomputable section

theorem constantPrimitive_totalDegree (B : ℕ) {k : ℕ} (hk : 0 < k)
    (c : Fin k → ℚ) (r : Fin k) : (constantPrimitive B hk c r).totalDegree = 0 := by
  have hc := eq_constantTuple_of_usesBelow_zero
    (usesBelow_constantPrimitive (n := 0) B hk c)
  rw [hc]
  exact totalDegree_C _

/-- Actual finite division with degree bounds on both outputs. -/
theorem exists_rooted_decomposition_both_degrees {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (F : PeriodicLocal k) (d : ℕ)
    (hF : ∀ r, (F r).totalDegree ≤ d) :
    ∃ R H : PeriodicLocal k, drop hk R = 0 ∧
      F = R + cyclicTelescope B hk H ∧
      (∀ r, (R r).totalDegree ≤ d) ∧ (∀ r, (H r).totalDegree ≤ d) := by
  obtain ⟨n, c, hc⟩ := exists_dropPower_constant hk F
  suffices ∀ n : ℕ, ∀ F : PeriodicLocal k, ∀ c : Fin k → ℚ,
      dropPower hk n F = constantTuple c → (∀ r, (F r).totalDegree ≤ d) →
      ∃ R H : PeriodicLocal k, drop hk R = 0 ∧
        F = R + cyclicTelescope B hk H ∧
        (∀ r, (R r).totalDegree ≤ d) ∧ (∀ r, (H r).totalDegree ≤ d) from
    this n F c hc hF
  intro n
  induction n with
  | zero =>
    intro F c hc hF
    refine ⟨0, constantPrimitive B hk c, by simp, ?_, ?_, ?_⟩
    · simpa [telescope_constantPrimitive hB hk] using hc
    · intro r
      simp
    · intro r
      rw [constantPrimitive_totalDegree]
      exact Nat.zero_le d
  | succ n ih =>
    intro F c hc hF
    have htail : dropPower hk n (drop hk F) = constantTuple c := by
      rw [dropPower_drop]
      exact hc
    obtain ⟨R, H, hR, hD, hRd, hHd⟩ :=
      ih (drop hk F) c htail (drop_totalDegree_le hk F d hF)
    refine ⟨rootPart hk F + (B : ℚ) • R, (B : ℚ) • H - drop hk F,
      by simp [hR], ?_, ?_, ?_⟩
    · calc
        F = rootPart hk F + (B : ℚ) • drop hk F -
            cyclicTelescope B hk (drop hk F) := one_step_decomposition B hk F
        _ = rootPart hk F + (B : ℚ) • R +
            cyclicTelescope B hk ((B : ℚ) • H - drop hk F) := by
          rw [map_sub, map_smul, hD]
          module
    · intro r
      apply (totalDegree_add _ _).trans
      exact max_le (rootPart_totalDegree_le hk F d hF r)
        ((totalDegree_smul_le (B : ℚ) (R r)).trans (hRd r))
    · intro r
      apply (totalDegree_sub _ _).trans
      exact max_le ((totalDegree_smul_le (B : ℚ) (H r)).trans (hHd r))
        (drop_totalDegree_le hk F d hF r)

theorem primitive_totalDegree_le {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) (d : ℕ) (hF : ∀ r, (F r).totalDegree ≤ d) :
    ∀ r, (primitive hB hk F r).totalDegree ≤ d := by
  obtain ⟨R, H, hR, hD, _, hHd⟩ :=
    exists_rooted_decomposition_both_degrees hB hk F d hF
  have hNF := normalForm_eq_of_decomposition hB hk F R H hR hD
  have hdecomp := decomposition hB hk F
  rw [hNF] at hdecomp
  have hH : primitive hB hk F = H :=
    telescope_injective hB hk (add_left_cancel (hdecomp.symm.trans hD))
  rwa [hH]

/-- Canonical algebra outputs simultaneously satisfy the frozen paper's
width and total-degree bounds. -/
theorem canonical_support_degree_bounds {B k n : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) (d : ℕ) (hw : UsesBelow F n)
    (hd : ∀ r, (F r).totalDegree ≤ d) :
    UsesBelow (normalForm hB hk F) n ∧ UsesBelow (primitive hB hk F) (n - 1) ∧
      (∀ r, (normalForm hB hk F r).totalDegree ≤ d) ∧
      (∀ r, (primitive hB hk F r).totalDegree ≤ d) :=
  ⟨normalForm_usesBelow hB hk F hw, primitive_usesBelow hB hk F hw,
    normalForm_totalDegree_le hB hk F d hd, primitive_totalDegree_le hB hk F d hd⟩

end

end PrimeGapNormality.Prime.CoreCyclic
