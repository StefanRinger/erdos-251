import PrimeGapNormality.Prime.CoreExecutableNormalForm

namespace PrimeGapNormality.Prime.CoreCyclic

open scoped BigOperators

/-- Canonical reduction is constant on each actual telescope class. -/
theorem normalForm_eq_of_telescope_representative {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (F G H : PeriodicLocal k)
    (hFG : F = G + cyclicTelescope B hk H) :
    normalForm hB hk F = normalForm hB hk G := by
  rw [hFG, normalForm_add, normalForm_telescope, add_zero]

/-- The canonical representative satisfies every degree bound satisfied by
any representative in its class. This proves the paper's minimality sentence. -/
theorem normalForm_least_degree_bound {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (F G H : PeriodicLocal k)
    (hFG : F = G + cyclicTelescope B hk H) (d : ℕ)
    (hG : ∀ r, (G r).totalDegree ≤ d) :
    ∀ r, (normalForm hB hk F r).totalDegree ≤ d := by
  rw [normalForm_eq_of_telescope_representative hB hk F G H hFG]
  exact normalForm_totalDegree_le hB hk G d hG

/-- Maximum component degree, using the natural-degree convention for zero. -/
noncomputable def tupleNatDegree {k : ℕ} (F : PeriodicLocal k) : ℕ :=
  Finset.univ.sup fun r => (F r).totalDegree

/-- A literal maximum-degree comparison against every representative. -/
theorem normalForm_tupleNatDegree_le {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (F G H : PeriodicLocal k)
    (hFG : F = G + cyclicTelescope B hk H) :
    tupleNatDegree (normalForm hB hk F) ≤ tupleNatDegree G := by
  apply Finset.sup_le
  intro r _
  exact normalForm_least_degree_bound hB hk F G H hFG _
    (fun r => Finset.le_sup (f := fun r => (G r).totalDegree) (Finset.mem_univ r)) r

/-- For a nonzero class all representatives are nonzero; thus the comparison
above agrees with the paper's convention `deg 0 = -∞`. -/
theorem representative_ne_zero_of_normalForm_ne_zero {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (F G H : PeriodicLocal k)
    (hFG : F = G + cyclicTelescope B hk H) (hF : normalForm hB hk F ≠ 0) :
    G ≠ 0 := by
  intro hG
  apply hF
  rw [normalForm_eq_of_telescope_representative hB hk F G H hFG, hG,
    normalForm_zero]

/-- The canonical representative both belongs to the class and attains its
least degree among all representatives, for every nonzero class. -/
theorem normalForm_attains_least_degree {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (F : PeriodicLocal k)
    (hF : normalForm hB hk F ≠ 0) :
    (∃ H, F = normalForm hB hk F + cyclicTelescope B hk H) ∧
      ∀ G H, F = G + cyclicTelescope B hk H →
        G ≠ 0 ∧ tupleNatDegree (normalForm hB hk F) ≤ tupleNatDegree G := by
  refine ⟨⟨primitive hB hk F, decomposition hB hk F⟩, ?_⟩
  intro G H hFG
  exact ⟨representative_ne_zero_of_normalForm_ne_zero hB hk F G H hFG hF,
    normalForm_tupleNatDegree_le hB hk F G H hFG⟩

end PrimeGapNormality.Prime.CoreCyclic
