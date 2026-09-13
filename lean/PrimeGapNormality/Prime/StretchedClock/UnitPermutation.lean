import PrimeGapNormality.Prime.StretchedClock.UnitIntervals

/-! Multiplication by a unit permutes the actual coprime natural residues.
The result applies to every set of target residues, including intervals. -/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset
open scoped Classical
noncomputable section

def unitResidues (a : ℕ) : Finset ℕ :=
  (range a).filter fun b => a.Coprime b

theorem mem_unitResidues {a b : ℕ} :
    b ∈ unitResidues a ↔ b < a ∧ a.Coprime b := by
  simp only [unitResidues, mem_filter, mem_range]

theorem unitResidues_card (a : ℕ) : (unitResidues a).card = a.totient := rfl

theorem mul_mod_injOn_range {a v : ℕ} (hv : v.Coprime a) :
    Set.InjOn (fun b => (v * b) % a) (range a : Set ℕ) := by
  intro b hb c hc hbc
  have hcast : (v : ZMod a) * (b : ZMod a) = (v : ZMod a) * (c : ZMod a) := by
    simpa only [Nat.cast_mul] using
      (ZMod.natCast_eq_natCast_iff' (v * b) (v * c) a).mpr hbc
  have hcancel := ((ZMod.isUnit_iff_coprime v a).mpr hv).mul_left_cancel hcast
  have hmod := (ZMod.natCast_eq_natCast_iff' b c a).mp hcancel
  simpa only [Nat.mod_eq_of_lt (mem_range.mp hb),
    Nat.mod_eq_of_lt (mem_range.mp hc)] using hmod

theorem mul_mod_mem_unitResidues {a v b : ℕ} (ha : 0 < a)
    (hv : v.Coprime a) (hb : b ∈ unitResidues a) :
    (v * b) % a ∈ unitResidues a := by
  apply mem_unitResidues.mpr
  refine ⟨Nat.mod_lt _ ha, ?_⟩
  apply Nat.Coprime.symm
  apply (ZMod.coprime_mod_iff_coprime _ _).mpr
  exact hv.mul_left (mem_unitResidues.mp hb).2.symm

/-- No equidistribution assumption: this is an exact finite permutation. -/
theorem unitResidues_image_mul_mod {a v : ℕ} (ha : 0 < a) (hv : v.Coprime a) :
    (unitResidues a).image (fun b => (v * b) % a) = unitResidues a := by
  have hsub : (unitResidues a).image (fun b => (v * b) % a) ⊆ unitResidues a := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hb
    exact mul_mod_mem_unitResidues ha hv hc
  have hinj : Set.InjOn (fun b => (v * b) % a) (unitResidues a : Set ℕ) :=
    (mul_mod_injOn_range hv).mono (filter_subset _ _)
  have hcard : ((unitResidues a).image (fun b => (v * b) % a)).card =
      (unitResidues a).card := card_image_of_injOn hinj
  apply eq_of_subset_of_card_le hsub
  rw [hcard]

/-- The count in any target residue set is unchanged by a unit multiplier. -/
theorem unitResidues_filter_mul_mod_card {a v : ℕ} (ha : 0 < a)
    (hv : v.Coprime a) (J : Set ℕ) :
    ((unitResidues a).filter fun b => (v * b) % a ∈ J).card =
      ((unitResidues a).filter fun b => b ∈ J).card := by
  apply card_bij (fun b _ => (v * b) % a)
  · intro b hb
    exact mem_filter.mpr ⟨mul_mod_mem_unitResidues ha hv (mem_filter.mp hb).1,
      (mem_filter.mp hb).2⟩
  · intro b hb c hc hbc
    exact mul_mod_injOn_range hv (filter_subset _ _ (mem_filter.mp hb).1)
      (filter_subset _ _ (mem_filter.mp hc).1) hbc
  · intro c hc
    have himg : c ∈ (unitResidues a).image (fun b => (v * b) % a) := by
      rw [unitResidues_image_mul_mod ha hv]
      exact (mem_filter.mp hc).1
    obtain ⟨b, hb, hbc⟩ := mem_image.mp himg
    refine ⟨b, mem_filter.mpr ⟨hb, ?_⟩, hbc⟩
    rw [hbc]
    exact (mem_filter.mp hc).2

end
end PrimeGapNormality.Prime.StretchedClock
