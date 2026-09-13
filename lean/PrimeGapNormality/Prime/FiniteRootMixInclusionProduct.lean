import PrimeGapNormality.Prime.CrtHLMismatchVanishing
import PrimeGapNormality.Prime.PresieveSmallGlobalLower
import PrimeGapNormality.Prime.ExactRootMix

/-!
# Exact rooting cancellation in the finite root mixture

Multiplying a rooted inclusion probability by `V(y)` cancels the
conditioning on the origin.  The resulting product is the ordinary
finite tuple sieve product for `insert 0 H`.  This identity includes
covering local factors, where both sides vanish.
-/

open Finset
open scoped Classical

namespace PrimeGapNormality.Prime

noncomputable section

private def rootTupleAllowed (p : ℕ) (H : Finset ℕ) : Finset (Fin (p - 1)) :=
  univ.filter fun a => ∀ h ∈ H, h % p ≠ a.val + 1

private theorem rootTupleAllowed_card {p : ℕ} (hp : Nat.Prime p) (H : Finset ℕ) :
    (rootTupleAllowed p H).card = p - residueCount (insert 0 H) p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let E := (insert 0 H).image fun h : ℕ => (h : ZMod p)
  have hlt : ∀ a : Fin (p - 1), a.val + 1 < p := by
    intro a
    have := a.isLt
    omega
  have hcard : (rootTupleAllowed p H).card = ((univ : Finset (ZMod p)) \ E).card := by
    refine card_bij (fun a _ => ((a.val + 1 : ℕ) : ZMod p)) ?_ ?_ ?_
    · intro a ha
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      intro hz
      obtain ⟨h, hh, heq⟩ := mem_image.mp hz
      have hval := congrArg (fun z : ZMod p => z.val) heq
      rw [ZMod.val_natCast, ZMod.val_natCast_of_lt (hlt a)] at hval
      rcases mem_insert.mp hh with rfl | hh
      · simp only [Nat.zero_mod] at hval
        omega
      · exact (mem_filter.mp ha).2 h hh hval
    · intro a ha b hb heq
      have hval := congrArg (fun z : ZMod p => z.val) heq
      rw [ZMod.val_natCast_of_lt (hlt a), ZMod.val_natCast_of_lt (hlt b)] at hval
      apply Fin.ext
      omega
    · intro z hz
      have hzE := (mem_sdiff.mp hz).2
      have hz0 : z ≠ 0 := by
        intro hzero
        apply hzE
        exact mem_image.mpr ⟨0, mem_insert_self _ _, by simpa using hzero.symm⟩
      have hzpos : 0 < z.val := Nat.pos_of_ne_zero ((ZMod.val_eq_zero z).not.mpr hz0)
      have hzlt : z.val < p := ZMod.val_lt z
      let a : Fin (p - 1) := ⟨z.val - 1, by omega⟩
      have haeq : a.val + 1 = z.val := by dsimp only [a]; omega
      refine ⟨a, ?_, ?_⟩
      · refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        intro h hh hmod
        apply hzE
        refine mem_image.mpr ⟨h, mem_insert_of_mem hh, ?_⟩
        apply ZMod.val_injective p
        rw [ZMod.val_natCast, hmod, haeq]
      · rw [haeq, ZMod.natCast_zmod_val]
  rw [hcard, card_sdiff_of_subset (subset_univ E), card_univ, ZMod.card]
  rfl

/-- Finite unrooted tuple sieve product. -/
def finiteTupleSieveProduct (E : Finset ℕ) (y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y, (1 - (residueCount E p : ℝ) / p)

private theorem rootTupleAllowed_factor {p : ℕ} (hp : Nat.Prime p) (H : Finset ℕ) :
    (1 - (p : ℝ)⁻¹) *
        ((rootTupleAllowed p H).card : ℝ) / (p - 1 : ℕ) =
      1 - (residueCount (insert 0 H) p : ℝ) / p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hres : residueCount (insert 0 H) p ≤ p := by
    unfold residueCount
    simpa only [ZMod.card] using card_le_univ ((insert 0 H).image fun h : ℕ => (h : ZMod p))
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
    linarith
  rw [rootTupleAllowed_card hp, Nat.cast_sub hres, Nat.cast_sub hp.one_le, Nat.cast_one]
  field_simp [hp0, hp1] <;> ring

private theorem rootTuple_survival_iff {y S : ℕ} {H : Finset ℕ}
    (hH : H ⊆ offsetWindow S) (σ : ResidueChoice y) :
    H ⊆ sieveSurvivorsFin y σ S ↔
      ∀ p : SievePrime y, σ p ∈ rootTupleAllowed p.val H := by
  constructor
  · intro h p
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    intro n hn
    have hsurv := (mem_filter.mp (h hn)).2
    have hearly := (earlyPresieveSurvives_iff_sieveSurvives y σ n).mpr hsurv
    exact hearly p
  · intro h n hn
    refine mem_filter.mpr ⟨hH hn, ?_⟩
    apply (earlyPresieveSurvives_iff_sieveSurvives y σ n).mp
    intro p
    exact (mem_filter.mp (h p)).2 n hn

/-- Exact cancellation of the root-density conditioning.  The only
restriction on `H` is its actual finite search window. -/
theorem eulerProd_mul_actualRootLaw_inclusionMass
    (y S : ℕ) {H : Finset ℕ} (hH : H ⊆ offsetWindow S) :
    eulerProdNat y * Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) H =
      finiteTupleSieveProduct (insert 0 H) y := by
  have hfilter :
      (univ : Finset (ResidueChoice y)).filter (fun σ => H ⊆ sieveSurvivorsFin y σ S) =
        Fintype.piFinset (fun p : SievePrime y => rootTupleAllowed p.val H) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset,
      rootTuple_survival_iff hH]
  rw [crtHL_inclusionMass_eq_survivalProb, hfilter,
    Fintype.card_piFinset, Fintype.card_pi, Nat.cast_prod, Nat.cast_prod]
  simp only [Fintype.card_fin]
  have hV : eulerProdNat y = ∏ p : SievePrime y, (1 - (p.val : ℝ)⁻¹) :=
    (Finset.prod_coe_sort (Nat.primesLE y) (fun p : ℕ => 1 - (p : ℝ)⁻¹)).symm
  rw [hV, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  have hpoint : ∀ p : SievePrime y,
      (1 - (p.val : ℝ)⁻¹) *
          (((rootTupleAllowed p.val H).card : ℝ) / (p.val - 1 : ℕ)) =
        1 - (residueCount (insert 0 H) p.val : ℝ) / p.val := by
    intro p
    simpa only [mul_div_assoc] using
      rootTupleAllowed_factor (Nat.prime_of_mem_primesLE p.property) H
  simp_rw [hpoint]
  exact Finset.prod_coe_sort (Nat.primesLE y)
    (fun p : ℕ => 1 - (residueCount (insert 0 H) p : ℝ) / p)

/-- The unnormalized finite mixture is exactly the integer-scale
average of unrooted tuple sieve products, divided by the prime root count. -/
theorem finiteRootMixUnnorm_inclusionMass_eq_product_sum
    (X S : ℕ) {H : Finset ℕ} (hH : H ⊆ offsetWindow S) :
    Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H =
      (∑ t ∈ mixScale X, finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) /
        (windowNX X : ℝ) := by
  have hlinear : Stopped.inclusionMass (offsetWindow S) (finiteRootMixUnnorm X S) H =
      (∑ t ∈ mixScale X, mixWeightV t *
        Stopped.inclusionMass (offsetWindow S) (actualRootLaw (sieveCutoff (t : ℝ)) S) H) /
        (windowNX X : ℝ) := by
    unfold Stopped.inclusionMass finiteRootMixUnnorm
    rw [← sum_div, sum_comm]
    simp only [mul_sum]
  rw [hlinear]
  congr 1
  apply sum_congr rfl
  intro t _
  exact eulerProd_mul_actualRootLaw_inclusionMass (sieveCutoff (t : ℝ)) S hH

theorem finiteRootMix_inclusionMass_eq_product_sum
    (X S : ℕ) {H : Finset ℕ} (hH : H ⊆ offsetWindow S) :
    Stopped.inclusionMass (offsetWindow S) (finiteRootMix X S) H =
      (∑ t ∈ mixScale X, finiteTupleSieveProduct (insert 0 H) (sieveCutoff (t : ℝ))) /
        mixZ X := by
  have hlinear : Stopped.inclusionMass (offsetWindow S) (finiteRootMix X S) H =
      (∑ t ∈ mixScale X, mixWeightV t *
        Stopped.inclusionMass (offsetWindow S) (actualRootLaw (sieveCutoff (t : ℝ)) S) H) /
        mixZ X := by
    unfold Stopped.inclusionMass finiteRootMix
    rw [← sum_div, sum_comm]
    simp only [mul_sum]
  rw [hlinear]
  congr 1
  apply sum_congr rfl
  intro t _
  exact eulerProd_mul_actualRootLaw_inclusionMass (sieveCutoff (t : ℝ)) S hH

end

end PrimeGapNormality.Prime
