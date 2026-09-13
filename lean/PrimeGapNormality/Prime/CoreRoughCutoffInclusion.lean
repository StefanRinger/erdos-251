import PrimeGapNormality.Prime.FiniteRootMixInclusionProduct
import PrimeGapNormality.Prime.StoppedPrime

/-!
# Exact rooted inclusion scaling between nested rough cutoffs

When the configuration window lies strictly below the old cutoff, every
new prime sees the points of a fixed `j`-set as `j` distinct nonzero
residues.  The rooted inclusion probability therefore changes by the exact
shape-independent factor

`prod_{z < p <= y} (1 - j/(p-1))`.

The proof below derives this from the actual finite residue law, via the
compiled unrooted-product identity.  It includes local covering/zero cases;
no Bernoulli or independence model is substituted for `actualRootLaw`.
-/

namespace PrimeGapNormality.Prime.CoreRoughCutoffInclusion

open Finset
open scoped BigOperators Classical

noncomputable section

/-- The exact rooted survival factor for a fixed `j`-set through the primes
newly added between `z` and `y`. -/
def cutoffInclusionFactor (z y j : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
    (1 - (j : ℝ) / ((p - 1 : ℕ) : ℝ))

private theorem newPrime_gt {z y p : ℕ}
    (hp : p ∈ Nat.primesLE y \ Nat.primesLE z) : z < p := by
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have hpNot : p ∉ Nat.primesLE z := (mem_sdiff.mp hp).2
  exact Nat.lt_of_not_ge fun hpz =>
    hpNot (Nat.mem_primesLE.mpr ⟨hpz, hpPrime⟩)

private theorem zero_not_mem_of_subset_offsetWindow
    {S : ℕ} {H : Finset ℕ} (hH : H ⊆ offsetWindow S) : 0 ∉ H := by
  intro h0
  have hmem := mem_Icc.mp (hH h0)
  omega

/-- Above the whole window, `insert 0 H` occupies exactly `card H + 1`
residue classes. -/
theorem residueCount_insert_zero_eq_card_add_one
    {S z y p : ℕ} {H : Finset ℕ} (hSz : S < z)
    (hH : H ⊆ offsetWindow S)
    (hp : p ∈ Nat.primesLE y \ Nat.primesLE z) :
    residueCount (insert 0 H) p = H.card + 1 := by
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have hzp : z < p := newPrime_gt hp
  have hlt : ∀ n ∈ insert 0 H, n < p := by
    intro n hn
    rcases mem_insert.mp hn with rfl | hnH
    · exact hpPrime.pos
    · have hnS : n ≤ S := (mem_Icc.mp (hH hnH)).2
      omega
  calc
    residueCount (insert 0 H) p = (insert 0 H).card :=
      by
        unfold residueCount
        apply card_image_of_injOn
        intro a ha b hb hab
        have hmod := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
        rwa [Nat.mod_eq_of_lt (hlt a ha), Nat.mod_eq_of_lt (hlt b hb)] at hmod
    _ = H.card + 1 := by
      rw [card_insert_of_notMem (zero_not_mem_of_subset_offsetWindow hH)]

/-- Each new unrooted local factor is the root factor times the exact
`j`-point rooted survival factor. -/
theorem newPrime_localFactor
    {S z y p : ℕ} {H : Finset ℕ} (hSz : S < z)
    (hH : H ⊆ offsetWindow S)
    (hp : p ∈ Nat.primesLE y \ Nat.primesLE z) :
    1 - (residueCount (insert 0 H) p : ℝ) / p =
      (1 - (p : ℝ)⁻¹) *
        (1 - (H.card : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
  have hpPrime : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpPrime.ne_zero
  have hpPred0 : (p : ℝ) - 1 ≠ 0 := by
    have hpOne : (1 : ℝ) < p := Nat.one_lt_cast.mpr hpPrime.one_lt
    linarith
  rw [residueCount_insert_zero_eq_card_add_one hSz hH hp,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hpPrime.one_le, Nat.cast_one]
  field_simp [hp0, hpPred0] <;> ring

private theorem finiteTupleSieveProduct_split
    (E : Finset ℕ) {z y : ℕ} (hzy : z ≤ y) :
    finiteTupleSieveProduct E y =
      finiteTupleSieveProduct E z *
        ∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
          (1 - (residueCount E p : ℝ) / p) := by
  have hsub : Nat.primesLE z ⊆ Nat.primesLE y := Nat.primesLE_mono hzy
  unfold finiteTupleSieveProduct
  calc
    (∏ p ∈ Nat.primesLE y, (1 - (residueCount E p : ℝ) / p)) =
        (∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
          (1 - (residueCount E p : ℝ) / p)) *
        ∏ p ∈ Nat.primesLE z, (1 - (residueCount E p : ℝ) / p) :=
      (Finset.prod_sdiff hsub).symm
    _ = (∏ p ∈ Nat.primesLE z, (1 - (residueCount E p : ℝ) / p)) *
        ∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
          (1 - (residueCount E p : ℝ) / p) := mul_comm _ _

private theorem eulerProdNat_split {z y : ℕ} (hzy : z ≤ y) :
    eulerProdNat y = eulerProdNat z *
      ∏ p ∈ Nat.primesLE y \ Nat.primesLE z, (1 - (p : ℝ)⁻¹) := by
  have hsub : Nat.primesLE z ⊆ Nat.primesLE y := Nat.primesLE_mono hzy
  unfold eulerProdNat
  calc
    (∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)) =
        (∏ p ∈ Nat.primesLE y \ Nat.primesLE z, (1 - (p : ℝ)⁻¹)) *
          ∏ p ∈ Nat.primesLE z, (1 - (p : ℝ)⁻¹) :=
      (Finset.prod_sdiff hsub).symm
    _ = (∏ p ∈ Nat.primesLE z, (1 - (p : ℝ)⁻¹)) *
        ∏ p ∈ Nat.primesLE y \ Nat.primesLE z, (1 - (p : ℝ)⁻¹) :=
      mul_comm _ _

private theorem newPrime_product_factorization
    {S z y : ℕ} {H : Finset ℕ} (hSz : S < z)
    (hH : H ⊆ offsetWindow S) :
    (∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
        (1 - (residueCount (insert 0 H) p : ℝ) / p)) =
      (∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
          (1 - (p : ℝ)⁻¹)) *
        cutoffInclusionFactor z y H.card := by
  calc
    (∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
        (1 - (residueCount (insert 0 H) p : ℝ) / p)) =
      ∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
        ((1 - (p : ℝ)⁻¹) *
          (1 - (H.card : ℝ) / ((p - 1 : ℕ) : ℝ))) := by
            apply prod_congr rfl
            intro p hp
            exact newPrime_localFactor hSz hH hp
    _ = (∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
          (1 - (p : ℝ)⁻¹)) *
        cutoffInclusionFactor z y H.card := by
          rw [cutoffInclusionFactor, prod_mul_distrib]

/-- Exact cutoff scaling for one actual rooted-law inclusion mass.  There is
no nonvanishing premise on the old inclusion mass, so local-zero cases are
part of the identity. -/
theorem actualRootLaw_inclusionMass_cutoff
    {S z y : ℕ} {H : Finset ℕ} (hSz : S < z) (hzy : z ≤ y)
    (hH : H ⊆ offsetWindow S) :
    Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) H =
      Stopped.inclusionMass (offsetWindow S) (actualRootLaw z S) H *
        cutoffInclusionFactor z y H.card := by
  have hy := eulerProd_mul_actualRootLaw_inclusionMass y S hH
  have hz := eulerProd_mul_actualRootLaw_inclusionMass z S hH
  have htuple := finiteTupleSieveProduct_split (insert 0 H) hzy
  have hnew := newPrime_product_factorization (y := y) hSz hH
  have hV := eulerProdNat_split hzy
  have hmul :
      eulerProdNat y *
          Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) H =
        eulerProdNat y *
          (Stopped.inclusionMass (offsetWindow S) (actualRootLaw z S) H *
            cutoffInclusionFactor z y H.card) := by
    calc
      eulerProdNat y *
          Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) H =
          finiteTupleSieveProduct (insert 0 H) y := hy
      _ = finiteTupleSieveProduct (insert 0 H) z *
          (∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
            (1 - (residueCount (insert 0 H) p : ℝ) / p)) := htuple
      _ = finiteTupleSieveProduct (insert 0 H) z *
          ((∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
              (1 - (p : ℝ)⁻¹)) * cutoffInclusionFactor z y H.card) := by
            rw [hnew]
      _ = (eulerProdNat z *
            Stopped.inclusionMass (offsetWindow S) (actualRootLaw z S) H) *
          ((∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
              (1 - (p : ℝ)⁻¹)) * cutoffInclusionFactor z y H.card) := by
            rw [hz]
      _ = (eulerProdNat z *
            ∏ p ∈ Nat.primesLE y \ Nat.primesLE z,
              (1 - (p : ℝ)⁻¹)) *
          (Stopped.inclusionMass (offsetWindow S) (actualRootLaw z S) H *
            cutoffInclusionFactor z y H.card) := by ring
      _ = eulerProdNat y *
          (Stopped.inclusionMass (offsetWindow S) (actualRootLaw z S) H *
            cutoffInclusionFactor z y H.card) := by rw [hV]
  exact mul_left_cancel₀ (eulerProdNat_ne_zero y) hmul

/-- Because the factor only depends on `j`, the actual factorial counting
moment has the same exact cutoff scaling. -/
theorem actualRootLaw_countMoment_cutoff
    {S z y j : ℕ} (hSz : S < z) (hzy : z ≤ y) :
    Stopped.countMoment (offsetWindow S) (actualRootLaw y S) j =
      Stopped.countMoment (offsetWindow S) (actualRootLaw z S) j *
        cutoffInclusionFactor z y j := by
  rw [countMoment_eq_sum_inclusionMass, countMoment_eq_sum_inclusionMass]
  calc
    (∑ H ∈ (offsetWindow S).powerset.filter (fun H => H.card = j),
        Stopped.inclusionMass (offsetWindow S) (actualRootLaw y S) H) =
      ∑ H ∈ (offsetWindow S).powerset.filter (fun H => H.card = j),
        Stopped.inclusionMass (offsetWindow S) (actualRootLaw z S) H *
          cutoffInclusionFactor z y j := by
            apply sum_congr rfl
            intro H hH
            have hmem := mem_filter.mp hH
            rw [← hmem.2]
            exact actualRootLaw_inclusionMass_cutoff hSz hzy
              (mem_powerset.mp hmem.1)
    _ = (∑ H ∈ (offsetWindow S).powerset.filter (fun H => H.card = j),
          Stopped.inclusionMass (offsetWindow S) (actualRootLaw z S) H) *
        cutoffInclusionFactor z y j := by rw [sum_mul]

end
end PrimeGapNormality.Prime.CoreRoughCutoffInclusion
