import PrimeGapNormality.Prime.CoreActualPattern
import PrimeGapNormality.Prime.PrimeSeries
import PrimeGapNormality.Prime.PrimeIndex

/-! Exact identification of the stopped finite prime configuration with the
first consecutive prime offsets. No distribution or matching hypothesis. -/

open Finset

namespace PrimeGapNormality.Prime

noncomputable def corePrimeOffset (n j : ℕ) : ℕ := nthPrime (n + j + 1) - nthPrime n

noncomputable def corePrimePrefix (n L : ℕ) : Finset ℕ :=
  (range L).image (corePrimeOffset n)

theorem corePrimeOffset_pos (n j : ℕ) : 0 < corePrimeOffset n j := by
  unfold corePrimeOffset
  exact Nat.sub_pos_of_lt (nthPrime_strictMono (by omega))

theorem corePrimeOffset_add (n j : ℕ) :
    nthPrime n + corePrimeOffset n j = nthPrime (n + j + 1) := by
  unfold corePrimeOffset
  exact Nat.add_sub_of_le (nthPrime_mono (by omega))

theorem corePrimeOffset_strictMono (n : ℕ) : StrictMono (corePrimeOffset n) := by
  intro i j hij
  have hi := corePrimeOffset_add n i
  have hj := corePrimeOffset_add n j
  have hp := nthPrime_strictMono (show n + i + 1 < n + j + 1 by omega)
  omega

theorem corePrimePrefix_card (n L : ℕ) : (corePrimePrefix n L).card = L := by
  unfold corePrimePrefix
  rw [card_image_of_injective _ (corePrimeOffset_strictMono n).injective, card_range]

theorem corePrimePrefix_mem_iff (n L x : ℕ) :
    x ∈ corePrimePrefix n L ↔
      0 < x ∧ Nat.Prime (nthPrime n + x) ∧ nthPrime n + x ≤ nthPrime (n + L) := by
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    have hjL := mem_range.mp hj
    refine ⟨corePrimeOffset_pos n j, ?_, ?_⟩
    · rw [corePrimeOffset_add]
      exact prime_nthPrime _
    · rw [corePrimeOffset_add]
      exact nthPrime_mono (by omega)
  · rintro ⟨hx, hp, hlast⟩
    obtain ⟨t, _, ht⟩ := Nat.exists_lt_card_nth_eq hp
    change nthPrime t = nthPrime n + x at ht
    have hnt : n < t := nthPrime_strictMono.lt_iff_lt.mp (by omega)
    have htlast : t ≤ n + L := nthPrime_strictMono.le_iff_le.mp (by omega)
    have hj : t - n - 1 < L := by omega
    have hidx : n + (t - n - 1) + 1 = t := by omega
    apply mem_image.mpr
    refine ⟨t - n - 1, mem_range.mpr hj, ?_⟩
    unfold corePrimeOffset
    rw [hidx, ht, Nat.add_sub_cancel_left]

theorem corePrimePrefix_max {n L : ℕ} (hL : 1 ≤ L)
    (hne : (corePrimePrefix n L).Nonempty) :
    (corePrimePrefix n L).max' hne = nthPrime (n + L) - nthPrime n := by
  apply le_antisymm
  · apply max'_le
    intro x hx
    have hm := (corePrimePrefix_mem_iff n L x).mp hx
    omega
  · apply le_max'
    apply (corePrimePrefix_mem_iff n L _).mpr
    have hp : nthPrime n < nthPrime (n + L) := nthPrime_strictMono (by omega)
    have heq : nthPrime n + (nthPrime (n + L) - nthPrime n) = nthPrime (n + L) :=
      Nat.add_sub_of_le hp.le
    refine ⟨Nat.sub_pos_of_lt hp, ?_, ?_⟩
    · rw [heq]; exact prime_nthPrime _
    · rw [heq]

theorem corePrimePrefix_subset_actual {n L S : ℕ}
    (hspan : nthPrime (n + L) - nthPrime n ≤ S) :
    corePrimePrefix n L ⊆ coreActualPattern (Icc 1 S) (nthPrime n) := by
  intro x hx
  have hm := (corePrimePrefix_mem_iff n L x).mp hx
  apply mem_filter.mpr
  exact ⟨mem_Icc.mpr ⟨hm.1, by omega⟩, hm.2.1⟩

theorem coreActualPattern_card_ge_iff_span {n L S : ℕ} (hL : 1 ≤ L) :
    L ≤ (coreActualPattern (Icc 1 S) (nthPrime n)).card ↔
      nthPrime (n + L) - nthPrime n ≤ S := by
  constructor
  · intro hcard
    by_contra hn
    have hsub : coreActualPattern (Icc 1 S) (nthPrime n) ⊆ corePrimePrefix n (L - 1) := by
      intro x hx
      have hx' := mem_filter.mp hx
      have hxr := mem_Icc.mp hx'.1
      obtain ⟨t, _, ht⟩ := Nat.exists_lt_card_nth_eq hx'.2
      change nthPrime t = nthPrime n + x at ht
      have htlast : t < n + L := nthPrime_strictMono.lt_iff_lt.mp (by omega)
      apply (corePrimePrefix_mem_iff n (L - 1) x).mpr
      refine ⟨hxr.1, hx'.2, ?_⟩
      rw [← ht]
      exact nthPrime_mono (by omega)
    have hsmall := card_le_card hsub
    rw [corePrimePrefix_card] at hsmall
    omega
  · intro hspan
    have h := card_le_card (corePrimePrefix_subset_actual hspan)
    rwa [corePrimePrefix_card] at h

theorem coreActualPattern_firstL_eq_prefix {n L S : ℕ} (hL : 1 ≤ L)
    (hspan : nthPrime (n + L) - nthPrime n ≤ S) :
    Stopped.firstL L (coreActualPattern (Icc 1 S) (nthPrime n)) = corePrimePrefix n L := by
  have hne : (corePrimePrefix n L).Nonempty := by
    apply card_pos.mp
    rw [corePrimePrefix_card]
    omega
  apply (Stopped.firstL_eq_iff hne hL
    ((coreActualPattern_card_ge_iff_span hL).mpr hspan)).mpr
  refine ⟨corePrimePrefix_subset_actual hspan, corePrimePrefix_card n L, ?_⟩
  intro x hx hxlast
  have hx' := mem_filter.mp hx
  rw [corePrimePrefix_max hL hne] at hxlast
  exact (corePrimePrefix_mem_iff n L x).mpr
    ⟨(mem_Icc.mp hx'.1).1, hx'.2, by omega⟩

end PrimeGapNormality.Prime
