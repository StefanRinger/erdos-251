import PrimeGapNormality.Prime.CorePrimeFirstL
import PrimeGapNormality.Prime.SubsetSpacing
import PrimeGapNormality.Prime.CoreSequenceResiduePassage

/-! Exact finite pattern geometry for an arbitrary increasing integer
sequence. Membership is membership in the actual range of the sequence;
no random model, density or distribution assumption is used. -/

namespace PrimeGapNormality.Prime.CoreSequencePattern

open Finset
noncomputable section
open scoped Classical

def offset (a : ℕ → ℕ) (n j : ℕ) : ℕ := a (n + j + 1) - a n
def prefixSet (a : ℕ → ℕ) (n L : ℕ) : Finset ℕ := (range L).image (offset a n)
def pattern (a : ℕ → ℕ) (Ω : Finset ℕ) (v : ℕ) : Finset ℕ :=
  Ω.filter (fun h => ∃ i, a i = v + h)

theorem offset_pos {a : ℕ → ℕ} (ha : StrictMono a) (n j : ℕ) : 0 < offset a n j :=
  Nat.sub_pos_of_lt (ha (by omega))

theorem offset_add {a : ℕ → ℕ} (ha : StrictMono a) (n j : ℕ) :
    a n + offset a n j = a (n + j + 1) :=
  Nat.add_sub_of_le (ha.monotone (by omega))

theorem offset_strictMono {a : ℕ → ℕ} (ha : StrictMono a) (n : ℕ) :
    StrictMono (offset a n) := by
  intro i j hij
  have hi := offset_add ha n i
  have hj := offset_add ha n j
  have hh := ha (show n + i + 1 < n + j + 1 by omega)
  omega

theorem prefixSet_card {a : ℕ → ℕ} (ha : StrictMono a) (n L : ℕ) :
    (prefixSet a n L).card = L := by
  unfold prefixSet
  rw [card_image_of_injective _ (offset_strictMono ha n).injective, card_range]

theorem mem_prefixSet_iff {a : ℕ → ℕ} (ha : StrictMono a) (n L x : ℕ) :
    x ∈ prefixSet a n L ↔
      0 < x ∧ (∃ t, a t = a n + x) ∧ a n + x ≤ a (n + L) := by
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    have hjL := mem_range.mp hj
    refine ⟨offset_pos ha n j, ⟨n + j + 1, (offset_add ha n j).symm⟩, ?_⟩
    rw [offset_add ha]
    exact ha.monotone (by omega)
  · rintro ⟨hx, ⟨t, ht⟩, hlast⟩
    have hnt : n < t := ha.lt_iff_lt.mp (by omega)
    have htlast : t ≤ n + L := ha.le_iff_le.mp (by omega)
    have hj : t - n - 1 < L := by omega
    have hidx : n + (t - n - 1) + 1 = t := by omega
    refine mem_image.mpr ⟨t - n - 1, mem_range.mpr hj, ?_⟩
    unfold offset
    rw [hidx, ht, Nat.add_sub_cancel_left]

theorem prefixSet_max {a : ℕ → ℕ} (ha : StrictMono a) {n L : ℕ}
    (hL : 1 ≤ L) (hne : (prefixSet a n L).Nonempty) :
    (prefixSet a n L).max' hne = a (n + L) - a n := by
  apply le_antisymm
  · apply max'_le
    intro x hx
    have hm := (mem_prefixSet_iff ha n L x).mp hx
    omega
  · apply le_max'
    apply (mem_prefixSet_iff ha n L _).mpr
    have hp : a n < a (n + L) := ha (by omega)
    have heq : a n + (a (n + L) - a n) = a (n + L) := Nat.add_sub_of_le hp.le
    exact ⟨Nat.sub_pos_of_lt hp, ⟨n + L, heq.symm⟩, heq.le⟩

theorem prefixSet_subset_pattern {a : ℕ → ℕ} (ha : StrictMono a) {n L S : ℕ}
    (hspan : a (n + L) - a n ≤ S) :
    prefixSet a n L ⊆ pattern a (Icc 1 S) (a n) := by
  intro x hx
  have hm := (mem_prefixSet_iff ha n L x).mp hx
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hm.1, by omega⟩, hm.2.1⟩

theorem pattern_card_ge_iff_span {a : ℕ → ℕ} (ha : StrictMono a)
    {n L S : ℕ} (hL : 1 ≤ L) :
    L ≤ (pattern a (Icc 1 S) (a n)).card ↔ a (n + L) - a n ≤ S := by
  constructor
  · intro hcard
    by_contra hn
    have hsub : pattern a (Icc 1 S) (a n) ⊆ prefixSet a n (L - 1) := by
      intro x hx
      have hx' := mem_filter.mp hx
      have hxr := mem_Icc.mp hx'.1
      obtain ⟨t, ht⟩ := hx'.2
      have htlast : t < n + L := ha.lt_iff_lt.mp (by omega)
      apply (mem_prefixSet_iff ha n (L - 1) x).mpr
      refine ⟨hxr.1, ⟨t, ht⟩, ?_⟩
      rw [← ht]
      exact ha.monotone (by omega)
    have hsmall := card_le_card hsub
    rw [prefixSet_card ha] at hsmall
    omega
  · intro hspan
    have hh := card_le_card (prefixSet_subset_pattern ha hspan)
    rwa [prefixSet_card ha] at hh

theorem pattern_firstL_eq_prefixSet {a : ℕ → ℕ} (ha : StrictMono a)
    {n L S : ℕ} (hL : 1 ≤ L) (hspan : a (n + L) - a n ≤ S) :
    Stopped.firstL L (pattern a (Icc 1 S) (a n)) = prefixSet a n L := by
  have hne : (prefixSet a n L).Nonempty := by
    apply card_pos.mp
    rw [prefixSet_card ha]
    omega
  apply (Stopped.firstL_eq_iff hne hL ((pattern_card_ge_iff_span ha hL).mpr hspan)).mpr
  refine ⟨prefixSet_subset_pattern ha hspan, prefixSet_card ha n L, ?_⟩
  intro x hx hxlast
  have hx' := mem_filter.mp hx
  rw [prefixSet_max ha hL hne] at hxlast
  exact (mem_prefixSet_iff ha n L x).mpr
    ⟨(mem_Icc.mp hx'.1).1, hx'.2, by omega⟩

theorem prefixSet_sort {a : ℕ → ℕ} (ha : StrictMono a) (n L : ℕ) :
    (prefixSet a n L).sort (· ≤ ·) = (List.range L).map (offset a n) := by
  let emb : ℕ ↪ ℕ := ⟨offset a n, (offset_strictMono ha n).injective⟩
  have hh := Finset.map_sort emb (range L) (· ≤ ·) (· ≤ ·)
    (fun i _ j _ => (offset_strictMono ha n).le_iff_le.symm)
  rw [sort_range, map_eq_image] at hh
  exact hh.symm

theorem prefixSet_orderStat {a : ℕ → ℕ} (ha : StrictMono a)
    (n L j : ℕ) (hj : j ≤ L) :
    orderStat (prefixSet a n L) j = a (n + j) - a n := by
  by_cases hz : j = 0
  · subst j
    simp [orderStat_zero]
  · have hp : 0 < j := Nat.pos_of_ne_zero hz
    have hc : j ≤ (prefixSet a n L).card := by rwa [prefixSet_card ha]
    rw [orderStat_pos_eq_sort hp hc]
    simp only [prefixSet_sort ha, List.getElem_map, List.getElem_range, offset]
    congr 2
    omega

theorem prefixSet_gap {a : ℕ → ℕ} (ha : StrictMono a) (n L j : ℕ) (hj : j < L) :
    subsetGap (prefixSet a n L) j = a (n + j + 1) - a (n + j) := by
  unfold subsetGap
  rw [prefixSet_orderStat ha n L (j + 1) (by omega), prefixSet_orderStat ha n L j hj.le]
  have h0 := ha.monotone (show n ≤ n + j by omega)
  have h1 := ha.monotone (show n + j ≤ n + (j + 1) by omega)
  have heq : n + (j + 1) = n + j + 1 := by omega
  rw [heq] at *
  omega

end
end PrimeGapNormality.Prime.CoreSequencePattern
