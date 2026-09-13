import PrimeGapNormality.Prime.CorePrimeComparisonInput
import PrimeGapNormality.Prime.AhlSmallOfLarge

/-!
# Frozen small-window AHL versus the literal Janossy transform

The legacy generic Janossy/adverse reindexing theorem is private.  This file
reproves its finite core for the public `coreJanossyTransform`.  It keeps the
exact endpoint multiplicity `choose (j-1) (L-1)` and hence introduces no
growing combinatorial loss that would be incompatible with qualitative AHL.
-/

namespace PrimeGapNormality.Prime.CoreFrozenAHL

open Finset

noncomputable section

private theorem nonempty_of_card_ge {s : Finset ℕ} {n : ℕ}
    (hn : 1 ≤ n) (hns : n ≤ s.card) : s.Nonempty :=
  card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one (hn.trans hns))

private theorem max_eq_posPart (x : ℝ) : max x 0 = x⁺ := rfl

private def truncDs (Ω : Finset ℕ) (L r : ℕ) (K : Finset ℕ) :
    Finset (Finset ℕ) :=
  if hK : K.Nonempty then
    (Stopped.beforeOutside Ω K hK).powerset.filter (fun D ↦ D.card ≤ r - L)
  else ∅

private theorem truncDs_eq {Ω : Finset ℕ} {L r : ℕ} {K : Finset ℕ}
    (hK : K.Nonempty) :
    truncDs Ω L r K =
      (Stopped.beforeOutside Ω K hK).powerset.filter
        (fun D ↦ D.card ≤ r - L) := by
  simp [truncDs, hK]

private theorem pos_sum_le_sum_pos {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    max (∑ i ∈ s, f i) 0 ≤ ∑ i ∈ s, max (f i) 0 := by
  have h1 : ∑ i ∈ s, f i ≤ ∑ i ∈ s, max (f i) 0 :=
    sum_le_sum fun _ _ ↦ le_max_left _ _
  have h2 : 0 ≤ ∑ i ∈ s, max (f i) 0 :=
    sum_nonneg fun _ _ ↦ le_max_right _ _
  exact max_le h1 h2

private theorem disjoint_beforeOutside {Ω K : Finset ℕ} (hK : K.Nonempty) :
    Disjoint K (Stopped.beforeOutside Ω K hK) :=
  disjoint_left.mpr fun x hxK hxB ↦ (mem_filter.mp hxB).2.2 hxK

private theorem card_union_trunc {Ω K D : Finset ℕ} {L : ℕ}
    (hK : K.Nonempty) (hcard : K.card = L)
    (hD : D ⊆ Stopped.beforeOutside Ω K hK) :
    (K ∪ D).card = L + D.card := by
  have hdisj : Disjoint K D :=
    (disjoint_beforeOutside (Ω := Ω) hK).mono_right hD
  rw [card_union_of_disjoint hdisj, hcard]

private theorem trunc_pair_maps {Ω : Finset ℕ} {L r : ℕ} {K D : Finset ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r)
    (hKmem : K ∈ Ω.powerset.filter (fun K ↦ K.card = L))
    (hD : D ∈ truncDs Ω L r K) :
    K ∪ D ∈ Ω.powerset.filter (fun H ↦ L ≤ H.card ∧ H.card ≤ r) := by
  have hK' := mem_filter.mp hKmem
  have hKΩ : K ⊆ Ω := mem_powerset.mp hK'.1
  have hcard : K.card = L := hK'.2
  have hKne : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
  have hD' : D ∈ (Stopped.beforeOutside Ω K hKne).powerset.filter
      (fun D ↦ D.card ≤ r - L) := by
    simpa [truncDs, hKne] using hD
  have hDB : D ⊆ Stopped.beforeOutside Ω K hKne :=
    mem_powerset.mp (mem_filter.mp hD').1
  have hDΩ : D ⊆ Ω := hDB.trans (filter_subset _ _)
  have hcardD : D.card ≤ r - L := (mem_filter.mp hD').2
  have hunion : K ∪ D ⊆ Ω := union_subset hKΩ hDΩ
  have hcardU : (K ∪ D).card = L + D.card :=
    card_union_trunc hKne hcard hDB
  refine mem_filter.mpr ⟨mem_powerset.mpr hunion, ?_, ?_⟩
  · omega
  · omega

private theorem max_eq_iff_mem {K H : Finset ℕ} (hK : K.Nonempty)
    (hH : H.Nonempty) (hKH : K ⊆ H) :
    K.max' hK = H.max' hH ↔ H.max' hH ∈ K := by
  constructor
  · intro h
    rw [← h]
    exact max'_mem K hK
  · intro hz
    exact le_antisymm (max'_subset hK hKH) (le_max' K _ hz)

private theorem fiber_card_eq {Ω H : Finset ℕ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) (hHΩ : H ⊆ Ω) (hHne : H.Nonempty)
    (hLo : L ≤ H.card) (hHi : H.card ≤ r) :
    (((Ω.powerset.filter (fun K ↦ K.card = L)).sigma
        (fun K ↦ truncDs Ω L r K)).filter
      (fun p ↦ p.1 ∪ p.2 = H)).card =
        (H.card - 1).choose (L - 1) := by
  set z := H.max' hHne
  let s :=
    ((Ω.powerset.filter (fun K ↦ K.card = L)).sigma
      (fun K ↦ truncDs Ω L r K)).filter (fun p ↦ p.1 ∪ p.2 = H)
  let t := H.powerset.filter (fun K ↦ K.card = L ∧ z ∈ K)
  have hcardt : t.card = (H.card - 1).choose (L - 1) :=
    Stopped.endpoint_multiplicity hHne hL hLo
  refine Eq.trans ?_ hcardt
  refine Finset.card_nbij'
    (i := fun p : Σ _ : Finset ℕ, Finset ℕ ↦ p.1)
    (j := fun K : Finset ℕ ↦ (⟨K, H \ K⟩ : Σ _ : Finset ℕ, Finset ℕ))
    ?_ ?_ ?_ ?_
  · intro p hp
    have hp' := mem_filter.mp hp
    have hσ := mem_sigma.mp hp'.1
    have hK' := mem_filter.mp hσ.1
    have hcard : p.1.card = L := hK'.2
    have hKne : p.1.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
    have hD : p.2 ∈ truncDs Ω L r p.1 := hσ.2
    have hD' : p.2 ∈ (Stopped.beforeOutside Ω p.1 hKne).powerset.filter
        (fun D ↦ D.card ≤ r - L) := by
      simpa [truncDs, hKne] using hD
    have hDB : p.2 ⊆ Stopped.beforeOutside Ω p.1 hKne :=
      mem_powerset.mp (mem_filter.mp hD').1
    have hEq : p.1 ∪ p.2 = H := hp'.2
    have hKsub : p.1 ⊆ H := by rw [← hEq]; exact subset_union_left
    have hmax : p.1.max' hKne = z := by
      have hHmax : ∀ x ∈ p.2, x < p.1.max' hKne := fun x hx ↦
        (mem_filter.mp (hDB hx)).2.1
      have hunion_ne : (p.1 ∪ p.2).Nonempty := by rw [hEq]; exact hHne
      have hle : (p.1 ∪ p.2).max' hunion_ne ≤ p.1.max' hKne :=
        max'_le _ _ _ fun x hx ↦ by
          rw [mem_union] at hx
          rcases hx with hx | hx
          · exact le_max' _ _ hx
          · exact (hHmax x hx).le
      have hge : p.1.max' hKne ≤ (p.1 ∪ p.2).max' hunion_ne :=
        le_max' _ _ (mem_union_left _ (max'_mem _ _))
      have hEqmax : (p.1 ∪ p.2).max' hunion_ne = z := by simp [hEq, z]
      exact le_antisymm (hEqmax ▸ hge) (hEqmax ▸ hle)
    have hzK : z ∈ p.1 := by
      have := max'_mem p.1 hKne
      simpa [hmax] using this
    exact mem_filter.mpr ⟨mem_powerset.mpr hKsub, hcard, hzK⟩
  · intro K hK
    have hK' := mem_filter.mp hK
    have hKH : K ⊆ H := mem_powerset.mp hK'.1
    have hcard : K.card = L := hK'.2.1
    have hzK : z ∈ K := hK'.2.2
    have hKne : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
    have hKΩ : K ⊆ Ω := hKH.trans hHΩ
    have hKmem : K ∈ Ω.powerset.filter (fun K ↦ K.card = L) :=
      mem_filter.mpr ⟨mem_powerset.mpr hKΩ, hcard⟩
    have hDsub : H \ K ⊆ Stopped.beforeOutside Ω K hKne := by
      intro x hx
      have hx' := mem_sdiff.mp hx
      have hxH : x ∈ H := hx'.1
      have hxK : x ∉ K := hx'.2
      have hlt : x < K.max' hKne := by
        have hxle : x ≤ H.max' hHne := le_max' _ _ hxH
        have hmax : K.max' hKne = z :=
          (max_eq_iff_mem hKne hHne hKH).mpr hzK
        have hne : x ≠ z := by intro hxz; exact hxK (hxz ▸ hzK)
        have hxle' : x ≤ K.max' hKne := by simpa [hmax] using hxle
        have hneK : x ≠ K.max' hKne := by simpa [hmax] using hne
        exact lt_of_le_of_ne hxle' hneK
      exact mem_filter.mpr ⟨hHΩ hxH, hlt, hxK⟩
    have hDcard : (H \ K).card ≤ r - L := by
      have hdisj : Disjoint K (H \ K) := disjoint_sdiff
      have hu : (K ∪ (H \ K)).card = H.card := by rw [union_sdiff_of_subset hKH]
      have hc : K.card + (H \ K).card = H.card := by
        rwa [card_union_of_disjoint hdisj] at hu
      omega
    have hDmem : H \ K ∈ truncDs Ω L r K := by
      simp [truncDs, hKne, mem_filter, mem_powerset, hDsub, hDcard]
    have hσ : (⟨K, H \ K⟩ : Σ _ : Finset ℕ, Finset ℕ) ∈
        (Ω.powerset.filter (fun K ↦ K.card = L)).sigma
          (fun K ↦ truncDs Ω L r K) :=
      mem_sigma.mpr ⟨hKmem, hDmem⟩
    have hEq : K ∪ (H \ K) = H := union_sdiff_of_subset hKH
    exact mem_filter.mpr ⟨hσ, hEq⟩
  · intro p hp
    have hp' := mem_filter.mp hp
    have hEq : p.1 ∪ p.2 = H := hp'.2
    have hσ := mem_sigma.mp hp'.1
    have hK' := mem_filter.mp hσ.1
    have hcard : p.1.card = L := hK'.2
    have hKne : p.1.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
    have hD : p.2 ∈ truncDs Ω L r p.1 := hσ.2
    have hD' : p.2 ∈ (Stopped.beforeOutside Ω p.1 hKne).powerset.filter
        (fun D ↦ D.card ≤ r - L) := by
      simpa [truncDs, hKne] using hD
    have hDB : p.2 ⊆ Stopped.beforeOutside Ω p.1 hKne :=
      mem_powerset.mp (mem_filter.mp hD').1
    have hdisj : Disjoint p.1 p.2 :=
      (disjoint_beforeOutside (Ω := Ω) hKne).mono_right hDB
    have : p.2 = H \ p.1 := by
      rw [← hEq, union_sdiff_cancel_left hdisj]
    exact Sigma.ext rfl (by rw [this])
  · intro K hK
    rfl

private theorem signed_difference (a b : Finset ℕ → ℝ) (L : ℕ)
    (H : Finset ℕ) :
    (-1 : ℝ) ^ (H.card - L) * (b H - a H) =
      (-1 : ℝ) ^ (H.card - L + 1) * (a H - b H) := by
  have hs : (-1 : ℝ) ^ (H.card - L + 1) =
      -((-1 : ℝ) ^ (H.card - L)) := by
    rw [pow_succ]
    ring
  rw [hs]
  ring

private theorem transform_diff_eq {Ω : Finset ℕ} {a b : Finset ℕ → ℝ}
    {L r : ℕ} {K : Finset ℕ} (hK : K.Nonempty) :
    coreJanossyTransform Ω b L r K - coreJanossyTransform Ω a L r K =
      ∑ D ∈ truncDs Ω L r K,
        (-1 : ℝ) ^ D.card * (b (K ∪ D) - a (K ∪ D)) := by
  unfold coreJanossyTransform truncDs
  rw [dif_pos hK, dif_pos hK, dif_pos hK, ← sum_sub_distrib]
  refine sum_congr rfl fun D _ ↦ ?_
  ring

/-- Exact endpoint reindexing of the positive difference of two literal
truncated Janossy transforms. -/
theorem sum_pospart_coreJanossyTransform_le
    {Ω : Finset ℕ} {a b : Finset ℕ → ℝ} {L r : ℕ}
    (hL : 1 ≤ L) (hr : L ≤ r) :
    ∑ K ∈ Ω.powerset.filter (fun K ↦ K.card = L),
        max (coreJanossyTransform Ω b L r K -
          coreJanossyTransform Ω a L r K) 0 ≤
      ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) *
        ∑ H ∈ Ω.powerset.filter (fun H ↦ H.card = j),
          (((-1 : ℝ) ^ (j - L + 1)) * (a H - b H))⁺ := by
  let shapes := Ω.powerset.filter (fun K ↦ K.card = L)
  let s := shapes.sigma (fun K ↦ truncDs Ω L r K)
  let t := Ω.powerset.filter (fun H ↦ L ≤ H.card ∧ H.card ≤ r)
  have hmaps : ∀ p ∈ s, p.1 ∪ p.2 ∈ t := by
    intro p hp
    have hσ := mem_sigma.mp hp
    exact trunc_pair_maps hL hr hσ.1 hσ.2
  have hKsum :
      ∑ K ∈ shapes, max (coreJanossyTransform Ω b L r K -
          coreJanossyTransform Ω a L r K) 0 ≤
        ∑ K ∈ shapes, ∑ D ∈ truncDs Ω L r K,
          max ((-1 : ℝ) ^ D.card * (b (K ∪ D) - a (K ∪ D))) 0 := by
    refine sum_le_sum fun K hK ↦ ?_
    have hmem := mem_filter.mp hK
    have hcard : K.card = L := hmem.2
    have hKne : K.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
    rw [transform_diff_eq (a := a) (b := b) hKne]
    exact pos_sum_le_sum_pos _ _
  have hsigma :
      ∑ K ∈ shapes, ∑ D ∈ truncDs Ω L r K,
          max ((-1 : ℝ) ^ D.card * (b (K ∪ D) - a (K ∪ D))) 0 =
        ∑ p ∈ s, max ((-1 : ℝ) ^ p.2.card *
          (b (p.1 ∪ p.2) - a (p.1 ∪ p.2))) 0 := by
    rw [sum_sigma']
  refine hKsum.trans ?_
  rw [hsigma]
  have hfiber :=
    (sum_fiberwise_of_maps_to' (s := s) (t := t)
      (g := fun p ↦ p.1 ∪ p.2) hmaps
      (fun H ↦ max ((-1 : ℝ) ^ (H.card - L) * (b H - a H)) 0)).symm
  have hrewrite :
      ∑ p ∈ s, max ((-1 : ℝ) ^ p.2.card *
          (b (p.1 ∪ p.2) - a (p.1 ∪ p.2))) 0 =
        ∑ p ∈ s, max ((-1 : ℝ) ^ ((p.1 ∪ p.2).card - L) *
          (b (p.1 ∪ p.2) - a (p.1 ∪ p.2))) 0 := by
    refine sum_congr rfl fun p hp ↦ ?_
    have hσ := mem_sigma.mp hp
    have hK' := mem_filter.mp hσ.1
    have hcard : p.1.card = L := hK'.2
    have hKne : p.1.Nonempty := nonempty_of_card_ge hL (le_of_eq hcard.symm)
    have hD : p.2 ∈ truncDs Ω L r p.1 := hσ.2
    have hD' : p.2 ∈ (Stopped.beforeOutside Ω p.1 hKne).powerset.filter
        (fun D ↦ D.card ≤ r - L) := by
      simpa [truncDs, hKne] using hD
    have hDB : p.2 ⊆ Stopped.beforeOutside Ω p.1 hKne :=
      mem_powerset.mp (mem_filter.mp hD').1
    have hcu : (p.1 ∪ p.2).card = L + p.2.card :=
      card_union_trunc hKne hcard hDB
    have he : (p.1 ∪ p.2).card - L = p.2.card := by omega
    simp [he]
  rw [hrewrite, hfiber]
  have hconst :
      ∑ H ∈ t, ∑ _p ∈ s.filter (fun p ↦ p.1 ∪ p.2 = H),
          max ((-1 : ℝ) ^ (H.card - L) * (b H - a H)) 0 =
        ∑ H ∈ t, ((s.filter (fun p ↦ p.1 ∪ p.2 = H)).card : ℝ) *
          max ((-1 : ℝ) ^ (H.card - L) * (b H - a H)) 0 := by
    refine sum_congr rfl fun H _ ↦ ?_
    rw [sum_const, nsmul_eq_mul]
  rw [hconst]
  have hcard :
      ∑ H ∈ t, ((s.filter (fun p ↦ p.1 ∪ p.2 = H)).card : ℝ) *
          max ((-1 : ℝ) ^ (H.card - L) * (b H - a H)) 0 =
        ∑ H ∈ t, ((H.card - 1).choose (L - 1) : ℝ) *
          max ((-1 : ℝ) ^ (H.card - L + 1) * (a H - b H)) 0 := by
    refine sum_congr rfl fun H hH ↦ ?_
    have hH' := mem_filter.mp hH
    have hHΩ : H ⊆ Ω := mem_powerset.mp hH'.1
    have ⟨hLo, hHi⟩ := hH'.2
    have hHne : H.Nonempty := nonempty_of_card_ge hL hLo
    have hc := fiber_card_eq (Ω := Ω) (H := H) (L := L) (r := r)
      hL hr hHΩ hHne hLo hHi
    have hsign := signed_difference a b L H
    rw [hc]
    refine congrArg (fun z ↦ ((H.card - 1).choose (L - 1) : ℝ) * z) ?_
    exact congrArg (fun z ↦ max z 0) hsign
  rw [hcard]
  have hgroup :
      ∑ H ∈ t, ((H.card - 1).choose (L - 1) : ℝ) *
          max ((-1 : ℝ) ^ (H.card - L + 1) * (a H - b H)) 0 =
        ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) *
          ∑ H ∈ Ω.powerset.filter (fun H ↦ H.card = j),
            max ((-1 : ℝ) ^ (j - L + 1) * (a H - b H)) 0 := by
    have ht : t = (Icc L r).biUnion
        (fun j ↦ Ω.powerset.filter (fun H ↦ H.card = j)) := by
      ext H
      simp only [mem_biUnion, mem_Icc, mem_filter, mem_powerset, t]
      constructor
      · intro h
        exact ⟨H.card, h.2, h.1, rfl⟩
      · intro ⟨j, hj, hH, hcard⟩
        exact ⟨hH, hcard ▸ hj.1, hcard ▸ hj.2⟩
    have hdisj : (Icc L r : Set ℕ).PairwiseDisjoint
        (fun j ↦ Ω.powerset.filter (fun H ↦ H.card = j)) := by
      intro x _ y _ hxy
      refine disjoint_left.mpr ?_
      intro H hHx hHy
      exact hxy ((mem_filter.mp hHx).2.symm.trans (mem_filter.mp hHy).2)
    rw [ht, sum_biUnion hdisj]
    refine sum_congr rfl fun j _ ↦ ?_
    have hs :
        ∑ H ∈ Ω.powerset.filter (fun H ↦ H.card = j),
            ((H.card - 1).choose (L - 1) : ℝ) *
              max ((-1 : ℝ) ^ (H.card - L + 1) * (a H - b H)) 0 =
          ∑ H ∈ Ω.powerset.filter (fun H ↦ H.card = j),
            ((j - 1).choose (L - 1) : ℝ) *
              max ((-1 : ℝ) ^ (j - L + 1) * (a H - b H)) 0 := by
      refine sum_congr rfl fun H hH ↦ ?_
      have he : H.card = j := (mem_filter.mp hH).2
      simp [he]
    rw [hs, ← mul_sum]
  rw [hgroup]
  simp only [max_eq_posPart]
  exact le_rfl

/-- The literal small-window AHL budget bounds exactly the adverse
main-minus-actual Janossy error used after rewriting `D(X,1)`. -/
theorem small_main_actual_Janossy_pos_le_ahlSmall_budget
    {κ d0 : ℝ} {X : ℕ} (hL : 1 ≤ profileL κ X)
    (hN : 0 < windowNX X) :
    (∑ K ∈ (ahlSmall_omega κ X).powerset.filter
        (fun K ↦ K.card = profileL κ X),
      max (coreJanossyTransform (ahlSmall_omega κ X) (rootedMainTerm X)
            (profileL κ X) (profileR (profileL κ X) d0) K -
          coreJanossyTransform (ahlSmall_omega κ X)
            (fun H ↦ (rootedTupleCount X H : ℝ))
            (profileL κ X) (profileR (profileL κ X) d0) K) 0) /
        (windowNX X : ℝ) ≤ ahlSmall_budget κ d0 X := by
  have hraw := sum_pospart_coreJanossyTransform_le
    (Ω := ahlSmall_omega κ X)
    (a := fun H ↦ (rootedTupleCount X H : ℝ))
    (b := rootedMainTerm X) hL (profileR_ge (profileL κ X) d0)
  have hden : 0 < (windowNX X : ℝ) := Nat.cast_pos.mpr hN
  have hdiv := div_le_div_of_nonneg_right hraw hden.le
  rw [ahlSmall_budget]
  simp only [if_neg (Nat.ne_of_gt hN), div_eq_mul_inv]
  simpa only [ahlSmall_layer, div_eq_mul_inv, one_div, one_mul, mul_comm,
    mul_left_comm, mul_assoc] using hdiv

end

end PrimeGapNormality.Prime.CoreFrozenAHL
