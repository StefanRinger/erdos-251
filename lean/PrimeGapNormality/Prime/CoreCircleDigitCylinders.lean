import PrimeGapNormality.Prime.CoreFourierMeasureUniqueness
import PrimeGapNormality.BFree.Definitions
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Literal half-open circle cylinders and exact empirical counts. Boundary
points are treated explicitly; no continuity of the fractional-part map at
the seam is assumed. -/

namespace PrimeGapNormality.Prime.CoreWeylNormality

open Set Filter MeasureTheory Finset
open scoped Topology ENNReal Classical

noncomputable section

def arc (a b : ℝ) : Set (AddCircle (1 : ℝ)) :=
  (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Ico a b

private theorem interval_in_fundamental {a b t : ℝ} (hwidth : b < a + 1)
    (ht : t ∈ Icc a b) : t ∈ Ioc (b - 1) (b - 1 + 1) := by
  constructor <;> linarith [ht.1, ht.2]

theorem measurableSet_arc {a b : ℝ} (hwidth : b < a + 1) : MeasurableSet (arc a b) := by
  have hclosed : IsClosed ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Icc a b) :=
    (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed
  have heq : arc a b =
      ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Icc a b) \ {(b : AddCircle (1 : ℝ))} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩, ?_⟩
      intro he
      have htb : t = b := (AddCircle.coe_eq_coe_iff_of_mem_Ioc
        (interval_in_fundamental hwidth ⟨ht.1, ht.2.le⟩)
        (show b ∈ Ioc (b - 1) (b - 1 + 1) by constructor <;> linarith)).1 he
      exact ht.2.ne htb
    · rintro ⟨⟨t, ht, rfl⟩, hne⟩
      have htb : t < b := lt_of_le_of_ne ht.2 (fun h ↦ hne (by simp [h]))
      exact ⟨t, ⟨ht.1, htb⟩, rfl⟩
  rw [heq]
  exact hclosed.measurableSet.diff (measurableSet_singleton _)

theorem volume_arc {a b : ℝ} (hwidth : b < a + 1) :
    volume (arc a b) = ENNReal.ofReal (b - a) := by
  have hmeas := measurableSet_arc hwidth
  have hpre :
      (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) ⁻¹' arc a b ∩
        Ioc (b - 1) (b - 1 + 1) = Ico a b := by
    ext t
    constructor
    · rintro ⟨⟨u, hu, hut⟩, ht⟩
      have hut' : u = t := (AddCircle.coe_eq_coe_iff_of_mem_Ioc
        (interval_in_fundamental hwidth ⟨hu.1, hu.2.le⟩) ht).1 hut
      rwa [← hut']
    · intro ht
      exact ⟨⟨t, ht, rfl⟩, interval_in_fundamental hwidth ⟨ht.1, ht.2.le⟩⟩
  have h := (AddCircle.measurePreserving_mk (1 : ℝ) (b - 1)).measure_preimage
    hmeas.nullMeasurableSet
  rw [Measure.restrict_apply (hmeas.preimage AddCircle.measurable_mk'), hpre,
    Real.volume_Ico] at h
  exact h.symm

theorem frontier_arc_subset (a b : ℝ) :
    frontier (arc a b) ⊆ {(a : AddCircle (1 : ℝ)), (b : AddCircle (1 : ℝ))} := by
  have hclosed : IsClosed ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Icc a b) :=
    (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed
  have hclosure : closure (arc a b) ⊆
      (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Icc a b :=
    closure_minimal (image_mono Ico_subset_Icc_self) hclosed
  have hopen : IsOpen ((fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Ioo a b) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hinterior : (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Ioo a b ⊆
      interior (arc a b) := interior_maximal (image_mono Ioo_subset_Ico_self) hopen
  intro x hx
  obtain ⟨t, ht, htx⟩ := hclosure (frontier_subset_closure hx)
  have htend : t = a ∨ t = b := by
    by_contra hn
    have hta : a < t := lt_of_le_of_ne ht.1 (by tauto)
    have htb : t < b := lt_of_le_of_ne ht.2 (by tauto)
    exact hx.2 (hinterior ⟨t, ⟨hta, htb⟩, htx⟩)
  rcases htend with rfl | rfl <;> simp [← htx]

theorem frontier_arc_null (a b : ℝ) : volume (frontier (arc a b)) = 0 := by
  have hsingleton (x : AddCircle (1 : ℝ)) : volume ({x} : Set (AddCircle (1 : ℝ))) = 0 := by
    simpa using (AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) 0)
  have hpair : volume ({(a : AddCircle (1 : ℝ)), (b : AddCircle (1 : ℝ))} :
      Set (AddCircle (1 : ℝ))) = 0 := by
    simpa only [Set.singleton_union] using
      measure_union_null (hsingleton (a : AddCircle (1 : ℝ)))
        (hsingleton (b : AddCircle (1 : ℝ)))
  exact measure_mono_null (frontier_arc_subset a b)
    hpair

theorem coe_mem_arc_iff_fract {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (x : ℝ) :
    (x : AddCircle (1 : ℝ)) ∈ arc a b ↔ Int.fract x ∈ Ico a b := by
  have hrepr : (AddCircle.equivIco (1 : ℝ) 0 (x : AddCircle (1 : ℝ)) : ℝ) =
      Int.fract x := by simp
  constructor
  · rintro ⟨t, ht, htx⟩
    have ht01 : t ∈ Ico (0 : ℝ) (0 + 1) :=
      ⟨ha.trans ht.1, by simpa only [zero_add] using ht.2.trans_le hb⟩
    have heq := congrArg
      (fun z : AddCircle (1 : ℝ) ↦ (AddCircle.equivIco (1 : ℝ) 0 z : ℝ)) htx
    rw [AddCircle.equivIco_coe_of_mem ht01, hrepr] at heq
    rwa [← heq]
  · intro hx
    refine ⟨Int.fract x, hx, ?_⟩
    rw [← hrepr]
    exact AddCircle.coe_equivIco

/-- Finite cardinal conversion from the uniform `Fin N` sample to the
literal filter of `range N` used by the digit-frequency definition. -/
private theorem card_fin_pred (N : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    Fintype.card {i : Fin N // p i} = ((range N).filter p).card := by
  have hsum := Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ if p n then (1 : ℕ) else 0) N
  simpa only [sum_boole, Fintype.card_subtype, Nat.cast_id, id_eq] using hsum

set_option backward.isDefEq.respectTransparency false in
theorem empirical_apply (B : ℕ) (α : ℝ) {N : ℕ} (hN : 0 < N)
    (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) :
    (empirical B α N : Measure (AddCircle (1 : ℝ))) s =
      (((range N).filter (fun n ↦ orbit B α n ∈ s)).card : ℝ≥0∞) / N := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hf : Measurable (fun i : Fin N ↦ orbit B α (0 + (i : ℕ))) := measurable_of_finite _
  have hmeasure : (empirical B α N : Measure (AddCircle (1 : ℝ))) =
      ((PMF.uniformOfFintype (Fin N)).map
        (fun i : Fin N ↦ orbit B α (0 + (i : ℕ)))).toMeasure := by
    unfold empirical coreDigitalWindowMeasure
    rw [dif_pos hN]
    rfl
  rw [hmeasure, PMF.toMeasure_map_apply _ (PMF.uniformOfFintype (Fin N)) s hf hs,
    PMF.toMeasure_uniformOfFintype_apply _ (hs.preimage hf)]
  simp only [Nat.zero_add, Fintype.card_fin]
  change ((Fintype.card {i : Fin N // orbit B α (i : ℕ) ∈ s} : ℝ≥0∞) / (N : ℝ≥0∞)) = _
  rw [card_fin_pred N (fun n ↦ orbit B α n ∈ s)]

theorem empirical_real_apply (B : ℕ) (α : ℝ) {N : ℕ} (hN : 0 < N)
    (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) :
    (empirical B α N : Measure (AddCircle (1 : ℝ))).real s =
      (((range N).filter (fun n ↦ orbit B α n ∈ s)).card : ℝ) / N := by
  rw [Measure.real, empirical_apply B α hN s hs]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]

end

end PrimeGapNormality.Prime.CoreWeylNormality
