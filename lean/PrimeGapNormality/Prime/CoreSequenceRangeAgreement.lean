import PrimeGapNormality.Prime.CoreSequencePatternLaw
import PrimeGapNormality.Prime.CoreSequenceSTConsumer

/-!
# Finite physical laws under eventual range agreement

Two strictly increasing enumerations whose ranges agree above a fixed
physical threshold have the same physical dyadic roots and the same rooted
finite patterns eventually.  Thus their exact finite pattern masses agree,
not merely their limiting laws.  This justifies changing finitely many
initial values without introducing any distributional assumption.
-/

namespace PrimeGapNormality.Prime.CoreSequenceRangeAgreement

open Filter Set Finset
open scoped Topology Classical

open CoreSequencePattern CoreSequencePatternLaw CoreSequenceSTConsumer

noncomputable section

/-- Physical values of an increasing sequence in `(X,2X]`. -/
def physicalRangeWindow (a : ℕ → ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter (fun v ↦ v ∈ Set.range a)

/-- The configuration at a physical root, written directly in terms of the
range rather than an enumeration index. -/
def physicalRangePattern
    (a : ℕ → ℕ) (Ω : Finset ℕ) (v : ℕ) : Finset ℕ :=
  Ω.filter (fun h ↦ v + h ∈ Set.range a)

/-- Physical-value presentation of the exact rooted-pattern pushforward. -/
def physicalRangePatternMass
    (a : ℕ → ℕ) (X : ℕ) (Ω U : Finset ℕ) : ℝ :=
  (∑ v ∈ physicalRangeWindow a X,
      if physicalRangePattern a Ω v = U then (1 : ℝ) else 0) /
    ((physicalRangeWindow a X).card : ℝ)

private theorem mem_seqWindow_iff
    {a : ℕ → ℕ} (ha : StrictMono a) {X n : ℕ} :
    n ∈ seqWindow a X ↔ X < a n ∧ a n ≤ 2 * X := by
  simp only [seqWindow, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨le_trans (strictMono_le_id ha n) h.2, h⟩

theorem image_seqWindow_eq_physicalRangeWindow
    {a : ℕ → ℕ} (ha : StrictMono a) (X : ℕ) :
    (seqWindow a X).image a = physicalRangeWindow a X := by
  ext v
  constructor
  · intro hv
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hv
    have hn' := (mem_seqWindow_iff ha).mp hn
    exact mem_filter.mpr ⟨Finset.mem_Ioc.mpr hn', ⟨n, rfl⟩⟩
  · intro hv
    obtain ⟨hvI, n, hn⟩ := mem_filter.mp hv
    apply mem_image.mpr
    refine ⟨n, (mem_seqWindow_iff ha).mpr ?_, hn⟩
    simpa only [hn] using Finset.mem_Ioc.mp hvI

theorem physicalRangeWindow_card_eq_seqWindow_card
    {a : ℕ → ℕ} (ha : StrictMono a) (X : ℕ) :
    (physicalRangeWindow a X).card = (seqWindow a X).card := by
  rw [← image_seqWindow_eq_physicalRangeWindow ha,
    card_image_of_injective _ ha.injective]

theorem rootedPattern_eq_physicalRangePattern
    (a : ℕ → ℕ) (Ω : Finset ℕ) (n : ℕ) :
    CoreSequencePatternLaw.rootedPattern a Ω n = physicalRangePattern a Ω (a n) := by
  ext h
  simp only [CoreSequencePatternLaw.rootedPattern, CoreSequencePattern.pattern,
    physicalRangePattern, Finset.mem_filter]
  apply and_congr_right
  intro _
  rfl

theorem patternMass_eq_physicalRangePatternMass
    {a : ℕ → ℕ} (ha : StrictMono a) (X : ℕ) (Ω U : Finset ℕ) :
    patternMass a X Ω U = physicalRangePatternMass a X Ω U := by
  have hsum :
      (∑ n ∈ seqWindow a X,
        if CoreSequencePatternLaw.rootedPattern a Ω n = U then (1 : ℝ) else 0) =
      ∑ v ∈ physicalRangeWindow a X,
        if physicalRangePattern a Ω v = U then (1 : ℝ) else 0 := by
    calc
      _ = ∑ n ∈ seqWindow a X,
          if physicalRangePattern a Ω (a n) = U then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro n hn
        rw [rootedPattern_eq_physicalRangePattern]
      _ = ∑ v ∈ (seqWindow a X).image a,
          if physicalRangePattern a Ω v = U then (1 : ℝ) else 0 := by
        symm
        rw [Finset.sum_image (fun n hn m hm hnm ↦ ha.injective hnm)]
      _ = _ := by rw [image_seqWindow_eq_physicalRangeWindow ha]
  unfold patternMass physicalRangePatternMass
  rw [hsum, physicalRangeWindow_card_eq_seqWindow_card ha]

private theorem physicalRangePattern_eq_of_tail
    {a b : ℕ → ℕ} {N v : ℕ}
    (htail : ∀ w, N ≤ w → (w ∈ Set.range a ↔ w ∈ Set.range b))
    (hv : N ≤ v) (Ω : Finset ℕ) :
    physicalRangePattern a Ω v = physicalRangePattern b Ω v := by
  ext h
  simp only [physicalRangePattern, mem_filter]
  apply and_congr_right
  intro _
  exact htail (v + h) (hv.trans (Nat.le_add_right v h))

private theorem physicalRangeWindow_eq_of_tail
    {a b : ℕ → ℕ} {N X : ℕ}
    (htail : ∀ v, N ≤ v → (v ∈ Set.range a ↔ v ∈ Set.range b))
    (hX : N ≤ X) :
    physicalRangeWindow a X = physicalRangeWindow b X := by
  ext v
  simp only [physicalRangeWindow, mem_filter]
  apply and_congr_right
  intro hv
  exact htail v (hX.trans (Finset.mem_Ioc.mp hv).1.le)

/-- Eventual equality of the actual physical-window cardinalities. -/
theorem eventually_seqWindow_card_eq_of_range_agreement
    {a b : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ v ∈ Set.range b)) :
    ∀ᶠ X : ℕ in atTop, (seqWindow a X).card = (seqWindow b X).card := by
  rcases eventually_atTop.1 hrange with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with X hX
  rw [← physicalRangeWindow_card_eq_seqWindow_card ha,
    ← physicalRangeWindow_card_eq_seqWindow_card hb,
    physicalRangeWindow_eq_of_tail hN hX]

/-- Strong finite conclusion: every exact rooted-pattern mass agrees
eventually, uniformly in the finite observation window and configuration. -/
theorem eventually_patternMass_eq_of_range_agreement
    {a b : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ v ∈ Set.range b)) :
    ∀ᶠ X : ℕ in atTop, ∀ Ω : Finset ℕ,
      patternMass a X Ω = patternMass b X Ω := by
  rcases eventually_atTop.1 hrange with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with X hX
  intro Ω
  funext U
  rw [patternMass_eq_physicalRangePatternMass ha,
    patternMass_eq_physicalRangePatternMass hb]
  unfold physicalRangePatternMass
  have hroots := physicalRangeWindow_eq_of_tail hN hX
  rw [← hroots]
  congr 1
  apply sum_congr rfl
  intro v hv
  have hvI := Finset.mem_Ioc.mp (mem_filter.mp hv).1
  rw [physicalRangePattern_eq_of_tail hN (hX.trans hvI.1.le)]

/-- Any concrete Shape-S input transfers across a finite change of the
enumerated range, with the same model scale and comparison constant. -/
theorem sequencePositiveShapeS_of_range_agreement
    {a b T : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ v ∈ Set.range b))
    {κ c : ℝ} (hS : SequencePositiveShapeS a T κ c) :
    SequencePositiveShapeS b T κ c := by
  intro ε hε
  filter_upwards [hS ε hε,
    eventually_patternMass_eq_of_range_agreement ha hb hrange] with X hSX hmass
  intro f hf0 hf1
  let Ω := offsetWindow (ahlSmall_window κ (T X))
  have heq : patternMass a X Ω = patternMass b X Ω := hmass Ω
  rw [← heq]
  exact hSX f hf0 hf1

/-- Range agreement is symmetric, so Shape-S is in fact invariant under
finite initial changes. -/
theorem sequencePositiveShapeS_iff_of_range_agreement
    {a b T : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ v ∈ Set.range b)) {κ c : ℝ} :
    SequencePositiveShapeS a T κ c ↔ SequencePositiveShapeS b T κ c := by
  constructor
  · exact sequencePositiveShapeS_of_range_agreement ha hb hrange
  · apply sequencePositiveShapeS_of_range_agreement hb ha
    filter_upwards [hrange] with v hv
    exact hv.symm

end

end PrimeGapNormality.Prime.CoreSequenceRangeAgreement
