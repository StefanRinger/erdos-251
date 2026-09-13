import PrimeGapNormality.BFree.Definitions
import PrimeGapNormality.BFree.Enumeration
import PrimeGapNormality.BFree.SingleCoordinate
import PrimeGapNormality.BFree.AffineWord
import PrimeGapNormality.BFree.ProductRotation
import PrimeGapNormality.BFree.ReturnTowers
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Countable positive affine carry is impossible (Wave A + Wave B + Wave C)

Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 3.1, Theorem 3.3,
Lemma 4.1, (2.3)–(2.6); `lean/BFREE_CARRY_LEMMAS.md` Wave A, Wave B §§7.9–7.11,
Wave C §7.12.
Contract: C3
Audit: GREEN (paper); Lean Wave A (3.1, fibres, 3.3); Wave B (`T`, `Y`, (2.5)–(2.6));
Wave C (model mean tail; Lemma 4.1 with explicit Palm hyp)

`Measurable C` is required for level sets. Recurrence uses real powers
`(b : ℝ) ^ …`. Inverse rotation is imported from ProductRotation.
`t` includes the present. `Y` is a.s. finite only; no ambient
`Integrable (futureRootCarry …) (productMeasure F)`.
Does not import CanonicalTransfer or Series. DAG: Carry → Irrationality later.
-/

open Classical
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology Filter symmDiff NNReal

namespace PrimeGapNormality.BFree

open Set Function
open Filter (Tendsto atTop)

/-! ### 7.0 Visit bits and the orbit affine path -/

noncomputable def visitBit (F : AdmissibleFamily) (ω : ResidueSpace F) (j : ℕ) : ℕ :=
  if (shift F)^[j] ω ∈ survival F then 1 else 0

noncomputable def orbitAffinePath (F : AdmissibleFamily) (b Q : ℝ)
    (C : ResidueSpace F → ℝ) (ω : ResidueSpace F) : ℕ → ℝ :=
  affinePath b Q (visitBit F ω) (C ω)

theorem visitBit_zero (F : AdmissibleFamily) (ω : ResidueSpace F) :
    visitBit F ω 0 = if ω ∈ survival F then 1 else 0 :=
  rfl

theorem survival_shift_iterate (F : AdmissibleFamily) (n : ℕ) (ω : ResidueSpace F) :
    (shift F)^[n] ω ∈ survival F ↔ ∀ i, ω i + n ≠ 0 := by
  simp [survival, shift_iterate_apply]

theorem visitBit_update (F : AdmissibleFamily) (iq : ℕ) (ω : ResidueSpace F)
    (r : ZMod (F.d iq)) (j : ℕ) :
    visitBit F (update ω iq r) j =
      if r + j ≠ 0 ∧ (∀ i, i ≠ iq → ω i + j ≠ 0) then 1 else 0 := by
  have hiff :
      (shift F)^[j] (update ω iq r) ∈ survival F ↔
        r + j ≠ 0 ∧ ∀ i, i ≠ iq → ω i + j ≠ 0 := by
    rw [survival_shift_iterate]
    constructor
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · simpa [Function.update_self] using h iq
      · simpa [Function.update_of_ne hi] using h i
    · intro ⟨hr, hrest⟩ i
      by_cases hi : i = iq
      · subst hi
        simpa [Function.update_self] using hr
      · simpa [Function.update_of_ne hi] using hrest i hi
  simp [visitBit, hiff]

theorem orbitAffinePath_succ_of_rec (F : AdmissibleFamily) (b Q : ℝ)
    (C : ResidueSpace F → ℝ) (ω : ResidueSpace F) (n : ℕ)
    (h : ∀ k < n,
      C ((shift F)^[k + 1] ω) =
        (b : ℝ) ^ visitBit F ω k * C ((shift F)^[k] ω) - Q) :
    C ((shift F)^[n] ω) = orbitAffinePath F b Q C ω n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hn := h n (Nat.lt_succ_self n)
    calc
      C ((shift F)^[n + 1] ω)
          = (b : ℝ) ^ visitBit F ω n * C ((shift F)^[n] ω) - Q := hn
      _ = (b : ℝ) ^ visitBit F ω n * orbitAffinePath F b Q C ω n - Q := by rw [ih']
      _ = orbitAffinePath F b Q C ω (n + 1) := by
          simp [orbitAffinePath, affinePath_succ, affineStep]

/-! ### Finite-coordinate dependence and period -/

def DependsOnFinset {F : AdmissibleFamily} (s : Finset ℕ) (f : ResidueSpace F → ℝ) : Prop :=
  ∀ ω ω', (∀ i ∈ s, ω i = ω' i) → f ω = f ω'

noncomputable def coordPeriod (F : AdmissibleFamily) (s : Finset ℕ) : ℕ :=
  ∏ i ∈ s, F.d i

theorem coordPeriod_pos (F : AdmissibleFamily) (s : Finset ℕ) : 0 < coordPeriod F s :=
  Finset.prod_pos fun i _ => d_pos F i

theorem d_dvd_coordPeriod (F : AdmissibleFamily) {s : Finset ℕ} {i : ℕ} (hi : i ∈ s) :
    F.d i ∣ coordPeriod F s :=
  Finset.dvd_prod_of_mem _ hi

theorem dependsOnFinset_periodic {F : AdmissibleFamily} {s : Finset ℕ} {H : ℕ}
    {C_F : ResidueSpace F → ℝ} (hW : ∀ i ∈ s, F.d i ∣ H) (hdep : DependsOnFinset s C_F) :
    C_F ∘ (shift F)^[H] = C_F := by
  funext ω
  apply hdep
  intro i hi
  have : (H : ZMod (F.d i)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (hW i hi)
  rw [shift_iterate_apply, this, add_zero]

theorem dependsOnFinset_update {F : AdmissibleFamily} {s : Finset ℕ} {iq : ℕ}
    {f : ResidueSpace F → ℝ} (hdep : DependsOnFinset s f) (hiq : iq ∉ s)
    (ω : ResidueSpace F) (r : ZMod (F.d iq)) :
    f (update ω iq r) = f ω := by
  apply hdep
  intro i hi
  have : i ≠ iq := fun h => hiq (h ▸ hi)
  exact Function.update_of_ne this r ω

theorem exists_unused_large_index (F : AdmissibleFamily) (s : Finset ℕ) :
    ∃ i, i ∉ s ∧ 8 * coordPeriod F s ≤ F.d i :=
  exists_unused_index F s (coordPeriod F s) (coordPeriod_pos F s)

theorem adaptedWindow_of_unused (F : AdmissibleFamily) {s : Finset ℕ} {i : ℕ}
    (hW : 0 < coordPeriod F s) (hq : 8 * coordPeriod F s ≤ F.d i) :
    let W := coordPeriod F s
    let q := F.d i
    let H := adaptedWindow W q
    W ∣ H ∧ H < q ∧ q ≤ 8 * H ∧ 4 * H ≤ q ∧
      (q : ℝ) / 8 ≤ H ∧ (H : ℝ) ≤ (q : ℝ) / 4 ∧ i ∉ s := by
  intro W q H
  have hspec := adaptedWindow_spec (W := W) (q := q) hW hq
  have hreal := adaptedWindow_real (W := W) (q := q) hW hq
  have hi : i ∉ s := by
    intro hins
    have hle : F.d i ≤ W := Nat.le_of_dvd hW (d_dvd_coordPeriod F hins)
    have : 8 * W ≤ W := hq.trans hle
    have : 8 ≤ 1 := Nat.le_of_mul_le_mul_right (by simpa using this) hW
    exact (by decide : ¬ (8 : ℕ) ≤ 1) this
  exact ⟨hspec.1, hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2, hreal.1, hreal.2, hi⟩

theorem measure_survival_toReal (F : AdmissibleFamily) :
    (productMeasure F (survival F)).toReal = rho F := by
  rw [measure_survival, ENNReal.toReal_ofReal (rho_pos F).le]

theorem rho_le_one (F : AdmissibleFamily) : rho F ≤ 1 := by
  have := productMeasure_isProbabilityMeasure F
  have h := ENNReal.toReal_mono ENNReal.one_ne_top
    (prob_le_one (μ := productMeasure F) (s := survival F))
  simpa [measure_survival_toReal, ENNReal.toReal_one] using h

theorem one_le_b {b : ℕ} (hb : 2 ≤ b) : (1 : ℝ) < b := by
  have : (2 : ℝ) ≤ b := Nat.cast_le.mpr hb
  linarith

/-! ### List fold used by Lemma 3.1 -/

noncomputable def approxOnList {F : AdmissibleFamily} (T : ℝ → Set (ResidueSpace F))
    (c0 : ℝ) : List ℝ → ResidueSpace F → ℝ
  | [] => fun _ => c0
  | c :: rest => fun ω => if ω ∈ T c then c else approxOnList T c0 rest ω

theorem measurable_approxOnList {F : AdmissibleFamily} {T : ℝ → Set (ResidueSpace F)}
    {c0 : ℝ} (hT : ∀ c, MeasurableSet (T c)) :
    ∀ l, Measurable (approxOnList T c0 l)
  | [] => measurable_const
  | c :: rest =>
    Measurable.ite (hT c) measurable_const (measurable_approxOnList hT rest)

theorem dependsOnFinset_approxOnList {F : AdmissibleFamily} {T : ℝ → Set (ResidueSpace F)}
    {c0 : ℝ} {s : Finset ℕ}
    (hT : ∀ c ω ω', (∀ i ∈ s, ω i = ω' i) → (ω ∈ T c ↔ ω' ∈ T c)) :
    ∀ l, DependsOnFinset s (approxOnList T c0 l)
  | [] => fun _ _ _ => rfl
  | c :: rest => by
    intro ω ω' hagree
    have hmem : ω ∈ T c ↔ ω' ∈ T c := hT c ω ω' hagree
    have hrest := dependsOnFinset_approxOnList (c0 := c0) hT rest ω ω' hagree
    simp [approxOnList, hmem, hrest]

theorem approxOnList_pos {F : AdmissibleFamily} {T : ℝ → Set (ResidueSpace F)} {c0 : ℝ}
    (hc0 : 0 < c0) :
    ∀ l, (∀ c ∈ l, 0 < c) → ∀ ω, 0 < approxOnList T c0 l ω
  | [], _, _ => hc0
  | c :: rest, hpos, ω => by
    simp [approxOnList]
    split_ifs
    · exact hpos c List.mem_cons_self
    · exact approxOnList_pos hc0 rest (fun d hd => hpos d (List.mem_cons_of_mem _ hd)) ω

theorem approxOnList_mem {F : AdmissibleFamily} {T : ℝ → Set (ResidueSpace F)} {c0 : ℝ} :
    ∀ l ω, approxOnList T c0 l ω = c0 ∨ approxOnList T c0 l ω ∈ (l.toFinset : Set ℝ)
  | [], _ => Or.inl rfl
  | c :: rest, ω => by
    simp only [approxOnList]
    split_ifs with hTc
    · refine Or.inr ?_
      simp
    · rcases approxOnList_mem (T := T) (c0 := c0) rest ω with h0 | hrest
      · exact Or.inl h0
      · refine Or.inr ?_
        simp only [List.toFinset_cons, Finset.coe_insert]
        exact Set.mem_insert_of_mem _ hrest

theorem approxOnList_eq_of {F : AdmissibleFamily} {T : ℝ → Set (ResidueSpace F)} {c0 : ℝ} :
    ∀ l c ω, c ∈ l → ω ∈ T c → (∀ d ∈ l, d ≠ c → ω ∉ T d) →
      approxOnList T c0 l ω = c
  | [], c, ω, hmem, _, _ => by simp at hmem
  | d :: rest, c, ω, hmem, hTc, hskip => by
    simp [approxOnList]
    by_cases hd : d = c
    · subst hd
      simp [hTc]
    · have hdT : ω ∉ T d := hskip d List.mem_cons_self hd
      rw [if_neg hdT]
      refine approxOnList_eq_of (c0 := c0) rest c ω ?_ hTc ?_
      · simp only [List.mem_cons] at hmem
        exact hmem.resolve_left (Ne.symm hd)
      · intro e he hne
        exact hskip e (List.mem_cons_of_mem _ he) hne

theorem cylinder_mem_of_agree {F : AdmissibleFamily} {I : Finset ℕ}
    {S : Set (∀ i : I, ZMod (F.d i))} {ω ω' : ResidueSpace F}
    (h : ∀ i ∈ I, ω i = ω' i) :
    ω ∈ cylinder I S ↔ ω' ∈ cylinder I S := by
  have hres : I.restrict ω = I.restrict ω' := by
    funext i
    exact h i.1 i.2
  simp [cylinder, hres]

/-! ### Lemma 3.1 -/

theorem exists_finset_vals (F : AdmissibleFamily) {C : ResidueSpace F → ℝ}
    (hC : Measurable C) {u : Set ℝ} (hct : Countable u)
    (hae : ∀ᵐ ω ∂productMeasure F, C ω ∈ u) (ε : ℝ) (hε : 0 < ε)
    (hune : u.Nonempty) :
    ∃ vals : Finset ℝ, (vals : Set ℝ) ⊆ u ∧ vals.Nonempty ∧
      productMeasure F {ω | C ω ∉ vals} < ENNReal.ofReal (ε / 2) := by
  have := productMeasure_isProbabilityMeasure F
  have htail0 : productMeasure F {ω | C ω ∉ u} = 0 := ae_iff.mp hae
  by_cases hfin : u.Finite
  · refine ⟨hfin.toFinset, by simp, ?_, ?_⟩
    · simpa using hune
    · have hsub : {ω : ResidueSpace F | C ω ∉ hfin.toFinset} ⊆ {ω | C ω ∉ u} := by
        intro ω hω
        simpa using hω
      have hzero : productMeasure F {ω | C ω ∉ hfin.toFinset} = 0 :=
        measure_mono_null hsub htail0
      rw [hzero]
      exact ENNReal.ofReal_pos.mpr (half_pos hε)
  · obtain ⟨f, hf⟩ := (Set.countable_coe_iff.mp hct).exists_eq_range hune
    let t : ℕ → Finset ℝ := fun n => (Finset.range n).image f
    have hanti : Antitone fun n => {ω : ResidueSpace F | C ω ∉ t n} := by
      intro a b hab ω hω hc
      apply hω
      rcases Finset.mem_image.mp hc with ⟨k, hk, heq⟩
      refine Finset.mem_image.mpr ⟨k, ?_, heq⟩
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hab)
    have hinter :
        ⋂ n, {ω : ResidueSpace F | C ω ∉ t n} = {ω | C ω ∉ Set.range f} := by
      ext ω
      constructor
      · intro h hfω
        rcases hfω with ⟨n, hn⟩
        have hN := (Set.mem_iInter.mp h) (n + 1)
        exact hN (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), hn⟩)
      · intro h
        refine Set.mem_iInter.mpr fun n hc => ?_
        rcases Finset.mem_image.mp hc with ⟨k, -, heq⟩
        exact h ⟨k, heq⟩
    have hmeas n : NullMeasurableSet {ω : ResidueSpace F | C ω ∉ t n} (productMeasure F) :=
      ((hC (t n).measurableSet).compl).nullMeasurableSet
    have hlim :
        Tendsto (fun n => productMeasure F {ω | C ω ∉ t n}) atTop (𝓝 0) := by
      have h0 : productMeasure F {ω | C ω ∉ Set.range f} = 0 := by
        simpa [hf] using htail0
      have htend := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
      rw [hinter, h0] at htend
      exact htend
    have hlt : ∀ᶠ n in atTop,
        productMeasure F {ω | C ω ∉ t n} < ENNReal.ofReal (ε / 2) :=
      (tendsto_order.1 hlim).2 (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hlt
    have hN0 := hN N le_rfl
    by_cases hne : (t N).Nonempty
    · refine ⟨t N, ?_, hne, hN0⟩
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨k, -, heq⟩
      simpa [hf] using ⟨k, heq⟩
    · refine ⟨{Classical.choose hune}, ?_, by simp, ?_⟩
      · intro c hc
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
        rw [hc]
        exact Classical.choose_spec hune
      · have hempty : t N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have huniv : {ω : ResidueSpace F | C ω ∉ t N} = univ := by
          simp [hempty]
        have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := by
          simpa [huniv, measure_univ] using hN0
        exact (prob_le_one (μ := productMeasure F)
          (s := {ω | C ω ∉ ({Classical.choose hune} : Finset ℝ)})).trans_lt h1

theorem exists_exact_cylinder_approx (F : AdmissibleFamily) {C : ResidueSpace F → ℝ}
    (hC : Measurable C) {u : Set ℝ} (hct : Countable u)
    (hae : ∀ᵐ ω ∂productMeasure F, C ω ∈ u) (hpos : ∀ c ∈ u, 0 < c) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (C_F : ResidueSpace F → ℝ),
      Measurable C_F ∧ DependsOnFinset s C_F ∧
        (Set.range C_F).Finite ∧ (∀ ω, 0 < C_F ω) ∧
          productMeasure F {ω | C ω ≠ C_F ω} < ENNReal.ofReal ε := by
  have := productMeasure_isProbabilityMeasure F
  have hune : u.Nonempty := by
    by_contra hu
    have hempty : {ω : ResidueSpace F | C ω ∈ u} = ∅ := by
      ext ω
      simp [Set.not_nonempty_iff_eq_empty.mp hu]
    have hmeas : MeasurableSet {ω : ResidueSpace F | C ω ∈ u} :=
      hC (Set.Countable.measurableSet (Set.countable_coe_iff.mp hct))
    have htail0 : productMeasure F {ω | C ω ∈ u}ᶜ = 0 := by
      simpa [compl_ofPred] using (ae_iff.mp hae)
    have hone : productMeasure F {ω | C ω ∈ u} = 1 :=
      (prob_compl_eq_zero_iff hmeas).mp htail0
    simp [hempty] at hone
  obtain ⟨vals, hvals_sub, hvals_ne, htail⟩ :=
    exists_finset_vals F hC hct hae ε hε hune
  let n : ℕ := vals.card
  have hnpos : 0 < n := Finset.card_pos.mpr hvals_ne
  let δ : ℝ≥0∞ := ENNReal.ofReal (ε / 2) / n
  have hδpos : 0 < δ :=
    ENNReal.div_pos (ENNReal.ofReal_pos.mpr (half_pos hε)).ne' (ENNReal.natCast_ne_top n)
  have hClevel : ∀ c, MeasurableSet {ω : ResidueSpace F | C ω = c} := fun c =>
    hC (measurableSet_singleton c)
  have hT0 : ∀ c ∈ vals,
      ∃ T, T ∈ measurableCylinders (fun i : ℕ => ZMod (F.d i)) ∧
        productMeasure F (T ∆ {ω | C ω = c}) < δ := by
    intro c hc
    exact exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := productMeasure F) isSetRing_measurableCylinders
      ⟨{univ}, countable_singleton _,
        singleton_subset_iff.mpr
          (univ_mem_measurableCylinders fun i : ℕ => ZMod (F.d i)),
        by simp⟩
      generateFrom_measurableCylinders.symm (hClevel c) hδpos
  let T : ℝ → Set (ResidueSpace F) := fun c =>
    if hc : c ∈ vals then Classical.choose (hT0 c hc) else ∅
  have hTmem : ∀ c ∈ vals, T c ∈ measurableCylinders (fun i : ℕ => ZMod (F.d i)) := by
    intro c hc
    dsimp [T]
    rw [dif_pos hc]
    exact (Classical.choose_spec (hT0 c hc)).1
  have hTδ : ∀ c ∈ vals, productMeasure F (T c ∆ {ω | C ω = c}) < δ := by
    intro c hc
    dsimp [T]
    rw [dif_pos hc]
    exact (Classical.choose_spec (hT0 c hc)).2
  have hTmeas : ∀ c, MeasurableSet (T c) := by
    intro c
    by_cases hc : c ∈ vals
    · exact MeasurableSet.of_mem_measurableCylinders (hTmem c hc)
    · simp [T, hc]
  let c0 : ℝ := vals.min' hvals_ne
  have hc0u : c0 ∈ u := hvals_sub (vals.min'_mem hvals_ne)
  have hc0pos : 0 < c0 := hpos c0 hc0u
  let C_F : ResidueSpace F → ℝ := approxOnList T c0 vals.toList
  have hCFm : Measurable C_F := measurable_approxOnList hTmeas _
  let s : Finset ℕ :=
    Finset.sup vals.attach fun c => measurableCylinders.finset (hTmem c.1 c.2)
  have hTagree : ∀ c ω ω', (∀ i ∈ s, ω i = ω' i) → (ω ∈ T c ↔ ω' ∈ T c) := by
    intro c ω ω' hagree
    by_cases hc : c ∈ vals
    · have hI : measurableCylinders.finset (hTmem c hc) ⊆ s :=
        Finset.le_sup (f := fun d : {x // x ∈ vals} =>
          measurableCylinders.finset (hTmem d.1 d.2))
          (Finset.mem_attach vals ⟨c, hc⟩)
      have heq := measurableCylinders.eq_cylinder (hTmem c hc)
      have hIω := cylinder_mem_of_agree (S := measurableCylinders.set (hTmem c hc))
        fun i hi => hagree i (hI hi)
      rw [heq]
      exact hIω
    · simp [T, hc]
  have hdep : DependsOnFinset s C_F :=
    dependsOnFinset_approxOnList (c0 := c0) hTagree vals.toList
  have hfin : (Set.range C_F).Finite := by
    refine (vals.finite_toSet.union (finite_singleton c0)).subset ?_
    intro y hy
    rcases hy with ⟨ω, rfl⟩
    rcases approxOnList_mem (T := T) (c0 := c0) vals.toList ω with h0 | h
    · exact Or.inr (by simp [C_F, h0])
    · exact Or.inl (by simpa using h)
  have hCFpos : ∀ ω, 0 < C_F ω := by
    intro ω
    refine approxOnList_pos (T := T) (c0 := c0) hc0pos vals.toList ?_ ω
    intro c hc
    have : c ∈ vals := by simpa using hc
    exact hpos c (hvals_sub this)
  have hdisc : productMeasure F {ω | C ω ≠ C_F ω} < ENNReal.ofReal ε := by
    have hsubset :
        {ω : ResidueSpace F | C ω ≠ C_F ω} ⊆
          {ω | C ω ∉ vals} ∪ ⋃ c ∈ vals, T c ∆ {ω | C ω = c} := by
      intro ω hω
      by_cases htailω : C ω ∈ vals
      · refine Or.inr ?_
        by_contra hnone
        have hΔ : ∀ c ∈ vals, ω ∉ T c ∆ {ω' | C ω' = c} := by
          intro c hc hmem
          exact hnone (Set.mem_biUnion hc hmem)
        have hTiff : ∀ c ∈ vals, ω ∈ T c ↔ C ω = c := by
          intro c hc
          have hsym : ω ∉ T c ∆ {ω' | C ω' = c} := hΔ c hc
          constructor
          · intro hT
            by_contra hne
            exact hsym (Or.inl ⟨hT, hne⟩)
          · intro heq
            by_contra hT
            exact hsym (Or.inr ⟨heq, hT⟩)
        have hfold : C_F ω = C ω := by
          refine approxOnList_eq_of (T := T) (c0 := c0) vals.toList (C ω) ω ?_ ?_ ?_
          · simpa using htailω
          · exact (hTiff (C ω) htailω).2 rfl
          · intro d hd hne
            have hd' : d ∈ vals := by simpa using hd
            intro hT
            have : C ω = d := (hTiff d hd').1 hT
            exact hne this.symm
        exact hω hfold.symm
      · exact Or.inl htailω
    have hunion :
        productMeasure F (⋃ c ∈ vals, T c ∆ {ω | C ω = c}) ≤
          ∑ c ∈ vals, productMeasure F (T c ∆ {ω | C ω = c}) :=
      measure_biUnion_finset_le _ _
    have hsumle :
        ∑ c ∈ vals, productMeasure F (T c ∆ {ω | C ω = c}) ≤
          ENNReal.ofReal (ε / 2) := by
      have : ∑ c ∈ vals, productMeasure F (T c ∆ {ω | C ω = c}) ≤ ∑ c ∈ vals, δ :=
        Finset.sum_le_sum fun c hc => (hTδ c hc).le
      have hδsum : ∑ c ∈ vals, δ = ENNReal.ofReal (ε / 2) := by
        simp only [Finset.sum_const, n, nsmul_eq_mul, δ]
        have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
        rw [mul_comm, ENNReal.div_mul_cancel hn0 (ENNReal.natCast_ne_top n)]
      exact this.trans (le_of_eq hδsum)
    have hle :
        productMeasure F {ω | C ω ≠ C_F ω} ≤
          productMeasure F {ω | C ω ∉ vals} +
            productMeasure F (⋃ c ∈ vals, T c ∆ {ω | C ω = c}) :=
      (measure_mono hsubset).trans (measure_union_le _ _)
    have hhalf : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
      congr 1
      ring
    have hsum' :
        productMeasure F {ω | C ω ∉ vals} +
            productMeasure F (⋃ c ∈ vals, T c ∆ {ω | C ω = c}) <
          ENNReal.ofReal ε := by
      have h1 : productMeasure F {ω | C ω ∉ vals} +
            productMeasure F (⋃ c ∈ vals, T c ∆ {ω | C ω = c}) ≤
          productMeasure F {ω | C ω ∉ vals} + ENNReal.ofReal (ε / 2) :=
        add_le_add le_rfl (hunion.trans hsumle)
      have h2 :
          productMeasure F {ω | C ω ∉ vals} + ENNReal.ofReal (ε / 2) <
            ENNReal.ofReal ε := by
        have h2a :=
          ENNReal.add_lt_add_of_lt_of_le ENNReal.ofReal_ne_top htail
            (le_refl (ENNReal.ofReal (ε / 2)))
        exact h2a.trans_eq hhalf
      exact h1.trans_lt h2
    exact hle.trans_lt hsum'
  exact ⟨s, C_F, hCFm, hdep, hfin, hCFpos, hdisc⟩

/-! ### Two-sided invariant conull set -/

noncomputable def zpowersShift (F : AdmissibleFamily) : ℤ → ResidueSpace F → ResidueSpace F
  | Int.ofNat k => (shift F)^[k]
  | Int.negSucc k => (shift_inv F)^[k + 1]

theorem zpowersShift_zero (F : AdmissibleFamily) : zpowersShift F 0 = id :=
  rfl

theorem zpowersShift_measurePreserving (F : AdmissibleFamily) (n : ℤ) :
    MeasurePreserving (zpowersShift F n) (productMeasure F) (productMeasure F) := by
  cases n with
  | ofNat k =>
    simpa [zpowersShift] using (shift_measurePreserving F).iterate k
  | negSucc k =>
    simpa [zpowersShift] using (shift_inv_measurePreserving F).iterate (k + 1)

theorem zpowersShift_shift (F : AdmissibleFamily) (n : ℤ) (ω : ResidueSpace F) :
    zpowersShift F n (shift F ω) = zpowersShift F (n + 1) ω := by
  cases n with
  | ofNat k =>
    simp only [zpowersShift, Int.ofNat_eq_natCast]
    rw [show (k : ℤ) + 1 = Int.ofNat (k + 1) from by simp]
    simp only [zpowersShift]
    rw [Function.iterate_succ_apply]
  | negSucc k =>
    cases k with
    | zero =>
      simp only [zpowersShift]
      exact shift_leftInverse F ω
    | succ k =>
      have hInt : (Int.negSucc (k + 1) : ℤ) + 1 = Int.negSucc k := by
        simp [Int.negSucc_eq]
      rw [hInt]
      change (shift_inv F)^[(k + 1) + 1] (shift F ω) = (shift_inv F)^[k + 1] ω
      rw [Function.iterate_succ_apply (f := shift_inv F) (n := k + 1)]
      rw [shift_leftInverse]

def uInvariantConull (F : AdmissibleFamily) (P : Set (ResidueSpace F)) :
    Set (ResidueSpace F) :=
  ⋂ n : ℤ, zpowersShift F n ⁻¹' P

theorem uInvariantConull_subset {F : AdmissibleFamily} {P : Set (ResidueSpace F)} :
    uInvariantConull F P ⊆ P := by
  intro ω hω
  have := (Set.mem_iInter.mp hω) (0 : ℤ)
  simpa [zpowersShift_zero] using this

theorem uInvariantConull_shift {F : AdmissibleFamily} {P : Set (ResidueSpace F)}
    {ω : ResidueSpace F} (hω : ω ∈ uInvariantConull F P) :
    shift F ω ∈ uInvariantConull F P := by
  rw [uInvariantConull, Set.mem_iInter] at hω ⊢
  intro n
  have := hω (n + 1)
  simpa [zpowersShift_shift] using this

theorem uInvariantConull_shift_iterate {F : AdmissibleFamily} {P : Set (ResidueSpace F)}
    {ω : ResidueSpace F} (hω : ω ∈ uInvariantConull F P) (k : ℕ) :
    (shift F)^[k] ω ∈ uInvariantConull F P := by
  induction k with
  | zero => simpa using hω
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact uInvariantConull_shift ih

theorem uInvariantConull_conull (F : AdmissibleFamily) {P : Set (ResidueSpace F)}
    (hP : MeasurableSet P) (hae : ∀ᵐ ω ∂productMeasure F, ω ∈ P) :
    productMeasure F (uInvariantConull F P)ᶜ = 0 := by
  have := productMeasure_isProbabilityMeasure F
  have hcompl : (uInvariantConull F P)ᶜ = ⋃ n : ℤ, (zpowersShift F n ⁻¹' P)ᶜ := by
    simp [uInvariantConull, compl_iInter]
  rw [hcompl]
  refine measure_iUnion_null fun n => ?_
  have hmp := zpowersShift_measurePreserving F n
  have hpre : (zpowersShift F n ⁻¹' P)ᶜ = zpowersShift F n ⁻¹' Pᶜ := preimage_compl
  rw [hpre]
  have hμ : productMeasure F (zpowersShift F n ⁻¹' Pᶜ) = productMeasure F Pᶜ :=
    hmp.measure_preimage hP.compl.nullMeasurableSet
  rw [hμ]
  exact ae_iff.mp hae

/-! ### One-coordinate Fubini -/

theorem coordMeasure_setOf (F : AdmissibleFamily) (i : ℕ)
    (p : ZMod (F.d i) → Prop) [DecidablePred p] :
    coordMeasure F i {r | p r} =
      ((Finset.univ.filter p).card : ℝ≥0∞) / F.d i := by
  have hset : {r | p r} = (Finset.univ.filter p : Set _) := by
    ext r
    simp
  rw [coordMeasure, uniformOn_univ, hset, Measure.count_apply_finset, ZMod.card]

theorem measurable_coordFibre (F : AdmissibleFamily) (iq : ℕ)
    {s : Set (ResidueSpace F)} (hs : MeasurableSet s) :
    Measurable fun ω : ResidueSpace F =>
      coordMeasure F iq {r | update ω iq r ∈ s} := by
  have hfun :
      (fun ω : ResidueSpace F => coordMeasure F iq {r | update ω iq r ∈ s}) =
        fun ω =>
          ((Finset.univ.filter fun r => update ω iq r ∈ s).card : ℝ≥0∞) / F.d iq := by
    funext ω
    exact coordMeasure_setOf F iq fun r => update ω iq r ∈ s
  rw [hfun]
  have hsum :
      (fun ω : ResidueSpace F =>
          ((Finset.univ.filter fun r => update ω iq r ∈ s).card : ℝ≥0∞)) =
        fun ω => ∑ r : ZMod (F.d iq), s.indicator (fun _ => (1 : ℝ≥0∞)) (update ω iq r) := by
    funext ω
    rw [Finset.card_filter]
    simp [Set.indicator]
  refine Measurable.div_const ?_ _
  rw [hsum]
  exact Finset.measurable_sum Finset.univ fun r _ =>
    (measurable_one.indicator hs).comp measurable_update_left

theorem lintegral_coordFibre_pi (F : AdmissibleFamily) (iq : ℕ) (s : Finset ℕ)
    (u : ∀ i, Set (ZMod (F.d i))) (hu : ∀ i, MeasurableSet (u i)) :
    ∫⁻ ω, coordMeasure F iq {r | update ω iq r ∈ (s : Set ℕ).pi u} ∂productMeasure F =
      productMeasure F ((s : Set ℕ).pi u) := by
  have := productMeasure_isProbabilityMeasure F
  have := coordMeasure_isProbabilityMeasure F iq
  have hpi : MeasurableSet ((s : Set ℕ).pi u) :=
    MeasurableSet.pi (Finset.countable_toSet _) fun i _ => hu i
  by_cases hiq : iq ∈ s
  · let s0 := s.erase iq
    have hs0 : MeasurableSet ((s0 : Set ℕ).pi u) :=
      MeasurableSet.pi (Finset.countable_toSet _) fun i _ => hu i
    have hfun :
        (fun ω : ResidueSpace F =>
            coordMeasure F iq {r | update ω iq r ∈ (s : Set ℕ).pi u}) =
          ((s0 : Set ℕ).pi u).indicator (fun _ => coordMeasure F iq (u iq)) := by
      funext ω
      by_cases hω : ω ∈ (s0 : Set ℕ).pi u
      · have hset : {r : ZMod (F.d iq) | update ω iq r ∈ (s : Set ℕ).pi u} = u iq := by
          ext r
          constructor
          · intro h
            simpa [Function.update_self] using (Set.mem_pi.mp h) iq hiq
          · intro hr
            refine Set.mem_pi.mpr ?_
            intro i hi
            by_cases hieq : i = iq
            · subst hieq
              simpa [Function.update_self] using hr
            · have hi0 : i ∈ s0 := Finset.mem_erase.mpr ⟨hieq, hi⟩
              simpa [Function.update_of_ne hieq] using (Set.mem_pi.mp hω) i hi0
        rw [hset, Set.indicator_of_mem hω]
      · have hset : {r : ZMod (F.d iq) | update ω iq r ∈ (s : Set ℕ).pi u} = ∅ := by
          ext r
          constructor
          · intro hr
            have : ω ∈ (s0 : Set ℕ).pi u := by
              refine Set.mem_pi.mpr ?_
              intro i hi
              have hie := Finset.mem_erase.mp hi
              simpa [Function.update_of_ne hie.1] using (Set.mem_pi.mp hr) i hie.2
            exact hω this
          · intro h
            exact h.elim
        rw [hset, measure_empty, Set.indicator_of_notMem hω]
    rw [hfun, lintegral_indicator_const hs0]
    have hprod :
        productMeasure F ((s : Set ℕ).pi u) =
          productMeasure F ((s0 : Set ℕ).pi u) * coordMeasure F iq (u iq) := by
      simp only [productMeasure]
      rw [Measure.infinitePi_pi (μ := coordMeasure F) (fun i _ => hu i),
        Measure.infinitePi_pi (μ := coordMeasure F) (fun i _ => hu i),
        Finset.prod_erase_mul _ _ hiq]
    rw [hprod, mul_comm]
  · have hfun :
        (fun ω : ResidueSpace F =>
            coordMeasure F iq {r | update ω iq r ∈ (s : Set ℕ).pi u}) =
          ((s : Set ℕ).pi u).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      by_cases hω : ω ∈ (s : Set ℕ).pi u
      · have hset : {r : ZMod (F.d iq) | update ω iq r ∈ (s : Set ℕ).pi u} = univ := by
          ext r
          constructor
          · intro
            trivial
          · intro _ i hi
            have : i ≠ iq := fun h => hiq (h ▸ hi)
            simpa [Function.update_of_ne this] using (Set.mem_pi.mp hω) i hi
        rw [hset, measure_univ, Set.indicator_of_mem hω]
      · have hset : {r : ZMod (F.d iq) | update ω iq r ∈ (s : Set ℕ).pi u} = ∅ := by
          ext r
          constructor
          · intro hr
            have : ω ∈ (s : Set ℕ).pi u := by
              refine Set.mem_pi.mpr ?_
              intro i hi
              have : i ≠ iq := fun h => hiq (h ▸ hi)
              simpa [Function.update_of_ne this] using (Set.mem_pi.mp hr) i hi
            exact hω this
          · intro h
            exact h.elim
        rw [hset, measure_empty, Set.indicator_of_notMem hω]
    rw [hfun, lintegral_indicator_const hpi, one_mul]

theorem lintegral_coordFibre (F : AdmissibleFamily) (iq : ℕ)
    {s : Set (ResidueSpace F)} (hs : MeasurableSet s) :
    ∫⁻ ω, coordMeasure F iq {r | update ω iq r ∈ s} ∂productMeasure F =
      productMeasure F s := by
  have := productMeasure_isProbabilityMeasure F
  refine MeasurableSpace.induction_on_inter
    (m := MeasurableSpace.pi)
    (C := fun t _ =>
      ∫⁻ ω, coordMeasure F iq {r | update ω iq r ∈ t} ∂productMeasure F =
        productMeasure F t)
    (s := squareCylinders fun i => {u : Set (ZMod (F.d i)) | MeasurableSet u})
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      (fun _ => by simp))
    ?empty ?basic ?compl ?iUnion s hs
  · simp
  · intro t ht
    rcases ht with ⟨s, u, hu, rfl⟩
    exact lintegral_coordFibre_pi F iq s u fun i => hu i (mem_univ i)
  · intro t htm ht
    have hf := measurable_coordFibre F iq htm
    have hfun :
        (fun ω : ResidueSpace F => coordMeasure F iq {r | update ω iq r ∈ tᶜ}) =
          fun ω => 1 - coordMeasure F iq {r | update ω iq r ∈ t} := by
      funext ω
      have hms : MeasurableSet {r : ZMod (F.d iq) | update ω iq r ∈ t} :=
        htm.preimage (measurable_update ω)
      rw [show {r : ZMod (F.d iq) | update ω iq r ∈ tᶜ} =
          {r | update ω iq r ∈ t}ᶜ from rfl, prob_compl_eq_one_sub hms]
    rw [hfun, lintegral_sub hf]
    · simp [lintegral_const, measure_univ, ht, prob_compl_eq_one_sub htm]
    · rw [ht]
      exact measure_ne_top _ _
    · exact Filter.Eventually.of_forall fun _ => prob_le_one
  · intro f hdisj hfm hf
    have hfun :
        (fun ω : ResidueSpace F => coordMeasure F iq {r | update ω iq r ∈ ⋃ i, f i}) =
          fun ω => ∑' i, coordMeasure F iq {r | update ω iq r ∈ f i} := by
      funext ω
      have hms i : MeasurableSet {r : ZMod (F.d iq) | update ω iq r ∈ f i} :=
        (hfm i).preimage (measurable_update ω)
      have hdisjr : Pairwise fun i j =>
          Disjoint {r : ZMod (F.d iq) | update ω iq r ∈ f i}
            {r | update ω iq r ∈ f j} := by
        intro i j hij
        refine disjoint_iff_inf_le.mpr ?_
        intro r ⟨hri, hrj⟩
        have : update ω iq r ∈ f i ∩ f j := ⟨hri, hrj⟩
        have hbot : f i ∩ f j = ∅ := (hdisj hij).inter_eq
        exact (hbot ▸ this).elim
      have : {r : ZMod (F.d iq) | update ω iq r ∈ ⋃ i, f i} =
          ⋃ i, {r | update ω iq r ∈ f i} := by
        ext r
        simp
      rw [this, measure_iUnion hdisjr hms]
    rw [hfun, lintegral_tsum fun i => (measurable_coordFibre F iq (hfm i)).aemeasurable]
    simp_rw [hf]
    exact (measure_iUnion hdisj hfm).symm

theorem ae_all_residues_mem_conull (F : AdmissibleFamily) (iq : ℕ)
    {Ωstar : Set (ResidueSpace F)} (hmeas : MeasurableSet Ωstar)
    (_hinv : ∀ ω ∈ Ωstar, shift F ω ∈ Ωstar)
    (hfull : productMeasure F Ωstarᶜ = 0) :
    ∀ᵐ ω ∂productMeasure F, ∀ r : ZMod (F.d iq), update ω iq r ∈ Ωstar := by
  have := productMeasure_isProbabilityMeasure F
  have h0 : ∫⁻ ω, coordMeasure F iq {r | update ω iq r ∈ Ωstarᶜ} ∂productMeasure F = 0 := by
    simpa [hfull] using lintegral_coordFibre F iq hmeas.compl
  have hf := measurable_coordFibre F iq hmeas.compl
  have hae := (lintegral_eq_zero_iff hf).1 h0
  filter_upwards [hae] with ω hω r
  have hzero : coordMeasure F iq {r | update ω iq r ∈ Ωstarᶜ} = 0 := hω
  by_contra hnot
  have hsub : ({r} : Set (ZMod (F.d iq))) ⊆ {r' | update ω iq r' ∈ Ωstarᶜ} := by
    intro x hx
    simp only [mem_singleton_iff] at hx
    subst hx
    exact hnot
  have : coordMeasure F iq {r} ≤ 0 := (measure_mono hsub).trans_eq hzero
  have hpos : coordMeasure F iq {r} ≠ 0 := by
    rw [coordMeasure_singleton]
    simp [d_ne_zero F iq]
  exact hpos (le_zero_iff.mp this)

/-! ### Candidates and first moment -/

noncomputable def candidateTimes (F : AdmissibleFamily) (iq : ℕ) (H : ℕ)
    (ω : ResidueSpace F) : Finset ℕ :=
  (Finset.range H).filter fun j => ∀ i, i ≠ iq → ω i + j ≠ 0

noncomputable def candidateCount (F : AdmissibleFamily) (iq : ℕ) (H : ℕ)
    (ω : ResidueSpace F) : ℕ :=
  (candidateTimes F iq H ω).card

theorem candidateTimes_mem (F : AdmissibleFamily) (iq H : ℕ) (ω : ResidueSpace F) (j : ℕ) :
    j ∈ candidateTimes F iq H ω ↔ j < H ∧ ∀ i, i ≠ iq → ω i + j ≠ 0 := by
  simp [candidateTimes, Finset.mem_filter, Finset.mem_range]

theorem candidateCount_le_H (F : AdmissibleFamily) (iq H : ℕ) (ω : ResidueSpace F) :
    candidateCount F iq H ω ≤ H := by
  simpa [candidateCount, candidateTimes, Finset.card_range] using
    Finset.card_filter_le (Finset.range H)
      (fun j => ∀ i, i ≠ iq → ω i + j ≠ 0)

theorem candidate_event_eq_preimage (F : AdmissibleFamily) (iq : ℕ) (j : ℕ) :
    {ω : ResidueSpace F | ∀ i, i ≠ iq → ω i + j ≠ 0} =
      (shift F)^[j] ⁻¹' {ω | ∀ i, i ≠ iq → ω i ≠ 0} := by
  ext ω
  simp [shift_iterate_apply]

theorem measurable_off_coord (F : AdmissibleFamily) (iq : ℕ) :
    MeasurableSet {ω : ResidueSpace F | ∀ i, i ≠ iq → ω i ≠ 0} := by
  have : {ω : ResidueSpace F | ∀ i, i ≠ iq → ω i ≠ 0} =
      ⋂ i : {i : ℕ // i ≠ iq}, (eval i.1 ⁻¹' ({0} : Set (ZMod (F.d i.1)))ᶜ) := by
    ext ω
    simp [eval]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurable_pi_apply i.1) (measurableSet_singleton 0).compl

theorem measurable_candidate_event (F : AdmissibleFamily) (iq j : ℕ) :
    MeasurableSet {ω : ResidueSpace F | ∀ i, i ≠ iq → ω i + j ≠ 0} := by
  rw [candidate_event_eq_preimage]
  exact ((shift_measurePreserving F).iterate j).measurable (measurable_off_coord F iq)

theorem measurable_candidateCount (F : AdmissibleFamily) (iq H : ℕ) :
    Measurable fun ω : ResidueSpace F => (candidateCount F iq H ω : ℝ≥0∞) := by
  have hfun :
      (fun ω : ResidueSpace F => (candidateCount F iq H ω : ℝ≥0∞)) =
        fun ω => ∑ j ∈ Finset.range H,
          ({ω' : ResidueSpace F | ∀ i, i ≠ iq → ω' i + j ≠ 0}.indicator 1 ω) := by
    funext ω
    simp only [candidateCount, candidateTimes]
    rw [Finset.card_filter]
    simp [Set.indicator, Nat.cast_sum]
  rw [hfun]
  exact Finset.measurable_sum _ fun j _ =>
    measurable_one.indicator (measurable_candidate_event F iq j)

theorem expected_candidateCount (F : AdmissibleFamily) (iq : ℕ) (H : ℕ) :
    ∫⁻ ω, candidateCount F iq H ω ∂productMeasure F =
      H * productMeasure F {ω | ∀ i, i ≠ iq → ω i ≠ 0} := by
  have := productMeasure_isProbabilityMeasure F
  have hfun :
      (fun ω : ResidueSpace F => (candidateCount F iq H ω : ℝ≥0∞)) =
        fun ω => ∑ j ∈ Finset.range H,
          ({ω' : ResidueSpace F | ∀ i, i ≠ iq → ω' i + j ≠ 0}.indicator 1 ω) := by
    funext ω
    simp only [candidateCount, candidateTimes]
    rw [Finset.card_filter]
    simp [Set.indicator]
  rw [hfun, lintegral_finsetSum (Finset.range H) fun j _ =>
    (measurable_one.indicator (measurable_candidate_event F iq j))]
  have hterm : ∀ j ∈ Finset.range H,
      ∫⁻ ω, ({ω' : ResidueSpace F | ∀ i, i ≠ iq → ω' i + j ≠ 0}.indicator 1 ω)
          ∂productMeasure F =
        productMeasure F {ω | ∀ i, i ≠ iq → ω i ≠ 0} := by
    intro j _
    rw [lintegral_indicator_one (measurable_candidate_event F iq j)]
    rw [candidate_event_eq_preimage]
    exact ((shift_measurePreserving F).iterate j).measure_preimage
      (measurable_off_coord F iq).nullMeasurableSet
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, Finset.card_range]

theorem measure_survival_off (F : AdmissibleFamily) (iq : ℕ) :
    productMeasure F {ω | ∀ i, i ≠ iq → ω i ≠ 0} *
        coordMeasure F iq ({0}ᶜ) =
      productMeasure F (survival F) := by
  have := productMeasure_isProbabilityMeasure F
  have hsurv : MeasurableSet (survival F) := survival_measurable F
  have hfun :
      (fun ω : ResidueSpace F => coordMeasure F iq {r | update ω iq r ∈ survival F}) =
        {ω : ResidueSpace F | ∀ i, i ≠ iq → ω i ≠ 0}.indicator
          (fun _ => coordMeasure F iq ({0}ᶜ)) := by
    funext ω
    by_cases hω : ∀ i, i ≠ iq → ω i ≠ 0
    · have hset : {r : ZMod (F.d iq) | update ω iq r ∈ survival F} =
          ({0} : Set (ZMod (F.d iq)))ᶜ := by
        ext r
        constructor
        · intro h hr
          have hiq0 := h iq
          simp [Function.update_self] at hiq0
          simp only [Set.mem_singleton_iff] at hr
          exact hiq0 hr
        · intro hr i
          by_cases hi : i = iq
          · subst hi
            simpa [Function.update_self] using hr
          · simpa [Function.update_of_ne hi] using hω i hi
      have hmem : ω ∈ {ω : ResidueSpace F | ∀ i, i ≠ iq → ω i ≠ 0} := hω
      rw [hset, Set.indicator_of_mem hmem]
    · have hset : {r : ZMod (F.d iq) | update ω iq r ∈ survival F} = ∅ := by
        ext r
        constructor
        · intro hr
          have : ∀ i, i ≠ iq → ω i ≠ 0 := by
            intro i hi h0
            have hri : update ω iq r i ≠ 0 := by
              simpa [survival] using hr i
            simpa [Function.update_of_ne hi, h0] using hri
          exact hω this
        · intro h
          exact h.elim
      have hmem : ω ∉ {ω : ResidueSpace F | ∀ i, i ≠ iq → ω i ≠ 0} := hω
      rw [hset, measure_empty, Set.indicator_of_notMem hmem]
  have hlin := lintegral_coordFibre F iq hsurv
  rw [hfun, lintegral_indicator_const (measurable_off_coord F iq)] at hlin
  rw [← hlin, mul_comm]

theorem measure_survival_off_toReal (F : AdmissibleFamily) (iq : ℕ) :
    (productMeasure F {ω | ∀ i, i ≠ iq → ω i ≠ 0}).toReal =
      rho F / (1 - (F.d iq : ℝ)⁻¹) := by
  have hprod := measure_survival_off F iq
  have hA := measure_survival_toReal F
  have hfac : (coordMeasure F iq ({0}ᶜ)).toReal = 1 - (F.d iq : ℝ)⁻¹ := by
    rw [coordMeasure_compl_zero, ENNReal.toReal_ofReal (survivalFactor_pos F iq).le]
  have hne : 1 - (F.d iq : ℝ)⁻¹ ≠ 0 := (survivalFactor_pos F iq).ne'
  have := congrArg ENNReal.toReal hprod
  rw [ENNReal.toReal_mul, hA, hfac] at this
  exact (eq_div_iff hne).mpr this

theorem expected_candidateCount_toReal (F : AdmissibleFamily) (iq : ℕ) (H : ℕ) :
    (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F).toReal =
      (H : ℝ) * rho F / (1 - (F.d iq : ℝ)⁻¹) := by
  rw [expected_candidateCount, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    measure_survival_off_toReal]
  ring

theorem expected_v_ge (F : AdmissibleFamily) {s : Finset ℕ} {iq : ℕ}
    (hW : 0 < coordPeriod F s) (hq : 8 * coordPeriod F s ≤ F.d iq) :
    let W := coordPeriod F s
    let q := F.d iq
    let H := adaptedWindow W q
    rho F / 8 ≤
      (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F).toReal / q := by
  intro W q H
  have hwin := adaptedWindow_of_unused F hW hq
  have hreal : (q : ℝ) / 8 ≤ H := hwin.2.2.2.2.1
  have hq1 : (1 : ℝ) < q :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) (F.two_le iq))
  have hE := expected_candidateCount_toReal F iq H
  have hval :
      (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F).toReal / q =
        (H : ℝ) / (q - 1) * rho F := by
    rw [hE]
    have hinv : 1 - (q : ℝ)⁻¹ = ((q : ℝ) - 1) / q := by
      field_simp
    rw [hinv]
    field_simp
  have hq1' : (0 : ℝ) < q - 1 := sub_pos.mpr hq1
  have hge : (q : ℝ) / 8 / (q - 1) * rho F ≤ (H : ℝ) / (q - 1) * rho F :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hreal hq1'.le) (rho_pos F).le
  have h8 : rho F / 8 ≤ (q : ℝ) / 8 / (q - 1) * rho F := by
    have hquot : (1 : ℝ) ≤ (q : ℝ) / ((q : ℝ) - 1) :=
      (one_le_div hq1').mpr (by linarith)
    have hsplit : (q : ℝ) / 8 / ((q : ℝ) - 1) = (1 / 8) * ((q : ℝ) / ((q : ℝ) - 1)) := by
      ring
    have h18 : (1 : ℝ) / 8 ≤ (q : ℝ) / 8 / ((q : ℝ) - 1) := by
      rw [hsplit]
      nlinarith [hquot]
    have hdiv : rho F / 8 = (1 / 8) * rho F := by ring
    rw [hdiv]
    exact mul_le_mul_of_nonneg_right h18 (rho_pos F).le
  calc
    rho F / 8 ≤ (q : ℝ) / 8 / (q - 1) * rho F := h8
    _ ≤ (H : ℝ) / (q - 1) * rho F := hge
    _ = (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F).toReal / q := hval.symm

theorem lintegral_candidateCount_le (F : AdmissibleFamily) (iq H : ℕ) :
    ∫⁻ ω, candidateCount F iq H ω ∂productMeasure F ≤ H := by
  have := productMeasure_isProbabilityMeasure F
  calc
    ∫⁻ ω, (candidateCount F iq H ω : ℝ≥0∞) ∂productMeasure F
        ≤ ∫⁻ _ : ResidueSpace F, (H : ℝ≥0∞) ∂productMeasure F :=
      lintegral_mono fun ω => Nat.cast_le.mpr (candidateCount_le_H F iq H ω)
    _ = H := by
      rw [lintegral_const, measure_univ, mul_one]

theorem lintegral_candidateCount_ne_top (F : AdmissibleFamily) (iq H : ℕ) :
    ∫⁻ ω, candidateCount F iq H ω ∂productMeasure F ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top H) (lintegral_candidateCount_le F iq H)

theorem lintegral_q_minus_count_div (F : AdmissibleFamily) (iq H : ℕ)
    (hH : H ≤ F.d iq) :
    ∫⁻ ω, ((F.d iq : ℝ≥0∞) - candidateCount F iq H ω) / F.d iq ∂productMeasure F =
      (1 : ℝ≥0∞) - (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F) / F.d iq := by
  have := productMeasure_isProbabilityMeasure F
  have hmc := measurable_candidateCount F iq H
  have hq0 : (F.d iq : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (d_ne_zero F iq)
  have hqtop : (F.d iq : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hMle : ∀ ω, (candidateCount F iq H ω : ℝ≥0∞) ≤ F.d iq :=
    fun ω => Nat.cast_le.mpr ((candidateCount_le_H F iq H ω).trans hH)
  have hsub :
      ∫⁻ ω, (F.d iq : ℝ≥0∞) - candidateCount F iq H ω ∂productMeasure F =
        (F.d iq : ℝ≥0∞) - ∫⁻ ω, candidateCount F iq H ω ∂productMeasure F := by
    rw [lintegral_sub hmc (lintegral_candidateCount_ne_top F iq H)
        (Filter.Eventually.of_forall hMle), lintegral_const, measure_univ, mul_one]
  have hinvtop : (F.d iq : ℝ≥0∞)⁻¹ ≠ ⊤ := (ENNReal.inv_ne_top).2 hq0
  calc
    ∫⁻ ω, ((F.d iq : ℝ≥0∞) - candidateCount F iq H ω) / F.d iq ∂productMeasure F =
        ∫⁻ ω, ((F.d iq : ℝ≥0∞) - candidateCount F iq H ω) * (F.d iq : ℝ≥0∞)⁻¹
          ∂productMeasure F := by
      simp_rw [div_eq_mul_inv]
    _ = (∫⁻ ω, (F.d iq : ℝ≥0∞) - candidateCount F iq H ω ∂productMeasure F) *
          (F.d iq : ℝ≥0∞)⁻¹ :=
      lintegral_mul_const' _ _ hinvtop
    _ = ((F.d iq : ℝ≥0∞) - ∫⁻ ω, candidateCount F iq H ω ∂productMeasure F) *
          (F.d iq : ℝ≥0∞)⁻¹ := by
      rw [hsub]
    _ = (F.d iq : ℝ≥0∞) * (F.d iq : ℝ≥0∞)⁻¹ -
          (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F) * (F.d iq : ℝ≥0∞)⁻¹ :=
      ENNReal.sub_mul fun _ _ => hinvtop
    _ = (1 : ℝ≥0∞) - (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F) / F.d iq := by
      rw [ENNReal.mul_inv_cancel hq0 hqtop]
      simp [div_eq_mul_inv]

/-! ### One fibre cannot host both good types -/

theorem visitBit_no_deletion (F : AdmissibleFamily) (iq : ℕ) (H : ℕ)
    (ω : ResidueSpace F) (r : ZMod (F.d iq)) (j : ℕ) (hj : j < H)
    (hnd : ∀ k ∈ candidateTimes F iq H ω, r + k ≠ 0) :
    visitBit F (update ω iq r) j =
      if j ∈ candidateTimes F iq H ω then 1 else 0 := by
  rw [visitBit_update]
  by_cases hc : j ∈ candidateTimes F iq H ω
  · have hr : r + j ≠ 0 := hnd j hc
    have hrest : ∀ i, i ≠ iq → ω i + j ≠ 0 := (candidateTimes_mem F iq H ω j).1 hc |>.2
    rw [if_pos ⟨hr, hrest⟩, if_pos hc]
  · rw [if_neg, if_neg hc]
    intro ⟨_hr, hrest⟩
    exact hc ((candidateTimes_mem F iq H ω j).2 ⟨hj, hrest⟩)

theorem visitBit_one_deletion (F : AdmissibleFamily) (iq : ℕ) (H : ℕ)
    (ω : ResidueSpace F) (r : ZMod (F.d iq)) {k : ℕ}
    (hk : k ∈ candidateTimes F iq H ω) (hrk : r + k = 0)
    (huniq : ∀ j ∈ candidateTimes F iq H ω, r + j = 0 → j = k) (j : ℕ)
    (hj : j < H) :
    visitBit F (update ω iq r) j =
      if j ∈ candidateTimes F iq H ω ∧ j ≠ k then 1 else 0 := by
  rw [visitBit_update]
  by_cases hc : j ∈ candidateTimes F iq H ω
  · by_cases hjk : j = k
    · subst hjk
      rw [if_neg (fun ⟨h0, _⟩ => (hrk ▸ h0) rfl),
        if_neg (fun h => h.2 rfl)]
    · have hr : r + j ≠ 0 := fun h => hjk (huniq j hc h)
      have hrest : ∀ i, i ≠ iq → ω i + j ≠ 0 := (candidateTimes_mem F iq H ω j).1 hc |>.2
      rw [if_pos ⟨hr, hrest⟩, if_pos ⟨hc, hjk⟩]
  · rw [if_neg, if_neg]
    · exact fun h => hc h.1
    · intro ⟨_hr, hrest⟩
      exact hc ((candidateTimes_mem F iq H ω j).2 ⟨hj, hrest⟩)

theorem candidate_residues_distinct (F : AdmissibleFamily) (iq : ℕ) {H : ℕ}
    (hH : H < F.d iq) (ω : ResidueSpace F) {j k : ℕ}
    (hj : j ∈ candidateTimes F iq H ω) (hk : k ∈ candidateTimes F iq H ω)
    (heq : (j : ZMod (F.d iq)) = k) : j = k := by
  have hjH : j < H := (candidateTimes_mem F iq H ω j).1 hj |>.1
  have hkH : k < H := (candidateTimes_mem F iq H ω k).1 hk |>.1
  have : j % F.d iq = k % F.d iq := by
    have := congrArg ZMod.val heq
    simpa [ZMod.val_natCast] using this
  exact candidate_residues_injective hH hjH hkH this

theorem candidate_neg_injOn (F : AdmissibleFamily) (iq : ℕ) {H : ℕ}
    (hH : H < F.d iq) (ω : ResidueSpace F) :
    Set.InjOn (fun j : ℕ => (-(Nat.cast j : ZMod (F.d iq)))) (candidateTimes F iq H ω) := by
  intro j hj k hk heq
  have hjk : (j : ZMod (F.d iq)) = k := by
    simpa using congrArg (fun x : ZMod (F.d iq) => -x) heq
  exact candidate_residues_distinct F iq hH ω hj hk hjk

theorem deletion_image_card (F : AdmissibleFamily) (iq : ℕ) {H : ℕ}
    (hH : H < F.d iq) (ω : ResidueSpace F) :
    ((candidateTimes F iq H ω).image
        (fun j : ℕ => (-(Nat.cast j : ZMod (F.d iq))))).card =
      candidateCount F iq H ω :=
  Finset.card_image_of_injOn (candidate_neg_injOn F iq hH ω)

theorem eq_neg_of_add_zero {q : ℕ} [NeZero q] (r : ZMod q) (j : ℕ)
    (h : r + j = 0) : r = - (j : ZMod q) := by
  have h' := congrArg (fun x : ZMod q => x + (-(j : ZMod q))) h
  simpa [add_assoc, add_neg_cancel, add_zero] using h'

theorem mem_deletion_image (F : AdmissibleFamily) (iq H : ℕ) (ω : ResidueSpace F)
    (r : ZMod (F.d iq)) :
    r ∈ (candidateTimes F iq H ω).image
        (fun j : ℕ => (-(Nat.cast j : ZMod (F.d iq)))) ↔
      ∃ j ∈ candidateTimes F iq H ω, r + j = 0 := by
  constructor
  · intro hr
    rcases Finset.mem_image.mp hr with ⟨j, hj, hrj⟩
    refine ⟨j, hj, ?_⟩
    rw [← hrj]
    exact neg_add_cancel _
  · intro ⟨j, hj, hj0⟩
    exact Finset.mem_image.mpr ⟨j, hj, (eq_neg_of_add_zero r j hj0).symm⟩

theorem exists_hit_of_not_avoid (F : AdmissibleFamily) (iq H : ℕ)
    (ω : ResidueSpace F) (r : ZMod (F.d iq))
    (h : ¬ ∀ j ∈ candidateTimes F iq H ω, r + j ≠ 0) :
    ∃ j ∈ candidateTimes F iq H ω, r + j = 0 := by
  push Not at h
  simpa using h

theorem noDeletion_eq_sdiff (F : AdmissibleFamily) (iq H : ℕ) (ω : ResidueSpace F) :
    (Finset.univ.filter fun r : ZMod (F.d iq) =>
        ∀ j ∈ candidateTimes F iq H ω, r + j ≠ 0) =
      Finset.univ \
        ((candidateTimes F iq H ω).image
          fun j : ℕ => (-(Nat.cast j : ZMod (F.d iq)))) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    mem_deletion_image]
  constructor
  · intro hnd hdel
    rcases hdel with ⟨j, hj, hj0⟩
    exact hnd j hj hj0
  · intro hnot j hj hj0
    exact hnot ⟨j, hj, hj0⟩

theorem noDeletion_card (F : AdmissibleFamily) (iq : ℕ) {H : ℕ}
    (hH : H < F.d iq) (ω : ResidueSpace F) :
    (Finset.univ.filter fun r : ZMod (F.d iq) =>
        ∀ j ∈ candidateTimes F iq H ω, r + j ≠ 0).card =
      F.d iq - candidateCount F iq H ω := by
  rw [noDeletion_eq_sdiff, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, ZMod.card, deletion_image_card F iq hH ω]

theorem one_step_rec_of_star {F : AdmissibleFamily} {b : ℕ} {Q : ℝ}
    {C : ResidueSpace F → ℝ} {P : Set (ResidueSpace F)}
    (hP : P = {ω | 0 < C ω ∧
      C (shift F ω) =
        (b : ℝ) ^ (if ω ∈ survival F then 1 else 0) * C ω - Q})
    {ω : ResidueSpace F} (hω : ω ∈ uInvariantConull F P) (k : ℕ) :
    0 < C ((shift F)^[k] ω) ∧
      C ((shift F)^[k + 1] ω) =
        (b : ℝ) ^ visitBit F ((shift F)^[k] ω) 0 *
          C ((shift F)^[k] ω) - Q := by
  have hmem := uInvariantConull_shift_iterate (P := P) hω k
  have hPω : (shift F)^[k] ω ∈ P := uInvariantConull_subset hmem
  rw [hP] at hPω
  refine ⟨hPω.1, ?_⟩
  simpa [visitBit_zero, Function.iterate_succ_apply'] using hPω.2

theorem orbit_eq_of_star {F : AdmissibleFamily} {b : ℕ} {Q : ℝ}
    {C : ResidueSpace F → ℝ} {P : Set (ResidueSpace F)}
    (hP : P = {ω | 0 < C ω ∧
      C (shift F ω) =
        (b : ℝ) ^ (if ω ∈ survival F then 1 else 0) * C ω - Q})
    {ω : ResidueSpace F} (hω : ω ∈ uInvariantConull F P) (n : ℕ) :
    C ((shift F)^[n] ω) = orbitAffinePath F b Q C ω n := by
  refine orbitAffinePath_succ_of_rec F b Q C ω n fun k hk => ?_
  have hk' := one_step_rec_of_star (C := C) (P := P) hP hω k
  have : visitBit F ((shift F)^[k] ω) 0 = visitBit F ω k := rfl
  simpa [this] using hk'.2

theorem fibre_cannot_host_both {F : AdmissibleFamily} {b : ℕ} (_hb : 2 ≤ b) {Q : ℝ}
    {C C_F : ResidueSpace F → ℝ} {s : Finset ℕ} {iq H : ℕ}
    {Ωstar G : Set (ResidueSpace F)} {ω : ResidueSpace F}
    {rPlus rMinus : ZMod (F.d iq)} {k : ℕ}
    (hb1 : (1 : ℝ) < b)
    (_hH : H < F.d iq) (hiq : iq ∉ s)
    (hdep : DependsOnFinset s C_F)
    (hP : Ωstar = uInvariantConull F {τ | 0 < C τ ∧
      C (shift F τ) =
        (b : ℝ) ^ (if τ ∈ survival F then 1 else 0) * C τ - Q})
    (hG : G = Ωstar ∩ {τ | C τ = C_F τ} ∩
      {τ | C ((shift F)^[H] τ) = C_F τ})
    (_hΩ : ∀ r : ZMod (F.d iq), update ω iq r ∈ Ωstar)
    (hplus : update ω iq rPlus ∈ G) (hminus : update ω iq rMinus ∈ G)
    (hk : k ∈ candidateTimes F iq H ω)
    (hnd : ∀ j ∈ candidateTimes F iq H ω, rPlus + j ≠ 0)
    (hrm : rMinus + k = 0)
    (huniq : ∀ j ∈ candidateTimes F iq H ω, rMinus + j = 0 → j = k) :
    False := by
  let P : Set (ResidueSpace F) := {τ | 0 < C τ ∧
    C (shift F τ) =
      (b : ℝ) ^ (if τ ∈ survival F then 1 else 0) * C τ - Q}
  have hPeq : Ωstar = uInvariantConull F P := hP
  have hplusΩ : update ω iq rPlus ∈ Ωstar := (hG ▸ hplus).1.1
  have hminusΩ : update ω iq rMinus ∈ Ωstar := (hG ▸ hminus).1.1
  have hCplus : C (update ω iq rPlus) = C_F (update ω iq rPlus) := (hG ▸ hplus).1.2
  have hCminus : C (update ω iq rMinus) = C_F (update ω iq rMinus) := (hG ▸ hminus).1.2
  have hCFeq : C_F (update ω iq rPlus) = C_F (update ω iq rMinus) := by
    rw [dependsOnFinset_update hdep hiq, dependsOnFinset_update hdep hiq]
  have hC0 : C (update ω iq rPlus) = C (update ω iq rMinus) := by
    rw [hCplus, hCminus, hCFeq]
  have hEndPlus : C ((shift F)^[H] (update ω iq rPlus)) = C_F (update ω iq rPlus) :=
    (hG ▸ hplus).2
  have hEndMinus : C ((shift F)^[H] (update ω iq rMinus)) = C_F (update ω iq rMinus) :=
    (hG ▸ hminus).2
  have hEnd : C ((shift F)^[H] (update ω iq rPlus)) =
      C ((shift F)^[H] (update ω iq rMinus)) := by
    rw [hEndPlus, hEndMinus, hCFeq]
  have hkH : k < H := (candidateTimes_mem F iq H ω k).1 hk |>.1
  have hagree : ∀ j < H, j ≠ k →
      visitBit F (update ω iq rPlus) j = visitBit F (update ω iq rMinus) j := by
    intro j hj hne
    rw [visitBit_no_deletion F iq H ω rPlus j hj hnd,
      visitBit_one_deletion F iq H ω rMinus hk hrm huniq j hj]
    by_cases hc : j ∈ candidateTimes F iq H ω
    · simp [hc, hne]
    · simp [hc]
  have hplus1 : visitBit F (update ω iq rPlus) k = 1 := by
    rw [visitBit_no_deletion F iq H ω rPlus k hkH hnd]
    simp [hk]
  have hminus0 : visitBit F (update ω iq rMinus) k = 0 := by
    rw [visitBit_one_deletion F iq H ω rMinus hk hrm huniq k hkH]
    simp
  have hpathPlus := orbit_eq_of_star (C := C) (P := P) rfl (hPeq ▸ hplusΩ) H
  have hpathMinus := orbit_eq_of_star (C := C) (P := P) rfl (hPeq ▸ hminusΩ) H
  have hpathPlusk := orbit_eq_of_star (C := C) (P := P) rfl (hPeq ▸ hplusΩ) k
  have hCpre : 0 < affinePath (b : ℝ) Q (visitBit F (update ω iq rPlus))
      (C (update ω iq rPlus)) k := by
    have hpos := (one_step_rec_of_star (C := C) (P := P) rfl (hPeq ▸ hplusΩ) k).1
    rw [hpathPlusk, orbitAffinePath] at hpos
    exact hpos
  have hlt :=
    affine_flip_diff_pos (b : ℝ) Q
      (visitBit F (update ω iq rPlus)) (visitBit F (update ω iq rMinus))
      (C (update ω iq rPlus)) hb1 hCpre hkH
      (fun j hj hne => hagree j hj hne) hplus1 hminus0
  have hEndPath :
      affinePath (b : ℝ) Q (visitBit F (update ω iq rPlus)) (C (update ω iq rPlus)) H =
        affinePath (b : ℝ) Q (visitBit F (update ω iq rMinus)) (C (update ω iq rPlus)) H := by
    have h := hEnd
    rw [hpathPlus, hpathMinus, orbitAffinePath, orbitAffinePath] at h
    rw [hC0] at h
    rw [hC0]
    exact h
  exact (not_le_of_gt hlt) hEndPath.le

/-! ### Theorem 3.3 -/

theorem no_countable_positive_affine_carry
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) {Q : ℝ} (hQ : 0 < Q)
    {C : ResidueSpace F → ℝ} (hCm : Measurable C)
    (hCpos : ∀ᵐ ω ∂productMeasure F, 0 < C ω)
    (hcount : ∃ u : Set ℝ, Countable u ∧ ∀ᵐ ω ∂productMeasure F, C ω ∈ u)
    (hrec : ∀ᵐ ω ∂productMeasure F,
      C (shift F ω) =
        (b : ℝ) ^ (if ω ∈ survival F then 1 else 0) * C ω - Q) :
    False := by
  have := productMeasure_isProbabilityMeasure F
  have hρ := rho_pos F
  let ε : ℝ := rho F / 32
  have hε : 0 < ε := div_pos hρ (by norm_num)
  have hε8 : 2 * ε < rho F / 8 := by
    change 2 * (rho F / 32) < rho F / 8
    have h16 : 2 * (rho F / 32) = rho F / 16 := by ring
    have hlt : rho F / 16 < rho F / 8 :=
      div_lt_div_of_pos_left hρ (by norm_num : (0 : ℝ) < 8) (by norm_num : (8 : ℝ) < 16)
    linarith
  obtain ⟨u, hct, hae⟩ := hcount
  let u' : Set ℝ := {c | c ∈ u ∧ 0 < c}
  have hct' : Countable u' :=
    (Set.Countable.mono (fun _ hc => hc.1) (Set.countable_coe_iff.mp hct)).to_subtype
  have hae' : ∀ᵐ ω ∂productMeasure F, C ω ∈ u' := by
    filter_upwards [hCpos, hae] with ω hpos hu
    exact ⟨hu, hpos⟩
  have hpos' : ∀ c ∈ u', 0 < c := fun _ hc => hc.2
  obtain ⟨s, C_F, hCFm, hdep, -, hCFpos, happx⟩ :=
    exists_exact_cylinder_approx F hCm hct' hae' hpos' ε hε
  let W := coordPeriod F s
  obtain ⟨iq, hiq, hq⟩ := exists_unused_large_index F s
  have hWpos : 0 < W := coordPeriod_pos F s
  have hwin := adaptedWindow_of_unused F hWpos hq
  let q := F.d iq
  let H := adaptedWindow W q
  have hWdvd : W ∣ H := hwin.1
  have hHlt : H < q := hwin.2.1
  have h4H : 4 * H ≤ q := hwin.2.2.2.1
  have hper : C_F ∘ (shift F)^[H] = C_F :=
    dependsOnFinset_periodic (fun i hi => (d_dvd_coordPeriod F hi).trans hWdvd) hdep
  let P : Set (ResidueSpace F) :=
    {ω | 0 < C ω ∧
      C (shift F ω) =
        (b : ℝ) ^ (if ω ∈ survival F then 1 else 0) * C ω - Q}
  have hPmeas : MeasurableSet P := by
    have hposS : MeasurableSet {ω : ResidueSpace F | 0 < C ω} :=
      hCm measurableSet_Ioi
    have hexp : Measurable fun ω : ResidueSpace F =>
        (b : ℝ) ^ (if ω ∈ survival F then 1 else 0) := by
      have hite : Measurable fun ω : ResidueSpace F =>
          if ω ∈ survival F then (b : ℝ) ^ 1 else (b : ℝ) ^ 0 :=
        Measurable.ite (survival_measurable F) measurable_const measurable_const
      convert hite using 1
      ext ω
      split_ifs <;> rfl
    have hrhs : Measurable fun ω : ResidueSpace F =>
        (b : ℝ) ^ (if ω ∈ survival F then 1 else 0) * C ω - Q :=
      (hexp.mul hCm).sub measurable_const
    exact hposS.inter (measurableSet_eq_fun (hCm.comp (shift_measurable F)) hrhs)
  have hPae : ∀ᵐ ω ∂productMeasure F, ω ∈ P := by
    filter_upwards [hCpos, hrec] with ω hpos hrec
    exact ⟨hpos, hrec⟩
  let Ωstar : Set (ResidueSpace F) := uInvariantConull F P
  have hΩmeas : MeasurableSet Ωstar :=
    MeasurableSet.iInter fun n =>
      (zpowersShift_measurePreserving F n).measurable hPmeas
  have hΩ0 : productMeasure F Ωstarᶜ = 0 := uInvariantConull_conull F hPmeas hPae
  have hΩinv : ∀ ω ∈ Ωstar, shift F ω ∈ Ωstar := fun ω hω => uInvariantConull_shift hω
  let E1 : Set (ResidueSpace F) := {ω | C ω = C_F ω}
  have hE1 : MeasurableSet E1 := measurableSet_eq_fun hCm hCFm
  have hE1μ : productMeasure F E1ᶜ < ENNReal.ofReal ε := by
    simpa [E1, compl_ofPred] using happx
  let E2 : Set (ResidueSpace F) := {ω | C ((shift F)^[H] ω) = C_F ω}
  have hE2eq : E2 = (shift F)^[H] ⁻¹' E1 := by
    ext ω
    have hperω : C_F ((shift F)^[H] ω) = C_F ω := congrFun hper ω
    simp [E2, E1, hperω]
  have hE2μ : productMeasure F E2ᶜ < ENNReal.ofReal ε := by
    have : E2ᶜ = (shift F)^[H] ⁻¹' E1ᶜ := by
      rw [hE2eq, preimage_compl]
    rw [this, ((shift_measurePreserving F).iterate H).measure_preimage hE1.compl.nullMeasurableSet]
    exact hE1μ
  let G : Set (ResidueSpace F) := Ωstar ∩ E1 ∩ E2
  have hGmeas : MeasurableSet G := hΩmeas.inter hE1 |>.inter (by
    rw [hE2eq]
    exact ((shift_measurePreserving F).iterate H).measurable hE1)
  have hGge : 1 - ENNReal.ofReal (2 * ε) < productMeasure F G := by
    have hGc : Gᶜ ⊆ Ωstarᶜ ∪ E1ᶜ ∪ E2ᶜ := by
      intro ω hω
      simp [G, mem_union, mem_compl_iff] at hω ⊢
      tauto
    have hle : productMeasure F Gᶜ ≤
        productMeasure F Ωstarᶜ + productMeasure F E1ᶜ + productMeasure F E2ᶜ := by
      calc
        productMeasure F Gᶜ ≤ productMeasure F (Ωstarᶜ ∪ E1ᶜ ∪ E2ᶜ) :=
          measure_mono hGc
        _ ≤ productMeasure F (Ωstarᶜ ∪ E1ᶜ) + productMeasure F E2ᶜ :=
          measure_union_le _ _
        _ ≤ productMeasure F Ωstarᶜ + productMeasure F E1ᶜ + productMeasure F E2ᶜ :=
          add_le_add (measure_union_le Ωstarᶜ E1ᶜ)
            (le_refl (productMeasure F E2ᶜ))
    have hsum : productMeasure F Ωstarᶜ + productMeasure F E1ᶜ + productMeasure F E2ᶜ <
        ENNReal.ofReal (2 * ε) := by
      rw [hΩ0, zero_add]
      have : ENNReal.ofReal ε + ENNReal.ofReal ε = ENNReal.ofReal (2 * ε) := by
        rw [← ENNReal.ofReal_add hε.le hε.le]
        congr 1
        ring
      exact this ▸ ENNReal.add_lt_add hE1μ hE2μ
    have thisGc : productMeasure F Gᶜ < ENNReal.ofReal (2 * ε) := hle.trans_lt hsum
    have h2le : ENNReal.ofReal (2 * ε) ≤ 1 := by
      refine ENNReal.ofReal_le_one.mpr ?_
      have hρ1 := rho_le_one F
      have : 2 * ε = rho F / 16 := by
        change 2 * (rho F / 32) = rho F / 16
        ring
      have : rho F / 16 ≤ 1 :=
        (div_le_one (by norm_num : (0 : ℝ) < 16)).mpr (by linarith [hρ1])
      linarith
    have hsumG : productMeasure F G + productMeasure F Gᶜ = 1 := by
      rw [prob_compl_eq_one_sub (μ := productMeasure F) hGmeas]
      exact add_tsub_cancel_of_le (prob_le_one (μ := productMeasure F) (s := G))
    have hltadd : (1 : ℝ≥0∞) < productMeasure F G + ENNReal.ofReal (2 * ε) := by
      have hadd := ENNReal.add_lt_add_left (measure_ne_top (productMeasure F) G) thisGc
      rwa [hsumG] at hadd
    exact ENNReal.sub_lt_of_lt_add h2le hltadd
  have hfib := ae_all_residues_mem_conull F iq hΩmeas hΩinv hΩ0
  have hbound :
      ∀ᵐ ω ∂productMeasure F,
        coordMeasure F iq {r | update ω iq r ∈ G} ≤
          (q - candidateCount F iq H ω : ℝ≥0∞) / q := by
    filter_upwards [hfib] with ω hΩ
    have hΩr : ∀ r : ZMod (F.d iq), update ω iq r ∈ Ωstar := hΩ
    have hMle : candidateCount F iq H ω ≤ H := candidateCount_le_H F iq H ω
    have h2M : 2 * candidateCount F iq H ω ≤ q := by
      have h2H : 2 * H ≤ q := by
        have : 2 * H ≤ 4 * H := by omega
        exact this.trans h4H
      exact (Nat.mul_le_mul_left 2 hMle).trans h2H
    let good : Finset (ZMod q) :=
      Finset.univ.filter fun r => update ω iq r ∈ G
    have hcle : good.card ≤ q - candidateCount F iq H ω := by
      by_cases hboth :
          (∃ rPlus : ZMod q, update ω iq rPlus ∈ G ∧
              ∀ j ∈ candidateTimes F iq H ω, rPlus + j ≠ 0) ∧
          (∃ rMinus : ZMod q, ∃ k ∈ candidateTimes F iq H ω,
              rMinus + k = 0 ∧ update ω iq rMinus ∈ G)
      · rcases hboth with ⟨⟨rPlus, hGp, hnd⟩, ⟨rMinus, k, hk, hrm, hGm⟩⟩
        have huniq : ∀ j ∈ candidateTimes F iq H ω, rMinus + j = 0 → j = k := by
          intro j hj hj0
          have : (j : ZMod q) = k := by
            have : rMinus + j = rMinus + k := by simp [hj0, hrm]
            exact add_right_injective rMinus this
          exact candidate_residues_distinct F iq hHlt ω hj hk this
        have := fibre_cannot_host_both (C := C) (C_F := C_F) (s := s) (Ωstar := Ωstar)
          (G := G) (ω := ω) hb (one_le_b hb) hHlt hiq hdep
          (by rfl) (by rfl) hΩr hGp hGm hk hnd hrm huniq
        exact this.elim
      · have hMle' : candidateCount F iq H ω ≤ q - candidateCount F iq H ω := by
          omega
        by_cases hplusEx :
            ∃ rPlus : ZMod q, update ω iq rPlus ∈ G ∧
              ∀ j ∈ candidateTimes F iq H ω, rPlus + j ≠ 0
        · have hnoMinus : ¬ ∃ rMinus : ZMod q, ∃ k ∈ candidateTimes F iq H ω,
              rMinus + k = 0 ∧ update ω iq rMinus ∈ G := by
            intro h
            exact hboth ⟨hplusEx, h⟩
          let noDel : Finset (ZMod q) :=
            Finset.univ.filter fun r =>
              ∀ j ∈ candidateTimes F iq H ω, r + j ≠ 0
          have hndcard : noDel.card = q - candidateCount F iq H ω :=
            noDeletion_card F iq hHlt ω
          have hsubsetg : good ⊆ noDel := by
            intro r hg
            simp only [good, noDel, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
            intro j hj hj0
            exact hnoMinus ⟨r, j, hj, hj0, hg⟩
          exact (Finset.card_le_card hsubsetg).trans (le_of_eq hndcard)
        · let oneDel : Finset (ZMod q) :=
            (candidateTimes F iq H ω).image
              fun j : ℕ => (-(Nat.cast j : ZMod q))
          have hcardDel : oneDel.card = candidateCount F iq H ω :=
            deletion_image_card F iq hHlt ω
          have hsubsetg : good ⊆ oneDel := by
            intro r hg
            have hnot : ¬ ∀ j ∈ candidateTimes F iq H ω, r + j ≠ 0 := by
              intro hnd
              exact hplusEx ⟨r, by
                simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hg
                exact hg, hnd⟩
            exact (mem_deletion_image F iq H ω r).mpr
              (exists_hit_of_not_avoid F iq H ω r hnot)
          exact (Finset.card_le_card hsubsetg).trans (le_of_eq hcardDel) |>.trans hMle'
    have hs : {r : ZMod q | update ω iq r ∈ G} = (good : Set _) := by
      ext r
      simp [good]
    rw [hs, coordMeasure, uniformOn_univ, Measure.count_apply_finset, ZMod.card]
    have hcast : ((q - candidateCount F iq H ω : ℕ) : ℝ≥0∞) =
        (q : ℝ≥0∞) - (candidateCount F iq H ω : ℝ≥0∞) := by
      have hle : candidateCount F iq H ω ≤ q :=
        Nat.le_of_lt (lt_of_le_of_lt hMle hHlt)
      have hqeq : (q : ℝ≥0∞) =
          ↑(q - candidateCount F iq H ω) + (candidateCount F iq H ω : ℝ≥0∞) := by
        rw [← Nat.cast_add, Nat.sub_add_cancel hle]
      exact (ENNReal.sub_eq_of_eq_add (ENNReal.natCast_ne_top _) hqeq).symm
    rw [← hcast]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcle) (q : ℝ≥0∞)
  have hμG :
      productMeasure F G ≤
        ∫⁻ ω, (q - candidateCount F iq H ω : ℝ≥0∞) / q ∂productMeasure F := by
    have hlin := lintegral_coordFibre F iq hGmeas
    rw [← hlin]
    exact lintegral_mono_ae hbound
  have hident :
      ∫⁻ ω, (q - candidateCount F iq H ω : ℝ≥0∞) / q ∂productMeasure F =
        (1 : ℝ≥0∞) - (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F) / q :=
    lintegral_q_minus_count_div F iq H hHlt.le
  have hμG' : productMeasure F G ≤
      (1 : ℝ≥0∞) - (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F) / q :=
    hμG.trans (le_of_eq hident)
  have hμGreal : (productMeasure F G).toReal ≤
      1 - (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F).toReal / q := by
    have hne : ((1 : ℝ≥0∞) -
        (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F) / q) ≠ ⊤ :=
      ENNReal.sub_ne_top ENNReal.one_ne_top
    have hle := ENNReal.toReal_mono hne hμG'
    have hdivle :
        (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F) / q ≤ 1 := by
      have hMint : ∫⁻ ω, candidateCount F iq H ω ∂productMeasure F ≤ q :=
        (lintegral_candidateCount_le F iq H).trans (Nat.cast_le.mpr hHlt.le)
      exact (ENNReal.div_le_iff_le_mul
        (Or.inl (Nat.cast_ne_zero.mpr (d_ne_zero F iq)))
        (Or.inl (ENNReal.natCast_ne_top q))).2 (by simpa using hMint)
    have hr : ((1 : ℝ≥0∞) -
        (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F) / q).toReal =
        1 - (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F).toReal / q := by
      rw [ENNReal.toReal_sub_of_le hdivle ENNReal.one_ne_top, ENNReal.toReal_div,
        ENNReal.toReal_one, ENNReal.toReal_natCast]
    exact hle.trans (le_of_eq hr)
  have hEv :
      rho F / 8 ≤ (∫⁻ ω, candidateCount F iq H ω ∂productMeasure F).toReal / q :=
    expected_v_ge F hWpos hq
  have hGupper : (productMeasure F G).toReal ≤ 1 - rho F / 8 :=
    hμGreal.trans (sub_le_sub_left hEv 1)
  have hGlower : 1 - 2 * ε < (productMeasure F G).toReal := by
    have hρ1 := rho_le_one F
    have h2εle1 : 2 * ε ≤ 1 := by
      have htwo : 2 * ε = rho F / 16 := by
        change 2 * (rho F / 32) = rho F / 16
        ring
      have : rho F / 16 ≤ 1 :=
        (div_le_one (by norm_num : (0 : ℝ) < 16)).mpr (by linarith [hρ1])
      linarith
    have h2εle : ENNReal.ofReal (2 * ε) ≤ 1 := ENNReal.ofReal_le_one.mpr h2εle1
    have hlt := (ENNReal.toReal_lt_toReal (ENNReal.sub_ne_top ENNReal.one_ne_top)
      (measure_ne_top _ _)).2 hGge
    rw [ENNReal.toReal_sub_of_le h2εle ENNReal.one_ne_top, ENNReal.toReal_one,
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε.le)] at hlt
    exact hlt
  linarith [hGlower, hGupper, hε8]

theorem no_positive_integer_affine_carry
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) {Q : ℝ} (hQ : 0 < Q)
    {C : ResidueSpace F → ℝ} (hCm : Measurable C)
    (hCpos : ∀ᵐ ω ∂productMeasure F, 0 < C ω)
    (hint : ∀ᵐ ω ∂productMeasure F, ∃ n : ℕ, C ω = n)
    (hrec : ∀ᵐ ω ∂productMeasure F,
      C (shift F ω) =
        (b : ℝ) ^ (if ω ∈ survival F then 1 else 0) * C ω - Q) :
    False := by
  refine no_countable_positive_affine_carry F hb hQ hCm hCpos ?_ hrec
  refine ⟨Set.range (Nat.cast : ℕ → ℝ),
    (Set.countable_range (Nat.cast : ℕ → ℝ)).to_subtype, ?_⟩
  filter_upwards [hint] with ω hω
  rcases hω with ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

/-! ### 7.9 Gap tail `T` on `A` (paper (2.3)) -/

set_option maxHeartbeats 400000

theorem firstHitTime_spec {F : AdmissibleFamily} {ω : ResidueSpace F}
    (hhit : {n : ℕ | (shift F)^[n] ω ∈ survival F}.Nonempty) :
    (shift F)^[firstHitTime F ω] ω ∈ survival F ∧
      ∀ k, k < firstHitTime F ω → (shift F)^[k] ω ∉ survival F := by
  have hmem := Nat.sInf_mem hhit
  refine ⟨hmem, ?_⟩
  intro k hk hkA
  have : firstHitTime F ω ≤ k := Nat.sInf_le hkA
  omega

theorem firstHitTime_pos_of_not_mem {F : AdmissibleFamily} {ω : ResidueSpace F}
    (hA : ω ∉ survival F)
    (hhit : {n : ℕ | (shift F)^[n] ω ∈ survival F}.Nonempty) :
    0 < firstHitTime F ω := by
  have hspec := firstHitTime_spec (F := F) hhit
  by_contra hle
  have h0 : firstHitTime F ω = 0 := Nat.eq_zero_of_not_pos hle
  rw [h0, iterate_zero_apply] at hspec
  exact hA hspec.1

theorem firstHitTime_shift_of_not_mem {F : AdmissibleFamily} {ω : ResidueSpace F}
    (hA : ω ∉ survival F)
    (hhit : {n : ℕ | (shift F)^[n] ω ∈ survival F}.Nonempty) :
    firstHitTime F (shift F ω) = firstHitTime F ω - 1 := by
  have htpos := firstHitTime_pos_of_not_mem (F := F) hA hhit
  have hspec := firstHitTime_spec (F := F) hhit
  have hland :
      (shift F)^[firstHitTime F ω - 1] (shift F ω) ∈ survival F := by
    have hsucc : firstHitTime F ω - 1 + 1 = firstHitTime F ω :=
      Nat.sub_add_cancel htpos
    have hiter : (shift F)^[firstHitTime F ω - 1] (shift F ω) =
        (shift F)^[firstHitTime F ω] ω := by
      conv_rhs => rw [← hsucc]
      rw [iterate_add_apply, iterate_one]
    rw [hiter]
    exact hspec.1
  have hshift_hit :
      {n : ℕ | (shift F)^[n] (shift F ω) ∈ survival F}.Nonempty :=
    ⟨firstHitTime F ω - 1, hland⟩
  have hspec' := firstHitTime_spec (F := F) (ω := shift F ω) hshift_hit
  apply le_antisymm
  · exact Nat.sInf_le hland
  · by_contra hlt
    rw [not_le] at hlt
    have hkA := hspec'.1
    have hklt : firstHitTime F (shift F ω) + 1 < firstHitTime F ω := by
      omega
    have : (shift F)^[firstHitTime F (shift F ω) + 1] ω ∈ survival F := by
      rw [iterate_add_apply, iterate_one]
      exact hkA
    exact hspec.2 _ hklt this

theorem firstHitTime_eq_iff {F : AdmissibleFamily} {ω : ResidueSpace F} {n : ℕ}
    (hn : 0 < n) :
    firstHitTime F ω = n ↔
      (shift F)^[n] ω ∈ survival F ∧
        ∀ k, k < n → (shift F)^[k] ω ∉ survival F := by
  constructor
  · intro hrt
    have hhit : {m : ℕ | (shift F)^[m] ω ∈ survival F}.Nonempty := by
      by_contra hempty
      have hz : firstHitTime F ω = 0 := by
        unfold firstHitTime
        refine Nat.sInf_eq_zero.mpr (Or.inr ?_)
        rwa [Set.not_nonempty_iff_eq_empty] at hempty
      omega
    have hspec := firstHitTime_spec (F := F) hhit
    rw [hrt] at hspec
    exact hspec
  · intro ⟨hUn, hmin⟩
    have hhit : {m : ℕ | (shift F)^[m] ω ∈ survival F}.Nonempty := ⟨n, hUn⟩
    apply le_antisymm
    · exact Nat.sInf_le hUn
    · by_contra hlt
      rw [not_le] at hlt
      exact hmin (firstHitTime F ω) hlt (firstHitTime_spec (F := F) hhit).1

theorem measurableSet_firstHitTime_eq (F : AdmissibleFamily) (n : ℕ) :
    MeasurableSet {ω : ResidueSpace F | firstHitTime F ω = n} := by
  match n with
  | 0 =>
    have heq : {ω : ResidueSpace F | firstHitTime F ω = 0} =
        survival F ∪ {ω | ∀ k, (shift F)^[k] ω ∉ survival F} := by
      ext ω
      constructor
      · intro ht
        by_cases hhit : {n : ℕ | (shift F)^[n] ω ∈ survival F}.Nonempty
        · left
          have hspec := firstHitTime_spec (F := F) hhit
          rw [ht] at hspec
          simpa [iterate_zero_apply] using hspec.1
        · right
          intro k hk
          exact hhit ⟨k, hk⟩
      · intro h
        rcases h with hA | hnever
        · exact firstHitTime_eq_zero_of_mem (F := F) hA
        · unfold firstHitTime
          refine Nat.sInf_eq_zero.mpr (Or.inr ?_)
          ext k
          exact iff_false_intro (hnever k)
    have hnever : {ω : ResidueSpace F | ∀ k, (shift F)^[k] ω ∉ survival F} =
        ⋂ k : ℕ, {ω | (shift F)^[k] ω ∉ survival F} := by
      ext ω
      simp
    rw [heq, hnever]
    exact (survival_measurable F).union
      (MeasurableSet.iInter fun k =>
        (measurableSet_iterate_mem_survival F k).compl)
  | n + 1 =>
    have heq : {ω : ResidueSpace F | firstHitTime F ω = n + 1} =
        {ω | (shift F)^[n + 1] ω ∈ survival F} ∩
          ⋂ k : Fin (n + 1),
            {ω | (shift F)^[(k : ℕ)] ω ∉ survival F} := by
      ext ω
      constructor
      · intro ht
        have h := (firstHitTime_eq_iff (F := F) (ω := ω) (n := n + 1)
          (Nat.succ_pos n)).mp ht
        refine ⟨h.1, ?_⟩
        rw [mem_iInter]
        intro k
        exact h.2 (k : ℕ) k.isLt
      · intro ⟨hUn, hmin⟩
        refine (firstHitTime_eq_iff (F := F) (ω := ω) (n := n + 1)
          (Nat.succ_pos n)).mpr ⟨hUn, ?_⟩
        intro k hk
        exact mem_iInter.mp hmin ⟨k, hk⟩
    rw [heq]
    exact (measurableSet_iterate_mem_survival F (n + 1)).inter
      (MeasurableSet.iInter fun k =>
        (measurableSet_iterate_mem_survival F (k : ℕ)).compl)

theorem measurable_firstHitTime (F : AdmissibleFamily) :
    Measurable (firstHitTime F) :=
  measurable_to_countable' fun n => measurableSet_firstHitTime_eq F n

theorem measurable_inducedShift (F : AdmissibleFamily) :
    Measurable (inducedShift F) := by
  intro s hs
  have hpre : inducedShift F ⁻¹' s =
      ⋃ n : ℕ, {ω | returnTime F ω = n} ∩ (shift F)^[n] ⁻¹' s := by
    ext ω
    constructor
    · intro h
      refine mem_iUnion.mpr ⟨returnTime F ω, ⟨rfl, h⟩⟩
    · intro h
      obtain ⟨n, ⟨hn, hmem⟩⟩ := mem_iUnion.mp h
      change (shift F)^[returnTime F ω] ω ∈ s
      rw [hn]
      exact hmem
  rw [hpre]
  exact MeasurableSet.iUnion fun n =>
    (measurableSet_returnTime_eq F n).inter
      (((shift_measurePreserving F).iterate n).measurable hs)

theorem returnLevel_eq_empty_zero (F : AdmissibleFamily) :
    returnLevel F 0 = ∅ := by
  ext ω
  constructor
  · intro h
    exact (returnTime_pos F ω).ne' h.2
  · intro h
    exact h.elim

noncomputable def returnImage (F : AdmissibleFamily) (n : ℕ) :
    Set (ResidueSpace F) :=
  (shift F)^[n] '' returnLevel F n

theorem returnImage_eq_preimage (F : AdmissibleFamily) (n : ℕ) :
    returnImage F n = (shift_inv F)^[n] ⁻¹' returnLevel F n :=
  shift_iterate_image_eq_shift_inv_preimage F n _

theorem measurableSet_returnImage (F : AdmissibleFamily) (n : ℕ) :
    MeasurableSet (returnImage F n) := by
  rw [returnImage_eq_preimage]
  exact (measurableSet_returnLevel F n).preimage
    ((shift_inv_measurable F).iterate n)

theorem returnImage_disjoint (F : AdmissibleFamily) {n m : ℕ} (hne : n ≠ m) :
    Disjoint (returnImage F n) (returnImage F m) := by
  refine disjoint_left.mpr ?_
  intro ω hω hω'
  obtain ⟨a, ha, rfl⟩ := hω
  obtain ⟨a', ha', hEq⟩ := hω'
  rcases ha with ⟨haA, haN⟩
  rcases ha' with ⟨ha'A, ha'N⟩
  have hn0 : n ≠ 0 := by
    intro hn
    subst hn
    exact (returnTime_pos F a).ne' haN
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    exact (returnTime_pos F a').ne' ha'N
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have hsplit :
        (shift F)^[m] a' = (shift F)^[n] ((shift F)^[m - n] a') := by
      calc
        (shift F)^[m] a'
            = (shift F)^[n + (m - n)] a' := by rw [Nat.add_sub_of_le (le_of_lt hlt)]
        _ = (shift F)^[n] ((shift F)^[m - n] a') :=
          iterate_add_apply _ _ _ _
    have haeq : a = (shift F)^[m - n] a' :=
      shift_iterate_injective F n (hEq.symm.trans hsplit)
    have hnot : (shift F)^[m - n] a' ∉ survival F :=
      not_mem_survival_of_lt_returnTime (F := F) ha'A ha'N
        (Nat.sub_pos_of_lt hlt)
        (Nat.sub_lt (Nat.pos_of_ne_zero hm0) (Nat.pos_of_ne_zero hn0))
    exact hnot (haeq ▸ haA)
  · exact hne heq
  · have hsplit :
        (shift F)^[n] a = (shift F)^[m] ((shift F)^[n - m] a) := by
      calc
        (shift F)^[n] a
            = (shift F)^[m + (n - m)] a := by rw [Nat.add_sub_of_le (le_of_lt hgt)]
        _ = (shift F)^[m] ((shift F)^[n - m] a) :=
          iterate_add_apply _ _ _ _
    have ha'eq : a' = (shift F)^[n - m] a :=
      shift_iterate_injective F m (hEq.trans hsplit)
    have hnot : (shift F)^[n - m] a ∉ survival F :=
      not_mem_survival_of_lt_returnTime (F := F) haA haN
        (Nat.sub_pos_of_lt hgt)
        (Nat.sub_lt (Nat.pos_of_ne_zero hn0) (Nat.pos_of_ne_zero hm0))
    exact hnot (ha'eq ▸ ha'A)

theorem returnImage_zero (F : AdmissibleFamily) : returnImage F 0 = ∅ := by
  simp [returnImage, returnLevel_eq_empty_zero]

theorem ae_exists_mem_returnImage (F : AdmissibleFamily) :
    ∀ᵐ a ∂productMeasure F,
      a ∈ survival F → ∃ n, a ∈ returnImage F n := by
  filter_upwards [ae_mem_survival_frequently_backward F] with a hback hA
  obtain ⟨N, hN1, hNA⟩ := (Filter.frequently_atTop.mp (hback hA)) 1
  have hne : {k : ℕ | 0 < k ∧ (shift_inv F)^[k] a ∈ survival F}.Nonempty :=
    ⟨N, Nat.succ_le_iff.mp hN1, hNA⟩
  set k := sInf {m : ℕ | 0 < m ∧ (shift_inv F)^[m] a ∈ survival F}
  have hk := Nat.sInf_mem hne
  set prev := (shift_inv F)^[k] a
  have hprevA : prev ∈ survival F := hk.2
  have hUa : (shift F)^[k] prev = a := shift_iterate_comp_shift_inv F k a
  have hret : {m : ℕ | 0 < m ∧ (shift F)^[m] prev ∈ survival F}.Nonempty :=
    ⟨k, hk.1, hUa.symm ▸ hA⟩
  have hle : returnTime F prev ≤ k := by
    unfold returnTime
    rw [dif_pos hret]
    exact Nat.sInf_le ⟨hk.1, hUa.symm ▸ hA⟩
  have hge : k ≤ returnTime F prev := by
    refine le_of_not_gt fun hlt => ?_
    set g := returnTime F prev
    set d := k - g
    have hsum : k = g + d := (Nat.add_sub_of_le hle).symm
    have hdecomp : prev = (shift_inv F)^[g] ((shift_inv F)^[d] a) := by
      change (shift_inv F)^[k] a = (shift_inv F)^[g] ((shift_inv F)^[d] a)
      rw [hsum]
      exact iterate_add_apply (shift_inv F) g d a
    have hcalc : (shift F)^[g] prev = (shift_inv F)^[d] a := by
      rw [hdecomp]
      exact shift_iterate_comp_shift_inv F g ((shift_inv F)^[d] a)
    have hpos : 0 < d := Nat.sub_pos_of_lt hlt
    have hmem : d ∈ {m : ℕ | 0 < m ∧ (shift_inv F)^[m] a ∈ survival F} :=
      ⟨hpos, by
        have hAg : (shift F)^[g] prev ∈ survival F := (returnTime_spec F hret).1
        rwa [hcalc] at hAg⟩
    have hgpos : 0 < g := returnTime_pos F prev
    exact (Nat.sInf_le hmem).not_gt (Nat.sub_lt hk.1 hgpos)
  exact ⟨k, prev, ⟨hprevA, le_antisymm hle hge⟩, hUa⟩

theorem measure_dummy_return_root (F : AdmissibleFamily) :
    productMeasure F
      {a | a ∈ survival F ∧
        ¬ {n : ℕ | 0 < n ∧ (shift F)^[n] a ∈ survival F}.Nonempty} = 0 :=
  measure_mono_null (fun _ ha => ha.2) (measure_never_returns F)

theorem measure_returnImage_diff_survival (F : AdmissibleFamily) (n : ℕ) :
    productMeasure F (returnImage F n \ survival F) = 0 := by
  let DummyRoot : Set (ResidueSpace F) :=
    {a | a ∈ survival F ∧
      ¬ {m : ℕ | 0 < m ∧ (shift F)^[m] a ∈ survival F}.Nonempty}
  have hsub : returnImage F n \ survival F ⊆ (shift F)^[n] '' DummyRoot := by
    intro ω hω
    obtain ⟨⟨a, ha, rfl⟩, hnotA⟩ := hω
    refine ⟨a, ⟨ha.1, ?_⟩, rfl⟩
    intro hret
    have : (shift F)^[n] a ∈ survival F := by
      convert (returnTime_spec F hret).1
      exact ha.2.symm
    exact hnotA this
  refine measure_mono_null hsub ?_
  rw [shift_iterate_image_eq_shift_inv_preimage]
  have hDummy : productMeasure F DummyRoot = 0 := measure_dummy_return_root F
  exact ((shift_inv_measurePreserving F).iterate n).measure_preimage
    (NullMeasurableSet.of_null hDummy) ▸ hDummy

theorem returnImage_iUnion_ae (F : AdmissibleFamily) :
    (⋃ n : ℕ, returnImage F n) =ᵐ[productMeasure F] survival F := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · have hunion :
        (⋃ n : ℕ, returnImage F n) \ survival F ⊆
          ⋃ n : ℕ, returnImage F n \ survival F := by
      intro ω hω
      obtain ⟨hU, hA⟩ := hω
      obtain ⟨n, hn⟩ := mem_iUnion.mp hU
      exact mem_iUnion.mpr ⟨n, hn, hA⟩
    refine measure_mono_null hunion ?_
    exact measure_iUnion_null fun n => measure_returnImage_diff_survival F n
  · have h := ae_exists_mem_returnImage F
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    intro a ha
    intro hf
    exact ha.2 (mem_iUnion.mpr (hf ha.1))

theorem returnImage_succ_iUnion (F : AdmissibleFamily) :
    (⋃ n : ℕ, returnImage F (n + 1)) = ⋃ n : ℕ, returnImage F n := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    cases n with
    | zero =>
      rw [returnImage_zero F] at hn
      exact hn.elim
    | succ n =>
      exact mem_iUnion.mpr ⟨n, hn⟩

/- S-invariance / Kac-Tonelli block: previous lake runs hung or failed here.
-- skipped live: `Measure.ext` on `inducedShift` preimages hung the compiler.
-- Live replacement below uses Kakutani levels + shift embeddings, not map-measure.
theorem measure_map_inducedShift_restrict (F : AdmissibleFamily) :
    Measure.map (inducedShift F)
        ((productMeasure F).restrict (survival F)) =
      (productMeasure F).restrict (survival F) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_inducedShift F) hs,
    Measure.restrict_apply ((measurable_inducedShift F) hs),
    Measure.restrict_apply hs]
  have hpart : inducedShift F ⁻¹' s ∩ survival F =
      ⋃ n : ℕ, returnLevel F (n + 1) ∩ (shift F)^[n + 1] ⁻¹' s := by
    ext ω
    constructor
    · intro h
      have hn : returnTime F ω = returnTime F ω - 1 + 1 :=
        (Nat.sub_add_cancel (returnTime_pos F ω)).symm
      refine mem_iUnion.mpr ⟨returnTime F ω - 1, ⟨⟨h.2, hn⟩, ?_⟩⟩
      have hS : inducedShift F ω ∈ s := h.1
      unfold inducedShift at hS
      rwa [hn] at hS
    · intro h
      obtain ⟨n, ⟨hlev, hpre⟩⟩ := mem_iUnion.mp h
      refine ⟨?_, hlev.1⟩
      unfold inducedShift
      rwa [hlev.2]
  have hd : Pairwise (Disjoint on fun n : ℕ =>
      returnLevel F (n + 1) ∩ (shift F)^[n + 1] ⁻¹' s) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    intro ω hω hω'
    exact hij (Nat.succ_injective (hω.1.2.symm.trans hω'.1.2))
  have hmeas : ∀ n : ℕ,
      MeasurableSet (returnLevel F (n + 1) ∩ (shift F)^[n + 1] ⁻¹' s) :=
    fun n => (measurableSet_returnLevel F (n + 1)).inter
      (((shift_measurePreserving F).iterate (n + 1)).measurable hs)
  rw [hpart, measure_iUnion hd hmeas]
  have hterm : ∀ n : ℕ,
      productMeasure F (returnLevel F (n + 1) ∩ (shift F)^[n + 1] ⁻¹' s) =
        productMeasure F (returnImage F (n + 1) ∩ s) := by
    intro n
    have him : (shift F)^[n + 1] ⁻¹' returnImage F (n + 1) =
        returnLevel F (n + 1) := by
      rw [returnImage_eq_preimage F (n + 1)]
      ext ω
      rw [mem_preimage, shift_inv_iterate_comp_shift F (n + 1) ω]
    have hpre : (shift F)^[n + 1] ⁻¹' (returnImage F (n + 1) ∩ s) =
        returnLevel F (n + 1) ∩ (shift F)^[n + 1] ⁻¹' s := by
      rw [preimage_inter, him]
    rw [← hpre]
    exact ((shift_measurePreserving F).iterate (n + 1)).measure_preimage
      ((measurableSet_returnImage F (n + 1)).inter hs).nullMeasurableSet
  rw [tsum_congr hterm]
  have hdImg : Pairwise (Disjoint on fun n : ℕ => returnImage F (n + 1) ∩ s) := by
    intro i j hij
    exact (returnImage_disjoint F (fun h => hij (Nat.succ_injective h))).inter_right s
  have hunion :
      productMeasure F (⋃ n : ℕ, returnImage F (n + 1) ∩ s) =
        ∑' n : ℕ, productMeasure F (returnImage F (n + 1) ∩ s) :=
    measure_iUnion hdImg fun n =>
      (measurableSet_returnImage F (n + 1)).inter hs
  rw [← hunion]
  have hU : (⋃ n : ℕ, returnImage F (n + 1) ∩ s) =
      (⋃ n : ℕ, returnImage F (n + 1)) ∩ s := by
    ext ω
    constructor
    · intro h
      obtain ⟨n, hn, hs'⟩ := mem_iUnion.mp h
      exact ⟨mem_iUnion.mpr ⟨n, hn⟩, hs'⟩
    · intro h
      obtain ⟨n, hn⟩ := mem_iUnion.mp h.1
      exact mem_iUnion.mpr ⟨n, hn, h.2⟩
  rw [hU, returnImage_succ_iUnion]
  exact measure_congr ((returnImage_iUnion_ae F).inter (ae_eq_refl s))

theorem lintegral_comp_inducedShift_survival (F : AdmissibleFamily)
    {f : ResidueSpace F → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in survival F, f (inducedShift F ω) ∂productMeasure F =
      ∫⁻ ω in survival F, f ω ∂productMeasure F := by
  rw [← lintegral_map hf (measurable_inducedShift F),
    measure_map_inducedShift_restrict F]

theorem lintegral_comp_inducedShift_iterate_survival (F : AdmissibleFamily)
    (j : ℕ) {f : ResidueSpace F → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in survival F, f ((inducedShift F)^[j] ω) ∂productMeasure F =
      ∫⁻ ω in survival F, f ω ∂productMeasure F := by
  induction j with
  | zero =>
    simp
  | succ j ih =>
    have hfj : Measurable (fun ω => f ((inducedShift F)^[j] ω)) :=
      hf.comp ((measurable_inducedShift F).iterate j)
    have hcomp : (fun ω => f ((inducedShift F)^[j + 1] ω)) =
        (fun ω => f ((inducedShift F)^[j] (inducedShift F ω))) := by
      funext ω
      rw [iterate_succ_apply' (inducedShift F) j ω]
    rw [hcomp, lintegral_comp_inducedShift_survival F hfj, ih]
-/

theorem pairwise_disjoint_returnLevel_succ (F : AdmissibleFamily) :
    Pairwise (Disjoint on fun n : ℕ => returnLevel F (n + 1)) := by
  intro i j hij
  refine disjoint_left.mpr ?_
  intro ω hω hω'
  exact hij (Nat.succ_injective (hω.2.symm.trans hω'.2))

theorem pairwise_disjoint_returnImage_succ (F : AdmissibleFamily) :
    Pairwise (Disjoint on fun n : ℕ => returnImage F (n + 1)) := by
  intro i j hij
  exact returnImage_disjoint F (fun h => hij (Nat.succ_injective h))

theorem measurableEmbedding_shift_iterate (F : AdmissibleFamily) (n : ℕ) :
    MeasurableEmbedding ((shift F)^[n]) where
  injective := shift_iterate_injective F n
  measurable := ((shift_measurePreserving F).iterate n).measurable
  measurableSet_image' := fun s hs => by
    rw [shift_iterate_image_eq_shift_inv_preimage]
    exact hs.preimage ((shift_inv_measurable F).iterate n)

theorem inducedShift_eq_of_mem_returnLevel {F : AdmissibleFamily} {n : ℕ}
    {ω : ResidueSpace F} (h : ω ∈ returnLevel F n) :
    inducedShift F ω = (shift F)^[n] ω :=
  congrArg (fun k => (shift F)^[k] ω) h.2

theorem lintegral_comp_shift_returnLevel (F : AdmissibleFamily) (n : ℕ)
    (f : ResidueSpace F → ℝ≥0∞) :
    ∫⁻ ω in returnLevel F (n + 1), f ((shift F)^[n + 1] ω) ∂productMeasure F =
      ∫⁻ ω in returnImage F (n + 1), f ω ∂productMeasure F :=
  ((shift_measurePreserving F).iterate (n + 1)).setLIntegral_comp_emb
    (measurableEmbedding_shift_iterate F (n + 1)) f (returnLevel F (n + 1))

theorem lintegral_comp_inducedShift_returnLevel (F : AdmissibleFamily) (n : ℕ)
    (f : ResidueSpace F → ℝ≥0∞) :
    ∫⁻ ω in returnLevel F (n + 1), f (inducedShift F ω) ∂productMeasure F =
      ∫⁻ ω in returnImage F (n + 1), f ω ∂productMeasure F := by
  have hfun : EqOn (fun ω => f (inducedShift F ω))
      (fun ω => f ((shift F)^[n + 1] ω)) (returnLevel F (n + 1)) :=
    fun ω hω => congrArg f (inducedShift_eq_of_mem_returnLevel hω)
  rw [setLIntegral_congr_fun (measurableSet_returnLevel F (n + 1)) hfun]
  exact lintegral_comp_shift_returnLevel F n f

theorem returnImage_succ_iUnion_ae (F : AdmissibleFamily) :
    (⋃ n : ℕ, returnImage F (n + 1)) =ᵐ[productMeasure F] survival F := by
  rw [returnImage_succ_iUnion F]
  exact returnImage_iUnion_ae F

theorem lintegral_comp_inducedShift_survival (F : AdmissibleFamily)
    {f : ResidueSpace F → ℝ≥0∞} (_hf : Measurable f) :
    ∫⁻ ω in survival F, f (inducedShift F ω) ∂productMeasure F =
      ∫⁻ ω in survival F, f ω ∂productMeasure F := by
  have hAeq : survival F = ⋃ n : ℕ, returnLevel F (n + 1) :=
    (returnLevel_iUnion_eq F).symm
  have hleft :
      ∫⁻ ω in survival F, f (inducedShift F ω) ∂productMeasure F =
        ∑' n : ℕ, ∫⁻ ω in returnLevel F (n + 1), f (inducedShift F ω)
          ∂productMeasure F := by
    rw [hAeq]
    exact lintegral_iUnion (fun n => measurableSet_returnLevel F (n + 1))
      (pairwise_disjoint_returnLevel_succ F) _
  have hright :
      ∫⁻ ω in survival F, f ω ∂productMeasure F =
        ∑' n : ℕ, ∫⁻ ω in returnImage F (n + 1), f ω ∂productMeasure F := by
    rw [← setLIntegral_congr (returnImage_succ_iUnion_ae F)]
    exact lintegral_iUnion (fun n => measurableSet_returnImage F (n + 1))
      (pairwise_disjoint_returnImage_succ F) _
  rw [hleft, hright]
  exact tsum_congr fun n => lintegral_comp_inducedShift_returnLevel F n f

theorem lintegral_comp_inducedShift_iterate_survival (F : AdmissibleFamily)
    (j : ℕ) {f : ResidueSpace F → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in survival F, f ((inducedShift F)^[j] ω) ∂productMeasure F =
      ∫⁻ ω in survival F, f ω ∂productMeasure F := by
  induction j with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
  | succ j ih =>
    have hfj : Measurable (fun ω => f ((inducedShift F)^[j] ω)) :=
      hf.comp ((measurable_inducedShift F).iterate j)
    have hcomp :
        (fun ω => f ((inducedShift F)^[j + 1] ω)) =
          (fun ω => f ((inducedShift F)^[j] (inducedShift F ω))) := by
      funext ω
      rw [iterate_succ_apply (inducedShift F) j ω]
    rw [hcomp, lintegral_comp_inducedShift_survival F hfj, ih]

theorem one_div_b_lt_one {b : ℕ} (hb : 2 ≤ b) : (1 : ℝ) / b < 1 := by
  have hb1 : (1 : ℝ) < b := one_le_b hb
  exact (div_lt_one (zero_lt_one.trans hb1)).2 hb1

theorem tsum_geom_inv_b_succ {b : ℕ} (hb : 2 ≤ b) :
    ∑' j : ℕ, ((1 : ℝ) / b) ^ (j + 1) = ((b : ℝ) - 1)⁻¹ := by
  have hr0 : 0 ≤ (1 : ℝ) / b := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hr1 := one_div_b_lt_one hb
  have hb1 : (1 : ℝ) < b := one_le_b hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  simp_rw [pow_succ']
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hden : (1 : ℝ) - 1 / b = (b - 1) / b := by
    rw [← div_self hb0.ne', sub_div]
  rw [hden, inv_div, ← one_div, div_mul_div_comm, one_mul]
  have : (b : ℝ) / (b * (b - 1)) = (1 : ℝ) / (b - 1) := by
    rw [div_mul_eq_div_div, div_self hb0.ne']
  exact this

theorem tsum_geom_inv_b_succ_ennreal {b : ℕ} (hb : 2 ≤ b) :
    ∑' j : ℕ, ((b : ℝ≥0∞)⁻¹) ^ (j + 1) = ENNReal.ofReal (((b : ℝ) - 1)⁻¹) := by
  have hr0 : ∀ j : ℕ, 0 ≤ ((1 : ℝ) / b) ^ (j + 1) := fun j =>
    pow_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _)) _
  have hsm : Summable fun j : ℕ => ((1 : ℝ) / b) ^ (j + 1) := by
    simp_rw [pow_succ']
    exact (summable_geometric_of_lt_one
      (div_nonneg zero_le_one (Nat.cast_nonneg _)) (one_div_b_lt_one hb)).mul_left _
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans (one_le_b hb)
  have hterm : ∀ j : ℕ,
      ((b : ℝ≥0∞)⁻¹) ^ (j + 1) = ENNReal.ofReal (((1 : ℝ) / b) ^ (j + 1)) := by
    intro j
    have : (b : ℝ≥0∞) = ENNReal.ofReal (b : ℝ) := (ENNReal.ofReal_natCast (n := b)).symm
    rw [this, ← ENNReal.ofReal_inv_of_pos hb0, ← ENNReal.ofReal_pow
      (inv_nonneg.2 (le_of_lt hb0)), one_div]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg hr0 hsm, tsum_geom_inv_b_succ hb]

noncomputable def gapTailTermENN (F : AdmissibleFamily) {b : ℕ} (_hb : 2 ≤ b)
    (ω : ResidueSpace F) (j : ℕ) : ℝ≥0∞ :=
  (returnTime F ((inducedShift F)^[j] ω) : ℝ≥0∞) / (b : ℝ≥0∞) ^ (j + 1)

noncomputable def gapTailENN (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (ω : ResidueSpace F) : ℝ≥0∞ :=
  if ω ∈ survival F then ∑' j : ℕ, gapTailTermENN F hb ω j else 0

noncomputable def gapTail (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ResidueSpace F → ℝ :=
  fun ω => (gapTailENN F hb ω).toReal

theorem gapTail_nonneg (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (ω : ResidueSpace F) : 0 ≤ gapTail F hb ω :=
  ENNReal.toReal_nonneg

theorem measurable_returnTime_ennreal (F : AdmissibleFamily) :
    Measurable fun ω : ResidueSpace F => (returnTime F ω : ℝ≥0∞) :=
  (measurable_from_nat (f := fun n : ℕ => (n : ℝ≥0∞))).comp
    (returnTime_measurable F)

theorem measurable_gapTailTermENN (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (j : ℕ) : Measurable (fun ω => gapTailTermENN F hb ω j) := by
  unfold gapTailTermENN
  exact (measurable_returnTime_ennreal F).comp
    ((measurable_inducedShift F).iterate j) |>.div measurable_const

theorem measurable_gapTailENN (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    Measurable (gapTailENN F hb) :=
  Measurable.ite (survival_measurable F)
    (Measurable.ennreal_tsum fun j => measurable_gapTailTermENN F hb j)
    measurable_const

theorem measurable_gapTail (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    Measurable (gapTail F hb) :=
  ENNReal.measurable_toReal.comp (measurable_gapTailENN F hb)

theorem gapTailTermENN_ne_top (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (ω : ResidueSpace F) (j : ℕ) : gapTailTermENN F hb ω j ≠ ⊤ := by
  unfold gapTailTermENN
  have hnum : (returnTime F ((inducedShift F)^[j] ω) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hb0 : (b : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.2 (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hb))
  have hden : (b : ℝ≥0∞) ^ (j + 1) ≠ 0 := pow_ne_zero (j + 1) hb0
  exact ENNReal.div_ne_top hnum hden

theorem measurable_returnTime_ennreal_iterate (F : AdmissibleFamily) (j : ℕ) :
    Measurable fun ω : ResidueSpace F =>
      (returnTime F ((inducedShift F)^[j] ω) : ℝ≥0∞) :=
  (measurable_returnTime_ennreal F).comp ((measurable_inducedShift F).iterate j)

/-! Kac + Tonelli on `A`. -/
theorem lintegral_returnTime_inducedShift_iterate (F : AdmissibleFamily) (j : ℕ) :
    ∫⁻ ω in survival F,
        (returnTime F ((inducedShift F)^[j] ω) : ℝ≥0∞) ∂productMeasure F = 1 := by
  rw [lintegral_comp_inducedShift_iterate_survival F j
      (measurable_returnTime_ennreal F), kac_returnTime F]

theorem lintegral_gapTailTermENN_survival (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (j : ℕ) :
    ∫⁻ ω in survival F, gapTailTermENN F hb ω j ∂productMeasure F =
      ((b : ℝ≥0∞)⁻¹) ^ (j + 1) := by
  have hr : ((b : ℝ≥0∞) ^ (j + 1))⁻¹ ≠ ⊤ := by
    have hb0 : (b : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.2 (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hb))
    exact ENNReal.inv_ne_top.2 (pow_ne_zero (j + 1) hb0)
  have hmul :
      ∫⁻ ω in survival F,
          (returnTime F ((inducedShift F)^[j] ω) : ℝ≥0∞) *
            ((b : ℝ≥0∞) ^ (j + 1))⁻¹ ∂productMeasure F =
        (∫⁻ ω in survival F,
            (returnTime F ((inducedShift F)^[j] ω) : ℝ≥0∞) ∂productMeasure F) *
          ((b : ℝ≥0∞) ^ (j + 1))⁻¹ :=
    lintegral_mul_const' _ _ hr
  unfold gapTailTermENN
  simp_rw [div_eq_mul_inv]
  rw [hmul, lintegral_returnTime_inducedShift_iterate F j, one_mul, ENNReal.inv_pow]

theorem lintegral_gapTailENN_survival (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∫⁻ ω in survival F, gapTailENN F hb ω ∂productMeasure F =
      ENNReal.ofReal (((b : ℝ) - 1)⁻¹) := by
  have hfun : EqOn (gapTailENN F hb)
      (fun ω => ∑' j : ℕ, gapTailTermENN F hb ω j) (survival F) := by
    intro ω hω
    simp [gapTailENN, hω]
  rw [setLIntegral_congr_fun (survival_measurable F) hfun]
  have htsum :
      ∫⁻ ω in survival F, ∑' j : ℕ, gapTailTermENN F hb ω j ∂productMeasure F =
        ∑' j : ℕ, ∫⁻ ω in survival F, gapTailTermENN F hb ω j ∂productMeasure F :=
    lintegral_tsum fun j => (measurable_gapTailTermENN F hb j).aemeasurable
  rw [htsum, tsum_congr (lintegral_gapTailTermENN_survival F hb),
    tsum_geom_inv_b_succ_ennreal hb]

theorem gapTailENN_ae_lt_top_restrict (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ a ∂(productMeasure F).restrict (survival F), gapTailENN F hb a < ⊤ :=
  ae_lt_top (measurable_gapTailENN F hb)
    (by
      rw [lintegral_gapTailENN_survival F hb]
      exact ENNReal.ofReal_ne_top)

theorem ae_rootMeasure_iff_restrict (F : AdmissibleFamily)
    {p : ResidueSpace F → Prop} :
    (∀ᵐ a ∂rootMeasure F, p a) ↔
      (∀ᵐ a ∂(productMeasure F).restrict (survival F), p a) := by
  unfold rootMeasure ProbabilityTheory.cond
  constructor
  · intro h
    rw [ae_iff] at h ⊢
    have hc0 : (productMeasure F (survival F))⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.2 (measure_ne_top _ _)
    have hmul :
        (productMeasure F (survival F))⁻¹ *
          ((productMeasure F).restrict (survival F) {a | ¬p a}) = 0 := h
    exact Or.resolve_left (mul_eq_zero.mp hmul) hc0
  · intro h
    rw [ae_iff] at h ⊢
    have hmul :
        (productMeasure F (survival F))⁻¹ *
          ((productMeasure F).restrict (survival F) {a | ¬p a}) = 0 := by
      rw [h, mul_zero]
    exact hmul

theorem ae_rootMeasure_of_mem (F : AdmissibleFamily)
    {p : ResidueSpace F → Prop} :
    (∀ᵐ a ∂rootMeasure F, p a) ↔
      ∀ᵐ a ∂productMeasure F, a ∈ survival F → p a := by
  rw [ae_rootMeasure_iff_restrict, ae_restrict_iff' (survival_measurable F)]

/- Needs Tonelli finiteness of T. -/
theorem gapTailENN_ae_ne_top_root (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ a ∂rootMeasure F, gapTailENN F hb a ≠ ⊤ :=
  (ae_rootMeasure_iff_restrict F).2
    ((gapTailENN_ae_lt_top_restrict F hb).mono fun _ h => h.ne)

theorem gapTail_ae_finite_on_root (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ a ∂rootMeasure F, gapTailENN F hb a ≠ ⊤ :=
  gapTailENN_ae_ne_top_root F hb

theorem ae_mem_survival_root (F : AdmissibleFamily) :
    ∀ᵐ a ∂rootMeasure F, a ∈ survival F :=
  (ae_rootMeasure_iff_restrict F).2 (ae_restrict_mem (survival_measurable F))

theorem inv_b_sub_one_nonneg {b : ℕ} (hb : 2 ≤ b) : 0 ≤ ((b : ℝ) - 1)⁻¹ :=
  inv_nonneg.2 (le_of_lt (sub_pos.2 (one_le_b hb)))

theorem gapTailENN_ge_geom (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    {a : ResidueSpace F} (hA : a ∈ survival F) :
    ENNReal.ofReal (((b : ℝ) - 1)⁻¹) ≤ gapTailENN F hb a := by
  have hterm : ∀ j : ℕ, ((b : ℝ≥0∞)⁻¹) ^ (j + 1) ≤ gapTailTermENN F hb a j := by
    intro j
    unfold gapTailTermENN
    have hg : (1 : ℝ≥0∞) ≤ (returnTime F ((inducedShift F)^[j] a) : ℝ≥0∞) :=
      Nat.one_le_cast.2 (Nat.succ_le_of_lt (returnTime_pos F _))
    have hb0 : (b : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.2 (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hb))
    have hden : (b : ℝ≥0∞) ^ (j + 1) ≠ 0 := pow_ne_zero (j + 1) hb0
    rw [← ENNReal.inv_pow, ← one_div]
    exact ENNReal.div_le_div_right hg _
  have htsum := ENNReal.tsum_le_tsum hterm
  rw [tsum_geom_inv_b_succ_ennreal hb] at htsum
  simpa [gapTailENN, hA] using htsum

/- Needs finite T and Kac-Tonelli. -/
theorem gapTail_pos_on_root (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ a ∂rootMeasure F, ((b : ℝ) - 1)⁻¹ ≤ gapTail F hb a := by
  filter_upwards [gapTail_ae_finite_on_root F hb, ae_mem_survival_root F] with a htop hA
  have hle := gapTailENN_ge_geom F hb hA
  have hnn := inv_b_sub_one_nonneg hb
  rw [← ENNReal.toReal_ofReal hnn]
  exact ENNReal.toReal_mono htop hle

theorem lintegral_gapTailENN_root (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∫⁻ a, gapTailENN F hb a ∂rootMeasure F =
      ENNReal.ofReal ((rho F)⁻¹ * ((b : ℝ) - 1)⁻¹) := by
  unfold rootMeasure
  rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul,
    lintegral_gapTailENN_survival F hb, measure_survival]
  rw [← ENNReal.ofReal_inv_of_pos (rho_pos F),
    ← ENNReal.ofReal_mul (inv_nonneg.2 (rho_pos F).le)]

theorem integrable_gapTail_root (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    Integrable (gapTail F hb) (rootMeasure F) := by
  refine integrable_toReal_of_lintegral_ne_top
    (measurable_gapTailENN F hb).aemeasurable ?_
  rw [lintegral_gapTailENN_root F hb]
  exact ENNReal.ofReal_ne_top

theorem expected_gapTail (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∫ a, gapTail F hb a ∂rootMeasure F = (rho F * ((b : ℝ) - 1))⁻¹ := by
  have hnn : 0 ≤ᵐ[rootMeasure F] gapTail F hb :=
    Filter.Eventually.of_forall (gapTail_nonneg F hb)
  rw [integral_eq_lintegral_of_nonneg_ae hnn
    (measurable_gapTail F hb).aestronglyMeasurable]
  have hcongr : (fun a => ENNReal.ofReal (gapTail F hb a)) =ᵐ[rootMeasure F]
      gapTailENN F hb := by
    filter_upwards [gapTail_ae_finite_on_root F hb] with a htop
    exact ENNReal.ofReal_toReal htop
  rw [lintegral_congr_ae hcongr, lintegral_gapTailENN_root F hb,
    ENNReal.toReal_ofReal]
  · rw [mul_inv, mul_comm]
  · exact mul_nonneg (inv_nonneg.2 (rho_pos F).le) (inv_b_sub_one_nonneg hb)

/-! Recurrence of `T` on `A`. -/
theorem gapTailENN_recurrence {F : AdmissibleFamily} {b : ℕ} {hb : 2 ≤ b}
    {a : ResidueSpace F} (hA : a ∈ survival F)
    (hSA : inducedShift F a ∈ survival F) :
    gapTailENN F hb a =
      (returnTime F a : ℝ≥0∞) / (b : ℝ≥0∞) +
        gapTailENN F hb (inducedShift F a) / (b : ℝ≥0∞) := by
  have h0 : gapTailTermENN F hb a 0 = (returnTime F a : ℝ≥0∞) / (b : ℝ≥0∞) := by
    unfold gapTailTermENN
    rw [iterate_zero_apply, zero_add, pow_one]
  have hsucc : ∀ j : ℕ,
      gapTailTermENN F hb a (j + 1) =
        gapTailTermENN F hb (inducedShift F a) j / (b : ℝ≥0∞) := by
    intro j
    unfold gapTailTermENN
    have hb0 : (b : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.2 (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hb))
    rw [iterate_succ_apply (f := inducedShift F), pow_succ]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (pow_ne_zero (j + 1) hb0)) (Or.inr hb0), mul_assoc]
  rw [gapTailENN, if_pos hA, tsum_eq_zero_add' ENNReal.summable, h0]
  have htail : ∑' j : ℕ, gapTailTermENN F hb a (j + 1) =
      ∑' j : ℕ, gapTailTermENN F hb (inducedShift F a) j / (b : ℝ≥0∞) :=
    tsum_congr hsucc
  rw [htail]
  have hdiv : ∑' j : ℕ, gapTailTermENN F hb (inducedShift F a) j / (b : ℝ≥0∞) =
      (∑' j : ℕ, gapTailTermENN F hb (inducedShift F a) j) / (b : ℝ≥0∞) := by
    simp_rw [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right]
  rw [hdiv, gapTailENN, if_pos hSA]

theorem ae_inducedShift_mem_survival (F : AdmissibleFamily) :
    ∀ᵐ ω ∂productMeasure F, inducedShift F ω ∈ survival F := by
  filter_upwards [returnTime_ae_finite F] with ω hret
  exact (returnTime_spec F hret).1

theorem ae_inducedShift_mem_survival_root (F : AdmissibleFamily) :
    ∀ᵐ a ∂rootMeasure F, inducedShift F a ∈ survival F :=
  (ae_rootMeasure_of_mem F).2
    ((ae_inducedShift_mem_survival F).mono fun _ h _ => h)

theorem ae_gapTailENN_inducedShift_ne_top_root (F : AdmissibleFamily) {b : ℕ}
    (hb : 2 ≤ b) :
    ∀ᵐ a ∂rootMeasure F, gapTailENN F hb (inducedShift F a) ≠ ⊤ := by
  let Bad : Set (ResidueSpace F) := {a | gapTailENN F hb a = ⊤}
  have hBad : productMeasure F Bad = 0 := by
    have h := gapTailENN_ae_lt_top_restrict F hb
    rw [ae_restrict_iff' (survival_measurable F), ae_iff] at h
    refine measure_mono_null ?_ h
    intro a ha
    change ¬ (a ∈ survival F → gapTailENN F hb a < ⊤)
    intro himp
    have hA : a ∈ survival F := by
      by_contra hnotA
      have h0 : gapTailENN F hb a = 0 := by
        unfold gapTailENN
        rw [if_neg hnotA]
      exact ENNReal.zero_ne_top (h0.symm.trans ha)
    exact ha.not_lt (himp hA)
  have hU : ∀ n : ℕ, productMeasure F ((shift F)^[n] ⁻¹' Bad) = 0 :=
    fun n => ((shift_measurePreserving F).iterate n).preimage_null hBad
  have hunion : productMeasure F (⋃ n : ℕ, (shift F)^[n] ⁻¹' Bad) = 0 :=
    measure_iUnion_null hU
  have hpre : ∀ᵐ a ∂productMeasure F, inducedShift F a ∉ Bad := by
    rw [ae_iff]
    refine measure_mono_null ?_ hunion
    intro a ha
    refine mem_iUnion.mpr ⟨returnTime F a, ?_⟩
    change (shift F)^[returnTime F a] a ∈ Bad
    exact not_not.mp ha
  exact (ae_rootMeasure_of_mem F).2 (hpre.mono fun _ ha _ => ha)

theorem gapTail_recurrence (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ a ∂rootMeasure F,
      gapTail F hb (inducedShift F a) =
        (b : ℝ) * gapTail F hb a - (returnTime F a : ℝ) := by
  filter_upwards [ae_mem_survival_root F, ae_inducedShift_mem_survival_root F,
    ae_gapTailENN_inducedShift_ne_top_root F hb]
    with a hA hSA hTS
  have hENN := gapTailENN_recurrence (hb := hb) hA hSA
  have hb0 : (b : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.2 (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hb))
  have hbT : (b : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top b
  have hmul : (b : ℝ≥0∞) * gapTailENN F hb a =
      (returnTime F a : ℝ≥0∞) + gapTailENN F hb (inducedShift F a) := by
    have hdiv : gapTailENN F hb a =
        ((returnTime F a : ℝ≥0∞) + gapTailENN F hb (inducedShift F a)) /
          (b : ℝ≥0∞) := by
      rw [hENN, ENNReal.div_add_div_same]
    rw [hdiv, mul_comm, ENNReal.div_mul_cancel hb0 hbT]
  have hR : (b : ℝ) * gapTail F hb a =
      (returnTime F a : ℝ) + gapTail F hb (inducedShift F a) := by
    have hrt := congrArg ENNReal.toReal hmul
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_add (ENNReal.natCast_ne_top _) hTS,
      ENNReal.toReal_natCast] at hrt
    exact hrt
  exact eq_sub_of_add_eq' hR.symm

noncomputable def futureRootCarry (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (ω : ResidueSpace F) : ℝ :=
  (firstHitTime F ω : ℝ) +
    gapTail F hb ((shift F)^[firstHitTime F ω] ω)

theorem futureRootCarry_eq_gapTail_on_root (F : AdmissibleFamily) {b : ℕ}
    (hb : 2 ≤ b) {ω : ResidueSpace F} (hω : ω ∈ survival F) :
    futureRootCarry F hb ω = gapTail F hb ω := by
  simp [futureRootCarry, firstHitTime_eq_zero_of_mem (F := F) hω]

theorem futureRootCarry_nonneg (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (ω : ResidueSpace F) : 0 ≤ futureRootCarry F hb ω :=
  add_nonneg (Nat.cast_nonneg _) (gapTail_nonneg F hb _)

theorem measurable_comp_shift_firstHit (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    Measurable fun ω : ResidueSpace F =>
      gapTail F hb ((shift F)^[firstHitTime F ω] ω) := by
  intro s hs
  have hpre :
      (fun ω => gapTail F hb ((shift F)^[firstHitTime F ω] ω)) ⁻¹' s =
        ⋃ n : ℕ, {ω | firstHitTime F ω = n} ∩
          ((shift F)^[n] ⁻¹' (gapTail F hb ⁻¹' s)) := by
    ext ω
    constructor
    · intro h
      exact mem_iUnion.mpr ⟨firstHitTime F ω, ⟨rfl, h⟩⟩
    · intro h
      obtain ⟨n, ⟨hn, hmem⟩⟩ := mem_iUnion.mp h
      change gapTail F hb ((shift F)^[firstHitTime F ω] ω) ∈ s
      rw [hn]
      exact hmem
  rw [hpre]
  exact MeasurableSet.iUnion fun n =>
    (measurableSet_firstHitTime_eq F n).inter
      (((shift_measurePreserving F).iterate n).measurable
        ((measurable_gapTail F hb) hs))

theorem measurable_futureRootCarry (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    Measurable (futureRootCarry F hb) :=
  ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
    (measurable_firstHitTime F)).add (measurable_comp_shift_firstHit F hb)

/-! Positivity and a.s. finiteness of `Y`. -/
theorem ae_gapTail_pos_survival (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ a ∂productMeasure F,
      a ∈ survival F → ((b : ℝ) - 1)⁻¹ ≤ gapTail F hb a :=
  (ae_rootMeasure_of_mem F).1 (gapTail_pos_on_root F hb)

theorem measure_gapTailENN_eq_top (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    productMeasure F {a | gapTailENN F hb a = ⊤} = 0 := by
  have h := gapTailENN_ae_lt_top_restrict F hb
  rw [ae_restrict_iff' (survival_measurable F), ae_iff] at h
  have hsub : {a | gapTailENN F hb a = ⊤} ⊆
      {a | ¬ (a ∈ survival F → gapTailENN F hb a < ⊤)} := by
    intro a ha
    intro himp
    have hA : a ∈ survival F := by
      by_contra hnotA
      have h0 : gapTailENN F hb a = 0 := by
        unfold gapTailENN
        rw [if_neg hnotA]
      exact ENNReal.zero_ne_top (h0.symm.trans ha)
    exact ha.not_lt (himp hA)
  exact measure_mono_null hsub h

theorem ae_forall_shift_iterate_not_mem {F : AdmissibleFamily}
    {s : Set (ResidueSpace F)} (h0 : productMeasure F s = 0) :
    ∀ᵐ ω ∂productMeasure F, ∀ k : ℕ, (shift F)^[k] ω ∉ s := by
  rw [ae_all_iff]
  intro k
  have hk : productMeasure F ((shift F)^[k] ⁻¹' s) = 0 :=
    ((shift_measurePreserving F).iterate k).preimage_null h0
  rw [ae_iff]
  have hset : {ω | ¬ (shift F)^[k] ω ∉ s} = (shift F)^[k] ⁻¹' s := by
    ext ω
    constructor
    · intro h
      exact not_not.mp h
    · intro h h'
      exact h' h
  rwa [hset]

theorem ae_landing_gapTailENN_ne_top (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ ω ∂productMeasure F,
      gapTailENN F hb ((shift F)^[firstHitTime F ω] ω) ≠ ⊤ := by
  let Bad : Set (ResidueSpace F) := {a | gapTailENN F hb a = ⊤}
  have hBad : productMeasure F Bad = 0 := measure_gapTailENN_eq_top F hb
  have hpre := ae_forall_shift_iterate_not_mem hBad
  filter_upwards [hpre] with ω hω
  exact hω (firstHitTime F ω)

theorem futureRootCarry_ae_finite (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ ω ∂productMeasure F,
      gapTailENN F hb ((shift F)^[firstHitTime F ω] ω) ≠ ⊤ :=
  ae_landing_gapTailENN_ne_top F hb

theorem futureRootCarry_pos (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ ω ∂productMeasure F, 0 < futureRootCarry F hb ω := by
  filter_upwards [firstHitTime_ae_finite F, ae_gapTail_pos_survival F hb]
    with ω hhit hT
  obtain ⟨N, hN⟩ := hhit
  by_cases hA : ω ∈ survival F
  · have hpos : 0 < ((b : ℝ) - 1)⁻¹ :=
      inv_pos.2 (sub_pos.2 (one_le_b hb))
    have hle := lt_of_lt_of_le hpos (hT hA)
    rwa [futureRootCarry_eq_gapTail_on_root F hb hA]
  · have htpos := firstHitTime_pos_of_not_mem (F := F) hA ⟨N, hN⟩
    have : (0 : ℝ) < firstHitTime F ω := Nat.cast_pos.2 htpos
    have hnn := gapTail_nonneg F hb ((shift F)^[firstHitTime F ω] ω)
    exact add_pos_of_pos_of_nonneg this hnn

/-! Paper (2.5)–(2.6). -/
theorem firstHitTime_after_root {F : AdmissibleFamily} {ω : ResidueSpace F}
    (_hA : ω ∈ survival F)
    (hret : {n : ℕ | 0 < n ∧ (shift F)^[n] ω ∈ survival F}.Nonempty)
    (hg : 1 < returnTime F ω) :
    firstHitTime F (shift F ω) = returnTime F ω - 1 ∧
      (shift F)^[firstHitTime F (shift F ω)] (shift F ω) =
        inducedShift F ω := by
  have hS : inducedShift F ω ∈ survival F := (returnTime_spec F hret).1
  have hsum : (returnTime F ω - 1).succ = returnTime F ω := by
    rw [Nat.succ_eq_add_one]
    exact Nat.sub_add_cancel (returnTime_pos F ω)
  have hland :
      (shift F)^[returnTime F ω - 1] (shift F ω) ∈ survival F := by
    rw [← iterate_succ_apply (f := shift F), hsum]
    exact hS
  have hiff := firstHitTime_eq_iff (F := F) (ω := shift F ω)
    (n := returnTime F ω - 1) (Nat.sub_pos_of_lt hg)
  have ht : firstHitTime F (shift F ω) = returnTime F ω - 1 := by
    refine hiff.mpr ⟨hland, ?_⟩
    intro k hk
    have hk' : k + 1 < returnTime F ω := by
      have hsucc : k + 1 < (returnTime F ω - 1) + 1 :=
        Nat.add_lt_add_right hk 1
      rwa [Nat.sub_add_cancel (returnTime_pos F ω)] at hsucc
    have : (shift F)^[k + 1] ω ∉ survival F :=
      (returnTime_spec F hret).2 (k + 1) (Nat.succ_pos k) hk'
    rw [← iterate_succ_apply (f := shift F)]
    exact this
  refine ⟨ht, ?_⟩
  rw [ht, ← iterate_succ_apply (f := shift F), hsum]
  rfl

theorem futureRootCarry_recurrence (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) :
    ∀ᵐ ω ∂productMeasure F,
      futureRootCarry F hb (shift F ω) =
        (b : ℝ) ^ (if ω ∈ survival F then 1 else 0) *
          futureRootCarry F hb ω - 1 := by
  have hTμ : ∀ᵐ a ∂productMeasure F,
      a ∈ survival F →
        gapTail F hb (inducedShift F a) =
          (b : ℝ) * gapTail F hb a - (returnTime F a : ℝ) :=
    (ae_rootMeasure_of_mem F).1 (gapTail_recurrence F hb)
  filter_upwards [firstHitTime_ae_finite F, returnTime_ae_finite F, hTμ]
    with ω hhit hret hTrec
  obtain ⟨N, hN⟩ := hhit
  by_cases hA : ω ∈ survival F
  · have hY : futureRootCarry F hb ω = gapTail F hb ω :=
      futureRootCarry_eq_gapTail_on_root F hb hA
    have hTeq := hTrec hA
    have hgpos := returnTime_pos F ω
    by_cases hg1 : returnTime F ω = 1
    · have hU : shift F ω ∈ survival F := by
        have := (returnTime_spec F hret).1
        rwa [hg1, iterate_one] at this
      have hYU : futureRootCarry F hb (shift F ω) = gapTail F hb (shift F ω) :=
        futureRootCarry_eq_gapTail_on_root F hb hU
      have hS : inducedShift F ω = shift F ω := by
        change (shift F)^[returnTime F ω] ω = shift F ω
        rw [hg1, iterate_one]
      rw [hYU, hY, ← hS, hTeq, hg1, if_pos hA, pow_one, Nat.cast_one]
    · have hg : 1 < returnTime F ω :=
        lt_of_le_of_ne (Nat.succ_le_of_lt hgpos) (Ne.symm hg1)
      obtain ⟨ht, hland⟩ := firstHitTime_after_root (F := F) hA hret hg
      have hcast : ((returnTime F ω - 1 : ℕ) : ℝ) = (returnTime F ω : ℝ) - 1 :=
        Nat.cast_pred hgpos
      have hYU : futureRootCarry F hb (shift F ω) =
          (firstHitTime F (shift F ω) : ℝ) +
            gapTail F hb ((shift F)^[firstHitTime F (shift F ω)] (shift F ω)) :=
        rfl
      rw [hYU]
      rw [ht] at hland ⊢
      rw [hland, hTeq, hY, hcast, if_pos hA, pow_one]
      linarith
  · have htpos := firstHitTime_pos_of_not_mem (F := F) hA ⟨N, hN⟩
    have ht := firstHitTime_shift_of_not_mem (F := F) hA ⟨N, hN⟩
    have hland :
        (shift F)^[firstHitTime F (shift F ω)] (shift F ω) =
          (shift F)^[firstHitTime F ω] ω := by
      rw [ht, ← iterate_succ_apply (f := shift F), Nat.succ_eq_add_one,
        Nat.sub_add_cancel htpos]
    have hcast : ((firstHitTime F ω - 1 : ℕ) : ℝ) = (firstHitTime F ω : ℝ) - 1 :=
      Nat.cast_pred htpos
    unfold futureRootCarry
    rw [if_neg hA, pow_zero, one_mul, ht]
    rw [ht] at hland
    rw [hland, hcast]
    linarith

theorem mul_futureRootCarry_recurrence (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    {Q : ℝ} (_hQ : 0 < Q) :
    ∀ᵐ ω ∂productMeasure F,
      Q * futureRootCarry F hb (shift F ω) =
        (b : ℝ) ^ (if ω ∈ survival F then 1 else 0) *
          (Q * futureRootCarry F hb ω) - Q := by
  filter_upwards [futureRootCarry_recurrence F hb] with ω hrec
  calc
    Q * futureRootCarry F hb (shift F ω)
        = Q * ((b : ℝ) ^ (if ω ∈ survival F then 1 else 0) *
            futureRootCarry F hb ω - 1) := by rw [hrec]
    _ = (b : ℝ) ^ (if ω ∈ survival F then 1 else 0) *
          (Q * futureRootCarry F hb ω) - Q := by
        rw [mul_sub, mul_left_comm, mul_one]

theorem integer_gapTail_to_integer_futureRootCarry (F : AdmissibleFamily)
    {b : ℕ} (hb : 2 ≤ b) {Q : ℕ} (_hQ : 0 < Q)
    (hint : ∀ᵐ a ∂rootMeasure F, ∃ n : ℤ, (Q : ℝ) * gapTail F hb a = n) :
    ∀ᵐ ω ∂productMeasure F, ∃ n : ℕ, (Q : ℝ) * futureRootCarry F hb ω = n := by
  have hintμ : ∀ᵐ a ∂productMeasure F,
      a ∈ survival F → ∃ n : ℤ, (Q : ℝ) * gapTail F hb a = n :=
    (ae_rootMeasure_of_mem F).1 hint
  let Bad : Set (ResidueSpace F) :=
    {a | a ∈ survival F ∧ ∀ n : ℤ, (Q : ℝ) * gapTail F hb a ≠ n}
  have hBad : productMeasure F Bad = 0 := by
    rw [ae_iff] at hintμ
    refine measure_mono_null ?_ hintμ
    intro a ha h
    obtain ⟨n, hn⟩ := h ha.1
    exact ha.2 n hn
  have hpre := ae_forall_shift_iterate_not_mem hBad
  filter_upwards [firstHitTime_ae_finite F, hpre] with ω hhit hgood
  obtain ⟨N, hN⟩ := hhit
  have hlandA := (firstHitTime_spec (F := F) ⟨N, hN⟩).1
  have hlandGood : ∃ n : ℤ,
      (Q : ℝ) * gapTail F hb ((shift F)^[firstHitTime F ω] ω) = n := by
    by_contra hne
    exact hgood (firstHitTime F ω) ⟨hlandA, fun n hn => hne ⟨n, hn⟩⟩
  obtain ⟨n, hn⟩ := hlandGood
  let m : ℤ := (Q : ℤ) * (firstHitTime F ω : ℤ) + n
  have hmR : (m : ℝ) = (Q : ℝ) * futureRootCarry F hb ω := by
    unfold m futureRootCarry
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ← hn, ← mul_add]
  have hm0 : (0 : ℤ) ≤ m := by
    have : (0 : ℝ) ≤ (m : ℝ) := by
      rw [hmR]
      exact mul_nonneg (Nat.cast_nonneg _) (futureRootCarry_nonneg F hb ω)
    exact Int.cast_nonneg_iff.mp this
  refine ⟨m.toNat, ?_⟩
  have hmNat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
  calc
    (Q : ℝ) * futureRootCarry F hb ω = (m : ℝ) := hmR.symm
    _ = ((m.toNat : ℤ) : ℝ) := by rw [hmNat]
    _ = (m.toNat : ℝ) := Int.cast_natCast _

/-! ### 7.12 Lemma 4.1 — lattice distance, truncated model tail, mean remainder -/

/-- Distance from a real to the integer lattice.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1;
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
noncomputable def distInt (x : ℝ) : ℝ :=
  Metric.infDist x (range fun n : ℤ => (n : ℝ))

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1;
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem distInt_eq_abs_sub_round (x : ℝ) : distInt x = |x - round x| := by
  unfold distInt
  refine le_antisymm ?upper ?lower
  · have hmem : (round x : ℝ) ∈ range ((↑) : ℤ → ℝ) := ⟨round x, rfl⟩
    simpa [Real.dist_eq] using Metric.infDist_le_dist_of_mem (x := x) hmem
  · rw [Metric.le_infDist (range_nonempty ((↑) : ℤ → ℝ))]
    intro y hy
    obtain ⟨n, rfl⟩ := hy
    simpa [Real.dist_eq] using round_le x n

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1;
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem distInt_nonneg (x : ℝ) : 0 ≤ distInt x :=
  Metric.infDist_nonneg

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1;
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem distInt_le_half (x : ℝ) : distInt x ≤ 1 / 2 := by
  rw [distInt_eq_abs_sub_round]
  exact abs_sub_round x

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1;
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem distInt_eq_zero_iff_mem (x : ℝ) :
    distInt x = 0 ↔ x ∈ range fun n : ℤ => (n : ℝ) := by
  constructor
  · intro h
    rw [distInt_eq_abs_sub_round] at h
    refine ⟨round x, ?_⟩
    exact (sub_eq_zero.mp (abs_eq_zero.mp h)).symm
  · intro hx
    unfold distInt
    exact Metric.infDist_zero_of_mem hx

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1;
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem measurable_distInt : Measurable distInt :=
  (Metric.lipschitz_infDist_pt (range fun n : ℤ => (n : ℝ))).continuous.measurable

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1;
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem distInt_Q_lipschitz {Q : ℝ} (hQ : 0 ≤ Q) :
    LipschitzWith ⟨Q, hQ⟩ (fun t => distInt (Q * t)) := by
  let K : ℝ≥0 := ⟨Q, hQ⟩
  have hK : (K : ℝ) = Q := rfl
  have hmul : LipschitzWith K fun t : ℝ => Q * t :=
    LipschitzWith.of_dist_le_mul fun x y => by
      have : dist (Q * x) (Q * y) = (K : ℝ) * dist x y := by
        simp [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hQ, hK]
      exact le_of_eq this
  have hdist : LipschitzWith 1 distInt :=
    Metric.lipschitz_infDist_pt (range fun n : ℤ => (n : ℝ))
  have hcomp : LipschitzWith (1 * K) fun t => distInt (Q * t) := by
    convert hdist.comp hmul
    rfl
  rwa [one_mul] at hcomp

/-- Elementary Lipschitz triangle. The paper bound
`distInt (Q * trunc) ≤ Q * (T - trunc)` is the special case
`distInt (Q * T) = 0` (lattice-valued full tail).

Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1;
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem distInt_le_trunc {Q : ℝ} (hQ : 0 ≤ Q) {T trunc : ℝ} (hle : trunc ≤ T) :
    distInt (Q * trunc) ≤ distInt (Q * T) + Q * (T - trunc) := by
  have h1 : distInt (Q * trunc) ≤
      distInt (Q * T) + dist (distInt (Q * trunc)) (distInt (Q * T)) := by
    rw [Real.dist_eq, ← sub_le_iff_le_add']
    exact le_abs_self _
  have h2 : dist (distInt (Q * trunc)) (distInt (Q * T)) ≤ Q * dist trunc T := by
    have hLip := (distInt_Q_lipschitz hQ).dist_le_mul trunc T
    have hK : ((⟨Q, hQ⟩ : ℝ≥0) : ℝ) = Q := rfl
    convert hLip
    exact hK.symm
  have h3 : dist trunc T = T - trunc := by
    rw [Real.dist_eq, abs_sub_comm trunc T, abs_of_nonneg (sub_nonneg.2 hle)]
  calc
    distInt (Q * trunc)
        ≤ distInt (Q * T) + dist (distInt (Q * trunc)) (distInt (Q * T)) := h1
    _ ≤ distInt (Q * T) + Q * dist trunc T := add_le_add le_rfl h2
    _ = distInt (Q * T) + Q * (T - trunc) := by rw [h3]

/-- Truncated model gap tail as an `ℝ≥0∞` finite sum. Zero off `survival`, matching
`gapTailENN`.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
noncomputable def gapTailTruncENN (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ)
    (ω : ResidueSpace F) : ℝ≥0∞ :=
  if ω ∈ survival F then ∑ j ∈ Finset.range J, gapTailTermENN F hb ω j else 0

/-- Truncated model gap tail on `A`:
`∑ j ∈ range J, (returnTime (inducedShift^[j] a) : ℝ) / (b : ℝ)^(j+1)`.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
noncomputable def gapTailTrunc (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    ResidueSpace F → ℝ :=
  fun ω => (gapTailTruncENN F hb J ω).toReal

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem gapTailTrunc_nonneg (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ)
    (ω : ResidueSpace F) : 0 ≤ gapTailTrunc F hb J ω :=
  ENNReal.toReal_nonneg

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem gapTailTermENN_eq_ofReal (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (ω : ResidueSpace F) (j : ℕ) :
    gapTailTermENN F hb ω j =
      ENNReal.ofReal
        ((returnTime F ((inducedShift F)^[j] ω) : ℝ) / (b : ℝ) ^ (j + 1)) := by
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans (one_le_b hb)
  have hpow : 0 < (b : ℝ) ^ (j + 1) := pow_pos hb0 _
  unfold gapTailTermENN
  rw [← ENNReal.ofReal_natCast (n := returnTime F ((inducedShift F)^[j] ω)),
    ← ENNReal.ofReal_natCast (n := b), ← ENNReal.ofReal_pow (Nat.cast_nonneg b),
    ENNReal.ofReal_div_of_pos hpow]

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem gapTailTruncENN_ne_top (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ)
    (ω : ResidueSpace F) : gapTailTruncENN F hb J ω ≠ ⊤ := by
  unfold gapTailTruncENN
  split_ifs with hA
  ·   exact (ENNReal.sum_lt_top.2 fun j _ =>
      lt_top_iff_ne_top.mpr (gapTailTermENN_ne_top F hb ω j)).ne
  · exact ENNReal.zero_ne_top

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem gapTailTrunc_eq_sum (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ)
    {ω : ResidueSpace F} (hω : ω ∈ survival F) :
    gapTailTrunc F hb J ω =
      ∑ j ∈ Finset.range J,
        (returnTime F ((inducedShift F)^[j] ω) : ℝ) / (b : ℝ) ^ (j + 1) := by
  unfold gapTailTrunc gapTailTruncENN
  rw [if_pos hω, ENNReal.toReal_sum fun j _ => gapTailTermENN_ne_top F hb ω j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gapTailTermENN_eq_ofReal F hb ω j, ENNReal.toReal_ofReal]
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem measurable_gapTailTruncENN (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    Measurable (gapTailTruncENN F hb J) :=
  Measurable.ite (survival_measurable F)
    (Finset.measurable_sum (Finset.range J) fun j _ => measurable_gapTailTermENN F hb j)
    measurable_const

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem measurable_gapTailTrunc (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    Measurable (gapTailTrunc F hb J) :=
  ENNReal.measurable_toReal.comp (measurable_gapTailTruncENN F hb J)

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem gapTailTrunc_le_gapTail (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    ∀ᵐ a ∂rootMeasure F, gapTailTrunc F hb J a ≤ gapTail F hb a := by
  filter_upwards [gapTail_ae_finite_on_root F hb, ae_mem_survival_root F] with a htop hA
  unfold gapTail gapTailTrunc
  have hle : gapTailTruncENN F hb J a ≤ gapTailENN F hb a := by
    simp only [gapTailTruncENN, gapTailENN, hA, ite_true]
    exact ENNReal.sum_le_tsum _
  exact ENNReal.toReal_mono htop hle

/-- Finite geometric sum matching the Kac remainder.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem sum_geom_inv_b_range {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    ∑ j ∈ Finset.range J, ((1 : ℝ) / b) ^ (j + 1) =
      (1 - (b : ℝ) ^ (-(J : ℤ))) / ((b : ℝ) - 1) := by
  have hb1 : (1 : ℝ) < b := one_le_b hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  have hr : (1 : ℝ) / b ≠ 1 := ne_of_lt ((div_lt_one hb0).2 hb1)
  have hz : ((1 : ℝ) / b) ^ J = (b : ℝ) ^ (-(J : ℤ)) := by
    rw [one_div, inv_pow, zpow_neg, zpow_natCast]
  have hneg :
      (((1 : ℝ) / b) ^ J - 1) / ((1 : ℝ) / b - 1) =
        (1 - ((1 : ℝ) / b) ^ J) / (1 - (1 : ℝ) / b) := by
    rw [← neg_div_neg_eq]
    congr 1 <;> ring
  have h1r : 1 - (1 : ℝ) / b = ((b : ℝ) - 1) / b := by
    rw [← div_self hb0.ne', sub_div]
  have hden : (b : ℝ) - 1 ≠ 0 := sub_ne_zero.2 hb1.ne'
  simp_rw [pow_succ']
  rw [← Finset.mul_sum, geom_sum_eq hr J, hneg, h1r]
  have hfin :
      (1 : ℝ) / b * ((1 - ((1 : ℝ) / b) ^ J) / (((b : ℝ) - 1) / b)) =
        (1 - ((1 : ℝ) / b) ^ J) / ((b : ℝ) - 1) := by
    field_simp [hb0.ne', hden]
  rw [hfin, hz]

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem geom_sum_inv_b_range_ennreal {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    ∑ j ∈ Finset.range J, ((b : ℝ≥0∞)⁻¹) ^ (j + 1) =
      ENNReal.ofReal (∑ j ∈ Finset.range J, ((1 : ℝ) / b) ^ (j + 1)) := by
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans (one_le_b hb)
  have hterm : ∀ j : ℕ,
      ((b : ℝ≥0∞)⁻¹) ^ (j + 1) = ENNReal.ofReal (((1 : ℝ) / b) ^ (j + 1)) := by
    intro j
    have : (b : ℝ≥0∞) = ENNReal.ofReal (b : ℝ) := (ENNReal.ofReal_natCast (n := b)).symm
    rw [this, ← ENNReal.ofReal_inv_of_pos hb0, ← ENNReal.ofReal_pow
      (inv_nonneg.2 (le_of_lt hb0)), one_div]
  simp_rw [hterm]
  exact (ENNReal.ofReal_sum_of_nonneg fun j _ =>
    pow_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _)) _).symm

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem lintegral_gapTailTruncENN_survival (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (J : ℕ) :
    ∫⁻ ω in survival F, gapTailTruncENN F hb J ω ∂productMeasure F =
      ∑ j ∈ Finset.range J, ((b : ℝ≥0∞)⁻¹) ^ (j + 1) := by
  have hfun : EqOn (gapTailTruncENN F hb J)
      (fun ω => ∑ j ∈ Finset.range J, gapTailTermENN F hb ω j) (survival F) := by
    intro ω hω
    simp [gapTailTruncENN, hω]
  rw [setLIntegral_congr_fun (survival_measurable F) hfun,
    lintegral_finsetSum (Finset.range J) fun j _ => measurable_gapTailTermENN F hb j]
  exact Finset.sum_congr rfl fun j _ => lintegral_gapTailTermENN_survival F hb j

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem lintegral_gapTailTruncENN_root (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (J : ℕ) :
    ∫⁻ a, gapTailTruncENN F hb J a ∂rootMeasure F =
      ENNReal.ofReal
        ((rho F)⁻¹ * ∑ j ∈ Finset.range J, ((1 : ℝ) / b) ^ (j + 1)) := by
  unfold rootMeasure
  rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul,
    lintegral_gapTailTruncENN_survival F hb J, measure_survival,
    geom_sum_inv_b_range_ennreal hb J, ← ENNReal.ofReal_inv_of_pos (rho_pos F),
    ← ENNReal.ofReal_mul (inv_nonneg.2 (rho_pos F).le)]

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem integrable_gapTailTrunc (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    Integrable (gapTailTrunc F hb J) (rootMeasure F) := by
  refine integrable_toReal_of_lintegral_ne_top
    (measurable_gapTailTruncENN F hb J).aemeasurable ?_
  rw [lintegral_gapTailTruncENN_root F hb J]
  exact ENNReal.ofReal_ne_top

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem expected_gapTailTrunc (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    ∫ a, gapTailTrunc F hb J a ∂rootMeasure F =
      (1 - (b : ℝ) ^ (-(J : ℤ))) / (rho F * ((b : ℝ) - 1)) := by
  have hnn : 0 ≤ᵐ[rootMeasure F] gapTailTrunc F hb J :=
    Filter.Eventually.of_forall (gapTailTrunc_nonneg F hb J)
  rw [integral_eq_lintegral_of_nonneg_ae hnn
    (measurable_gapTailTrunc F hb J).aestronglyMeasurable]
  have hcongr : (fun a => ENNReal.ofReal (gapTailTrunc F hb J a)) =
      gapTailTruncENN F hb J := by
    funext a
    exact ENNReal.ofReal_toReal (gapTailTruncENN_ne_top F hb J a)
  rw [hcongr, lintegral_gapTailTruncENN_root F hb J, ENNReal.toReal_ofReal, sum_geom_inv_b_range hb J]
  · rw [← div_eq_inv_mul, div_div, mul_comm ((b : ℝ) - 1)]
  · exact mul_nonneg (inv_nonneg.2 (rho_pos F).le)
      (Finset.sum_nonneg fun _ _ =>
        pow_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _)) _)

/-- Model identity (4.1) right-hand side. Kac on `A` plus the geometric remainder;
not CanonicalTransfer.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.1);
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem expected_gapTail_sub_trunc (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    ∫ a, (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F =
      (b : ℝ) ^ (-(J : ℤ)) / (rho F * ((b : ℝ) - 1)) := by
  rw [integral_sub (integrable_gapTail_root F hb) (integrable_gapTailTrunc F hb J),
    expected_gapTail F hb, expected_gapTailTrunc F hb J]
  rw [inv_eq_one_div, div_sub_div_same, sub_sub_self]

/-- Bounded lattice test of a measurable real function is integrable on the root.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1;
`lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem integrable_distInt_mul (F : AdmissibleFamily) {Q : ℕ}
    {f : ResidueSpace F → ℝ} (hf : Measurable f) :
    Integrable (fun a => distInt ((Q : ℝ) * f a)) (rootMeasure F) := by
  refine (integrable_const ((1 : ℝ) / 2)).mono' ?_ ?_
  · exact (measurable_distInt.comp (hf.const_mul (Q : ℝ))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (distInt_nonneg _)]
    exact distInt_le_half _

/-- Lemma 4.1, hypothesis form. `hβ` is the rational seed `Q β_b ∈ ℤ`
(`gapSeries` lives in `Definitions`, so no Series import). Carry does **not**
consume `hβ`: the canonical recurrence `Q T_n ∈ ℤ` and the J-gap/Palm transfer
of `f = distInt ∘ (Q * ·)` are C4 facts. They are packaged as `h_trunc_mean`
(paper (4.3) after (21)). Lipschitz plus `expected_gapTail_sub_trunc → 0`
does not by itself use rationality.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1;
`lean/BFREE_CARRY_LEMMAS.md` §7.12; `lean/BFREE_IRRATIONALITY.md` §§4.4–5.3.
Contract: C3
Audit: GREEN -/
theorem rational_posSeries_to_lattice_gapTail
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) {Q : ℕ} (hQ : 0 < Q)
    (_hβ : (Q : ℝ) * gapSeries F b ∈ range fun n : ℤ => (n : ℝ))
    (h_trunc_mean : ∀ J : ℕ,
      ∫ a, distInt ((Q : ℝ) * gapTailTrunc F hb J a) ∂rootMeasure F
        ≤ (Q : ℝ) *
          ∫ a, (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F) :
    ∀ᵐ a ∂rootMeasure F, ∃ n : ℤ, (Q : ℝ) * gapTail F hb a = n := by
  have hQ0 : (0 : ℝ) ≤ Q := (Nat.cast_pos.mpr hQ).le
  have hfT :
      Integrable (fun a => distInt ((Q : ℝ) * gapTail F hb a)) (rootMeasure F) :=
    integrable_distInt_mul F (measurable_gapTail F hb)
  have hI :
      0 ≤ ∫ a, distInt ((Q : ℝ) * gapTail F hb a) ∂rootMeasure F :=
    integral_nonneg fun _ => distInt_nonneg _
  have hbound : ∀ J : ℕ,
      ∫ a, distInt ((Q : ℝ) * gapTail F hb a) ∂rootMeasure F
        ≤ (2 : ℝ) * Q * (b : ℝ) ^ (-(J : ℤ)) /
            (rho F * ((b : ℝ) - 1)) := by
    intro J
    have hfTr :
        Integrable (fun a => distInt ((Q : ℝ) * gapTailTrunc F hb J a))
          (rootMeasure F) :=
      integrable_distInt_mul F (measurable_gapTailTrunc F hb J)
    have hsub :
        Integrable (fun a => gapTail F hb a - gapTailTrunc F hb J a)
          (rootMeasure F) :=
      (integrable_gapTail_root F hb).sub (integrable_gapTailTrunc F hb J)
    have hQsub :
        Integrable
          (fun a => (Q : ℝ) * (gapTail F hb a - gapTailTrunc F hb J a))
          (rootMeasure F) :=
      hsub.const_mul _
    have hsum :
        Integrable
          (fun a =>
            distInt ((Q : ℝ) * gapTailTrunc F hb J a) +
              (Q : ℝ) * (gapTail F hb a - gapTailTrunc F hb J a))
          (rootMeasure F) :=
      hfTr.add hQsub
    have hlip :
        (fun a => distInt ((Q : ℝ) * gapTail F hb a)) ≤ᵐ[rootMeasure F]
          fun a =>
            distInt ((Q : ℝ) * gapTailTrunc F hb J a) +
              (Q : ℝ) * (gapTail F hb a - gapTailTrunc F hb J a) := by
      filter_upwards [gapTailTrunc_le_gapTail F hb J] with a hle
      have htri :=
        (distInt_Q_lipschitz hQ0).le_add_mul (gapTail F hb a)
          (gapTailTrunc F hb J a)
      have hd :
          dist (gapTail F hb a) (gapTailTrunc F hb J a) =
            gapTail F hb a - gapTailTrunc F hb J a := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hle)]
      have hK : ((⟨(Q : ℝ), hQ0⟩ : ℝ≥0) : ℝ) = (Q : ℝ) := rfl
      have htri' :
          distInt ((Q : ℝ) * gapTail F hb a) ≤
            distInt ((Q : ℝ) * gapTailTrunc F hb J a) +
              (Q : ℝ) * dist (gapTail F hb a) (gapTailTrunc F hb J a) := by
        convert htri
        exact hK.symm
      rwa [hd] at htri'
    have hinter := integral_mono_ae hfT hsum hlip
    have hadd := integral_add hfTr hQsub
    have hmul :
        ∫ a, (Q : ℝ) * (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F =
          (Q : ℝ) *
            ∫ a, (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F :=
      integral_const_mul (μ := rootMeasure F) (Q : ℝ)
        (fun a => gapTail F hb a - gapTailTrunc F hb J a)
    have htail := expected_gapTail_sub_trunc F hb J
    have hmean := h_trunc_mean J
    calc
      ∫ a, distInt ((Q : ℝ) * gapTail F hb a) ∂rootMeasure F
          ≤ ∫ a,
              distInt ((Q : ℝ) * gapTailTrunc F hb J a) +
                (Q : ℝ) * (gapTail F hb a - gapTailTrunc F hb J a)
              ∂rootMeasure F := hinter
      _ = ∫ a, distInt ((Q : ℝ) * gapTailTrunc F hb J a) ∂rootMeasure F +
            (Q : ℝ) *
              ∫ a, (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F := by
          rw [hadd, hmul]
      _ ≤ (Q : ℝ) *
              ∫ a, (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F +
            (Q : ℝ) *
              ∫ a, (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F :=
          add_le_add hmean le_rfl
      _ = (2 : ℝ) * Q *
            ∫ a, (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F := by
          ring
      _ = (2 : ℝ) * Q *
            ((b : ℝ) ^ (-(J : ℤ)) / (rho F * ((b : ℝ) - 1))) := by
          rw [htail]
      _ = (2 : ℝ) * Q * (b : ℝ) ^ (-(J : ℤ)) /
            (rho F * ((b : ℝ) - 1)) := by
          rw [mul_div_assoc]
  have hb1 : (1 : ℝ) < b := one_le_b hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb1
  have hpow : Tendsto (fun J : ℕ => (b : ℝ) ^ (-(J : ℤ))) atTop (𝓝 0) := by
    have heq : (fun J : ℕ => (b : ℝ) ^ (-(J : ℤ))) =
        fun J : ℕ => (b : ℝ)⁻¹ ^ J := by
      funext J
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [heq]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hb0.le)
      (inv_lt_one_of_one_lt₀ hb1)
  have hlim : Tendsto (fun J : ℕ =>
      (2 : ℝ) * Q * (b : ℝ) ^ (-(J : ℤ)) /
        (rho F * ((b : ℝ) - 1))) atTop (𝓝 0) := by
    have hfun :
        (fun J : ℕ =>
          (2 : ℝ) * Q * (b : ℝ) ^ (-(J : ℤ)) /
            (rho F * ((b : ℝ) - 1))) =
          fun J : ℕ =>
            ((2 : ℝ) * Q / (rho F * ((b : ℝ) - 1))) *
              (b : ℝ) ^ (-(J : ℤ)) := by
      funext J
      ring
    rw [hfun]
    simpa using
      Filter.Tendsto.const_mul ((2 : ℝ) * Q / (rho F * ((b : ℝ) - 1))) hpow
  have hle0 :
      ∫ a, distInt ((Q : ℝ) * gapTail F hb a) ∂rootMeasure F ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
  have hzero :
      ∫ a, distInt ((Q : ℝ) * gapTail F hb a) ∂rootMeasure F = 0 :=
    le_antisymm hle0 hI
  have hae :=
    (integral_eq_zero_iff_of_nonneg (fun a => distInt_nonneg ((Q : ℝ) * gapTail F hb a))
      hfT).1 hzero
  filter_upwards [hae] with a ha
  obtain ⟨n, hn⟩ := mem_range.mp ((distInt_eq_zero_iff_mem _).1 ha)
  exact ⟨n, hn.symm⟩

/-- Lemma 4.1 plus (2.6) and Theorem 3.3 / 7.8: a rational gap series with the
Palm transfer of the Lipschitz test cannot produce a positive integer affine
carry. Does not claim `posSeries_irrational`. Same explicit hyp `h_trunc_mean`
as `rational_posSeries_to_lattice_gapTail`.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` Lemma 4.1, (2.6),
Theorem 3.3; `lean/BFREE_CARRY_LEMMAS.md` §7.12.
Contract: C3
Audit: GREEN -/
theorem rational_posSeries_to_lattice_carry
    (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) {Q : ℕ} (hQ : 0 < Q)
    (hβ : (Q : ℝ) * gapSeries F b ∈ range fun n : ℤ => (n : ℝ))
    (h_trunc_mean : ∀ J : ℕ,
      ∫ a, distInt ((Q : ℝ) * gapTailTrunc F hb J a) ∂rootMeasure F
        ≤ (Q : ℝ) *
          ∫ a, (gapTail F hb a - gapTailTrunc F hb J a) ∂rootMeasure F) :
    False := by
  have hintA :=
    rational_posSeries_to_lattice_gapTail F hb hQ hβ h_trunc_mean
  have hintY :=
    integer_gapTail_to_integer_futureRootCarry F hb hQ hintA
  have hC :
      Measurable fun ω => (Q : ℝ) * futureRootCarry F hb ω :=
    (measurable_futureRootCarry F hb).const_mul _
  have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hpos : ∀ᵐ ω ∂productMeasure F,
      0 < (Q : ℝ) * futureRootCarry F hb ω := by
    filter_upwards [futureRootCarry_pos F hb] with ω hω
    exact mul_pos hQpos hω
  have hrec := mul_futureRootCarry_recurrence F hb hQpos
  exact no_positive_integer_affine_carry F hb hQpos hC hpos hintY hrec

end PrimeGapNormality.BFree

