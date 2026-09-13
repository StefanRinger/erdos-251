import PrimeGapNormality.Prime.CoreJointEquidistribution
import PrimeGapNormality.Prime.CoreLocalRelations

/-!
# Literal joint equidistribution of actual local prime-gap series

The same effective-degree D input gives weak convergence of the actual
joint orbit, all continuous test averages, and literal half-open box
frequencies. The finite coordinate set may be empty.
-/

namespace PrimeGapNormality.Prime.CoreJointEquidistribution

open Set Filter MeasureTheory Finset
open scoped Topology ENNReal Classical

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

local instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp⟩

def box {I : Type*} (a b : I → ℝ) : Set (Torus I) :=
  Set.univ.pi (fun i => CoreWeylNormality.arc (a i) (b i))

theorem measurableSet_box {I : Type*} [Fintype I] (a b : I → ℝ)
    (hw : ∀ i, b i < a i + 1) : MeasurableSet (box a b) :=
  MeasurableSet.univ_pi (fun i => CoreWeylNormality.measurableSet_arc (hw i))

theorem frontier_box_null {I : Type*} [Fintype I] (a b : I → ℝ) :
    volume (frontier (box a b)) = 0 := by
  have hsub : frontier (box a b) ⊆
      ⋃ i, (Function.eval i) ⁻¹' frontier (CoreWeylNormality.arc (a i) (b i)) := by
    intro x hx
    rw [box, frontier, closure_pi_set, interior_pi_set Set.finite_univ] at hx
    rcases hx with ⟨hcl, hni⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies] at hcl hni
    obtain ⟨i, hi⟩ := not_forall.mp hni
    exact Set.mem_iUnion.2 ⟨i, ⟨hcl i, hi⟩⟩
  apply measure_mono_null hsub
  apply measure_iUnion_null
  intro i
  have hm := measurePreserving_eval
    (fun _ : I => (volume : Measure (AddCircle (1 : ℝ)))) i
  exact (hm.measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet).trans
    (CoreWeylNormality.frontier_arc_null (a i) (b i))

theorem volume_box_real {I : Type*} [Fintype I] (a b : I → ℝ)
    (hab : ∀ i, a i ≤ b i) (hw : ∀ i, b i < a i + 1) :
    (volume : Measure (Torus I)).real (box a b) = ∏ i, (b i - a i) := by
  change (Measure.pi (fun _ : I => (volume : Measure (AddCircle (1 : ℝ))))).real
    (Set.univ.pi fun i => CoreWeylNormality.arc (a i) (b i)) = _
  rw [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [CoreWeylNormality.volume_arc (hw i), ENNReal.toReal_ofReal (sub_nonneg.mpr (hab i))]

private theorem card_fin_pred (N : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    Fintype.card {i : Fin N // p i} = ((range N).filter p).card := by
  have h := Fin.sum_univ_eq_sum_range (fun n : ℕ => if p n then (1 : ℕ) else 0) N
  simpa only [sum_boole, Fintype.card_subtype, Nat.cast_id, id_eq] using h

/-- Exact set-count identity for the actual uniform orbit law. -/
theorem empirical_apply {I : Type*} [Fintype I]
    (b : I → ℕ) (θ : I → ℝ) {N : ℕ} (hN : 0 < N)
    (s : Set (Torus I)) (hs : MeasurableSet s) :
    (empirical b θ N : Measure (Torus I)) s =
      (((range N).filter (fun n => orbit b θ n ∈ s)).card : ℝ≥0∞) / N := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hf : Measurable (fun i : Fin N => orbit b θ i) := measurable_of_finite _
  have hmeasure : (empirical b θ N : Measure (Torus I)) =
      ((PMF.uniformOfFintype (Fin N)).map (fun i : Fin N => orbit b θ i)).toMeasure := by
    unfold empirical
    rw [dif_pos hN]
    rfl
  rw [hmeasure, PMF.toMeasure_map_apply _ (PMF.uniformOfFintype (Fin N)) s hf hs,
    PMF.toMeasure_uniformOfFintype_apply _ (hs.preimage hf)]
  simp only [Fintype.card_fin]
  change ((Fintype.card {i : Fin N // orbit b θ (i : ℕ) ∈ s} : ℝ≥0∞) / (N : ℝ≥0∞)) = _
  rw [card_fin_pred N (fun n => orbit b θ n ∈ s)]

theorem empirical_real_apply {I : Type*} [Fintype I]
    (b : I → ℕ) (θ : I → ℝ) {N : ℕ} (hN : 0 < N)
    (s : Set (Torus I)) (hs : MeasurableSet s) :
    (empirical b θ N : Measure (Torus I)).real s =
      (((range N).filter (fun n => orbit b θ n ∈ s)).card : ℝ) / N := by
  rw [Measure.real, empirical_apply b θ hN s hs]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]

/-- Literal simultaneous fractional-part box frequencies. Intervals are
half open inside [0,1], of length less than one; these form a box basis. -/
theorem box_frequency_of_jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I] {base : I → ℕ} {θ : I → ℝ}
    (h : JointWeyl base θ) (a b : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ 1)
    (hw : ∀ i, b i < a i + 1) :
    Tendsto (fun N : ℕ => (((range N).filter (fun n =>
      ∀ i, Int.fract ((base i : ℝ) ^ n * θ i) ∈ Ico (a i) (b i))).card : ℝ) / N)
      atTop (𝓝 (∏ i, (b i - a i))) := by
  have hnull : (torusVolume I : Measure (Torus I)) (frontier (box a b)) = 0 :=
    frontier_box_null a b
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (empirical_tendsto_of_jointWeyl h) hnull
  have hreal := (ENNReal.tendsto_toReal
    (measure_ne_top (volume : Measure (Torus I)) (box a b))).comp hlim
  have hmass : ((volume : Measure (Torus I)) (box a b)).toReal = ∏ i, (b i - a i) :=
    volume_box_real a b hab hw
  have ht : Tendsto (fun N => (empirical base θ N : Measure (Torus I)).real (box a b))
      atTop (𝓝 (∏ i, (b i - a i))) := by
    simpa only [Measure.real, Function.comp_def, hmass] using hreal
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [empirical_real_apply base θ hN (box a b) (measurableSet_box a b hw)]
  have hfilter : (range N).filter (fun n => orbit base θ n ∈ box a b) =
      (range N).filter (fun n => ∀ i,
        Int.fract ((base i : ℝ) ^ n * θ i) ∈ Ico (a i) (b i)) := by
    apply Finset.filter_congr
    intro n hn
    simp only [box, Set.mem_pi, Set.mem_univ, true_implies, orbit]
    exact forall_congr' fun i => CoreWeylNormality.coe_mem_arc_iff_fract (ha i) (hb i) _
  rw [hfilter]

end
end PrimeGapNormality.Prime.CoreJointEquidistribution

namespace PrimeGapNormality.Prime.CorePrimeLocalJointEnd

open Filter MeasureTheory CoreCyclic CoreJointEquidistribution
open scoped Topology Classical
noncomputable section

/-- Actual joint probability convergence at the paper's B^k clock. -/
theorem empirical_tendsto_of_D {I : Type*} [Fintype I] [DecidableEq I]
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    Tendsto (empirical (fun _ : I => B ^ k)
      (fun i => coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (F i)))
      atTop (𝓝 (torusVolume I)) :=
  empirical_tendsto_of_jointWeyl
    (CoreLocalRelations.jointWeyl_of_independent_normalForms_of_D
      hB hk phase F hdeg hlin hκ hd0 hc hD)

theorem continuous_test_tendsto_of_D {I : Type*} [Fintype I] [DecidableEq I]
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) (f : C(Torus I, ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (fun i =>
      ((((B ^ k : ℕ) : ℝ) ^ n *
        coreCyclicFullSeries B hk phase (fun q => (primeGap q : ℝ)) (F i) : ℝ) :
          AddCircle (1 : ℝ)))) / N) atTop (𝓝 (∫ x : Torus I, f x)) :=
  continuous_test_tendsto_of_jointWeyl
    (CoreLocalRelations.jointWeyl_of_independent_normalForms_of_D
      hB hk phase F hdeg hlin hκ hd0 hc hD) f

/-- In particular, every literal half-open coordinate box has the correct
frequency along the actual simultaneous B^{kN} orbit. -/
theorem box_frequency_of_D {I : Type*} [Fintype I] [DecidableEq I]
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c)
    (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hb : ∀ i, b i ≤ 1) (hw : ∀ i, b i < a i + 1) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter (fun n => ∀ i,
      Int.fract (((B ^ k : ℕ) : ℝ) ^ n *
        coreCyclicFullSeries B hk phase (fun q => (primeGap q : ℝ)) (F i)) ∈
          Set.Ico (a i) (b i))).card : ℝ) / N) atTop (𝓝 (∏ i, (b i - a i))) :=
  box_frequency_of_jointWeyl
    (CoreLocalRelations.jointWeyl_of_independent_normalForms_of_D
      hB hk phase F hdeg hlin hκ hd0 hc hD) a b ha hab hb hw

end
end PrimeGapNormality.Prime.CorePrimeLocalJointEnd
