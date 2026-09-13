import PrimeGapNormality.Prime.CoreRectangleMeasureDomination
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Sequences

/-!
Fixed-dimensional frame laws: a uniform first norm moment gives tightness
and a weakly convergent subsequence. Eventual open-rectangle bounds pass to
every weak limit by Portmanteau and give actual Lebesgue domination.
Neither higher moments nor absolute continuity of the limit are assumed.
-/

namespace PrimeGapNormality.Prime.CoreFrameProbabilityLimit

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

noncomputable section

abbrev Frame (r : ℕ) := Fin r → ℝ

/-- The norm tail of a probability law is bounded by its first moment.
The extended integral formulation includes integrability in the bound. -/
theorem norm_tail_le {r : ℕ} (μ : ProbabilityMeasure (Frame r)) {M R : ℝ}
    (hR : 0 < R)
    (hmoment : (∫⁻ x, ENNReal.ofReal ‖x‖ ∂(μ : Measure (Frame r))) ≤ ENNReal.ofReal M) :
    (μ : Measure (Frame r)) (Metric.closedBall (0 : Frame r) R)ᶜ ≤
      ENNReal.ofReal (M / R) := by
  have hsub : (Metric.closedBall (0 : Frame r) R)ᶜ ⊆
      {x : Frame r | ENNReal.ofReal R ≤ ENNReal.ofReal ‖x‖} := by
    intro x hx
    have hnorm : R < ‖x‖ := by
      simpa only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    exact ENNReal.ofReal_le_ofReal hnorm.le
  have hmark := meas_ge_le_lintegral_div
    (μ := (μ : Measure (Frame r)))
    (f := fun x : Frame r ↦ ENNReal.ofReal ‖x‖)
    (ENNReal.continuous_ofReal.comp continuous_norm).measurable.aemeasurable
    (ENNReal.ofReal_pos.2 hR).ne' ENNReal.ofReal_ne_top
  calc
    (μ : Measure (Frame r)) (Metric.closedBall (0 : Frame r) R)ᶜ ≤
        (μ : Measure (Frame r)) {x | ENNReal.ofReal R ≤ ENNReal.ofReal ‖x‖} := measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal ‖x‖ ∂(μ : Measure (Frame r))) / ENNReal.ofReal R := hmark
    _ ≤ ENNReal.ofReal M / ENNReal.ofReal R := ENNReal.div_le_div_right hmoment _
    _ = ENNReal.ofReal (M / R) := (ENNReal.ofReal_div_of_pos hR).symm

theorem tight_of_norm_lintegral_bound {r : ℕ} (μ : ℕ → ProbabilityMeasure (Frame r))
    {M : ℝ} (hM : 0 ≤ M)
    (hmoment : ∀ j, (∫⁻ x, ENNReal.ofReal ‖x‖ ∂(μ j : Measure (Frame r))) ≤ ENNReal.ofReal M) :
    IsTightMeasureSet {ν : Measure (Frame r) | ∃ j, (μ j : Measure (Frame r)) = ν} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, _, hδ, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδpos : 0 < δ := ENNReal.ofReal_pos.1 hδ
  let R : ℝ := (M + 1) / δ
  have hR : 0 < R := div_pos (by linarith) hδpos
  refine ⟨Metric.closedBall (0 : Frame r) R, isCompact_closedBall _ _, ?_⟩
  rintro ν ⟨j, rfl⟩
  have hratio : M / R ≤ δ := by
    apply (div_le_iff₀ hR).2
    have heq : δ * R = M + 1 := by
      dsimp only [R]
      field_simp [hδpos.ne']
    linarith
  exact (norm_tail_le (μ j) hR (hmoment j)).trans
    ((ENNReal.ofReal_le_ofReal hratio).trans hδε.le)

/-- Ordinary first-integral formulation. Integrability is explicit so the
Bochner integral cannot vanish merely through the nonintegrable convention. -/
theorem tight_of_first_moment {r : ℕ} (μ : ℕ → ProbabilityMeasure (Frame r))
    {M : ℝ} (hM : 0 ≤ M)
    (hint : ∀ j, Integrable (fun x : Frame r ↦ ‖x‖) (μ j : Measure (Frame r)))
    (hmoment : ∀ j, (∫ x, ‖x‖ ∂(μ j : Measure (Frame r))) ≤ M) :
    IsTightMeasureSet {ν : Measure (Frame r) | ∃ j, (μ j : Measure (Frame r)) = ν} := by
  apply tight_of_norm_lintegral_bound μ hM
  intro j
  rw [← ofReal_integral_eq_lintegral_ofReal (hint j) (Eventually.of_forall fun x ↦ norm_nonneg x)]
  exact ENNReal.ofReal_le_ofReal (hmoment j)

/-- Prokhorov extraction in the fixed frame dimension, from only a first
norm moment. The subsequence is chosen before any test rectangle. -/
theorem exists_weak_subsequence {r : ℕ} (μ : ℕ → ProbabilityMeasure (Frame r))
    {M : ℝ} (hM : 0 ≤ M)
    (hmoment : ∀ j, (∫⁻ x, ENNReal.ofReal ‖x‖ ∂(μ j : Measure (Frame r))) ≤ ENNReal.ofReal M) :
    ∃ ν : ProbabilityMeasure (Frame r), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have htight := tight_of_norm_lintegral_bound μ hM hmoment
  have hcompact : IsCompact (closure (Set.range μ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    simpa only [Set.mem_range, exists_exists_eq_and] using htight
  obtain ⟨ν, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun j ↦ subset_closure (Set.mem_range_self j))
  exact ⟨ν, φ, hφ, hlim⟩

/-- Portmanteau inheritance of the literal open-rectangle estimate. The
eventual threshold may depend on the rectangle; no uniformity is silently
added, and the error sequence is only required to tend to zero. -/
theorem rectangle_bound_of_weak_limit {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Frame r)) (ν : ProbabilityMeasure (Frame r))
    (hweak : Tendsto μ atTop (𝓝 ν)) {K : ℝ} (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hrect : ∀ a b : Fin r → ℝ, (∀ i, a i < b i) → ∀ᶠ j : ℕ in atTop,
      (μ j : Measure (Frame r)) (Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)) + ENNReal.ofReal (ε j)) :
    ∀ a b : Fin r → ℝ, (∀ i, a i < b i) →
      (ν : Measure (Frame r)) (Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)) := by
  intro a b hab
  have hopen : IsOpen (Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpen_Ioo)
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hopen
  have herror := (ENNReal.continuous_ofReal.tendsto 0).comp hε
  have hlim : Tendsto (fun j ↦ ENNReal.ofReal (K * ∏ i, (b i - a i)) +
      ENNReal.ofReal (ε j)) atTop (𝓝 (ENNReal.ofReal (K * ∏ i, (b i - a i)))) := by
    simpa only [Function.comp_apply, ENNReal.ofReal_zero, add_zero] using
      tendsto_const_nhds.add herror
  exact hport.trans ((Filter.liminf_le_liminf (hrect a b hab)).trans_eq hlim.liminf_eq)

theorem weak_limit_le_volume {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Frame r)) (ν : ProbabilityMeasure (Frame r))
    (hweak : Tendsto μ atTop (𝓝 ν)) {K : ℝ} (hK : 0 < K) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hrect : ∀ a b : Fin r → ℝ, (∀ i, a i < b i) → ∀ᶠ j : ℕ in atTop,
      (μ j : Measure (Frame r)) (Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)) + ENNReal.ofReal (ε j)) :
    (ν : Measure (Frame r)) ≤ ENNReal.ofReal (K * (2 : ℝ) ^ r) • volume :=
  CoreRectangleMeasureDomination.le_volume_of_open_rectangle_bound
    (n := r) (ν : Measure (Frame r)) hK
    (rectangle_bound_of_weak_limit μ ν hweak ε hε hrect)

theorem weak_limit_absolutelyContinuous {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Frame r)) (ν : ProbabilityMeasure (Frame r))
    (hweak : Tendsto μ atTop (𝓝 ν)) {K : ℝ} (hK : 0 < K) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hrect : ∀ a b : Fin r → ℝ, (∀ i, a i < b i) → ∀ᶠ j : ℕ in atTop,
      (μ j : Measure (Frame r)) (Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)) + ENNReal.ofReal (ε j)) :
    (ν : Measure (Frame r)) ≪ volume :=
  Measure.absolutelyContinuous_of_le_smul (weak_limit_le_volume μ ν hweak hK ε hε hrect)

/-- An actual AC subsequential limit, with compactness supplied solely by
the first moment and AC supplied solely by the asymptotic rectangles. -/
theorem exists_absolutelyContinuous_subsequence {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Frame r)) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 < K)
    (hmoment : ∀ j, (∫⁻ x, ENNReal.ofReal ‖x‖ ∂(μ j : Measure (Frame r))) ≤ ENNReal.ofReal M)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hrect : ∀ a b : Fin r → ℝ, (∀ i, a i < b i) → ∀ᶠ j : ℕ in atTop,
      (μ j : Measure (Frame r)) (Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)) + ENNReal.ofReal (ε j)) :
    ∃ ν : ProbabilityMeasure (Frame r), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) ∧ (ν : Measure (Frame r)) ≪ volume := by
  obtain ⟨ν, φ, hφ, hweak⟩ := exists_weak_subsequence μ hM hmoment
  refine ⟨ν, φ, hφ, hweak, ?_⟩
  exact weak_limit_absolutelyContinuous (μ ∘ φ) ν hweak hK (ε ∘ φ)
    (hε.comp hφ.tendsto_atTop)
    (fun a b hab ↦ hφ.tendsto_atTop.eventually (hrect a b hab))

end

end PrimeGapNormality.Prime.CoreFrameProbabilityLimit
