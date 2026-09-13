import PrimeGapNormality.Prime.CoreFrameProbabilityLimit
import Mathlib.MeasureTheory.Group.AddCircle

/-!
# Fixed-dimensional joint frame extraction

The outer phase, exterior frame and scale may be arbitrarily correlated.
Only the frame's first norm moment and compact scale support are used for
tightness. The subsequence is chosen before every test and cutoff.
Rectangle absolute continuity is asserted only for the frame marginal.
First moments pass by nonnegative Portmanteau, not uniform integrability.
-/

namespace PrimeGapNormality.Prime.CoreJointFrameLimit

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)
abbrev Frame (r : ℕ) := Fin r → ℝ
abbrev Joint (r : ℕ) := Circle × (Frame r × ℝ)

def frame {r : ℕ} (z : Joint r) : Frame r := z.2.1
def scale {r : ℕ} (z : Joint r) : ℝ := z.2.2

theorem continuous_frame {r : ℕ} : Continuous (@frame r) :=
  continuous_fst.comp continuous_snd

theorem continuous_scale {r : ℕ} : Continuous (@scale r) :=
  continuous_snd.comp continuous_snd

def frameMarginal {r : ℕ} (μ : ProbabilityMeasure (Joint r)) : ProbabilityMeasure (Frame r) :=
  μ.map continuous_frame.measurable.aemeasurable

theorem frameMarginal_lintegral {r : ℕ} (μ : ProbabilityMeasure (Joint r))
    (f : Frame r → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂(frameMarginal μ : Measure (Frame r))) =
      ∫⁻ z, f (frame z) ∂(μ : Measure (Joint r)) := by
  change (∫⁻ x, f x ∂Measure.map frame (μ : Measure (Joint r))) = _
  exact lintegral_map hf continuous_frame.measurable

theorem frameMarginal_weak {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) (ν : ProbabilityMeasure (Joint r))
    (hweak : Tendsto μ atTop (𝓝 ν)) :
    Tendsto (fun j => frameMarginal (μ j)) atTop (𝓝 (frameMarginal ν)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hweak continuous_frame

/-- A tight frame marginal and a compactly supported scale control the
joint law, regardless of correlations with the compact outer circle. -/
theorem tight_of_first_norm_moment {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) {M C : ℝ} (hM : 0 ≤ M)
    (hmoment : ∀ j,
      (∫⁻ z, ENNReal.ofReal ‖frame z‖ ∂(μ j : Measure (Joint r))) ≤ ENNReal.ofReal M)
    (hscale : ∀ j, ∀ᵐ z ∂(μ j : Measure (Joint r)), scale z ∈ Icc 1 C) :
    IsTightMeasureSet {ν : Measure (Joint r) | ∃ j, (μ j : Measure (Joint r)) = ν} := by
  have hframe : IsTightMeasureSet {ν : Measure (Frame r) |
      ∃ j, (frameMarginal (μ j) : Measure (Frame r)) = ν} := by
    apply CoreFrameProbabilityLimit.tight_of_norm_lintegral_bound
      (fun j => frameMarginal (μ j)) hM
    intro j
    rw [frameMarginal_lintegral (μ j) (fun x : Frame r => ENNReal.ofReal ‖x‖)
      (ENNReal.continuous_ofReal.comp continuous_norm).measurable]
    exact hmoment j
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hframe ⊢
  intro ε hε
  obtain ⟨K, hK, hmass⟩ := hframe ε hε
  refine ⟨(univ : Set Circle) ×ˢ (K ×ˢ Icc 1 C),
    isCompact_univ.prod (hK.prod isCompact_Icc), ?_⟩
  rintro ν ⟨j, rfl⟩
  have hle : (μ j : Measure (Joint r)) ((univ : Set Circle) ×ˢ (K ×ˢ Icc 1 C))ᶜ ≤
      (μ j : Measure (Joint r)) (frame ⁻¹' Kᶜ) := by
    apply measure_mono_ae
    filter_upwards [hscale j] with z hz
    intro hnot
    change frame z ∉ K
    intro hmem
    exact hnot ⟨mem_univ _, hmem, hz⟩
  have hmap : (frameMarginal (μ j) : Measure (Frame r)) Kᶜ =
      (μ j : Measure (Joint r)) (frame ⁻¹' Kᶜ) :=
    ProbabilityMeasure.map_apply' (μ j) continuous_frame.measurable.aemeasurable
      hK.measurableSet.compl
  rw [← hmap] at hle
  exact hle.trans (hmass _ ⟨j, rfl⟩)

/-- One joint subsequence, chosen without reference to a test or cutoff. -/
theorem exists_joint_subsequence {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) {M C : ℝ} (hM : 0 ≤ M)
    (hmoment : ∀ j,
      (∫⁻ z, ENNReal.ofReal ‖frame z‖ ∂(μ j : Measure (Joint r))) ≤ ENNReal.ofReal M)
    (hscale : ∀ j, ∀ᵐ z ∂(μ j : Measure (Joint r)), scale z ∈ Icc 1 C) :
    ∃ ν : ProbabilityMeasure (Joint r), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have htight := tight_of_first_norm_moment μ hM hmoment hscale
  have hcompact : IsCompact (closure (Set.range μ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    simpa only [Set.mem_range, exists_exists_eq_and] using htight
  obtain ⟨ν, _, φ, hφ, hweak⟩ := hcompact.tendsto_subseq
    (fun j => subset_closure (Set.mem_range_self j))
  exact ⟨ν, φ, hφ, hweak⟩

/-- Closed support is retained by every weak joint limit. -/
theorem ae_closed_of_weak_limit {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) (ν : ProbabilityMeasure (Joint r))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Joint r)) (hs : IsClosed s)
    (hsupport : ∀ j, ∀ᵐ z ∂(μ j : Measure (Joint r)), z ∈ s) :
    ∀ᵐ z ∂(ν : Measure (Joint r)), z ∈ s := by
  have hz : ∀ j, (μ j : Measure (Joint r)) sᶜ = 0 :=
    fun j => mem_ae_iff.1 (hsupport j)
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hs.isOpen_compl
  have hzero : (ν : Measure (Joint r)) sᶜ = 0 := by
    apply le_zero_iff.1
    simpa only [hz, liminf_const] using hport
  exact mem_ae_iff.2 hzero

theorem scale_support_of_weak_limit {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) (ν : ProbabilityMeasure (Joint r))
    (hweak : Tendsto μ atTop (𝓝 ν)) {C : ℝ}
    (hscale : ∀ j, ∀ᵐ z ∂(μ j : Measure (Joint r)), scale z ∈ Icc 1 C) :
    ∀ᵐ z ∂(ν : Measure (Joint r)), scale z ∈ Icc 1 C :=
  ae_closed_of_weak_limit μ ν hweak (scale ⁻¹' Icc 1 C)
    (isClosed_Icc.preimage continuous_scale) hscale

theorem frame_nonneg_of_weak_limit {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) (ν : ProbabilityMeasure (Joint r))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hnonneg : ∀ j, ∀ᵐ z ∂(μ j : Measure (Joint r)), ∀ i, 0 ≤ frame z i) :
    ∀ᵐ z ∂(ν : Measure (Joint r)), ∀ i, 0 ≤ frame z i := by
  have hclosed : IsClosed {z : Joint r | ∀ i, 0 ≤ frame z i} := by
    have h : IsClosed (⋂ i : Fin r, {z : Joint r | 0 ≤ frame z i}) :=
      isClosed_iInter fun i => isClosed_le continuous_const
        ((continuous_apply i).comp continuous_frame)
    convert h using 1
    ext z
    simp only [mem_setOf_eq, mem_iInter]
  exact ae_closed_of_weak_limit μ ν hweak _ hclosed hnonneg

/-- The rectangle bound is inherited by the frame marginal, not imposed
on the possibly singular joint law. -/
theorem frameMarginal_ac_of_weak_limit {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) (ν : ProbabilityMeasure (Joint r))
    (hweak : Tendsto μ atTop (𝓝 ν)) {K : ℝ} (hK : 0 < K)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hrect : ∀ a b : Fin r → ℝ, (∀ i, a i < b i) → ∀ᶠ j in atTop,
      (frameMarginal (μ j) : Measure (Frame r)) (Set.pi univ (fun i => Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)) + ENNReal.ofReal (ε j)) :
    (frameMarginal ν : Measure (Frame r)) ≪ volume :=
  CoreFrameProbabilityLimit.weak_limit_absolutelyContinuous
    (fun j => frameMarginal (μ j)) (frameMarginal ν)
    (frameMarginal_weak μ ν hweak) hK ε hε hrect

/-- Nonnegative continuous moments are lower semicontinuous along the
joint sequence. A bounded first moment is sufficient; UI is not used. -/
theorem nonnegative_moment_of_weak_limit {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) (ν : ProbabilityMeasure (Joint r))
    (hweak : Tendsto μ atTop (𝓝 ν)) (f : Joint r → ℝ)
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) {H : ℝ}
    (hbound : ∀ j, (∫⁻ z, ENNReal.ofReal (f z) ∂(μ j : Measure (Joint r))) ≤
      ENNReal.ofReal H) :
    (∫⁻ z, ENNReal.ofReal (f z) ∂(ν : Measure (Joint r))) ≤ ENNReal.ofReal H := by
  have hport := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (ν : Measure (Joint r))) (μs := fun j => (μ j : Measure (Joint r))) hf hf0
    (fun _ hs => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hs)
  exact hport.trans ((Filter.liminf_le_liminf (Eventually.of_forall hbound)).trans_eq
    tendsto_const_nhds.liminf_eq)

/-- The central coordinate can retain its own sharper first-moment bound
instead of the coarser whole-frame norm bound. -/
theorem coordinate_moment_of_weak_limit {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) (ν : ProbabilityMeasure (Joint r))
    (hweak : Tendsto μ atTop (𝓝 ν)) (i : Fin r) {H : ℝ}
    (hbound : ∀ j, (∫⁻ z, ENNReal.ofReal (frame z i) ∂(μ j : Measure (Joint r))) ≤
      ENNReal.ofReal H) :
    (∫⁻ z, ENNReal.ofReal (frame z i) ∂(ν : Measure (Joint r))) ≤ ENNReal.ofReal H := by
  have h := nonnegative_moment_of_weak_limit μ ν hweak
    (fun z => max (frame z i) 0)
    (((continuous_apply i).comp continuous_frame).max continuous_const)
    (fun z => le_max_right _ _) (H := H)
    (fun j => by simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero]
      using hbound j)
  simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero] using h

/-- Convert the finite nonnegative central moment into an honest Bochner
integral and its bound, rather than relying on the nonintegrable-zero convention. -/
theorem coordinate_integrable_and_integral_le {r : ℕ}
    (ν : ProbabilityMeasure (Joint r)) (i : Fin r) {H : ℝ} (hH : 0 ≤ H)
    (hnonneg : ∀ᵐ z ∂(ν : Measure (Joint r)), 0 ≤ frame z i)
    (hmoment : (∫⁻ z, ENNReal.ofReal (frame z i) ∂(ν : Measure (Joint r))) ≤
      ENNReal.ofReal H) :
    Integrable (fun z => frame z i) (ν : Measure (Joint r)) ∧
      (∫ z, frame z i ∂(ν : Measure (Joint r))) ≤ H := by
  have hfin : (∫⁻ z, ENNReal.ofReal (frame z i) ∂(ν : Measure (Joint r))) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmoment
  have hint : Integrable (fun z => frame z i) (ν : Measure (Joint r)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      ((continuous_apply i).comp continuous_frame).measurable.aestronglyMeasurable hnonneg).1 hfin
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg] at hmoment
  exact (ENNReal.ofReal_le_ofReal_iff hH).1 hmoment

/-- The complete fixed-joint-limit supplier. This single extraction works
for every subsequent test and cutoff. The central coordinate is arbitrary
but fixed, so the paper can choose its merged gap `W`. -/
theorem exists_joint_limit {r : ℕ}
    (μ : ℕ → ProbabilityMeasure (Joint r)) {M C K H : ℝ}
    (hM : 0 ≤ M) (hK : 0 < K) (hH : 0 ≤ H)
    (hmoment : ∀ j,
      (∫⁻ z, ENNReal.ofReal ‖frame z‖ ∂(μ j : Measure (Joint r))) ≤ ENNReal.ofReal M)
    (hnonneg : ∀ j, ∀ᵐ z ∂(μ j : Measure (Joint r)), ∀ i, 0 ≤ frame z i)
    (hscale : ∀ j, ∀ᵐ z ∂(μ j : Measure (Joint r)), scale z ∈ Icc 1 C)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hrect : ∀ a b : Fin r → ℝ, (∀ i, a i < b i) → ∀ᶠ j in atTop,
      (frameMarginal (μ j) : Measure (Frame r)) (Set.pi univ (fun i => Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)) + ENNReal.ofReal (ε j))
    (i : Fin r)
    (hcentral : ∀ j,
      (∫⁻ z, ENNReal.ofReal (frame z i) ∂(μ j : Measure (Joint r))) ≤ ENNReal.ofReal H) :
    ∃ ν : ProbabilityMeasure (Joint r), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) ∧
      (frameMarginal ν : Measure (Frame r)) ≪ volume ∧
      (∀ᵐ z ∂(ν : Measure (Joint r)), ∀ a, 0 ≤ frame z a) ∧
      (∀ᵐ z ∂(ν : Measure (Joint r)), scale z ∈ Icc 1 C) ∧
      Integrable (fun z => frame z i) (ν : Measure (Joint r)) ∧
      (∫ z, frame z i ∂(ν : Measure (Joint r))) ≤ H := by
  obtain ⟨ν, φ, hφ, hweak⟩ := exists_joint_subsequence μ hM hmoment hscale
  have hνnonneg := frame_nonneg_of_weak_limit (μ ∘ φ) ν hweak
    (fun j => hnonneg (φ j))
  have hνscale := scale_support_of_weak_limit (μ ∘ φ) ν hweak
    (fun j => hscale (φ j))
  have hνac := frameMarginal_ac_of_weak_limit (μ ∘ φ) ν hweak hK (ε ∘ φ)
    (hε.comp hφ.tendsto_atTop)
    (fun a b hab => hφ.tendsto_atTop.eventually (hrect a b hab))
  have hνmoment := coordinate_moment_of_weak_limit (μ ∘ φ) ν hweak i
    (fun j => hcentral (φ j))
  have hνintegral := coordinate_integrable_and_integral_le ν i hH
    (hνnonneg.mono fun z hz => hz i) hνmoment
  exact ⟨ν, φ, hφ, hweak, hνac, hνnonneg, hνscale, hνintegral⟩

end

end PrimeGapNormality.Prime.CoreJointFrameLimit
