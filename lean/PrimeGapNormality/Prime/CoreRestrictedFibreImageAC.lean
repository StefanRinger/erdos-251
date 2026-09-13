import PrimeGapNormality.Prime.CorePolynomialReferenceMeasure

/-!
# Absolutely continuous images of restricted variable-length fibres

Unlike CoreFibreImageAC's full-line fibre theorem, the hypothesis here
concerns only the actual open insertion interval (0,W(a)). Zero-span
fibres are empty and need no nondegeneracy. The joint parameter law can
retain arbitrary dependence. Its first length moment, not an assumed
finite image measure, proves the source and reference are finite.
-/

namespace PrimeGapNormality.Prime.CoreRestrictedFibreImageAC

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

variable {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]

abbrev insertionDomain (W : α → ℝ) : Set (α × ℝ) :=
  CorePolynomialReference.insertionDomain W

def sourceMeasure (Λ : Measure α) (W : α → ℝ) : Measure (α × ℝ) :=
  (Λ.prod volume).restrict (insertionDomain W)

def referenceMeasure (Λ : Measure α) (W : α → ℝ) (H : α × ℝ → γ) : Measure γ :=
  Measure.map H (sourceMeasure Λ W)

theorem measurableSet_insertionDomain {W : α → ℝ} (hW : Measurable W) :
    MeasurableSet (insertionDomain W) :=
  CorePolynomialReference.measurableSet_insertionDomain hW

/-- The genuine restricted-fibre Fubini argument. No assertion about the
image of unrestricted real volume appears in the hypotheses. The target
measure may be real volume, circle volume, or any other measure. -/
theorem referenceMeasure_absolutelyContinuous (Λ : Measure α) (τ : Measure γ)
    {W : α → ℝ} (hW : Measurable W) (H : α × ℝ → γ) (hH : Measurable H)
    (hfibre : ∀ᵐ a ∂Λ,
      Measure.map (fun t : ℝ => H (a, t)) (volume.restrict (Ioo 0 (W a))) ≪ τ) :
    referenceMeasure Λ W H ≪ τ := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [referenceMeasure, Measure.map_apply hH hs, sourceMeasure,
    Measure.restrict_apply (hs.preimage hH)]
  apply Measure.measure_prod_null_of_ae_null
    ((hs.preimage hH).inter (measurableSet_insertionDomain hW))
  filter_upwards [hfibre] with a ha
  have hzero := ha hs0
  have hHa : Measurable (fun t : ℝ => H (a, t)) :=
    hH.comp (measurable_prodMk_left (x := a))
  rw [Measure.map_apply hHa hs, Measure.restrict_apply (hs.preimage hHa)] at hzero
  exact hzero

/-- It is enough to prove fibre AC for strictly positive spans. Nonpositive
spans have the zero source measure and cause no exceptional atom. -/
theorem referenceMeasure_absolutelyContinuous_of_pos_fibres
    (Λ : Measure α) (τ : Measure γ) {W : α → ℝ} (hW : Measurable W)
    (H : α × ℝ → γ) (hH : Measurable H)
    (hfibre : ∀ᵐ a ∂Λ, 0 < W a →
      Measure.map (fun t : ℝ => H (a, t)) (volume.restrict (Ioo 0 (W a))) ≪ τ) :
    referenceMeasure Λ W H ≪ τ := by
  apply referenceMeasure_absolutelyContinuous Λ τ hW H hH
  filter_upwards [hfibre] with a ha
  by_cases hp : 0 < W a
  · exact ha hp
  · rw [Ioo_eq_empty_of_le (le_of_not_gt hp), Measure.restrict_empty, Measure.map_zero]
    intro s hs
    rfl

/-- Tonelli gives the exact mass of the source. This remains valid for
negative W, where ofReal and the corresponding open fibre are both zero. -/
theorem sourceMeasure_mass (Λ : Measure α) {W : α → ℝ} (hW : Measurable W) :
    sourceMeasure Λ W univ = ∫⁻ a, ENNReal.ofReal (W a) ∂Λ := by
  rw [sourceMeasure, Measure.restrict_apply_univ]
  exact CorePolynomialReference.insertionDomain_mass Λ hW

theorem referenceMeasure_mass (Λ : Measure α) {W : α → ℝ} (hW : Measurable W)
    (H : α × ℝ → γ) (hH : Measurable H) :
    referenceMeasure Λ W H univ = ∫⁻ a, ENNReal.ofReal (W a) ∂Λ := by
  rw [referenceMeasure, Measure.map_apply hH MeasurableSet.univ,
    preimage_univ, sourceMeasure_mass Λ hW]

theorem sourceMeasure_mass_eq_integral (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a) (hWi : Integrable W Λ) :
    sourceMeasure Λ W univ = ENNReal.ofReal (∫ a, W a ∂Λ) := by
  rw [sourceMeasure_mass Λ hW, ← ofReal_integral_eq_lintegral_ofReal hWi hW0]

theorem referenceMeasure_mass_eq_integral (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a) (hWi : Integrable W Λ)
    (H : α × ℝ → γ) (hH : Measurable H) :
    referenceMeasure Λ W H univ = ENNReal.ofReal (∫ a, W a ∂Λ) := by
  rw [referenceMeasure_mass Λ hW H hH, ← ofReal_integral_eq_lintegral_ofReal hWi hW0]

theorem sourceMeasure_isFinite (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a) (hWi : Integrable W Λ) :
    IsFiniteMeasure (sourceMeasure Λ W) :=
  ⟨by rw [sourceMeasure_mass_eq_integral Λ hW hW0 hWi]; exact ENNReal.ofReal_lt_top⟩

theorem referenceMeasure_isFinite (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a) (hWi : Integrable W Λ)
    (H : α × ℝ → γ) (hH : Measurable H) :
    IsFiniteMeasure (referenceMeasure Λ W H) :=
  ⟨by rw [referenceMeasure_mass_eq_integral Λ hW hW0 hWi H hH]; exact ENNReal.ofReal_lt_top⟩

theorem referenceMeasure_mass_le (Λ : Measure α) {W : α → ℝ}
    (hW : Measurable W) (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a) (hWi : Integrable W Λ)
    (H : α × ℝ → γ) (hH : Measurable H) {M : ℝ} (hM : ∫ a, W a ∂Λ ≤ M) :
    referenceMeasure Λ W H univ ≤ ENNReal.ofReal M := by
  rw [referenceMeasure_mass_eq_integral Λ hW hW0 hWi H hH]
  exact ENNReal.ofReal_le_ofReal hM

/-- Tonelli for every nonnegative measurable target test, on the actual
restricted fibres. Finiteness of the first moment is not needed here. -/
theorem lintegral_referenceMeasure (Λ : Measure α) [SFinite Λ] {W : α → ℝ}
    (hW : Measurable W) (H : α × ℝ → γ) (hH : Measurable H)
    (f : γ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂referenceMeasure Λ W H) =
      ∫⁻ a, ∫⁻ t in Ioo 0 (W a), f (H (a, t)) ∂volume ∂Λ := by
  have hD := measurableSet_insertionDomain hW
  have hmeas : Measurable ((insertionDomain W).indicator (fun z => f (H z))) :=
    (hf.comp hH).indicator hD
  rw [referenceMeasure, lintegral_map hf hH, sourceMeasure,
    ← lintegral_indicator hD, lintegral_prod _ hmeas.aemeasurable]
  apply lintegral_congr
  intro a
  change (∫⁻ t, (Ioo 0 (W a)).indicator (fun t => f (H (a, t))) t ∂volume) = _
  exact lintegral_indicator measurableSet_Ioo _

/-- Combined finite-reference conclusion for a finite/probability parameter
law, and in fact any parameter measure for which the stated first moment
is integrable. The local AC premise is ONLY on positive physical fibres. -/
theorem finite_reference_of_pos_fibres (Λ : Measure α) (τ : Measure γ)
    {W : α → ℝ} (hW : Measurable W) (hW0 : ∀ᵐ a ∂Λ, 0 ≤ W a) (hWi : Integrable W Λ)
    (H : α × ℝ → γ) (hH : Measurable H)
    (hfibre : ∀ᵐ a ∂Λ, 0 < W a →
      Measure.map (fun t : ℝ => H (a, t)) (volume.restrict (Ioo 0 (W a))) ≪ τ) :
    IsFiniteMeasure (sourceMeasure Λ W) ∧ IsFiniteMeasure (referenceMeasure Λ W H) ∧
      referenceMeasure Λ W H ≪ τ ∧
      referenceMeasure Λ W H univ = ENNReal.ofReal (∫ a, W a ∂Λ) :=
  ⟨sourceMeasure_isFinite Λ hW hW0 hWi, referenceMeasure_isFinite Λ hW hW0 hWi H hH,
    referenceMeasure_absolutelyContinuous_of_pos_fibres Λ τ hW H hH hfibre,
    referenceMeasure_mass_eq_integral Λ hW hW0 hWi H hH⟩

end
end PrimeGapNormality.Prime.CoreRestrictedFibreImageAC
