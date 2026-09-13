import PrimeGapNormality.Prime.CoreGeneralScaledGapModelReferenceSharp
import PrimeGapNormality.Prime.CoreGeneralScaledGapPositiveST
import PrimeGapNormality.Prime.CoreGeneralRoundedPositive
import PrimeGapNormality.Prime.CoreResidueDominationSharp

/-!
# Literal 24*k*c domination for rounded/scaled actual residue limits

A genuine restricted-fibre reference is fixed before tests, tolerances and
residue weak limits. The actual positive S comparison contributes c, and
the exact full-length/residue-count ratio contributes k. The reference is
not replaced by Haar or rescaled to hide a larger coefficient. Its mass
at most two is proved on the same extracted joint limit.
-/
namespace PrimeGapNormality.Prime.CoreGeneralRoundedReferenceSharp
open Filter Finset MeasureTheory CoreCyclic CoreIntegerGapObservable
open CoreGeneralSequenceST CoreGeneralModelReference CoreSequenceSTConsumer
  CoreSequenceSTMeanTail CoreSequenceSubexponentialGrowth CoreGeneralScaledGapST
  CoreCalibratedMixtureFiniteSupport CoreCalibratedMixtureProfile
open scoped Classical Topology NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
abbrev Circle := AddCircle (1 : ℝ)

section Positive
variable {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1)
    (b : Fin k → ℤ) (hb : b ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent b)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G)

include ha hB hk r F hC hF he he1 b hb hscale hκ hc hG hω hsum hcal hS hT

theorem exists_fullWindow_reference (χ : ℕ → ℕ) (hχ : StrictMono χ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ σ : Measure Circle,
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 2 ∧
      ∀ (f : Circle →ᵇ ℝ) (Kf : ℝ≥0), LipschitzWith Kf f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          coreDigitalWindowAverage (orbit B hk r F a) f
            (seqCount a (χ (ψ n))) (CoreSequenceResiduePassage.seqCountDifference a (χ (ψ n))) ≤
              (24 * c) * (∫ x, f x ∂σ) + ε := by
  have hGχ : Tendsto (fun X => G (χ X)) atTop atTop := by
    simpa only [Function.comp_def] using hG.comp hχ.tendsto_atTop
  have hcal' : UniformCalibration (fun X y => ω (χ X) y) (fun X => G (χ X)) :=
    fun ε hε => hχ.tendsto_atTop.eventually (hcal ε hε)
  obtain ⟨ψ, hψ, σ, hfin, hac, hmass, hmodel⟩ :=
    CoreGeneralScaledGapModelReferenceSharp.exists_reference_subsequence hB hk r F
      he he1 b hb hscale hκ hGχ (fun X y => hω (χ X) y) (fun X => hsum (χ X)) hcal'
  refine ⟨ψ, hψ, σ, hfin, hac, hmass, ?_⟩
  intro f Kf hKf hf ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hδ : 0 < ε / (2 * c) := by positivity
  have hχψ : Tendsto (fun n => χ (ψ n)) atTop atTop := by
    simpa only [Function.comp_def] using hχ.tendsto_atTop.comp hψ.tendsto_atTop
  filter_upwards [hmodel f Kf hKf hf (ε / (2 * c)) hδ,
    hχψ.eventually (CoreGeneralScaledGapPositiveST.positive_comparison
      ha hB hk r F hC hF hκ hc hG hω hsum hcal hS hT f hKf hf hε2)] with n hm hp
  change CoreGeneralScaledGapModelReference.modelMean B hk r F κ G ω (χ (ψ n)) f ≤
    (24 : ℝ) * (∫ x, f x ∂σ) + ε / (2 * c) at hm
  have hscaled := mul_le_mul_of_nonneg_left hm hc.le
  have heps : c * (ε / (2 * c)) = ε / 2 := by field_simp [hc.ne'] <;> ring
  calc
    _ ≤ c * CoreGeneralScaledGapModelReference.modelMean B hk r F κ G ω (χ (ψ n)) f + ε / 2 := hp
    _ ≤ c * ((24 : ℝ) * (∫ x, f x ∂σ) + ε / (2 * c)) + ε / 2 :=
      _root_.add_le_add hscaled le_rfl
    _ = _ := by rw [mul_add, heps]; ring

/-- The same sigma is chosen before every test and before all actual residue
weak limits on the chosen subsequence. Counts are derived from positive S/T. -/
theorem exists_reference_for_residue_limits (χ : ℕ → ℕ) (hχ : StrictMono χ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ σ : Measure Circle,
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 2 ∧
      ∀ (j : ℕ) (μ : ProbabilityMeasure Circle),
        Tendsto (fun n => CoreResidueDigitalReference.residueMeasure hk j
          (orbit B hk r F a) (seqCount a (χ (ψ n)))
          (CoreSequenceResiduePassage.seqCountDifference a (χ (ψ n)))) atTop (𝓝 μ) →
        (μ : Measure Circle) ≤ ENNReal.ofReal (24 * (k : ℝ) * c) • σ := by
  obtain ⟨ψ, hψ, σ, hfin, hac, hmass, hfull⟩ :=
    exists_fullWindow_reference ha hB hk r F hC hF he he1 b hb hscale hκ hc
      hG hω hsum hcal hS hT χ hχ
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hcount := CoreGeneralSequenceST.windowCountToInfinity
    ha hκp hc hG hω hsum hcal hS (meanGapTail_eventually_nonempty hT)
  have hN := CoreSequenceResiduePassage.tendsto_seqCountDifference_atTop ha hcount
  have hindices : Tendsto (fun n => χ (ψ n)) atTop atTop := by
    simpa only [Function.comp_def] using hχ.tendsto_atTop.comp hψ.tendsto_atTop
  refine ⟨ψ, hψ, σ, hfin, hac, hmass, ?_⟩
  intro j μ hweak
  letI : IsFiniteMeasure σ := hfin
  have hle := CoreResidueDominationSharp.weak_limit_le_reference hk j
    (orbit B hk r F a) (fun n => seqCount a (χ (ψ n)))
    (fun n => CoreSequenceResiduePassage.seqCountDifference a (χ (ψ n)))
    (hN.comp hindices) μ hweak σ (A := 24 * c)
    (mul_nonneg (by norm_num) hc.le) hfull
  simpa only [show (k : ℝ) * (24 * c) = 24 * (k : ℝ) * c by ring] using hle

/-- The limit premise only identifies an actual empirical weak limit. -/
theorem residue_limit_le_reference
    (j : ℕ) (χ : ℕ → ℕ) (hχ : StrictMono χ) (μ : ProbabilityMeasure Circle)
    (hweak : Tendsto (fun n => CoreResidueDigitalReference.residueMeasure hk j
      (orbit B hk r F a) (seqCount a (χ n))
      (CoreSequenceResiduePassage.seqCountDifference a (χ n))) atTop (𝓝 μ)) :
    ∃ σ : Measure Circle, IsFiniteMeasure σ ∧ σ ≪ volume ∧
      σ Set.univ ≤ ENNReal.ofReal 2 ∧
      (μ : Measure Circle) ≤ ENNReal.ofReal (24 * (k : ℝ) * c) • σ := by
  obtain ⟨ψ, hψ, σ, hfin, hac, hmass, hdom⟩ :=
    exists_reference_for_residue_limits ha hB hk r F hC hF he he1 b hb hscale hκ hc
      hG hω hsum hcal hS hT χ hχ
  refine ⟨σ, hfin, hac, hmass, hdom j μ ?_⟩
  simpa only [Function.comp_def] using hweak.comp hψ.tendsto_atTop

end Positive

theorem residue_limit_le_of_complexPatternS
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1)
    (b : Fin k → ℤ) (hb : b ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent b)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G)
    (j : ℕ) (χ : ℕ → ℕ) (hχ : StrictMono χ) (μ : ProbabilityMeasure Circle)
    (hweak : Tendsto (fun n => CoreResidueDigitalReference.residueMeasure hk j
      (orbit B hk r F a) (seqCount a (χ n))
      (CoreSequenceResiduePassage.seqCountDifference a (χ n))) atTop (𝓝 μ)) :
    ∃ σ : Measure Circle, IsFiniteMeasure σ ∧ σ ≪ volume ∧
      σ Set.univ ≤ ENNReal.ofReal 2 ∧
      (μ : Measure Circle) ≤ ENNReal.ofReal (24 * (k : ℝ)) • σ := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hs := shapeS_of_patternS hκp hG hω hsum hcal
    (patternS_of_complex hS) (meanGapTail_eventually_nonempty hT)
  simpa only [mul_one] using residue_limit_le_reference ha hB hk r F hC hF
    he he1 b hb hscale hκ (by norm_num : (0 : ℝ) < 1) hG hω hsum hcal hs hT j χ hχ μ hweak

theorem residue_limit_le_of_realPositive
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1)
    (b : Fin k → ℤ) (hb : b ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent b)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (cutoffs : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration cutoffs G)
    (hS : CoreGeneralRoundedPositive.RealShapeS a κ G cutoffs c)
    (hT : MeanGapTailT a (localTailBase κ) G)
    (j : ℕ) (χ : ℕ → ℕ) (hχ : StrictMono χ) (μ : ProbabilityMeasure Circle)
    (hweak : Tendsto (fun n => CoreResidueDigitalReference.residueMeasure hk j
      (orbit B hk r F a) (seqCount a (χ n))
      (CoreSequenceResiduePassage.seqCountDifference a (χ n))) atTop (𝓝 μ)) :
    ∃ σ : Measure Circle, IsFiniteMeasure σ ∧ σ ≪ volume ∧
      σ Set.univ ≤ ENNReal.ofReal 2 ∧
      (μ : Measure Circle) ≤ ENNReal.ofReal (24 * (k : ℝ) * c) • σ :=
  residue_limit_le_reference ha hB hk r F hC hF he he1 b hb hscale hκ hc hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (cutoffs X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (cutoffs X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae cutoffs G hcal)
    (CoreGeneralRoundedPositive.shapeS_of_real hG hcal hS) hT j χ hχ μ hweak

/-- Literal floor/ceiling combinations: both deterministic conditions are
discharged, leaving only original positive S/T and algebraic leading data. -/
theorem rounded_residue_limit_le_reference
    {I : Type*} [Fintype I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : CoreRoundedPowerScaling.RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {exponent κ : ℝ} (he : 0 < exponent) (he1 : exponent ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = exponent ∨ alpha i < exponent))
    (hb : CoreRoundedPowerScaling.leadingColumn alpha b exponent ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G)
    (j : ℕ) (χ : ℕ → ℕ) (hχ : StrictMono χ) (μ : ProbabilityMeasure Circle)
    (hweak : Tendsto (fun n => CoreResidueDigitalReference.residueMeasure hk j
      (orbit B hk r (CoreRoundedPowerScaling.roundedCombination kind alpha b) a) (seqCount a (χ n))
      (CoreSequenceResiduePassage.seqCountDifference a (χ n))) atTop (𝓝 μ)) :
    ∃ σ : Measure Circle, IsFiniteMeasure σ ∧ σ ≪ volume ∧
      σ Set.univ ≤ ENNReal.ofReal 2 ∧
      (μ : Measure Circle) ≤ ENNReal.ofReal (24 * (k : ℝ) * c) • σ := by
  have hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1 := fun i =>
    ⟨(halpha i).1, (halpha i).2.elim (fun h => h ▸ he1) (fun h => h.le.trans he1)⟩
  exact residue_limit_le_reference ha hB hk r _
    (CoreRoundedPrimeNormality.roundedLinearConstant_nonneg b)
    (CoreRoundedPrimeNormality.roundedCombination_linear_bound kind alpha b hα)
    he he1 (CoreRoundedModelSubsequence.integerLeadingColumn alpha b exponent)
    (CoreRoundedModelSubsequence.integerLeadingColumn_ne_zero alpha b exponent hb)
    (CoreGeneralRoundedST.rounded_compactScaling kind alpha b he he1 halpha)
    hκ hc hG hω hsum hcal hS hT j χ hχ μ hweak

end
end PrimeGapNormality.Prime.CoreGeneralRoundedReferenceSharp
