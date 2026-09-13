import PrimeGapNormality.Prime.CoreCalibratedModelReferenceSharp
import PrimeGapNormality.Prime.CoreGeneralSequenceST
import PrimeGapNormality.Prime.CoreGeneralRealCutoff
import PrimeGapNormality.Prime.CoreResidueDominationSharp

/-!
# The literal 24*k*c reference domination under general S/T

The actual model reference is chosen after the proposed physical
subsequence and before every test, error tolerance and residue weak limit.
The physical comparison contributes c; the exact limiting residue-count
ratio contributes k. No Haar substitution or coarse 2k restriction is used.
The same reference has mass at most two.
-/

namespace PrimeGapNormality.Prime.CoreGeneralReferenceSharp

open Filter Finset MeasureTheory CoreCyclic
open CoreGeneralSequenceST CoreGeneralModelReference CoreSequenceSTConsumer
  CoreSequenceSTMeanTail CoreSequenceSubexponentialGrowth
  CoreCalibratedMixtureFiniteSupport CoreCalibratedMixtureProfile
open scoped Classical Topology NNReal ENNReal BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

abbrev Circle := AddCircle (1 : ℝ)

section Positive
variable {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (P : PeriodicLocal k) (w : ℕ)
    (hroot : drop hk P = 0) (hP : P ≠ 0)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    {κ c : ℝ} (hκ : (topDegree P : ℝ) / Real.log (B : ℝ) ≤ κ) (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G)

include ha hB hk r P w hroot hP hw hκ hc hG hω hsum hcal hS hT

/-- Exact full-window coefficient 24c, with the reference fixed before all tests. -/
theorem exists_fullWindow_reference (χ : ℕ → ℕ) (hχ : StrictMono χ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ σ : Measure Circle,
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 2 ∧
      ∀ (f : Circle →ᵇ ℝ) (Kf : ℝ≥0), LipschitzWith Kf f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          coreDigitalWindowAverage (sequenceLocalOrbit B hk r P a) f
            (seqCount a (χ (ψ n))) (CoreSequenceResiduePassage.seqCountDifference a (χ (ψ n))) ≤
              (24 * c) * (∫ x, f x ∂σ) + ε := by
  have hd := one_le_topDegree_of_rooted hk P hroot hP
  have hdeg : ∀ s, (P s).totalDegree ≤ topDegree P := fun s =>
    Finset.le_sup (f := fun t => (P t).totalDegree) (Finset.mem_univ s)
  have hGχ : Tendsto (fun X => G (χ X)) atTop atTop := by
    simpa only [Function.comp_def] using hG.comp hχ.tendsto_atTop
  have hcal' : UniformCalibration (fun X y => ω (χ X) y) (fun X => G (χ X)) := by
    intro ε hε
    exact hχ.tendsto_atTop.eventually (hcal ε hε)
  obtain ⟨ψ, hψ, σ, hσfin, hσac, hmass, hmodel⟩ :=
    CoreCalibratedModelReferenceSharp.exists_reference_subsequence hB hk r w P hroot hP hw hκ
      hGχ (fun X y => hω (χ X) y) (fun X => hsum (χ X)) hcal'
  refine ⟨ψ, hψ, σ, hσfin, hσac, hmass, ?_⟩
  intro f Kf hKf hf ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hδ : 0 < ε / (2 * c) := by positivity
  have hχψ : Tendsto (fun n => χ (ψ n)) atTop atTop := by
    simpa only [Function.comp_def] using hχ.tendsto_atTop.comp hψ.tendsto_atTop
  filter_upwards [hmodel f Kf hKf hf (ε / (2 * c)) hδ,
    hχψ.eventually
      (positive_comparison ha hB hk r P w (topDegree P) hd hw hdeg hκ hc hG
        hω hsum hcal hS hT f hKf hf hε2)] with n hm hp
  change CoreCalibratedModelSubsequence.modelMean B hk r P w G (rank κ G) ω (χ (ψ n)) f ≤
    (24 : ℝ) * (∫ x, f x ∂σ) + ε / (2 * c) at hm
  rw [windowAvgReal_eq_coreDigitalWindowAverage ha] at hp
  have hscaled := mul_le_mul_of_nonneg_left hm hc.le
  have heps : c * (ε / (2 * c)) = ε / 2 := by field_simp [hc.ne'] <;> ring
  calc
    _ ≤ c * CoreCalibratedModelSubsequence.modelMean B hk r P w G (rank κ G) ω (χ (ψ n)) f + ε / 2 := hp
    _ ≤ c * ((24 : ℝ) * (∫ x, f x ∂σ) + ε / (2 * c)) + ε / 2 :=
      _root_.add_le_add hscaled le_rfl
    _ = _ := by rw [mul_add, heps]; ring

/-- One original reference controls every tested residue weak limit on the
chosen further subsequence. Window-count growth is derived from S and T. -/
theorem exists_reference_for_residue_limits (χ : ℕ → ℕ) (hχ : StrictMono χ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ σ : Measure Circle,
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 2 ∧
      ∀ (j : ℕ) (μ : ProbabilityMeasure Circle),
        Tendsto (fun n => CoreResidueDigitalReference.residueMeasure hk j
          (sequenceLocalOrbit B hk r P a) (seqCount a (χ (ψ n)))
          (CoreSequenceResiduePassage.seqCountDifference a (χ (ψ n)))) atTop (𝓝 μ) →
        (μ : Measure Circle) ≤ ENNReal.ofReal (24 * (k : ℝ) * c) • σ := by
  obtain ⟨ψ, hψ, σ, hfin, hac, hmass, hfull⟩ :=
    exists_fullWindow_reference ha hB hk r P w hroot hP hw hκ hc hG hω hsum hcal hS hT χ hχ
  have hd := one_le_topDegree_of_rooted hk P hroot hP
  have hκp : 0 < κ :=
    (div_pos (Nat.cast_pos.mpr (show 0 < topDegree P by omega))
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
    (sequenceLocalOrbit B hk r P a)
    (fun n => seqCount a (χ (ψ n)))
    (fun n => CoreSequenceResiduePassage.seqCountDifference a (χ (ψ n)))
    (hN.comp hindices) μ hweak σ (A := 24 * c)
    (mul_nonneg (by norm_num) hc.le) hfull
  simpa only [show (k : ℝ) * (24 * c) = 24 * (k : ℝ) * c by ring] using hle

/-- The paper's visible domination bound for any actual tested residue
weak limit. The only limit premise identifies that empirical weak limit;
all model/reference/count suppliers are discharged from the original S/T. -/
theorem residue_limit_le_reference
    (j : ℕ) (χ : ℕ → ℕ) (hχ : StrictMono χ) (μ : ProbabilityMeasure Circle)
    (hweak : Tendsto (fun n => CoreResidueDigitalReference.residueMeasure hk j
      (sequenceLocalOrbit B hk r P a) (seqCount a (χ n))
      (CoreSequenceResiduePassage.seqCountDifference a (χ n))) atTop (𝓝 μ)) :
    ∃ σ : Measure Circle, IsFiniteMeasure σ ∧ σ ≪ volume ∧
      σ Set.univ ≤ ENNReal.ofReal 2 ∧
      (μ : Measure Circle) ≤ ENNReal.ofReal (24 * (k : ℝ) * c) • σ := by
  obtain ⟨ψ, hψ, σ, hfin, hac, hmass, hdom⟩ :=
    exists_reference_for_residue_limits ha hB hk r P w hroot hP hw hκ hc
      hG hω hsum hcal hS hT χ hχ
  refine ⟨σ, hfin, hac, hmass, hdom j μ ?_⟩
  simpa only [Function.comp_def] using hweak.comp hψ.tendsto_atTop

end Positive

/-- Literal complex S has c=1, so its actual residue weak limits are
dominated by 24k times the same mass-two polynomial reference. -/
theorem residue_limit_le_of_complexPatternS
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (P : PeriodicLocal k) (w : ℕ)
    (hroot : drop hk P = 0) (hP : P ≠ 0)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    {κ : ℝ} (hκ : (topDegree P : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G)
    (j : ℕ) (χ : ℕ → ℕ) (hχ : StrictMono χ) (μ : ProbabilityMeasure Circle)
    (hweak : Tendsto (fun n => CoreResidueDigitalReference.residueMeasure hk j
      (sequenceLocalOrbit B hk r P a) (seqCount a (χ n))
      (CoreSequenceResiduePassage.seqCountDifference a (χ n))) atTop (𝓝 μ)) :
    ∃ σ : Measure Circle, IsFiniteMeasure σ ∧ σ ≪ volume ∧
      σ Set.univ ≤ ENNReal.ofReal 2 ∧
      (μ : Measure Circle) ≤ ENNReal.ofReal (24 * (k : ℝ)) • σ := by
  have hd := one_le_topDegree_of_rooted hk P hroot hP
  have hκp : 0 < κ :=
    (div_pos (Nat.cast_pos.mpr (show 0 < topDegree P by omega))
      (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hs := shapeS_of_patternS hκp hG hω hsum hcal
    (patternS_of_complex hS) (meanGapTail_eventually_nonempty hT)
  simpa only [mul_one] using residue_limit_le_reference
    ha hB hk r P w hroot hP hw hκ (by norm_num : (0 : ℝ) < 1)
    hG hω hsum hcal hs hT j χ hχ μ hweak

/-- Arbitrary real-cutoff probability measures, including nonatomic laws,
inherit the same exact constant by the proved floor-pushforward identity. -/
theorem residue_limit_le_of_realCutoff
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (P : PeriodicLocal k) (w : ℕ)
    (hroot : drop hk P = 0) (hP : P ≠ 0)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    {κ : ℝ} (hκ : (topDegree P : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (cutoffs : ℕ → ProbabilityMeasure ℝ) (hcal : CoreGeneralRealCutoff.Calibration cutoffs G)
    (hS : CoreGeneralRealCutoff.PatternS a κ G cutoffs)
    (hT : MeanGapTailT a (localTailBase κ) G)
    (j : ℕ) (χ : ℕ → ℕ) (hχ : StrictMono χ) (μ : ProbabilityMeasure Circle)
    (hweak : Tendsto (fun n => CoreResidueDigitalReference.residueMeasure hk j
      (sequenceLocalOrbit B hk r P a) (seqCount a (χ n))
      (CoreSequenceResiduePassage.seqCountDifference a (χ n))) atTop (𝓝 μ)) :
    ∃ σ : Measure Circle, IsFiniteMeasure σ ∧ σ ≪ volume ∧
      σ Set.univ ≤ ENNReal.ofReal 2 ∧
      (μ : Measure Circle) ≤ ENNReal.ofReal (24 * (k : ℝ)) • σ :=
  residue_limit_le_of_complexPatternS ha hB hk r P w hroot hP hw hκ hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (cutoffs X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (cutoffs X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae cutoffs G hcal)
    (CoreGeneralRealCutoff.patternS_nat hG hcal hS) hT j χ hχ μ hweak

end
end PrimeGapNormality.Prime.CoreGeneralReferenceSharp
