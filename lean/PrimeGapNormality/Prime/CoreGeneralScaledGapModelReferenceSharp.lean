import PrimeGapNormality.Prime.CoreGeneralScaledGapModelReference
import PrimeGapNormality.Prime.CoreCalibratedRetentionSharp
import PrimeGapNormality.Prime.CoreCalibratedFrameMeanSharp

/-!
# Sharp rounded/scaled references for arbitrary calibrated mixtures

Actual ordered resampling uses contraction threshold T=2, discharged by
support-uniform calibration and the genuine Euler-product limit. Thus its
model coefficient is 24. The full original count and original-law cutoff
are unchanged. After one joint limit is fixed, the mean-two lemma applies
to that SAME nu and subsequence for every epsilon. Its actual restricted
fibre reference has mass at most two; there is no independent replacement
law or supplied contraction/mean/reference hypothesis in the endpoint.
-/
namespace PrimeGapNormality.Prime.CoreGeneralScaledGapModelReferenceSharp
open Filter Finset MeasureTheory CoreCyclic
open CoreCalibratedMixtureFiniteSupport CoreCalibratedMixtureProfile
  CoreCalibratedAuxiliaryFrame CoreCalibratedFrameProbability CoreCalibratedFrameLimit
  CoreCalibratedModelFinite CoreGeneralModelReference CoreRoundedModelFinite
  CoreGeneralScaledGapModelReference
open scoped Classical Topology NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
abbrev Circle := AddCircle (1 : ℝ)
abbrev Joint := CoreJointFrameLimit.Joint 1

theorem single_cutoff_bound (S y M J : ℕ) (hSy : S ≤ y)
    (hJ : 1 ≤ J) (hJM : J < M) {G R δ : ℝ} (hG : 1 < G) (hR : 0 < R) (hδ : 0 ≤ δ)
    (hθ : 0 < lateRetention S y) (hθ4 : lateRetention S y ≤ (1 : ℝ) / 4)
    (hret : lateRetention S y * G / Real.log G ≤ 2)
    (hcal : CoreRoughSyntheticScale.roughGapScale y / G ≤ 2)
    (test v : Finset ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ht0 : ∀ U, 0 ≤ test U) (htC : ∀ U, test U ≤ C) (hv : ∀ F, 0 ≤ v F)
    (hslot : ∀ σ : ResidueChoice S,
      ∀ n ∈ (Finset.Icc M (presieveSurvivors S σ).card).filter
        (fun n : ℕ => (n : ℝ) ≤ 2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y),
      ∀ F ∈ (presieveSurvivors S σ).powersetCard (n - 1),
        auxFrame_slotInsertSum (presieveSurvivors S σ) (J - 1)
          (corePositiveCutTest (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R test) F ≤
            3 * G / Real.log G * (v F + δ)) :
    CoreOriginalDeletedFrame.highMean y S M test ≤ (24 : ℝ) *
      ((∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryLayerFrameMass S y M F * v F) + δ) +
        C * coreFiniteRootMixUpperRootMass S y + 4 * C / R := by
  let I := OnePoint.FiniteExterior.frameRanks 0 J
  have hcut0 : ∀ U, 0 ≤ corePositiveCutTest I (J - 1) G R test U := by
    intro U
    unfold corePositiveCutTest
    split_ifs <;> first | exact le_rfl | exact ht0 U
  have hcutC : ∀ U, corePositiveCutTest I (J - 1) G R test U ≤ C := by
    intro U
    unfold corePositiveCutTest
    split_ifs <;> first | exact hC | exact htC U
  have hg := corePositive_highMean_le_frame_add_high S y M (J - 1)
    (corePositiveCutTest I (J - 1) G R test) (fun F => 3 * G / Real.log G * (v F + δ))
    hSy (by omega) hcut0 hcutC
    (fun F => mul_nonneg (div_nonneg (by positivity) (Real.log_pos hG).le) (add_nonneg (hv F) hδ))
    hθ hθ4 hslot
  have ht := corePositive_highMean_le_cut_add_originalTail y S M I (J - 1) G R test
    (by omega) (fun i hi =>
      OnePoint.FiniteExterior.frameRanks_valid (w := 0) hJ (by simpa using hJM) hi)
    (zero_lt_one.trans hG) hR ht0 htC
  have hm := layer_contraction S y M hSy hG
    (by norm_num : (0 : ℝ) ≤ 2) hδ hret v hv
  have htail : (2 * (I.card : ℝ)) / (R * G * eulerProdNat y) ≤ 4 / R := by
    have hi : I.card = 1 := by
      simpa only [I, Nat.mul_zero, Nat.zero_add] using OnePoint.FiniteExterior.frameRanks_card 0 J hJ
    rw [hi, Nat.cast_one, mul_one]
    have hh := mul_le_mul_of_nonneg_left hcal (show 0 ≤ 2 / R by positivity)
    have he : 2 / (R * G * eulerProdNat y) =
        (2 / R) * (CoreRoughSyntheticScale.roughGapScale y / G) := by
      unfold CoreRoughSyntheticScale.roughGapScale
      field_simp [hR.ne', (zero_lt_one.trans hG).ne', (eulerProdNat_pos y).ne'] <;> ring
    rw [he]
    exact hh.trans_eq (by ring)
  have hh := (ht.trans (_root_.add_le_add hg le_rfl)).trans
    (_root_.add_le_add (_root_.add_le_add hm le_rfl) (mul_le_mul_of_nonneg_left htail hC))
  exact hh.trans_eq (by ring)

/-- Actual arbitrary-cutoff finite resampling estimate, with no slot or
mean bound as an end premise. -/
theorem eventually_mixture
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (F : Fin k → ℕ → ℤ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (b : Fin k → ℤ)
    (hscale : CoreScaledGapModelReference.CompactScaling F a b)
    {R : ℝ} (hR : 0 < R) (f : Circle →ᵇ ℝ) {Kf : ℝ≥0}
    (hKf : LipschitzWith Kf f) (hf : ∀ x, 0 ≤ f x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ G : ℝ in atTop, ∀ (J S M : ℕ) (ω : ℕ → ℝ), Weights ω S →
      1 ≤ J → J < M → phaseAt hk r (J - 1) = s → 1 < G → ⌊G⌋₊ ≤ S →
      (∀ y, ω y ≠ 0 → 0 < lateRetention S y ∧ lateRetention S y ≤ (1 : ℝ) / 4 ∧
        lateRetention S y * G / Real.log G ≤ 2 ∧
        CoreRoughSyntheticScale.roughGapScale y / G ≤ 2) →
      1 ≤ G ^ a / (B : ℝ) ^ (J + 1) → G ^ a / (B : ℝ) ^ (J + 1) < (B : ℝ) ^ k →
      CoreCalibratedModelFinite.mean ω S M (actualTest B hk r F M f) ≤
        (24 : ℝ) * ((∫ z, compactTest hR.le ha ((B : ℝ) * (b s : ℝ))
          (b (cyclicSucc hk s) : ℝ) f z ∂(jointLaw ω S M (OnePoint.FiniteExterior.frameRank 0 J)
            G (G ^ a / (B : ℝ) ^ (J + 1)) (outerMap B hk r F M J S) : Measure Joint)) + δ) +
          CoreCalibratedMixtureCountException.highMass ω S * ‖f‖ + 4 * ‖f‖ / R := by
  filter_upwards [CoreScaledGapModelReference.eventually_slot_sum_le F b ha ha1 hscale hR hB hk r s f hKf hf hδ]
    with G hslot
  intro J S M ω hω hJ hJM hlabel hG hfloor hret hlo hhi
  let θ := G ^ a / (B : ℝ) ^ (J + 1)
  let O := outerMap B hk r F M J S
  let v : Finset ℕ → ℝ := fun E => compactTest hR.le ha ((B : ℝ) * (b s : ℝ))
    (b (cyclicSucc hk s) : ℝ) f (CoreActualFrameJoint.jointPoint 0 J G θ O E)
  have hv : ∀ E, 0 ≤ v E := fun E => compactTest_nonneg hR.le ha _ _ f hf _ (by
    rw [point_width J hJ]
    exact div_nonneg (Nat.cast_nonneg _) (zero_lt_one.trans hG).le)
  have hv0 : v ∅ = 0 := by
    simpa only [v, CoreActualFrameJoint.jointPoint, CoreActualFrameJoint.localFrame_empty] using
      compactTest_empty hR.le ha ((B : ℝ) * (b s : ℝ)) (b (cyclicSucc hk s) : ℝ) f (O ∅) θ
  obtain ⟨N, hz, hs⟩ := hω.2.2
  have hp (y : ℕ) : ω y * CoreOriginalDeletedFrame.highMean y S M (actualTest B hk r F M f) ≤
      ω y * ((24 : ℝ) * ((∑ E ∈ (offsetWindow S).powerset, coreAuxiliaryLayerFrameMass S y M E * v E) + δ) +
        ‖f‖ * coreFiniteRootMixUpperRootMass S y + 4 * ‖f‖ / R) := by
    by_cases hy : ω y = 0
    · simp only [hy, zero_mul, le_refl]
    · have hr := hret y hy
      apply mul_le_mul_of_nonneg_left _ (hω.1 y)
      exact single_cutoff_bound S y M J (hω.2.1 y hy) hJ hJM hG hR hδ.le
        hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 _ v (norm_nonneg f)
        (fun U => hf _) (fun U => f.apply_le_norm _) hv (by
          intro σ n hn E hE
          exact hslot M J S n σ E hJ hJM hlabel hfloor
            (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1 hE hlo hhi)
  have hint : (∑ E ∈ (offsetWindow S).powerset, mass ω S M E * v E) =
      ∫ z, compactTest hR.le ha ((B : ℝ) * (b s : ℝ)) (b (cyclicSucc hk s) : ℝ) f z
        ∂(jointLaw ω S M (OnePoint.FiniteExterior.frameRank 0 J) G θ O : Measure Joint) := by
    rw [integral_jointLaw _ _ _ hω _ _ _ _ _ (compactTest hR.le ha _ _ f).continuous.measurable]
    change _ = ∑ E ∈ (offsetWindow S).powerset, completed ω S M E * v E
    rw [completed_expectation, hv0, mul_zero, add_zero]
  rw [mean_eq_finite ω S M hz]
  refine (sum_le_sum fun y _ => hp y).trans_eq ?_
  rw [weighted_three_terms _ _ _ N hs, ← expectation_eq_finite ω S M hz v, hint]
  unfold CoreCalibratedMixtureCountException.highMass
  rw [weighted_tsum_eq_sum_of_tail_zero ω _ hz]
  ring

theorem exists_reference_subsequence
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (b : Fin k → ℤ) (hb : b ≠ 0) (hscale : CoreScaledGapModelReference.CompactScaling F a b)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ σ : Measure Circle,
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 2 ∧
      ∀ (f : Circle →ᵇ ℝ) (Kf : ℝ≥0), LipschitzWith Kf f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          modelMean B hk r F κ G ω (ψ n) f ≤ (24 : ℝ) * (∫ x, f x ∂σ) + ε := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hM := tendsto_rank_ratio hκp hG
  obtain ⟨s, hs, J, hJ⟩ := exists_label_ranks hB hk r ha ha1 b hb hκ hG
  let q := fun X => OnePoint.FiniteExterior.frameRank 0 (J X)
  let θ := scale B a G J
  let O := fun X => outerMap B hk r F (rank κ G X) (J X) (physicalSpan G (rank κ G) X)
  have hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧ ∀ i, q X i + 1 < rank κ G X := by
    filter_upwards [hJ] with X hx
    exact ⟨OnePoint.FiniteExterior.frameRank_injective 0 (J X) hx.1,
      OnePoint.FiniteExterior.frameRank_valid (w := 0) hx.1 (by simpa using hx.2.1)⟩
  have hθ : ∀ᶠ X in atTop, θ X ∈ Set.Icc 1 ((B : ℝ) ^ k) :=
    hJ.mono fun X hx => ⟨hx.2.2.2.1, hx.2.2.2.2.le⟩
  obtain ⟨ν, ψ, hψ, hweak, hACunused, hnonneg, hθrange, hWi, hWmean⟩ :=
    CoreCalibratedFrameProbability.exists_joint_limit hG hκp hM hω hsum hcal q hq θ O hθ (0 : Fin 1)
  change Integrable CoreRoundedReferenceMeasure.width (ν : Measure Joint) at hWi
  change (∫ z, CoreRoundedReferenceMeasure.width z ∂(ν : Measure Joint)) ≤ 4 at hWmean
  have hW : ∀ᵐ z ∂(ν : Measure Joint), 0 ≤ CoreRoundedReferenceMeasure.width z := hnonneg.mono fun z hz => hz 0
  have hmeanTwo := CoreCalibratedFrameMeanSharp.coordinate_integral_le_two
    hG hκp hM hω hsum hcal q (hq.mono fun X hx => hx.2) θ O
    ν ψ hψ.tendsto_atTop hweak (0 : Fin 1) hW
  change Integrable CoreRoundedReferenceMeasure.width (ν : Measure Joint) ∧
    (∫ z, CoreRoundedReferenceMeasure.width z ∂(ν : Measure Joint)) ≤ 2 at hmeanTwo
  let A := (B : ℝ) * (b s : ℝ)
  let C := (b (cyclicSucc hk s) : ℝ)
  let σ := CoreRoundedReferenceMeasure.referenceMeasure ν a A C
  have hfin : IsFiniteMeasure σ := CoreRoundedReferenceMeasure.referenceMeasure_finite ν ha A C hW hWi
  have hac : σ ≪ volume := CoreRoundedReferenceMeasure.referenceMeasure_absolutelyContinuous ν ha ha1
    (CoreRoundedReferenceMeasure.usableCoefficients_of_label hB hk b s hs)
    (hθrange.mono fun z hz => (zero_lt_one.trans_le hz.1).ne')
  have hmass : σ Set.univ ≤ ENNReal.ofReal 2 := by
    change CoreRoundedReferenceMeasure.referenceMeasure ν a A C Set.univ ≤ ENNReal.ofReal 2
    rw [CoreRoundedReferenceMeasure.referenceMeasure_mass_eq_integral ν ha A C hW hWi]
    exact ENNReal.ofReal_le_ofReal hmeanTwo.2
  refine ⟨ψ, hψ, σ, hfin, hac, hmass, ?_⟩
  have hweakModel : Tendsto
      (fun n => modelLaw B hk r F a κ G ω J (ψ n)) atTop (𝓝 ν) := by
    change Tendsto (fun n => profileLaw G (rank κ G) ω q θ O (ψ n)) atTop (𝓝 ν)
    exact hweak
  have hhigh : Tendsto (fun n =>
      CoreCalibratedMixtureCountException.highMass (ω (ψ n))
        (physicalSpan G (rank κ G) (ψ n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (CoreCalibratedMixtureCountException.tendsto_mixture_high_zero
        hG hκp hM hω hsum hcal).comp hψ.tendsto_atTop
  apply CoreRoundedModelSubsequence.reference_domination_of_finite_bounds ha
    (fun n => modelLaw B hk r F a κ G ω J (ψ n)) ν hweakModel hW hWi
    (fun n f => modelMean B hk r F κ G ω (ψ n) f) (by norm_num : (0 : ℝ) ≤ 24)
    (fun n => CoreCalibratedMixtureCountException.highMass (ω (ψ n)) (physicalSpan G (rank κ G) (ψ n)))
    hhigh
  intro R hR f Kf hKf hf δ hδ
  have he := hG.eventually (eventually_mixture hB hk r s F ha ha1 b hscale hR f hKf hf hδ)
  have hfinite : ∀ᶠ X : ℕ in atTop,
      modelMean B hk r F κ G ω X f ≤
        (24 : ℝ) * (∫ z, compactTest hR.le ha A C f z
          ∂(modelLaw B hk r F a κ G ω J X : Measure Joint)) +
        8 * ‖f‖ / R +
        CoreCalibratedMixtureCountException.highMass (ω X)
          (physicalSpan G (rank κ G) X) * ‖f‖ + (24 : ℝ) * δ := by
    filter_upwards [he, hJ, eventually_profile_data hG hκp hM hω hsum hcal,
      eventually_scaled_retention hG hκp hM hcal,
      CoreCalibratedRetentionSharp.eventually_scaled_retention_lt_two hG hκp hM hcal]
      with X hm hj hdata hret hsharp
    have hwgt : Weights (ω X) (physicalSpan G (rank κ G) X) := ⟨hω X, hdata.2.1, hdata.2.2.2⟩
    have hp := hm (J X) (physicalSpan G (rank κ G) X) (rank κ G X) (ω X) hwgt
      hj.1 hj.2.1 hj.2.2.1 hret.1 hret.2.2.1 (by
        intro y hy
        have hh := hret.2.2.2 y (lt_of_le_of_ne (hω X y) (Ne.symm hy))
        exact ⟨hh.2.1, hh.2.2.1,
          (hsharp y (lt_of_le_of_ne (hω X y) (Ne.symm hy))).le, hdata.2.2.1 y hy⟩) hj.2.2.2.1 hj.2.2.2.2
    have htail : 4 * ‖f‖ / R ≤ 8 * ‖f‖ / R := by
      exact div_le_div_of_nonneg_right (by nlinarith [norm_nonneg f]) hR.le
    have hh := hp.trans (_root_.add_le_add le_rfl htail)
    dsimp only [modelMean, modelLaw, profileLaw, scale, A, C, q, θ, O,
      Function.comp_apply] at hh ⊢
    exact hh.trans_eq (by ring)
  simpa only [Function.comp_def] using hψ.tendsto_atTop.eventually hfinite

end
end PrimeGapNormality.Prime.CoreGeneralScaledGapModelReferenceSharp
