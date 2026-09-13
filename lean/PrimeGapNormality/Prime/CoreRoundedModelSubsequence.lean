import PrimeGapNormality.Prime.CoreRoundedModelFinite

/-!
# Actual rounded model and its fixed-reference subsequence

The slot estimate is discharged, the actual full retained-count law is
averaged, and the original-law cutoff loss is retained. A usable integer
leading column and all actual admissible ranks are then derived. One joint
limit and its finite AC reference are chosen before every test or cutoff;
ordinary weak convergence of the G-independent leading test completes
the model domination. No model/reference estimate is an end hypothesis.
-/

namespace PrimeGapNormality.Prime.CoreRoundedModelSubsequence

open Finset Filter MeasureTheory CoreCyclic CoreRoundedPowerScaling
  CoreRoundedModelFinite CoreLocalModelMixture
open scoped Topology Classical NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

abbrev Circle := AddCircle (1 : ℝ)
abbrev Joint := CoreJointFrameLimit.Joint 1

theorem compact_expectation_eq_joint
    (X S L J : ℕ) (G θ : ℝ) (O : Finset ℕ → Circle)
    {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (A C : ℝ) (f : Circle →ᵇ ℝ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryFrameMass X S L F *
      compactTest hR ha A C f (CoreActualFrameJoint.jointPoint 0 J G θ O F)) =
      ∫ z, compactTest hR ha A C f z
        ∂(CoreActualFrameJoint.jointLaw X S L 0 J G θ O hSy hZ : Measure Joint) := by
  have hh := CoreActualFrameJoint.integral_jointLaw X S L 0 J G θ O hSy hZ
    (compactTest hR ha A C f) (compactTest hR ha A C f).continuous.measurable
  have hmissing : coreAuxiliaryFrameMissingMass X S L * (0 : ℝ) = 0 := mul_zero _
  rw [compactTest_empty hR ha A C f, hmissing, add_zero] at hh
  exact hh.symm

/-- Actual finite-root mixture domination by the leading compact joint
test. The Selberg and rounded approximation inputs are proved internally;
the remaining hypotheses are only literal finite scale/rank validity. -/
theorem eventually_finiteRootMean_le_joint_add_errors
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a R T : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hR : 0 < R) (hT : 0 ≤ T)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    {B : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (f : Circle →ᵇ ℝ) {Kf : ℝ≥0} (hKf : LipschitzWith Kf f)
    (hf : ∀ x, 0 ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ G : ℝ in atTop, ∀ (J X S L : ℕ),
      1 ≤ J → J < L → phaseAt hk r (J - 1) = s →
      ∀ (hG : 1 < G) (hfloor : ⌊G⌋₊ ≤ S)
        (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X),
      (∀ t ∈ mixScale X, 0 < lateRetention S (sieveCutoff (t : ℝ))) →
      (∀ t ∈ mixScale X, lateRetention S (sieveCutoff (t : ℝ)) ≤ (1 : ℝ) / 4) →
      1 ≤ G ^ a / (B : ℝ) ^ (J + 1) → G ^ a / (B : ℝ) ^ (J + 1) < (B : ℝ) ^ k →
      (∀ t ∈ mixScale X, lateRetention S (sieveCutoff (t : ℝ)) * G / Real.log G ≤ T) →
      corePositiveFiniteRootMean X S L (actualTest B hk r (roundedCombination kind alpha b) L f) ≤
        12 * T * ((∫ z, compactTest hR.le ha ((B : ℝ) * leadingColumn alpha b a s)
            (leadingColumn alpha b a (cyclicSucc hk s)) f z
          ∂(CoreActualFrameJoint.jointLaw X S L 0 J G (G ^ a / (B : ℝ) ^ (J + 1))
            (CoreRoundedModelFinite.outerMap B hk r (roundedCombination kind alpha b) L J S)
            hSy hZ : Measure Joint)) + ε) +
          nonMainTerm X S L (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R ‖f‖ := by
  filter_upwards [eventually_slot_sum_le kind alpha b ha ha1 hR halpha hB hk r s f hKf hf hε]
    with G hslot
  intro J X S L hJ hJL hlabel hG hfloor hSy hZ hlate hquarter hθlo hθhi hret
  let O := CoreRoundedModelFinite.outerMap B hk r (roundedCombination kind alpha b) L J S
  let θ := G ^ a / (B : ℝ) ^ (J + 1)
  let Acoef := (B : ℝ) * leadingColumn alpha b a s
  let Ccoef := leadingColumn alpha b a (cyclicSucc hk s)
  let v := fun F => compactTest hR.le ha Acoef Ccoef f (CoreActualFrameJoint.jointPoint 0 J G θ O F)
  let frameBound := fun (_t : ℕ) (F : Finset ℕ) => 3 * G / Real.log G * (v F + ε)
  have hv : ∀ F, 0 ≤ v F := by
    intro F
    apply compactTest_nonneg hR.le ha Acoef Ccoef f hf
    rw [point_width J hJ]
    exact div_nonneg (Nat.cast_nonneg _) (zero_lt_one.trans hG).le
  have hframe0 : ∀ t ∈ mixScale X, ∀ F, 0 ≤ frameBound t F := by
    intro t ht F
    exact mul_nonneg (div_nonneg (by positivity) (Real.log_pos hG).le) (add_nonneg (hv F) hε.le)
  have hroot := corePositiveFiniteRootMean_le_frame_high_originalBad
    X S L (J - 1) (OnePoint.FiniteExterior.frameRanks 0 J) G R
    (actualTest B hk r (roundedCombination kind alpha b) L f) frameBound
    hZ (by omega : J - 1 + 1 < L) (fun U => hf _) (fun U => f.apply_le_norm _)
    hSy hlate hquarter hframe0 (by
      intro t ht σ n hn F hF
      exact hslot L J S n σ F hJ hJL hlabel hfloor (mem_Icc.mp (mem_filter.mp hn).1).1 hF hθlo hθhi)
  have hdecomp :
      (∑ t ∈ mixScale X, mixWeightV t *
        (((4 : ℝ) * lateRetention S (sieveCutoff (t : ℝ)) *
            (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F *
              frameBound t F) + ‖f‖ * coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) +
          ‖f‖ * CoreOriginalDeletedFrame.highMean (sieveCutoff (t : ℝ)) S L
            (fun U => if corePositiveFrameBad (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) G R U
              then 1 else 0))) / mixZ X =
        mainFrameTerm X S L G ε v + nonMainTerm X S L (OnePoint.FiniteExterior.frameRanks 0 J)
          (J - 1) G R ‖f‖ := by
    unfold mainFrameTerm nonMainTerm
    rw [← add_div, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro t ht
    dsimp only [frameBound]
    ring
  have hmain := mainFrameTerm_le X S L v hG hε.le hT hv hSy hZ hret
  have hint := compact_expectation_eq_joint X S L J G θ O hR.le ha Acoef Ccoef f hSy hZ
  change (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryFrameMass X S L F * v F) = _ at hint
  have hh := (hroot.trans_eq hdecomp).trans (_root_.add_le_add hmain le_rfl)
  rw [hint] at hh
  exact hh

/-- At the actual physical profile, both nonmain pieces have the original
law normalization. In width zero the fixed-deletion loss is 8||f||/R. -/
theorem nonMainTerm_profile_le (κ : ℝ) (X J : ℕ) {R : ℝ} (hR : 0 < R)
    (hZ : 0 < mixZ X) (hJ : 1 ≤ J) (hJL : J < profileL κ X)
    (hG : 0 < windowG X) (f : Circle →ᵇ ℝ)
    (hcal : ∀ t ∈ mixScale X, (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / windowG X ≤ 4) :
    nonMainTerm X (ahlSmall_window κ X) (profileL κ X)
      (OnePoint.FiniteExterior.frameRanks 0 J) (J - 1) (windowG X) R ‖f‖ ≤
      ‖f‖ * coreFiniteRootMixUpperException κ X + 8 * ‖f‖ / R := by
  simpa only [Nat.zero_add, Nat.add_zero, Nat.mul_zero, Nat.cast_one, mul_one] using
    nonMainTerm_frameRanks_le κ X (profileL κ X) 0 J hZ
      (by simpa only [Nat.zero_add] using hJ)
      (by simpa only [Nat.add_zero] using hJL) hG hR (norm_nonneg f) hcal

/-! ## Reference passage for the G-independent leading compact test -/

theorem integral_reference (ν : ProbabilityMeasure Joint) {a : ℝ} (ha : 0 < a)
    (A C : ℝ) (hW : ∀ᵐ z ∂(ν : Measure Joint), 0 ≤ CoreRoundedReferenceMeasure.width z)
    (hWi : Integrable CoreRoundedReferenceMeasure.width (ν : Measure Joint)) (f : Circle →ᵇ ℝ) :
    (∫ x, f x ∂CoreRoundedReferenceMeasure.referenceMeasure ν a A C) =
      ∫ z, (∫ t in (0 : ℝ)..CoreRoundedReferenceMeasure.width z,
        f (CoreRoundedReferenceMeasure.phase a A C (z, t))) ∂(ν : Measure Joint) := by
  let σ := CoreRoundedReferenceMeasure.referenceMeasure ν a A C
  let W := CoreRoundedReferenceMeasure.width
  let H := CoreRoundedReferenceMeasure.phase a A C
  let D := CoreRestrictedFibreImageAC.insertionDomain W
  have hH : Measurable H := (CoreRoundedReferenceMeasure.continuous_phase ha A C).measurable
  have hD : MeasurableSet D := CoreRestrictedFibreImageAC.measurableSet_insertionDomain
    CoreRoundedReferenceMeasure.continuous_width.measurable
  letI : IsFiniteMeasure σ := CoreRoundedReferenceMeasure.referenceMeasure_finite ν ha A C hW hWi
  have hfi : Integrable f σ := f.integrable _
  have hcomp : Integrable (fun z => f (H z)) (((ν : Measure Joint).prod volume).restrict D) :=
    hfi.comp_aemeasurable hH.aemeasurable
  have hind : Integrable (D.indicator (fun z => f (H z))) ((ν : Measure Joint).prod volume) :=
    (integrable_indicator_iff hD).2 hcomp
  change (∫ x, f x ∂Measure.map H (((ν : Measure Joint).prod volume).restrict D)) = _
  rw [integral_map_of_stronglyMeasurable hH f.continuous.stronglyMeasurable,
    ← integral_indicator hD, integral_prod _ hind]
  apply integral_congr_ae
  filter_upwards [hW] with z hz
  change (∫ t, (Set.Ioo 0 (W z)).indicator (fun t => f (H (z, t))) t) = _
  rw [integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le hz,
    integral_Ioc_eq_integral_Ioo]

theorem compact_integral_le_reference (ν : ProbabilityMeasure Joint) {a R : ℝ}
    (ha : 0 < a) (hR : 0 ≤ R) (A C : ℝ)
    (hW : ∀ᵐ z ∂(ν : Measure Joint), 0 ≤ CoreRoundedReferenceMeasure.width z)
    (hWi : Integrable CoreRoundedReferenceMeasure.width (ν : Measure Joint))
    (f : Circle →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∫ z, compactTest hR ha A C f z ∂(ν : Measure Joint)) ≤
      ∫ x, f x ∂CoreRoundedReferenceMeasure.referenceMeasure ν a A C := by
  let g := fun z : Joint => ∫ t in (0 : ℝ)..CoreRoundedReferenceMeasure.width z,
    f (CoreRoundedReferenceMeasure.phase a A C (z, t))
  have hgc : Continuous g := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact f.continuous.comp (CoreRoundedReferenceMeasure.continuous_phase ha A C)
    · exact CoreRoundedReferenceMeasure.continuous_width
  have hgi : Integrable g (ν : Measure Joint) := by
    apply (hWi.norm.const_mul ‖f‖).mono' hgc.measurable.aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    simpa only [g, sub_zero, Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := CoreRoundedReferenceMeasure.width z)
        (fun t _ => f.norm_coe_le_norm (CoreRoundedReferenceMeasure.phase a A C (z, t)))
  have hpair : ∀ᵐ z ∂(ν : Measure Joint), 0 ≤ compactTest hR ha A C f z ∧
      compactTest hR ha A C f z ≤ g z := by
    filter_upwards [hW] with z hz
    exact CoreCompactFrameTest.rawTest_nonneg_le_fullIntegral hR CoreJointFrameLimit.frame
      CoreRoundedReferenceMeasure.width (fun z t => CoreRoundedReferenceMeasure.phase a A C (z, t))
      (CoreRoundedReferenceMeasure.continuous_phase ha A C) f hf z hz
  rw [integral_reference ν ha A C hW hWi]
  exact integral_mono_of_nonneg (hpair.mono fun z hz => hz.1) hgi (hpair.mono fun z hz => hz.2)

theorem reference_domination_of_finite_bounds
    {a A C : ℝ} (ha : 0 < a) (μ : ℕ → ProbabilityMeasure Joint) (ν : ProbabilityMeasure Joint)
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hW : ∀ᵐ z ∂(ν : Measure Joint), 0 ≤ CoreRoundedReferenceMeasure.width z)
    (hWi : Integrable CoreRoundedReferenceMeasure.width (ν : Measure Joint))
    (mean : ℕ → (Circle →ᵇ ℝ) → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hfinite : ∀ (R : ℝ) (hR : 0 < R), ∀ (f : Circle →ᵇ ℝ) (K : ℝ≥0),
      LipschitzWith K f → (∀ x, 0 ≤ f x) → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, mean n f ≤
        c * (∫ z, compactTest hR.le ha A C f z ∂(μ n : Measure Joint)) +
          8 * ‖f‖ / R + η n * ‖f‖ + c * δ) :
    ∀ (f : Circle →ᵇ ℝ) (K : ℝ≥0), LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        mean n f ≤ c * (∫ x, f x ∂CoreRoundedReferenceMeasure.referenceMeasure ν a A C) + ε := by
  intro f K hK hf ε hε
  let R := max 1 (32 * ‖f‖ / ε)
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  let δ := ε / (4 * (c + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcδ : c * δ ≤ ε / 4 := by
    have heq : (4 * (c + 1)) * δ = ε := by
      dsimp [δ]
      field_simp [(show 0 < c + 1 from by positivity).ne']
    nlinarith
  have hcut : 8 * ‖f‖ / R ≤ ε / 4 := by
    apply (div_le_iff₀ hR).2
    have hh := (div_le_iff₀ hε).1 (le_max_right 1 (32 * ‖f‖ / ε))
    change 32 * ‖f‖ ≤ R * ε at hh
    nlinarith
  let I := ∫ z, compactTest hR.le ha A C f z ∂(ν : Measure Joint)
  have hI : I ≤ ∫ x, f x ∂CoreRoundedReferenceMeasure.referenceMeasure ν a A C :=
    compact_integral_le_reference ν ha hR.le A C hW hWi f hf
  have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak
    (compactTest hR.le ha A C f)
  have herr : Tendsto (fun n => η n * ‖f‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hη.mul_const ‖f‖
  filter_upwards [hfinite R hR f K hK hf δ hδ,
    hlim.eventually_le_const (by dsimp only [I]; linarith : I < I + δ),
    herr.eventually_le_const (by linarith : (0 : ℝ) < ε / 4)] with n hn ht he
  have hb := mul_le_mul_of_nonneg_left (ht.trans (_root_.add_le_add hI le_rfl)) hc
  linarith

/-! ## Fixed integer leading label and actual admissible profiles -/

def integerLeadingColumn {I : Type*} [Fintype I] {k : ℕ}
    (alpha : I → ℝ) (b : Fin k → I → ℤ) (a : ℝ) (s : Fin k) : ℤ :=
  ∑ i, if alpha i = a then b s i else 0

theorem integerLeadingColumn_cast {I : Type*} [Fintype I] {k : ℕ}
    (alpha : I → ℝ) (b : Fin k → I → ℤ) (a : ℝ) (s : Fin k) :
    (integerLeadingColumn alpha b a s : ℝ) = leadingColumn alpha b a s := by
  simp [integerLeadingColumn, leadingColumn]

theorem integerLeadingColumn_ne_zero {I : Type*} [Fintype I] {k : ℕ}
    (alpha : I → ℝ) (b : Fin k → I → ℤ) (a : ℝ)
    (hb : leadingColumn alpha b a ≠ 0) : integerLeadingColumn alpha b a ≠ 0 := by
  intro hz
  apply hb
  funext s
  rw [← integerLeadingColumn_cast, hz]
  simp

structure Admissible (B : ℕ) {k : ℕ} (hk : 0 < k) (r s : Fin k)
    (a κ : ℝ) (X J : ℕ) : Prop where
  gap_gt : 1 < windowG X
  floor_le : ⌊windowG X⌋₊ ≤ ahlSmall_window κ X
  lower : 1 ≤ J
  upper : J < profileL κ X
  label : phaseAt hk r (J - 1) = s
  scale_lower : 1 ≤ windowG X ^ a / (B : ℝ) ^ (J + 1)
  scale_upper : windowG X ^ a / (B : ℝ) ^ (J + 1) < (B : ℝ) ^ k
  cutoff : ∀ t ∈ mixScale X, ahlSmall_window κ X ≤ sieveCutoff (t : ℝ)
  retention_pos : ∀ t ∈ mixScale X, 0 < lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ))
  retention_small : ∀ t ∈ mixScale X,
    lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) ≤ (1 / 4 : ℝ)
  retention_bound : ∀ t ∈ mixScale X,
    lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) * windowG X / Real.log (windowG X) ≤
      3 / eulerProdLowerConst
  calibration : ∀ t ∈ mixScale X, (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / windowG X ≤ 4
  normalization_pos : 0 < mixZ X

private theorem mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos'
  · exact fun t _ => mixWeightV_nonneg t
  · refine ⟨2 * X, ?_, eulerProdNat_pos _⟩
    simp only [mixScale, mem_Ioc]
    omega

theorem exists_fixed_label_admissible
    {I : Type*} [Fintype I] {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (alpha : I → ℝ) (b : Fin k → I → ℤ) {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hb : leadingColumn alpha b a ≠ 0) :
    ∃ s : Fin k, CoreRoundedCriticalRank.UsableLeadingLabel B hk a (integerLeadingColumn alpha b a) s ∧
      ∀ᶠ X : ℕ in atTop, ∃ J : ℕ, Admissible B hk r s a κ X J := by
  have hκ0 : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  obtain ⟨s, hs, hrank⟩ := CoreRoundedCriticalRank.exists_usableLabel_eventually_rank
    hB hk r ha ha1 hκ (integerLeadingColumn alpha b a) (integerLeadingColumn_ne_zero alpha b a hb)
  refine ⟨s, hs, ?_⟩
  filter_upwards [hrank, eventually_coreLinearMixtureScales hκ0,
    coreFRMUpper_eventually_lateRetention_le_quarter hκ0, eventually_ge_atTop (1 : ℕ)]
    with X hrankX hscale hret hX
  obtain ⟨J, hJ, hL, hlabel, hlo, hhi⟩ := hrankX
  refine ⟨J, ⟨hscale.1, hscale.2.2.2.1, hJ, hL, hlabel, hlo, hhi,
    ?_, ?_, hret, ?_, ?_, mixZ_pos hX⟩⟩
  · exact fun t ht => (hscale.2.2.2.2 t ht).1
  · intro t ht
    exact rootedEulerProdNat_pos (by have hh := hscale.2.2.1; omega)
  · exact fun t ht => (hscale.2.2.2.2 t ht).2.2.2.1
  · exact fun t ht => (hscale.2.2.2.2 t ht).2.2.2.2

def modelConstant : ℝ := 12 * (3 / eulerProdLowerConst)
theorem modelConstant_nonneg : 0 ≤ modelConstant := by
  unfold modelConstant
  exact mul_nonneg (by norm_num) coreLinearScales_retentionConst_pos.le

def profileScale (B : ℕ) (a : ℝ) (X J : ℕ) : ℝ := windowG X ^ a / (B : ℝ) ^ (J + 1)

def profileLaw (B : ℕ) {k : ℕ} (hk : 0 < k) (r s : Fin k)
    (Fobs : Fin k → ℕ → ℤ) (a κ : ℝ) (X J : ℕ) (h : Admissible B hk r s a κ X J) :
    ProbabilityMeasure Joint :=
  CoreActualFrameJoint.jointLaw X (ahlSmall_window κ X) (profileL κ X) 0 J
    (windowG X) (profileScale B a X J)
    (CoreRoundedModelFinite.outerMap B hk r Fobs (profileL κ X) J (ahlSmall_window κ X))
    h.cutoff h.normalization_pos

def profileMean (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (Fobs : Fin k → ℕ → ℤ) (κ : ℝ) (X : ℕ) (f : Circle →ᵇ ℝ) : ℝ :=
  corePositiveFiniteRootMean X (ahlSmall_window κ X) (profileL κ X)
    (actualTest B hk r Fobs (profileL κ X) f)

theorem eventually_profile_compact_bound
    {I : Type*} [Fintype I] {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (X j : ℕ → ℕ) (hX : Tendsto X atTop atTop)
    (had : ∀ n, Admissible B hk r s a κ (X n) (j n))
    (R : ℝ) (hR : 0 < R) (f : Circle →ᵇ ℝ) (K : ℝ≥0)
    (hK : LipschitzWith K f) (hf : ∀ x, 0 ≤ f x) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, profileMean B hk r (roundedCombination kind alpha b) κ (X n) f ≤
      modelConstant * (∫ z, compactTest hR.le ha ((B : ℝ) * leadingColumn alpha b a s)
        (leadingColumn alpha b a (cyclicSucc hk s)) f z
        ∂(profileLaw B hk r s (roundedCombination kind alpha b) a κ (X n) (j n) (had n) : Measure Joint)) +
      8 * ‖f‖ / R + coreFiniteRootMixUpperException κ (X n) * ‖f‖ + modelConstant * δ := by
  have he := (tendsto_windowG_atTop.comp hX).eventually
    (eventually_finiteRootMean_le_joint_add_errors kind alpha b ha ha1 hR
      coreLinearScales_retentionConst_pos.le halpha hB hk r s f hK hf hδ)
  filter_upwards [he] with n hn
  have hm := hn (j n) (X n) (ahlSmall_window κ (X n)) (profileL κ (X n))
    (had n).lower (had n).upper (had n).label (had n).gap_gt (had n).floor_le
    (had n).cutoff (had n).normalization_pos (had n).retention_pos (had n).retention_small
    (had n).scale_lower (had n).scale_upper (had n).retention_bound
  have herr := nonMainTerm_profile_le κ (X n) (j n) hR (had n).normalization_pos
    (had n).lower (had n).upper (zero_lt_one.trans (had n).gap_gt) f (had n).calibration
  have hh := hm.trans (_root_.add_le_add le_rfl herr)
  change profileMean B hk r (roundedCombination kind alpha b) κ (X n) f ≤
    modelConstant * (_ + δ) + (‖f‖ * coreFiniteRootMixUpperException κ (X n) + 8 * ‖f‖ / R) at hh
  exact hh.trans_eq (by
    dsimp only [profileLaw, profileScale, Function.comp_apply]
    ring)

/-! ## Final actual rounded model endpoint -/

/-- Every scale sequence admits a further subsequence with one fixed
finite AC reference controlling all positive Lipschitz tests. All rounded
expansion, slot, presieve, moment and reference suppliers are discharged.
Only the actual rounded data and the paper's base/profile bound remain. -/
theorem exists_reference_subsequence
    {I : Type*} [Fintype I] {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (hb : leadingColumn alpha b a ≠ 0) (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (X : ℕ → ℕ) (hX : Tendsto X atTop atTop) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ σ : Measure Circle,
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 8 ∧
      ∀ (f : Circle →ᵇ ℝ) (K : ℝ≥0), LipschitzWith K f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          profileMean B hk r (roundedCombination kind alpha b) κ (X (ψ n)) f ≤
            modelConstant * (∫ x, f x ∂σ) + ε := by
  have hκ0 : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  obtain ⟨s, hs, he⟩ := exists_fixed_label_admissible hB hk r alpha b ha ha1 hκ hb
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hX.eventually he)
  let Y := fun n => X (n + n₀)
  have hY : Tendsto Y atTop atTop := hX.comp (tendsto_add_atTop_nat n₀)
  have hchoose : ∀ n, ∃ J, Admissible B hk r s a κ (Y n) J :=
    fun n => hn₀ (n + n₀) (Nat.le_add_left _ _)
  let j := fun n => Classical.choose (hchoose n)
  have had : ∀ n, Admissible B hk r s a κ (Y n) (j n) :=
    fun n => Classical.choose_spec (hchoose n)
  let θ := fun n => profileScale B a (Y n) (j n)
  let O := fun n => CoreRoundedModelFinite.outerMap B hk r (roundedCombination kind alpha b)
    (profileL κ (Y n)) (j n) (ahlSmall_window κ (Y n))
  obtain ⟨ν, χ, hχ, hweak, hW, hscale, hWi, hfinite, hac, hmass⟩ :=
    CoreRoundedReferenceMeasure.exists_actual_profile_reference hB hk ha ha1 hκ0
      (integerLeadingColumn alpha b a) s hs Y hY j θ O
      (fun n => (had n).cutoff) (fun n => (had n).normalization_pos)
      (fun n => zero_lt_one.trans (had n).gap_gt) (fun n => (had n).lower)
      (fun n => (had n).upper) (fun n => (had n).calibration)
      (fun n => ⟨(had n).scale_lower, (had n).scale_upper.le⟩)
  let A := (B : ℝ) * leadingColumn alpha b a s
  let C := leadingColumn alpha b a (cyclicSucc hk s)
  have href : CoreRoundedReferenceMeasure.labelledReference ν B hk a
      (integerLeadingColumn alpha b a) s = CoreRoundedReferenceMeasure.referenceMeasure ν a A C := by
    simp only [CoreRoundedReferenceMeasure.labelledReference, integerLeadingColumn_cast, A, C]
  rw [href] at hfinite hac hmass
  let μ := fun n => profileLaw B hk r s (roundedCombination kind alpha b) a κ
    (Y (χ n)) (j (χ n)) (had (χ n))
  have hweak' : Tendsto μ atTop (𝓝 ν) := hweak
  let mean := fun n f => profileMean B hk r (roundedCombination kind alpha b) κ (Y (χ n)) f
  have hη : Tendsto (fun n => coreFiniteRootMixUpperException κ (Y (χ n))) atTop (𝓝 0) :=
    (tendsto_coreFiniteRootMixUpperException hκ0).comp (hY.comp hχ.tendsto_atTop)
  have hbound := reference_domination_of_finite_bounds (a := a) (A := A) (C := C) ha
    μ ν hweak' hW hWi mean modelConstant_nonneg
    (fun n => coreFiniteRootMixUpperException κ (Y (χ n))) hη (by
      intro R hR f K hK hf δ hδ
      exact eventually_profile_compact_bound hB hk r s kind alpha b ha ha1 halpha
        (fun n => Y (χ n)) (fun n => j (χ n)) (hY.comp hχ.tendsto_atTop)
        (fun n => had (χ n)) R hR f K hK hf δ hδ)
  refine ⟨fun n => χ n + n₀, ?_, CoreRoundedReferenceMeasure.referenceMeasure ν a A C,
    hfinite, hac, hmass, ?_⟩
  · exact fun m n hmn => Nat.add_lt_add_right (hχ hmn) n₀
  · exact hbound

end
end PrimeGapNormality.Prime.CoreRoundedModelSubsequence
