import PrimeGapNormality.Prime.CoreCalibratedModelFinite
import PrimeGapNormality.Prime.CoreCalibratedReference

/-!
# Actual arbitrary-mixture model domination by one fixed reference

The emission horizon is M-w, while the original survivor count is tested
against M. The explicit critical-rank conditions are deterministic: they
must later be supplied from a canonical positive square-root reserve, not
deduced merely from M/log G → κ at the endpoint. There is no assumed slot,
mean, frame-limit or reference domination in the final rooted theorem.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedModelSubsequence

open Filter MeasureTheory MvPolynomial CoreCyclic CoreLocalReferencePassage
open CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
  CoreCalibratedAuxiliaryFrame CoreCalibratedFrameProbability CoreCalibratedFrameLimit
  CoreCalibratedModelFinite
open scoped Classical Topology Polynomial ENNReal NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def criticalScale (B d : ℕ) (G : ℕ → ℝ) (J : ℕ → ℕ) (X : ℕ) : ℝ :=
  G X ^ d / (B : ℝ) ^ (J X + 1)

def RankAdmissible (B : ℕ) {k : ℕ} (hk : 0 < k) (r s : Fin k)
    (w d : ℕ) (G : ℕ → ℝ) (M J : ℕ → ℕ) (X : ℕ) : Prop :=
  w + 1 ≤ J X ∧ J X + w < M X ∧ phaseAt hk r (J X - 1) = s ∧
    criticalScale B d G J X ∈ Set.Icc 1 ((B : ℝ) ^ k)

def outer (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) (P : PeriodicLocal k)
    (w : ℕ) (G : ℕ → ℝ) (M J : ℕ → ℕ) (X : ℕ) : Finset ℕ → (AddCircle (1 : ℝ)) :=
  CoreLocalModelMixture.outerMap B hk r P (M X - w) w (J X) (physicalSpan G M X)

def modelMean (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) (P : PeriodicLocal k)
    (w : ℕ) (G : ℕ → ℝ) (M : ℕ → ℕ) (ω : ℕ → ℕ → ℝ)
    (X : ℕ) (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) : ℝ :=
  mean (ω X) (physicalSpan G M X) (M X)
    (CoreLocalModelPositive.actualTest B hk r P (M X - w) f)

def modelLaw (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) (P : PeriodicLocal k)
    (w d : ℕ) (G : ℕ → ℝ) (M J : ℕ → ℕ) (ω : ℕ → ℕ → ℝ)
    (X : ℕ) : ProbabilityMeasure (CoreJointFrameLimit.Joint (2 * w + 1)) :=
  profileLaw G M ω (fun n => OnePoint.FiniteExterior.frameRank w (J n))
    (criticalScale B d G J) (outer B hk r P w G M J) X

/-- The actual mixture compact-test estimate. All finite-support,
retention and Selberg inputs are discharged from the stated profile. -/
theorem eventually_compact_bound
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (w d : ℕ)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (OnePoint.action B hk w s P).totalDegree ≤ d)
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G)
    (J : ℕ → ℕ) (hJ : ∀ᶠ X in atTop, RankAdmissible B hk r s w d G M J X)
    {R : ℝ} (hR : 0 < R) (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) {Kf : ℝ≥0}
    (hKf : LipschitzWith Kf f) (hf : ∀ x, 0 ≤ f x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X in atTop, modelMean B hk r P w G M ω X f ≤
      modelConstant * (∫ z,
        CoreLocalModelPositive.compactInsertionTest hR.le w d (OnePoint.action B hk w s P) hd (G X)⁻¹ f z
          ∂(modelLaw B hk r P w d G M J ω X : Measure (CoreLocalReferencePassage.Joint w))) +
      (4 * (2 * w + 1 : ℕ)) * ‖f‖ / R +
      CoreCalibratedMixtureCountException.highMass (ω X) (physicalSpan G M X) * ‖f‖ +
      modelConstant * δ := by
  filter_upwards [hG.eventually (eventually_mixture hB hk r s P w d hw hd hR f hKf hf hδ),
    eventually_profile_data hG hκ hM hω hsum hcal,
    eventually_scaled_retention hG hκ hM hcal, hJ] with X hfinite hdata hret hj
  have hweights : Weights (ω X) (physicalSpan G M X) := ⟨hω X, hdata.2.1, hdata.2.2.2⟩
  have hs : ∀ y, ω X y ≠ 0 →
      0 < lateRetention (physicalSpan G M X) y ∧
      lateRetention (physicalSpan G M X) y ≤ (1 : ℝ) / 4 ∧
      lateRetention (physicalSpan G M X) y * G X / Real.log (G X) ≤ 6 / eulerProdLowerConst ∧
      CoreRoughSyntheticScale.roughGapScale y / G X ≤ 2 := by
    intro y hy
    have hh := hret.2.2.2 y (lt_of_le_of_ne (hω X y) (Ne.symm hy))
    exact ⟨hh.2.1, hh.2.2.1, hh.2.2.2, hdata.2.2.1 y hy⟩
  have hh := hfinite (M X - w) (J X) (physicalSpan G M X) (M X) (ω X)
    hweights hj.1 (by have hh := hj.2.1; omega) hj.2.1 hj.2.2.1
    hret.1 hret.2.2.1 hs hj.2.2.2.1 hj.2.2.2.2
  exact hh.trans_eq (by
    dsimp only [modelLaw, profileLaw, outer, criticalScale, Function.comp_apply]
    ring)

/-- Fixed-label actual model endpoint. The formal derivative assumption
is algebraic and is removed by the rooted-tuple theorem below. -/
theorem exists_reference_subsequence_of_rank
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r s : Fin k)
    (P : PeriodicLocal k) (w d : ℕ)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (OnePoint.action B hk w s P).totalDegree ≤ d)
    (hp : pderiv (-1) (homogeneousComponent d (OnePoint.action B hk w s P)) ≠ 0)
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G)
    (J : ℕ → ℕ) (hJ : ∀ᶠ X in atTop, RankAdmissible B hk r s w d G M J X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ σ : Measure (AddCircle (1 : ℝ)),
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 4 ∧
      ∀ (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) (Kf : ℝ≥0), LipschitzWith Kf f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          modelMean B hk r P w G M ω (φ n) f ≤ modelConstant * (∫ x, f x ∂σ) + ε := by
  have hq : ∀ᶠ X in atTop,
      Function.Injective (OnePoint.FiniteExterior.frameRank w (J X)) ∧
        ∀ i, OnePoint.FiniteExterior.frameRank w (J X) i + 1 < M X := by
    filter_upwards [hJ] with X hx
    exact ⟨OnePoint.FiniteExterior.frameRank_injective w (J X) hx.1,
      OnePoint.FiniteExterior.frameRank_valid hx.1 hx.2.1⟩
  have hθ : ∀ᶠ X in atTop, criticalScale B d G J X ∈ Set.Icc 1 ((B : ℝ) ^ k) :=
    hJ.mono fun X hx => hx.2.2.2
  obtain ⟨ν, φ, hφ, hweak, hνac, hν0, hνθ, hWi, hfin, hac, hmass, hconv, hdom⟩ :=
    CoreCalibratedReference.exists_reference w d (OnePoint.action B hk w s P) hd
      (fun i hi => OnePoint.FiniteExterior.action_vars_bounds B hk w s P hw hi) hp
      hG hκ hM hω hsum hcal (fun X => OnePoint.FiniteExterior.frameRank w (J X)) hq
      (criticalScale B d G J) (outer B hk r P w G M J) hθ
  refine ⟨φ, hφ, reference w d (OnePoint.action B hk w s P) ν, hfin, hac, hmass, ?_⟩
  have hGφ : Tendsto (fun n => G (φ n)) atTop atTop := by
    simpa only [Function.comp_def] using hG.comp hφ.tendsto_atTop
  have hhigh : Tendsto (fun n =>
      CoreCalibratedMixtureCountException.highMass (ω (φ n))
        (physicalSpan G M (φ n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (CoreCalibratedMixtureCountException.tendsto_mixture_high_zero
        hG hκ hM hω hsum hcal).comp hφ.tendsto_atTop
  have hweakModel : Tendsto
      (fun n => modelLaw B hk r P w d G M J ω (φ n)) atTop (𝓝 ν) := by
    change Tendsto (fun n => CoreCalibratedFrameProbability.profileLaw G M ω
      (fun X => OnePoint.FiniteExterior.frameRank w (J X))
      (criticalScale B d G J) (outer B hk r P w G M J) (φ n)) atTop (𝓝 ν)
    exact hweak
  apply reference_domination_of_finite_compact_bounds w d (OnePoint.action B hk w s P) hd
    (fun n => G (φ n)) hGφ
    (fun n => modelLaw B hk r P w d G M J ω (φ n)) ν hweakModel
    (hν0.mono fun z hz => hz (CoreCyclicScaledSlot.centralIndex w)) hWi
    (fun n f => modelMean B hk r P w G M ω (φ n) f)
    modelConstant_nonneg (show 0 ≤ (4 : ℝ) * (2 * w + 1 : ℕ) by positivity)
    (fun n => CoreCalibratedMixtureCountException.highMass (ω (φ n)) (physicalSpan G M (φ n)))
    hhigh
  intro R hR f Kf hKf hf δ hδ
  exact hφ.tendsto_atTop.eventually
    (eventually_compact_bound hB hk r s P w d hw hd hG hκ hM hω hsum hcal J hJ hR f hKf hf hδ)

/-- Rooted nonzero normal-form endpoint. Label selection precedes the
profile and weights. The only remaining rank assumptions describe the
literal deterministic slot; no probabilistic or analytic model supplier
is exposed. -/
theorem exists_rooted_model_reference
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ s i, i ∈ (N s).vars → i ≤ w) :
    ∃ s : Fin k, ∀ (G : ℕ → ℝ) (M : ℕ → ℕ) (κ : ℝ),
      Tendsto G atTop atTop → 0 < κ →
      Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ) →
      ∀ (ω : ℕ → ℕ → ℝ), (∀ X y, 0 ≤ ω X y) →
      (∀ X, ∑' y, ω X y = 1) → UniformCalibration ω G →
      ∀ (J : ℕ → ℕ),
      (∀ᶠ X in atTop, RankAdmissible B hk r s w (topDegree N) G M J X) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ σ : Measure (AddCircle (1 : ℝ)),
        IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 4 ∧
        ∀ (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) (Kf : ℝ≥0), LipschitzWith Kf f → (∀ x, 0 ≤ f x) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
            modelMean B hk r N w G M ω (φ n) f ≤ modelConstant * (∫ x, f x ∂σ) + ε := by
  let s := selectedLabel hB hk w N hroot hN hw
  refine ⟨s, ?_⟩
  intro G M κ hG hκ hM ω hω hsum hcal J hJ
  exact exists_reference_subsequence_of_rank hB hk r s N w (topDegree N) hw
    (action_totalDegree_le_topDegree B hk w s N)
    (selectedLabel_moving hB hk w N hroot hN hw)
    hG hκ hM hω hsum hcal J hJ

end
end PrimeGapNormality.Prime.CoreCalibratedModelSubsequence
