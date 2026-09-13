import PrimeGapNormality.Prime.CoreCalibratedFrameProbability
import PrimeGapNormality.Prime.CoreLocalReferencePassage

/-!
# Fixed polynomial references for arbitrary calibrated mixtures

The joint law below is the actual completed auxiliary mixture, not a
replacement independent frame law. The formal top-action label is chosen
before the profile, ranks, outer phases, joint limit and all tests. Its
nonzero derivative and the proved frame-marginal AC imply fibre
nonconstancy. The reference has finite mass at most four; no bounded density
is asserted. Converting original model means into these reference integrals
is the remaining resampling consumer, not a hypothesis of this construction.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedReference

open Filter MeasureTheory MvPolynomial CoreCyclic CoreLocalReferencePassage
open CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
open scoped Topology ENNReal Polynomial BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Actual joint extraction followed by the actual polynomial-image
reference. The only non-probabilistic nondegeneracy input is a proved
nonzero formal moving derivative. -/
theorem exists_reference
    (w d : ℕ) (p : OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (hpvars : ∀ i ∈ p.vars, -(w : ℤ) - 1 ≤ i ∧ i ≤ (w : ℤ))
    (hp : pderiv (-1) (homogeneousComponent d p) ≠ 0)
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G)
    (q : ℕ → Fin (2 * w + 1) → ℕ)
    (hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧ ∀ i, q X i + 1 < M X)
    (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ))) {C : ℝ}
    (hθ : ∀ᶠ X in atTop, θ X ∈ Set.Icc 1 C) :
    ∃ ν : ProbabilityMeasure (Joint w), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => CoreCalibratedFrameProbability.profileLaw G M ω q θ O (φ n))
        atTop (𝓝 ν) ∧
      (CoreJointFrameLimit.frameMarginal ν : Measure (Frame w)) ≪ volume ∧
      (∀ᵐ z ∂(ν : Measure (Joint w)), ∀ i, 0 ≤ CoreJointFrameLimit.frame z i) ∧
      (∀ᵐ z ∂(ν : Measure (Joint w)), CoreJointFrameLimit.scale z ∈ Set.Icc 1 C) ∧
      Integrable (CoreLocalModelPositive.jointWidth w) (ν : Measure (Joint w)) ∧
      IsFiniteMeasure (reference w d p ν) ∧ reference w d p ν ≪ volume ∧
      reference w d p ν Set.univ ≤ ENNReal.ofReal 4 ∧
      (∀ (R : ℝ) (hR : 0 ≤ R) (f : (AddCircle (1 : ℝ)) →ᵇ ℝ),
        Tendsto (fun n => ∫ z,
          CoreLocalModelPositive.compactInsertionTest hR w d p hd (G (φ n))⁻¹ f z
            ∂(CoreCalibratedFrameProbability.profileLaw G M ω q θ O (φ n) : Measure (Joint w)))
          atTop (𝓝 (∫ z, CoreLocalModelPositive.compactInsertionTest hR w d p hd 0 f z
            ∂(ν : Measure (Joint w))))) ∧
      (∀ (R : ℝ) (hR : 0 ≤ R) (f : (AddCircle (1 : ℝ)) →ᵇ ℝ), (∀ x, 0 ≤ f x) →
        (∫ z, CoreLocalModelPositive.compactInsertionTest hR w d p hd 0 f z
          ∂(ν : Measure (Joint w))) ≤ ∫ x, f x ∂reference w d p ν) := by
  obtain ⟨ν, φ, hφ, hweak, hνac, hν0, hνθ, hWi, hWmean⟩ :=
    CoreCalibratedFrameProbability.exists_joint_limit hG hκ hM hω hsum hcal q hq θ O hθ
      (CoreCyclicScaledSlot.centralIndex w)
  change Integrable (CoreLocalModelPositive.jointWidth w)
    (ν : Measure (Joint w)) at hWi
  change (∫ z, CoreLocalModelPositive.jointWidth w z
    ∂(ν : Measure (Joint w))) ≤ 4 at hWmean
  have hW0 : ∀ᵐ z ∂(ν : Measure (Joint w)), 0 ≤ CoreLocalModelPositive.jointWidth w z :=
    hν0.mono fun z hz => hz (CoreCyclicScaledSlot.centralIndex w)
  have hWbound : (∫⁻ z, ENNReal.ofReal (CoreLocalModelPositive.jointWidth w z)
      ∂(ν : Measure (Joint w))) ≤ ENNReal.ofReal 4 := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (f := CoreLocalModelPositive.jointWidth w) hWi hW0]
    exact ENNReal.ofReal_le_ofReal hWmean
  have hWfin := lt_of_le_of_lt hWbound ENNReal.ofReal_lt_top
  refine ⟨ν, φ, hφ, hweak, hνac, hν0, hνθ, hWi,
    reference_isFinite w d p hd ν hWfin,
    reference_absolutelyContinuous w d p hd hpvars hp ν hνac
      (hνθ.mono fun z hz => hz.1), ?_, ?_, ?_⟩
  · rw [reference_mass w d p hd ν]
    exact hWbound
  · intro R hR f
    have hGφ : Tendsto (fun n => G (φ n)) atTop atTop := by
      simpa only [Function.comp_def] using hG.comp hφ.tendsto_atTop
    exact compact_integrals_tendsto w d p hd (fun n => G (φ n))
      hGφ
      (fun n => CoreCalibratedFrameProbability.profileLaw G M ω q θ O (φ n))
      ν hweak hR f
  · intro R hR f hf
    exact compact_integral_le_reference w d p hd ν hW0 hWi hR f hf

/-- Choose the genuine nondegenerate local label before every arbitrary
calibrated profile and before its joint law. This final reference supplier
has no nonzero-coefficient, frame-AC, tightness or moment oracle. -/
theorem exists_rooted_reference
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w) :
    ∃ s : Fin k, ∀ (G : ℕ → ℝ) (M : ℕ → ℕ) (κ : ℝ),
      Tendsto G atTop atTop → 0 < κ →
      Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ) →
      ∀ (ω : ℕ → ℕ → ℝ), (∀ X y, 0 ≤ ω X y) →
      (∀ X, ∑' y, ω X y = 1) → UniformCalibration ω G →
      ∀ (q : ℕ → Fin (2 * w + 1) → ℕ),
      (∀ᶠ X in atTop, Function.Injective (q X) ∧ ∀ i, q X i + 1 < M X) →
      ∀ (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ))) (C : ℝ),
      (∀ᶠ X in atTop, θ X ∈ Set.Icc 1 C) →
      ∃ ν : ProbabilityMeasure (Joint w), ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
        Tendsto (fun n => CoreCalibratedFrameProbability.profileLaw G M ω q θ O (φ n))
          atTop (𝓝 ν) ∧
        IsFiniteMeasure (reference w (topDegree N) (OnePoint.action B hk w s N) ν) ∧
        reference w (topDegree N) (OnePoint.action B hk w s N) ν ≪ volume ∧
        reference w (topDegree N) (OnePoint.action B hk w s N) ν Set.univ ≤ ENNReal.ofReal 4 ∧
        (∀ (R : ℝ) (hR : 0 ≤ R) (f : (AddCircle (1 : ℝ)) →ᵇ ℝ), (∀ x, 0 ≤ f x) →
          (∫ z, CoreLocalModelPositive.compactInsertionTest hR w (topDegree N)
            (OnePoint.action B hk w s N) (action_totalDegree_le_topDegree B hk w s N) 0 f z
              ∂(ν : Measure (Joint w))) ≤
          ∫ x, f x ∂reference w (topDegree N) (OnePoint.action B hk w s N) ν) := by
  let s := selectedLabel hB hk w N hroot hN hw
  refine ⟨s, ?_⟩
  intro G M κ hG hκ hM ω hω hsum hcal q hq θ O C hθ
  obtain ⟨ν, φ, hφ, hweak, hνac, hν0, hνθ, hWi, hfin, hac, hmass, hconv, hdom⟩ :=
    exists_reference w (topDegree N) (OnePoint.action B hk w s N)
      (action_totalDegree_le_topDegree B hk w s N)
      (fun i hi => OnePoint.FiniteExterior.action_vars_bounds B hk w s N hw hi)
      (selectedLabel_moving hB hk w N hroot hN hw)
      hG hκ hM hω hsum hcal q hq θ O hθ
  exact ⟨ν, φ, hφ, hweak, hfin, hac, hmass, hdom⟩

end
end PrimeGapNormality.Prime.CoreCalibratedReference
