import PrimeGapNormality.Prime.CoreCalibratedModelFiniteSharp
import PrimeGapNormality.Prime.CoreCalibratedFrameMeanSharp
import PrimeGapNormality.Prime.CoreGeneralModelReference

/-!
# Coefficient-24 references with the paper's mean two

The SAME actual joint limit supplied by CoreCalibratedReference is retained.
After that limit has been selected, support-uniform qualitative calibration
and nonnegative Portmanteau sharpen its width mean from four to two. The
reference therefore has mass at most two. Compact convergence and removal
of the original-law cutoff then use the sharp finite coefficient 24.

This file ends at actual model-reference domination. The additional
sequence-comparison factor c and limiting residue factor k belong to the
downstream physical-window/residue-measure passage; no combined empirical
measure inequality is asserted here.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedModelReferenceSharp

open Filter MeasureTheory MvPolynomial CoreCyclic CoreLocalReferencePassage
open CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
  CoreCalibratedAuxiliaryFrame CoreCalibratedFrameProbability CoreCalibratedFrameLimit
  CoreCalibratedModelSubsequence CoreGeneralModelReference
open scoped Classical Topology Polynomial ENNReal NNReal BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Fixed-label model domination with coefficient 24 and mass-two reference.
The deterministic derivative/rank conditions are discharged below. -/
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
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 2 ∧
      ∀ (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) (Kf : ℝ≥0), LipschitzWith Kf f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          modelMean B hk r P w G M ω (φ n) f ≤ (24 : ℝ) * (∫ x, f x ∂σ) + ε := by
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
  have hW0 : ∀ᵐ z ∂(ν : Measure (CoreLocalReferencePassage.Joint w)), 0 ≤ CoreLocalModelPositive.jointWidth w z :=
    hν0.mono fun z hz => hz (CoreCyclicScaledSlot.centralIndex w)
  have hmeanTwo := CoreCalibratedFrameMeanSharp.coordinate_integral_le_two
    hG hκ hM hω hsum hcal (fun X => OnePoint.FiniteExterior.frameRank w (J X))
    (hq.mono fun X hx => hx.2) (criticalScale B d G J) (outer B hk r P w G M J)
    ν φ hφ.tendsto_atTop hweak (CoreCyclicScaledSlot.centralIndex w) hW0
  change Integrable (CoreLocalModelPositive.jointWidth w)
      (ν : Measure (CoreLocalReferencePassage.Joint w)) ∧
    (∫ z, CoreLocalModelPositive.jointWidth w z
      ∂(ν : Measure (CoreLocalReferencePassage.Joint w))) ≤ 2 at hmeanTwo
  have hmassTwo :
      reference w d (OnePoint.action B hk w s P) ν Set.univ ≤ ENNReal.ofReal 2 := by
    rw [reference_mass w d (OnePoint.action B hk w s P) hd ν,
      ← ofReal_integral_eq_lintegral_ofReal
        (f := CoreLocalModelPositive.jointWidth w) hWi hW0]
    exact ENNReal.ofReal_le_ofReal hmeanTwo.2
  refine ⟨φ, hφ, reference w d (OnePoint.action B hk w s P) ν, hfin, hac, hmassTwo, ?_⟩
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
    (by norm_num : (0 : ℝ) ≤ 24) (show 0 ≤ (4 : ℝ) * (2 * w + 1 : ℕ) by positivity)
    (fun n => CoreCalibratedMixtureCountException.highMass (ω (φ n)) (physicalSpan G M (φ n)))
    hhigh
  intro R hR f Kf hKf hf δ hδ
  exact hφ.tendsto_atTop.eventually
    (CoreCalibratedModelFiniteSharp.eventually_compact_bound hB hk r s P w d hw hd hG hκ hM hω hsum hcal J hJ hR f hKf hf hδ)

/-- Algebraic label selection precedes every profile and every actual law. -/
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
        IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 2 ∧
        ∀ (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) (Kf : ℝ≥0), LipschitzWith Kf f → (∀ x, 0 ≤ f x) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
            modelMean B hk r N w G M ω (φ n) f ≤ (24 : ℝ) * (∫ x, f x ∂σ) + ε := by
  let s := selectedLabel hB hk w N hroot hN hw
  refine ⟨s, ?_⟩
  intro G M κ hG hκ hM ω hω hsum hcal J hJ
  exact exists_reference_subsequence_of_rank hB hk r s N w (topDegree N) hw
    (action_totalDegree_le_topDegree B hk w s N)
    (selectedLabel_moving hB hk w N hroot hN hw)
    hG hκ hM hω hsum hcal J hJ

/-- Canonical-reserve endpoint: only actual tuple/profile/calibration data remain. -/
theorem exists_reference_subsequence
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ s i, i ∈ (N s).vars → i ≤ w)
    {κ : ℝ} (hκ : (topDegree N : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ σ : Measure (AddCircle (1 : ℝ)),
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 2 ∧
      ∀ (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) (Kf : ℝ≥0), LipschitzWith Kf f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          modelMean B hk r N w G (rank κ G) ω (φ n) f ≤
            (24 : ℝ) * (∫ x, f x ∂σ) + ε := by
  have hd := one_le_topDegree_of_rooted hk N hroot hN
  have hb : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hκp : 0 < κ := (div_pos (Nat.cast_pos.2 (show 0 < topDegree N by omega))
    (Real.log_pos hb)).trans_le hκ
  obtain ⟨s, hs⟩ := exists_rooted_model_reference hB hk r w N hroot hN hw
  obtain ⟨J, hJ⟩ := exists_admissible_ranks hB hk hd r s w hκ hG
  exact hs G (rank κ G) κ hG hκp (tendsto_rank_ratio hκp hG) ω hω hsum hcal J hJ

end
end PrimeGapNormality.Prime.CoreCalibratedModelReferenceSharp
