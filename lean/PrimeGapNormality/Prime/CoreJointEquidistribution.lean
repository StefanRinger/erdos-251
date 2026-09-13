import PrimeGapNormality.Prime.CoreCircleDigitCylinders
import PrimeGapNormality.Prime.JointWeyl
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Joint Weyl gives actual finite-torus equidistribution

Actual uniform empirical probabilities of the specified coordinate orbit
converge weakly to product circle volume. The finite index type may be
empty. No additional independence or arithmetic hypothesis occurs.
-/

namespace PrimeGapNormality.Prime.CoreJointEquidistribution

open Set Filter MeasureTheory Finset BoundedContinuousFunction
open scoped Topology ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

abbrev Torus (I : Type*) := I → AddCircle (1 : ℝ)

local instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp⟩

def torusVolume (I : Type*) [Fintype I] : ProbabilityMeasure (Torus I) :=
  ⟨volume, inferInstance⟩

private def boundedFourierAlgebra (I : Type*) [Fintype I] :
    StarSubalgebra ℂ (Torus I →ᵇ ℂ) :=
  (UnitAddTorus.mFourierSubalgebra I).comap (toContinuousMapStarₐ ℂ)

private theorem boundedFourierAlgebra_map (I : Type*) [Fintype I] :
    (boundedFourierAlgebra I).map (toContinuousMapStarₐ ℂ) =
      UnitAddTorus.mFourierSubalgebra I := by
  ext f
  constructor
  · intro hf
    obtain ⟨g, hg, rfl⟩ := StarSubalgebra.mem_map.1 hf
    exact hg
  · intro hf
    exact StarSubalgebra.mem_map.2 ⟨mkOfCompact f, hf, rfl⟩

/-- Fourier integrals determine weak convergence on the finite torus. -/
theorem tendsto_of_fourier_integrals {I : Type*} [Fintype I]
    (μ : ℕ → ProbabilityMeasure (Torus I)) (ν : ProbabilityMeasure (Torus I))
    (hf : ∀ t : I → ℤ,
      Tendsto (fun n => ∫ x, UnitAddTorus.mFourier t x ∂(μ n : Measure (Torus I)))
        atTop (𝓝 (∫ x, UnitAddTorus.mFourier t x ∂(ν : Measure (Torus I))))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℂ
    IsTightMeasureSet.of_compactSpace (A := boundedFourierAlgebra I)
    (by rw [boundedFourierAlgebra_map]; exact UnitAddTorus.mFourierSubalgebra_separatesPoints)
  intro g hg
  have hspan : g.toContinuousMap ∈
      Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := I))) := by
    rw [← UnitAddTorus.mFourierSubalgebra_coe]
    exact hg
  suffices ∀ f : C(Torus I, ℂ),
      f ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := I))) →
      Tendsto (fun n => ∫ x, f x ∂(μ n : Measure (Torus I))) atTop
        (𝓝 (∫ x, f x ∂(ν : Measure (Torus I)))) from this g.toContinuousMap hspan
  intro f hf'
  induction hf' using Submodule.span_induction with
  | mem f hm =>
    obtain ⟨t, rfl⟩ := hm
    exact hf t
  | zero => simpa only [ContinuousMap.zero_apply, integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  | add f g hmf hmg ihf ihg =>
    have hadd (m : ProbabilityMeasure (Torus I)) :
        (∫ x, f x + g x ∂(m : Measure (Torus I))) =
          (∫ x, f x ∂(m : Measure (Torus I))) + ∫ x, g x ∂(m : Measure (Torus I)) :=
      integral_add (mkOfCompact f |>.integrable _) (mkOfCompact g |>.integrable _)
    simp_rw [ContinuousMap.add_apply, hadd]
    exact ihf.add ihg
  | smul c f hmf ih =>
    simpa only [ContinuousMap.smul_apply, integral_smul] using ih.const_smul c

def orbit {I : Type*} (b : I → ℕ) (θ : I → ℝ) (n : ℕ) : Torus I :=
  fun i => (((b i : ℝ) ^ n * θ i : ℝ) : AddCircle (1 : ℝ))

/-- Zero sample size is a Dirac mass; positive sizes are the actual
uniform samples of indices 0 through N-1. -/
def empirical {I : Type*} [Fintype I] (b : I → ℕ) (θ : I → ℝ) (N : ℕ) :
    ProbabilityMeasure (Torus I) :=
  if h : 0 < N then
    letI : Nonempty (Fin N) := ⟨⟨0, h⟩⟩
    ⟨((PMF.uniformOfFintype (Fin N)).map (fun i : Fin N => orbit b θ i)).toMeasure,
      inferInstance⟩
  else ⟨(PMF.pure (orbit b θ 0)).toMeasure, inferInstance⟩

theorem empirical_integral {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : I → ℕ) (θ : I → ℝ) {N : ℕ} (hN : 0 < N) (f : Torus I →ᵇ E) :
    (∫ x, f x ∂(empirical b θ N : Measure (Torus I))) =
      (N : ℝ)⁻¹ • ∑ n ∈ range N, f (orbit b θ n) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hm : Measurable (fun i : Fin N => orbit b θ i) := measurable_of_finite _
  have hmeasure : (empirical b θ N : Measure (Torus I)) =
      ((PMF.uniformOfFintype (Fin N)).map (fun i : Fin N => orbit b θ i)).toMeasure := by
    unfold empirical
    rw [dif_pos hN]
    rfl
  rw [hmeasure, ← PMF.toMeasure_map (fun i : Fin N => orbit b θ i)
    (PMF.uniformOfFintype (Fin N)) hm, integral_map hm.aemeasurable
    f.continuous.aestronglyMeasurable, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← Finset.smul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun n => f (orbit b θ n)) N]

private theorem e_sum {I : Type*} (s : Finset I) (f : I → ℝ) :
    e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [e]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, ← ih]
    simp only [e, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem fourier_orbit {I : Type*} [Fintype I]
    (b : I → ℕ) (θ : I → ℝ) (t : I → ℤ) (n : ℕ) :
    UnitAddTorus.mFourier t (orbit b θ n) =
      e (∑ i, (t i : ℝ) * (b i : ℝ) ^ n * θ i) := by
  change (∏ i, fourier (t i) (CoreWeylNormality.orbit (b i) (θ i) n)) = _
  simp_rw [CoreWeylNormality.fourier_orbit]
  exact (e_sum univ _).symm

theorem nonzero_fourier_integral {I : Type*} [Fintype I]
    (t : I → ℤ) (ht : ∃ i, t i ≠ 0) :
    (∫ x, UnitAddTorus.mFourier t x ∂(torusVolume I : Measure (Torus I))) = 0 := by
  change (∫ x : Torus I, ∏ i, fourier (t i) (x i)) = 0
  rw [integral_fintype_prod_volume_eq_prod]
  obtain ⟨i, hi⟩ := ht
  exact Finset.prod_eq_zero (mem_univ i) (coreDigital_nonzero_character_integral hi)

/-- The existing integer-frequency joint Weyl predicate implies weak
convergence of the exact empirical orbit law to product circle volume. -/
theorem empirical_tendsto_of_jointWeyl {I : Type*} [Fintype I] [DecidableEq I]
    {b : I → ℕ} {θ : I → ℝ} (h : JointWeyl b θ) :
    Tendsto (empirical b θ) atTop (𝓝 (torusVolume I)) := by
  apply tendsto_of_fourier_integrals
  intro t
  by_cases ht : ∃ i, t i ≠ 0
  · rw [nonzero_fourier_integral t ht]
    apply (h t ht).congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    simpa only [mkOfCompact_apply, fourier_orbit, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_natCast, div_eq_mul_inv, mul_comm] using
      (empirical_integral b θ hN (mkOfCompact (UnitAddTorus.mFourier t))).symm
  · have ht0 : t = 0 := by
      funext i
      exact not_ne_iff.mp (fun hi => ht ⟨i, hi⟩)
    subst t
    simpa only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, integral_const,
      probReal_univ, one_smul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))

/-- Literal real continuous-test averages on the specified joint orbit. -/
theorem continuous_test_tendsto_of_jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I] {b : I → ℕ} {θ : I → ℝ}
    (h : JointWeyl b θ) (f : C(Torus I, ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f (orbit b θ n)) / N) atTop
      (𝓝 (∫ x : Torus I, f x)) := by
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (empirical_tendsto_of_jointWeyl h)) (mkOfCompact f)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [empirical_integral b θ hN (mkOfCompact f)]
  simp only [mkOfCompact_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

end
end PrimeGapNormality.Prime.CoreJointEquidistribution
