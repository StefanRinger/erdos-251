import PrimeGapNormality.Prime.CoreDigitalCharacterMean
import PrimeGapNormality.Prime.Fourier
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-! Fourier tests determine weak convergence of actual circle probability
measures. The final specialization is the existing Weyl criterion, not a
new equidistribution assumption. -/

namespace PrimeGapNormality.Prime.CoreWeylNormality

open Set Filter MeasureTheory BoundedContinuousFunction
open scoped Topology BoundedContinuousFunction

noncomputable section

private def boundedFourierAlgebra :
    StarSubalgebra ℂ (AddCircle (1 : ℝ) →ᵇ ℂ) :=
  (fourierSubalgebra (T := (1 : ℝ))).comap (toContinuousMapStarₐ ℂ)

private theorem boundedFourierAlgebra_map :
    boundedFourierAlgebra.map (toContinuousMapStarₐ ℂ) =
      fourierSubalgebra (T := (1 : ℝ)) := by
  ext f
  constructor
  · intro hf
    obtain ⟨g, hg, rfl⟩ := StarSubalgebra.mem_map.1 hf
    exact hg
  · intro hf
    exact StarSubalgebra.mem_map.2 ⟨mkOfCompact f, hf, rfl⟩

/-- All circle Fourier integrals suffice for weak convergence. Tightness
is automatic on the compact circle; finite Fourier sums are the existing
point-separating star subalgebra. -/
theorem tendsto_of_fourier_integrals
    (μ : ℕ → ProbabilityMeasure (AddCircle (1 : ℝ)))
    (ν : ProbabilityMeasure (AddCircle (1 : ℝ)))
    (hfourier : ∀ q : ℤ,
      Tendsto (fun N ↦ ∫ x, fourier q x ∂(μ N : Measure (AddCircle (1 : ℝ))))
        atTop (𝓝 (∫ x, fourier q x ∂(ν : Measure (AddCircle (1 : ℝ)))))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℂ
    IsTightMeasureSet.of_compactSpace
    (A := boundedFourierAlgebra)
    (by rw [boundedFourierAlgebra_map]; exact fourierSubalgebra_separatesPoints)
  intro g hg
  have hspan : g.toContinuousMap ∈
      Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) := by
    rw [← fourierSubalgebra_coe]
    exact hg
  suffices ∀ f : C(AddCircle (1 : ℝ), ℂ),
      f ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) →
      Tendsto (fun N ↦ ∫ x, f x ∂(μ N : Measure (AddCircle (1 : ℝ))))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure (AddCircle (1 : ℝ))))) from
    this g.toContinuousMap hspan
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨q, rfl⟩ := hf
    exact hfourier q
  | zero => simpa only [ContinuousMap.zero_apply, integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0))
  | add f g hf hg ihf ihg =>
    have hadd (m : ProbabilityMeasure (AddCircle (1 : ℝ))) :
        (∫ x, f x + g x ∂(m : Measure (AddCircle (1 : ℝ)))) =
          (∫ x, f x ∂(m : Measure (AddCircle (1 : ℝ)))) +
            ∫ x, g x ∂(m : Measure (AddCircle (1 : ℝ))) :=
      integral_add (mkOfCompact f |>.integrable _) (mkOfCompact g |>.integrable _)
    simp_rw [ContinuousMap.add_apply, hadd]
    exact ihf.add ihg
  | smul c f hf ih =>
    simpa only [ContinuousMap.smul_apply, integral_smul] using ih.const_smul c

def orbit (B : ℕ) (α : ℝ) (n : ℕ) : AddCircle (1 : ℝ) :=
  (((B : ℝ) ^ n * α : ℝ) : AddCircle (1 : ℝ))

def empirical (B : ℕ) (α : ℝ) (N : ℕ) : ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  coreDigitalWindowMeasure (orbit B α) 0 N

theorem fourier_orbit (B : ℕ) (α : ℝ) (q : ℤ) (n : ℕ) :
    fourier q (orbit B α n) = e ((q : ℝ) * (B : ℝ) ^ n * α) := by
  rw [orbit, fourier_coe_apply]
  simp only [e, Complex.ofReal_one, div_one, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

theorem empirical_fourier_integral (B : ℕ) (α : ℝ) (q : ℤ) {N : ℕ} (hN : 0 < N) :
    (∫ x, fourier q x ∂(empirical B α N : Measure (AddCircle (1 : ℝ)))) =
      (∑ n ∈ Finset.range N, e ((q : ℝ) * (B : ℝ) ^ n * α)) / (N : ℂ) := by
  have h := coreDigitalWindowMeasure_integral_complex (orbit B α) 0 hN
    (mkOfCompact (fourier q))
  simpa only [empirical, mkOfCompact_apply, Nat.zero_add, fourier_orbit] using h

/-- The genuine Weyl criterion gives weak convergence of the actual
finite orbit measures. The zero-length convention is discarded eventually. -/
theorem empirical_tendsto_of_weyl {B : ℕ} {α : ℝ} (hW : weylCriterion B α) :
    Tendsto (empirical B α) atTop (𝓝 coreCircleVolume) := by
  apply tendsto_of_fourier_integrals
  intro q
  by_cases hq : q = 0
  · subst q
    simpa only [fourier_zero, integral_const, probReal_univ, one_smul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (𝓝 1))
  · have h := hW q hq
    have hzero : (∫ x, fourier q x ∂(coreCircleVolume : Measure (AddCircle (1 : ℝ)))) = 0 :=
      coreDigital_nonzero_character_integral hq
    rw [hzero]
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (empirical_fourier_integral B α q hN).symm

end

end PrimeGapNormality.Prime.CoreWeylNormality
