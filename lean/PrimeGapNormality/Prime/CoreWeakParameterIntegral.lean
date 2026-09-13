import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Weak convergence with a varying deterministic parameter

If probability measures converge weakly and a real parameter converges,
then every bounded continuous test on the product has convergent integrals.
The proof regards the deterministic parameter as a Dirac probability and
uses continuity of product probability measures.  No independence or
uniform-integrability premise is involved.
-/

namespace PrimeGapNormality.Prime.CoreWeakParameterIntegral

open Filter MeasureTheory TopologicalSpace
open scoped Topology BoundedContinuousFunction

noncomputable section

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [SecondCountableTopology α] [PseudoMetrizableSpace α]
  [OpensMeasurableSpace α]

/-- Integrating a product test against a Dirac probability in its first
coordinate is literal parameter substitution. -/
theorem integral_diracProba_prod
    (t : ℝ) (μ : ProbabilityMeasure α) (H : ℝ × α →ᵇ ℝ) :
    (∫ z, H z ∂((diracProba t).prod μ : Measure (ℝ × α))) =
      ∫ x, H (t, x) ∂(μ : Measure α) := by
  change (∫ z, H z ∂(Measure.dirac t).prod (μ : Measure α)) = _
  rw [Measure.dirac_prod,
    integral_map measurable_prodMk_left.aemeasurable
      H.continuous.aestronglyMeasurable]

/-- Joint weak convergence of the deterministic Dirac coordinate and the
random coordinate. -/
theorem tendsto_diracProba_prod
    (γ : ℕ → ℝ) (γlim : ℝ) (hγ : Tendsto γ atTop (𝓝 γlim))
    (μ : ℕ → ProbabilityMeasure α) (ν : ProbabilityMeasure α)
    (hμ : Tendsto μ atTop (𝓝 ν)) :
    Tendsto (fun n ↦ (diracProba (γ n)).prod (μ n)) atTop
      (𝓝 ((diracProba γlim).prod ν)) := by
  have hdirac : Tendsto (fun n ↦ diracProba (γ n)) atTop
      (𝓝 (diracProba γlim)) :=
    (continuous_diracProba.tendsto γlim).comp hγ
  have hpair : Tendsto (fun n ↦ (diracProba (γ n), μ n)) atTop
      (𝓝 (diracProba γlim, ν)) := by
    rw [nhds_prod_eq]
    exact hdirac.prodMk hμ
  exact (ProbabilityMeasure.continuous_prod.tendsto
    (diracProba γlim, ν)).comp hpair

/-- A bounded continuous product test may be evaluated at a converging
deterministic parameter while the probability measure converges weakly. -/
theorem tendsto_integral_of_weak_and_parameter
    (γ : ℕ → ℝ) (γlim : ℝ) (hγ : Tendsto γ atTop (𝓝 γlim))
    (μ : ℕ → ProbabilityMeasure α) (ν : ProbabilityMeasure α)
    (hμ : Tendsto μ atTop (𝓝 ν))
    (H : ℝ × α →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, H (γ n, x) ∂(μ n : Measure α)) atTop
      (𝓝 (∫ x, H (γlim, x) ∂(ν : Measure α))) := by
  have hprod := tendsto_diracProba_prod γ γlim hγ μ ν hμ
  have hint :=
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction H).tendsto
      ((diracProba γlim).prod ν)).comp hprod
  simpa only [Function.comp_def, integral_diracProba_prod] using hint

end

end PrimeGapNormality.Prime.CoreWeakParameterIntegral
