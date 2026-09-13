import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.Extreme
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

/-!
# The invariant-limit consumer of the frozen digital argument

This is the last identification step of Lemma `lem:rigidity` and Step 4
of Proposition `prop:localconsumer` in the 10 September 2026 frozen paper.
Actual model domination is supplied upstream; it is not established here.
The orbit-window theorem below derives invariance from the exact recurrence
and a vanishing boundary/length ratio, rather than assuming invariance.
-/

open MeasureTheory Filter Finset
open scoped Topology ENNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

local instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp⟩

/-- An absolutely continuous invariant probability for multiplication by an
integer at least two is normalized Lebesgue measure. -/
theorem coreDigital_eq_volume_of_invariant_ac {C : ℕ} (hC : 2 ≤ C)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (fun x : AddCircle (1 : ℝ) => C • x) μ μ)
    (hac : μ ≪ volume) : μ = volume := by
  exact (AddCircle.ergodic_nsmul (T := (1 : ℝ)) hC).eq_of_absolutelyContinuous
    hinv hac

/-- In particular the direct linear estimate `μ ≤ 72*k*c*volume` is enough;
no model Fourier-vanishing hypothesis is required. -/
theorem coreDigital_eq_volume_of_invariant_domination {C : ℕ} (hC : 2 ≤ C)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (fun x : AddCircle (1 : ℝ) => C • x) μ μ)
    {A : ℝ≥0∞} (hdom : μ ≤ A • volume) : μ = volume :=
  coreDigital_eq_volume_of_invariant_ac hC μ hinv
    (Measure.absolutelyContinuous_of_le_smul hdom)

/-- A window average of a circle orbit; zero length uses real division by zero. -/
noncomputable def coreDigitalWindowAverage (u : ℕ → AddCircle (1 : ℝ))
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (a N : ℕ) : ℝ :=
  (∑ i ∈ range N, f (u (a + i))) / (N : ℝ)

/-- The exact recurrence telescopes the defect to two endpoints. -/
theorem coreDigitalWindowAverage_defect {C : ℕ}
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (a N : ℕ) :
    coreDigitalWindowAverage u
        (f.compContinuous ⟨fun x => C • x, continuous_nsmul C⟩) a N -
      coreDigitalWindowAverage u f a N =
        (f (u (a + N)) - f (u a)) / (N : ℝ) := by
  unfold coreDigitalWindowAverage
  rw [← sub_div, ← sum_sub_distrib]
  congr 1
  have hs : ∀ i, f (C • u (a + i)) = f (u (a + (i + 1))) := by
    intro i
    rw [← hu, Nat.add_assoc]
  simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, hs]
  simpa using (sum_range_sub (fun i => f (u (a + i))) N)

/-- Uniform boundary estimate, independent of the starting point. -/
theorem coreDigitalWindowAverage_defect_bound {C : ℕ}
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (a N : ℕ) :
    ‖coreDigitalWindowAverage u
        (f.compContinuous ⟨fun x => C • x, continuous_nsmul C⟩) a N -
      coreDigitalWindowAverage u f a N‖ ≤ 2 * ‖f‖ / (N : ℝ) := by
  rw [coreDigitalWindowAverage_defect u hu, norm_div, Real.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  calc
    ‖f (u (a + N)) - f (u a)‖ ≤ ‖f (u (a + N))‖ + ‖f (u a)‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
    _ = 2 * ‖f‖ := by ring

/-- Any probability limit of growing windows of an exact circle orbit is
invariant. The limit hypothesis is the usual continuous-test formulation
of weak convergence, evaluated on the actual finite orbit averages. -/
theorem coreDigital_invariant_of_window_limit {C : ℕ}
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hlim : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a j) (N j)) atTop
        (𝓝 (∫ x, f x ∂μ))) :
    MeasurePreserving (fun x : AddCircle (1 : ℝ) => C • x) μ μ := by
  have hc : Continuous (fun x : AddCircle (1 : ℝ) => C • x) :=
    continuous_nsmul C
  refine ⟨hc.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hc.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  let g := f.compContinuous ⟨fun x => C • x, hc⟩
  have hzero : Tendsto (fun j =>
      coreDigitalWindowAverage u g (a j) (N j) -
        coreDigitalWindowAverage u f (a j) (N j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => coreDigitalWindowAverage_defect_bound u hu f (a j) (N j))
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN)
  have heq := tendsto_nhds_unique ((hlim g).sub (hlim f)) hzero
  exact sub_eq_zero.mp heq

/-- The model's absolute-continuity output closes the identification of every
growing-window orbit limit. Supplying that output is the finite insertion /
physical-gap-mean task, separate from the arithmetic pattern comparison. -/
theorem coreDigital_window_limit_eq_volume {C : ℕ} (hC : 2 ≤ C)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hlim : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a j) (N j)) atTop
        (𝓝 (∫ x, f x ∂μ)))
    (hac : μ ≪ volume) : μ = volume :=
  coreDigital_eq_volume_of_invariant_ac hC μ
    (coreDigital_invariant_of_window_limit u hu a N hN μ hlim) hac

end PrimeGapNormality.Prime
