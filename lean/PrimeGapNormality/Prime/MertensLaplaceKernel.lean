import PrimeGapNormality.Prime.MertensAbelian
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# The normalized Laplace kernel in the Mertens Abelian argument

This file records the two exact improper integrals needed after the change of
variables `u = t * log x` in the Abelian passage from reciprocal-prime sums to
the prime Dirichlet series.  The logarithmic identity is obtained by comparing
Mathlib's derivative-under-the-Gamma-integral formula with the known value of
the derivative of `Gamma` at one.
-/

namespace PrimeGapNormality.Prime

open Asymptotics Filter MeasureTheory Set

noncomputable section

/-- The normalized exponential kernel has total mass one on `(0, ∞)`. -/
theorem integral_exp_neg_Ioi_zero_eq_one :
    (∫ u : ℝ in Ioi 0, Real.exp (-u)) = 1 :=
  integral_exp_neg_Ioi_zero

/-- Integrability of the mass-one exponential kernel. -/
theorem integrableOn_exp_neg_Ioi_zero :
    IntegrableOn (fun u : ℝ ↦ Real.exp (-u)) (Ioi 0) :=
  integrableOn_exp_neg_Ioi 0

/- The derivative-under-the-Mellin-integral theorem supplies convergence in
`ℂ`.  We first put that assertion in the exact `Complex.ofReal` form needed
below; keeping the cast explicit makes both the norm and integral projections
canonical. -/
private theorem integrableOn_ofReal_exp_neg_mul_log_Ioi_zero :
    IntegrableOn
      (fun u : ℝ ↦ ((Real.exp (-u) * Real.log u : ℝ) : ℂ))
      (Ioi 0) := by
  have hconv :
      MellinConvergent
        (fun u : ℝ ↦ Real.log u • (Real.exp (-u) : ℂ)) (1 : ℂ) := by
    refine
      (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) (a := 2) (b := 0)
        (s := (1 : ℂ)) ?_ ?_ (by norm_num) ?_ (by norm_num)).1
    · refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
      exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
    · rw [← isBigO_norm_left]
      simp_rw [Complex.norm_real, isBigO_norm_left]
      simpa only [neg_one_mul] using
        (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-2)).isBigO
    · simp_rw [neg_zero, Real.rpow_zero]
      refine isBigO_const_of_tendsto (?_ : Tendsto _ _ (nhds (1 : ℂ))) one_ne_zero
      rw [(by simp : (1 : ℂ) = Real.exp (-0))]
      exact
        (Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp continuous_neg)).continuousWithinAt
  rw [MellinConvergent] at hconv
  refine hconv.congr_fun ?_ measurableSet_Ioi
  intro u hu
  change
    (u : ℂ) ^ ((1 : ℂ) - 1) *
        ((Real.log u : ℂ) * (Real.exp (-u) : ℂ)) =
      ((Real.exp (-u) * Real.log u : ℝ) : ℂ)
  simp [mul_comm]

/-- The logarithmic moment of the exponential kernel is absolutely
integrable.  This is the convergence assertion used internally in Mathlib's
derivative-under-the-Gamma-integral theorem, specialized at `s = 1`. -/
theorem integrableOn_exp_neg_mul_log_Ioi_zero :
    IntegrableOn (fun u : ℝ ↦ Real.exp (-u) * Real.log u) (Ioi 0) := by
  have hcomplex := integrableOn_ofReal_exp_neg_mul_log_Ioi_zero
  change
    Integrable
      (fun u : ℝ ↦ ((Real.exp (-u) * Real.log u : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) at hcomplex
  change
    Integrable (fun u : ℝ ↦ Real.exp (-u) * Real.log u)
      (volume.restrict (Ioi 0))
  refine hcomplex.congr' ?_ ?_
  · exact
      ((Real.continuous_exp.comp continuous_neg).measurable.mul
        Real.measurable_log).aestronglyMeasurable
  · filter_upwards with u
    simp only [Complex.norm_real, Real.norm_eq_abs]

/-- The logarithmic moment of the normalized exponential kernel is `-γ`.

This is the constant term produced by the substitution `u = t * log x` in
the main kernel of the Mertens Abelian bridge. -/
theorem integral_exp_neg_mul_log_Ioi_zero :
    (∫ u : ℝ in Ioi 0, Real.exp (-u) * Real.log u) =
      -Real.eulerMascheroniConstant := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hder :
      HasDerivAt Complex.Gamma
        (∫ u : ℝ in Ioi 0,
          (u : ℂ) ^ ((1 : ℂ) - 1) *
            (Real.log u * Real.exp (-u))) 1 := by
    apply
      (Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact Complex.Gamma_eq_integral hs
  have hvalue :
      (∫ u : ℝ in Ioi 0,
          (u : ℂ) ^ ((1 : ℂ) - 1) *
            (Real.log u * Real.exp (-u))) =
        -(Real.eulerMascheroniConstant : ℂ) :=
    hder.unique Complex.hasDerivAt_Gamma_one
  have hcoe :
      (∫ u : ℝ in Ioi 0,
          (u : ℂ) ^ ((1 : ℂ) - 1) *
            (Real.log u * Real.exp (-u))) =
        ∫ u : ℝ in Ioi 0,
          ((Real.exp (-u) * Real.log u : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
    simp [mul_comm]
  have hcomplexValue :
      (∫ u : ℝ in Ioi 0,
          ((Real.exp (-u) * Real.log u : ℝ) : ℂ)) =
        -(Real.eulerMascheroniConstant : ℂ) :=
    hcoe.symm.trans hvalue
  have hcomplexIntegrable := integrableOn_ofReal_exp_neg_mul_log_Ioi_zero
  change
    Integrable
      (fun u : ℝ ↦ ((Real.exp (-u) * Real.log u : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) at hcomplexIntegrable
  change
    (∫ u : ℝ, Real.exp (-u) * Real.log u
      ∂volume.restrict (Ioi 0)) = -Real.eulerMascheroniConstant
  change
    (∫ u : ℝ,
        ((Real.exp (-u) * Real.log u : ℝ) : ℂ)
      ∂volume.restrict (Ioi 0)) =
      -(Real.eulerMascheroniConstant : ℂ) at hcomplexValue
  have hproject :
      (∫ u : ℝ, Real.exp (-u) * Real.log u
        ∂volume.restrict (Ioi 0)) =
        (∫ u : ℝ,
            ((Real.exp (-u) * Real.log u : ℝ) : ℂ)
          ∂volume.restrict (Ioi 0)).re := by
    have hpoint (u : ℝ) :
        RCLike.re (↑(Real.exp (-u) * Real.log u) : ℂ) =
          Real.exp (-u) * Real.log u := by
      change (↑(Real.exp (-u) * Real.log u) : ℂ).re = _
      exact Complex.ofReal_re _
    calc
      (∫ u : ℝ, Real.exp (-u) * Real.log u
        ∂volume.restrict (Ioi 0)) =
          (∫ u : ℝ,
              RCLike.re (↑(Real.exp (-u) * Real.log u) : ℂ)
            ∂volume.restrict (Ioi 0)) := by
        apply integral_congr_ae
        filter_upwards with u
        exact hpoint u
      _ = (∫ u : ℝ,
            ((Real.exp (-u) * Real.log u : ℝ) : ℂ)
          ∂volume.restrict (Ioi 0)).re :=
        integral_re hcomplexIntegrable
  calc
    (∫ u : ℝ, Real.exp (-u) * Real.log u
      ∂volume.restrict (Ioi 0)) =
        (∫ u : ℝ,
            ((Real.exp (-u) * Real.log u : ℝ) : ℂ)
          ∂volume.restrict (Ioi 0)).re := hproject
    _ = (-(Real.eulerMascheroniConstant : ℂ)).re :=
      congrArg Complex.re hcomplexValue
    _ = -Real.eulerMascheroniConstant := by
      simp only [Complex.neg_re, Complex.ofReal_re]

/-- The centered logarithmic moment, in the form used after extracting a
constant from the logarithm. -/
theorem integral_exp_neg_mul_log_sub_const_Ioi_zero (c : ℝ) :
    (∫ u : ℝ in Ioi 0, Real.exp (-u) * (Real.log u - c)) =
      -Real.eulerMascheroniConstant - c := by
  calc
    (∫ u : ℝ in Ioi 0, Real.exp (-u) * (Real.log u - c)) =
        ∫ u : ℝ in Ioi 0,
          Real.exp (-u) * Real.log u - Real.exp (-u) * c := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
      ring
    _ = (∫ u : ℝ in Ioi 0, Real.exp (-u) * Real.log u) -
        ∫ u : ℝ in Ioi 0, Real.exp (-u) * c :=
      MeasureTheory.integral_sub integrableOn_exp_neg_mul_log_Ioi_zero
        (integrableOn_exp_neg_Ioi_zero.mul_const c)
    _ = -Real.eulerMascheroniConstant - c := by
      rw [integral_exp_neg_mul_log_Ioi_zero, integral_mul_const,
        integral_exp_neg_Ioi_zero_eq_one]
      ring

/-- Division form of the normalized logarithmic kernel. -/
theorem integral_exp_neg_mul_log_div_Ioi_zero {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ in Ioi 0, Real.exp (-u) * Real.log (u / t)) =
      -Real.eulerMascheroniConstant - Real.log t := by
  calc
    (∫ u : ℝ in Ioi 0, Real.exp (-u) * Real.log (u / t)) =
        ∫ u : ℝ in Ioi 0,
          Real.exp (-u) * (Real.log u - Real.log t) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
      rw [Real.log_div hu.ne' ht.ne']
    _ = -Real.eulerMascheroniConstant - Real.log t :=
      integral_exp_neg_mul_log_sub_const_Ioi_zero (Real.log t)

end

end PrimeGapNormality.Prime
