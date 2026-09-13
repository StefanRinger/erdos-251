import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
A nonzero real polynomial in finitely many variables has a Lebesgue-null
zero set. Split off the first coordinate; one nonzero coefficient controls
the exceptional parameter set, and all other one-variable slices have
finitely many roots. The coordinate split preserves the actual product
volume, so Fubini introduces no assumed Haar normalization.
-/

namespace PrimeGapNormality.Prime.CoreMvPolynomialZeroSet

open Set Filter MeasureTheory MvPolynomial
open scoped Topology ENNReal Polynomial

noncomputable section

theorem measurable_zero_set {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MeasurableSet {x : Fin n → ℝ | eval x P = 0} :=
  (isClosed_eq P.continuous_eval continuous_const).measurableSet

/-- The explicit scalar polynomial obtained by freezing all but the first
coordinate. Its coefficients are evaluations of actual lower-dimensional
polynomials, not assumed parameter functions. -/
def slice {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ) (y : Fin n → ℝ) : ℝ[X] :=
  Polynomial.map (eval y) (finSuccEquiv ℝ n P)

theorem slice_eval {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (y : Fin n → ℝ) (t : ℝ) :
    (slice P y).eval t = eval (Fin.cons t y) P :=
  (eval_eq_eval_mv_eval' y t P).symm

theorem slice_ne_zero_of_coefficient {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℝ) (i : ℕ) (y : Fin n → ℝ)
    (hi : eval y ((finSuccEquiv ℝ n P).coeff i) ≠ 0) : slice P y ≠ 0 := by
  intro hz
  have hc := congrArg (fun Q : ℝ[X] ↦ Q.coeff i) hz
  exact hi (by simpa only [slice, Polynomial.coeff_map, Polynomial.coeff_zero] using hc)

theorem slice_zero_set_null {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (y : Fin n → ℝ) (hy : slice P y ≠ 0) :
    volume {t : ℝ | eval (Fin.cons t y) P = 0} = 0 := by
  have hfinite := Polynomial.finite_setOfPred_isRoot hy
  have hnull := hfinite.measure_zero volume
  simpa only [Polynomial.IsRoot, slice_eval] using hnull

/-- Global Lebesgue-null zero set in every finite dimension, including the
zero-dimensional case of a nonzero constant. -/
theorem volume_zero_set : ∀ n : ℕ, ∀ P : MvPolynomial (Fin n) ℝ,
    P ≠ 0 → volume {x : Fin n → ℝ | eval x P = 0} = 0 := by
  intro n
  induction n with
  | zero =>
    intro P hP
    have hpC := P.eq_C_of_isEmpty
    have hc : P.coeff 0 ≠ 0 := by
      intro hc
      apply hP
      exact hpC.trans (by simp only [hc, map_zero])
    have hempty : {x : Fin 0 → ℝ | eval x P = 0} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      rw [hpC, eval_C]
      exact hc
    rw [hempty, measure_empty]
  | succ n ih =>
    intro P hP
    have hQ : finSuccEquiv ℝ n P ≠ 0 := by
      intro hz
      apply hP
      apply (finSuccEquiv ℝ n).injective
      simpa only [map_zero] using hz
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.2 hQ
    have hcoeff : (finSuccEquiv ℝ n P).coeff i ≠ 0 := Polynomial.mem_support_iff.1 hi
    have hcoeffnull := ih ((finSuccEquiv ℝ n P).coeff i) hcoeff
    have hgood : ∀ᵐ y : Fin n → ℝ ∂volume,
        eval y ((finSuccEquiv ℝ n P).coeff i) ≠ 0 := by
      apply ae_iff.2
      simpa only [not_not] using hcoeffnull
    let e : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
    have he : MeasurePreserving e :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm _
    have heval (t : ℝ) (y : Fin n → ℝ) : e (t, y) = Fin.cons t y := by
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero']
    let Z : Set (Fin (n + 1) → ℝ) := {x | eval x P = 0}
    have hZ : MeasurableSet Z := measurable_zero_set P
    have hpre : MeasurableSet (e ⁻¹' Z) := hZ.preimage e.measurable
    change volume Z = 0
    rw [← he.measure_preimage hZ.nullMeasurableSet, Measure.volume_eq_prod,
      Measure.prod_apply_symm hpre]
    calc
      (∫⁻ y : Fin n → ℝ, volume ((fun t : ℝ ↦ (t, y)) ⁻¹' (e ⁻¹' Z))) =
          ∫⁻ _y : Fin n → ℝ, (0 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [hgood] with y hy
        have hslice := slice_zero_set_null P y (slice_ne_zero_of_coefficient P i y hy)
        have hset : (fun t : ℝ ↦ (t, y)) ⁻¹' (e ⁻¹' Z) =
            {t : ℝ | eval (Fin.cons t y) P = 0} := by
          ext t
          simp only [mem_preimage, Z, mem_setOf_eq, heval]
        rw [hset]
        exact hslice
      _ = 0 := by simp

theorem eval_ne_zero_ae {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0) :
    ∀ᵐ x : Fin n → ℝ ∂volume, eval x P ≠ 0 := by
  apply ae_iff.2
  simpa only [not_not] using volume_zero_set n P hP

/-- Every absolutely continuous frame law inherits the same null set. -/
theorem zero_set_null_of_absolutelyContinuous {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0)
    (μ : Measure (Fin n → ℝ)) (hμ : μ ≪ volume) :
    μ {x : Fin n → ℝ | eval x P = 0} = 0 :=
  hμ (volume_zero_set n P hP)

theorem eval_ne_zero_ae_of_absolutelyContinuous {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0)
    (μ : Measure (Fin n → ℝ)) (hμ : μ ≪ volume) :
    ∀ᵐ x ∂μ, eval x P ≠ 0 := by
  apply ae_iff.2
  simpa only [not_not] using zero_set_null_of_absolutelyContinuous P hP μ hμ

end

end PrimeGapNormality.Prime.CoreMvPolynomialZeroSet
