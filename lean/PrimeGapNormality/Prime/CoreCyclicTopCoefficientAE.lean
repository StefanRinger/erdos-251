import PrimeGapNormality.Prime.CoreCyclicTopDegree
import PrimeGapNormality.Prime.CoreCyclicFiniteExterior
import PrimeGapNormality.Prime.CoreMvPolynomialZeroSet

/-!
# Almost-everywhere nonconstancy of the top normalized action

The top-degree action chosen algebraically has a genuinely nonzero moving
derivative.  Its finite exterior coefficient is the actual polynomial
constructed by `FiniteExterior.realCoeff`; its evaluation is proved equal to
an actual derivative coefficient.  Hence every frame law absolutely
continuous with respect to finite-dimensional Lebesgue measure sees a
nonconstant moving polynomial almost everywhere.
-/

namespace PrimeGapNormality.Prime.CoreCyclic.TopCoefficientAE

open MvPolynomial MeasureTheory Filter
open scoped Polynomial

noncomputable section

/-- Extend a finite normalized frame to the signed exterior coordinates.
Only coordinates in the genuine finite box can occur in the action. -/
def exteriorFrame (w : ℕ) (x : Fin (2 * w + 1) → ℝ) :
    OnePoint.ExteriorIndex → ℝ :=
  fun i ↦ x (Function.invFun (OnePoint.FiniteExterior.embedding w) i)

@[simp] theorem exteriorFrame_embedding (w : ℕ)
    (x : Fin (2 * w + 1) → ℝ) (i : Fin (2 * w + 1)) :
    exteriorFrame w x (OnePoint.FiniteExterior.embedding w i) = x i := by
  unfold exteriorFrame
  rw [Function.leftInverse_invFun
    (OnePoint.FiniteExterior.embedding w).injective]

/-- The top homogeneous part of the actual action, specialized at a finite
normalized exterior frame. -/
def normalizedTopAction
    (B : ℕ) {k : ℕ} (hk : 0 < k) (w : ℕ) (s : Fin k)
    (N : PeriodicLocal k) (x : Fin (2 * w + 1) → ℝ) : ℝ[X] :=
  OnePoint.movingSpecialization
    (homogeneousComponent (topDegree N) (OnePoint.action B hk w s N))
    (exteriorFrame w x)

/-- The displayed top action is literally the action of the selected top
homogeneous tuple, not a separately postulated polynomial. -/
theorem normalizedTopAction_eq_topHomogeneousTuple
    (B : ℕ) {k : ℕ} (hk : 0 < k) (w : ℕ) (s : Fin k)
    (N : PeriodicLocal k) (x : Fin (2 * w + 1) → ℝ) :
    normalizedTopAction B hk w s N x =
      OnePoint.movingSpecialization
        (OnePoint.action B hk w s (topHomogeneousTuple N))
        (exteriorFrame w x) := by
  unfold normalizedTopAction topHomogeneousTuple
  rw [OnePoint.homogeneousComponent_action]

/-- Evaluation of an exterior derivative coefficient is the corresponding
coefficient of the actual specialized moving derivative. -/
theorem exteriorDerivativeCoeff_eval_eq_derivative_coeff
    (p : OnePoint.SignedPoly) (y : OnePoint.ExteriorIndex → ℝ) (n : ℕ) :
    OnePoint.exteriorEval y (OnePoint.exteriorDerivativeCoeff p n) =
      (OnePoint.movingSpecialization p y).derivative.coeff n := by
  rw [OnePoint.derivative_movingSpecialization]
  simp only [OnePoint.movingSpecialization, OnePoint.exteriorDerivativeCoeff,
    OnePoint.movingDerivativeFamily, Polynomial.coeff_map,
    OnePoint.exteriorEval]

/-- A true finite representative for a derivative coefficient of the
chosen top action.  The final equality connects it pointwise to the actual
normalized action. -/
theorem exists_topCoefficient_representative_of_rooted
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w) :
    ∃ s : Fin k, ∃ n : ℕ, ∃ P : MvPolynomial (Fin (2 * w + 1)) ℝ,
      P = OnePoint.FiniteExterior.realCoeff w
        (OnePoint.exteriorDerivativeCoeff
          (OnePoint.action B hk w s (topHomogeneousTuple N)) n) ∧
      P ≠ 0 ∧
      ∀ x : Fin (2 * w + 1) → ℝ,
        eval x P = (normalizedTopAction B hk w s N x).derivative.coeff n := by
  obtain ⟨s, hs⟩ :=
    exists_action_topHomogeneousTuple_of_rooted hB hk w N hroot hN hw
  obtain ⟨n, hP, hrepresent⟩ :=
    OnePoint.FiniteExterior.exists_nonzero_finite_coefficient
    B hk w s (topHomogeneousTuple N) (topHomogeneousTuple_width N hw) hs
  let P : MvPolynomial (Fin (2 * w + 1)) ℝ :=
    OnePoint.FiniteExterior.realCoeff w
      (OnePoint.exteriorDerivativeCoeff
        (OnePoint.action B hk w s (topHomogeneousTuple N)) n)
  refine ⟨s, n, P, rfl, hP, ?_⟩
  intro x
  calc
    eval x P = OnePoint.exteriorEval (exteriorFrame w x)
        (OnePoint.exteriorDerivativeCoeff
          (OnePoint.action B hk w s (topHomogeneousTuple N)) n) := by
      simpa only [P, exteriorFrame_embedding] using
        hrepresent (exteriorFrame w x)
    _ = (OnePoint.movingSpecialization
          (OnePoint.action B hk w s (topHomogeneousTuple N))
          (exteriorFrame w x)).derivative.coeff n :=
      exteriorDerivativeCoeff_eval_eq_derivative_coeff _ _ _
    _ = (normalizedTopAction B hk w s N x).derivative.coeff n := by
      rw [normalizedTopAction_eq_topHomogeneousTuple]

/-- Under any explicitly supplied absolutely continuous finite-frame
marginal, the actual top normalized action is nonconstant almost everywhere.
The witness polynomial remains definitionally tied to the action and its
evaluation is the chosen derivative coefficient. -/
theorem exists_normalizedTopAction_nonconstant_ae_of_rooted
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w)
    (μ : Measure (Fin (2 * w + 1) → ℝ)) (hμ : μ ≪ volume) :
    ∃ s : Fin k, ∃ n : ℕ, ∃ P : MvPolynomial (Fin (2 * w + 1)) ℝ,
      P = OnePoint.FiniteExterior.realCoeff w
        (OnePoint.exteriorDerivativeCoeff
          (OnePoint.action B hk w s (topHomogeneousTuple N)) n) ∧
      P ≠ 0 ∧
      (∀ x : Fin (2 * w + 1) → ℝ,
        eval x P = (normalizedTopAction B hk w s N x).derivative.coeff n) ∧
      ∀ᵐ x ∂μ,
        (normalizedTopAction B hk w s N x).derivative ≠ 0 ∧
          (normalizedTopAction B hk w s N x).natDegree ≠ 0 := by
  obtain ⟨s, n, P, hPdef, hP, hrepresent⟩ :=
    exists_topCoefficient_representative_of_rooted hB hk w N hroot hN hw
  refine ⟨s, n, P, hPdef, hP, hrepresent, ?_⟩
  have hae := CoreMvPolynomialZeroSet.eval_ne_zero_ae_of_absolutelyContinuous
    P hP μ hμ
  filter_upwards [hae] with x hx
  have hcoeff : (normalizedTopAction B hk w s N x).derivative.coeff n ≠ 0 := by
    rwa [← hrepresent x]
  have hderiv : (normalizedTopAction B hk w s N x).derivative ≠ 0 := by
    intro hz
    apply hcoeff
    rw [hz, Polynomial.coeff_zero]
  exact ⟨hderiv, Polynomial.derivative_ne_zero.mp hderiv⟩

/-- Canonical fixed-point variant of the a.e. nonconstancy package. -/
theorem exists_normalizedTopAction_nonconstant_ae_of_normalForm_fixed
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (w : ℕ)
    (N : PeriodicLocal k) (hN : N ≠ 0)
    (hnormal : N = normalForm hB hk N)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w)
    (μ : Measure (Fin (2 * w + 1) → ℝ)) (hμ : μ ≪ volume) :
    ∃ s : Fin k, ∃ n : ℕ, ∃ P : MvPolynomial (Fin (2 * w + 1)) ℝ,
      P = OnePoint.FiniteExterior.realCoeff w
        (OnePoint.exteriorDerivativeCoeff
          (OnePoint.action B hk w s (topHomogeneousTuple N)) n) ∧
      P ≠ 0 ∧
      (∀ x : Fin (2 * w + 1) → ℝ,
        eval x P = (normalizedTopAction B hk w s N x).derivative.coeff n) ∧
      ∀ᵐ x ∂μ,
        (normalizedTopAction B hk w s N x).derivative ≠ 0 ∧
          (normalizedTopAction B hk w s N x).natDegree ≠ 0 := by
  apply exists_normalizedTopAction_nonconstant_ae_of_rooted hB hk w N _ hN hw μ hμ
  exact (congrArg (drop hk) hnormal).trans (drop_normalForm hB hk N)

end

end PrimeGapNormality.Prime.CoreCyclic.TopCoefficientAE
