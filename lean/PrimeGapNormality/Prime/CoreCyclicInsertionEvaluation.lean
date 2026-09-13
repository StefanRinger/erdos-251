import PrimeGapNormality.Prime.CoreCyclicAction
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Real.Basic

/-!
# Exact evaluation of the cyclic one-point action

This file separates the moving signed gap `X (-1)` from all exterior
signed gaps.  The result is a genuine univariate polynomial whose
coefficients are polynomials in the exterior frame.  In particular, a
nonzero formal moving derivative supplies a nonzero exterior coefficient
polynomial; it does not incorrectly assert that every specialized frame is
nondegenerate.

The identities below are purely algebraic.  Absolute continuity of the
exterior frame, and hence nullity of the exceptional coefficient zero set,
belongs to the separate rectangle-count argument.
-/

namespace PrimeGapNormality.Prime.CoreCyclic.OnePoint

open MvPolynomial
open scoped BigOperators Polynomial

noncomputable section

/-- Signed indices other than the moving coordinate `-1`. -/
abbrev ExteriorIndex := {i : ℤ // i ≠ (-1 : ℤ)}

/-- View a signed multivariate polynomial as a polynomial in `X (-1)`,
with multivariate coefficients in all exterior signed coordinates. -/
def splitMoving :
    SignedPoly ≃ₐ[ℚ] Polynomial (MvPolynomial ExteriorIndex ℚ) :=
  (renameEquiv ℚ (Equiv.optionSubtypeNe (-1 : ℤ)).symm).trans
    (optionEquivLeft ℚ ExteriorIndex)

@[simp] theorem splitMoving_C (q : ℚ) :
    splitMoving (C q) = Polynomial.C (C q) := by
  simp [splitMoving]

@[simp] theorem splitMoving_X_moving :
    splitMoving (X (-1 : ℤ)) = Polynomial.X := by
  simp [splitMoving, Equiv.optionSubtypeNe_symm_self]

@[simp] theorem splitMoving_X_exterior (i : ExteriorIndex) :
    splitMoving (X (i : ℤ)) = Polynomial.C (X i) := by
  simp [splitMoving, Equiv.optionSubtypeNe_symm_of_ne i.property]

/-- Evaluate the exterior coefficient variables in a real frame. -/
def exteriorEval (y : ExteriorIndex → ℝ) :
    MvPolynomial ExteriorIndex ℚ →+* ℝ :=
  eval₂Hom (algebraMap ℚ ℝ) y

/-- The univariate real polynomial obtained by freezing the exterior
coordinates and retaining `X (-1)` as `Polynomial.X`. -/
def movingSpecialization (p : SignedPoly) (y : ExteriorIndex → ℝ) : ℝ[X] :=
  Polynomial.map (exteriorEval y) (splitMoving p)

@[simp] theorem movingSpecialization_zero (y : ExteriorIndex → ℝ) :
    movingSpecialization 0 y = 0 := by
  simp [movingSpecialization]

@[simp] theorem movingSpecialization_one (y : ExteriorIndex → ℝ) :
    movingSpecialization 1 y = 1 := by
  simp [movingSpecialization]

@[simp] theorem movingSpecialization_add (p q : SignedPoly)
    (y : ExteriorIndex → ℝ) :
    movingSpecialization (p + q) y =
      movingSpecialization p y + movingSpecialization q y := by
  simp [movingSpecialization]

@[simp] theorem movingSpecialization_mul (p q : SignedPoly)
    (y : ExteriorIndex → ℝ) :
    movingSpecialization (p * q) y =
      movingSpecialization p y * movingSpecialization q y := by
  simp [movingSpecialization]

/-- The corresponding full real assignment of signed variables. -/
def movingAssignment (y : ExteriorIndex → ℝ) (v : ℝ) : ℤ → ℝ :=
  fun i ↦ if hi : i = -1 then v else y ⟨i, hi⟩

@[simp] theorem movingAssignment_moving (y : ExteriorIndex → ℝ) (v : ℝ) :
    movingAssignment y v (-1) = v := by
  simp [movingAssignment]

@[simp] theorem movingAssignment_exterior (y : ExteriorIndex → ℝ) (v : ℝ)
    (i : ExteriorIndex) : movingAssignment y v i = y i := by
  simp [movingAssignment, i.property]

@[simp] theorem movingSpecialization_C (q : ℚ) (y : ExteriorIndex → ℝ) :
    movingSpecialization (C q) y = Polynomial.C (q : ℝ) := by
  simp [movingSpecialization, exteriorEval]

@[simp] theorem movingSpecialization_X_moving (y : ExteriorIndex → ℝ) :
    movingSpecialization (X (-1 : ℤ)) y = Polynomial.X := by
  simp [movingSpecialization]

@[simp] theorem movingSpecialization_X_exterior (y : ExteriorIndex → ℝ)
    (i : ExteriorIndex) :
    movingSpecialization (X (i : ℤ)) y = Polynomial.C (y i) := by
  simp [movingSpecialization, exteriorEval]

/-- Evaluating the univariate specialization is exactly the original
multivariate evaluation with the moving coordinate set to `v`. -/
theorem movingSpecialization_eval (p : SignedPoly) (y : ExteriorIndex → ℝ)
    (v : ℝ) :
    Polynomial.eval v (movingSpecialization p y) =
      eval₂ (algebraMap ℚ ℝ) (movingAssignment y v) p := by
  induction p using MvPolynomial.induction_on with
  | C q => simp
  | add p q hp hq =>
      rw [movingSpecialization_add, Polynomial.eval_add, hp, hq, eval₂_add]
  | mul_X p i hp =>
      by_cases hi : i = (-1 : ℤ)
      · subst i
        rw [movingSpecialization_mul, movingSpecialization_X_moving,
          Polynomial.eval_mul, Polynomial.eval_X, hp, eval₂_mul, eval₂_X,
          movingAssignment_moving]
      · let i' : ExteriorIndex := ⟨i, hi⟩
        have hs : splitMoving (X i) = Polynomial.C (X i') := by
          simpa [i'] using splitMoving_X_exterior i'
        have hspec : movingSpecialization (X i) y = Polynomial.C (y i') := by
          simp [movingSpecialization, hs, exteriorEval]
        have ha : movingAssignment y v i = y i' := by
          simp [movingAssignment, hi, i']
        rw [movingSpecialization_mul, hspec, Polynomial.eval_mul,
          Polynomial.eval_C, hp, eval₂_mul, eval₂_X, ha]

/-! ### The formal derivative and its exterior coefficient witness -/

/-- The formal moving derivative, still kept as a polynomial over the
exterior polynomial ring. -/
def movingDerivativeFamily (p : SignedPoly) :
    Polynomial (MvPolynomial ExteriorIndex ℚ) :=
  splitMoving (pderiv (-1 : ℤ) p)

/-- Its coefficient at a chosen power of the moving variable. -/
def exteriorDerivativeCoeff (p : SignedPoly) (n : ℕ) :
    MvPolynomial ExteriorIndex ℚ :=
  (movingDerivativeFamily p).coeff n

theorem movingDerivativeFamily_ne_zero {p : SignedPoly}
    (hp : pderiv (-1 : ℤ) p ≠ 0) : movingDerivativeFamily p ≠ 0 := by
  intro hz
  apply hp
  apply splitMoving.injective
  simpa [movingDerivativeFamily] using hz

/-- A nonzero moving derivative exposes an actual nonzero polynomial in
the exterior frame variables.  This is the coefficient to which the
rectangle/null-set argument is applied. -/
theorem exists_exteriorDerivativeCoeff_ne_zero {p : SignedPoly}
    (hp : pderiv (-1 : ℤ) p ≠ 0) :
    ∃ n : ℕ, exteriorDerivativeCoeff p n ≠ 0 := by
  have hnonzero := movingDerivativeFamily_ne_zero hp
  obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr hnonzero
  exact ⟨n, by simpa [exteriorDerivativeCoeff] using
    (Polynomial.mem_support_iff.mp hn)⟩

/-- Specialization commutes with the formal moving derivative. -/
theorem derivative_movingSpecialization (p : SignedPoly)
    (y : ExteriorIndex → ℝ) :
    (movingSpecialization p y).derivative =
      movingSpecialization (pderiv (-1 : ℤ) p) y := by
  induction p using MvPolynomial.induction_on with
  | C q =>
      rw [movingSpecialization_C, Polynomial.derivative_C, pderiv_C,
        movingSpecialization_zero]
  | add p q hp hq =>
      rw [movingSpecialization_add, Polynomial.derivative_add, hp, hq,
        map_add, movingSpecialization_add]
  | mul_X p i hp =>
      by_cases hi : i = (-1 : ℤ)
      · subst i
        rw [movingSpecialization_mul, movingSpecialization_X_moving,
          Polynomial.derivative_mul, hp, Polynomial.derivative_X,
          pderiv_mul, pderiv_X_self, movingSpecialization_add,
          movingSpecialization_mul, movingSpecialization_X_moving,
          movingSpecialization_mul, movingSpecialization_one]
      · let i' : ExteriorIndex := ⟨i, hi⟩
        have hs : splitMoving (X i) = Polynomial.C (X i') := by
          simpa [i'] using splitMoving_X_exterior i'
        have hspec : movingSpecialization (X i) y = Polynomial.C (y i') := by
          simp [movingSpecialization, hs, exteriorEval]
        have hdx : pderiv (-1 : ℤ) (X i : SignedPoly) = 0 :=
          pderiv_X_of_ne hi
        rw [movingSpecialization_mul, hspec, Polynomial.derivative_mul, hp,
          Polynomial.derivative_C, mul_zero, add_zero, pderiv_mul, hdx,
          movingSpecialization_add, movingSpecialization_mul,
          movingSpecialization_mul, movingSpecialization_zero, mul_zero,
          add_zero]
        rw [hspec]

/-- If a particular exterior frame makes the univariate derivative zero,
then every exterior coefficient polynomial vanishes at that frame. -/
theorem exteriorDerivativeCoeff_eval_eq_zero_of_derivative_eq_zero
    (p : SignedPoly) (y : ExteriorIndex → ℝ)
    (hzero : (movingSpecialization p y).derivative = 0) (n : ℕ) :
    eval₂ (algebraMap ℚ ℝ) y (exteriorDerivativeCoeff p n) = 0 := by
  rw [derivative_movingSpecialization] at hzero
  have hc := congrArg (fun q : ℝ[X] ↦ q.coeff n) hzero
  simpa [movingSpecialization, exteriorDerivativeCoeff, movingDerivativeFamily,
    exteriorEval] using hc

/-! ### Exact action evaluation -/

/-- The assignment induced before and after splitting the adjacent gaps:
the old signed gap `0` is replaced by `x 0 - x (-1)`. -/
def movedGapAssignment (x : ℤ → ℝ) : ℤ → ℝ :=
  fun i ↦ if i = 0 then x 0 - x (-1) else x i

theorem eval₂_moveSubst (p : SignedPoly) (x : ℤ → ℝ) :
    eval₂ (algebraMap ℚ ℝ) x (moveSubst p) =
      eval₂ (algebraMap ℚ ℝ) (movedGapAssignment x) p := by
  induction p using MvPolynomial.induction_on with
  | C q => simp [moveSubst, movedGapAssignment]
  | add p q hp hq =>
      rw [map_add, eval₂_add, hp, hq, eval₂_add]
  | mul_X p i hp =>
      by_cases hi : i = 0
      · subst i
        rw [map_mul, eval₂_mul, hp, moveSubst_X, if_pos rfl, eval₂_sub,
          eval₂_X, eval₂_X, eval₂_mul, eval₂_X]
        simp [movedGapAssignment]
      · rw [map_mul, eval₂_mul, hp, moveSubst_X, if_neg hi, eval₂_X,
          eval₂_mul, eval₂_X]
        simp [movedGapAssignment, hi]

/-- Exact rational-to-real evaluation of the pre-action as its finite
shifted local-polynomial sum. -/
theorem eval₂_preAction (B : ℕ) {k : ℕ} (hk : 0 < k) (w : ℕ)
    (s : Fin k) (F : PeriodicLocal k) (x : ℤ → ℝ) :
    eval₂ (algebraMap ℚ ℝ) x (preAction B hk w s F) =
      ∑ j ∈ Finset.range (w + 2), (B : ℝ) ^ j *
        eval₂ (algebraMap ℚ ℝ)
          (fun i : ℕ ↦ x ((i : ℤ) - (j : ℤ)))
          (F ((predecessor hk)^[j] (cyclicSucc hk s))) := by
  change eval₂Hom (algebraMap ℚ ℝ) x (preAction B hk w s F) = _
  unfold preAction
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [eval₂Hom_smul]
  unfold signedShift
  rw [eval₂Hom_rename]
  simp only [smul_eq_mul, map_pow, map_natCast, Function.comp_apply]
  rfl

/-- The existing signed action, after exterior specialization, evaluates
to the exact finite one-point sum with the adjacent gap split. -/
theorem movingSpecialization_action_eval
    (B : ℕ) {k : ℕ} (hk : 0 < k) (w : ℕ) (s : Fin k)
    (F : PeriodicLocal k) (y : ExteriorIndex → ℝ) (v : ℝ) :
    Polynomial.eval v (movingSpecialization (action B hk w s F) y) =
      ∑ j ∈ Finset.range (w + 2), (B : ℝ) ^ j *
        eval₂ (algebraMap ℚ ℝ)
          (fun i : ℕ ↦ movedGapAssignment (movingAssignment y v)
            ((i : ℤ) - (j : ℤ)))
          (F ((predecessor hk)^[j] (cyclicSucc hk s))) := by
  rw [movingSpecialization_eval, action, eval₂_moveSubst,
    eval₂_preAction]

end

end PrimeGapNormality.Prime.CoreCyclic.OnePoint
