import PrimeGapNormality.Prime.CoreCyclicIntegerLift
import PrimeGapNormality.Prime.CoreCyclicTopDegree
import PrimeGapNormality.Prime.CoreCyclicOrbitIdentification

/-!
# The selected integer lift of a rooted rational tuple

This file packages the already constructed common-denominator lift.  For a
rooted nonzero rational tuple, its mapped integer tuple is again rooted and
nonzero, has exactly the same variables and top degree, and its genuine full
local series is the positive integer scale times the original series.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Finset MvPolynomial

noncomputable section

/-- The rational image of the selected integer-coefficient tuple. -/
def liftedIntegerTuple {k : ℕ} (N : PeriodicLocal k) : PeriodicLocal k :=
  mapIntTuple (integerTupleLift N).tuple

/-- Its selected positive integral scale. -/
def liftedIntegerScale {k : ℕ} (N : PeriodicLocal k) : ℕ :=
  (integerTupleLift N).scale

theorem liftedIntegerScale_pos {k : ℕ} (N : PeriodicLocal k) :
    0 < liftedIntegerScale N :=
  (integerTupleLift N).scale_pos

theorem liftedIntegerScale_ne_zero_rat {k : ℕ} (N : PeriodicLocal k) :
    ((liftedIntegerScale N : ℕ) : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (liftedIntegerScale_pos N).ne'

/-- The exact common-denominator identity. -/
theorem liftedIntegerTuple_eq_smul {k : ℕ} (N : PeriodicLocal k) :
    liftedIntegerTuple N = (liftedIntegerScale N : ℚ) • N := by
  exact integerTupleLift_map_eq N

theorem liftedIntegerTuple_rooted {k : ℕ} (hk : 0 < k)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) :
    drop hk (liftedIntegerTuple N) = 0 := by
  rw [liftedIntegerTuple_eq_smul, map_smul, hroot, smul_zero]

theorem liftedIntegerTuple_ne_zero {k : ℕ} (N : PeriodicLocal k)
    (hN : N ≠ 0) : liftedIntegerTuple N ≠ 0 := by
  rw [liftedIntegerTuple_eq_smul]
  exact smul_ne_zero (liftedIntegerScale_ne_zero_rat N) hN

/-- Rootedness also makes the lifted tuple a fixed point of the canonical
normal form. -/
theorem normalForm_liftedIntegerTuple {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) :
    normalForm hB hk (liftedIntegerTuple N) = liftedIntegerTuple N :=
  normalForm_of_rooted hB hk _ (liftedIntegerTuple_rooted hk N hroot)

/-- Exact componentwise variable preservation after mapping the integer
coefficients back to `ℚ`. -/
theorem liftedIntegerTuple_vars {k : ℕ} (N : PeriodicLocal k) (r : Fin k) :
    (liftedIntegerTuple N r).vars = (N r).vars := by
  change (MvPolynomial.map (algebraMap ℤ ℚ) ((integerTupleLift N).tuple r)).vars =
    (N r).vars
  calc
    (MvPolynomial.map (algebraMap ℤ ℚ)
        ((integerTupleLift N).tuple r)).vars =
        ((integerTupleLift N).tuple r).vars :=
      vars_map_of_injective _ Int.cast_injective
    _ = (N r).vars := integerTupleLift_vars N r

theorem liftedIntegerTuple_width_iff {k w : ℕ} (N : PeriodicLocal k) :
    (∀ r i, i ∈ (liftedIntegerTuple N r).vars → i ≤ w) ↔
      ∀ r i, i ∈ (N r).vars → i ≤ w := by
  constructor <;> intro h r i hi
  · exact h r i (by rwa [liftedIntegerTuple_vars])
  · exact h r i (by rwa [liftedIntegerTuple_vars] at hi)

theorem liftedIntegerTuple_usesBelow_iff {k n : ℕ} (N : PeriodicLocal k) :
    UsesBelow (liftedIntegerTuple N) n ↔ UsesBelow N n := by
  constructor <;> intro h r i hi
  · exact h r i (by rwa [liftedIntegerTuple_vars])
  · exact h r i (by rwa [liftedIntegerTuple_vars] at hi)

/-- Exact top-degree preservation; no upper-bound relaxation is used. -/
theorem topDegree_liftedIntegerTuple {k : ℕ} (N : PeriodicLocal k) :
    topDegree (liftedIntegerTuple N) = topDegree N := by
  unfold topDegree
  apply congrArg (fun f : Fin k → ℕ ↦ Finset.univ.sup f)
  funext r
  change (MvPolynomial.map (algebraMap ℤ ℚ)
      ((integerTupleLift N).tuple r)).totalDegree = (N r).totalDegree
  unfold MvPolynomial.totalDegree
  rw [support_map_of_injective _ Int.cast_injective,
    integerTupleLift_support]

/-- The actual infinite local series scales by the same selected positive
integer. -/
theorem coreCyclicFullSeries_liftedIntegerTuple
    (B : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (g : ℕ → ℝ) (N : PeriodicLocal k) :
    coreCyclicFullSeries B hk phase g (liftedIntegerTuple N) =
      (liftedIntegerScale N : ℝ) *
        coreCyclicFullSeries B hk phase g N := by
  calc
    coreCyclicFullSeries B hk phase g (liftedIntegerTuple N) =
        coreLocalSeries B hk phase g (liftedIntegerTuple N) 0 :=
      (coreLocalSeries_zero_eq_fullSeries B hk phase g
        (liftedIntegerTuple N)).symm
    _ = (liftedIntegerScale N : ℝ) * coreLocalSeries B hk phase g N 0 := by
      exact coreLocalSeries_integerTupleLift B hk phase g N 0
    _ = (liftedIntegerScale N : ℝ) *
        coreCyclicFullSeries B hk phase g N := by
      rw [coreLocalSeries_zero_eq_fullSeries]

end

end PrimeGapNormality.Prime.CoreCyclic
