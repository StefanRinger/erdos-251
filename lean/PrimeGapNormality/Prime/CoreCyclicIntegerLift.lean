import PrimeGapNormality.Prime.CoreLocalSeriesRecurrence
import PrimeGapNormality.Prime.CoreCyclicDegree
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Clearing denominators in a finite periodic local tuple

Every rational tuple is a positive integral rescaling of an actual
integer-coefficient tuple.  The construction is finite (polynomial induction,
then a product over the period), and the injective coefficient embedding
shows that support, degree and width are preserved exactly.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Finset MvPolynomial
open scoped BigOperators

noncomputable section

private theorem map_int_smul (z : ℤ) (p : MvPolynomial ℕ ℤ) :
    MvPolynomial.map (algebraMap ℤ ℚ) (z • p) =
      (z : ℚ) • MvPolynomial.map (algebraMap ℤ ℚ) p := by
  simp only [smul_eq_C_mul, map_mul, map_C]
  rfl

/-- Denominator clearing for one finite multivariate polynomial. -/
theorem exists_integerPolynomial_lift (p : LocalPoly) :
    ∃ q : ℕ, 0 < q ∧ ∃ P : MvPolynomial ℕ ℤ,
      MvPolynomial.map (algebraMap ℤ ℚ) P = (q : ℚ) • p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      refine ⟨c.den, c.den_pos, C c.num, ?_⟩
      have hd : (c.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
      have hc : (c.num : ℚ) = c * c.den :=
        (div_eq_iff hd).mp c.num_div_den
      rw [map_C]
      change C (c.num : ℚ) = (c.den : ℚ) • C c
      rw [smul_eq_C_mul, ← C_mul]
      congr 1
      simpa only [mul_comm] using hc
  | add p r hp hr =>
      obtain ⟨q, hq, P, hP⟩ := hp
      obtain ⟨s, hs, R, hR⟩ := hr
      refine ⟨q * s, Nat.mul_pos hq hs,
        (s : ℤ) • P + (q : ℤ) • R, ?_⟩
      rw [map_add, map_int_smul, map_int_smul, hP, hR,
        Nat.cast_mul]
      module
  | mul_X p i hp =>
      obtain ⟨q, hq, P, hP⟩ := hp
      refine ⟨q, hq, P * X i, ?_⟩
      rw [map_mul, map_X, hP]
      simp only [smul_eq_C_mul, mul_assoc]

/-- A selected positive common denominator and integer tuple. -/
structure IntegerTupleLift {k : ℕ} (F : PeriodicLocal k) where
  scale : ℕ
  scale_pos : 0 < scale
  tuple : Fin k → MvPolynomial ℕ ℤ
  map_eq : mapIntTuple tuple = (scale : ℚ) • F

theorem exists_integerTupleLift {k : ℕ} (F : PeriodicLocal k) :
    Nonempty (IntegerTupleLift F) := by
  classical
  let q : Fin k → ℕ := fun r ↦ Classical.choose (exists_integerPolynomial_lift (F r))
  let P : Fin k → MvPolynomial ℕ ℤ := fun r ↦
    Classical.choose (Classical.choose_spec (exists_integerPolynomial_lift (F r))).2
  have hq (r : Fin k) : 0 < q r :=
    (Classical.choose_spec (exists_integerPolynomial_lift (F r))).1
  have hP (r : Fin k) :
      MvPolynomial.map (algebraMap ℤ ℚ) (P r) = (q r : ℚ) • F r :=
    Classical.choose_spec
      (Classical.choose_spec (exists_integerPolynomial_lift (F r))).2
  let Q : ℕ := ∏ r, q r
  have hQ : 0 < Q := prod_pos fun r _ ↦ hq r
  have hdiv (r : Fin k) : q r ∣ Q :=
    dvd_prod_of_mem q (mem_univ r)
  let Fz : Fin k → MvPolynomial ℕ ℤ := fun r ↦
    ((Q / q r : ℕ) : ℤ) • P r
  refine ⟨⟨Q, hQ, Fz, ?_⟩⟩
  funext r
  rw [Pi.smul_apply]
  unfold mapIntTuple Fz
  rw [map_int_smul, hP]
  have hmul : Q / q r * q r = Q := Nat.div_mul_cancel (hdiv r)
  simp only [smul_smul, Int.cast_natCast, ← Nat.cast_mul, hmul]

/-- A canonical selected integer lift. -/
def integerTupleLift {k : ℕ} (F : PeriodicLocal k) : IntegerTupleLift F :=
  Classical.choice (exists_integerTupleLift F)

theorem integerTupleLift_map_eq {k : ℕ} (F : PeriodicLocal k) :
    mapIntTuple (integerTupleLift F).tuple =
      ((integerTupleLift F).scale : ℚ) • F :=
  (integerTupleLift F).map_eq

theorem integerTupleLift_scale_ne_zero {k : ℕ} (F : PeriodicLocal k) :
    ((integerTupleLift F).scale : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (integerTupleLift F).scale_pos.ne'

/-- Coefficient support is unchanged by the selected lift. -/
theorem integerTupleLift_support {k : ℕ} (F : PeriodicLocal k) (r : Fin k) :
    ((integerTupleLift F).tuple r).support = (F r).support := by
  let T := integerTupleLift F
  have hmap := congrFun (integerTupleLift_map_eq F) r
  simp only [T, mapIntTuple, Pi.smul_apply] at hmap
  have hmapSupport :
      (MvPolynomial.map (algebraMap ℤ ℚ) (T.tuple r)).support =
        (T.tuple r).support :=
    support_map_of_injective _ Int.cast_injective
  have hscaleSupport : (((T.scale : ℚ) • F r).support) = (F r).support :=
    support_smul_eq (Nat.cast_ne_zero.mpr T.scale_pos.ne') _
  change (T.tuple r).support = (F r).support
  rw [← hmapSupport, hmap, hscaleSupport]

theorem integerTupleLift_totalDegree {k : ℕ} (F : PeriodicLocal k) (r : Fin k) :
    ((integerTupleLift F).tuple r).totalDegree = (F r).totalDegree := by
  unfold MvPolynomial.totalDegree
  rw [integerTupleLift_support]

theorem integerTupleLift_vars {k : ℕ} (F : PeriodicLocal k) (r : Fin k) :
    ((integerTupleLift F).tuple r).vars = (F r).vars := by
  unfold MvPolynomial.vars MvPolynomial.degrees
  rw [integerTupleLift_support]

/-- Exact preservation of the paper's width predicate. -/
theorem integerTupleLift_usesBelow_iff {k n : ℕ} (F : PeriodicLocal k) :
    (∀ r i, i ∈ ((integerTupleLift F).tuple r).vars → i < n) ↔ UsesBelow F n := by
  constructor <;> intro h r i hi
  · exact h r i (by rwa [integerTupleLift_vars])
  · exact h r i (by rwa [integerTupleLift_vars] at hi)

/-- Rational linearity identifies the normal form of the lifted tuple. -/
theorem normalForm_integerTupleLift {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) :
    normalForm hB hk (mapIntTuple (integerTupleLift F).tuple) =
      ((integerTupleLift F).scale : ℚ) • normalForm hB hk F := by
  rw [integerTupleLift_map_eq, normalForm_smul]

theorem normalForm_integerTupleLift_eq_zero_iff {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (F : PeriodicLocal k) :
    normalForm hB hk (mapIntTuple (integerTupleLift F).tuple) = 0 ↔
      normalForm hB hk F = 0 := by
  rw [normalForm_integerTupleLift]
  exact smul_eq_zero.trans (or_iff_right (integerTupleLift_scale_ne_zero F))

theorem normalForm_integerTupleLift_ne_zero_iff {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (F : PeriodicLocal k) :
    normalForm hB hk (mapIntTuple (integerTupleLift F).tuple) ≠ 0 ↔
      normalForm hB hk F ≠ 0 := by
  exact not_congr (normalForm_integerTupleLift_eq_zero_iff hB hk F)

theorem relativeLocalValue_smul {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (a : ℚ) (F : PeriodicLocal k) (n i : ℕ) :
    relativeLocalValue hk r g (a • F) n i =
      (a : ℝ) * relativeLocalValue hk r g F n i := by
  unfold relativeLocalValue
  simp only [Pi.smul_apply, smul_eq_C_mul, eval₂_mul, eval₂_C]
  rfl

/-- The entire relative-label series scales by the same positive integer. -/
theorem coreLocalSeries_integerTupleLift (B : ℕ) {k : ℕ} (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (F : PeriodicLocal k) (n : ℕ) :
    coreLocalSeries B hk r g (mapIntTuple (integerTupleLift F).tuple) n =
      ((integerTupleLift F).scale : ℝ) * coreLocalSeries B hk r g F n := by
  rw [integerTupleLift_map_eq]
  unfold coreLocalSeries
  simp_rw [relativeLocalValue_smul, mul_div_assoc]
  rw [tsum_mul_left]
  rfl

end

end PrimeGapNormality.Prime.CoreCyclic
