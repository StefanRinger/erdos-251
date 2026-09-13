import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite covariance and orbit variance

This file isolates the finite analytic algebra in the quantitative orbit
argument.  It proves that the actual multiplication clock on the unit
additive circle preserves Haar measure, and that a dyadically decaying
pair-covariance estimate gives an `O(1/T)` second moment and an
`O(1/sqrt T)` first moment for the finite time average.

The separate bounded-variation input still has to prove the displayed
pair-covariance estimate for the concrete interval approximants.  Thus no
mixing or covariance assertion is hidden in the statement of the final
finite algebra theorem here.
-/

namespace PrimeGapNormality.Prime.CoreOrbitCovarianceVariance

open Filter Finset MeasureTheory
open scoped BigOperators Topology

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local instance : IsProbabilityMeasure (volume : Measure Circle) :=
  ⟨by simp⟩

/-- The actual expanding clock on the unit additive circle. -/
def circleClock (q : ℕ) (x : Circle) : Circle := q • x

theorem circleClock_continuous (q : ℕ) : Continuous (circleClock q) := by
  unfold circleClock
  exact continuous_const_smul q

theorem circleClock_surjective {q : ℕ} (hq : 0 < q) :
    Function.Surjective (circleClock q) := by
  intro x
  refine ⟨DivisibleBy.div x (q : ℤ), ?_⟩
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  simpa only [circleClock, natCast_zsmul] using DivisibleBy.div_cancel x hqZ

/-- Integer multiplication by a positive clock preserves normalized Haar
measure on the circle. -/
theorem circleClock_measurePreserving {q : ℕ} (hq : 0 < q) :
    MeasurePreserving (circleClock q) (volume : Measure Circle) volume := by
  let e : Circle →+ Circle := nsmulAddMonoidHom q
  have he : (e : Circle → Circle) = circleClock q := rfl
  have hcont : Continuous e := by
    rw [he]
    exact circleClock_continuous q
  have hsurj : Function.Surjective e := by
    simpa only [he] using circleClock_surjective hq
  simpa only [he] using e.measurePreserving hcont hsurj (by simp)

/-- The `h`-fold clock is multiplication by `q^h`. -/
theorem circleClock_iterate (q h : ℕ) (x : Circle) :
    (circleClock q)^[h] x = q ^ h • x := by
  induction h with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_nsmul]
  | succ h ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold circleClock
      rw [smul_smul, pow_succ]
      exact congrArg (fun n : ℕ ↦ n • x) (Nat.mul_comm q (q ^ h))

/-- Reverse geometric mass.  Its exponents are `n,n-1,...,1`. -/
def backwardDyadicMass (n : ℕ) : ℝ :=
  ∑ i ∈ range n, (1 / 2 : ℝ) ^ (n - i)

private theorem backwardDyadicMass_succ (n : ℕ) :
    backwardDyadicMass (n + 1) =
      (1 / 2 : ℝ) * backwardDyadicMass n + 1 / 2 := by
  have hold : (∑ i ∈ range n, (1 / 2 : ℝ) ^ (n + 1 - i)) =
      (1 / 2 : ℝ) * backwardDyadicMass n := by
    unfold backwardDyadicMass
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hin : i < n := mem_range.mp hi
    rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
    ring
  change (∑ i ∈ range (n + 1), (1 / 2 : ℝ) ^ (n + 1 - i)) =
    (1 / 2 : ℝ) * backwardDyadicMass n + 1 / 2
  rw [sum_range_succ, hold]
  norm_num

theorem backwardDyadicMass_le_one (n : ℕ) : backwardDyadicMass n ≤ 1 := by
  induction n with
  | zero => simp only [backwardDyadicMass, range_zero, sum_empty, zero_le_one]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl, backwardDyadicMass_succ]
      nlinarith

/-- Total dyadic covariance kernel on a finite time square. -/
def dyadicCovarianceMass (T : ℕ) : ℝ :=
  ∑ i ∈ range T, ∑ j ∈ range T, (1 / 2 : ℝ) ^ Nat.dist i j

private theorem dyadicCovarianceMass_succ (n : ℕ) :
    dyadicCovarianceMass (n + 1) =
      dyadicCovarianceMass n + 2 * backwardDyadicMass n + 1 := by
  have holdRows :
      (∑ i ∈ range n, ∑ j ∈ range (n + 1),
          (1 / 2 : ℝ) ^ Nat.dist i j) =
        dyadicCovarianceMass n + backwardDyadicMass n := by
    simp_rw [sum_range_succ]
    rw [sum_add_distrib]
    change dyadicCovarianceMass n +
      (∑ i ∈ range n, (1 / 2 : ℝ) ^ Nat.dist i n) =
        dyadicCovarianceMass n + backwardDyadicMass n
    apply congrArg (fun z : ℝ => dyadicCovarianceMass n + z)
    unfold backwardDyadicMass
    apply sum_congr rfl
    intro i hi
    rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt (mem_range.mp hi))]
  have hlastRow :
      (∑ j ∈ range (n + 1), (1 / 2 : ℝ) ^ Nat.dist n j) =
        backwardDyadicMass n + 1 := by
    rw [sum_range_succ]
    congr 1
    · unfold backwardDyadicMass
      apply sum_congr rfl
      intro j hj
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_lt (mem_range.mp hj))]
    · rw [Nat.dist_eq_zero rfl, pow_zero]
  change (∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
    (1 / 2 : ℝ) ^ Nat.dist i j) =
      dyadicCovarianceMass n + 2 * backwardDyadicMass n + 1
  rw [sum_range_succ, holdRows, hlastRow]
  ring

theorem dyadicCovarianceMass_le (T : ℕ) :
    dyadicCovarianceMass T ≤ 3 * (T : ℝ) := by
  induction T with
  | zero => simp [dyadicCovarianceMass]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl, dyadicCovarianceMass_succ]
      have hb := backwardDyadicMass_le_one n
      push_cast
      nlinarith

/-- Pairwise dyadic covariance bounds sum to at most `3*C*T`. -/
theorem covariance_sum_le
    {T : ℕ} {a : ℕ → ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i ∈ range T, ∀ j ∈ range T,
      |a i j| ≤ C * (1 / 2 : ℝ) ^ Nat.dist i j) :
    (∑ i ∈ range T, ∑ j ∈ range T, a i j) ≤ 3 * C * (T : ℝ) := by
  have hpoint : (∑ i ∈ range T, ∑ j ∈ range T, a i j) ≤
      ∑ i ∈ range T, ∑ j ∈ range T,
        C * (1 / 2 : ℝ) ^ Nat.dist i j := by
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    exact (le_abs_self (a i j)).trans (ha i hi j hj)
  have hmass := mul_le_mul_of_nonneg_left (dyadicCovarianceMass_le T) hC
  calc
    (∑ i ∈ range T, ∑ j ∈ range T, a i j) ≤
        ∑ i ∈ range T, ∑ j ∈ range T,
          C * (1 / 2 : ℝ) ^ Nat.dist i j := hpoint
    _ = C * dyadicCovarianceMass T := by
      unfold dyadicCovarianceMass
      simp only [mul_sum]
    _ ≤ C * (3 * (T : ℝ)) := hmass
    _ = 3 * C * (T : ℝ) := by ring

/-- Finite average of a family of observables. -/
def finiteTimeMean {α : Type*} (g : ℕ → α → ℝ) (T : ℕ) (x : α) : ℝ :=
  (∑ h ∈ range T, g h x) / (T : ℝ)

theorem integral_finiteTimeMean_sq_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : ℕ → α → ℝ) {T : ℕ}
    (hprod : ∀ i ∈ range T, ∀ j ∈ range T,
      Integrable (fun x ↦ g i x * g j x) μ) :
    (∫ x, finiteTimeMean g T x ^ 2 ∂μ) =
      (∑ i ∈ range T, ∑ j ∈ range T,
        ∫ x, g i x * g j x ∂μ) / (T : ℝ) ^ 2 := by
  have hfun : (fun x ↦ finiteTimeMean g T x ^ 2) =
      fun x ↦ (∑ i ∈ range T, ∑ j ∈ range T, g i x * g j x) /
        (T : ℝ) ^ 2 := by
    funext x
    unfold finiteTimeMean
    rw [div_pow, sq]
    congr 1
    rw [sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum]
  rw [hfun, integral_div]
  rw [integral_finsetSum (range T) (fun i hi ↦
    integrable_finsetSum (range T) (fun j hj ↦ hprod i hi j hj))]
  apply congrArg (fun z : ℝ ↦ z / (T : ℝ) ^ 2)
  apply sum_congr rfl
  intro i hi
  exact integral_finsetSum (range T) (fun j hj ↦ hprod i hi j hj)

/-- Pairwise dyadic covariance decay gives the finite `O(1/T)` variance
bound. -/
theorem integral_finiteTimeMean_sq_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : ℕ → α → ℝ) {T : ℕ} (hT : 0 < T) {C : ℝ} (hC : 0 ≤ C)
    (hprod : ∀ i ∈ range T, ∀ j ∈ range T,
      Integrable (fun x ↦ g i x * g j x) μ)
    (hcov : ∀ i ∈ range T, ∀ j ∈ range T,
      |∫ x, g i x * g j x ∂μ| ≤
        C * (1 / 2 : ℝ) ^ Nat.dist i j) :
    (∫ x, finiteTimeMean g T x ^ 2 ∂μ) ≤ 3 * C / (T : ℝ) := by
  rw [integral_finiteTimeMean_sq_eq g hprod]
  have hsum := covariance_sum_le hC hcov
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  apply (div_le_iff₀ (sq_pos_of_pos hTR)).2
  have hcancel : (3 * C / (T : ℝ)) * (T : ℝ) ^ 2 =
      3 * C * (T : ℝ) := by field_simp [hTR.ne']
  rw [hcancel]
  exact hsum

private theorem integral_abs_le_sqrt_of_integral_sq_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {K : ℝ}
    (hK : 0 < K) (hf : Integrable f μ)
    (hfSq : Integrable (fun x ↦ f x ^ 2) μ)
    (hint : (∫ x, f x ^ 2 ∂μ) ≤ K) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt K := by
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hpoint : ∀ x, |f x| ≤
      f x ^ 2 / (2 * Real.sqrt K) + Real.sqrt K / 2 := by
    intro x
    have hsq := sq_nonneg (|f x| - Real.sqrt K)
    have habsSq : |f x| ^ 2 = f x ^ 2 := sq_abs (f x)
    have hrewrite : f x ^ 2 / (2 * Real.sqrt K) + Real.sqrt K / 2 =
        (f x ^ 2 + Real.sqrt K ^ 2) / (2 * Real.sqrt K) := by
      field_simp [hsqrt.ne'] <;> ring
    rw [hrewrite]
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hsqrt)).2
    nlinarith [habsSq]
  have hright : Integrable
      (fun x ↦ f x ^ 2 / (2 * Real.sqrt K) + Real.sqrt K / 2) μ :=
    (hfSq.div_const _).add (integrable_const _)
  have hmono := integral_mono_ae hf.abs hright (Eventually.of_forall hpoint)
  calc
    (∫ x, |f x| ∂μ) ≤
        ∫ x, f x ^ 2 / (2 * Real.sqrt K) + Real.sqrt K / 2 ∂μ := hmono
    _ = (∫ x, f x ^ 2 ∂μ) / (2 * Real.sqrt K) + Real.sqrt K / 2 := by
      rw [integral_add (hfSq.div_const (2 * Real.sqrt K)) (integrable_const _), integral_div]
      simp
    _ ≤ K / (2 * Real.sqrt K) + Real.sqrt K / 2 :=
      _root_.add_le_add
        (div_le_div_of_nonneg_right hint
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsqrt.le))
        (le_refl (Real.sqrt K / 2))
    _ = Real.sqrt K := by
      have hsqrtSq := Real.sq_sqrt hK.le
      field_simp [hsqrt.ne']
      nlinarith

/-- The corresponding finite `O(1/sqrt T)` first-moment bound. -/
theorem integral_abs_finiteTimeMean_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    (g : ℕ → α → ℝ) {T : ℕ} (hT : 0 < T) {C : ℝ} (hC : 0 < C)
    (hg : ∀ i ∈ range T, Integrable (g i) μ)
    (hprod : ∀ i ∈ range T, ∀ j ∈ range T,
      Integrable (fun x ↦ g i x * g j x) μ)
    (hcov : ∀ i ∈ range T, ∀ j ∈ range T,
      |∫ x, g i x * g j x ∂μ| ≤
        C * (1 / 2 : ℝ) ^ Nat.dist i j) :
    (∫ x, |finiteTimeMean g T x| ∂μ) ≤
      Real.sqrt (3 * C / (T : ℝ)) := by
  have hmean : Integrable (finiteTimeMean g T) μ := by
    unfold finiteTimeMean
    exact (integrable_finsetSum (range T) hg).div_const _
  have hmeanSq : Integrable (fun x ↦ finiteTimeMean g T x ^ 2) μ := by
    have hsum : Integrable
        (fun x ↦ ∑ i ∈ range T, ∑ j ∈ range T, g i x * g j x) μ :=
      integrable_finsetSum (range T) fun i hi ↦
        integrable_finsetSum (range T) fun j hj ↦ hprod i hi j hj
    have hfun : (fun x ↦ finiteTimeMean g T x ^ 2) =
        fun x ↦ (∑ i ∈ range T, ∑ j ∈ range T, g i x * g j x) /
          (T : ℝ) ^ 2 := by
      funext x
      unfold finiteTimeMean
      rw [div_pow, sq, sum_mul]
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [mul_sum]
    rw [hfun]
    exact hsum.div_const _
  have hK : 0 < 3 * C / (T : ℝ) := by positivity
  exact integral_abs_le_sqrt_of_integral_sq_le hK hmean hmeanSq
    (integral_finiteTimeMean_sq_le g hT hC.le hprod hcov)

end

end PrimeGapNormality.Prime.CoreOrbitCovarianceVariance
