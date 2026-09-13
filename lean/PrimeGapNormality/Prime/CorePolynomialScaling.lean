import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform scaling to the top homogeneous component

The estimate is an exact finite monomial calculation. Only variables in
the polynomial's actual support need to be bounded. The degree parameter
is an upper bound, not an assumption that the degree remains equal to it
after specialization: if the degree drops, the limiting component is zero.
-/

namespace PrimeGapNormality.Prime.CorePolynomialScaling

open MvPolynomial Finset Filter
open scoped Topology BigOperators

noncomputable section

variable {σ : Type*}

def monomialValue (m : σ →₀ ℕ) (x : σ → ℝ) : ℝ :=
  ∏ i ∈ m.support, x i ^ m i

/-- Literal monomial scaling, including the constant monomial. -/
theorem monomialValue_scale (m : σ →₀ ℕ) (x : σ → ℝ) (G : ℝ) :
    monomialValue m (fun i => G * x i) = G ^ m.degree * monomialValue m x := by
  classical
  simp only [monomialValue, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, Finsupp.degree_apply]

theorem monomialValue_abs_le (m : σ →₀ ℕ) (x : σ → ℝ) {A : ℝ}
    (hx : ∀ i ∈ m.support, |x i| ≤ A) :
    |monomialValue m x| ≤ A ^ m.degree := by
  classical
  rw [monomialValue, abs_prod, Finsupp.degree_apply, ← prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro i _
    exact abs_nonneg _
  · intro i hi
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hx i hi) _

/-- A finite coefficient constant, independent of the scale `G`. -/
def coefficientBound (F : MvPolynomial σ ℝ) (A : ℝ) : ℝ :=
  ∑ m ∈ F.support, |F.coeff m| * A ^ m.degree

theorem coefficientBound_nonneg (F : MvPolynomial σ ℝ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ coefficientBound F A :=
  sum_nonneg fun m _ => mul_nonneg (abs_nonneg _) (pow_nonneg hA _)

theorem eval_homogeneousComponent_sum (F : MvPolynomial σ ℝ) (d : ℕ)
    (x : σ → ℝ) :
    eval x (homogeneousComponent d F) =
      ∑ m ∈ F.support, if m.degree = d then F.coeff m * monomialValue m x else 0 := by
  classical
  rw [homogeneousComponent_apply]
  simp only [map_sum, eval_monomial, sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m.degree = d
  · simp only [if_pos hm, eval_monomial, monomialValue, Finsupp.prod]
  · simp only [if_neg hm, map_zero]

/-- An exact remainder formula. The degree-`d` terms cancel, and all
remaining terms retain their actual powers of `G`. -/
theorem scaled_eval_sub_top (F : MvPolynomial σ ℝ) (d : ℕ)
    (x : σ → ℝ) {G : ℝ} (hG : G ≠ 0) :
    eval (fun i => G * x i) F / G ^ d - eval x (homogeneousComponent d F) =
      ∑ m ∈ F.support, if m.degree = d then 0 else
        F.coeff m * monomialValue m x * (G ^ m.degree / G ^ d) := by
  classical
  rw [eval_eq, eval_homogeneousComponent_sum]
  change (∑ m ∈ F.support, F.coeff m * monomialValue m (fun i => G * x i)) /
      G ^ d - (∑ m ∈ F.support,
        if m.degree = d then F.coeff m * monomialValue m x else 0) = _
  rw [Finset.sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m _
  rw [monomialValue_scale]
  by_cases hmd : m.degree = d
  · simp only [hmd, ite_true]
    field_simp [pow_ne_zero d hG]
    <;> simp <;> ring
  · simp only [hmd, if_false, sub_zero]
    ring

private theorem power_ratio_le_inverse {G : ℝ} (hG : 1 ≤ G) {e d : ℕ}
    (hed : e < d) : G ^ e / G ^ d ≤ 1 / G := by
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  apply (div_le_div_iff₀ (pow_pos hG0 d) hG0).2
  rw [one_mul, ← pow_succ]
  exact pow_le_pow_right₀ hG (Nat.succ_le_of_lt hed)

/-- Explicit uniform compact-frame error, with no asymptotic premise.
The stated `A ≥ 1` can even be weakened to `A ≥ 0`. -/
theorem scaled_eval_sub_top_abs_le (F : MvPolynomial σ ℝ) (d : ℕ)
    (hd : F.totalDegree ≤ d) {A G : ℝ} (hA : 0 ≤ A) (hG : 1 ≤ G)
    (x : σ → ℝ) (hx : ∀ i ∈ F.vars, |x i| ≤ A) :
    |eval (fun i => G * x i) F / G ^ d - eval x (homogeneousComponent d F)| ≤
      coefficientBound F A / G := by
  classical
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  rw [scaled_eval_sub_top F d x hG0.ne', coefficientBound, Finset.sum_div]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro m hm
  have hmd : m.degree ≤ d := (le_totalDegree hm).trans hd
  by_cases heq : m.degree = d
  · simp only [if_pos heq, abs_zero]
    exact div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hA _)) hG0.le
  · rw [if_neg heq, abs_mul, abs_mul,
      abs_of_nonneg (div_nonneg (pow_nonneg hG0.le _) (pow_nonneg hG0.le _))]
    have hmabs : |monomialValue m x| ≤ A ^ m.degree :=
      monomialValue_abs_le m x (fun i hi =>
        hx i ((mem_vars_iff_mem_support i).2 ⟨m, hm, hi⟩))
    have hratio : G ^ m.degree / G ^ d ≤ 1 / G :=
      power_ratio_le_inverse hG (lt_of_le_of_ne hmd heq)
    calc
      |F.coeff m| * |monomialValue m x| * (G ^ m.degree / G ^ d) ≤
          (|F.coeff m| * A ^ m.degree) * (1 / G) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmabs (abs_nonneg _)) hratio
          (div_nonneg (pow_nonneg hG0.le _) (pow_nonneg hG0.le _))
          (mul_nonneg (abs_nonneg _) (pow_nonneg hA _))
      _ = (|F.coeff m| * A ^ m.degree) / G := by ring

/-- Uniform convergence along any scale tending to infinity. This is
uniform on the actual polynomial variables, even for an infinite variable
type; in finite dimensions it applies in particular to every compact box. -/
theorem tendstoUniformlyOn_scaled_eval {ι : Type*} {l : Filter ι}
    (G : ι → ℝ) (hG : Tendsto G l atTop)
    (F : MvPolynomial σ ℝ) (d : ℕ) (hd : F.totalDegree ≤ d)
    {A : ℝ} (hA : 0 ≤ A) :
    TendstoUniformlyOn
      (fun t x => eval (fun i => G t * x i) F / G t ^ d)
      (fun x => eval x (homogeneousComponent d F)) l
      {x : σ → ℝ | ∀ i ∈ F.vars, |x i| ≤ A} := by
  have herror : Tendsto (fun t => coefficientBound F A / G t) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hG
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  filter_upwards [hG.eventually (eventually_ge_atTop 1),
    herror.eventually_lt_const hε] with t ht hsmall
  intro x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (scaled_eval_sub_top_abs_le F d hd hA ht x hx).trans_lt hsmall

end

end PrimeGapNormality.Prime.CorePolynomialScaling
