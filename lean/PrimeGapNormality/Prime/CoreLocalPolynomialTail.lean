import PrimeGapNormality.Prime.CoreCyclicSeriesConvergence
import PrimeGapNormality.Prime.CharacterRemainder

/-!
# First-moment tails for local polynomials

This file begins the local-polynomial truncation step with the finite
algebraic estimate used in the paper.  A fixed rational local polynomial
of degree at most `d`, evaluated on positive gaps, is bounded by its
coefficient mass times the `d`-th power of the sum of the gaps in its
finite window.

The subsequent geometric tail comparison can therefore use the existing
first-gap tail estimates; no moments of powers of prime gaps are assumed.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Finset MvPolynomial
open scoped BigOperators

noncomputable section

/-- Sum of the absolute values of the real images of the coefficients. -/
def localPolyCoeffMass (p : LocalPoly) : ℝ :=
  ∑ m ∈ p.support, |((p.coeff m : ℚ) : ℝ)|

theorem localPolyCoeffMass_nonneg (p : LocalPoly) :
    0 ≤ localPolyCoeffMass p :=
  sum_nonneg fun _ _ ↦ abs_nonneg _

private theorem monomialValue_le_sum_pow
    {m : ℕ →₀ ℕ} {w d : ℕ} {z : ℕ → ℝ}
    (hmw : ∀ i ∈ m.support, i ≤ w)
    (hmd : m.sum (fun _ e ↦ e) ≤ d)
    (hz : ∀ i, 0 ≤ z i)
    (hS : 1 ≤ ∑ i ∈ range (w + 1), z i) :
    (∏ i ∈ m.support, z i ^ m i) ≤
      (∑ i ∈ range (w + 1), z i) ^ d := by
  let S : ℝ := ∑ i ∈ range (w + 1), z i
  have hmem : ∀ i ∈ m.support, i ∈ range (w + 1) := by
    intro i hi
    exact mem_range.mpr (Nat.lt_succ_of_le (hmw i hi))
  have hzi : ∀ i ∈ m.support, z i ≤ S := by
    intro i hi
    exact single_le_sum (fun j _ ↦ hz j) (hmem i hi)
  have hprod :
      (∏ i ∈ m.support, z i ^ m i) ≤
        ∏ i ∈ m.support, S ^ m i :=
    prod_le_prod
      (fun i _ ↦ pow_nonneg (hz i) _)
      (fun i hi ↦ pow_le_pow_left₀ (hz i) (hzi i hi) _)
  have hdegree : ∑ i ∈ m.support, m i ≤ d := by
    simpa only [Finsupp.sum] using hmd
  calc
    (∏ i ∈ m.support, z i ^ m i) ≤
        ∏ i ∈ m.support, S ^ m i := hprod
    _ = S ^ (∑ i ∈ m.support, m i) :=
      Finset.prod_pow_eq_pow_sum m.support (fun i ↦ m i) S
    _ ≤ S ^ d := pow_le_pow_right₀ hS hdegree

/-- Finite local-polynomial bound with the lower bound on the window sum
stated explicitly. -/
theorem abs_eval₂_le_localPolyCoeffMass_mul_sum_pow
    (p : LocalPoly) (w d : ℕ) (z : ℕ → ℝ)
    (hw : ∀ i ∈ p.vars, i ≤ w)
    (hd : p.totalDegree ≤ d)
    (hz : ∀ i, 0 ≤ z i)
    (hS : 1 ≤ ∑ i ∈ range (w + 1), z i) :
    |eval₂ (algebraMap ℚ ℝ) z p| ≤
      localPolyCoeffMass p * (∑ i ∈ range (w + 1), z i) ^ d := by
  rw [eval₂_eq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    (∑ m ∈ p.support,
        |(algebraMap ℚ ℝ) (p.coeff m) *
          ∏ i ∈ m.support, z i ^ m i|) ≤
        ∑ m ∈ p.support,
          |((p.coeff m : ℚ) : ℝ)| *
            (∑ i ∈ range (w + 1), z i) ^ d := by
      apply sum_le_sum
      intro m hm
      have hmw : ∀ i ∈ m.support, i ≤ w := by
        intro i hi
        apply hw i
        exact (mem_vars_iff_mem_support i).2 ⟨m, hm, hi⟩
      have hmd : m.sum (fun _ e ↦ e) ≤ d :=
        (le_totalDegree hm).trans hd
      have hmono := monomialValue_le_sum_pow hmw hmd hz hS
      have hprod0 : 0 ≤ ∏ i ∈ m.support, z i ^ m i :=
        prod_nonneg fun i _ ↦ pow_nonneg (hz i) _
      rw [abs_mul, abs_of_nonneg hprod0]
      exact mul_le_mul_of_nonneg_left hmono (abs_nonneg _)
    _ = localPolyCoeffMass p *
          (∑ i ∈ range (w + 1), z i) ^ d := by
      unfold localPolyCoeffMass
      rw [Finset.sum_mul]

/-- Paper form: positive gaps automatically make the finite window sum at
least one. -/
theorem abs_eval₂_le_localPolyCoeffMass_mul_sum_pow_of_one_le
    (p : LocalPoly) (w d : ℕ) (z : ℕ → ℝ)
    (hw : ∀ i ∈ p.vars, i ≤ w)
    (hd : p.totalDegree ≤ d)
    (hz : ∀ i, 1 ≤ z i) :
    |eval₂ (algebraMap ℚ ℝ) z p| ≤
      localPolyCoeffMass p * (∑ i ∈ range (w + 1), z i) ^ d := by
  apply abs_eval₂_le_localPolyCoeffMass_mul_sum_pow p w d z hw hd
  · exact fun i ↦ zero_le_one.trans (hz i)
  · calc
      (1 : ℝ) ≤ z 0 := hz 0
      _ ≤ ∑ i ∈ range (w + 1), z i :=
        single_le_sum (fun i _ ↦ zero_le_one.trans (hz i))
          (mem_range.mpr (Nat.zero_lt_succ w))

/-- A coefficient bound uniform over the finite cyclic tuple. -/
def localTupleCoeffMass {k : ℕ} (F : PeriodicLocal k) : ℝ :=
  ∑ r : Fin k, localPolyCoeffMass (F r)

theorem localTupleCoeffMass_nonneg {k : ℕ} (F : PeriodicLocal k) :
    0 ≤ localTupleCoeffMass F :=
  sum_nonneg fun _ _ ↦ localPolyCoeffMass_nonneg _

/-- Uniform local-value estimate along an arbitrary positive gap sequence. -/
theorem abs_localValue_le_localTupleCoeffMass_mul_sum_pow
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : PeriodicLocal k)
    (w d n : ℕ) (g : ℕ → ℝ)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hg : ∀ i, 1 ≤ g i) :
    |localValue hk r g F n| ≤
      localTupleCoeffMass F *
        (∑ i ∈ range (w + 1), g (n + i)) ^ d := by
  let s := phaseAt hk r n
  have hp := abs_eval₂_le_localPolyCoeffMass_mul_sum_pow_of_one_le
    (F s) w d (fun i ↦ g (n + i)) (hw s) (hd s) (fun i ↦ hg (n + i))
  have hmass : localPolyCoeffMass (F s) ≤ localTupleCoeffMass F := by
    exact single_le_sum (fun q _ ↦ localPolyCoeffMass_nonneg (F q)) (mem_univ s)
  have hpow0 : 0 ≤ (∑ i ∈ range (w + 1), g (n + i)) ^ d :=
    pow_nonneg (sum_nonneg fun i _ ↦ zero_le_one.trans (hg (n + i))) _
  unfold localValue
  exact hp.trans (mul_le_mul_of_nonneg_right hmass hpow0)

end

end PrimeGapNormality.Prime.CoreCyclic
