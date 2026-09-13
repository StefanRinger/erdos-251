import PrimeGapNormality.Prime.CorePrimeLocalNormality
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Periodic rational one-gap polynomials

The user-facing nondegeneracy condition is simply that some univariate
component is nonconstant. The actual normal form removes precisely the
constant coefficients. All final conclusions concern the literal full
prime-gap polynomial series.
-/

namespace PrimeGapNormality.Prime.CoreOneGapPolynomialEnd

open CoreCyclic MvPolynomial Finset
open scoped Polynomial
noncomputable section

set_option maxHeartbeats 600000

def tuple {k : ℕ} (P : Fin k → ℚ[X]) : PeriodicLocal k :=
  fun s => (P s).toMvPolynomial (0 : ℕ)

def maxDegree {k : ℕ} (P : Fin k → ℚ[X]) : ℕ :=
  Finset.univ.sup fun s => (P s).natDegree

theorem strip_one_toMvPolynomial (P : ℚ[X]) :
    stripPoly 1 (P.toMvPolynomial (0 : ℕ)) = C (P.coeff 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [map_add, Polynomial.coeff_add] using congrArg₂ (· + ·) hP hQ
  | monomial n c =>
    by_cases hn : n = 0
    · subst n
      simp [Polynomial.toMvPolynomial, Polynomial.aeval_monomial]
    · simp [Polynomial.toMvPolynomial, Polynomial.aeval_monomial,
        Polynomial.coeff_monomial, hn, Ne.symm hn]

/-- The actual normal form deletes the constant term in each component;
it does not mix the remaining one-gap polynomials. -/
theorem normalForm_tuple {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (P : Fin k → ℚ[X]) :
    normalForm hB hk (tuple P) = tuple P - constantTuple (fun s => (P s).coeff 0) := by
  let c : Fin k → ℚ := fun s => (P s).coeff 0
  have hroot : drop hk (tuple P - constantTuple c) = 0 := by
    funext s
    simp [drop_apply, tuple, constantTuple, c, strip_one_toMvPolynomial]
  calc
    normalForm hB hk (tuple P) =
        normalForm hB hk ((tuple P - constantTuple c) + constantTuple c) := by
      rw [sub_add_cancel]
    _ = tuple P - constantTuple c := by
      rw [normalForm_add, normalForm_of_rooted hB hk _ hroot,
        normalForm_constantTuple, add_zero]

/-- Exactly the obstruction expected for one-gap polynomials. -/
theorem normalForm_zero_iff_constant {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (P : Fin k → ℚ[X]) :
    normalForm hB hk (tuple P) = 0 ↔ ∀ s, ∃ a : ℚ, P s = Polynomial.C a := by
  rw [normalForm_tuple hB hk, sub_eq_zero]
  constructor
  · intro h s
    refine ⟨(P s).coeff 0, ?_⟩
    apply Polynomial.toMvPolynomial_injective (0 : ℕ)
    simpa only [tuple, constantTuple, Polynomial.toMvPolynomial_C] using congrFun h s
  · intro h
    funext s
    obtain ⟨a, ha⟩ := h s
    simp [tuple, constantTuple, ha]

theorem normalForm_zero_iff_natDegree_zero {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (P : Fin k → ℚ[X]) : normalForm hB hk (tuple P) = 0 ↔ ∀ s, (P s).natDegree = 0 := by
  rw [normalForm_zero_iff_constant hB hk]
  constructor
  · intro h s
    obtain ⟨a, ha⟩ := h s
    rw [ha]
    exact Polynomial.natDegree_C a
  · intro h s
    exact ⟨(P s).coeff 0, Polynomial.eq_C_of_natDegree_eq_zero (h s)⟩

theorem normalForm_ne_zero_of_nonconstant {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (P : Fin k → ℚ[X]) (hP : ∃ s, ¬ ∃ a : ℚ, P s = Polynomial.C a) :
    normalForm hB hk (tuple P) ≠ 0 := by
  intro hzero
  obtain ⟨s, hs⟩ := hP
  exact hs ((normalForm_zero_iff_constant hB hk P).mp hzero s)

theorem totalDegree_toMvPolynomial_le (P : ℚ[X]) :
    (P.toMvPolynomial (0 : ℕ)).totalDegree ≤ P.natDegree := by
  unfold Polynomial.toMvPolynomial
  rw [Polynomial.aeval_eq_sum_range]
  apply totalDegree_finsetSum_le
  intro n hn
  apply (totalDegree_smul_le (P.coeff n) ((X (0 : ℕ) : MvPolynomial ℕ ℚ) ^ n)).trans
  rw [totalDegree_X_pow]
  exact Nat.lt_succ_iff.mp (mem_range.mp hn)

theorem topDegree_normalForm_le_maxDegree {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (P : Fin k → ℚ[X]) : topDegree (normalForm hB hk (tuple P)) ≤ maxDegree P := by
  apply Finset.sup_le
  intro s hs
  apply normalForm_totalDegree_le hB hk (tuple P) (maxDegree P) _ s
  intro r
  exact (totalDegree_toMvPolynomial_le (P r)).trans
    (Finset.le_sup (f := fun r => (P r).natDegree) (mem_univ r))

theorem localValue_tuple {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (P : Fin k → ℚ[X]) (g : ℕ → ℝ) (n : ℕ) :
    localValue hk phase g (tuple P) n =
      Polynomial.eval₂ (algebraMap ℚ ℝ) (g n) (P (phaseAt hk phase n)) := by
  change MvPolynomial.aeval (fun j => g (n + j))
    ((P (phaseAt hk phase n)).toMvPolynomial (0 : ℕ)) =
      Polynomial.aeval (g n) (P (phaseAt hk phase n))
  simpa only [Nat.add_zero] using MvPolynomial.aeval_toMvPolynomial
    (fun j => g (n + j)) (0 : ℕ) (P (phaseAt hk phase n))

def series (B : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k) (P : Fin k → ℚ[X]) : ℝ :=
  ∑' n : ℕ, Polynomial.eval₂ (algebraMap ℚ ℝ) (primeGap n : ℝ)
    (P (phaseAt hk phase n)) / (B : ℝ) ^ (n + 1)

theorem fullSeries_eq (B : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (P : Fin k → ℚ[X]) :
    coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (tuple P) =
      series B hk phase P := by
  unfold coreCyclicFullSeries series
  simp_rw [localValue_tuple]

theorem summable {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (P : Fin k → ℚ[X]) :
    Summable (fun n : ℕ => Polynomial.eval₂ (algebraMap ℚ ℝ) (primeGap n : ℝ)
      (P (phaseAt hk phase n)) / (B : ℝ) ^ (n + 1)) := by
  simpa only [localValue_tuple] using
    (primeLocalSeries_and_normalForm_summable hB hk phase (tuple P)).1

theorem rational_of_constant {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (P : Fin k → ℚ[X]) (hP : ∀ s, ∃ a : ℚ, P s = Polynomial.C a) :
    ∃ a : ℚ, series B hk phase P = (a : ℝ) := by
  rw [← fullSeries_eq B hk phase P]
  exact coreCyclicFullSeries_rational_of_normalForm_zero hB hk phase (tuple P)
    ((normalForm_zero_iff_constant hB hk P).mpr hP)

theorem weyl_clock_of_D {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (P : Fin k → ℚ[X]) (hP : ∃ s, ¬ ∃ a : ℚ, P s = Polynomial.C a)
    {κ d0 c : ℝ} (hκ : (maxDegree P : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    weylCriterion (B ^ k) (series B hk phase P) := by
  have hκ' : (topDegree (normalForm hB hk (tuple P)) : ℝ) / Real.log (B : ℝ) ≤ κ :=
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (topDegree_normalForm_le_maxDegree hB hk P))
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B)))).trans hκ
  have hW := corePrime_local_weyl_clock_of_D hB hk phase (tuple P)
    (normalForm_ne_zero_of_nonconstant hB hk P hP) hκ' hd0 hc hD
  rwa [fullSeries_eq] at hW

theorem isNormal_of_D {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (P : Fin k → ℚ[X]) (hP : ∃ s, ¬ ∃ a : ℚ, P s = Polynomial.C a)
    {κ d0 c : ℝ} (hκ : (maxDegree P : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    PrimeGapNormality.BFree.IsNormal B (series B hk phase P) :=
  CoreWeylNormality.isNormal_of_weyl hB (weylCriterion_of_pow hB (by omega : 1 ≤ k)
    (weyl_clock_of_D hB hk phase P hP hκ hd0 hc hD))

theorem weyl_clock_of_kuperberg {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (P : Fin k → ℚ[X]) (hP : ∃ s, ¬ ∃ a : ℚ, P s = Polynomial.C a)
    (hK : KuperbergConj13) : weylCriterion (B ^ k) (series B hk phase P) := by
  have hW := corePrime_local_weyl_clock_of_kuperberg hB hk phase (tuple P)
    (normalForm_ne_zero_of_nonconstant hB hk P hP) hK
  rwa [fullSeries_eq] at hW

theorem isNormal_of_kuperberg {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (P : Fin k → ℚ[X]) (hP : ∃ s, ¬ ∃ a : ℚ, P s = Polynomial.C a)
    (hK : KuperbergConj13) : PrimeGapNormality.BFree.IsNormal B (series B hk phase P) :=
  CoreWeylNormality.isNormal_of_weyl hB (weylCriterion_of_pow hB (by omega : 1 ≤ k)
    (weyl_clock_of_kuperberg hB hk phase P hP hK))

theorem irrational_of_kuperberg {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (P : Fin k → ℚ[X]) (hP : ∃ s, ¬ ∃ a : ℚ, P s = Polynomial.C a)
    (hK : KuperbergConj13) : Irrational (series B hk phase P) :=
  weylCriterion_irrational (weyl_clock_of_kuperberg hB hk phase P hP hK)

end
end PrimeGapNormality.Prime.CoreOneGapPolynomialEnd
