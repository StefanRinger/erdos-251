import PrimeGapNormality.Prime.CoreResidueSubsequenceReference
import PrimeGapNormality.Prime.CoreCyclicOrbitIdentification
import PrimeGapNormality.Prime.CoreWeylNormality
import PrimeGapNormality.Prime.Components

/-!
# End of the integer local-orbit route

For an actual integer-coefficient periodic tuple, polynomial growth of the
prime gaps proves both convergence and the literal `k`-step circle
recurrence.  An explicit subsequence reference bound then gives character
cancellation on the zero residue class of prime indices.  The exact orbit
identity identifies this with Weyl's criterion for the genuine full local
series at base `B^k`; finite interleaving descends to base `B`.

This is an intermediate model-bound consumer.  It does not claim that its
subsequence reference bound follows from the D-only arithmetic endpoint.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Finset Filter MvPolynomial
open scoped Topology

noncomputable section

/-- The actual relative-label local prime-gap series, viewed modulo one. -/
def primeLocalOrbit
    (B : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ) (n : ℕ) : AddCircle (1 : ℝ) :=
  coreLocalSeriesCircle B hk phase (fun q ↦ (primeGap q : ℝ))
    (mapIntTuple F) n

/-- Its period-step recurrence is a theorem from integer coefficients and
the unconditional quadratic growth of the prime gaps. -/
theorem primeLocalOrbit_add_period
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ) (n : ℕ) :
    primeLocalOrbit B hk phase F (n + k) =
      B ^ k • primeLocalOrbit B hk phase F n := by
  simpa only [primeLocalOrbit, Int.cast_natCast] using
    coreLocalSeriesCircle_add_period_of_intTuple hB hk phase
      (fun q ↦ (primeGap q : ℤ))
      (by simpa only [Int.cast_natCast] using primeGap_hasPolynomialGrowth)
      F n

/-- The defining genuine full local prime-gap series is summable. -/
theorem primeLocalFullSeries_summable
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ) :
    Summable fun n : ℕ ↦
      localValue hk phase (fun q ↦ (primeGap q : ℝ)) (mapIntTuple F) n /
        (B : ℝ) ^ (n + 1) := by
  simpa only [Nat.zero_add] using
    primeGap_localSeries_summable hB hk phase (mapIntTuple F) 0

private theorem fourier_coe_eq_e (z : ℤ) (x : ℝ) :
    fourier z (x : AddCircle (1 : ℝ)) = e ((z : ℝ) * x) := by
  rw [fourier_coe_apply]
  simp only [e, Complex.ofReal_one, div_one, Complex.ofReal_mul,
    Complex.ofReal_intCast]
  congr 1
  ring

private theorem fourier_nsmul_coe_eq_e
    (z : ℤ) (C q : ℕ) (x : ℝ) :
    fourier z (C ^ q • (x : AddCircle (1 : ℝ))) =
      e ((z : ℝ) * (C : ℝ) ^ q * x) := by
  rw [← AddCircle.coe_nsmul, fourier_coe_eq_e]
  simp only [nsmul_eq_mul, Nat.cast_pow]
  congr 1
  ring

/-- The zero-residue character mean is exactly the Weyl mean of the full
series under the clock `B^k`. -/
theorem primeLocalFullSeries_weyl_pow_of_subsequence_reference
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ)
    (hbound : CoreResidueDigitalReference.SubsequenceReferenceBounds
      (primeLocalOrbit B hk phase F)
      (fun X ↦ Nat.primeCounting X) windowNX) :
    weylCriterion (B ^ k)
      (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
        (mapIntTuple F)) := by
  have hk1 : 1 ≤ k := by omega
  have hclock : 2 ≤ B ^ k := by
    have hsplit : k = k - 1 + 1 := (Nat.sub_add_cancel hk1).symm
    rw [hsplit, pow_succ]
    have hBpos : 0 < B := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hB
    have hpowpos : 0 < B ^ (k - 1) := pow_pos hBpos _
    exact hB.trans (Nat.le_mul_of_pos_left B hpowpos)
  intro z hz
  have hchar :=
    CorePrimeResiduePassage.primeResidue_character_cesaro_of_subsequence_reference
      hclock hk1 (r := 0) (by omega : 0 < k)
      (primeLocalOrbit B hk phase F)
      (primeLocalOrbit_add_period hB hk phase F) hbound hz
  unfold CesaroMeanVanishing at hchar
  apply hchar.congr'
  exact Eventually.of_forall fun N ↦ by
    apply congrArg (fun v : ℂ ↦ v / (N : ℂ))
    apply sum_congr rfl
    intro q hq
    have horbit :
        coreLocalSeriesCircle B hk phase (fun n ↦ (primeGap n : ℝ))
            (mapIntTuple F) (k * q) =
          (B ^ k) ^ q •
            (coreCyclicFullSeries B hk phase (fun n ↦ (primeGap n : ℝ))
              (mapIntTuple F) : AddCircle (1 : ℝ)) := by
      simpa only [Int.cast_natCast] using
        coreLocalSeriesCircle_progression_zero_eq_fullSeries_of_intTuple
          hB hk phase (fun n ↦ (primeGap n : ℤ))
          (by simpa only [Int.cast_natCast] using primeGap_hasPolynomialGrowth) F q
    change fourier z
      (coreLocalSeriesCircle B hk phase (fun n ↦ (primeGap n : ℝ))
        (mapIntTuple F) (q * k + 0)) = _
    rw [show q * k + 0 = k * q by simp only [Nat.add_zero, Nat.mul_comm], horbit]
    exact fourier_nsmul_coe_eq_e z (B ^ k) q _

/-- Interleaving the `k` clock residues descends the preceding Weyl result
to the original base. -/
theorem primeLocalFullSeries_weyl_of_subsequence_reference
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ)
    (hbound : CoreResidueDigitalReference.SubsequenceReferenceBounds
      (primeLocalOrbit B hk phase F)
      (fun X ↦ Nat.primeCounting X) windowNX) :
    weylCriterion B
      (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
        (mapIntTuple F)) :=
  weylCriterion_of_pow hB (by omega : 1 ≤ k)
    (primeLocalFullSeries_weyl_pow_of_subsequence_reference
      hB hk phase F hbound)

/-- Literal base-`B` digit normality of the genuine full local series. -/
theorem primeLocalFullSeries_isNormal_of_subsequence_reference
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ)
    (hbound : CoreResidueDigitalReference.SubsequenceReferenceBounds
      (primeLocalOrbit B hk phase F)
      (fun X ↦ Nat.primeCounting X) windowNX) :
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
        (mapIntTuple F)) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (primeLocalFullSeries_weyl_of_subsequence_reference
      hB hk phase F hbound)

/-- Irrationality follows from the same actual Weyl criterion. -/
theorem primeLocalFullSeries_irrational_of_subsequence_reference
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ)
    (hbound : CoreResidueDigitalReference.SubsequenceReferenceBounds
      (primeLocalOrbit B hk phase F)
      (fun X ↦ Nat.primeCounting X) windowNX) :
    Irrational
      (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
        (mapIntTuple F)) :=
  weylCriterion_irrational
    (primeLocalFullSeries_weyl_of_subsequence_reference
      hB hk phase F hbound)

/-- Combined endpoint, with summability retained as an explicit theorem
rather than an input. -/
theorem primeLocalFullSeries_converges_normal_and_irrational
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : Fin k → MvPolynomial ℕ ℤ)
    (hbound : CoreResidueDigitalReference.SubsequenceReferenceBounds
      (primeLocalOrbit B hk phase F)
      (fun X ↦ Nat.primeCounting X) windowNX) :
    (Summable fun n : ℕ ↦
      localValue hk phase (fun q ↦ (primeGap q : ℝ)) (mapIntTuple F) n /
        (B : ℝ) ^ (n + 1)) ∧
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
        (mapIntTuple F)) ∧
    Irrational
      (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ))
        (mapIntTuple F)) :=
  ⟨primeLocalFullSeries_summable hB hk phase F,
    primeLocalFullSeries_isNormal_of_subsequence_reference hB hk phase F hbound,
    primeLocalFullSeries_irrational_of_subsequence_reference hB hk phase F hbound⟩

end

end PrimeGapNormality.Prime.CoreCyclic
