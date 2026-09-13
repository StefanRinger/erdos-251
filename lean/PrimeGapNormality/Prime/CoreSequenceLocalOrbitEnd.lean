import PrimeGapNormality.Prime.CoreSequenceResiduePassage
import PrimeGapNormality.Prime.CoreCyclicOrbitIdentification
import PrimeGapNormality.Prime.CoreWeylNormality
import PrimeGapNormality.Prime.Components

/-! Sequence-independent final orbit adapter. This reuses the proven
integer-series recurrence and physical-window assembly. It deliberately
retains the explicit subsequence reference bound: neither the generic
S/T supplier nor the unconditional rough arithmetic is asserted here. -/

namespace PrimeGapNormality.Prime.CoreSequenceLocalOrbitEnd

open Finset Filter MvPolynomial CoreCyclic
open scoped Topology
noncomputable section

def localOrbit (B : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (g : ℕ → ℤ) (F : Fin k → MvPolynomial ℕ ℤ) (n : ℕ) : AddCircle (1 : ℝ) :=
  coreLocalSeriesCircle B hk phase (fun j => (g j : ℝ)) (mapIntTuple F) n

theorem localOrbit_add_period {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (g : ℕ → ℤ) (hg : HasPolynomialGrowth fun n => (g n : ℝ))
    (F : Fin k → MvPolynomial ℕ ℤ) (n : ℕ) :
    localOrbit B hk phase g F (n + k) = B ^ k • localOrbit B hk phase g F n :=
  coreLocalSeriesCircle_add_period_of_intTuple hB hk phase g hg F n

private theorem clock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) : 2 ≤ B ^ k := by
  have heq : k = k - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [heq, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

private theorem fourier_nsmul (z : ℤ) (C q : ℕ) (x : ℝ) :
    fourier z (C ^ q • (x : AddCircle (1 : ℝ))) =
      e ((z : ℝ) * (C : ℝ) ^ q * x) := by
  rw [← AddCircle.coe_nsmul, fourier_coe_apply]
  simp only [nsmul_eq_mul, Nat.cast_pow, e, Complex.ofReal_one, div_one,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

/-- A genuine physical-window reference bound yields the full local-series
Weyl conclusion, for any increasing integer sequence used as the physical
indexing clock. No prime-counting asymptotic is required by this adapter. -/
theorem fullSeries_weyl_clock_of_subsequence_reference
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (g : ℕ → ℤ) (hg : HasPolynomialGrowth fun n => (g n : ℝ))
    (F : Fin k → MvPolynomial ℕ ℤ)
    (hbound : CoreResidueDigitalReference.SubsequenceReferenceBounds
      (localOrbit B hk phase g F) (fun X => seqCount a X)
      (CoreSequenceResiduePassage.seqCountDifference a)) :
    weylCriterion (B ^ k)
      (coreCyclicFullSeries B hk phase (fun j => (g j : ℝ)) (mapIntTuple F)) := by
  intro z hz
  have hchar := CoreSequenceResiduePassage.residue_character_cesaro_of_subsequence_reference
    ha hcount (clock_ge hB hk) (by omega : 1 ≤ k) (r := 0) hk
    (localOrbit B hk phase g F) (localOrbit_add_period hB hk phase g hg F) hbound hz
  unfold CesaroMeanVanishing at hchar
  apply hchar.congr'
  exact Eventually.of_forall fun N => by
    apply congrArg (fun v : ℂ => v / (N : ℂ))
    apply sum_congr rfl
    intro q hq
    have horbit := coreLocalSeriesCircle_progression_zero_eq_fullSeries_of_intTuple
      hB hk phase g hg F q
    change fourier z (coreLocalSeriesCircle B hk phase (fun j => (g j : ℝ))
      (mapIntTuple F) (q * k + 0)) = _
    -- Normalize the progression exactly; omega does not commute two variable factors.
    rw [show q * k + 0 = k * q by simp only [Nat.add_zero, Nat.mul_comm], horbit]
    exact fourier_nsmul z (B ^ k) q _

theorem fullSeries_isNormal_of_subsequence_reference
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (g : ℕ → ℤ) (hg : HasPolynomialGrowth fun n => (g n : ℝ))
    (F : Fin k → MvPolynomial ℕ ℤ)
    (hbound : CoreResidueDigitalReference.SubsequenceReferenceBounds
      (localOrbit B hk phase g F) (fun X => seqCount a X)
      (CoreSequenceResiduePassage.seqCountDifference a)) :
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk phase (fun j => (g j : ℝ)) (mapIntTuple F)) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (weylCriterion_of_pow hB (by omega : 1 ≤ k)
      (fullSeries_weyl_clock_of_subsequence_reference ha hcount hB hk phase g hg F hbound))

end
end PrimeGapNormality.Prime.CoreSequenceLocalOrbitEnd
