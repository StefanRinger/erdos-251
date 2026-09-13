import PrimeGapNormality.Prime.CoreOneGapPolynomialEnd
import PrimeGapNormality.Prime.CoreOneGapWeights
import PrimeGapNormality.Prime.CoreLocalRelations

/-!
# The two telescoping worked examples in the paper

This file specializes the public cyclic-normal-form API to the last two
rows of the paper's period-one table.  The indexing is the project's
0-based indexing: `primeGap 0` is the paper's `g₁`.

The second example is the linear **prime-gap** series plus one.  It is not
the prime-position series.  Its high-degree summand is an exact telescope,
so its canonical effective degree is one for every `M` (in particular for
the paper's `M ≥ 2`).
-/

namespace PrimeGapNormality.Prime.CorePaperWorkedExamples

open MvPolynomial
open CoreCyclic

noncomputable section

/-- The unique phase of a period-one tuple. -/
def phaseOne : Fin 1 := 0

/-- The period-one rooted monomial `u₀^M`. -/
def rootPowerTuple (M : ℕ) : PeriodicLocal 1 :=
  fun _ => (X 0 : LocalPoly) ^ M

/-- The literal numerator `B u₀^M - u₁^M`. -/
def telescopingNumerator (B M : ℕ) : PeriodicLocal 1 :=
  cyclicTelescope B (by omega : 0 < 1) (rootPowerTuple M)

/-- The literal numerator `u₀ + B u₀^M - u₁^M`. -/
def degreeDropNumerator (B M : ℕ) : PeriodicLocal 1 :=
  CoreOneGapWeights.tuple (fun _ : Fin 1 => (1 : ℚ)) +
    telescopingNumerator B M

/-- In the project's 0-based indexing, the first prime gap is the paper's
`g₁ = p₂ - p₁ = 3 - 2 = 1`. -/
@[simp] theorem primeGap_zero : primeGap 0 = 1 := by
  simp [primeGap, nthPrime]

/-- Coordinatewise, the cyclic definition is exactly the displayed
period-one telescope `B u₀^M-u₁^M`. -/
theorem telescopingNumerator_apply (B M : ℕ) (s : Fin 1) :
    telescopingNumerator B M s =
      C (B : ℚ) * (X 0 : LocalPoly) ^ M - (X 1 : LocalPoly) ^ M := by
  simp only [telescopingNumerator, cyclicTelescope_apply, rootPowerTuple,
    map_pow, rename_X, Nat.zero_add]

/-- Coordinatewise, this is the last numerator in the paper's table. -/
theorem degreeDropNumerator_apply (B M : ℕ) (s : Fin 1) :
    degreeDropNumerator B M s =
      (X 0 : LocalPoly) +
        (C (B : ℚ) * (X 0 : LocalPoly) ^ M - (X 1 : LocalPoly) ^ M) := by
  rw [degreeDropNumerator, Pi.add_apply, telescopingNumerator_apply]
  simp [CoreOneGapWeights.tuple]

/-- The canonical class of `B u₀-u₁` is zero. -/
theorem normalForm_telescopingNumerator {B M : ℕ} (hB : 2 ≤ B) :
    normalForm hB (by omega : 0 < 1) (telescopingNumerator B M) = 0 := by
  exact normalForm_telescope hB (by omega : 0 < 1) (rootPowerTuple M)

/-- In the canonical decomposition of an explicit telescope, the selected
primitive is the displayed primitive itself. -/
theorem primitive_telescopingNumerator {B M : ℕ} (hB : 2 ≤ B) :
    primitive hB (by omega : 0 < 1) (telescopingNumerator B M) =
      rootPowerTuple M := by
  apply telescope_injective hB (by omega : 0 < 1)
  have h := decomposition hB (by omega : 0 < 1) (telescopingNumerator B M)
  rw [normalForm_telescopingNumerator hB, zero_add] at h
  simpa only [telescopingNumerator] using h.symm

/-- Every actual prime-gap telescope has the exact initial boundary value.
This is an infinite-series identity; summability and boundary decay are
supplied by the proved polynomial growth of the prime gaps. -/
theorem fullSeries_telescopingNumerator {B M : ℕ} (hB : 2 ≤ B) :
    coreCyclicFullSeries B (by omega : 0 < 1) phaseOne
        (fun n => (primeGap n : ℝ)) (telescopingNumerator B M) =
      (primeGap 0 : ℝ) ^ M := by
  have h := infiniteSeries_normalForm hB (by omega : 0 < 1) phaseOne
    (fun n => (primeGap n : ℝ)) primeGap_hasPolynomialGrowth
    (telescopingNumerator B M) 0
  rw [normalForm_telescopingNumerator hB,
    primitive_telescopingNumerator hB] at h
  simpa only [coreCyclicFullSeries, Nat.zero_add, localValue, rootPowerTuple,
    Pi.zero_apply, eval₂_zero, zero_div, tsum_zero, sub_zero, eval₂_pow,
    eval₂_X] using h

/-- The fourth table row: `Σ (B g_n-g_{n+1})B^{-n}=g₁=1`. -/
theorem fullSeries_Bu0_sub_u1 {B : ℕ} (hB : 2 ≤ B) :
    coreCyclicFullSeries B (by omega : 0 < 1) phaseOne
        (fun n => (primeGap n : ℝ)) (telescopingNumerator B 1) = 1 := by
  rw [fullSeries_telescopingNumerator hB, primeGap_zero]
  norm_num

/-- The rooted linear period-one tuple is exactly the usual linear
prime-gap series `α_{u₀}`. -/
theorem fullSeries_linearTuple_eq (B : ℕ) :
    coreCyclicFullSeries B (by omega : 0 < 1) phaseOne
        (fun n => (primeGap n : ℝ))
        (CoreOneGapWeights.tuple (fun _ : Fin 1 => (1 : ℚ))) =
      primeGapPowerSeries B 1 := by
  rw [CoreOneGapWeights.series_tuple]
  unfold primeGapPowerSeries
  apply tsum_congr
  intro n
  simp only [Rat.cast_one, one_mul, pow_one]

/-- The last table numerator has canonical normal form exactly `u₀`, for
every exponent `M`; no degree-`M` arithmetic input survives. -/
theorem normalForm_degreeDropNumerator {B M : ℕ} (hB : 2 ≤ B) :
    normalForm hB (by omega : 0 < 1) (degreeDropNumerator B M) =
      CoreOneGapWeights.tuple (fun _ : Fin 1 => (1 : ℚ)) := by
  rw [degreeDropNumerator, normalForm_add,
    CoreOneGapWeights.normalForm_tuple, normalForm_telescopingNumerator hB,
    add_zero]

/-- Consequently the effective degree of the last table row is exactly
one, independently of the displayed exponent `M`. -/
theorem topDegree_normalForm_degreeDropNumerator {B M : ℕ} (hB : 2 ≤ B) :
    topDegree (normalForm hB (by omega : 0 < 1)
      (degreeDropNumerator B M)) = 1 := by
  rw [normalForm_degreeDropNumerator hB]
  apply CoreOneGapWeights.degree_eq_one (by omega : 0 < 1)
  intro h
  have h0 := congrFun h (0 : Fin 1)
  simpa using h0

/-- The last table series is literally `α_{u₀}+1`, where `α_{u₀}` is the
linear prime-gap series (not the prime-position series). -/
theorem fullSeries_degreeDropNumerator {B M : ℕ} (hB : 2 ≤ B) :
    coreCyclicFullSeries B (by omega : 0 < 1) phaseOne
        (fun n => (primeGap n : ℝ)) (degreeDropNumerator B M) =
      primeGapPowerSeries B 1 + 1 := by
  change CoreLocalRelations.primeSeriesLinear hB (by omega : 0 < 1) phaseOne
      (CoreOneGapWeights.tuple (fun _ : Fin 1 => (1 : ℚ)) +
        telescopingNumerator B M) = _
  rw [map_add]
  change
    coreCyclicFullSeries B (by omega : 0 < 1) phaseOne
        (fun n => (primeGap n : ℝ))
        (CoreOneGapWeights.tuple (fun _ : Fin 1 => (1 : ℚ))) +
      coreCyclicFullSeries B (by omega : 0 < 1) phaseOne
        (fun n => (primeGap n : ℝ)) (telescopingNumerator B M) = _
  rw [fullSeries_linearTuple_eq,
    fullSeries_telescopingNumerator hB, primeGap_zero]
  norm_num

/-- The degree-one arithmetic hypothesis directly gives normality of the
last worked example, regardless of `M` (hence in particular for `M ≥ 2`). -/
theorem degreeDrop_isNormal_of_D {B M : ℕ} (hB : 2 ≤ B)
    {κ d0 c : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    PrimeGapNormality.BFree.IsNormal B (primeGapPowerSeries B 1 + 1) := by
  have hne : normalForm hB (by omega : 0 < 1) (degreeDropNumerator B M) ≠ 0 := by
    rw [normalForm_degreeDropNumerator hB]
    apply CoreOneGapWeights.ne_zero
    intro h
    have h0 := congrFun h (0 : Fin 1)
    simpa using h0
  have hdegree :
      (topDegree (normalForm hB (by omega : 0 < 1)
        (degreeDropNumerator B M)) : ℝ) / Real.log (B : ℝ) ≤ κ := by
    simpa only [topDegree_normalForm_degreeDropNumerator hB, Nat.cast_one] using hκ
  have hW := corePrime_local_weyl_clock_of_D hB (by omega : 0 < 1) phaseOne
    (degreeDropNumerator B M) hne hdegree hd0 hc hD
  have hWB : weylCriterion B (primeGapPowerSeries B 1 + 1) := by
    simpa only [pow_one, fullSeries_degreeDropNumerator hB] using hW
  exact CoreWeylNormality.isNormal_of_weyl hB hWB

/-- Kuperberg's conjecture supplies the same concrete normality statement
without exposing any additional comparison premise. -/
theorem degreeDrop_isNormal_of_kuperberg {B M : ℕ} (hB : 2 ≤ B)
    (hK : KuperbergConj13) :
    PrimeGapNormality.BFree.IsNormal B (primeGapPowerSeries B 1 + 1) := by
  have hne : normalForm hB (by omega : 0 < 1) (degreeDropNumerator B M) ≠ 0 := by
    rw [normalForm_degreeDropNumerator hB]
    apply CoreOneGapWeights.ne_zero
    intro h
    have h0 := congrFun h (0 : Fin 1)
    simpa using h0
  have hW := corePrime_local_weyl_clock_of_kuperberg hB (by omega : 0 < 1)
    phaseOne (degreeDropNumerator B M) hne hK
  apply CoreWeylNormality.isNormal_of_weyl hB
  simpa only [pow_one, fullSeries_degreeDropNumerator hB] using hW

end

end PrimeGapNormality.Prime.CorePaperWorkedExamples
