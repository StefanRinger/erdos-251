import PrimeGapNormality.Prime.CorePrimeLocalNormality
import PrimeGapNormality.Prime.CoreOneGapWeights
import PrimeGapNormality.Prime.PeriodicAbel

/-!
# Periodic prime-position weights

This file passes a nonzero rational periodic position weight through the
exact Abel transform and the concrete one-gap cyclic tuple.  The only
translation between the position and gap series is the explicit rational
boundary from `primePosWeightedSeries_eq_gapAbel_rat`.
-/

namespace PrimeGapNormality.Prime.CorePeriodicPositionEnd

open Function CoreCyclic MvPolynomial

noncomputable section

/-- The zero phase of a nonempty cyclic label set. -/
def phaseZero {k : ℕ} (hk : 0 < k) : Fin k := ⟨0, hk⟩

/-- The finite cyclic coefficient tuple obtained from the one-based Abel
gap weights. -/
def periodicGapFinWeight (c : ℕ → ℚ) (B : ℕ) {k : ℕ} (s : Fin k) : ℚ :=
  periodicGapWeightQ c B k (s.val + 1)

/-- The rational endpoint term in periodic Abel summation. -/
def periodicPositionBoundaryQ (c : ℕ → ℚ) (B k : ℕ) : ℚ :=
  (nthPrime 0 : ℚ) * periodicGapWeightQ c B k 0

private theorem periodic_add_mul {α : Type*} {f : ℕ → α} {k : ℕ}
    (hf : Periodic f k) (x q : ℕ) : f (x + k * q) = f x := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, ← add_assoc]
    exact (hf (x + k * q)).trans ih

/-- The rational Abel gap weights inherit the original period. -/
theorem periodicGapWeightQ_periodic {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (c : ℕ → ℚ) (hc : Periodic c k) :
    Periodic (periodicGapWeightQ c B k) k := by
  intro j
  have h := (periodicGapWeight_periodic'
    (B := B) (k := k) (fun n : ℕ ↦ (c n : ℝ)) (periodic_cast_rat hc)) j
  rw [periodicGapWeight_eq_rat (j := j + k) hB hk c,
    periodicGapWeight_eq_rat (j := j) hB hk c] at h
  exact Rat.cast_injective h

/-- At phase zero, the finite label `n mod k` represents exactly the
one-based infinite Abel weight at `n+1`. -/
theorem periodicGapFinWeight_phase {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (n : ℕ) :
    periodicGapFinWeight c B (phaseAt hk (phaseZero hk) n) =
      periodicGapWeightQ c B k (n + 1) := by
  have hd := periodicGapWeightQ_periodic hB (by omega : 1 ≤ k) c hc
  have hdiv : n + 1 = (n % k + 1) + k * (n / k) := by
    have hn := Nat.div_add_mod n k
    omega
  unfold periodicGapFinWeight
  rw [phaseAt_val]
  simp only [phaseZero, Fin.val_mk, Nat.zero_add]
  rw [hdiv]
  exact (periodic_add_mul hd (n % k + 1) (n / k)).symm

/-- A nonzero periodic position weight has a nonzero finite Abel gap
coefficient tuple.  This is the injectivity of the cyclic Abel recurrence,
proved here from the literal recurrence rather than assumed. -/
theorem periodicGapFinWeight_ne_zero {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0) :
    periodicGapFinWeight (k := k) c B ≠ 0 := by
  intro hd
  have hdper := periodicGapWeightQ_periodic hB (by omega : 1 ≤ k) c hc
  have hdSucc (n : ℕ) : periodicGapWeightQ c B k (n + 1) = 0 := by
    have hs := congrFun hd (phaseAt hk (phaseZero hk) n)
    rw [periodicGapFinWeight_phase hB hk c hc n] at hs
    simpa only [Pi.zero_apply] using hs
  have hdk : periodicGapWeightQ c B k k = 0 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hdSucc (k - 1)
  have hd0 : periodicGapWeightQ c B k 0 = 0 := by
    have hp := hdper 0
    rw [Nat.zero_add] at hp
    exact hp.symm.trans hdk
  have hdAll (n : ℕ) : periodicGapWeightQ c B k n = 0 := by
    cases n with
    | zero => exact hd0
    | succ n => simpa only [Nat.succ_eq_add_one] using hdSucc n
  have hcSucc (j : ℕ) : c (j + 1) = 0 := by
    have hrec := periodicGapWeight_rec (j := j) hB (by omega : 1 ≤ k)
      (fun n : ℕ ↦ (c n : ℝ)) (periodic_cast_rat hc)
    unfold recGapWeight at hrec
    rw [periodicGapWeight_eq_rat (j := j) hB (by omega : 1 ≤ k) c,
      periodicGapWeight_eq_rat (j := j + 1) hB (by omega : 1 ≤ k) c] at hrec
    simp only [hdAll, Rat.cast_zero, mul_zero, sub_zero] at hrec
    exact_mod_cast hrec.symm
  apply hc0
  funext n
  cases n with
  | zero =>
      have hck : c k = 0 := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hcSucc (k - 1)
      have hp := hc 0
      rw [Nat.zero_add] at hp
      simpa only [Pi.zero_apply] using hp.symm.trans hck
  | succ n =>
      simpa only [Nat.succ_eq_add_one, Pi.zero_apply] using hcSucc n

/-- The concrete one-gap tuple has nonzero canonical normal form. -/
theorem periodicGapTuple_normalForm_ne_zero {B k : ℕ} (hB : 2 ≤ B)
    (hk : 0 < k) (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0) :
    normalForm hB hk (CoreOneGapWeights.tuple (periodicGapFinWeight c B)) ≠ 0 := by
  rw [CoreOneGapWeights.normalForm_tuple hB hk]
  exact CoreOneGapWeights.ne_zero _
    (periodicGapFinWeight_ne_zero hB hk c hc hc0)

/-- The effective degree of the concrete nonzero Abel tuple is exactly one. -/
theorem periodicGapTuple_normalForm_degree {B k : ℕ} (hB : 2 ≤ B)
    (hk : 0 < k) (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0) :
    topDegree
      (normalForm hB hk (CoreOneGapWeights.tuple (periodicGapFinWeight c B))) = 1 := by
  rw [CoreOneGapWeights.normalForm_tuple hB hk]
  exact CoreOneGapWeights.degree_eq_one hk _
    (periodicGapFinWeight_ne_zero hB hk c hc hc0)

/-- The concrete local one-gap series is literally the Abel-transformed
prime-gap series. -/
theorem coreCyclicFullSeries_gapWeight {B k : ℕ} (hB : 2 ≤ B)
    (hk : 0 < k) (c : ℕ → ℚ) (hc : Periodic c k) :
    coreCyclicFullSeries B hk (phaseZero hk) (fun n ↦ (primeGap n : ℝ))
        (CoreOneGapWeights.tuple (periodicGapFinWeight c B)) =
      primeGapWeightedSeries (fun j ↦ (periodicGapWeightQ c B k j : ℝ)) B := by
  rw [CoreOneGapWeights.series_tuple]
  unfold primeGapWeightedSeries
  apply tsum_congr
  intro n
  rw [periodicGapFinWeight_phase hB hk c hc n]

/-- Exact scalar Abel identity with the cyclic local series and its explicit
rational boundary. -/
theorem primePositionSeries_eq_boundary_add_core {B k : ℕ} (hB : 2 ≤ B)
    (hk : 0 < k) (c : ℕ → ℚ) (hc : Periodic c k) :
    primePosWeightedSeries (fun n ↦ (c n : ℝ)) B =
      (periodicPositionBoundaryQ c B k : ℝ) +
        coreCyclicFullSeries B hk (phaseZero hk) (fun n ↦ (primeGap n : ℝ))
          (CoreOneGapWeights.tuple (periodicGapFinWeight c B)) := by
  calc
    primePosWeightedSeries (fun n ↦ (c n : ℝ)) B =
        (nthPrime 0 : ℝ) * (periodicGapWeightQ c B k 0 : ℝ) +
          primeGapWeightedSeries (fun j ↦ (periodicGapWeightQ c B k j : ℝ)) B :=
      primePosWeightedSeries_eq_gapAbel_rat hB (by omega : 1 ≤ k) c hc
    _ = (periodicPositionBoundaryQ c B k : ℝ) +
          primeGapWeightedSeries (fun j ↦ (periodicGapWeightQ c B k j : ℝ)) B := by
      simp only [periodicPositionBoundaryQ, Rat.cast_mul, Rat.cast_natCast]
    _ = (periodicPositionBoundaryQ c B k : ℝ) +
        coreCyclicFullSeries B hk (phaseZero hk) (fun n ↦ (primeGap n : ℝ))
          (CoreOneGapWeights.tuple (periodicGapFinWeight c B)) := by
      rw [coreCyclicFullSeries_gapWeight hB hk c hc]

/-- The original periodic prime-position series is absolutely summable. -/
theorem primePositionSeries_summable {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) :
    Summable fun n : ℕ ↦
      (c (n + 1) : ℝ) * (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) :=
  primePosWeightedSeries_summable hB (by omega : 1 ≤ k)
    (fun n ↦ (c n : ℝ)) (periodic_cast_rat hc)

private theorem periodicClock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    2 ≤ B ^ k := by
  have hsplit : k = k - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [hsplit, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

/-- Degree-one D input gives Weyl at the literal period clock for every
nonzero rational periodic position weight. -/
theorem primePositionSeries_weyl_clock_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    {κ d0 C : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hC : 1 ≤ C) (hD : CoreLinearD κ d0 C) :
    weylCriterion (B ^ k) (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) := by
  have hnf := periodicGapTuple_normalForm_ne_zero hB hk c hc hc0
  have hdeg := periodicGapTuple_normalForm_degree hB hk c hc hc0
  have hκ' :
      (topDegree
        (normalForm hB hk (CoreOneGapWeights.tuple (periodicGapFinWeight c B))) : ℝ) /
          Real.log (B : ℝ) ≤ κ := by
    rw [hdeg]
    simpa only [Nat.cast_one] using hκ
  have hlocal := corePrime_local_weyl_clock_of_D hB hk (phaseZero hk)
    (CoreOneGapWeights.tuple (periodicGapFinWeight c B)) hnf hκ' hd0 hC hD
  have hshift := CoreRationalAffine.weylCriterion_add_rat
    (periodicClock_ge hB hk) (periodicPositionBoundaryQ c B k) hlocal
  rw [primePositionSeries_eq_boundary_add_core hB hk c hc]
  simpa only [add_comm] using hshift

theorem primePositionSeries_weyl_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    {κ d0 C : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hC : 1 ≤ C) (hD : CoreLinearD κ d0 C) :
    weylCriterion B (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) :=
  weylCriterion_of_pow hB (by omega : 1 ≤ k)
    (primePositionSeries_weyl_clock_of_D hB hk c hc hc0 hκ hd0 hC hD)

theorem primePositionSeries_isNormal_clock_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    {κ d0 C : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hC : 1 ≤ C) (hD : CoreLinearD κ d0 C) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) :=
  CoreWeylNormality.isNormal_of_weyl (periodicClock_ge hB hk)
    (primePositionSeries_weyl_clock_of_D hB hk c hc hc0 hκ hd0 hC hD)

theorem primePositionSeries_isNormal_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    {κ d0 C : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hC : 1 ≤ C) (hD : CoreLinearD κ d0 C) :
    PrimeGapNormality.BFree.IsNormal B
      (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (primePositionSeries_weyl_of_D hB hk c hc hc0 hκ hd0 hC hD)

theorem primePositionSeries_irrational_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    {κ d0 C : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hC : 1 ≤ C) (hD : CoreLinearD κ d0 C) :
    Irrational (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) :=
  weylCriterion_irrational
    (primePositionSeries_weyl_of_D hB hk c hc hc0 hκ hd0 hC hD)

/-- Kuperberg supplies the degree-one profile with no residual model or
tail hypothesis. -/
theorem primePositionSeries_weyl_clock_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    (hK : KuperbergConj13) :
    weylCriterion (B ^ k) (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) := by
  have hnf := periodicGapTuple_normalForm_ne_zero hB hk c hc hc0
  have hlocal := corePrime_local_weyl_clock_of_kuperberg hB hk (phaseZero hk)
    (CoreOneGapWeights.tuple (periodicGapFinWeight c B)) hnf hK
  have hshift := CoreRationalAffine.weylCriterion_add_rat
    (periodicClock_ge hB hk) (periodicPositionBoundaryQ c B k) hlocal
  rw [primePositionSeries_eq_boundary_add_core hB hk c hc]
  simpa only [add_comm] using hshift

theorem primePositionSeries_weyl_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    (hK : KuperbergConj13) :
    weylCriterion B (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) :=
  weylCriterion_of_pow hB (by omega : 1 ≤ k)
    (primePositionSeries_weyl_clock_of_kuperberg hB hk c hc hc0 hK)

theorem primePositionSeries_isNormal_clock_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    (hK : KuperbergConj13) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) :=
  CoreWeylNormality.isNormal_of_weyl (periodicClock_ge hB hk)
    (primePositionSeries_weyl_clock_of_kuperberg hB hk c hc hc0 hK)

theorem primePositionSeries_isNormal_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    (hK : KuperbergConj13) :
    PrimeGapNormality.BFree.IsNormal B
      (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (primePositionSeries_weyl_of_kuperberg hB hk c hc hc0 hK)

theorem primePositionSeries_irrational_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : ℕ → ℚ) (hc : Periodic c k) (hc0 : c ≠ 0)
    (hK : KuperbergConj13) :
    Irrational (primePosWeightedSeries (fun n ↦ (c n : ℝ)) B) :=
  weylCriterion_irrational
    (primePositionSeries_weyl_of_kuperberg hB hk c hc hc0 hK)

end

end PrimeGapNormality.Prime.CorePeriodicPositionEnd
