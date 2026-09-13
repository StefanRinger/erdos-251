import PrimeGapNormality.Prime.CoreRoundedModelFinite
import PrimeGapNormality.Prime.CorePrimeNormalityOfD
import PrimeGapNormality.Prime.CorePrimeGapTailUnconditional
import PrimeGapNormality.Prime.CoreSubexponentialAlgebra

/-!
# D transfer for arbitrary linearly bounded integer gap observables

This is the arithmetic half of the rounded-gap argument.  For a fixed
relative cyclic label, the literal infinite integer-gap series on the prime
window is compared with the actual normalized finite root model.  The
finite model test is exactly `CoreRoundedModelFinite.actualTest`, so the
rounded insertion argument consumes the result without a change of phase
or of configuration law.

The relative label is fixed before the physical window is averaged.  Thus
no statistic marked by the absolute residue of the prime index is assumed;
selection of an absolute residue progression remains the separate positive
residue-class passage used by the cyclic orbit argument.

Only the genuine D quantity is an input.  The Janossy calibration, prime
first-gap mean, convergence of the unbounded observable, and normalization
of `finiteRootMix` are discharged by proved project theorems.
-/

namespace PrimeGapNormality.Prime.CoreIntegerGapDTransfer

open Finset Filter MeasureTheory CoreCyclic
open CoreIntegerGapObservable CoreIntegerGapInsertion
open CoreSequenceSubexponentialGrowth
open scoped Topology Classical NNReal BoundedContinuousFunction

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

/-- The stopped exact-`L` expression occurring directly in the positive
arithmetic comparison. -/
def stoppedMean
    (B S L : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (ν : Finset ℕ → ℝ)
    (f : Circle → ℝ) : ℝ :=
  ∑ U ∈ (offsetWindow S).powerset.filter (fun U ↦ U.card = L),
    f (actualFiniteObservablePhase B hk r F L U : Circle) *
      Stopped.shortShapeMass (offsetWindow S) ν L U

/-- The finite model mean used by the rounded insertion module. -/
def finiteRootModelMean
    (B X S L : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (f : Circle →ᵇ ℝ) : ℝ :=
  corePositiveFiniteRootMean X S L
    (CoreRoundedModelFinite.actualTest B hk r F L f)

/-- The finite observable reads the consecutive prime gaps on the literal
prime-prefix configuration. -/
theorem actualFiniteObservablePhase_primePrefix_eq
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (n L : ℕ) :
    actualFiniteObservablePhase B hk r F L (corePrimePrefix n L) =
      observableTrunc B hk r F primeGap n L := by
  unfold actualFiniteObservablePhase finiteObservablePhase observableTrunc
    observableValue
  apply sum_congr rfl
  intro e he
  dsimp only
  rw [corePrimePrefix_gap n L e (mem_range.mp he)]

/-- Taking `firstL` does not alter the first `L` ordered gaps. -/
theorem actualFiniteObservablePhase_firstL
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (L : ℕ) (U : Finset ℕ)
    (hLU : L ≤ U.card) :
    actualFiniteObservablePhase B hk r F L (Stopped.firstL L U) =
      actualFiniteObservablePhase B hk r F L U := by
  unfold actualFiniteObservablePhase finiteObservablePhase
  apply sum_congr rfl
  intro e he
  apply congrArg (fun z : ℝ ↦ z / (B : ℝ) ^ (e + 1))
  unfold subsetGap
  dsimp only
  rw [CoreLinearInsertion.orderStat_firstL L U (by
      have := mem_range.mp he
      omega : e + 1 ≤ L),
    CoreLinearInsertion.orderStat_firstL L U (by
      have := mem_range.mp he
      omega : e ≤ L)]

/-- The stopped sum is exactly the high-configuration finite root mean.
This is the bridge used by `CoreRoundedModelFinite`; no new model law is
chosen. -/
theorem stoppedMean_finiteRootMix_eq_modelMean
    (B X S L : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (f : Circle →ᵇ ℝ) :
    stoppedMean B S L hk r F (finiteRootMix X S) f =
      finiteRootModelMean B X S L hk r F f := by
  rw [stoppedMean, coreStopped_positive_test_eq_pushforward]
  unfold finiteRootModelMean corePositiveFiniteRootMean
  apply sum_congr rfl
  intro U hU
  by_cases hLU : L ≤ U.card
  · simp only [hLU, if_true, CoreRoundedModelFinite.actualTest]
    rw [actualFiniteObservablePhase_firstL B hk r F L U hLU]
  · simp only [hLU, if_false]

theorem stoppedMean_const_mul
    (B S L : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (ν : Finset ℕ → ℝ) (c : ℝ)
    (f : Circle → ℝ) :
    stoppedMean B S L hk r F (fun U ↦ c * ν U) f =
      c * stoppedMean B S L hk r F ν f := by
  unfold stoppedMean
  rw [mul_sum]
  apply sum_congr rfl
  intro U hU
  have hm : Stopped.shortShapeMass (offsetWindow S) (fun E ↦ c * ν E) L U =
      c * Stopped.shortShapeMass (offsetWindow S) ν L U := by
    unfold Stopped.shortShapeMass
    rw [mul_sum]
    apply sum_congr rfl
    intro E hE
    split_ifs <;> simp
  rw [hm]
  ring

theorem stoppedMean_nonneg
    {B S L : ℕ} {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {ν : Finset ℕ → ℝ}
    (hν : ∀ U ∈ (offsetWindow S).powerset, 0 ≤ ν U)
    (f : Circle → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ stoppedMean B S L hk r F ν f := by
  unfold stoppedMean
  apply sum_nonneg
  intro U hU
  apply mul_nonneg (hf _)
  unfold Stopped.shortShapeMass
  exact sum_nonneg fun E hE ↦ by
    split_ifs
    · exact hν E hE
    · exact le_rfl

private theorem mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos
  · intro t ht
    exact eulerProdNat_pos (sieveCutoff (t : ℝ))
  · exact ⟨2 * X, by simp only [mixScale, mem_Ioc]; omega⟩

private theorem finiteRootMix_nonneg
    {X S : ℕ} (hZ : 0 ≤ mixZ X) (U : Finset ℕ) :
    0 ≤ finiteRootMix X S U := by
  unfold finiteRootMix
  exact div_nonneg
    (sum_nonneg fun t ht ↦
      mul_nonneg (mixWeightV_nonneg t) (actualRootLaw_nonneg _ _ _)) hZ

/-- Exact normalization of the integer-observable stopped mean. -/
theorem stoppedMean_finiteRootMixUnnorm_eq
    {X : ℕ} (hN : 0 < windowNX X) (hZ : 0 < mixZ X)
    (B S L : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (f : Circle → ℝ) :
    stoppedMean B S L hk r F (finiteRootMixUnnorm X S) f =
      mixZeta X * stoppedMean B S L hk r F (finiteRootMix X S) f := by
  have hfun : finiteRootMixUnnorm X S =
      fun U ↦ mixZeta X * finiteRootMix X S U := by
    funext U
    exact finiteRootMixUnnorm_eq_mixZeta_mul_finiteRootMix hN hZ S U
  rw [hfun, stoppedMean_const_mul]

/-- Exact finite positive transfer for the integer observable. -/
theorem prime_truncated_positive_window_le
    (B X S : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {L : ℕ} (hL : 1 ≤ L)
    (f : Circle →ᵇ ℝ) {C : ℝ} (hfC : ∀ x, f x ≤ C) :
    windowAvgReal (seqWindow nthPrime X) (fun n ↦
      f (observableTrunc B hk r F primeGap n L : Circle)) ≤
      C * Stopped.failureMass (offsetWindow S)
        (coreActualPatternMass X (offsetWindow S)) L +
      stoppedMean B S L hk r F (coreActualPatternMass X (offsetWindow S)) f := by
  classical
  unfold stoppedMean offsetWindow
  rw [coreActual_span_failure_eq_index X S hL,
    coreActual_firstL_test_eq_index_average X S hL]
  simp_rw [actualFiniteObservablePhase_primePrefix_eq B hk r F]
  unfold windowAvgReal
  rw [seqWindow_nthPrime_card, corePrime_seqWindow_eq_Ico,
    ← mul_div_assoc, ← add_div, mul_sum, ← sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro n hn
  by_cases hs : nthPrime (n + L) - nthPrime n ≤ S
  · simp [hs]
  · simp only [hs, if_false, mul_one, add_zero]
    exact hfC _

/-- D and the actual Janossy comparison applied to the exact integer
observable test. -/
theorem prime_truncated_positive_window_le_comparisonQuantity
    {B X S L R k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {ν : Finset ℕ → ℝ} {c C : ℝ}
    (hN : 0 < windowNX X) (hL : 1 ≤ L) (hLR : L ≤ R)
    (hpar : Odd (R - L)) (hc : 0 ≤ c) (hC : 0 < C)
    (hν : ∀ U ∈ (offsetWindow S).powerset, 0 ≤ ν U)
    (f : Circle →ᵇ ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfC : ∀ x, f x ≤ C) :
    windowAvgReal (seqWindow nthPrime X) (fun n ↦
      f (observableTrunc B hk r F primeGap n L : Circle)) ≤
      c * stoppedMean B S L hk r F ν f +
      C * (corePrimeComparisonQuantity X (offsetWindow S) L R c +
        c * ∑ U ∈ (offsetWindow S).powerset.filter (fun U ↦ U.card = L),
          |coreJanossyTransform (offsetWindow S) (rootedMainTerm X) L R U /
              (windowNX X : ℝ) -
            Stopped.janossyTrunc (offsetWindow S) ν L R U|) := by
  have hfinite := prime_truncated_positive_window_le B X S hk r F hL f hfC
  exact hfinite.trans
    (corePrime_positive_test_bounded_le_comparisonQuantity
      hN hL hLR hpar hc hC hν
      (f := fun U ↦ f (actualFiniteObservablePhase B hk r F L U : Circle))
      (fun U hU ↦ hf0 _) (fun U hU ↦ hfC _))

/-- Restoring the literal infinite integer-observable series leaves only
its genuine physical-window phase-test remainder. -/
theorem prime_full_positive_window_le_comparisonQuantity
    {B X S L R k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {ν : Finset ℕ → ℝ} {c C : ℝ}
    (hN : 0 < windowNX X) (hL : 1 ≤ L) (hLR : L ≤ R)
    (hpar : Odd (R - L)) (hc : 0 ≤ c) (hC : 0 < C)
    (hν : ∀ U ∈ (offsetWindow S).powerset, 0 ≤ ν U)
    (f : Circle →ᵇ ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfC : ∀ x, f x ≤ C) :
    windowAvgReal (seqWindow nthPrime X) (fun n ↦
      f (observableSeries B hk r F primeGap n : Circle)) ≤
      c * stoppedMean B S L hk r F ν f +
      C * (corePrimeComparisonQuantity X (offsetWindow S) L R c +
        c * ∑ U ∈ (offsetWindow S).powerset.filter (fun U ↦ U.card = L),
          |coreJanossyTransform (offsetWindow S) (rootedMainTerm X) L R U /
              (windowNX X : ℝ) -
            Stopped.janossyTrunc (offsetWindow S) ν L R U|) +
      windowAvgReal (seqWindow nthPrime X) (fun n ↦
        |f (observableSeries B hk r F primeGap n : Circle) -
          f (observableTrunc B hk r F primeGap n L : Circle)|) := by
  have hfinite := prime_truncated_positive_window_le_comparisonQuantity
    (B := B) hk r F hN hL hLR hpar hc hC hν f hf0 hfC
  have htriangle :
      windowAvgReal (seqWindow nthPrime X) (fun n ↦
        f (observableSeries B hk r F primeGap n : Circle)) ≤
        windowAvgReal (seqWindow nthPrime X) (fun n ↦
          f (observableTrunc B hk r F primeGap n L : Circle)) +
        windowAvgReal (seqWindow nthPrime X) (fun n ↦
          |f (observableSeries B hk r F primeGap n : Circle) -
            f (observableTrunc B hk r F primeGap n L : Circle)|) := by
    unfold windowAvgReal
    rw [← add_div, ← sum_add_distrib]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro n hn
    linarith [le_abs_self
      (f (observableSeries B hk r F primeGap n : Circle) -
        f (observableTrunc B hk r F primeGap n L : Circle))]
  exact htriangle.trans (_root_.add_le_add hfinite le_rfl)

/-- The unconditional prime first-gap mean kills the observable tail at the
exact paper profile. -/
theorem tendsto_prime_observablePositiveTestRemainder_profileL_zero
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    Tendsto (fun X : ℕ ↦
      windowAvgReal (seqWindow nthPrime X) (fun n ↦
        |f (observableSeries B hk r F primeGap n : Circle) -
          f (observableTrunc B hk r F primeGap n (profileL κ X) : Circle)|))
      atTop (nhds 0) := by
  have hBlog : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hκpos : 0 < κ := (div_pos zero_lt_one hBlog).trans_le hκ
  let rho := localTailBase κ
  have hrho : 1 < rho := localTailBase_one_lt hκpos
  have hrhoB : rho ≤ (B : ℝ) := by
    have h := localTailBase_pow_le (κ := κ) hB (show 1 ≤ (1 : ℕ) by omega)
      (by simpa only [Nat.cast_one] using hκ)
    simpa only [pow_one] using h
  have hcount : WindowCountToInfinity nthPrime := by
    have hreal := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      CorePrimeDensity.tendsto_windowNX_atTop
    simpa only [WindowCountToInfinity, seqWindow_nthPrime_card,
      Function.comp_def] using hreal
  have hgrowth : HasSubexponentialGrowth
      (fun n ↦ (primeGap n : ℝ)) := by
    simpa only [seqGap_nthPrime] using
      (sequenceGap_hasSubexponentialGrowth nthPrime_strictMono hcount)
  have hgapPos : ∀ n, 1 ≤ primeGap n := by
    intro n
    unfold primeGap
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.sub_ne_zero_of_lt (nthPrime_strictMono (Nat.lt_succ_self n)))
  have htail := tendsto_scaledGapTail_avg_of_GapTailT
    (CorePrimeGapTailUnconditional.gapTailT_nthPrime_windowG hrho)
  have hmajor := htail.const_mul ((K : ℝ) * C)
  simp only [mul_zero] at hmajor
  have hprofile : ∀ X, profileL κ X = stdProfileL rho (windowG X) :=
    profileL_eq_stdProfileL_localTailBase hκpos
  apply squeeze_zero'
  · exact Eventually.of_forall fun X ↦
      div_nonneg (sum_nonneg fun n hn ↦ abs_nonneg _) (Nat.cast_nonneg _)
  · apply Eventually.of_forall
    intro X
    have hpoint : ∀ n,
        |f (observableSeries B hk r F primeGap n : Circle) -
          f (observableTrunc B hk r F primeGap n (profileL κ X) : Circle)| ≤
          (K : ℝ) * C *
            scaledGapTail rho (fun q ↦ (primeGap q : ℝ)) n (profileL κ X) := by
      intro n
      have hsplit := observableSeries_eq_trunc_add_tail hB hk r F hgapPos
        hgrowth hC hF n (profileL κ X)
      have hlip := corePositiveTest_real_dist_le f hK
        (observableSeries B hk r F primeGap n)
        (observableTrunc B hk r F primeGap n (profileL κ X))
      have hobs := abs_observableTail_le_firstGapTail hB hk r F
        nthPrime_strictMono hgrowth hC hF hrho hrhoB n (profileL κ X)
      have hdiff :
          |observableSeries B hk r F primeGap n -
              observableTrunc B hk r F primeGap n (profileL κ X)| =
            |observableTail B hk r F primeGap n (profileL κ X)| := by
        rw [hsplit]
        ring_nf
      rw [hdiff] at hlip
      have hscaled :
          C * rho⁻¹ ^ profileL κ X *
              seqGapTail rho nthPrime (n + profileL κ X) =
            C * scaledGapTail rho (fun q ↦ (primeGap q : ℝ)) n
              (profileL κ X) := by
        change C * rho⁻¹ ^ profileL κ X * seqGapTail rho nthPrime (n + profileL κ X) =
          C * scaledGapTail rho (fun q ↦ (seqGap nthPrime q : ℝ)) n (profileL κ X)
        rw [scaledGapTail_seqGap, inv_pow]
        ring
      exact hlip.trans ((mul_le_mul_of_nonneg_left hobs K.coe_nonneg).trans_eq (by
        rw [hscaled]
        ring))
    have havg : windowAvgReal (seqWindow nthPrime X) (fun n ↦
        |f (observableSeries B hk r F primeGap n : Circle) -
          f (observableTrunc B hk r F primeGap n (profileL κ X) : Circle)|) ≤
        windowAvgReal (seqWindow nthPrime X) (fun n ↦
          (K : ℝ) * C * scaledGapTail rho
            (fun q ↦ (primeGap q : ℝ)) n (profileL κ X)) := by
      unfold windowAvgReal
      exact div_le_div_of_nonneg_right
        (sum_le_sum fun n hn ↦ hpoint n) (Nat.cast_nonneg _)
    calc
      windowAvgReal (seqWindow nthPrime X) (fun n ↦
          |f (observableSeries B hk r F primeGap n : Circle) -
            f (observableTrunc B hk r F primeGap n (profileL κ X) : Circle)|) ≤
        windowAvgReal (seqWindow nthPrime X) (fun n ↦
          (K : ℝ) * C * scaledGapTail rho
            (fun q ↦ (primeGap q : ℝ)) n (profileL κ X)) := havg
      _ = (K : ℝ) * C * windowAvgReal (seqWindow nthPrime X) (fun n ↦
          scaledGapTail rho (fun q ↦ (primeGap q : ℝ)) n
            (profileL κ X)) := by
        unfold windowAvgReal
        rw [← Finset.mul_sum]
        ring
      _ = (K : ℝ) * C * windowAvgReal (seqWindow nthPrime X) (fun n ↦
          scaledGapTail rho (fun q ↦ (primeGap q : ℝ)) n
            (stdProfileL rho (windowG X))) := by rw [← hprofile X]
  · exact hmajor

/-- Final arithmetic D transfer.  Its right side is the genuine normalized
finite-root-model mean used by the rounded insertion analysis. -/
theorem eventually_prime_observableMean_le_finiteRootModel_of_D
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {Cobs : ℝ} (hCobs : 0 ≤ Cobs)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ Cobs * (q : ℝ))
    {κ d0 c : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c)
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    (hf0 : ∀ x, 0 ≤ f x) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ X : ℕ in atTop,
      coreDigitalWindowAverage
        (fun n ↦ (observableSeries B hk r F primeGap n : Circle)) f
        (Nat.primeCounting X) (windowNX X) ≤
      16 * c * finiteRootModelMean B X (ahlSmall_window κ X)
        (profileL κ X) hk r F f + eps := by
  have hBlog : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hκpos : 0 < κ := (div_pos zero_lt_one hBlog).trans_le hκ
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  let C : ℝ := ‖f‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hfC (x : Circle) : f x ≤ C :=
    (f.apply_le_norm x).trans (le_add_of_nonneg_right zero_le_one)
  let Rem : ℕ → ℝ := fun X ↦
    windowAvgReal (seqWindow nthPrime X) (fun n ↦
      |f (observableSeries B hk r F primeGap n : Circle) -
        f (observableTrunc B hk r F primeGap n (profileL κ X) : Circle)|)
  have hRem : Tendsto Rem atTop (nhds 0) := by
    simpa only [Rem] using
      tendsto_prime_observablePositiveTestRemainder_profileL_zero
        hB hk r F hCobs hF hκ f hK
  let Err : ℕ → ℝ := fun X ↦ C *
    (corePrimeComparisonQuantity X (ahlSmall_omega κ X) (profileL κ X)
      (profileR (profileL κ X) d0) c +
      c * coreMixtureJanossyCalibration κ d0 X) + Rem X
  have hErr : Tendsto Err atTop (nhds 0) := by
    have hcal := (CoreCalibrationUnconditional.tendsto_calibration hκpos hd0).const_mul c
    simp only [mul_zero] at hcal
    have hmain := (hD.add hcal).const_mul C
    simpa only [Err, add_zero, mul_zero] using hmain.add hRem
  filter_upwards [eventually_ge_atTop 1, eventually_one_le_profileL hκpos,
    CorePrimeDensity.eventually_mixZeta_le_sixteen,
    hErr.eventually (Metric.ball_mem_nhds (0 : ℝ) heps)] with X hX hL hζ herror
  have hN : 0 < windowNX X := windowNX_pos (by omega)
  have hZ : 0 < mixZ X := mixZ_pos hX
  have hfull := prime_full_positive_window_le_comparisonQuantity
    (B := B) (X := X) (S := ahlSmall_window κ X)
    (L := profileL κ X) (R := profileR (profileL κ X) d0)
    (ν := finiteRootMixUnnorm X (ahlSmall_window κ X))
    hk r F hN hL (crtMixProf_le_at κ d0 X) (crtMixProf_odd_at κ d0 X)
    hcpos.le hC
    (fun U hU ↦ crtMixUnnorm_finiteRootMixUnnorm_nonneg X _ U)
    f hf0 hfC
  have hfull' :
      windowAvgReal (seqWindow nthPrime X) (fun n ↦
        f (observableSeries B hk r F primeGap n : Circle)) ≤
      c * stoppedMean B (ahlSmall_window κ X) (profileL κ X) hk r F
        (finiteRootMixUnnorm X (ahlSmall_window κ X)) f + Err X := by
    simpa only [Err, Rem, coreMixtureJanossyCalibration, ahlSmall_omega,
      offsetWindow, add_assoc] using hfull
  rw [stoppedMean_finiteRootMixUnnorm_eq hN hZ] at hfull'
  have hν : ∀ U ∈ (offsetWindow (ahlSmall_window κ X)).powerset,
      0 ≤ finiteRootMix X (ahlSmall_window κ X) U :=
    fun U hU ↦ finiteRootMix_nonneg hZ.le U
  have hmean0 : 0 ≤ stoppedMean B (ahlSmall_window κ X) (profileL κ X)
      hk r F (finiteRootMix X (ahlSmall_window κ X)) f :=
    stoppedMean_nonneg hk r F hν f hf0
  have hmain : c * (mixZeta X * stoppedMean B (ahlSmall_window κ X)
      (profileL κ X) hk r F (finiteRootMix X (ahlSmall_window κ X)) f) ≤
      16 * c * stoppedMean B (ahlSmall_window κ X) (profileL κ X)
        hk r F (finiteRootMix X (ahlSmall_window κ X)) f := by
    have hm := mul_le_mul_of_nonneg_right hζ hmean0
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hm hcpos.le
  have herr : Err X ≤ eps := by
    have habs : |Err X - 0| < eps := by
      simpa only [Metric.mem_ball, Real.dist_eq] using herror
    rw [sub_zero] at habs
    exact (le_abs_self _).trans habs.le
  have hresult := hfull'.trans (_root_.add_le_add hmain herr)
  rw [corePrime_window_positive_average_eq] at hresult
  rw [stoppedMean_finiteRootMix_eq_modelMean] at hresult
  exact hresult

end

end PrimeGapNormality.Prime.CoreIntegerGapDTransfer
