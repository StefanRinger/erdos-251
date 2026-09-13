import PrimeGapNormality.Prime.CorePrimeLocalPositiveWindow
import PrimeGapNormality.Prime.CorePositiveRootFrameAssembly
import PrimeGapNormality.Prime.CorePrimeWindowMean
import PrimeGapNormality.Prime.CoreKuperbergComparison

/-! Exact identification of the stopped local-polynomial mean with the
full-configuration mean used by resampling. All survivors are retained in
the frame even though only the first L-w emissions are observed. -/

namespace PrimeGapNormality.Prime
open Finset MvPolynomial
open scoped Classical
noncomputable section

theorem coreCyclicFinitePhase_firstL
    (B : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k)
    {w L : ℕ} (hwL : w ≤ L)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w) (E : Finset ℕ) :
    CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
      (CoreCyclic.orderedRealGap (Stopped.firstL L E)) =
    CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
      (CoreCyclic.orderedRealGap E) := by
  unfold CoreCyclic.coreCyclicFinitePhase
  apply sum_congr rfl
  intro e he
  apply congrArg (fun z : ℝ ↦ z / (B : ℝ) ^ (e + 1))
  apply eval₂_congr
  intro i m hi hm
  have hivars : i ∈ (F (CoreCyclic.phaseAt hk phase e)).vars :=
    (mem_vars_iff_mem_support i).2 ⟨m, mem_support_iff.mpr hm, hi⟩
  have hiw := hw _ i hivars
  have heL := mem_range.mp he
  have heiL : e + i < L := by omega
  unfold CoreCyclic.orderedRealGap subsetGap
  rw [CoreLinearInsertion.orderStat_firstL L E (by omega : e + i + 1 ≤ L),
    CoreLinearInsertion.orderStat_firstL L E (by omega : e + i ≤ L)]

def coreLocalStoppedMean (B S L w : ℕ) {k : ℕ} (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) (ν : Finset ℕ → ℝ)
    (f : AddCircle (1 : ℝ) → ℝ) : ℝ :=
  ∑ U ∈ (offsetWindow S).powerset.filter (fun U ↦ U.card = L),
    f (CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
      (CoreCyclic.orderedRealGap U) : AddCircle (1 : ℝ)) *
        Stopped.shortShapeMass (offsetWindow S) ν L U

theorem coreLocalStoppedMean_eq_fullConfiguration
    (B X S : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k)
    {w L : ℕ} (hwL : w ≤ L)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w) (f : AddCircle (1 : ℝ) → ℝ) :
    coreLocalStoppedMean B S L w hk phase F (finiteRootMix X S) f =
      corePositiveFiniteRootMean X S L (fun U ↦
        f (CoreCyclic.coreCyclicFinitePhase B hk phase F (L - w)
          (CoreCyclic.orderedRealGap U) : AddCircle (1 : ℝ))) := by
  rw [coreLocalStoppedMean, coreStopped_positive_test_eq_pushforward]
  simp_rw [coreCyclicFinitePhase_firstL B hk phase F hwL hw]
  rfl

theorem coreLocalStoppedMean_const_mul
    (B S L w : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k)
    (ν : Finset ℕ → ℝ) (c : ℝ) (f : AddCircle (1 : ℝ) → ℝ) :
    coreLocalStoppedMean B S L w hk phase F (fun U ↦ c * ν U) f =
      c * coreLocalStoppedMean B S L w hk phase F ν f := by
  unfold coreLocalStoppedMean
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

theorem coreLocalStoppedMean_unnormalized_eq
    (B X S L w : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (f : AddCircle (1 : ℝ) → ℝ)
    (hN : 0 < windowNX X) (hZ : 0 < mixZ X) :
    coreLocalStoppedMean B S L w hk phase F (finiteRootMixUnnorm X S) f =
      mixZeta X * coreLocalStoppedMean B S L w hk phase F (finiteRootMix X S) f := by
  have hfun : finiteRootMixUnnorm X S =
      fun U ↦ mixZeta X * finiteRootMix X S U := by
    funext U
    exact finiteRootMixUnnorm_eq_mixZeta_mul_finiteRootMix hN hZ S U
  rw [hfun, coreLocalStoppedMean_const_mul]

end
end PrimeGapNormality.Prime
