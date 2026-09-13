import PrimeGapNormality.Prime.MertensAbelianBridge
import PrimeGapNormality.Prime.FiniteRootMixSmallMomentBound
import PrimeGapNormality.Prime.FiniteRootMixSmallRemainder
import PrimeGapNormality.Prime.FiniteRootMixSmallFailure

/-!
# Unconditional small finite-root-mix costs

The Mertens--Abelian bridge supplies the Euler-product lower tail used by
the small-model moment, Bonferroni remainder, and failure-mass bounds.
The failure bound deliberately retains the explicit lower-count exception.
-/

open Filter
open scoped Topology

namespace PrimeGapNormality.Prime

noncomputable section

theorem finiteRootMix_small_countMoment_le_five
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, ∀ j : ℕ,
      Stopped.countMoment (ahlSmall_omega κ X)
        (finiteRootMix X (ahlSmall_window κ X)) j
      ≤ ((5 : ℝ) * (profileL κ X : ℝ)) ^ j /
          (j.factorial : ℝ) := by
  exact finiteRootMix_small_countMoment_le_five_of_euler_tail hκ
    eventually_half_lt_eulerProdNat_mul_log

theorem tendsto_finiteRootMix_small_modelRemainder
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      Stopped.modelRemainder (ahlSmall_omega κ X)
        (finiteRootMix X (ahlSmall_window κ X))
        (profileL κ X) (profileR (profileL κ X) 20))
      atTop (nhds 0) := by
  exact tendsto_finiteRootMix_small_modelRemainder_of_euler_tail hκ
    eventually_half_lt_eulerProdNat_mul_log

theorem finiteRootMix_small_failureMass_le_lowerException
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      Stopped.failureMass (ahlSmall_omega κ X)
          (finiteRootMix X (ahlSmall_window κ X)) (profileL κ X) ≤
        (500 : ℝ) / (profileL κ X : ℝ) +
          finiteRootMixSmallLowerException κ X := by
  exact eventually_finiteRootMix_small_failureMass_le_lowerException hκ
    eventually_half_lt_eulerProdNat_mul_log

end

end PrimeGapNormality.Prime
