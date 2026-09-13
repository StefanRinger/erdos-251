import PrimeGapNormality.Prime.CoreLocalPositiveTailBridge
import PrimeGapNormality.Prime.CoreLinearCriticalRank

/-!
# Local phase tail at the supplied `κ` profile

For `κ ≥ d / log B`, take `rho = exp (1/κ)`.  Then `rho^d ≤ B` and the
`rho`-based standard cutoff is definitionally the paper cutoff
`profileL κ X`.  This transports the local positive-test remainder theorem
to every supplied admissible `κ`, including the non-strict endpoint.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

noncomputable section

/-- Tail base corresponding to the supplied profile coefficient. -/
def localTailBase (κ : ℝ) : ℝ :=
  Real.exp (1 / κ)

theorem localTailBase_one_lt {κ : ℝ} (hκ : 0 < κ) :
    1 < localTailBase κ := by
  unfold localTailBase
  exact Real.one_lt_exp_iff.mpr (div_pos zero_lt_one hκ)

theorem localTailBase_profileCoefficient {κ : ℝ} (hκ : 0 < κ) :
    1 / Real.log (localTailBase κ) = κ := by
  unfold localTailBase
  rw [Real.log_exp]
  field_simp [hκ.ne']

/-- The degree-`d` base comparison at the exact non-strict endpoint
`κ = d / log B`. -/
theorem localTailBase_pow_le
    {B d : ℕ} (hB : 2 ≤ B) (hd : 1 ≤ d) {κ : ℝ}
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    localTailBase κ ^ d ≤ (B : ℝ) := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos hBr
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hκpos : 0 < κ :=
    (div_pos hdR hlogB).trans_le hκ
  have hmul : (d : ℝ) ≤ κ * Real.log (B : ℝ) :=
    (div_le_iff₀ hlogB).mp hκ
  have hquot : (d : ℝ) / κ ≤ Real.log (B : ℝ) :=
    (div_le_iff₀ hκpos).mpr (by simpa only [mul_comm] using hmul)
  unfold localTailBase
  rw [← Real.exp_nat_mul]
  calc
    Real.exp ((d : ℝ) * (1 / κ)) ≤ Real.exp (Real.log (B : ℝ)) := by
      apply Real.exp_le_exp.mpr
      simpa only [div_eq_mul_inv, one_mul] using hquot
    _ = (B : ℝ) := Real.exp_log (zero_lt_one.trans hBr)

/-- Exact identification of the two cutoff notations for the chosen tail
base. -/
theorem profileL_eq_stdProfileL_localTailBase {κ : ℝ} (hκ : 0 < κ)
    (X : ℕ) :
    profileL κ X = stdProfileL (localTailBase κ) (windowG X) := by
  rw [CoreLinearInsertion.stdProfileL_eq_linearProfileL,
    localTailBase_profileCoefficient hκ]
  rfl

/-- Actual bounded Lipschitz local-phase remainder at the supplied paper
profile.  The only restriction is `κ ≥ d / log B`; the unconditional prime
gap tail theorem supplies all analytic convergence. -/
theorem tendsto_primeGap_localPositiveTestRemainder_profileL_zero
    {B d : ℕ} (hB : 2 ≤ B) (hd : 1 ≤ d) {κ : ℝ}
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    {k : ℕ} (hk : 0 < k) (phase : Fin k) (F : PeriodicLocal k)
    (w : ℕ) (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hdeg : ∀ s, (F s).totalDegree ≤ d)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    Tendsto (fun X : ℕ ↦
      windowAvgReal (seqWindow nthPrime X) (fun n ↦
        |f (coreLocalSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F n :
              AddCircle (1 : ℝ)) -
          f (coreLocalSeriesTrunc B hk phase (fun q ↦ (primeGap q : ℝ)) F n
              (profileL κ X - w) : AddCircle (1 : ℝ))|))
      atTop (𝓝 0) := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos hBr
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hκpos : 0 < κ := (div_pos hdR hlogB).trans_le hκ
  have htail := tendsto_primeGap_localPositiveTestRemainder_zero
    hB (localTailBase_one_lt hκpos) (localTailBase_pow_le hB hd hκ)
    hk phase F w hd hw hdeg f hK
  simpa only [← profileL_eq_stdProfileL_localTailBase hκpos] using htail

end

end PrimeGapNormality.Prime.CoreCyclic
