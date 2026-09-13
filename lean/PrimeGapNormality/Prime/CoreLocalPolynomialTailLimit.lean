import PrimeGapNormality.Prime.CoreLocalPolynomialTail
import PrimeGapNormality.Prime.CoreLocalSeriesRecurrence
import PrimeGapNormality.Prime.PhysicalRemainderOfGapTail
import PrimeGapNormality.Prime.TailMinOne

/-!
# Infinite local-polynomial tail from a first-gap tail

The finite local-polynomial estimate is combined here with the existing
natural-power tail comparison.  The resulting infinite remainder is
controlled by the first-moment scaled gap tail.  No moment hypothesis on
polynomial powers of the gaps is introduced.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Filter Finset MvPolynomial
open scoped BigOperators Topology

noncomputable section

/-- Sum of the `w+1` consecutive gaps seen by a width-`w` local
polynomial. -/
def localGapWindow (w : ℕ) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (w + 1), g (n + i)

theorem localGapWindow_nonneg (w : ℕ) {g : ℕ → ℝ}
    (hg : ∀ i, 0 ≤ g i) (n : ℕ) :
    0 ≤ localGapWindow w g n :=
  sum_nonneg fun i _ ↦ hg (n + i)

theorem localGapWindow_one_le (w : ℕ) {g : ℕ → ℝ}
    (hg : ∀ i, 1 ≤ g i) (n : ℕ) :
    1 ≤ localGapWindow w g n := by
  unfold localGapWindow
  exact (hg n).trans
    (single_le_sum (fun i _ ↦ zero_le_one.trans (hg (n + i)))
      (mem_range.mpr (Nat.zero_lt_succ w)))

/-- A finite sum of shifted first-gap tails is summable. -/
theorem summable_localGapWindow_div
    (w : ℕ) (g : ℕ → ℝ) {rho : ℝ} (q : ℕ)
    (hsm : ∀ a : ℕ, Summable fun j : ℕ ↦ g (a + j) / rho ^ (j + 1)) :
    Summable fun j : ℕ ↦ localGapWindow w g (q + j) / rho ^ (j + 1) := by
  have hi : ∀ i ∈ range (w + 1),
      Summable fun j : ℕ ↦ g (q + j + i) / rho ^ (j + 1) := by
    intro i _
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsm (q + i)
  have hs := summable_sum hi
  apply hs.congr
  intro j
  unfold localGapWindow
  rw [Finset.sum_div]

/-- The first `K` terms of the relative-label series. -/
def coreLocalSeriesTrunc (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F : PeriodicLocal k) (n K : ℕ) : ℝ :=
  ∑ i ∈ range K,
    relativeLocalValue hk r g F n i / (B : ℝ) ^ (i + 1)

/-- Difference between the true relative-label local series and its first
`K` terms. -/
def coreLocalSeriesRemainder (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F : PeriodicLocal k) (n K : ℕ) : ℝ :=
  coreLocalSeries B hk r g F n - coreLocalSeriesTrunc B hk r g F n K

theorem coreLocalSeriesRemainder_eq_tsum
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F : PeriodicLocal k) (n K : ℕ)
    (hsm : Summable fun i : ℕ ↦
      relativeLocalValue hk r g F n i / (B : ℝ) ^ (i + 1)) :
    coreLocalSeriesRemainder B hk r g F n K =
      ∑' j : ℕ,
        relativeLocalValue hk r g F n (K + j) /
          (B : ℝ) ^ (K + j + 1) := by
  have hsplit := hsm.sum_add_tsum_nat_add K
  unfold coreLocalSeriesRemainder coreLocalSeries coreLocalSeriesTrunc
  have htail :
      (∑' j : ℕ,
        relativeLocalValue hk r g F n (j + K) / (B : ℝ) ^ (j + K + 1)) =
      ∑' j : ℕ,
        relativeLocalValue hk r g F n (K + j) /
          (B : ℝ) ^ (K + j + 1) := by
    apply tsum_congr
    intro j
    congr 2 <;> omega
  rw [← hsplit, add_sub_cancel_left, htail]

private theorem localLinearShift_summable
    {rho : ℝ} (hrho : 1 < rho) (h : ℕ → ℝ) (n K : ℕ)
    (hsm : Summable fun j : ℕ ↦ h (n + K + j) / rho ^ (j + 1)) :
    Summable fun j : ℕ ↦ h (n + K + j) / rho ^ (K + j + 1) := by
  have hrho0 : rho ≠ 0 := (zero_lt_one.trans hrho).ne'
  have hfun :
      (fun j : ℕ ↦ h (n + K + j) / rho ^ (K + j + 1)) =
        fun j : ℕ ↦ (rho ^ K)⁻¹ *
          (h (n + K + j) / rho ^ (j + 1)) := by
    funext j
    rw [show K + j + 1 = K + (j + 1) by omega, pow_add]
    field_simp [pow_ne_zero K hrho0, pow_ne_zero (j + 1) hrho0]
  rw [hfun]
  exact hsm.mul_left (rho ^ K)⁻¹

private theorem linearGapTailTrunc_le_scaled
    {rho : ℝ} (hrho : 1 < rho) (h : ℕ → ℝ) (n K N : ℕ)
    (hh : ∀ i, 0 ≤ h i)
    (hsm : Summable fun j : ℕ ↦ h (n + K + j) / rho ^ (j + 1)) :
    linearGapTailTrunc rho h n K (K + N) ≤
      scaledGapTail rho h n K := by
  have hs := localLinearShift_summable hrho h n K hsm
  rw [linearGapTailTrunc, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  rw [scaledGapTail_eq_linear_tsum hrho hsm]
  simpa only [Nat.add_assoc] using
    hs.sum_le_tsum (range N) (fun j _ ↦
      div_nonneg (hh _) (pow_nonneg (zero_lt_one.trans hrho).le _))

private theorem finite_localTail_abs_le_scaled_pow
    {B d : ℕ} {rho : ℝ} (hrho : 1 < rho) (hB : 2 ≤ B)
    (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : PeriodicLocal k)
    (w n K N : ℕ) (g : ℕ → ℝ)
    (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hg : ∀ i, 1 ≤ g i)
    (hsm : Summable fun j : ℕ ↦
      localGapWindow w g (n + K + j) / rho ^ (j + 1)) :
    (∑ j ∈ range N,
      |relativeLocalValue hk r g F n (K + j) /
        (B : ℝ) ^ (K + j + 1)|) ≤
      localTupleCoeffMass F *
        scaledGapTail rho (localGapWindow w g) n K ^ d := by
  let h : ℕ → ℝ := localGapWindow w g
  let C : ℝ := localTupleCoeffMass F
  have hC : 0 ≤ C := localTupleCoeffMass_nonneg F
  have hh : ∀ q, 0 ≤ h q := fun q ↦
    localGapWindow_nonneg w (fun i ↦ zero_le_one.trans (hg i)) q
  have hterm : ∀ j ∈ range N,
      |relativeLocalValue hk r g F n (K + j) /
        (B : ℝ) ^ (K + j + 1)| ≤
        C * h (n + K + j) ^ d / (B : ℝ) ^ (K + j + 1) := by
    intro j _
    have hv := abs_localValue_le_localTupleCoeffMass_mul_sum_pow
      hk r F w d (K + j) (fun q ↦ g (n + q)) hw hd (fun q ↦ hg (n + q))
    have hv' : |relativeLocalValue hk r g F n (K + j)| ≤
        C * h (n + K + j) ^ d := by
      simpa only [relativeLocalValue, localValue, C, h, localGapWindow,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv
    have hden : 0 ≤ (B : ℝ) ^ (K + j + 1) := pow_nonneg (Nat.cast_nonneg _) _
    rw [abs_div, abs_of_nonneg hden]
    exact div_le_div_of_nonneg_right hv' hden
  have hsum := sum_le_sum hterm
  have hrewrite :
      (∑ j ∈ range N,
        C * h (n + K + j) ^ d / (B : ℝ) ^ (K + j + 1)) =
        C * gapPowerRemainderTrunc h B d n K (K + N) := by
    unfold gapPowerRemainderTrunc
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [Nat.add_assoc]
    ring
  rw [hrewrite] at hsum
  have hpower := gapPowerRemainderTrunc_le_pow_linearGapTailTrunc
    h n K (K + N) hrho hB hbase hd0 le_rfl hh
  have hlin := linearGapTailTrunc_le_scaled hrho h n K N hh hsm
  have hlin0 : 0 ≤ linearGapTailTrunc rho h n K (K + N) :=
    sum_nonneg fun j _ ↦
      div_nonneg (hh _) (pow_nonneg (zero_lt_one.trans hrho).le _)
  have hpow := pow_le_pow_left₀ hlin0 hlin d
  exact hsum.trans ((mul_le_mul_of_nonneg_left (hpower.trans hpow) hC))

/-- Infinite local remainder bounded by a power of a first-moment scaled
gap tail. -/
theorem abs_coreLocalSeriesRemainder_le_scaledGapTail_pow
    {B d : ℕ} {rho : ℝ} (hrho : 1 < rho) (hB : 2 ≤ B)
    (hbase : rho ^ d ≤ (B : ℝ))
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : PeriodicLocal k)
    (w n K : ℕ) (g : ℕ → ℝ)
    (hd0 : 1 ≤ d)
    (hw : ∀ s i, i ∈ (F s).vars → i ≤ w)
    (hd : ∀ s, (F s).totalDegree ≤ d)
    (hg : ∀ i, 1 ≤ g i)
    (hgrowth : HasPolynomialGrowth g)
    (hsmGap : ∀ a : ℕ, Summable fun j : ℕ ↦
      g (a + j) / rho ^ (j + 1)) :
    |coreLocalSeriesRemainder B hk r g F n K| ≤
      localTupleCoeffMass F *
        scaledGapTail rho (localGapWindow w g) n K ^ d := by
  have hlocal := relativeLocalSeries_summable hB hk r g hgrowth F n
  rw [coreLocalSeriesRemainder_eq_tsum B hk r g F n K hlocal]
  let term : ℕ → ℝ := fun j ↦
    relativeLocalValue hk r g F n (K + j) / (B : ℝ) ^ (K + j + 1)
  have hterm : Summable term := by
    have hs := (summable_nat_add_iff K).2 hlocal
    apply hs.congr
    intro j
    dsimp only [term]
    congr 2 <;> omega
  have hsmWindow : Summable fun j : ℕ ↦
      localGapWindow w g (n + K + j) / rho ^ (j + 1) :=
    summable_localGapWindow_div w g (n + K) hsmGap
  have hbound : ∀ N : ℕ,
      ∑ j ∈ range N, |term j| ≤
        localTupleCoeffMass F *
          scaledGapTail rho (localGapWindow w g) n K ^ d := by
    intro N
    exact finite_localTail_abs_le_scaled_pow hrho hB hbase hk r F w n K N g
      hd0 hw hd hg hsmWindow
  have htsum := Real.tsum_le_of_sum_range_le (fun j ↦ abs_nonneg (term j)) hbound
  exact (norm_tsum_le_tsum_norm hterm.norm).trans htsum

end

end PrimeGapNormality.Prime.CoreCyclic
