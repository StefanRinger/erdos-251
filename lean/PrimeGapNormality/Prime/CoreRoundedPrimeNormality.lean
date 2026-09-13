import PrimeGapNormality.Prime.CoreIntegerGapDTransfer
import PrimeGapNormality.Prime.CoreRoundedModelSubsequence
import PrimeGapNormality.Prime.CoreResidueSubsequenceReference
import PrimeGapNormality.Prime.CoreAHLToD

/-!
# Rounded real gap powers on the actual prime sequence

This file closes the scalar rounded-power argument.  All summands use one
rounding convention (`floor` or `ceil`); nothing here asserts a mixed
floor/ceiling statement.

For a fixed finite integer combination of exponents in `(0,1]`, a nonzero
largest-exponent column supplies the compact insertion action.  The actual
D transfer and the actual rounded finite-model subsequence theorem then
give a physical-window subsequence reference bound.  The established
positive residue-class passage, followed by the exact integer period
recurrence, proves Weyl for the literal infinite series.

The relative label is fixed before every physical limit.  Absolute index
classes enter only through `primeResidue_character_cesaro_of_subsequence_reference`;
no marked prime-tuple estimate is assumed.
-/

namespace PrimeGapNormality.Prime.CoreRoundedPrimeNormality

open Finset Filter MeasureTheory CoreCyclic
open CoreRoundedPowerScaling CoreIntegerGapObservable
open CoreSequenceSubexponentialGrowth
open scoped Topology Classical NNReal BoundedContinuousFunction

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

private theorem clock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    2 ≤ B ^ k := by
  have heq : k = k - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [heq, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

private theorem primeGap_one_le (n : ℕ) : 1 ≤ primeGap n := by
  unfold primeGap
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.sub_ne_zero_of_lt (nthPrime_strictMono (Nat.lt_succ_self n)))

private theorem primeGap_subexponential :
    HasSubexponentialGrowth (fun n ↦ (primeGap n : ℝ)) := by
  have hcount : WindowCountToInfinity nthPrime := by
    have hreal := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      CorePrimeDensity.tendsto_windowNX_atTop
    simpa only [WindowCountToInfinity, seqWindow_nthPrime_card,
      Function.comp_def] using hreal
  simpa only [seqGap_nthPrime] using
    (sequenceGap_hasSubexponentialGrowth nthPrime_strictMono hcount)

/-- A single finite constant controls every label of the rounded
combination. -/
def roundedLinearConstant {I : Type*} [Fintype I] {k : ℕ}
    (b : Fin k → I → ℤ) : ℝ :=
  ∑ s, 2 * ∑ i, |(b s i : ℝ)|

theorem roundedLinearConstant_nonneg
    {I : Type*} [Fintype I] {k : ℕ} (b : Fin k → I → ℤ) :
    0 ≤ roundedLinearConstant b := by
  unfold roundedLinearConstant
  exact sum_nonneg fun s hs ↦ mul_nonneg (by norm_num)
    (sum_nonneg fun i hi ↦ abs_nonneg _)

theorem roundedCombination_linear_bound
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (s : Fin k) (q : ℕ) (hq : 1 ≤ q) :
    |(roundedCombination kind alpha b s q : ℝ)| ≤
      roundedLinearConstant b * (q : ℝ) := by
  rw [roundedCombination_cast]
  have hlocal := roundedCombinationReal_abs_le_linear kind alpha b halpha s hq
  have hcoeff : 2 * ∑ i, |(b s i : ℝ)| ≤ roundedLinearConstant b := by
    unfold roundedLinearConstant
    exact single_le_sum
      (f := fun t : Fin k ↦ (2 : ℝ) * ∑ i : I, |(b t i : ℝ)|)
      (fun t ht ↦ mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (sum_nonneg fun i hi ↦ abs_nonneg (b t i : ℝ))) (mem_univ s)
  exact hlocal.trans
    (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg q))

/-- Exact `B^k` orbit for the integer observable on the actual prime gaps. -/
theorem observablePrimeOrbit_add_period
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ)) (n : ℕ) :
    (observableSeries B hk r F primeGap (n + k) : Circle) =
      B ^ k • (observableSeries B hk r F primeGap n : Circle) :=
  observableSeriesCircle_add_period hB hk r F primeGap_one_le
    primeGap_subexponential hC hF n

private theorem fourier_nsmul (z : ℤ) (C q : ℕ) (x : ℝ) :
    fourier z (C ^ q • (x : Circle)) =
      e ((z : ℝ) * (C : ℝ) ^ q * x) := by
  rw [← AddCircle.coe_nsmul, fourier_coe_apply]
  simp only [nsmul_eq_mul, Nat.cast_pow, e, Complex.ofReal_one, div_one,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

/-- The true positive residue-class passage turns a subsequence reference
bound for the restarted observable into Weyl for its literal full series.
The zero class is selected only after the unmarked physical-window bound. -/
theorem observableFullSeries_weyl_clock_of_subsequence_reference
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    (hbound : CoreResidueDigitalReference.SubsequenceReferenceBounds
      (fun n ↦ (observableSeries B hk r F primeGap n : Circle))
      (fun X ↦ Nat.primeCounting X) windowNX) :
    weylCriterion (B ^ k) (observableFullSeries B hk r F primeGap) := by
  have hk1 : 1 ≤ k := by omega
  have hrec := observablePrimeOrbit_add_period hB hk r F hC hF
  intro z hz
  have hchar :=
    CorePrimeResiduePassage.primeResidue_character_cesaro_of_subsequence_reference
      (clock_ge hB hk) hk1 (r := 0) (by omega : 0 < k)
      (fun n ↦ (observableSeries B hk r F primeGap n : Circle)) hrec hbound hz
  unfold CesaroMeanVanishing at hchar
  apply hchar.congr'
  exact Eventually.of_forall fun N ↦ by
    apply congrArg (fun v : ℂ ↦ v / (N : ℂ))
    apply sum_congr rfl
    intro q hq
    have horbit := CoreCyclic.circleOrbit_of_add_period
      (u := fun n ↦ (observableSeries B hk r F primeGap n : Circle))
      (C := B ^ k) (k := k) hrec 0 q
    have horbit' :
        (observableSeries B hk r F primeGap (k * q) : Circle) =
          (B ^ k) ^ q • (observableFullSeries B hk r F primeGap : Circle) := by
      simpa only [Nat.zero_add, observableFullSeries] using horbit
    change fourier z
      (observableSeries B hk r F primeGap (q * k + 0) : Circle) = _
    rw [show q * k + 0 = k * q by simp only [Nat.add_zero, Nat.mul_comm], horbit']
    exact fourier_nsmul z (B ^ k) q _

/-- The actual rounded finite-model subsequence theorem and D give the
physical subsequence reference contract needed by the residue passage. -/
theorem rounded_subsequenceReference_of_D
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (hb : leadingColumn alpha b a ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {d0 c : ℝ} (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    CoreResidueDigitalReference.SubsequenceReferenceBounds
      (fun n ↦ (observableSeries B hk r
        (roundedCombination kind alpha b) primeGap n : Circle))
      (fun X ↦ Nat.primeCounting X) windowNX := by
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hC : 0 ≤ roundedLinearConstant b := roundedLinearConstant_nonneg b
  have halphaLinear : ∀ i, 0 < alpha i ∧ alpha i ≤ 1 := by
    intro i
    refine ⟨(halpha i).1, ?_⟩
    exact (halpha i).2.elim (fun h ↦ h ▸ ha1) (fun h ↦ h.le.trans ha1)
  have hlin : ∀ s q, 1 ≤ q →
      |(roundedCombination kind alpha b s q : ℝ)| ≤
        roundedLinearConstant b * (q : ℝ) :=
    roundedCombination_linear_bound kind alpha b halphaLinear
  intro φ hφ
  obtain ⟨ψ, hψ, σ, hσfinite, hσac, hσmass, hmodel⟩ :=
    CoreRoundedModelSubsequence.exists_reference_subsequence
      hB hk r kind alpha b ha ha1 halpha hb hκ φ hφ.tendsto_atTop
  refine ⟨ψ, hψ, σ, hσfinite, hσac,
    16 * c * CoreRoundedModelSubsequence.modelConstant,
    mul_nonneg (mul_nonneg (by norm_num) hcpos.le)
      CoreRoundedModelSubsequence.modelConstant_nonneg, ?_⟩
  intro f K hK hf eps heps
  have heps2 : 0 < eps / 2 := half_pos heps
  have hsmall : 0 < eps / (32 * c) :=
    div_pos heps (mul_pos (by norm_num) hcpos)
  have hindices : Tendsto (fun n ↦ φ (ψ n)) atTop atTop :=
    hφ.tendsto_atTop.comp hψ.tendsto_atTop
  have harith := hindices.eventually
    (CoreIntegerGapDTransfer.eventually_prime_observableMean_le_finiteRootModel_of_D
      hB hk r (roundedCombination kind alpha b) hC hlin hκ hd0 hc hD
      f hK hf heps2)
  have hmod := hmodel f K hK hf (eps / (32 * c)) hsmall
  filter_upwards [harith, hmod] with n hn hm
  have hm' : CoreIntegerGapDTransfer.finiteRootModelMean B (φ (ψ n))
      (ahlSmall_window κ (φ (ψ n))) (profileL κ (φ (ψ n))) hk r
      (roundedCombination kind alpha b) f ≤
        CoreRoundedModelSubsequence.modelConstant * (∫ x, f x ∂σ) +
          eps / (32 * c) := by
    simpa only [CoreIntegerGapDTransfer.finiteRootModelMean,
      CoreRoundedModelSubsequence.profileMean] using hm
  have hmul := mul_le_mul_of_nonneg_left hm'
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hcpos.le)
  have herr : 16 * c * (eps / (32 * c)) = eps / 2 := by
    field_simp [hcpos.ne']
    ring
  rw [mul_add, herr] at hmul
  exact hn.trans (by
    calc
      16 * c * CoreIntegerGapDTransfer.finiteRootModelMean B (φ (ψ n))
            (ahlSmall_window κ (φ (ψ n))) (profileL κ (φ (ψ n))) hk r
            (roundedCombination kind alpha b) f + eps / 2 ≤
          (16 * c * CoreRoundedModelSubsequence.modelConstant) *
              (∫ x, f x ∂σ) + eps / 2 + eps / 2 :=
        by simpa only [mul_assoc] using _root_.add_le_add hmul (le_refl (eps / 2))
      _ = (16 * c * CoreRoundedModelSubsequence.modelConstant) *
            (∫ x, f x ∂σ) + eps := by ring)

/-- Scalar actual rounded-combination Weyl theorem at the common clock. -/
theorem roundedCombination_weyl_clock_of_D
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (hb : leadingColumn alpha b a ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {d0 c : ℝ} (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    weylCriterion (B ^ k)
      (observableFullSeries B hk r (roundedCombination kind alpha b) primeGap) := by
  have halphaLinear : ∀ i, 0 < alpha i ∧ alpha i ≤ 1 := by
    intro i
    refine ⟨(halpha i).1, ?_⟩
    exact (halpha i).2.elim (fun h ↦ h ▸ ha1) (fun h ↦ h.le.trans ha1)
  let C := roundedLinearConstant b
  have hC : 0 ≤ C := roundedLinearConstant_nonneg b
  have hlin : ∀ s q, 1 ≤ q →
      |(roundedCombination kind alpha b s q : ℝ)| ≤ C * (q : ℝ) :=
    roundedCombination_linear_bound kind alpha b halphaLinear
  exact observableFullSeries_weyl_clock_of_subsequence_reference hB hk r
    (roundedCombination kind alpha b) hC hlin
    (rounded_subsequenceReference_of_D hB hk r kind alpha b ha ha1 halpha hb
      hκ hd0 hc hD)

theorem roundedCombination_weyl_of_D
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (hb : leadingColumn alpha b a ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {d0 c : ℝ} (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    weylCriterion B
      (observableFullSeries B hk r (roundedCombination kind alpha b) primeGap) :=
  weylCriterion_of_pow hB (by omega : 1 ≤ k)
    (roundedCombination_weyl_clock_of_D hB hk r kind alpha b ha ha1
      halpha hb hκ hd0 hc hD)

theorem roundedCombination_isNormal_clock_of_D
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (hb : leadingColumn alpha b a ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {d0 c : ℝ} (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (observableFullSeries B hk r (roundedCombination kind alpha b) primeGap) :=
  CoreWeylNormality.isNormal_of_weyl (clock_ge hB hk)
    (roundedCombination_weyl_clock_of_D hB hk r kind alpha b ha ha1
      halpha hb hκ hd0 hc hD)

theorem roundedCombination_isNormal_of_D
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (hb : leadingColumn alpha b a ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {d0 c : ℝ} (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    PrimeGapNormality.BFree.IsNormal B
      (observableFullSeries B hk r (roundedCombination kind alpha b) primeGap) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (roundedCombination_weyl_of_D hB hk r kind alpha b ha ha1
      halpha hb hκ hd0 hc hD)

theorem roundedCombination_irrational_of_D
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (hb : leadingColumn alpha b a ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {d0 c : ℝ} (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    Irrational
      (observableFullSeries B hk r (roundedCombination kind alpha b) primeGap) :=
  weylCriterion_irrational
    (roundedCombination_weyl_of_D hB hk r kind alpha b ha ha1
      halpha hb hκ hd0 hc hD)

/-- The small-window AHL input supplies the same D endpoint. -/
theorem roundedCombination_isNormal_clock_of_AHL
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (hb : leadingColumn alpha b a ≠ 0)
    (hκpos : 0 < κ) (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hAHL : ahlSmall_AHL κ 20) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (observableFullSeries B hk r (roundedCombination kind alpha b) primeGap) :=
  roundedCombination_isNormal_clock_of_D hB hk r kind alpha b ha ha1
    halpha hb hκ (by norm_num) (by norm_num)
    (CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκpos hAHL)

/-- Kuperberg supplies D at every fixed admissible rounded profile. -/
theorem roundedCombination_isNormal_clock_of_kuperberg
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (hb : leadingColumn alpha b a ≠ 0)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hK : KuperbergConj13) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (observableFullSeries B hk r (roundedCombination kind alpha b) primeGap) := by
  have hκpos : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  exact roundedCombination_isNormal_clock_of_D hB hk r kind alpha b ha ha1
    halpha hb hκ (by norm_num) (by norm_num)
    (coreLinearD_of_kuperberg hK hκpos)

end

end PrimeGapNormality.Prime.CoreRoundedPrimeNormality
