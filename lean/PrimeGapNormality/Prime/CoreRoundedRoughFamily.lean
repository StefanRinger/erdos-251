import PrimeGapNormality.Prime.CoreRoundedRoughNormality
import PrimeGapNormality.Prime.CoreIntegerGapLinearAlgebra
import PrimeGapNormality.Prime.JointWeyl
import PrimeGapNormality.Prime.CoreJointEquidistribution

/-!
# Literal finite families of rounded moving-rough gap powers

For one fixed rounding convention and a finite injective family of exponents
in `(0,1]`, this file defines the actual residue-labelled moving-rough gap
series.  A nonzero character has a maximal active exponent; changing only
the exponents attached to zero coefficients produces the compact-scaling
form required by the rounded S/T theorem, and injectivity prevents
cancellation of its active leading column.

The moving-rough Shape S, first-gap Tail T, count growth, and subexponential
gap growth are all derived internally.  No joint Weyl, leading-column,
model, reference, Shape S, or Tail T premise occurs in the public family
theorems.  A single `RoundKind` is shared by the whole family, so the result
does not assert mixed floor/ceiling independence.
-/

namespace PrimeGapNormality.Prime.CoreRoundedRoughFamily

open Finset Filter CoreCyclic
open CoreRoundedPowerScaling CoreIntegerGapObservable
open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSyntheticScale
open CoreSequenceSTConsumer CoreSequenceSubexponentialGrowth
open scoped Topology Classical BigOperators

noncomputable section

private theorem family_clock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    2 ≤ B ^ k := by
  have heq : k = k - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [heq, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

/-- The integer observable selecting one relative residue label and one
rounded exponent. -/
def roundedRoughBasisObservable {I : Type*} {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (p : Fin k × I)
    (s : Fin k) (q : ℕ) : ℤ :=
  if s = p.1 then roundedPower kind (alpha p.2) q else 0

/-- Literal residue-labelled rounded gap-power series on the canonical
moving-rough enumeration.  The label is relative to the fixed initial
phase `r`; the denominator is `B^(n+1)`. -/
def movingRoughRoundedResidueSeries {I : Type*} {k : ℕ}
    (Ψ : ℝ → ℝ) (B : ℕ) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (p : Fin k × I) : ℝ :=
  observableFullSeries B hk r (roundedRoughBasisObservable kind alpha p)
    (seqGap (movingRoughSequence (zPsi Ψ)))

/-- The floor family is the fixed-`floor` specialization of the literal
rounded family. -/
def movingRoughFloorResidueSeries {I : Type*} {k : ℕ}
    (Ψ : ℝ → ℝ) (B : ℕ) (hk : 0 < k) (r : Fin k)
    (alpha : I → ℝ) (p : Fin k × I) : ℝ :=
  movingRoughRoundedResidueSeries Ψ B hk r .floor alpha p

/-- The ceiling family is the fixed-`ceil` specialization of the literal
rounded family. -/
def movingRoughCeilResidueSeries {I : Type*} {k : ℕ}
    (Ψ : ℝ → ℝ) (B : ℕ) (hk : 0 < k) (r : Fin k)
    (alpha : I → ℝ) (p : Fin k × I) : ℝ :=
  movingRoughRoundedResidueSeries Ψ B hk r .ceil alpha p

private theorem roundedRoughBasisObservable_linear_bound
    {I : Type*} {k : ℕ} (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1) (p : Fin k × I)
    (s : Fin k) (q : ℕ) (hq : 1 ≤ q) :
    |(roundedRoughBasisObservable kind alpha p s q : ℝ)| ≤ 2 * (q : ℝ) := by
  by_cases hs : s = p.1
  · simp only [roundedRoughBasisObservable, hs, if_true]
    have hqR : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
    have hp := abs_roundedPower_le_rpow_add_one kind q (alpha := alpha p.2)
    have hpow : (q : ℝ) ^ alpha p.2 ≤ (q : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hqR (halpha p.2).2
    exact hp.trans (by linarith)
  · simp only [roundedRoughBasisObservable, hs, if_false, Int.cast_zero, abs_zero]
    positivity

private theorem roundedCombination_compactScaling
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a)) :
    CoreScaledGapModelReference.CompactScaling
      (roundedCombination kind alpha b) a
      (CoreRoundedModelSubsequence.integerLeadingColumn alpha b a) := by
  intro A hA eps heps
  have hh := eventually_roundedCombination_compact_expansion
    kind alpha b ha ha1 hA halpha eps heps
  filter_upwards [hh] with G hG
  intro s q hq
  rw [CoreRoundedModelSubsequence.integerLeadingColumn_cast]
  simpa only [roundedCombination_cast] using hG s q hq

private theorem roundedCombination_linearBound
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1) :
    ∀ s q, 1 ≤ q → |(roundedCombination kind alpha b s q : ℝ)| ≤
      CoreRoundedPrimeNormality.roundedLinearConstant b * (q : ℝ) :=
  CoreRoundedPrimeNormality.roundedCombination_linear_bound kind alpha b halpha

/-- Every nonzero integer character of the finite injective exponent family
is Weyl at the common clock `B^k`, using only the actual moving-rough
regularity hypotheses. -/
theorem movingRoughRoundedResidue_jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    JointWeyl (fun _ : Fin k × I ↦ B ^ k)
      (movingRoughRoundedResidueSeries Ψ B hk r kind alpha) := by
  let aSeq : ℕ → ℕ := movingRoughSequence (zPsi Ψ)
  let T : ℕ → ℕ := fun X ↦ roughSyntheticScale (zPsi Ψ X)
  have haSeq : StrictMono aSeq := movingRoughSequence_strictMono
    hSlope.eventually_zPsi_lt
  have hκpos : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hT : Tendsto T atTop atTop := by
    simpa only [T] using
      CoreRoughLocalNormality.tendsto_movingRoughModelScale hSlope
  have hTail : GapTailT aSeq (localTailBase κ) (windowG ∘ T) := by
    simpa only [aSeq, T] using
      CoreRoughLocalNormality.movingRough_gapTailT hκpos hSlope hC hreg
  have hS : SequencePositiveShapeS aSeq T κ 1 := by
    simpa only [aSeq, T] using
      CoreRoughAdverseLimit.sequencePositiveShapeS hκpos hSlope hC hreg
  have hcount :=
    CoreSequenceWindowGrowthFromS.windowCountToInfinity_of_shapeS_and_gapTail
      haSeq hκpos (by norm_num : (0 : ℝ) < 1) hT hS hTail
  have hg : HasSubexponentialGrowth (fun n ↦ (seqGap aSeq n : ℝ)) :=
    sequenceGap_hasSubexponentialGrowth haSeq hcount
  have hgapPos : ∀ n, 1 ≤ seqGap aSeq n := by
    intro n
    unfold seqGap
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.sub_ne_zero_of_lt (haSeq (Nat.lt_succ_self n)))
  intro t ht
  let active : Finset (Fin k × I) := univ.filter (fun p ↦ t p ≠ 0)
  have hactive : active.Nonempty := by
    obtain ⟨p, hp⟩ := ht
    exact ⟨p, mem_filter.mpr ⟨mem_univ p, hp⟩⟩
  obtain ⟨p, hp, hpmax⟩ := exists_max_image active
    (fun q : Fin k × I ↦ alpha q.2) hactive
  have htp : t p ≠ 0 := (mem_filter.mp hp).2
  let a : ℝ := alpha p.2
  let alpha' : Fin k × I → ℝ := fun q ↦ if t q = 0 then a else alpha q.2
  let b' : Fin k → (Fin k × I) → ℤ :=
    fun s q ↦ if s = q.1 then t q else 0
  have ha : 0 < a := by
    dsimp only [a]
    exact (halpha p.2).1
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact (halpha p.2).2
  have halpha' : ∀ q, 0 < alpha' q ∧ (alpha' q = a ∨ alpha' q < a) := by
    intro q
    by_cases htq : t q = 0
    · simp only [alpha', htq, if_true, ha, true_and, true_or]
    · have hqmem : q ∈ active := mem_filter.mpr ⟨mem_univ q, htq⟩
      have hle : alpha q.2 ≤ a := hpmax q hqmem
      simp only [alpha', htq, if_false]
      exact ⟨(halpha q.2).1, eq_or_lt_of_le hle⟩
  have halpha'Linear : ∀ q, 0 < alpha' q ∧ alpha' q ≤ 1 := by
    intro q
    exact ⟨(halpha' q).1, (halpha' q).2.elim (fun h ↦ h ▸ ha1)
      (fun h ↦ h.le.trans ha1)⟩
  have hlead :
      CoreRoundedModelSubsequence.integerLeadingColumn alpha' b' a ≠ 0 := by
    intro hz
    have hz' := congrFun hz p.1
    have heval :
        CoreRoundedModelSubsequence.integerLeadingColumn alpha' b' a p.1 = t p := by
      unfold CoreRoundedModelSubsequence.integerLeadingColumn
      rw [Fintype.sum_eq_single p]
      · simp [alpha', b', htp, a]
      · intro q hqp
        by_cases htq : t q = 0
        · simp [b', htq]
        · by_cases hs : p.1 = q.1
          · have hsecond : q.2 ≠ p.2 := by
              intro he
              apply hqp
              apply Prod.ext
              · exact hs.symm
              · exact he
            have hexp : alpha' q ≠ a := by
              simp only [alpha', htq, if_false, a]
              exact fun he ↦ hsecond (halphaInj he)
            simp only [hexp, if_false]
          · have hs' : p.1 ≠ q.1 := hs
            simp [b', hs']
    rw [heval] at hz'
    exact htp hz'
  have hobservable :
      CoreIntegerGapLinearAlgebra.integerCombination t
          (roundedRoughBasisObservable kind alpha) =
        roundedCombination kind alpha' b' := by
    funext s q
    unfold CoreIntegerGapLinearAlgebra.integerCombination
      roundedRoughBasisObservable roundedCombination
    apply sum_congr rfl
    intro u hu
    by_cases htu : t u = 0
    · simp [htu, b']
    · have hua : alpha' u = alpha u.2 := by simp [alpha', htu]
      rw [hua]
      by_cases hsu : s = u.1 <;> simp [b', hsu]
  have hlinear :=
    CoreIntegerGapLinearAlgebra.observableFullSeries_integerCombination
      hB hk r (seqGap aSeq) hgapPos hg t
      (roundedRoughBasisObservable kind alpha) (fun _ ↦ (2 : ℝ))
      (fun _ ↦ by norm_num)
      (fun u s q hq ↦
        roundedRoughBasisObservable_linear_bound kind alpha halpha u s q hq)
  have hseries :
      observableFullSeries B hk r (roundedCombination kind alpha' b')
          (seqGap aSeq) =
        ∑ q : Fin k × I, (t q : ℝ) *
          movingRoughRoundedResidueSeries Ψ B hk r kind alpha q := by
    rw [← hobservable]
    simpa only [movingRoughRoundedResidueSeries, aSeq] using hlinear
  have hW :=
    CoreScaledGapSTNormality.observableFullSeries_weyl_clock_of_shapeS
      haSeq hB hk r (roundedCombination kind alpha' b')
      (CoreRoundedPrimeNormality.roundedLinearConstant_nonneg b')
      (roundedCombination_linearBound kind alpha' b' halpha'Linear)
      ha ha1 (CoreRoundedModelSubsequence.integerLeadingColumn alpha' b' a)
      hlead
      (roundedCombination_compactScaling kind alpha' b' ha ha1 halpha')
      hκ (by norm_num : (0 : ℝ) < 1) hT hTail hS
  have hone := hW 1 (by norm_num)
  apply hone.congr'
  exact Eventually.of_forall fun N ↦ by
    apply congrArg (fun z : ℂ ↦ z / (N : ℂ))
    apply sum_congr rfl
    intro n hn
    apply congrArg e
    rw [hseries]
    simp only [Int.cast_one, one_mul, Finset.mul_sum]
    apply sum_congr rfl
    intro q hq
    ring

/-- Every nontrivial rational combination of the literal family is Weyl at
the common clock. -/
theorem movingRoughRoundedResidue_rationalCombination_weyl
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (q : Fin k × I → ℚ) (hq : ∃ i, q i ≠ 0) :
    weylCriterion (B ^ k)
      (∑ i, (q i : ℝ) *
        movingRoughRoundedResidueSeries Ψ B hk r kind alpha i) :=
  weylCriterion_linearCombination (family_clock_ge hB hk)
    (movingRoughRoundedResidue_jointWeyl hSlope hC hreg hB hk r kind
      alpha halpha halphaInj hκ) hq

/-- Every nontrivial rational combination is normal to the common clock
`B^k`. -/
theorem movingRoughRoundedResidue_rationalCombination_isNormal_clock
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (q : Fin k × I → ℚ) (hq : ∃ i, q i ≠ 0) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (∑ i, (q i : ℝ) *
        movingRoughRoundedResidueSeries Ψ B hk r kind alpha i) :=
  CoreWeylNormality.isNormal_of_weyl (family_clock_ge hB hk)
    (movingRoughRoundedResidue_rationalCombination_weyl
      hSlope hC hreg hB hk r kind alpha halpha halphaInj hκ q hq)

/-- The same rational combination is normal in the original base `B`. -/
theorem movingRoughRoundedResidue_rationalCombination_isNormal
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (q : Fin k × I → ℚ) (hq : ∃ i, q i ≠ 0) :
    PrimeGapNormality.BFree.IsNormal B
      (∑ i, (q i : ℝ) *
        movingRoughRoundedResidueSeries Ψ B hk r kind alpha i) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (weylCriterion_of_pow hB (by omega : 1 ≤ k)
      (movingRoughRoundedResidue_rationalCombination_weyl
        hSlope hC hreg hB hk r kind alpha halpha halphaInj hκ q hq))

/-- `1` and all residue/exponent components of the fixed family are
rationally linearly independent. -/
theorem movingRoughRoundedResidue_one_linearIndependent
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    LinearIndependent ℚ (fun i : Option (Fin k × I) ↦ match i with
      | none => (1 : ℝ)
      | some i => movingRoughRoundedResidueSeries Ψ B hk r kind alpha i) := by
  convert linearIndependent_one_jointWeyl (family_clock_ge hB hk)
    (movingRoughRoundedResidue_jointWeyl hSlope hC hreg hB hk r kind
      alpha halpha halphaInj hκ) using 1
  funext i
  cases i <;> rfl

/-- Actual empirical measures converge to product Haar, not only to a
named Fourier-test condition. -/
theorem movingRoughRoundedResidue_empirical_tendsto
    {I : Type*} [Fintype I] [DecidableEq I]
    {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ (1000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    Tendsto (CoreJointEquidistribution.empirical (fun _ : Fin k × I => B ^ k)
      (movingRoughRoundedResidueSeries Ψ B hk r kind alpha)) atTop
      (𝓝 (CoreJointEquidistribution.torusVolume (Fin k × I))) :=
  CoreJointEquidistribution.empirical_tendsto_of_jointWeyl
    (movingRoughRoundedResidue_jointWeyl hSlope hC hreg hB hk r kind
      alpha halpha halphaInj hκ)

end

end PrimeGapNormality.Prime.CoreRoundedRoughFamily
