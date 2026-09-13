import PrimeGapNormality.Prime.CoreGeneralRoundedST
import PrimeGapNormality.Prime.CoreIntegerGapLinearAlgebra
import PrimeGapNormality.Prime.CoreJointEquidistribution

/-!
# Actual finite rounded families under arbitrary-mixture S/T

Every frequency selects its maximal active exponent. Equal exponents are
grouped by the actual residue label; injectivity prevents cancellation.
The exact series identity uses sequence-generic summability and linearity,
not a prime-gap specialization. One rounding convention is fixed throughout.
-/
namespace PrimeGapNormality.Prime.CoreGeneralRoundedFamily
open Finset Filter MeasureTheory CoreCyclic CoreIntegerGapObservable CoreRoundedPowerScaling
open CoreGeneralRoundedST CoreGeneralSequenceST CoreSequenceSTMeanTail CoreGeneralModelReference
open CoreCalibratedMixtureFiniteSupport CoreSequenceSubexponentialGrowth
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

def basisObservable {I : Type*} {k : ℕ} (kind : RoundKind) (alpha : I → ℝ)
    (p : Fin k × I) (s : Fin k) (q : ℕ) : ℤ :=
  if s = p.1 then roundedPower kind (alpha p.2) q else 0

def residueSeries {I : Type*} (a : ℕ → ℕ) (B : ℕ) {k : ℕ} (hk : 0 < k)
    (r : Fin k) (kind : RoundKind) (alpha : I → ℝ) (p : Fin k × I) : ℝ :=
  observableFullSeries B hk r (basisObservable kind alpha p) (seqGap a)

theorem basis_linear {I : Type*} {k : ℕ} (kind : RoundKind) (alpha : I → ℝ)
    (hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1) (p : Fin k × I) (s : Fin k) (q : ℕ) (hq : 1 ≤ q) :
    |(basisObservable kind alpha p s q : ℝ)| ≤ 2 * (q : ℝ) := by
  by_cases hs : s = p.1
  · simp only [basisObservable, hs, if_true]
    have hqR : (1 : ℝ) ≤ q := Nat.one_le_cast.2 hq
    have hp := abs_roundedPower_le_rpow_add_one kind q (alpha := alpha p.2)
    have hpow : (q : ℝ) ^ alpha p.2 ≤ (q : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hqR (hα p.2).2
    exact hp.trans (by linarith)
  · simp only [basisObservable, hs, if_false, Int.cast_zero, abs_zero]
    positivity

/-- An algebraic active-maximum choice. No leading-column nonvanishing is
assumed for the combination: it is derived from the nonzero frequency. -/
theorem exists_active_leading {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (hinj : Function.Injective alpha) (t : Fin k × I → ℤ) (ht : ∃ p, t p ≠ 0) :
    ∃ exponent : ℝ, 0 < exponent ∧ exponent ≤ 1 ∧
      ∃ alpha' : Fin k × I → ℝ, ∃ b' : Fin k → (Fin k × I) → ℤ,
        (∀ p, 0 < alpha' p ∧ (alpha' p = exponent ∨ alpha' p < exponent)) ∧
        leadingColumn alpha' b' exponent ≠ 0 ∧
        CoreIntegerGapLinearAlgebra.integerCombination t (basisObservable kind alpha) =
          roundedCombination kind alpha' b' := by
  let active : Finset (Fin k × I) := univ.filter fun p => t p ≠ 0
  have hactive : active.Nonempty := by
    obtain ⟨p, hp⟩ := ht
    exact ⟨p, mem_filter.2 ⟨mem_univ p, hp⟩⟩
  obtain ⟨p, hp, hpmax⟩ := exists_max_image active (fun p => alpha p.2) hactive
  have htp : t p ≠ 0 := (mem_filter.1 hp).2
  let exponent := alpha p.2
  let alpha' : Fin k × I → ℝ := fun q => if t q = 0 then exponent else alpha q.2
  let b' : Fin k → (Fin k × I) → ℤ := fun s q => if s = q.1 then t q else 0
  refine ⟨exponent, (hα p.2).1, (hα p.2).2, alpha', b', ?_, ?_, ?_⟩
  · intro q
    by_cases htq : t q = 0
    · simpa only [alpha', htq, if_true] using
        (show 0 < exponent ∧ (exponent = exponent ∨ exponent < exponent) from
          ⟨(hα p.2).1, Or.inl rfl⟩)
    · simp only [alpha', htq, if_false]
      exact ⟨(hα q.2).1, eq_or_lt_of_le (hpmax q (mem_filter.2 ⟨mem_univ q, htq⟩))⟩
  · intro hz
    have heval : leadingColumn alpha' b' exponent p.1 = (t p : ℝ) := by
      unfold leadingColumn
      rw [Fintype.sum_eq_single p]
      · simp [alpha', b', htp, exponent]
      · intro q hqp
        by_cases htq : t q = 0
        · simp [b', htq]
        · by_cases hs : p.1 = q.1
          · have hsecond : q.2 ≠ p.2 := by
              intro he
              exact hqp (Prod.ext hs.symm he)
            have hexp : alpha' q ≠ exponent := by
              simp only [alpha', htq, if_false, exponent]
              exact fun he => hsecond (hinj he)
            simp only [hexp, if_false]
          · simp [b', hs]
    have hz' := congrFun hz p.1
    rw [heval] at hz'
    exact htp (Int.cast_eq_zero.1 hz')
  · funext s q
    unfold CoreIntegerGapLinearAlgebra.integerCombination basisObservable roundedCombination
    apply sum_congr rfl
    intro u hu
    by_cases htu : t u = 0
    · simp [htu, b']
    · have hua : alpha' u = alpha u.2 := by simp [alpha', htu]
      rw [hua]
      by_cases hsu : s = u.1 <;> simp [b', hsu]

theorem residue_jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (hinj : Function.Injective alpha) {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    JointWeyl (fun _ : Fin k × I => B ^ k) (residueSeries a B hk r kind alpha) := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hs := shapeS_of_patternS hκp hG hω hsum hcal (patternS_of_complex hS)
    (meanGapTail_eventually_nonempty hT)
  have hcount := windowCountToInfinity ha hκp (by norm_num : (0 : ℝ) < 1)
    hG hω hsum hcal hs (meanGapTail_eventually_nonempty hT)
  have hg := sequenceGap_hasSubexponentialGrowth ha hcount
  have hgap : ∀ n, 1 ≤ seqGap a n := by
    intro n
    unfold seqGap
    exact Nat.one_le_iff_ne_zero.2 (Nat.sub_ne_zero_of_lt (ha (Nat.lt_succ_self n)))
  intro t ht
  obtain ⟨exponent, he, he1, alpha', b', hα', hb', hobs⟩ := exists_active_leading kind alpha hα hinj t ht
  have hW := roundedCombination_weyl ha hB hk r kind alpha' b' he he1 hα' hb'
    hκ hG hω hsum hcal hS hT
  have hseries : observableFullSeries B hk r (roundedCombination kind alpha' b') (seqGap a) =
      ∑ p : Fin k × I, (t p : ℝ) * residueSeries a B hk r kind alpha p := by
    rw [← hobs]
    exact CoreIntegerGapLinearAlgebra.observableFullSeries_integerCombination hB hk r _ hgap hg
      t (basisObservable kind alpha) (fun _ => 2) (fun _ => by norm_num)
      (basis_linear kind alpha hα)
  have hone := hW 1 (by norm_num)
  apply hone.congr'
  exact Eventually.of_forall fun N => by
    apply congrArg (fun z : ℂ => z / (N : ℂ))
    apply sum_congr rfl
    intro n hn
    apply congrArg e
    rw [hseries]
    simp only [Int.cast_one, one_mul, Finset.mul_sum]
    apply sum_congr rfl
    intro q hq
    ring

section Consequences
variable {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (hinj : Function.Injective alpha) {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G)

include ha hB hk r kind alpha hα hinj hκ hG hω hsum hcal hS hT

theorem residue_rationalCombination_normal (q : Fin k × I → ℚ) (hq : ∃ p, q p ≠ 0) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (∑ p, (q p : ℝ) * residueSeries a B hk r kind alpha p) := by
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  exact CoreWeylNormality.isNormal_of_weyl hclock (weylCriterion_linearCombination hclock
    (residue_jointWeyl ha hB hk r kind alpha hα hinj hκ hG hω hsum hcal hS hT) hq)

theorem residue_one_linearIndependent :
    LinearIndependent ℚ (fun p : Option (Fin k × I) => match p with
      | none => (1 : ℝ)
      | some p => residueSeries a B hk r kind alpha p) := by
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  convert (linearIndependent_one_jointWeyl (I := Fin k × I)
    (θ := residueSeries a B hk r kind alpha) hclock
    (residue_jointWeyl ha hB hk r kind alpha hα hinj hκ hG hω hsum hcal hS hT)) using 1 <;>
    first | (funext p; cases p <;> rfl) | rfl

theorem residue_empirical_tendsto :
    Tendsto (CoreJointEquidistribution.empirical (fun _ : Fin k × I => B ^ k)
      (residueSeries a B hk r kind alpha)) atTop
      (𝓝 (CoreJointEquidistribution.torusVolume (Fin k × I))) :=
  CoreJointEquidistribution.empirical_tendsto_of_jointWeyl
    (residue_jointWeyl ha hB hk r kind alpha hα hinj hκ hG hω hsum hcal hS hT)

end Consequences

/-- The same actual finite family for arbitrary real-cutoff probability
laws. Calibration and complex S are transferred by exact expectation. -/
theorem residue_jointWeyl_realCutoff
    {I : Type*} [Fintype I] [DecidableEq I] {a : ℕ → ℕ} (ha : StrictMono a)
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (hα : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (hinj : Function.Injective alpha) {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) (μ : ℕ → ProbabilityMeasure ℝ)
    (hcal : CoreGeneralRealCutoff.Calibration μ G) (hS : CoreGeneralRealCutoff.PatternS a κ G μ)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    JointWeyl (fun _ : Fin k × I => B ^ k) (residueSeries a B hk r kind alpha) :=
  residue_jointWeyl ha hB hk r kind alpha hα hinj hκ hG
    (fun X y => CoreCalibratedRealCutoff.real_weights_nonneg (μ X) y)
    (fun X => CoreCalibratedRealCutoff.real_weights_sum (μ X))
    (CoreCalibratedRealCutoff.uniformCalibration_of_ae μ G hcal)
    (CoreGeneralRealCutoff.patternS_nat hG hcal hS) hT

end
end PrimeGapNormality.Prime.CoreGeneralRoundedFamily
