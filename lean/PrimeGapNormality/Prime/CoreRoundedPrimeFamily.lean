import PrimeGapNormality.Prime.CoreRoundedPrimeNormality
import PrimeGapNormality.Prime.CoreIntegerGapLinearAlgebra
import PrimeGapNormality.Prime.JointWeyl

/-!
# Literal finite families of rounded prime-gap powers

For a finite injective list of exponents in `(0,1]`, this file defines the
literal residue-labelled floor (or, separately, ceiling) component series.
Every nonzero integer character has a nonempty finite active support.  A
maximal active exponent supplies the nonzero leading column required by the
scalar rounded theorem; inactive coordinates are harmlessly assigned that
same exponent because their coefficients vanish.  Thus no linear
independence of model polynomials is assumed.
-/

namespace PrimeGapNormality.Prime.CoreRoundedPrimeFamily

open Finset Filter CoreCyclic
open CoreRoundedPowerScaling CoreIntegerGapObservable
open CoreRoundedPrimeNormality CoreSequenceSubexponentialGrowth
open scoped Topology Classical BigOperators

noncomputable section

private theorem family_clock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    2 ≤ B ^ k := by
  have heq : k = k - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [heq, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

private theorem family_primeGap_one_le (n : ℕ) : 1 ≤ primeGap n := by
  unfold primeGap
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.sub_ne_zero_of_lt (nthPrime_strictMono (Nat.lt_succ_self n)))

private theorem family_primeGap_subexponential :
    HasSubexponentialGrowth (fun n ↦ (primeGap n : ℝ)) := by
  have hcount : WindowCountToInfinity nthPrime := by
    have hreal := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      CorePrimeDensity.tendsto_windowNX_atTop
    simpa only [WindowCountToInfinity, seqWindow_nthPrime_card,
      Function.comp_def] using hreal
  simpa only [seqGap_nthPrime] using
    (sequenceGap_hasSubexponentialGrowth nthPrime_strictMono hcount)

/-- The integer observable selecting one relative residue label and one
rounded exponent. -/
def basisObservable {I : Type*} {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (p : Fin k × I)
    (s : Fin k) (q : ℕ) : ℤ :=
  if s = p.1 then roundedPower kind (alpha p.2) q else 0

/-- Literal residue-labelled rounded gap-power series.  Lean labels are
zero-based, while the denominator is `B^(n+1)`, matching the paper's
one-based residue convention after the usual shift. -/
def roundedResidueSeries {I : Type*} {k : ℕ}
    (B : ℕ) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (p : Fin k × I) : ℝ :=
  observableFullSeries B hk r (basisObservable kind alpha p) primeGap

private theorem basisObservable_linear_bound
    {I : Type*} {k : ℕ} (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1) (p : Fin k × I)
    (s : Fin k) (q : ℕ) (hq : 1 ≤ q) :
    |(basisObservable kind alpha p s q : ℝ)| ≤ 2 * (q : ℝ) := by
  by_cases hs : s = p.1
  · simp only [basisObservable, hs, if_true]
    have hqR : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
    have hp := abs_roundedPower_le_rpow_add_one kind q (alpha := alpha p.2)
    have hpow : (q : ℝ) ^ alpha p.2 ≤ (q : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hqR (halpha p.2).2
    exact hp.trans (by linarith)
  · simp only [basisObservable, hs, if_false, Int.cast_zero, abs_zero]
    positivity

private theorem basisSeries_summable
    {I : Type*} {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1) (p : Fin k × I) :
    Summable (fun n : ℕ ↦
      (CoreIntegerGapObservable.observableValue hk r
        (basisObservable kind alpha p) primeGap 0 n : ℝ) /
          (B : ℝ) ^ (n + 1)) := by
  apply observableSeries_summable hB hk r (basisObservable kind alpha p)
    family_primeGap_one_le family_primeGap_subexponential (by norm_num : (0 : ℝ) ≤ 2)
  intro s q hq
  exact basisObservable_linear_bound kind alpha halpha p s q hq

/-- Exact finite integer-combination identity for the convergent literal
series. -/
theorem roundedCombination_fullSeries_eq
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (t : Fin k × I → ℤ) :
    observableFullSeries B hk r
        (roundedCombination kind (fun p : Fin k × I ↦ alpha p.2)
          (fun s p ↦ if s = p.1 then t p else 0)) primeGap =
      ∑ p : Fin k × I, (t p : ℝ) *
        roundedResidueSeries B hk r kind alpha p := by
  have hobservable :
      CoreIntegerGapLinearAlgebra.integerCombination t
          (basisObservable kind alpha) =
        roundedCombination kind (fun p : Fin k × I ↦ alpha p.2)
          (fun s p ↦ if s = p.1 then t p else 0) := by
    funext s q
    unfold CoreIntegerGapLinearAlgebra.integerCombination basisObservable
      roundedCombination
    apply sum_congr rfl
    intro p hp
    by_cases hs : s = p.1 <;> simp [hs]
  rw [← hobservable]
  simpa only [roundedResidueSeries] using
    (CoreIntegerGapLinearAlgebra.observableFullSeries_integerCombination
      hB hk r primeGap family_primeGap_one_le family_primeGap_subexponential
      t (basisObservable kind alpha) (fun _ ↦ (2 : ℝ))
      (fun _ ↦ by norm_num)
      (basisObservable_linear_bound kind alpha halpha))

private theorem alteredCombination_fullSeries_eq
    {I : Type*} [Fintype I] {B k : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ) (alpha' : Fin k × I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halpha' : ∀ p, 0 < alpha' p ∧ alpha' p ≤ 1)
    (t : Fin k × I → ℤ) (hactive : ∀ p, t p ≠ 0 → alpha' p = alpha p.2) :
    observableFullSeries B hk r
        (roundedCombination kind alpha'
          (fun s p ↦ if s = p.1 then t p else 0)) primeGap =
      ∑ p : Fin k × I, (t p : ℝ) *
        observableFullSeries B hk r (basisObservable kind alpha p) primeGap := by
  have hobservable :
      CoreIntegerGapLinearAlgebra.integerCombination t
          (basisObservable kind alpha) =
        roundedCombination kind alpha'
          (fun s p ↦ if s = p.1 then t p else 0) := by
    funext s q
    unfold CoreIntegerGapLinearAlgebra.integerCombination basisObservable
      roundedCombination
    apply sum_congr rfl
    intro p hp
    by_cases htp : t p = 0
    · simp [htp]
    · rw [hactive p htp]
      by_cases hs : s = p.1 <;> simp [hs]
  rw [← hobservable]
  exact CoreIntegerGapLinearAlgebra.observableFullSeries_integerCombination
    hB hk r primeGap family_primeGap_one_le family_primeGap_subexponential
    t (basisObservable kind alpha) (fun _ ↦ (2 : ℝ))
    (fun _ ↦ by norm_num)
    (basisObservable_linear_bound kind alpha halpha)

/-- Every nonzero integer character of a finite injective exponent family
is Weyl at the common clock. -/
theorem roundedResidue_jointWeyl_of_D
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ d0 c : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    JointWeyl (fun _ : Fin k × I ↦ B ^ k)
      (roundedResidueSeries B hk r kind alpha) := by
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
  have ha : 0 < a := by dsimp only [a]; exact (halpha p.2).1
  have ha1 : a ≤ 1 := by dsimp only [a]; exact (halpha p.2).2
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
  have hb : leadingColumn alpha' b' a ≠ 0 := by
    intro hz
    have hz' := congrFun hz p.1
    have heval : leadingColumn alpha' b' a p.1 = (t p : ℝ) := by
      unfold leadingColumn
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
    exact htp (Int.cast_eq_zero.mp hz')
  have hW := roundedCombination_weyl_clock_of_D hB hk r kind alpha' b'
    ha ha1 halpha' hb hκ hd0 hc hD
  have hseries :
      observableFullSeries B hk r (roundedCombination kind alpha' b') primeGap =
        ∑ q : Fin k × I, (t q : ℝ) * roundedResidueSeries B hk r kind alpha q := by
    exact alteredCombination_fullSeries_eq hB hk r kind
      alpha alpha' halpha halpha'Linear t (by
        intro q htq
        simp only [alpha', htq, if_false])
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

/-- Every nontrivial rational combination of the literal finite family is
normal to the common clock. -/
theorem roundedResidue_rationalCombination_weyl_of_D
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ d0 c : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c)
    (q : Fin k × I → ℚ) (hq : ∃ i, q i ≠ 0) :
    weylCriterion (B ^ k)
      (∑ i, (q i : ℝ) * roundedResidueSeries B hk r kind alpha i) :=
  weylCriterion_linearCombination (family_clock_ge hB hk)
    (roundedResidue_jointWeyl_of_D hB hk r kind alpha halpha halphaInj
      hκ hd0 hc hD) hq

theorem roundedResidue_rationalCombination_isNormal_of_D
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ d0 c : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c)
    (q : Fin k × I → ℚ) (hq : ∃ i, q i ≠ 0) :
    PrimeGapNormality.BFree.IsNormal (B ^ k)
      (∑ i, (q i : ℝ) * roundedResidueSeries B hk r kind alpha i) :=
  CoreWeylNormality.isNormal_of_weyl (family_clock_ge hB hk)
    (roundedResidue_rationalCombination_weyl_of_D hB hk r kind alpha
      halpha halphaInj hκ hd0 hc hD q hq)

/-- Joint common-clock Weyl implies the advertised independence of `1`
and every component in the fixed finite family. -/
theorem roundedResidue_one_linearIndependent_of_D
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ d0 c : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    LinearIndependent ℚ (fun i : Option (Fin k × I) => match i with
      | none => (1 : ℝ)
      | some i => roundedResidueSeries B hk r kind alpha i) := by
  convert linearIndependent_one_jointWeyl
    (family_clock_ge hB hk)
    (roundedResidue_jointWeyl_of_D hB hk r kind alpha halpha halphaInj
      hκ hd0 hc hD) using 1
  funext i
  cases i <;> rfl

/-- Kuperberg supplies the actual D input for every fixed finite rounded
family without changing the exponent or residue index set. -/
theorem roundedResidue_jointWeyl_of_kuperberg
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hK : KuperbergConj13) :
    JointWeyl (fun _ : Fin k × I ↦ B ^ k)
      (roundedResidueSeries B hk r kind alpha) := by
  have hκpos : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  exact roundedResidue_jointWeyl_of_D hB hk r kind alpha halpha halphaInj
    hκ (by norm_num) (by norm_num) (coreLinearD_of_kuperberg hK hκpos)

theorem roundedResidue_one_linearIndependent_of_kuperberg
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hK : KuperbergConj13) :
    LinearIndependent ℚ (fun i : Option (Fin k × I) => match i with
      | none => (1 : ℝ)
      | some i => roundedResidueSeries B hk r kind alpha i) := by
  convert linearIndependent_one_jointWeyl (family_clock_ge hB hk)
    (roundedResidue_jointWeyl_of_kuperberg hB hk r kind alpha halpha
      halphaInj hκ hK) using 1
  funext i
  cases i <;> rfl

/-- The small-window AHL supplier gives the same family theorem. -/
theorem roundedResidue_jointWeyl_of_AHL
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (kind : RoundKind) (alpha : I → ℝ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (halphaInj : Function.Injective alpha)
    {κ : ℝ} (hκpos : 0 < κ) (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hAHL : ahlSmall_AHL κ 20) :
    JointWeyl (fun _ : Fin k × I ↦ B ^ k)
      (roundedResidueSeries B hk r kind alpha) :=
  roundedResidue_jointWeyl_of_D hB hk r kind alpha halpha halphaInj
    hκ (by norm_num) (by norm_num)
      (CoreAHLToD.coreLinearD_of_ahlSmall_AHL hκpos hAHL)

end

end PrimeGapNormality.Prime.CoreRoundedPrimeFamily
