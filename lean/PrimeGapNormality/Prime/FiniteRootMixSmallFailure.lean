import PrimeGapNormality.Prime.FiniteRootMixSmallMomentBound
import PrimeGapNormality.Prime.ResidueHoeffdingPi

/-!
# Failure mass for the small finite root mix: the lower-count reduction

The small window has expected final count near `(6 / 5) L`, not near
`4 L`.  Thus the older `[3L,5L]` fibre wrapper is not applicable.  This
file proves the Chebyshev estimate at the correct scale: on a fibre with
mean in `[11L/10,5L]`, the probability of fewer than `L` points is at most
`500/L`.

It then averages this estimate first over the early residue choices and
then over `t` with the normalized `mixWeightV` weights.  The resulting
finite bound has exactly one concrete remainder: the weighted mass of
presieve fibres whose conditional mean is below `11L/10`.  Proving that
remainder tends to zero is the global-presieve lower-count step.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-- Early residue choices whose conditional final mean is below
`11L/10`.  The candidate interval is `Icc 1 S`, so the root `0` is not
counted. -/
def finiteRootMixSmallLowerFibreSet (S y L : ℕ) :
    Finset (ResidueChoice S) :=
  (univ : Finset (ResidueChoice S)).filter fun σ =>
    ((presieveSurvivors S σ).card : ℝ) * lateRetention S y <
      (11 / 10 : ℝ) * (L : ℝ)

/-- Uniform residue-choice mass of the concrete lower-mean fibres. -/
def finiteRootMixSmallLowerFibreMass (S y L : ℕ) : ℝ :=
  ((finiteRootMixSmallLowerFibreSet S y L).card : ℝ) /
    (Fintype.card (ResidueChoice S) : ℝ)

/-- The normalized `mixWeightV` average of the concrete lower-mean fibre
mass.  Division by `mixZ` is the same normalization as in
`finiteRootMix`. -/
def finiteRootMixSmallLowerException (κ : ℝ) (X : ℕ) : ℝ :=
  (∑ t ∈ mixScale X, mixWeightV t *
      finiteRootMixSmallLowerFibreMass (ahlSmall_window κ X)
        (sieveCutoff (t : ℝ)) (profileL κ X)) /
    mixZ X

theorem finiteRootMixSmallLowerFibreMass_nonneg (S y L : ℕ) :
    0 ≤ finiteRootMixSmallLowerFibreMass S y L :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem finiteRootMixSmallLowerException_nonneg (κ : ℝ) (X : ℕ) :
    0 ≤ finiteRootMixSmallLowerException κ X := by
  unfold finiteRootMixSmallLowerException
  exact div_nonneg
    (sum_nonneg fun t _ => mul_nonneg (mixWeightV_nonneg t)
      (finiteRootMixSmallLowerFibreMass_nonneg _ _ _))
    (mixZ_nonneg X)

/-! ### Conditional lower tail at the `(6/5)L` scale -/

/-- A late fibre whose mean is between `11L/10` and `5L` has failure
mass at most `500/L`.  This is Chebyshev with gap `L/10` and
`Var N ≤ E N`; unlike the old mean-band wrapper it is compatible with a
mean asymptotic to `(6/5)L`. -/
theorem lateRootLaw_failureMass_le_five_hundred_div_of_mean_bounds
    (S y : ℕ) {T : ℕ} {A : Finset ℕ} {L : ℕ}
    (hA : A ⊆ Icc 1 T) (hT : T ≤ S) (hSy : S ≤ y) (hL : 0 < L)
    (hlo : (11 / 10 : ℝ) * L ≤
      (A.card : ℝ) * lateRetention S y)
    (hhi : (A.card : ℝ) * lateRetention S y ≤ (5 : ℝ) * L) :
    Stopped.failureMass A (lateRootLaw S y A) L ≤
      (500 : ℝ) / (L : ℝ) := by
  let μ := lateRootLaw S y A
  let m := (A.card : ℝ) * lateRetention S y
  have hμ := lateRootLaw_cardinalitySymmetric S y hA hT hSy
  have hMom := exactCountMoments_lateRootLaw S y hA hT hSy
  have hsum1 : ∑ E ∈ A.powerset, μ E = 1 := hμ.2.1
  have hnonneg : ∀ E ∈ A.powerset, 0 ≤ μ E := hμ.1
  have hEN : ∑ E ∈ A.powerset, (E.card : ℝ) * μ E = m := hMom.1
  have hVar :
      (∑ E ∈ A.powerset, (E.card : ℝ) ^ 2 * μ E) - m ^ 2 ≤ m :=
    hMom.2.1
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hgapPos : (0 : ℝ) < (L : ℝ) / 10 := div_pos hLpos (by norm_num)
  have hdev : ∀ E ∈ A.powerset.filter (fun E => E.card < L),
      (L : ℝ) / 10 ≤ |(E.card : ℝ) - m| := by
    intro E hE
    have hcard : E.card < L := (mem_filter.mp hE).2
    have hcardR : (E.card : ℝ) < (L : ℝ) := Nat.cast_lt.mpr hcard
    have hEm : (E.card : ℝ) ≤ m := by
      have hLm : (L : ℝ) ≤ m := by
        dsimp [m] at hlo ⊢
        nlinarith
      exact hcardR.le.trans hLm
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hEm)]
    dsimp [m] at hlo ⊢
    nlinarith
  have hexp :
      ∑ E ∈ A.powerset, ((E.card : ℝ) - m) ^ 2 * μ E =
        (∑ E ∈ A.powerset, (E.card : ℝ) ^ 2 * μ E) - m ^ 2 := by
    have hpt : ∀ E ∈ A.powerset,
        ((E.card : ℝ) - m) ^ 2 * μ E =
          (E.card : ℝ) ^ 2 * μ E -
            2 * m * ((E.card : ℝ) * μ E) + m ^ 2 * μ E := by
      intro E _
      ring
    rw [sum_congr (s₁ := A.powerset) (s₂ := A.powerset) rfl hpt,
      sum_add_distrib, sum_sub_distrib]
    have hlin :
        ∑ E ∈ A.powerset, 2 * m * ((E.card : ℝ) * μ E) =
          2 * m * ∑ E ∈ A.powerset, (E.card : ℝ) * μ E := by
      rw [← mul_sum]
    have hsq : ∑ E ∈ A.powerset, m ^ 2 * μ E = m ^ 2 := by
      rw [← mul_sum, hsum1, mul_one]
    rw [hlin, hEN, hsq]
    ring
  have hVar' :
      ∑ E ∈ A.powerset, ((E.card : ℝ) - m) ^ 2 * μ E ≤ m := by
    rw [hexp]
    exact hVar
  have hbad :
      ((L : ℝ) / 10) ^ 2 *
          ∑ E ∈ A.powerset.filter (fun E => E.card < L), μ E ≤
        ∑ E ∈ A.powerset.filter (fun E => E.card < L),
          ((E.card : ℝ) - m) ^ 2 * μ E := by
    calc
      ((L : ℝ) / 10) ^ 2 *
          ∑ E ∈ A.powerset.filter (fun E => E.card < L), μ E =
        ∑ E ∈ A.powerset.filter (fun E => E.card < L),
          ((L : ℝ) / 10) ^ 2 * μ E :=
            Finset.mul_sum _ _ _
      _ ≤ ∑ E ∈ A.powerset.filter (fun E => E.card < L),
          ((E.card : ℝ) - m) ^ 2 * μ E := by
        exact sum_le_sum fun E hE => by
          have hμ0 : 0 ≤ μ E := hnonneg E (mem_filter.mp hE).1
          have hsqle : ((L : ℝ) / 10) ^ 2 ≤
              ((E.card : ℝ) - m) ^ 2 := by
            have habs : |(L : ℝ) / 10| ≤ |(E.card : ℝ) - m| := by
              rw [abs_of_pos hgapPos]
              exact hdev E hE
            exact sq_le_sq.mpr habs
          exact mul_le_mul_of_nonneg_right hsqle hμ0
  have hbadle :
      ∑ E ∈ A.powerset.filter (fun E => E.card < L),
          ((E.card : ℝ) - m) ^ 2 * μ E ≤
        ∑ E ∈ A.powerset, ((E.card : ℝ) - m) ^ 2 * μ E := by
    refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_
    intro E hE _
    exact mul_nonneg (sq_nonneg _) (hnonneg E hE)
  have hprob :
      ∑ E ∈ A.powerset.filter (fun E => E.card < L), μ E ≤
        m / ((L : ℝ) / 10) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hgapPos)).2
    simpa [mul_comm] using hbad.trans (hbadle.trans hVar')
  have hfinal : m / ((L : ℝ) / 10) ^ 2 ≤ (500 : ℝ) / (L : ℝ) := by
    have hstep := div_le_div_of_nonneg_right hhi (sq_nonneg ((L : ℝ) / 10))
    have hcalc :
        ((5 : ℝ) * (L : ℝ)) / ((L : ℝ) / 10) ^ 2 =
          (500 : ℝ) / (L : ℝ) := by
      field_simp [hLpos.ne']
      ring
    exact hstep.trans_eq hcalc
  unfold Stopped.failureMass
  exact hprob.trans hfinal

/-! ### Uniform residue average -/

/-- The actual root law is bounded by the conditional Chebyshev term
plus precisely the uniform mass of fibres below `11L/10`. -/
theorem finiteRootMixSmall_actual_failureMass_le_lowerFibreMass
    (S y L : ℕ) (hSy : S ≤ y) (hL : 0 < L)
    (hupper : ∀ σ : ResidueChoice S,
      ((presieveSurvivors S σ).card : ℝ) * lateRetention S y ≤
        (5 : ℝ) * L) :
    Stopped.failureMass (offsetWindow S) (actualRootLaw y S) L ≤
      (500 : ℝ) / (L : ℝ) +
        finiteRootMixSmallLowerFibreMass S y L := by
  have hdenpos : 0 < (Fintype.card (ResidueChoice S) : ℝ) :=
    Nat.cast_pos.mpr (residueChoice_card_pos S)
  rw [actualRootLaw_failureMass_eq_avg S y S L le_rfl hSy]
  simp_rw [← finiteRootMixSmall_presieve_eq_lateCandidateSet]
  have hfib : ∀ σ : ResidueChoice S,
      Stopped.failureMass (offsetWindow S)
          (lateRootLaw S y (presieveSurvivors S σ)) L =
        Stopped.failureMass (presieveSurvivors S σ)
          (lateRootLaw S y (presieveSurvivors S σ)) L :=
    fun σ => lateRootLaw_failureMass_window_eq_fibre S y S
      (presieveSurvivors_subset_Icc_self S σ) L
  simp_rw [hfib]
  let bad := finiteRootMixSmallLowerFibreSet S y L
  let good := (univ : Finset (ResidueChoice S)) \ bad
  let fail (σ : ResidueChoice S) :=
    Stopped.failureMass (presieveSurvivors S σ)
      (lateRootLaw S y (presieveSurvivors S σ)) L
  have hunion : good ∪ bad = (univ : Finset (ResidueChoice S)) := by
    simp [good, bad]
  have hdisj : Disjoint good bad := Finset.sdiff_disjoint
  have hsum : ∑ σ : ResidueChoice S, fail σ =
      ∑ σ ∈ good, fail σ + ∑ σ ∈ bad, fail σ := by
    rw [← hunion, sum_union hdisj]
  have hgood : ∀ σ ∈ good, fail σ ≤ (500 : ℝ) / (L : ℝ) := by
    intro σ hσ
    have hnotbad : σ ∉ bad := (mem_sdiff.mp hσ).2
    have hlo : (11 / 10 : ℝ) * (L : ℝ) ≤
        ((presieveSurvivors S σ).card : ℝ) * lateRetention S y := by
      simpa [bad, finiteRootMixSmallLowerFibreSet] using hnotbad
    exact lateRootLaw_failureMass_le_five_hundred_div_of_mean_bounds
      S y (presieveSurvivors_subset_Icc_self S σ) le_rfl hSy hL hlo
      (hupper σ)
  have hbad : ∀ σ ∈ bad, fail σ ≤ 1 :=
    fun σ _ => lateRootLaw_failureMass_le_one S y _ L
  have hle : ∑ σ : ResidueChoice S, fail σ ≤
      ∑ _σ ∈ good, (500 : ℝ) / (L : ℝ) +
        ∑ _σ ∈ bad, (1 : ℝ) := by
    rw [hsum]
    exact add_le_add (sum_le_sum hgood) (sum_le_sum hbad)
  have hconst :
      ∑ _σ ∈ good, (500 : ℝ) / (L : ℝ) +
          ∑ _σ ∈ bad, (1 : ℝ) =
        (good.card : ℝ) * ((500 : ℝ) / (L : ℝ)) + (bad.card : ℝ) := by
    rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  have hdiv := div_le_div_of_nonneg_right (hconst ▸ hle) hdenpos.le
  have hgoodle : (good.card : ℝ) /
      (Fintype.card (ResidueChoice S) : ℝ) ≤ 1 := by
    apply (div_le_one hdenpos).2
    exact Nat.cast_le.mpr
      (card_le_card (show good ⊆ univ from fun _ _ => mem_univ _))
  have h500 : 0 ≤ (500 : ℝ) / (L : ℝ) :=
    div_nonneg (by norm_num) (Nat.cast_nonneg _)
  calc
    (∑ σ : ResidueChoice S, fail σ) /
          (Fintype.card (ResidueChoice S) : ℝ)
        ≤ ((good.card : ℝ) * ((500 : ℝ) / (L : ℝ)) +
            (bad.card : ℝ)) /
          (Fintype.card (ResidueChoice S) : ℝ) := hdiv
    _ = ((good.card : ℝ) /
            (Fintype.card (ResidueChoice S) : ℝ)) *
          ((500 : ℝ) / (L : ℝ)) +
        (bad.card : ℝ) /
          (Fintype.card (ResidueChoice S) : ℝ) := by ring
    _ ≤ (500 : ℝ) / (L : ℝ) +
        (bad.card : ℝ) /
          (Fintype.card (ResidueChoice S) : ℝ) := by
      exact add_le_add (mul_le_of_le_one_left h500 hgoodle) le_rfl
    _ = (500 : ℝ) / (L : ℝ) +
        finiteRootMixSmallLowerFibreMass S y L := by
      rfl

/-! ### Normalized `mixWeightV` average -/

theorem finiteRootMix_failureMass_nonneg (X S L : ℕ) :
    0 ≤ Stopped.failureMass (offsetWindow S) (finiteRootMix X S) L := by
  unfold Stopped.failureMass finiteRootMix
  exact sum_nonneg fun U _ =>
    div_nonneg
      (sum_nonneg fun t _ =>
        mul_nonneg (mixWeightV_nonneg t) (actualRootLaw_nonneg _ _ _))
      (mixZ_nonneg X)

/-- Pull `failureMass` through the normalized finite root mix.  This
identity is valid without a positivity hypothesis on `mixZ`; both sides
use the same division. -/
theorem finiteRootMix_failureMass_eq_weighted (X S L : ℕ) :
    Stopped.failureMass (offsetWindow S) (finiteRootMix X S) L =
      (∑ t ∈ mixScale X, mixWeightV t *
          Stopped.failureMass (offsetWindow S)
            (actualRootLaw (sieveCutoff (t : ℝ)) S) L) /
        mixZ X := by
  unfold Stopped.failureMass finiteRootMix
  rw [← sum_div]
  refine congrArg (fun z => z / mixZ X) ?_
  rw [sum_comm]
  exact sum_congr rfl fun t _ => (mul_sum _ _ _).symm

private theorem eventually_ahlSmall_window_le_mix_cutoff {κ : ℝ}
    (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X,
      ahlSmall_window κ X ≤ sieveCutoff (t : ℝ) := by
  filter_upwards [eventually_profileS_le_sieveCutoff hκ,
    crtNestVR_eventually_exp_sixteen] with X hprofile hX
  intro t ht
  have htI : t ∈ Ioc X (2 * X) := by simpa [mixScale] using ht
  have hXt : (X : ℝ) < (t : ℝ) := Nat.cast_lt.mpr (mem_Ioc.mp htI).1
  have hX1 : (1 : ℝ) < X := by
    exact lt_of_lt_of_le
      (lt_trans (by norm_num : (1 : ℝ) < 2)
        (lt_trans Real.exp_one_gt_two
          (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16)))) hX
  have hprofileNat : profileS κ X ≤ sieveCutoff (X : ℝ) :=
    Nat.cast_le.mp hprofile
  exact (ahlSmall_window_le_profileS κ X).trans
    (hprofileNat.trans (crtNestVR_sieveCutoff_mono hX1 hXt))

private theorem mixZ_pos_of_one_le {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos
  · intro t _
    exact eulerProdNat_pos (sieveCutoff (t : ℝ))
  · exact ⟨2 * X, by
      simp only [mixScale, mem_Ioc]
      omega⟩

/-- Concrete finite reduction for the small model.  The deterministic
Selberg cap supplies the upper endpoint `5L`; all failure beyond
`500/L` is charged to the explicit weighted lower-count exception. -/
theorem eventually_finiteRootMix_small_failureMass_le_lowerException
    {κ : ℝ} (hκ : 0 < κ)
    (hEuler : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) < eulerProdNat n * Real.log n) :
    ∀ᶠ X : ℕ in atTop,
      Stopped.failureMass (ahlSmall_omega κ X)
          (finiteRootMix X (ahlSmall_window κ X)) (profileL κ X) ≤
        (500 : ℝ) / (profileL κ X : ℝ) +
          finiteRootMixSmallLowerException κ X := by
  filter_upwards [
    eventually_small_presieve_mean_le_five_of_euler_tail hκ hEuler,
    eventually_ahlSmall_window_le_mix_cutoff hκ,
    eventually_one_le_profileL hκ,
    eventually_ge_atTop 1] with X hupper hcut hL hX
  let S := ahlSmall_window κ X
  let L := profileL κ X
  have hZ : 0 < mixZ X := mixZ_pos_of_one_le hX
  rw [show ahlSmall_omega κ X = offsetWindow S from rfl,
    finiteRootMix_failureMass_eq_weighted]
  have hterm : ∀ t ∈ mixScale X,
      Stopped.failureMass (offsetWindow S)
          (actualRootLaw (sieveCutoff (t : ℝ)) S) L ≤
        (500 : ℝ) / (L : ℝ) +
          finiteRootMixSmallLowerFibreMass S
            (sieveCutoff (t : ℝ)) L := by
    intro t ht
    exact finiteRootMixSmall_actual_failureMass_le_lowerFibreMass
      S (sieveCutoff (t : ℝ)) L (hcut t ht) hL
      (fun σ => hupper t ht σ)
  have hsum :
      ∑ t ∈ mixScale X, mixWeightV t *
          Stopped.failureMass (offsetWindow S)
            (actualRootLaw (sieveCutoff (t : ℝ)) S) L ≤
        ∑ t ∈ mixScale X, mixWeightV t *
          ((500 : ℝ) / (L : ℝ) +
            finiteRootMixSmallLowerFibreMass S
              (sieveCutoff (t : ℝ)) L) := by
    exact sum_le_sum fun t ht =>
      mul_le_mul_of_nonneg_left (hterm t ht) (mixWeightV_nonneg t)
  apply (div_le_iff₀ hZ).2
  calc
    ∑ t ∈ mixScale X, mixWeightV t *
          Stopped.failureMass (offsetWindow S)
            (actualRootLaw (sieveCutoff (t : ℝ)) S) L
        ≤ ∑ t ∈ mixScale X, mixWeightV t *
          ((500 : ℝ) / (L : ℝ) +
            finiteRootMixSmallLowerFibreMass S
              (sieveCutoff (t : ℝ)) L) := hsum
    _ = ((500 : ℝ) / (L : ℝ) +
          finiteRootMixSmallLowerException κ X) * mixZ X := by
      unfold finiteRootMixSmallLowerException
      dsimp [S, L]
      simp_rw [mul_add]
      rw [sum_add_distrib]
      have hconstWeight :
          (∑ t ∈ mixScale X, mixWeightV t *
              ((500 : ℝ) / (profileL κ X : ℝ))) =
            mixZ X * ((500 : ℝ) / (profileL κ X : ℝ)) := by
        rw [← Finset.sum_mul]
        rfl
      rw [hconstWeight]
      change mixZ X * ((500 : ℝ) / (profileL κ X : ℝ)) +
          (∑ t ∈ mixScale X, mixWeightV t *
            finiteRootMixSmallLowerFibreMass (ahlSmall_window κ X)
              (sieveCutoff (t : ℝ)) (profileL κ X)) =
        ((500 : ℝ) / (profileL κ X : ℝ) +
          (∑ t ∈ mixScale X, mixWeightV t *
            finiteRootMixSmallLowerFibreMass (ahlSmall_window κ X)
              (sieveCutoff (t : ℝ)) (profileL κ X)) / mixZ X) * mixZ X
      rw [add_mul, div_mul_cancel₀ _ hZ.ne']
      ring

/-- The explicit conditional-variance term in the finite reduction
vanishes because `profileL κ X → ∞`. -/
theorem tendsto_five_hundred_div_profileL {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ => (500 : ℝ) / (profileL κ X : ℝ))
      atTop (nhds 0) := by
  have hfun :
      (fun X : ℕ => (500 : ℝ) / (profileL κ X : ℝ)) =
        fun X => (500 : ℝ) * (profileL κ X : ℝ)⁻¹ := by
    funext X
    rw [div_eq_mul_inv]
  rw [hfun]
  exact mul_zero (500 : ℝ) ▸
    (tendsto_const_nhds (x := (500 : ℝ))).mul (tendsto_inv_profileL hκ)

end

end PrimeGapNormality.Prime
