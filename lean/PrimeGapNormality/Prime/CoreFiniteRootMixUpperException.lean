import PrimeGapNormality.Prime.FiniteRootMixSmallLowerException
import PrimeGapNormality.Prime.CrtPhysicalRetentionToZeroOfLogRatio
import PrimeGapNormality.Prime.CrtLogProfileSDivLogX
import PrimeGapNormality.Prime.CorePresieveLaw

/-!
# The actual high-count exception in the small finite root mixture

On a fixed exposed presieve fibre, the exact late-root second moment gives
`Var N ≤ Mϑ`.  Chebyshev at the self-normalized threshold `N > 2Mϑ`
therefore costs at most `(Mϑ)⁻¹`.  Fibres with `Mϑ < 11L/10` are charged to
the already proved lower-mean exception; no global upper-presieve
concentration is introduced.

The same concrete scales also force `ϑ ≤ 1/4` uniformly on the finite mix
support.  Hence the good-count condition `N ≤ 2Mϑ` implies `N ≤ M/2`, as
required by the positive insertion prefactor.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-- Conditional late-root mass above twice its exact fibre mean. -/
noncomputable def coreFiniteRootMixUpperFibreMass
    (S y : ℕ) (σ : ResidueChoice S) : ℝ :=
  let A := presieveSurvivors S σ
  let m := (A.card : ℝ) * lateRetention S y
  ∑ E ∈ A.powerset.filter (fun E => 2 * m < (E.card : ℝ)),
    lateRootLaw S y A E

/-- Uniform early-root average of the self-normalized high-count mass. -/
noncomputable def coreFiniteRootMixUpperRootMass (S y : ℕ) : ℝ :=
  (∑ σ : ResidueChoice S, coreFiniteRootMixUpperFibreMass S y σ) /
    (Fintype.card (ResidueChoice S) : ℝ)

/-- The same normalized `mixWeightV` average used by `finiteRootMix`. -/
noncomputable def coreFiniteRootMixUpperException (κ : ℝ) (X : ℕ) : ℝ :=
  (∑ t ∈ mixScale X, mixWeightV t *
      coreFiniteRootMixUpperRootMass (ahlSmall_window κ X)
        (sieveCutoff (t : ℝ))) /
    mixZ X

theorem coreFiniteRootMixUpperFibreMass_nonneg
    (S y : ℕ) (σ : ResidueChoice S) :
    0 ≤ coreFiniteRootMixUpperFibreMass S y σ := by
  unfold coreFiniteRootMixUpperFibreMass
  exact sum_nonneg fun E _hE => lateProductMass_nonneg S y _ E

theorem coreFiniteRootMixUpperRootMass_nonneg (S y : ℕ) :
    0 ≤ coreFiniteRootMixUpperRootMass S y :=
  div_nonneg (sum_nonneg fun σ _ =>
    coreFiniteRootMixUpperFibreMass_nonneg S y σ) (Nat.cast_nonneg _)

theorem coreFiniteRootMixUpperException_nonneg (κ : ℝ) (X : ℕ) :
    0 ≤ coreFiniteRootMixUpperException κ X := by
  unfold coreFiniteRootMixUpperException
  exact div_nonneg
    (sum_nonneg fun t _ => mul_nonneg (mixWeightV_nonneg t)
      (coreFiniteRootMixUpperRootMass_nonneg _ _))
    (mixZ_nonneg X)

/-! ### Conditional Chebyshev at `2Mϑ` -/

/-- A late fibre with mean `m=Mϑ ≥ 1` has mass at most `m⁻¹` above
`2m`.  The mean and variance are the actual exact late-root moments. -/
theorem coreFiniteRootMixUpperFibreMass_le_inv_mean
    (S y : ℕ) (σ : ResidueChoice S) (hSy : S ≤ y)
    (hm : 1 ≤ ((presieveSurvivors S σ).card : ℝ) * lateRetention S y) :
    coreFiniteRootMixUpperFibreMass S y σ ≤
      (((presieveSurvivors S σ).card : ℝ) * lateRetention S y)⁻¹ := by
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  let m := (A.card : ℝ) * lateRetention S y
  have hμ : CardinalitySymmetricMass A μ := by
    simpa [A, μ] using
      corePresieveLaw_cardinalitySymmetric S y σ hSy
  have hMom : ExactCountMoments S y A μ := by
    simpa [A, μ] using corePresieveLaw_exactCountMoments S y σ hSy
  have hm1 : (1 : ℝ) ≤ m := by simpa [A, m] using hm
  have hmpos : 0 < m := zero_lt_one.trans_le hm1
  have hsum1 : ∑ E ∈ A.powerset, μ E = 1 := hμ.2.1
  have hnonneg : ∀ E ∈ A.powerset, 0 ≤ μ E := hμ.1
  have hEN : ∑ E ∈ A.powerset, (E.card : ℝ) * μ E = m := hMom.1
  have hVar :
      (∑ E ∈ A.powerset, (E.card : ℝ) ^ 2 * μ E) - m ^ 2 ≤ m :=
    hMom.2.1
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
  let bad := A.powerset.filter (fun E => 2 * m < (E.card : ℝ))
  have hdev : ∀ E ∈ bad, m ≤ |(E.card : ℝ) - m| := by
    intro E hE
    have hhigh : 2 * m < (E.card : ℝ) := (mem_filter.mp hE).2
    have hnon : 0 ≤ (E.card : ℝ) - m := by linarith
    rw [abs_of_nonneg hnon]
    linarith
  have hbad :
      m ^ 2 * ∑ E ∈ bad, μ E ≤
        ∑ E ∈ bad, ((E.card : ℝ) - m) ^ 2 * μ E := by
    rw [Finset.mul_sum]
    exact sum_le_sum fun E hE => by
      have hμ0 : 0 ≤ μ E := hnonneg E (mem_filter.mp hE).1
      have habs : |m| ≤ |(E.card : ℝ) - m| := by
        rw [abs_of_pos hmpos]
        exact hdev E hE
      exact mul_le_mul_of_nonneg_right (sq_le_sq.mpr habs) hμ0
  have hbadle :
      ∑ E ∈ bad, ((E.card : ℝ) - m) ^ 2 * μ E ≤
        ∑ E ∈ A.powerset, ((E.card : ℝ) - m) ^ 2 * μ E := by
    refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_
    intro E hE _
    exact mul_nonneg (sq_nonneg _) (hnonneg E hE)
  have hprob : ∑ E ∈ bad, μ E ≤ m / m ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hmpos)).2
    simpa [mul_comm] using hbad.trans (hbadle.trans hVar')
  unfold coreFiniteRootMixUpperFibreMass
  change (∑ E ∈ bad, μ E) ≤ m⁻¹
  calc
    (∑ E ∈ bad, μ E) ≤ m / m ^ 2 := hprob
    _ = m⁻¹ := by field_simp [hmpos.ne']

theorem coreFiniteRootMixUpperFibreMass_le_one
    (S y : ℕ) (σ : ResidueChoice S) (hSy : S ≤ y) :
    coreFiniteRootMixUpperFibreMass S y σ ≤ 1 := by
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  have hμ : CardinalitySymmetricMass A μ := by
    simpa [A, μ] using
      corePresieveLaw_cardinalitySymmetric S y σ hSy
  unfold coreFiniteRootMixUpperFibreMass
  change (∑ E ∈ A.powerset.filter
      (fun E => 2 * ((A.card : ℝ) * lateRetention S y) < (E.card : ℝ)), μ E) ≤ 1
  calc
    _ ≤ ∑ E ∈ A.powerset, μ E := by
      refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_
      intro E hE _
      exact hμ.1 E hE
    _ = 1 := hμ.2.1

/-! ### Early-root and finite-mixture aggregation -/

/-- Except for the already named low-mean fibres, the self-normalized high
tail costs at most `1/L`. -/
theorem coreFiniteRootMixUpperRootMass_le
    (S y L : ℕ) (hSy : S ≤ y) (hL : 0 < L) :
    coreFiniteRootMixUpperRootMass S y ≤
      ((L : ℝ)⁻¹) + finiteRootMixSmallLowerFibreMass S y L := by
  have hdenpos : 0 < (Fintype.card (ResidueChoice S) : ℝ) :=
    Nat.cast_pos.mpr (residueChoice_card_pos S)
  let bad := finiteRootMixSmallLowerFibreSet S y L
  let good := (univ : Finset (ResidueChoice S)) \ bad
  let upper (σ : ResidueChoice S) := coreFiniteRootMixUpperFibreMass S y σ
  have hunion : good ∪ bad = (univ : Finset (ResidueChoice S)) := by
    simp [good, bad]
  have hdisj : Disjoint good bad := Finset.sdiff_disjoint
  have hsum : ∑ σ : ResidueChoice S, upper σ =
      ∑ σ ∈ good, upper σ + ∑ σ ∈ bad, upper σ := by
    rw [← hunion, sum_union hdisj]
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hgood : ∀ σ ∈ good, upper σ ≤ (L : ℝ)⁻¹ := by
    intro σ hσ
    have hnotbad : σ ∉ bad := (mem_sdiff.mp hσ).2
    have hlo : (11 / 10 : ℝ) * (L : ℝ) ≤
        ((presieveSurvivors S σ).card : ℝ) * lateRetention S y := by
      simpa [bad, finiteRootMixSmallLowerFibreSet] using hnotbad
    have hm1 : (1 : ℝ) ≤
        ((presieveSurvivors S σ).card : ℝ) * lateRetention S y := by
      have hL1 : (1 : ℝ) ≤ L := Nat.one_le_cast.mpr hL
      nlinarith
    have hcond := coreFiniteRootMixUpperFibreMass_le_inv_mean S y σ hSy hm1
    have hLm : (L : ℝ) ≤
        ((presieveSurvivors S σ).card : ℝ) * lateRetention S y := by
      nlinarith
    exact hcond.trans ((inv_le_inv₀ (zero_lt_one.trans_le hm1) hLR).mpr hLm)
  have hbad : ∀ σ ∈ bad, upper σ ≤ 1 :=
    fun σ _ => coreFiniteRootMixUpperFibreMass_le_one S y σ hSy
  have hle : ∑ σ : ResidueChoice S, upper σ ≤
      ∑ _σ ∈ good, (L : ℝ)⁻¹ + ∑ _σ ∈ bad, (1 : ℝ) := by
    rw [hsum]
    exact add_le_add (sum_le_sum hgood) (sum_le_sum hbad)
  have hconst :
      ∑ _σ ∈ good, (L : ℝ)⁻¹ + ∑ _σ ∈ bad, (1 : ℝ) =
        (good.card : ℝ) * (L : ℝ)⁻¹ + (bad.card : ℝ) := by
    rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  have hdiv := div_le_div_of_nonneg_right (hconst ▸ hle) hdenpos.le
  have hgoodle : (good.card : ℝ) /
      (Fintype.card (ResidueChoice S) : ℝ) ≤ 1 := by
    apply (div_le_one hdenpos).2
    exact Nat.cast_le.mpr (card_le_card (show good ⊆ univ from fun _ _ => mem_univ _))
  have hinv0 : 0 ≤ (L : ℝ)⁻¹ := inv_nonneg.mpr hLR.le
  unfold coreFiniteRootMixUpperRootMass
  change (∑ σ : ResidueChoice S, upper σ) /
      (Fintype.card (ResidueChoice S) : ℝ) ≤ _
  calc
    _ ≤ ((good.card : ℝ) * (L : ℝ)⁻¹ + (bad.card : ℝ)) /
        (Fintype.card (ResidueChoice S) : ℝ) := hdiv
    _ = ((good.card : ℝ) /
          (Fintype.card (ResidueChoice S) : ℝ)) * (L : ℝ)⁻¹ +
        (bad.card : ℝ) / (Fintype.card (ResidueChoice S) : ℝ) := by ring
    _ ≤ (L : ℝ)⁻¹ +
        (bad.card : ℝ) / (Fintype.card (ResidueChoice S) : ℝ) :=
      add_le_add (mul_le_of_le_one_left hinv0 hgoodle) le_rfl
    _ = (L : ℝ)⁻¹ + finiteRootMixSmallLowerFibreMass S y L := rfl

private theorem coreFRMUpper_eventually_window_le_mix_cutoff
    {κ : ℝ} (hκ : 0 < κ) :
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
  have hprofileNat : profileS κ X ≤ sieveCutoff (X : ℝ) := Nat.cast_le.mp hprofile
  exact (ahlSmall_window_le_profileS κ X).trans
    (hprofileNat.trans (crtNestVR_sieveCutoff_mono hX1 hXt))

private theorem coreFRMUpper_mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply sum_pos'
  · intro t _
    exact mixWeightV_nonneg t
  · refine ⟨2 * X, ?_, ?_⟩
    · simp only [mixScale, mem_Ioc]
      omega
    · exact eulerProdNat_pos (sieveCutoff ((2 * X : ℕ) : ℝ))

theorem eventually_coreFiniteRootMixUpperException_le
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      coreFiniteRootMixUpperException κ X ≤
        (profileL κ X : ℝ)⁻¹ + finiteRootMixSmallLowerException κ X := by
  filter_upwards [coreFRMUpper_eventually_window_le_mix_cutoff hκ,
    eventually_one_le_profileL hκ, eventually_ge_atTop 1] with X hcut hL hX
  let S := ahlSmall_window κ X
  let L := profileL κ X
  have hZ : 0 < mixZ X := coreFRMUpper_mixZ_pos hX
  have hterm : ∀ t ∈ mixScale X,
      coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ)) ≤
        (L : ℝ)⁻¹ + finiteRootMixSmallLowerFibreMass S
          (sieveCutoff (t : ℝ)) L := by
    intro t ht
    exact coreFiniteRootMixUpperRootMass_le S (sieveCutoff (t : ℝ)) L
      (hcut t ht) hL
  unfold coreFiniteRootMixUpperException finiteRootMixSmallLowerException
  apply (div_le_iff₀ hZ).2
  calc
    ∑ t ∈ mixScale X, mixWeightV t *
        coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ)) ≤
      ∑ t ∈ mixScale X, mixWeightV t *
        ((L : ℝ)⁻¹ + finiteRootMixSmallLowerFibreMass S
          (sieveCutoff (t : ℝ)) L) :=
      sum_le_sum fun t ht =>
        mul_le_mul_of_nonneg_left (hterm t ht) (mixWeightV_nonneg t)
    _ = ((L : ℝ)⁻¹ +
          (∑ t ∈ mixScale X, mixWeightV t *
            finiteRootMixSmallLowerFibreMass S (sieveCutoff (t : ℝ)) L) /
              mixZ X) * mixZ X := by
      simp_rw [mul_add]
      rw [sum_add_distrib]
      have hconst :
          (∑ t ∈ mixScale X, mixWeightV t * (L : ℝ)⁻¹) =
            mixZ X * (L : ℝ)⁻¹ := by
        rw [← Finset.sum_mul]
        rfl
      rw [hconst, add_mul, div_mul_cancel₀ _ hZ.ne']
      ring

theorem tendsto_coreFiniteRootMixUpperException {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (coreFiniteRootMixUpperException κ) atTop (nhds 0) := by
  have hlim := (tendsto_inv_profileL hκ).add
    (tendsto_finiteRootMixSmallLowerException hκ)
  simp only [add_zero] at hlim
  exact squeeze_zero'
    (Eventually.of_forall fun X => coreFiniteRootMixUpperException_nonneg κ X)
    (eventually_coreFiniteRootMixUpperException_le hκ) hlim

/-! ### Deterministic smallness of the late retention -/

/-- Uniformly over the literal finite mix support, the late retention is at
most one quarter. -/
theorem coreFRMUpper_eventually_lateRetention_le_quarter
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X,
      lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) ≤ (1 / 4 : ℝ) := by
  have hratio := (crtLogSLogX_tendsto hκ).eventually_le_const
    (div_pos eulerProdLowerConst_pos (by norm_num : (0 : ℝ) < 4))
  filter_upwards [hratio, coreFRMUpper_eventually_window_le_mix_cutoff hκ,
    (tendsto_ahlSmall_window_atTop hκ).eventually_ge_atTop 16,
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 16)),
    eventually_one_le_profileS hκ] with X hratio hcut hS hX hPS
  intro t ht
  have htI : t ∈ Ioc X (2 * X) := by simpa [mixScale] using ht
  have hXtNat : X < t := (mem_Ioc.mp htI).1
  have hXt : (X : ℝ) < (t : ℝ) := Nat.cast_lt.mpr hXtNat
  have htexp : Real.exp 16 ≤ (t : ℝ) := hX.trans hXt.le
  have hbase := crtPhysRetZero_le (le_trans (by omega : 2 ≤ 16) hS) hS
    (hcut t ht) htexp
  have hXpos : (0 : ℝ) < X := (Real.exp_pos 16).trans_le hX
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hX)
  have hX1 : (1 : ℝ) < X :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hX
  have hlogt : 0 < Real.log (t : ℝ) := Real.log_pos (hX1.trans hXt)
  have hSprof : ahlSmall_window κ X ≤ profileS κ X :=
    ahlSmall_window_le_profileS κ X
  have hlogS : Real.log (ahlSmall_window κ X : ℝ) ≤
      Real.log (profileS κ X : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr hSprof)
  have hlogProf0 : 0 ≤ Real.log (profileS κ X : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.mpr hPS)
  have hlogDen : Real.log (X : ℝ) ≤ Real.log (t : ℝ) :=
    Real.log_le_log hXpos hXt.le
  have hrat :
      Real.log (ahlSmall_window κ X : ℝ) / Real.log (t : ℝ) ≤
        Real.log (profileS κ X : ℝ) / Real.log (X : ℝ) := by
    calc
      Real.log (ahlSmall_window κ X : ℝ) / Real.log (t : ℝ) ≤
          Real.log (profileS κ X : ℝ) / Real.log (t : ℝ) :=
        div_le_div_of_nonneg_right hlogS hlogt.le
      _ ≤ Real.log (profileS κ X : ℝ) / Real.log (X : ℝ) :=
        div_le_div_of_nonneg_left hlogProf0 hlogX hlogDen
  have hscaled := mul_le_mul_of_nonneg_left (hrat.trans hratio)
    (show (0 : ℝ) ≤ 1 / eulerProdLowerConst from
      div_nonneg zero_le_one eulerProdLowerConst_pos.le)
  exact hbase.trans (hscaled.trans_eq (by
    field_simp [eulerProdLowerConst_pos.ne']))

/-- Consequently the self-normalized good-count threshold is at most half
the presieve carrier cardinality. -/
theorem coreFRMUpper_eventually_twice_mean_le_half_card
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X, ∀ σ : ResidueChoice (ahlSmall_window κ X),
      2 * ((presieveSurvivors (ahlSmall_window κ X) σ).card : ℝ) *
          lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) ≤
        ((presieveSurvivors (ahlSmall_window κ X) σ).card : ℝ) / 2 := by
  filter_upwards [coreFRMUpper_eventually_lateRetention_le_quarter hκ] with X hθ
  intro t ht σ
  have hc : (0 : ℝ) ≤ (presieveSurvivors (ahlSmall_window κ X) σ).card :=
    Nat.cast_nonneg _
  have := hθ t ht
  nlinarith

end

end PrimeGapNormality.Prime
