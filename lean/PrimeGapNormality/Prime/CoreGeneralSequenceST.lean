import PrimeGapNormality.Prime.CoreGeneralModelReference
import PrimeGapNormality.Prime.CoreSequenceSTMeanTail
import PrimeGapNormality.Prime.CoreSequenceSubexponentialTail
import PrimeGapNormality.Prime.StoppedUnequalMass

/-!
# Sequence S/T with arbitrary calibrated rooted mixtures

S compares the actual finite pattern law with the actual cutoff-weighted
rooted law. It is not a bundle of model consequences. T is the bare first
gap-tail mean, including eventual nonempty physical windows. The canonical
positive square-root reserve and original span are used unchanged.
-/

namespace PrimeGapNormality.Prime.CoreGeneralSequenceST
open Filter Finset MeasureTheory MvPolynomial CoreCyclic
open CoreGeneralModelReference CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
  CoreSequencePatternLaw CoreSequenceWindowGrowthFromS CoreSequenceSubexponentialGrowth
  CoreSequenceSTMeanTail CoreSequenceSTConsumer
open scoped Classical Topology NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def span (κ : ℝ) (G : ℕ → ℝ) (X : ℕ) : ℕ := physicalSpan G (rank κ G) X

def model (κ : ℝ) (G : ℕ → ℝ) (ω : ℕ → ℕ → ℝ) (X : ℕ) : Finset ℕ → ℝ :=
  CoreCalibratedMixtureMoments.law (ω X) (span κ G X)

/-- Uniformity in the finite shape test is inside the eventual X. -/
def ShapeS (a : ℕ → ℕ) (κ : ℝ) (G : ℕ → ℝ) (ω : ℕ → ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ X in atTop, ∀ f : Finset ℕ → ℝ,
    (∀ U ∈ (offsetWindow (span κ G X)).powerset.filter (fun U => U.card = rank κ G X), 0 ≤ f U) →
    (∀ U ∈ (offsetWindow (span κ G X)).powerset.filter (fun U => U.card = rank κ G X), f U ≤ 1) →
    Stopped.failureMass (offsetWindow (span κ G X))
        (patternMass a X (offsetWindow (span κ G X))) (rank κ G X) +
      shapeMean (offsetWindow (span κ G X))
        (patternMass a X (offsetWindow (span κ G X))) (rank κ G X) f ≤
      c * shapeMean (offsetWindow (span κ G X)) (model κ G ω X) (rank κ G X) f + ε

/-- The real-test restriction of the paper's literal short-test equality.
Unlike positive S this definition does NOT assume any failure bound. -/
def PatternS (a : ℕ → ℕ) (κ : ℝ) (G : ℕ → ℝ) (ω : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ X in atTop, ∀ f : Finset ℕ → ℝ,
    (∀ U ∈ (offsetWindow (span κ G X)).powerset.filter (fun U => U.card = rank κ G X), |f U| ≤ 1) →
    |shapeMean (offsetWindow (span κ G X))
        (patternMass a X (offsetWindow (span κ G X))) (rank κ G X) f -
      shapeMean (offsetWindow (span κ G X)) (model κ G ω X) (rank κ G X) f| ≤ ε

def complexShapeMean (Ω : Finset ℕ) (μ : Finset ℕ → ℝ) (L : ℕ)
    (f : Finset ℕ → ℂ) : ℂ :=
  ∑ U ∈ Ω.powerset.filter (fun U => U.card = L), f U * (Stopped.shortShapeMass Ω μ L U : ℂ)

/-- Literal complex first-M comparison on the actual pattern laws. The
restriction to M-point subsets represents tests zero when x_M>S. -/
def ComplexPatternS (a : ℕ → ℕ) (κ : ℝ) (G : ℕ → ℝ) (ω : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ X in atTop, ∀ f : Finset ℕ → ℂ,
    (∀ U ∈ (offsetWindow (span κ G X)).powerset.filter (fun U => U.card = rank κ G X), ‖f U‖ ≤ 1) →
    ‖complexShapeMean (offsetWindow (span κ G X))
        (patternMass a X (offsetWindow (span κ G X))) (rank κ G X) f -
      complexShapeMean (offsetWindow (span κ G X)) (model κ G ω X) (rank κ G X) f‖ ≤ ε

theorem patternS_of_complex {a : ℕ → ℕ} {κ : ℝ} {G : ℕ → ℝ} {ω : ℕ → ℕ → ℝ}
    (h : ComplexPatternS a κ G ω) : PatternS a κ G ω := by
  intro ε hε
  filter_upwards [h ε hε] with X hx
  intro f hf
  have he (Ω : Finset ℕ) (μ : Finset ℕ → ℝ) (L : ℕ) :
      complexShapeMean Ω μ L (fun U => (f U : ℂ)) = (shapeMean Ω μ L f : ℂ) := by
    simp only [complexShapeMean, shapeMean, Complex.ofReal_sum, Complex.ofReal_mul]
  have hh := hx (fun U => (f U : ℂ)) (fun U hU => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hf U hU)
  simpa only [he, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh

/-- Model span concentration, rather than an extra arithmetic assumption,
supplies the actual failure bound needed by positive resampling. -/
theorem shapeS_of_patternS {a : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ) {G : ℕ → ℝ}
    (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G)
    (hS : PatternS a κ G ω) (hne : ∀ᶠ X in atTop, 0 < (seqWindow a X).card) :
    ShapeS a κ G ω 1 := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hfail := CoreCalibratedMixtureCountException.tendsto_mixture_failure_zero hG hκ
    (tendsto_rank_ratio hκ hG) hω hsum hcal
  filter_upwards [hS (ε / 3) hε3, hne,
    hfail.eventually_le_const hε3,
    CoreCalibratedMixtureMoments.eventually_law_total hG hω hsum hcal (span κ G)] with X hx hN hνfail htotal
  let Ω := offsetWindow (span κ G X)
  let L := rank κ G X
  let μ := patternMass a X Ω
  let ν := model κ G ω X
  have hμmass : shapeMean Ω μ L (fun _ => 1) + Stopped.failureMass Ω μ L = 1 := by
    have hh := Stopped.shortShapeMass_add_failureMass (Ω := Ω) (μ := μ) (L := L)
    rw [patternMass_total Ω hN] at hh
    simpa only [shapeMean, one_mul] using hh
  have hνmass : shapeMean Ω ν L (fun _ => 1) + Stopped.failureMass Ω ν L = 1 := by
    have hh := Stopped.shortShapeMass_add_failureMass (Ω := Ω) (μ := ν) (L := L)
    change (∑ U ∈ Ω.powerset, ν U) = 1 at htotal
    rw [htotal] at hh
    simpa only [shapeMean, one_mul] using hh
  have hone := hx (fun _ => 1) (fun _ _ => by norm_num)
  have hone' := (abs_le.1 hone).1
  have hμfail : Stopped.failureMass Ω μ L ≤ 2 * (ε / 3) := by
    change Stopped.failureMass Ω ν L ≤ ε / 3 at hνfail
    change -(ε / 3) ≤ shapeMean Ω μ L (fun _ => 1) - shapeMean Ω ν L (fun _ => 1) at hone'
    linarith
  intro f hf0 hf1
  have htest := (abs_le.1 (hx f (fun U hU => by rw [abs_of_nonneg (hf0 U hU)]; exact hf1 U hU))).2
  change shapeMean Ω μ L f - shapeMean Ω ν L f ≤ ε / 3 at htest
  change Stopped.failureMass Ω μ L + shapeMean Ω μ L f ≤ 1 * shapeMean Ω ν L f + ε
  linarith

theorem eventually_singleton_bound {κ : ℝ} (hκ : 0 < κ) {G : ℕ → ℝ}
    (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G) :
    ∀ᶠ X in atTop, ∀ d ∈ offsetWindow (span κ G X),
      Stopped.inclusionMass (offsetWindow (span κ G X)) (model κ G ω X) {d} ≤
        singletonCap G (rank κ G) X := by
  filter_upwards [CoreCalibratedAuxiliaryFrame.eventually_profile_data hG hκ
    (tendsto_rank_ratio hκ hG) hω hsum hcal,
    eventually_support_singleton_le hG hκ (tendsto_rank_ratio hκ hG) hcal] with X hdata hsite
  obtain ⟨N, hz, hs⟩ := hdata.2.2.2
  intro d hd
  have hd' : 1 ≤ d ∧ d ≤ span κ G X := Finset.mem_Icc.1 hd
  have he : Stopped.inclusionMass (offsetWindow (span κ G X)) (model κ G ω X) {d} =
      ∑ y ∈ range N, ω X y *
        Stopped.inclusionMass (offsetWindow (span κ G X)) (actualRootLaw y (span κ G X)) {d} := by
    unfold Stopped.inclusionMass model CoreCalibratedMixtureMoments.law
    simp_rw [weighted_tsum_eq_sum_of_tail_zero (ω X) _ hz]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [he]
  calc
    _ ≤ ∑ y ∈ range N, ω X y * singletonCap G (rank κ G) X := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hwy : ω X y = 0
      · simp only [hwy, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left
          (hsite y (lt_of_le_of_ne (hω X y) (Ne.symm hwy)) d hd'.1 hd'.2) (hω X y)
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]

/-- Count growth is forced by genuine singleton caps and the uniform S
test; it is not an independent density assumption. -/
theorem windowCountToInfinity {a : ℕ → ℕ} (ha : StrictMono a) {κ c : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G)
    (hS : ShapeS a κ G ω c) (hne : ∀ᶠ X in atTop, 0 < (seqWindow a X).card) :
    WindowCountToInfinity a := by
  change Tendsto (fun X : ℕ => ((seqWindow a X).card : ℝ)) atTop atTop
  have hnat : Tendsto (fun X => (seqWindow a X).card) atTop atTop := by
    apply tendsto_atTop.mpr
    intro m
    let ε : ℝ := 1 / (4 * ((m : ℝ) + 1))
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hε1 : ε < 1 := by
      dsimp [ε]
      apply (div_lt_iff₀ (by positivity)).2
      have hm := Nat.cast_nonneg (α := ℝ) m
      linarith
    have hη : Tendsto (fun X => c * singletonCap G (rank κ G) X)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_singletonCap_zero hG hκ (tendsto_rank_ratio hκ hG)).const_mul c
    filter_upwards [hS ε hε, hne,
      eventually_singleton_bound hκ hG hω hsum hcal,
      (tendsto_rank_atTop hκ hG).eventually_ge_atTop 1,
      hη.eventually_le_const hε] with X hSX hN hsite hL hηX
    have hf := hSX (fun _ => 0) (fun _ _ => le_rfl) (fun _ _ => zero_le_one)
    simp only [shapeMean, zero_mul, sum_const_zero, mul_zero, add_zero, zero_add] at hf
    obtain ⟨d, hd, hm⟩ := exists_point_mass_ge ha X (span κ G X) hL hN (hf.trans_lt hε1)
    have hpoint := hSX (pointTest d) (fun U _ => (pointTest_bounds d U).1)
      (fun U _ => (pointTest_bounds d U).2)
    have hmodel := (point_shapeMean_le_inclusion (offsetWindow (span κ G X)) (model κ G ω X)
      (fun U _ => CoreCalibratedMixtureMoments.law_nonneg (ω X) (hω X) _ U)
      (rank κ G X) d).trans (hsite d hd)
    have hf0 : 0 ≤ Stopped.failureMass (offsetWindow (span κ G X))
        (patternMass a X (offsetWindow (span κ G X))) (rank κ G X) := by
      unfold Stopped.failureMass
      exact Finset.sum_nonneg fun U _ => patternMass_nonneg _ _ _ _
    have hcmodel := mul_le_mul_of_nonneg_left hmodel hc.le
    have hinv : (1 : ℝ) / (seqWindow a X).card ≤ 2 * ε := by linarith
    have hden := (div_le_iff₀ (Nat.cast_pos.2 hN)).1 hinv
    have heq : (4 * ((m : ℝ) + 1)) * ε = 1 := by
      dsimp [ε]
      field_simp [show (m : ℝ) + 1 ≠ 0 by positivity]
    by_contra hn
    have hn' : ((seqWindow a X).card : ℝ) < m := Nat.cast_lt.2 (Nat.lt_of_not_ge hn)
    have hmul := mul_le_mul_of_nonneg_left hn'.le hε.le
    nlinarith
  apply ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hnat).congr'
  exact Eventually.of_forall fun X => rfl

theorem gapTailT {a : ℕ → ℕ} (ha : StrictMono a) {κ c : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G)
    (hS : ShapeS a κ G ω c) (hT : MeanGapTailT a (localTailBase κ) G) :
    GapTailT a (localTailBase κ) G := by
  have hcount := windowCountToInfinity ha hκ hc hG hω hsum hcal hS
    (meanGapTail_eventually_nonempty hT)
  have hsub := sequence_hasSubexponentialGrowth ha hcount
  obtain ⟨C, hC, ht⟩ := hT
  exact ⟨localTailBase_one_lt hκ, hG, hsub.summable_div_pow (localTailBase_one_lt hκ), C, hC, ht⟩

theorem shapeMean_div (Ω : Finset ℕ) (μ : Finset ℕ → ℝ) (L : ℕ)
    (f : Finset ℕ → ℝ) (C : ℝ) :
    shapeMean Ω μ L (fun U => f U / C) = shapeMean Ω μ L f / C := by
  unfold shapeMean
  simp only [div_mul_eq_mul_div, Finset.sum_div]

theorem shapeMean_actualTest_eq_mean
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) (P : PeriodicLocal k)
    (w S M : ℕ) (hwM : w ≤ M) (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (ω : ℕ → ℝ) {N : ℕ} (hz : ∀ y, N ≤ y → ω y = 0) (f : AddCircle (1 : ℝ) →ᵇ ℝ) :
    shapeMean (offsetWindow S) (CoreCalibratedMixtureMoments.law ω S) M
      (CoreLocalModelPositive.actualTest B hk r P (M - w) f) =
      CoreCalibratedModelFinite.mean ω S M (CoreLocalModelPositive.actualTest B hk r P (M - w) f) := by
  rw [shapeMean, firstL_test_eq_pushforward]
  simp_rw [CoreLocalModelPositive.actualTest, CoreActualCyclicSlot.actualFinitePhase,
    coreCyclicFinitePhase_firstL B hk r P hwM hw]
  exact (CoreCalibratedModelFinite.mean_eq_law ω S M hz _).symm

/-- The sequence comparison, with the genuine infinite-series tail added.
Every occurrence of M and S is the same actual reserve/span used in S. -/
theorem positive_comparison
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (P : PeriodicLocal k) (w d : ℕ) (hd : 1 ≤ d)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w) (hdeg : ∀ s, (P s).totalDegree ≤ d)
    {κ c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {Kf : ℝ≥0} (hKf : LipschitzWith Kf f)
    (hf : ∀ x, 0 ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop,
      windowAvgReal (seqWindow a X) (fun n => f (sequenceLocalOrbit B hk r P a n)) ≤
        c * CoreCalibratedModelSubsequence.modelMean B hk r P w G (rank κ G) ω X f + ε := by
  have hb : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hκp : 0 < κ := (div_pos (Nat.cast_pos.2 (show 0 < d by omega)) (Real.log_pos hb)).trans_le hκ
  have hcount := windowCountToInfinity ha hκp hc hG hω hsum hcal hS
    (meanGapTail_eventually_nonempty hT)
  have hgrowth := sequenceGap_hasSubexponentialGrowth ha hcount
  have ht := tendsto_sequence_localPositiveTestRemainder_zero_of_subexponential ha hcount hB
    (localTailBase_pow_le hB hd hκ) hk r P w hd hw hdeg hgrowth
    (gapTailT ha hκp hc hG hω hsum hcal hS hT) f hKf
  let C : ℝ := ‖f‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hfC (x : AddCircle (1 : ℝ)) : f x ≤ C :=
    (f.apply_le_norm x).trans (le_add_of_nonneg_right zero_le_one)
  have he2 : 0 < ε / 2 := by positivity
  filter_upwards [hS (ε / (2 * C)) (by positivity),
    (tendsto_rank_atTop hκp hG).eventually_ge_atTop (w + 1),
    ht.eventually_le_const he2,
    CoreCalibratedAuxiliaryFrame.eventually_profile_data hG hκp
      (tendsto_rank_ratio hκp hG) hω hsum hcal] with X hs hM htail hdata
  let M := rank κ G X
  let S := span κ G X
  let t : Finset ℕ → ℝ := CoreLocalModelPositive.actualTest B hk r P (M - w) f
  have hs' := hs (fun U => t U / C)
    (fun U _ => div_nonneg (hf _) hC.le) (fun U _ => (div_le_one hC).2 (hfC _))
  rw [shapeMean_div, shapeMean_div] at hs'
  have hscale := mul_le_mul_of_nonneg_left hs' hC.le
  have heps : C * (ε / (2 * C)) = ε / 2 := by field_simp [hC.ne'] <;> ring
  have hshape : C * Stopped.failureMass (offsetWindow S) (patternMass a X (offsetWindow S)) M +
      shapeMean (offsetWindow S) (patternMass a X (offsetWindow S)) M t ≤
      c * shapeMean (offsetWindow S) (model κ G ω X) M t + ε / 2 := by
    have he (v : ℝ) : C * (v / C) = v := by field_simp [hC.ne']
    simpa only [mul_add, mul_left_comm C c, he, heps] using hscale
  obtain ⟨N, hz, hsumN⟩ := hdata.2.2.2
  rw [show shapeMean (offsetWindow S) (model κ G ω X) M t =
      CoreCalibratedModelSubsequence.modelMean B hk r P w G (rank κ G) ω X f from
    shapeMean_actualTest_eq_mean B hk r P w S M (by dsimp [M]; omega) hw (ω X) hz f] at hshape
  have hfinite := CoreSequenceLocalPositiveWindow.truncated_positive_window_le
    ha B X S hk r P (by dsimp [M]; omega : w ≤ M) (by dsimp [M]; omega : 1 ≤ M) hw f hfC
  have htrunc : windowAvgReal (seqWindow a X) (fun n =>
      f (coreLocalSeriesTrunc B hk r (fun q => (seqGap a q : ℝ)) P n (M - w) : AddCircle (1 : ℝ))) ≤
      c * CoreCalibratedModelSubsequence.modelMean B hk r P w G (rank κ G) ω X f + ε / 2 := by
    apply le_trans _ hshape
    have hrealGap : CoreSequenceLocalPositiveWindow.realGap a =
        fun q => (seqGap a q : ℝ) := by
      funext q
      rfl
    rw [hrealGap] at hfinite
    simpa only [shapeMean, t, CoreLocalModelPositive.actualTest, CoreActualCyclicSlot.actualFinitePhase,
      offsetWindow] using hfinite
  have htail' : windowAvgReal (seqWindow a X) (fun n =>
      |f (sequenceLocalOrbit B hk r P a n) -
        f (coreLocalSeriesTrunc B hk r (fun q => (seqGap a q : ℝ)) P n (M - w) : AddCircle (1 : ℝ))|) ≤ ε / 2 := by
    simpa only [sequenceLocalOrbit, M, rank_eq_stdProfile hκp] using htail
  have htriangle : windowAvgReal (seqWindow a X) (fun n => f (sequenceLocalOrbit B hk r P a n)) ≤
      windowAvgReal (seqWindow a X) (fun n =>
        f (coreLocalSeriesTrunc B hk r (fun q => (seqGap a q : ℝ)) P n (M - w) : AddCircle (1 : ℝ))) +
      windowAvgReal (seqWindow a X) (fun n =>
        |f (sequenceLocalOrbit B hk r P a n) -
          f (coreLocalSeriesTrunc B hk r (fun q => (seqGap a q : ℝ)) P n (M - w) : AddCircle (1 : ℝ))|) := by
    unfold windowAvgReal
    rw [← add_div, ← Finset.sum_add_distrib]
    have hpoint : ∀ n ∈ seqWindow a X,
        f (sequenceLocalOrbit B hk r P a n) ≤
          f (coreLocalSeriesTrunc B hk r (fun q => (seqGap a q : ℝ)) P n
            (M - w) : AddCircle (1 : ℝ)) +
          |f (sequenceLocalOrbit B hk r P a n) -
            f (coreLocalSeriesTrunc B hk r (fun q => (seqGap a q : ℝ)) P n
              (M - w) : AddCircle (1 : ℝ))| := by
      intro n hn
      linarith [le_abs_self
        (f (sequenceLocalOrbit B hk r P a n) -
          f (coreLocalSeriesTrunc B hk r (fun q => (seqGap a q : ℝ)) P n
            (M - w) : AddCircle (1 : ℝ)))]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) (Nat.cast_nonneg _)
  linarith

/-- Reference selection follows every prescribed physical subsequence and
precedes every positive test. Both the model and the S/T comparison are
discharged from their actual definitions. -/
theorem subsequenceReference
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (P : PeriodicLocal k) (w : ℕ)
    (hroot : drop hk P = 0) (hP : P ≠ 0)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    {κ c : ℝ} (hκ : (topDegree P : ℝ) / Real.log (B : ℝ) ≤ κ) (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    CoreResidueDigitalReference.SubsequenceReferenceBounds (sequenceLocalOrbit B hk r P a)
      (fun X => seqCount a X) (CoreSequenceResiduePassage.seqCountDifference a) := by
  have hd := one_le_topDegree_of_rooted hk P hroot hP
  have hdeg : ∀ s, (P s).totalDegree ≤ topDegree P := fun s =>
    Finset.le_sup (f := fun t => (P t).totalDegree) (Finset.mem_univ s)
  intro χ hχ
  have hGχ : Tendsto (fun X => G (χ X)) atTop atTop := by
    simpa only [Function.comp_def] using hG.comp hχ.tendsto_atTop
  have hcal' : UniformCalibration (fun X y => ω (χ X) y) (fun X => G (χ X)) := by
    intro ε hε
    exact hχ.tendsto_atTop.eventually (hcal ε hε)
  obtain ⟨ψ, hψ, σ, hσfin, hσac, hmass, hmodel⟩ :=
    CoreGeneralModelReference.exists_reference_subsequence hB hk r w P hroot hP hw hκ
      hGχ (fun X y => hω (χ X) y) (fun X => hsum (χ X)) hcal'
  refine ⟨ψ, hψ, σ, hσfin, hσac, c * CoreCalibratedModelFinite.modelConstant,
    mul_nonneg hc.le CoreCalibratedModelFinite.modelConstant_nonneg, ?_⟩
  intro f Kf hKf hf ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hδ : 0 < ε / (2 * c) := by positivity
  have hχψ : Tendsto (fun n => χ (ψ n)) atTop atTop := by
    simpa only [Function.comp_def] using hχ.tendsto_atTop.comp hψ.tendsto_atTop
  filter_upwards [hmodel f Kf hKf hf (ε / (2 * c)) hδ,
    hχψ.eventually
      (positive_comparison ha hB hk r P w (topDegree P) hd hw hdeg hκ hc hG
        hω hsum hcal hS hT f hKf hf hε2)] with n hm hp
  change CoreCalibratedModelSubsequence.modelMean B hk r P w G (rank κ G) ω (χ (ψ n)) f ≤
    CoreCalibratedModelFinite.modelConstant * (∫ x, f x ∂σ) + ε / (2 * c) at hm
  rw [windowAvgReal_eq_coreDigitalWindowAverage ha] at hp
  have hscaled := mul_le_mul_of_nonneg_left hm hc.le
  have heps : c * (ε / (2 * c)) = ε / 2 := by field_simp [hc.ne'] <;> ring
  calc
    _ ≤ c * CoreCalibratedModelSubsequence.modelMean B hk r P w G (rank κ G) ω (χ (ψ n)) f + ε / 2 := hp
    _ ≤ c * (CoreCalibratedModelFinite.modelConstant * (∫ x, f x ∂σ) + ε / (2 * c)) + ε / 2 :=
      _root_.add_le_add hscaled le_rfl
    _ = _ := by rw [mul_add, heps]; ring

private theorem clock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) : 2 ≤ B ^ k := by
  rw [show k = k - 1 + 1 by omega, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

private theorem fourier_clock (z : ℤ) (C q : ℕ) (x : ℝ) :
    fourier z (C ^ q • (x : AddCircle (1 : ℝ))) = e ((z : ℝ) * (C : ℝ) ^ q * x) := by
  rw [← AddCircle.coe_nsmul, fourier_coe_apply]
  simp only [nsmul_eq_mul, Nat.cast_pow, e, Complex.ofReal_one, div_one,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

/-- The first final arithmetic-free S/T normality endpoint: integer local
tuples in nonzero rooted normal form. No density, growth, summability,
model-limit or reference premise remains. -/
theorem fullSeries_weyl_clock
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (F : Fin k → MvPolynomial ℕ ℤ) (w : ℕ)
    (hroot : drop hk (mapIntTuple F) = 0) (hF : mapIntTuple F ≠ 0)
    (hw : ∀ s i, i ∈ (mapIntTuple F s).vars → i ≤ w)
    {κ c : ℝ} (hκ : (topDegree (mapIntTuple F) : ℝ) / Real.log (B : ℝ) ≤ κ) (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion (B ^ k)
      (coreCyclicFullSeries B hk r (fun q => (seqGap a q : ℝ)) (mapIntTuple F)) := by
  have hd := one_le_topDegree_of_rooted hk (mapIntTuple F) hroot hF
  have hb : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hκp : 0 < κ := (div_pos (Nat.cast_pos.2 (show 0 < topDegree (mapIntTuple F) by omega))
    (Real.log_pos hb)).trans_le hκ
  have hcount := windowCountToInfinity ha hκp hc hG hω hsum hcal hS
    (meanGapTail_eventually_nonempty hT)
  have hgrowth := sequenceGap_hasSubexponentialGrowth ha hcount
  have href := subsequenceReference ha hB hk r (mapIntTuple F) w hroot hF hw hκ hc hG
    hω hsum hcal hS hT
  have hrec : ∀ n, sequenceLocalOrbit B hk r (mapIntTuple F) a (n + k) =
      B ^ k • sequenceLocalOrbit B hk r (mapIntTuple F) a n := by
    intro n
    unfold sequenceLocalOrbit
    simpa only [coreLocalSeriesCircle, Int.cast_natCast] using
      coreLocalSeriesCircle_add_period_of_intTuple_subexponential hB hk r
        (fun q => (seqGap a q : ℤ)) (by simpa only [Int.cast_natCast] using hgrowth) F n
  intro z hz
  have hchar := CoreSequenceResiduePassage.residue_character_cesaro_of_subsequence_reference
    ha hcount (clock_ge hB hk) hk (r := 0) hk (sequenceLocalOrbit B hk r (mapIntTuple F) a) hrec href hz
  unfold CesaroMeanVanishing at hchar
  apply hchar.congr'
  exact Eventually.of_forall fun N => by
    apply congrArg (fun v : ℂ => v / (N : ℂ))
    apply Finset.sum_congr rfl
    intro q hq
    have horbit := coreLocalSeriesCircle_progression_zero_eq_fullSeries_subexponential
      hB hk r (fun j => (seqGap a j : ℤ)) (by simpa only [Int.cast_natCast] using hgrowth) F q
    simp only [Int.cast_natCast] at horbit
    change fourier z (coreLocalSeriesCircle B hk r (fun j => (seqGap a j : ℝ))
      (mapIntTuple F) (q * k + 0)) = _
    rw [show q * k + 0 = k * q by simp only [Nat.add_zero, Nat.mul_comm], horbit]
    exact fourier_clock z (B ^ k) q _

theorem fullSeries_isNormal
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (F : Fin k → MvPolynomial ℕ ℤ) (w : ℕ)
    (hroot : drop hk (mapIntTuple F) = 0) (hF : mapIntTuple F ≠ 0)
    (hw : ∀ s i, i ∈ (mapIntTuple F s).vars → i ≤ w)
    {κ c : ℝ} (hκ : (topDegree (mapIntTuple F) : ℝ) / Real.log (B : ℝ) ≤ κ) (hc : 0 < c)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk r (fun q => (seqGap a q : ℝ)) (mapIntTuple F)) :=
  CoreWeylNormality.isNormal_of_weyl hB (weylCriterion_of_pow hB hk
    (fullSeries_weyl_clock ha hB hk r F w hroot hF hw hκ hc hG hω hsum hcal hS hT))

/-- Paper-facing integer-rooted endpoint: literal uniform complex (S),
actual first-gap mean (T), and arbitrary qualitative calibration only. -/
theorem fullSeries_isNormal_of_complexPatternS
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (F : Fin k → MvPolynomial ℕ ℤ) (w : ℕ)
    (hroot : drop hk (mapIntTuple F) = 0) (hF : mapIntTuple F ≠ 0)
    (hw : ∀ s i, i ∈ (mapIntTuple F s).vars → i ≤ w)
    {κ : ℝ} (hκ : (topDegree (mapIntTuple F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) {ω : ℕ → ℕ → ℝ}
    (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ComplexPatternS a κ G ω)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk r (fun q => (seqGap a q : ℝ)) (mapIntTuple F)) := by
  have hd := one_le_topDegree_of_rooted hk (mapIntTuple F) hroot hF
  have hb : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hκp : 0 < κ := (div_pos (Nat.cast_pos.2 (show 0 < topDegree (mapIntTuple F) by omega))
    (Real.log_pos hb)).trans_le hκ
  exact fullSeries_isNormal ha hB hk r F w hroot hF hw hκ (by norm_num : (0 : ℝ) < 1)
    hG hω hsum hcal
    (shapeS_of_patternS hκp hG hω hsum hcal (patternS_of_complex hS)
      (meanGapTail_eventually_nonempty hT)) hT

end
end PrimeGapNormality.Prime.CoreGeneralSequenceST
