import PrimeGapNormality.Prime.CoreGeneralSequenceST

/-!
# Positive-density sequences are excluded from the diverging-gap model

The paper's calibrated model has vanishing one-site inclusion probabilities
when `G -> infinity`.  On the other hand, a strictly increasing sequence of
positive natural density has a positive proportion of bounded first gaps in
every sufficiently large dyadic physical window.  A single bounded positive
shape test therefore contradicts `ComplexPatternS`.

This is a sequence-generic statement.  In particular, it does not use a
tail condition, a prime theorem, or a special description of squarefree
integers.
-/

namespace PrimeGapNormality.Prime.CoreGeneralPositiveDensityExclusion

open Filter Finset
open CoreSequencePattern CoreSequencePatternLaw CoreSequenceResiduePassage
open CoreSequenceWindowGrowthFromS CoreCalibratedMixtureProfile
open CoreCalibratedMixtureFiniteSupport
open CoreGeneralModelReference CoreGeneralSequenceST
open scoped Classical Topology

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Indicator that a finite rooted shape contains a point at distance at
most `K` from its root. -/
def smallPointTest (K : ℕ) (U : Finset ℕ) : ℝ :=
  if ∃ d ∈ Icc 1 K, d ∈ U then 1 else 0

theorem smallPointTest_bounds (K : ℕ) (U : Finset ℕ) :
    0 ≤ smallPointTest K U ∧ smallPointTest K U ≤ 1 := by
  unfold smallPointTest
  split_ifs <;> norm_num

private theorem smallPointTest_le_sum_pointTest (Ω : Finset ℕ) (K : ℕ)
    {U : Finset ℕ} (hU : U ⊆ Ω) :
    smallPointTest K U ≤ ∑ d ∈ Icc 1 K ∩ Ω, pointTest d U := by
  by_cases h : ∃ d ∈ Icc 1 K, d ∈ U
  · obtain ⟨d, hdK, hdU⟩ := h
    rw [smallPointTest, if_pos ⟨d, hdK, hdU⟩]
    have hone : (1 : ℝ) = pointTest d U := by simp [pointTest, hdU]
    rw [hone]
    apply Finset.single_le_sum (fun i hi => (pointTest_bounds i U).1)
    exact Finset.mem_inter.mpr ⟨hdK, hU hdU⟩
  · rw [smallPointTest, if_neg h]
    exact Finset.sum_nonneg fun i hi => (pointTest_bounds i U).1

private theorem shortShapeMass_nonneg
    (Ω : Finset ℕ) (μ : Finset ℕ → ℝ)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U) (L : ℕ) (K : Finset ℕ) :
    0 ≤ Stopped.shortShapeMass Ω μ L K := by
  unfold Stopped.shortShapeMass
  apply Finset.sum_nonneg
  intro U hU
  split_ifs
  · exact hμ U hU
  · exact le_rfl

/-- The small-point shape test is bounded by the sum of its singleton
inclusion masses. -/
theorem smallPoint_shapeMean_le_sum_inclusion
    (Ω : Finset ℕ) (μ : Finset ℕ → ℝ)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U) (L K : ℕ) :
    shapeMean Ω μ L (smallPointTest K) ≤
      ∑ d ∈ Icc 1 K ∩ Ω, Stopped.inclusionMass Ω μ {d} := by
  calc
    shapeMean Ω μ L (smallPointTest K) ≤
        shapeMean Ω μ L (fun U => ∑ d ∈ Icc 1 K ∩ Ω, pointTest d U) := by
      unfold shapeMean
      apply Finset.sum_le_sum
      intro U hU
      exact mul_le_mul_of_nonneg_right
        (smallPointTest_le_sum_pointTest Ω K
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1))
        (shortShapeMass_nonneg Ω μ hμ L U)
    _ = ∑ d ∈ Icc 1 K ∩ Ω, shapeMean Ω μ L (pointTest d) := by
      unfold shapeMean
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ ∑ d ∈ Icc 1 K ∩ Ω, Stopped.inclusionMass Ω μ {d} := by
      apply Finset.sum_le_sum
      intro d hd
      exact point_shapeMean_le_inclusion Ω μ hμ L d

/-- The first genuine gap is detected by `smallPointTest` as soon as one
point is retained. -/
private theorem smallGapTest_le_prefixTest
    {a : ℕ → ℕ} (ha : StrictMono a) (K n L : ℕ) (hL : 1 ≤ L) :
    (if seqGap a n ≤ K then (1 : ℝ) else 0) ≤
      smallPointTest K (prefixSet a n L) := by
  by_cases hgap : seqGap a n ≤ K
  · have hpos : 1 ≤ seqGap a n := by
      unfold seqGap
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.sub_pos_of_lt (ha (Nat.lt_succ_self n))))
    have hmem : seqGap a n ∈ prefixSet a n L := by
      unfold prefixSet seqGap offset
      apply Finset.mem_image.mpr
      refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      simp only [Nat.add_zero]
    have htest : smallPointTest K (prefixSet a n L) = 1 := by
      exact if_pos ⟨seqGap a n, Finset.mem_Icc.mpr ⟨hpos, hgap⟩, hmem⟩
    simp only [if_pos hgap, htest, le_refl]
  · simp only [hgap, if_false]
    exact (smallPointTest_bounds K (prefixSet a n L)).1

private theorem nat_mul_tendsto_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun X : ℕ => k * X) atTop atTop :=
  tendsto_atTop_atTop_of_monotone
    (fun _ _ h => Nat.mul_le_mul_left k h)
    (fun N => ⟨N, Nat.le_mul_of_pos_left N hk⟩)

/-- Positive natural density gives a linear lower bound for every dyadic
window and locates its next sequence value below `3X`. -/
theorem eventually_dense_dyadic_geometry
    {a : ℕ → ℕ} (ha : StrictMono a) {d : ℝ} (hd : 0 < d)
    (hdensity : Tendsto (fun X : ℕ => (seqCount a X : ℝ) / (X : ℝ))
      atTop (nhds d)) :
    ∀ᶠ X : ℕ in atTop,
      0 < X ∧
      d / 2 * (X : ℝ) ≤ ((seqWindow a X).card : ℝ) ∧
      a (seqCount a (2 * X)) ≤ 3 * X := by
  have htwo : Tendsto
      (fun X : ℕ => (seqCount a (2 * X) : ℝ) / ((2 * X : ℕ) : ℝ))
      atTop (nhds d) := by
    simpa only [Function.comp_def] using
      hdensity.comp (nat_mul_tendsto_atTop 2 (by norm_num))
  have hthree : Tendsto
      (fun X : ℕ => (seqCount a (3 * X) : ℝ) / ((3 * X : ℕ) : ℝ))
      atTop (nhds d) := by
    simpa only [Function.comp_def] using
      hdensity.comp (nat_mul_tendsto_atTop 3 (by norm_num))
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_order.mp hdensity).1 (7 * d / 8) (by linarith),
    (tendsto_order.mp hdensity).2 (9 * d / 8) (by linarith),
    (tendsto_order.mp htwo).1 (7 * d / 8) (by linarith),
    (tendsto_order.mp htwo).2 (9 * d / 8) (by linarith),
    (tendsto_order.mp hthree).1 (7 * d / 8) (by linarith)] with
      X hX hXlo hXup h2lo h2up h3lo
  have hXpos : 0 < X := by omega
  have hXr : (0 : ℝ) < X := Nat.cast_pos.mpr hXpos
  have h2Xr : (0 : ℝ) < (2 * X : ℕ) := Nat.cast_pos.mpr (by omega)
  have h3Xr : (0 : ℝ) < (3 * X : ℕ) := Nat.cast_pos.mpr (by omega)
  have hA1up := (div_lt_iff₀ hXr).mp hXup
  have hA2lo := (lt_div_iff₀ h2Xr).mp h2lo
  have hA2up := (div_lt_iff₀ h2Xr).mp h2up
  have hA3lo := (lt_div_iff₀ h3Xr).mp h3lo
  have hmono12 : seqCount a X ≤ seqCount a (2 * X) :=
    seqCount_mono (by omega)
  have hwindow : d / 2 * (X : ℝ) ≤ ((seqWindow a X).card : ℝ) := by
    rw [seqWindow_card_eq_countDifference ha]
    unfold seqCountDifference
    rw [Nat.cast_sub hmono12]
    norm_num [Nat.cast_mul] at hA1up hA2lo ⊢
    nlinarith
  have hcount23 : seqCount a (2 * X) < seqCount a (3 * X) := by
    have hr : (seqCount a (2 * X) : ℝ) < seqCount a (3 * X) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hA2up hA3lo
      have hdX : 0 < d * (X : ℝ) := mul_pos hd hXr
      calc
        (seqCount a (2 * X) : ℝ) < (9 * d / 8) * (2 * (X : ℝ)) := hA2up
        _ < (7 * d / 8) * (3 * (X : ℝ)) := by nlinarith [hdX]
        _ < (seqCount a (3 * X) : ℝ) := hA3lo
    exact_mod_cast hr
  have hnext : a (seqCount a (2 * X)) ≤ 3 * X :=
    (seqCount_lt_iff ha).mp hcount23
  exact ⟨hXpos, hwindow, hnext⟩

private theorem sum_Ico_seqGap
    {a : ℕ → ℕ} (ha : StrictMono a) {p q : ℕ} (hpq : p ≤ q) :
    ∑ n ∈ Ico p q, (seqGap a n : ℝ) = (a q : ℝ) - a p := by
  refine Nat.le_induction ?_ ?_ q hpq
  · simp
  · intro m hpm ih
    rw [sum_Ico_succ_top hpm, ih]
    unfold seqGap
    rw [Nat.cast_sub (ha.monotone (Nat.le_succ m))]
    ring

/-- A positive-density sequence has a fixed bounded-gap test of mass at
least one half in every sufficiently large dyadic physical window. -/
theorem exists_bounded_gap_test
    {a : ℕ → ℕ} (ha : StrictMono a) {d : ℝ} (hd : 0 < d)
    (hdensity : Tendsto (fun X : ℕ => (seqCount a X : ℝ) / (X : ℝ))
      atTop (nhds d)) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ X : ℕ in atTop,
      (1 : ℝ) / 2 ≤ windowAvgReal (seqWindow a X)
        (fun n => if seqGap a n ≤ K then 1 else 0) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (12 / d)
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := lt_trans (by positivity : (0 : ℝ) < 12 / d) hK
    exact_mod_cast this
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [eventually_dense_dyadic_geometry ha hd hdensity] with X hX
  let p := seqCount a X
  let q := seqCount a (2 * X)
  let W := seqWindow a X
  have hpq : p ≤ q := seqCount_mono (by omega)
  have hW : W = Ico p q := seqWindow_eq_Ico_seqCount ha X
  have hsumGap : (∑ n ∈ W, (seqGap a n : ℝ)) ≤ 3 * (X : ℝ) := by
    rw [hW, sum_Ico_seqGap ha hpq]
    have hap0 : (0 : ℝ) ≤ a p := Nat.cast_nonneg _
    have haq : (a q : ℝ) ≤ 3 * (X : ℝ) := by
      exact_mod_cast hX.2.2
    linarith
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hKpos
  have hcoef : 3 / (K : ℝ) < d / 4 := by
    apply (div_lt_iff₀ hKr).mpr
    have hh := (div_lt_iff₀ hd).mp hK
    nlinarith
  have htail : (∑ n ∈ W, (seqGap a n : ℝ)) / (K : ℝ) <
      ((W.card : ℝ)) / 2 := by
    have hdiv := div_le_div_of_nonneg_right hsumGap hKr.le
    have hscaled := mul_lt_mul_of_pos_right hcoef (Nat.cast_pos.mpr hX.1)
    have hcard := hX.2.1
    change d / 2 * (X : ℝ) ≤ (W.card : ℝ) at hcard
    calc
      _ ≤ 3 * (X : ℝ) / (K : ℝ) := hdiv
      _ = (3 / (K : ℝ)) * (X : ℝ) := by ring
      _ < d / 4 * (X : ℝ) := hscaled
      _ ≤ (W.card : ℝ) / 2 := by linarith
  have hpoint (n : ℕ) :
      (1 : ℝ) ≤ (if seqGap a n ≤ K then 1 else 0) + (seqGap a n : ℝ) / K := by
    by_cases hn : seqGap a n ≤ K
    · simp only [if_pos hn]
      exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hKr.le)
    · have hn' : K < seqGap a n := Nat.lt_of_not_ge hn
      have hnR : (K : ℝ) ≤ seqGap a n := by exact_mod_cast hn'.le
      simp only [hn, if_false, zero_add]
      exact (le_div_iff₀ hKr).mpr (by simpa only [one_mul] using hnR)
  have hsumPoint : (∑ n ∈ W, (1 : ℝ)) ≤
      ∑ n ∈ W, ((if seqGap a n ≤ K then 1 else 0) + (seqGap a n : ℝ) / K) := by
    apply Finset.sum_le_sum
    intro n hn
    exact hpoint n
  simp only [Finset.sum_const, nsmul_one, Finset.sum_add_distrib,
    ← Finset.sum_div] at hsumPoint
  change (1 : ℝ) / 2 ≤
    (∑ n ∈ W, if seqGap a n ≤ K then (1 : ℝ) else 0) / (W.card : ℝ)
  have hWpos : (0 : ℝ) < W.card := by
    have hdXpos : 0 < d / 2 * (X : ℝ) := mul_pos (by positivity) (Nat.cast_pos.mpr hX.1)
    exact lt_of_lt_of_le hdXpos hX.2.1
  apply (le_div_iff₀ hWpos).mpr
  nlinarith

/-- A strictly increasing sequence of positive natural density cannot obey
the paper's calibrated complex-pattern criterion at a scale tending to
infinity.  No tail hypothesis is needed. -/
theorem not_complexPatternS_of_positive_density
    {a : ℕ → ℕ} (ha : StrictMono a) {d : ℝ} (hd : 0 < d)
    (hdensity : Tendsto (fun X : ℕ => (seqCount a X : ℝ) / (X : ℝ))
      atTop (nhds d))
    {κ : ℝ} (hκ : 0 < κ) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G) :
    ¬ ComplexPatternS a κ G ω := by
  intro hcomplex
  obtain ⟨K, hKpos, hsmall⟩ := exists_bounded_gap_test ha hd hdensity
  have hgeom := eventually_dense_dyadic_geometry ha hd hdensity
  have hne : ∀ᶠ X : ℕ in atTop, 0 < (seqWindow a X).card := by
    filter_upwards [hgeom] with X hX
    have hpos : 0 < d / 2 * (X : ℝ) :=
      mul_pos (by positivity) (Nat.cast_pos.mpr hX.1)
    exact Nat.cast_pos.mp (hpos.trans_le hX.2.1)
  have hshape : ShapeS a κ G ω 1 :=
    shapeS_of_patternS hκ hG hω hsum hcal (patternS_of_complex hcomplex) hne
  have hcap := tendsto_singletonCap_zero hG hκ (tendsto_rank_ratio hκ hG)
  have hcapK : Tendsto
      (fun X => ((Icc 1 K).card : ℝ) * singletonCap G (rank κ G) X)
      atTop (nhds 0) := by
    simpa only [mul_zero] using hcap.const_mul ((Icc 1 K).card : ℝ)
  suffices hfalse : ∀ᶠ X : ℕ in atTop, False by
    obtain ⟨X, hX⟩ := hfalse.exists
    exact hX
  filter_upwards [hshape (1 / 8) (by norm_num),
    hsmall, eventually_singleton_bound hκ hG hω hsum hcal,
    (tendsto_rank_atTop hκ hG).eventually_ge_atTop 1,
    hcapK.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 8),
    (tendsto_physicalSpan_atTop hG hκ (tendsto_rank_ratio hκ hG)).eventually_ge_atTop 1,
    hG.eventually_gt_atTop 0] with
      X hSX hsmallX hsite hL hcapSmall hspan1 hGpos
  let Ω := offsetWindow (span κ G X)
  let L := rank κ G X
  let μ := patternMass a X Ω
  let ν := model κ G ω X
  have hactual := positive_firstL_window_le ha X (span κ G X) hL
    (smallPointTest K) (fun U => (smallPointTest_bounds K U).2)
  have hprefix : windowAvgReal (seqWindow a X)
      (fun n => if seqGap a n ≤ K then 1 else 0) ≤
      windowAvgReal (seqWindow a X) (fun n => smallPointTest K (prefixSet a n L)) := by
    unfold windowAvgReal
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro n hn
    exact smallGapTest_le_prefixTest ha K n L hL
  have hmodel : shapeMean Ω ν L (smallPointTest K) ≤
      ((Icc 1 K).card : ℝ) * singletonCap G (rank κ G) X := by
    calc
      shapeMean Ω ν L (smallPointTest K) ≤
          ∑ d ∈ Icc 1 K ∩ Ω, Stopped.inclusionMass Ω ν {d} :=
        smallPoint_shapeMean_le_sum_inclusion Ω ν
          (fun U _ => CoreCalibratedMixtureMoments.law_nonneg (ω X) (hω X) _ U) L K
      _ ≤ ∑ d ∈ Icc 1 K ∩ Ω, singletonCap G (rank κ G) X := by
        apply Finset.sum_le_sum
        intro e he
        apply hsite e
        exact (Finset.mem_inter.mp he).2
      _ ≤ ((Icc 1 K).card : ℝ) * singletonCap G (rank κ G) X := by
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast card_le_card inter_subset_left
        · unfold singletonCap
          exact mul_nonneg
            (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) eulerProdLowerConst_pos.le)
            (div_nonneg (Real.log_nonneg (by exact_mod_cast hspan1)) hGpos.le)
  have hSbound := hSX (smallPointTest K)
    (fun U hU => (smallPointTest_bounds K U).1)
    (fun U hU => (smallPointTest_bounds K U).2)
  simp only [one_mul] at hSbound hactual
  change Stopped.failureMass Ω μ L + shapeMean Ω μ L (smallPointTest K) ≤
      shapeMean Ω ν L (smallPointTest K) + 1 / 8 at hSbound
  change windowAvgReal (seqWindow a X) (fun n => smallPointTest K (prefixSet a n L)) ≤
      Stopped.failureMass Ω μ L + shapeMean Ω μ L (smallPointTest K) at hactual
  have : (1 : ℝ) / 2 ≤ 1 / 4 := by
    calc
      (1 : ℝ) / 2 ≤ windowAvgReal (seqWindow a X)
          (fun n => if seqGap a n ≤ K then 1 else 0) := hsmallX
      _ ≤ windowAvgReal (seqWindow a X)
          (fun n => smallPointTest K (prefixSet a n L)) := hprefix
      _ ≤ Stopped.failureMass Ω μ L + shapeMean Ω μ L (smallPointTest K) := hactual
      _ ≤ shapeMean Ω ν L (smallPointTest K) + 1 / 8 := by linarith
      _ ≤ 1 / 4 := by linarith
  norm_num at this

end
end PrimeGapNormality.Prime.CoreGeneralPositiveDensityExclusion
