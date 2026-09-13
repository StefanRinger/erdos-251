import PrimeGapNormality.Prime.CoreGeneralScaledGapST

/-!
# Scaled integer gap observables under positive arbitrary-mixture S/T

ShapeS is used one-sided, with its actual comparison factor c. No complex
S conclusion is inferred. The original rank, physical span and n+M tail
are unchanged. The existing true calibrated model supplies the reference.
Any c>0 is allowed, in particular the paper's c≥1.
-/

namespace PrimeGapNormality.Prime.CoreGeneralScaledGapPositiveST
open Filter Finset MeasureTheory CoreCyclic CoreIntegerGapObservable CoreIntegerGapInsertion
open CoreGeneralSequenceST CoreGeneralModelReference CoreSequencePattern CoreSequencePatternLaw
  CoreSequenceWindowGrowthFromS CoreSequenceSubexponentialGrowth CoreSequenceSTMeanTail
  CoreCalibratedMixtureFiniteSupport CoreCalibratedMixtureProfile CoreGeneralScaledGapST
open scoped Classical Topology NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
abbrev Circle := AddCircle (1 : ℝ)

/-- The positive arithmetic comparison supplies convergence, not a new
growth premise in its rounded consumers. -/
theorem gap_growth {a : ℕ → ℕ} (ha : StrictMono a) {κ c : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G)
    (hS : ShapeS a κ G ω c) (hT : MeanGapTailT a (localTailBase κ) G) :
    HasSubexponentialGrowth (fun n => (seqGap a n : ℝ)) :=
  sequenceGap_hasSubexponentialGrowth ha
    (windowCountToInfinity ha hκ hc hG hω hsum hcal hS
      (meanGapTail_eventually_nonempty hT))

theorem positive_comparison
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {κ : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G)
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) (hf : ∀ x, 0 ≤ f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop,
      coreDigitalWindowAverage (orbit B hk r F a) f (seqCount a X) (CoreSequenceResiduePassage.seqCountDifference a X) ≤
        c * CoreGeneralScaledGapModelReference.modelMean B hk r F κ G ω X f + ε := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hcount := windowCountToInfinity ha hκp hc hG hω hsum hcal hS
    (meanGapTail_eventually_nonempty hT)
  have ht := tail_test_tendsto_zero ha hcount hB hk r F hC hF hκ
    (gapTailT ha hκp hc hG hω hsum hcal hS hT) f hK
  let D : ℝ := ‖f‖ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hfD (x : Circle) : f x ≤ D := (f.apply_le_norm x).trans (le_add_of_nonneg_right zero_le_one)
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [hS (ε / (2 * D)) (by positivity), ht.eventually_le_const hε2,
    (tendsto_rank_atTop hκp hG).eventually_ge_atTop 1,
    CoreCalibratedAuxiliaryFrame.eventually_profile_data hG hκp (tendsto_rank_ratio hκp hG) hω hsum hcal]
    with X hSX htail hL hdata
  let L := rank κ G X
  let S := span κ G X
  let test := CoreRoundedModelFinite.actualTest B hk r F L f
  have hshape := hSX (fun U => test U / D)
    (fun U _ => div_nonneg (hf _) hD.le) (fun U _ => (div_le_one hD).2 (hfD _))
  rw [shapeMean_div, shapeMean_div] at hshape
  have hm := mul_le_mul_of_nonneg_left hshape hD.le
  have he (x : ℝ) : D * (x / D) = x := by field_simp [hD.ne']
  have heps : D * (ε / (2 * D)) = ε / 2 := by field_simp [hD.ne'] <;> ring
  have hs' : D * Stopped.failureMass (offsetWindow S) (patternMass a X (offsetWindow S)) L +
      shapeMean (offsetWindow S) (patternMass a X (offsetWindow S)) L test ≤
      c * shapeMean (offsetWindow S) (model κ G ω X) L test + ε / 2 := by
    have hscale_eq (x : ℝ) : D * (c * (x / D)) = c * x := by
      rw [mul_left_comm D c, he]
    simpa only [mul_add, he, hscale_eq, heps] using hm
  obtain ⟨N, hz, hsumN⟩ := hdata.2.2.2
  have hemodel : shapeMean (offsetWindow S) (model κ G ω X) L test =
      CoreGeneralScaledGapModelReference.modelMean B hk r F κ G ω X f :=
    shapeMean_eq_modelMean B S L hk r F (ω X) hz f
  rw [hemodel] at hs'
  have hfinite := positive_firstL_window_le ha X S hL
    (fun U => f (actualFiniteObservablePhase B hk r F L U : Circle)) (fun U => hfD _)
  have htrunc : windowAvgReal (seqWindow a X) (fun n =>
      f (observableTrunc B hk r F (seqGap a) n L : Circle)) ≤
      c * CoreGeneralScaledGapModelReference.modelMean B hk r F κ G ω X f + ε / 2 := by
    apply le_trans _ hs'
    simpa only [L, prefix_phase ha, shapeMean, test, CoreRoundedModelFinite.actualTest, offsetWindow] using hfinite
  have htriangle : windowAvgReal (seqWindow a X) (fun n => f (orbit B hk r F a n)) ≤
      windowAvgReal (seqWindow a X) (fun n => f (observableTrunc B hk r F (seqGap a) n L : Circle)) +
        windowAvgReal (seqWindow a X) (fun n =>
          |f (orbit B hk r F a n) - f (observableTrunc B hk r F (seqGap a) n L : Circle)|) := by
    unfold windowAvgReal
    rw [← add_div, ← sum_add_distrib]
    have hpoint : ∀ n ∈ seqWindow a X,
        f (orbit B hk r F a n) ≤
          f (observableTrunc B hk r F (seqGap a) n L : Circle) +
            |f (orbit B hk r F a n) -
              f (observableTrunc B hk r F (seqGap a) n L : Circle)| := by
      intro n hn
      linarith [le_abs_self
        (f (orbit B hk r F a n) -
          f (observableTrunc B hk r F (seqGap a) n L : Circle))]
    exact div_le_div_of_nonneg_right (sum_le_sum hpoint) (Nat.cast_nonneg _)
  rw [← CoreSequenceSTConsumer.windowAvgReal_eq_coreDigitalWindowAverage ha]
  linarith

theorem subsequenceReference
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {exponent κ : ℝ} (hexp : 0 < exponent) (hexp1 : exponent ≤ 1) (b : Fin k → ℤ) (hb : b ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent b)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    CoreResidueDigitalReference.SubsequenceReferenceBounds (orbit B hk r F a)
      (fun X => seqCount a X) (CoreSequenceResiduePassage.seqCountDifference a) := by
  intro χ hχ
  have hcal' : UniformCalibration (fun X y => ω (χ X) y) (fun X => G (χ X)) :=
    fun ε hε => hχ.tendsto_atTop.eventually (hcal ε hε)
  have hGχ : Tendsto (fun X => G (χ X)) atTop atTop := by
    simpa only [Function.comp_def] using hG.comp hχ.tendsto_atTop
  obtain ⟨ψ, hψ, σ, hfin, hac, hmass, hmodel⟩ :=
    CoreGeneralScaledGapModelReference.exists_reference_subsequence hB hk r F hexp hexp1 b hb hscale hκ
      hGχ (fun X y => hω (χ X) y) (fun X => hsum (χ X)) hcal'
  have hχψ : Tendsto (fun n => χ (ψ n)) atTop atTop := by
    simpa only [Function.comp_def] using hχ.tendsto_atTop.comp hψ.tendsto_atTop
  refine ⟨ψ, hψ, σ, hfin, hac, c * CoreCalibratedModelFinite.modelConstant,
    mul_nonneg hc.le CoreCalibratedModelFinite.modelConstant_nonneg, ?_⟩
  intro f K hK hf ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hδ : 0 < ε / (2 * c) := by positivity
  filter_upwards [hmodel f K hK hf (ε / (2 * c)) hδ,
    hχψ.eventually
      (positive_comparison ha hB hk r F hC hF hκ hc hG hω hsum hcal hS hT f hK hf hε2)] with n hm hp
  change CoreGeneralScaledGapModelReference.modelMean B hk r F κ G ω (χ (ψ n)) f ≤
    CoreCalibratedModelFinite.modelConstant * (∫ x, f x ∂σ) + ε / (2 * c) at hm
  have hscaled := mul_le_mul_of_nonneg_left hm hc.le
  have heps : c * (ε / (2 * c)) = ε / 2 := by field_simp [hc.ne'] <;> ring
  calc
    _ ≤ c * CoreGeneralScaledGapModelReference.modelMean B hk r F κ G ω (χ (ψ n)) f + ε / 2 := hp
    _ ≤ c * (CoreCalibratedModelFinite.modelConstant * (∫ x, f x ∂σ) +
        ε / (2 * c)) + ε / 2 := _root_.add_le_add hscaled le_rfl
    _ = _ := by rw [mul_add, heps]; ring

/-- Genuine arbitrary-mixture S/T common-clock Weyl theorem for the
actual full observable series. -/
theorem observableFullSeries_weyl
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {exponent κ : ℝ} (hexp : 0 < exponent) (hexp1 : exponent ≤ 1) (b : Fin k → ℤ) (hb : b ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent b)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    weylCriterion (B ^ k) (observableFullSeries B hk r F (seqGap a)) := by
  have hκp : 0 < κ := (div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))).trans_le hκ
  have hcount := windowCountToInfinity ha hκp hc hG hω hsum hcal hS
    (meanGapTail_eventually_nonempty hT)
  have hgrowth := sequenceGap_hasSubexponentialGrowth ha hcount
  have hgap : ∀ n, 1 ≤ seqGap a n := by
    intro n
    unfold seqGap
    exact Nat.one_le_iff_ne_zero.2 (Nat.sub_ne_zero_of_lt (ha (Nat.lt_succ_self n)))
  have href := subsequenceReference ha hB hk r F hC hF hexp hexp1 b hb hscale hκ hc hG hω hsum hcal hS hT
  have hrec : ∀ n, orbit B hk r F a (n + k) = B ^ k • orbit B hk r F a n :=
    fun n => observableSeriesCircle_add_period hB hk r F hgap hgrowth hC hF n
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  intro z hz
  have hchar := CoreSequenceResiduePassage.residue_character_cesaro_of_subsequence_reference
    ha hcount hclock hk (r := 0) hk (orbit B hk r F a) hrec href hz
  unfold CesaroMeanVanishing at hchar
  apply hchar.congr'
  exact Eventually.of_forall fun N => by
    apply congrArg (fun v : ℂ => v / (N : ℂ))
    apply sum_congr rfl
    intro q hq
    have hp := circleOrbit_of_add_period hrec 0 q
    have hp' : orbit B hk r F a (k * q) =
        (B ^ k) ^ q • (observableFullSeries B hk r F (seqGap a) : Circle) := by
      simpa only [Nat.zero_add, orbit, observableFullSeries] using hp
    change fourier z (orbit B hk r F a (q * k + 0)) = _
    rw [show q * k + 0 = k * q by simp only [Nat.add_zero, Nat.mul_comm], hp']
    rw [← AddCircle.coe_nsmul, fourier_coe_apply]
    simp only [nsmul_eq_mul, Nat.cast_pow, e, Complex.ofReal_one, div_one,
      Complex.ofReal_mul, Complex.ofReal_intCast]
    congr 1
    ring

/-- Literal normality both in the period clock and in the digit base. -/
theorem observableFullSeries_normal
    {a : ℕ → ℕ} (ha : StrictMono a) {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {exponent κ : ℝ} (hexp : 0 < exponent) (hexp1 : exponent ≤ 1) (b : Fin k → ℤ) (hb : b ≠ 0)
    (hscale : CoreScaledGapModelReference.CompactScaling F exponent b)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) {c : ℝ} (hc : 0 < c) {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y) (hsum : ∀ X, ∑' y, ω X y = 1)
    (hcal : UniformCalibration ω G) (hS : ShapeS a κ G ω c)
    (hT : MeanGapTailT a (localTailBase κ) G) :
    PrimeGapNormality.BFree.IsNormal (B ^ k) (observableFullSeries B hk r F (seqGap a)) ∧
      PrimeGapNormality.BFree.IsNormal B (observableFullSeries B hk r F (seqGap a)) := by
  have hW := observableFullSeries_weyl ha hB hk r F hC hF hexp hexp1 b hb hscale hκ hc hG hω hsum hcal hS hT
  have hclock : 2 ≤ B ^ k := by
    rw [show k = k - 1 + 1 by omega, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  exact ⟨CoreWeylNormality.isNormal_of_weyl hclock hW,
    CoreWeylNormality.isNormal_of_weyl hB (weylCriterion_of_pow hB hk hW)⟩

end
end PrimeGapNormality.Prime.CoreGeneralScaledGapPositiveST
