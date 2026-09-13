import PrimeGapNormality.Prime.CoreRoughWindowRestriction
import PrimeGapNormality.Prime.CoreRoughFullShapeComparison
import PrimeGapNormality.Prime.CoreRoughModelLimit
import Mathlib.Analysis.Complex.Basic

/-!
# Every deterministic asymptotic rough window

One larger arithmetic comparison, at 2*kappa, supplies all smaller stopped
tests by exact physical-window restriction. The final model is the single
actual rooted law at z(X), hence is perfectly calibrated to 1/V(z(X)).
No small-window failure limit and no change of tail depth is claimed.
-/

namespace PrimeGapNormality.Prime.CoreRoughEveryWindow

open Finset Filter CoreMovingRoughSequence CoreRoughThreshold
  CoreRoughSyntheticScale CoreRoughScaleLimits CoreRoughProfileError
  CoreRoughWindowRestriction CoreRoughFullShapeComparison CoreRoughModelLimit
  CoreSequencePatternLaw
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1000000

def logGap (Ψ : ℝ → ℝ) (X : ℕ) : ℝ := Real.log (roughGapScale (zPsi Ψ X))

def smallSpan (Ψ : ℝ → ℝ) (M : ℕ → ℕ) (X : ℕ) : ℕ :=
  ⌊((6 : ℝ) / 5) * (M X : ℝ) * roughGapScale (zPsi Ψ X)⌋₊

theorem tendsto_logGap_atTop {Ψ : ℝ → ℝ} {A : ℝ} (hSlope : HasSlopeBudget Ψ A) :
    Tendsto (logGap Ψ) atTop atTop := by
  change Tendsto (fun X : ℕ => Real.log (roughGapScale (zPsi Ψ X))) atTop atTop
  simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp
    (tendsto_roughGapScale_atTop.comp hSlope.tendsto_zPsi_atTop)

/-- The O(sqrt(log G)) hypothesis in the frozen paper implies the weaker
ratio hypothesis consumed below; its implicit constant is arbitrary. -/
theorem tendsto_rank_ratio_of_sqrt_error {Ψ : ℝ → ℝ} {A κ C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (M : ℕ → ℕ) (hC : 0 ≤ C)
    (herr : ∀ᶠ X : ℕ in atTop,
      |(M X : ℝ) - κ * logGap Ψ X| ≤ C * Real.sqrt (logGap Ψ X)) :
    Tendsto (fun X => (M X : ℝ) / logGap Ψ X) atTop (𝓝 κ) := by
  have hlim : Tendsto (fun X => C / Real.sqrt (logGap Ψ X)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_logGap_atTop hSlope))).const_mul C
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using h
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun X =>
    (dist_nonneg : 0 ≤ dist ((M X : ℝ) / logGap Ψ X) κ)) ?_ hlim
  filter_upwards [herr, (tendsto_logGap_atTop hSlope).eventually_gt_atTop 0] with X hX hlog
  have hsqrt : 0 < Real.sqrt (logGap Ψ X) := Real.sqrt_pos.2 hlog
  have hh := div_le_div_of_nonneg_right hX hlog.le
  have hleft : |(M X : ℝ) - κ * logGap Ψ X| / logGap Ψ X =
      dist ((M X : ℝ) / logGap Ψ X) κ := by
    rw [Real.dist_eq]
    calc
      |(M X : ℝ) - κ * logGap Ψ X| / logGap Ψ X =
          |((M X : ℝ) - κ * logGap Ψ X) / logGap Ψ X| := by
            rw [abs_div, abs_of_pos hlog]
      _ = |(M X : ℝ) / logGap Ψ X - κ| := by
        congr 1
        field_simp [hlog.ne']
  have hright : C * Real.sqrt (logGap Ψ X) / logGap Ψ X =
      C / Real.sqrt (logGap Ψ X) := by
    apply (div_eq_div_iff hlog.ne' hsqrt.ne').2
    calc
      C * Real.sqrt (logGap Ψ X) * Real.sqrt (logGap Ψ X) =
          C * (Real.sqrt (logGap Ψ X)) ^ 2 := by ring
      _ = C * logGap Ψ X := by rw [Real.sq_sqrt hlog.le]
  rwa [hleft, hright] at hh

theorem eventually_rank_span_fit {Ψ : ℝ → ℝ} {A κ : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hκ : 0 < κ) (M : ℕ → ℕ)
    (hM : Tendsto (fun X => (M X : ℝ) / logGap Ψ X) atTop (𝓝 κ)) :
    ∀ᶠ X : ℕ in atTop,
      M X ≤ roughProfileL (2 * κ) (zPsi Ψ X) ∧
        smallSpan Ψ M X ≤ roughProfileS (2 * κ) (zPsi Ψ X) := by
  have hupper := (tendsto_order.mp hM).2 (3 * κ / 2) (by linarith)
  filter_upwards [hupper, (tendsto_logGap_atTop hSlope).eventually_gt_atTop 0]
    with X hMX hlog
  let z := zPsi Ψ X
  let G := windowG (roughSyntheticScale z)
  have hG : roughGapScale z ≤ G :=
    (roughGapScale_le_log_synthetic_and_le z).1.trans (le_max_left _ _)
  have hlogmono : logGap Ψ X ≤ Real.log G :=
    Real.log_le_log (roughGapScale_pos z) hG
  have hceil : 2 * κ * Real.log G ≤ (roughProfileL (2 * κ) z : ℝ) := by
    have hc := Nat.le_ceil (2 * κ * Real.log G + Real.sqrt (2 * κ * Real.log G))
    change _ ≤ (roughProfileL (2 * κ) z : ℝ) at hc
    linarith [Real.sqrt_nonneg (2 * κ * Real.log G)]
  have hr : (M X : ℝ) ≤ (roughProfileL (2 * κ) z : ℝ) := by
    have hh := (div_lt_iff₀ hlog).mp hMX
    have hm := mul_le_mul_of_nonneg_left hlogmono
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ.le)
    have hκlog : 0 < κ * logGap Ψ X := mul_pos hκ hlog
    nlinarith only [hh, hm, hceil, hκlog]
  have hrN : M X ≤ roughProfileL (2 * κ) z := Nat.cast_le.mp hr
  refine ⟨hrN, ?_⟩
  unfold smallSpan roughProfileS ahlSmall_window
  apply Nat.floor_mono
  have hcoef : (0 : ℝ) ≤ 6 / 5 := by norm_num
  exact mul_le_mul (mul_le_mul_of_nonneg_left hr hcoef) hG
    (roughGapScale_pos z).le
    (mul_nonneg hcoef (Nat.cast_nonneg (roughProfileL (2 * κ) z)))

/-- A single error, independent of M, the smaller span, and the test. -/
def comparisonError (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  fullShapeError (2 * κ) Ψ X + modelMassL1 (2 * κ) (zPsi Ψ X) +
    Stopped.failureMass (offsetWindow (roughProfileS (2 * κ) (zPsi Ψ X)))
      (actualRootLaw (zPsi Ψ X) (roughProfileS (2 * κ) (zPsi Ψ X)))
      (roughProfileL (2 * κ) (zPsi Ψ X))

theorem tendsto_comparisonError_zero {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (2000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (comparisonError κ Ψ) atTop (𝓝 0) := by
  have hb : 0 < 2 * κ := by positivity
  have hs : HasSlopeBudget Ψ (1000000 * (2 * κ)) := by
    simpa only [show (1000000 : ℝ) * (2 * κ) = 2000000 * κ by ring] using hSlope
  have h1 := tendsto_fullShapeError_zero hb hs hC hreg
  have h2 := (tendsto_modelMassL1_zero hb).comp hSlope.tendsto_zPsi_atTop
  have h3 := (CoreRoughModelCosts.tendsto_actual_failureMass_zero hb).comp
    hSlope.tendsto_zPsi_atTop
  have hh := (h1.add h2).add h3
  change Tendsto (fun X : ℕ =>
    fullShapeError (2 * κ) Ψ X + modelMassL1 (2 * κ) (zPsi Ψ X) +
      Stopped.failureMass (offsetWindow (roughProfileS (2 * κ) (zPsi Ψ X)))
        (actualRootLaw (zPsi Ψ X) (roughProfileS (2 * κ) (zPsi Ψ X)))
        (roughProfileL (2 * κ) (zPsi Ψ X))) atTop (𝓝 0)
  simpa only [Function.comp_def, add_zero] using hh

def realMean (S M : ℕ) (μ : Finset ℕ → ℝ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ U ∈ (offsetWindow S).powerset, μ U * Stopped.stoppedValue M f U

theorem real_test_le (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) {M s : ℕ}
    (hM : M ≤ roughProfileL (2 * κ) (zPsi Ψ X))
    (hs : s ≤ roughProfileS (2 * κ) (zPsi Ψ X)) (f : Finset ℕ → ℝ)
    (hf : ∀ K, |f K| ≤ 1) :
    |realMean s M (patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow s)) f -
      realMean s M (actualRootLaw (zPsi Ψ X) s) f| ≤ comparisonError κ Ψ X := by
  let z := zPsi Ψ X
  let S := roughProfileS (2 * κ) z
  let L := roughProfileL (2 * κ) z
  let μ := patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow S)
  let ν := actualRootLaw z S
  let ξ := finiteRootMix (roughSyntheticScale z) S
  have hsmall := actual_small_test_le_big_shape
    (movingRoughSequence (zPsi Ψ)) X z hM hs f hf
  have htri := shapeL1_triangle (offsetWindow S) μ ξ ν L
  have hproj := shapeL1_le_massL1 (offsetWindow S) ξ ν L
  have hmass : CoreRoughFullShapeComparison.massL1 (offsetWindow S) ξ ν =
      modelMassL1 (2 * κ) z := by
    unfold CoreRoughFullShapeComparison.massL1 modelMassL1
    apply sum_congr rfl
    intro U hU
    exact abs_sub_comm _ _
  rw [hmass] at hproj
  change |realMean s M
      (patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow s)) f -
      realMean s M (actualRootLaw (zPsi Ψ X) s) f| ≤
    Stopped.shapeL1 (offsetWindow S) μ ν L +
    Stopped.failureMass (offsetWindow S) μ L + Stopped.failureMass (offsetWindow S) ν L at hsmall
  change _ ≤ (Stopped.shapeL1 (offsetWindow S) μ ξ L + Stopped.failureMass (offsetWindow S) μ L) +
    modelMassL1 (2 * κ) z + Stopped.failureMass (offsetWindow S) ν L
  linarith only [hsmall, htri, hproj]

def complexMean (S M : ℕ) (μ : Finset ℕ → ℝ) (f : Finset ℕ → ℂ) : ℂ :=
  ∑ U ∈ (offsetWindow S).powerset, (μ U : ℂ) *
    if M ≤ U.card then f (Stopped.firstL M U) else 0

theorem complexMean_re (S M : ℕ) (μ : Finset ℕ → ℝ) (f : Finset ℕ → ℂ) :
    (complexMean S M μ f).re = realMean S M μ (fun K => (f K).re) := by
  unfold complexMean realMean Stopped.stoppedValue
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro U hU
  split_ifs <;> simp

theorem complexMean_im (S M : ℕ) (μ : Finset ℕ → ℝ) (f : Finset ℕ → ℂ) :
    (complexMean S M μ f).im = realMean S M μ (fun K => (f K).im) := by
  unfold complexMean realMean Stopped.stoppedValue
  rw [Complex.im_sum]
  apply sum_congr rfl
  intro U hU
  split_ifs <;> simp

theorem complexMean_congr_on_shapes (S M : ℕ) (μ : Finset ℕ → ℝ)
    {f g : Finset ℕ → ℂ}
    (hfg : ∀ K ∈ (offsetWindow S).powerset.filter (fun K => K.card = M), f K = g K) :
    complexMean S M μ f = complexMean S M μ g := by
  unfold complexMean
  apply sum_congr rfl
  intro U hU
  by_cases hM : M ≤ U.card
  · rw [if_pos hM, if_pos hM, hfg _ (mem_filter.mpr
      ⟨mem_powerset.mpr (Stopped.firstL_subset.trans (mem_powerset.mp hU)),
        Stopped.firstL_card hM⟩)]
  · rw [if_neg hM, if_neg hM]

theorem realMean_actual_eq_prefix {a : ℕ → ℕ} (ha : StrictMono a)
    (X S : ℕ) {M : ℕ} (hM : 1 ≤ M) (f : Finset ℕ → ℝ) :
    realMean S M (patternMass a X (offsetWindow S)) f =
      (∑ n ∈ seqWindow a X,
        if a (n + M) - a n ≤ S then f (CoreSequencePattern.prefixSet a n M) else 0) /
          ((seqWindow a X).card : ℝ) := by
  have hh := firstL_test_eq_prefix_average ha X S hM f
  rw [firstL_test_eq_pushforward] at hh
  simpa only [realMean, offsetWindow, Stopped.stoppedValue] using hh

/-- Literal bounded prefix test of the original sequence, including its
physical cutoff and the original index-window normalization. -/
def prefixMean (a : ℕ → ℕ) (X S M : ℕ) (f : Finset ℕ → ℂ) : ℂ :=
  (∑ n ∈ seqWindow a X,
    if a (n + M) - a n ≤ S then f (CoreSequencePattern.prefixSet a n M) else 0) /
      (((seqWindow a X).card : ℝ) : ℂ)

theorem complexMean_actual_eq_prefix {a : ℕ → ℕ} (ha : StrictMono a)
    (X S : ℕ) {M : ℕ} (hM : 1 ≤ M) (f : Finset ℕ → ℂ) :
    complexMean S M (patternMass a X (offsetWindow S)) f = prefixMean a X S M f := by
  apply Complex.ext
  · rw [complexMean_re, realMean_actual_eq_prefix ha X S hM]
    simp only [prefixMean, Complex.div_ofReal_re, Complex.re_sum, apply_ite, Complex.zero_re]
  · rw [complexMean_im, realMean_actual_eq_prefix ha X S hM]
    simp only [prefixMean, Complex.div_ofReal_im, Complex.im_sum, apply_ite, Complex.zero_im]

theorem complex_test_le (κ : ℝ) (Ψ : ℝ → ℝ) (X : ℕ) {M s : ℕ}
    (hM : M ≤ roughProfileL (2 * κ) (zPsi Ψ X))
    (hs : s ≤ roughProfileS (2 * κ) (zPsi Ψ X)) (f : Finset ℕ → ℂ)
    (hf : ∀ K, ‖f K‖ ≤ 1) :
    ‖complexMean s M (patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow s)) f -
      complexMean s M (actualRootLaw (zPsi Ψ X) s) f‖ ≤ 2 * comparisonError κ Ψ X := by
  have hr := real_test_le κ Ψ X hM hs (fun K => (f K).re)
    (fun K => (Complex.abs_re_le_norm _).trans (hf K))
  have hi := real_test_le κ Ψ X hM hs (fun K => (f K).im)
    (fun K => (Complex.abs_im_le_norm _).trans (hf K))
  have hn := Complex.norm_le_abs_re_add_abs_im
    (complexMean s M (patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow s)) f -
      complexMean s M (actualRootLaw (zPsi Ψ X) s) f)
  rw [Complex.sub_re, Complex.sub_im, complexMean_re, complexMean_re,
    complexMean_im, complexMean_im] at hn
  linarith

/-- Literal actual first-M truncated shape comparison against the single
rooted law at z(X), uniformly over complex tests chosen after X.
No density, model error, smaller failure, or tail condition is a premise. -/
theorem eventually_complex_comparison {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (2000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (M : ℕ → ℕ)
    (hM : Tendsto (fun X => (M X : ℝ) / logGap Ψ X) atTop (𝓝 κ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ f : Finset ℕ → ℂ, (∀ K, ‖f K‖ ≤ 1) →
      ‖complexMean (smallSpan Ψ M X) (M X)
          (patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow (smallSpan Ψ M X))) f -
        complexMean (smallSpan Ψ M X) (M X)
          (actualRootLaw (zPsi Ψ X) (smallSpan Ψ M X)) f‖ < ε := by
  have he := (tendsto_order.mp (tendsto_comparisonError_zero hκ hSlope hC hreg)).2
    (ε / 2) (by positivity)
  filter_upwards [eventually_rank_span_fit hSlope hκ M hM, he] with X hfit hX
  intro f hf
  exact (complex_test_le κ Ψ X hfit.1 hfit.2 f hf).trans_lt (by linarith)

/-- The exact O(sqrt(log G)) profile stated in the frozen paper. -/
theorem eventually_complex_comparison_of_sqrt_error {Ψ dΨ : ℝ → ℝ} {κ C D : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (2000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (M : ℕ → ℕ) (hD : 0 ≤ D)
    (hM : ∀ᶠ X : ℕ in atTop, |(M X : ℝ) - κ * logGap Ψ X| ≤ D * Real.sqrt (logGap Ψ X))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ f : Finset ℕ → ℂ, (∀ K, ‖f K‖ ≤ 1) →
      ‖complexMean (smallSpan Ψ M X) (M X)
          (patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow (smallSpan Ψ M X))) f -
        complexMean (smallSpan Ψ M X) (M X)
          (actualRootLaw (zPsi Ψ X) (smallSpan Ψ M X)) f‖ < ε :=
  eventually_complex_comparison hκ hSlope hC hreg M
    (tendsto_rank_ratio_of_sqrt_error hSlope M hD hM) hε

theorem eventually_complex_comparison_on_shapes {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (2000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (M : ℕ → ℕ)
    (hM : Tendsto (fun X => (M X : ℝ) / logGap Ψ X) atTop (𝓝 κ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ f : Finset ℕ → ℂ,
      (∀ K ∈ (offsetWindow (smallSpan Ψ M X)).powerset.filter (fun K => K.card = M X),
        ‖f K‖ ≤ 1) →
      ‖complexMean (smallSpan Ψ M X) (M X)
          (patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow (smallSpan Ψ M X))) f -
        complexMean (smallSpan Ψ M X) (M X)
          (actualRootLaw (zPsi Ψ X) (smallSpan Ψ M X)) f‖ < ε := by
  filter_upwards [eventually_complex_comparison hκ hSlope hC hreg M hM hε] with X hX
  intro f hf
  let shapes := (offsetWindow (smallSpan Ψ M X)).powerset.filter (fun K => K.card = M X)
  let g := fun K => if K ∈ shapes then f K else 0
  have hg : ∀ K, ‖g K‖ ≤ 1 := by
    intro K
    dsimp only [g]
    split_ifs with hK
    · exact hf K hK
    · simp
  have heq (μ : Finset ℕ → ℝ) :
      complexMean (smallSpan Ψ M X) (M X) μ f =
        complexMean (smallSpan Ψ M X) (M X) μ g :=
    complexMean_congr_on_shapes _ _ μ (fun K hK => by
      exact (if_pos (show K ∈ shapes from hK)).symm)
  have hh := hX g hg
  rw [← heq, ← heq] at hh
  exact hh

theorem eventually_rank_pos {Ψ : ℝ → ℝ} {A κ : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hκ : 0 < κ) (M : ℕ → ℕ)
    (hM : Tendsto (fun X => (M X : ℝ) / logGap Ψ X) atTop (𝓝 κ)) :
    ∀ᶠ X : ℕ in atTop, 1 ≤ M X := by
  filter_upwards [(tendsto_order.mp hM).1 (κ / 2) (by linarith),
    (tendsto_logGap_atTop hSlope).eventually_gt_atTop 0] with X hr hlog
  have hh := (lt_div_iff₀ hlog).mp hr
  have hp : (0 : ℝ) < M X := (mul_pos (by positivity : 0 < κ / 2) hlog).trans hh
  have hn := Nat.cast_pos.mp hp
  omega

/-- Every-window (S), now written as the literal actual prefix average.
The model is Dirac at zPsi Ψ X; the exact physical span uses Graw, not Gsyn.
The test is bounded only on the relevant successful M-shapes. -/
theorem eventually_prefix_comparison {Ψ dΨ : ℝ → ℝ} {κ C : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (2000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (M : ℕ → ℕ)
    (hM : Tendsto (fun X => (M X : ℝ) / logGap Ψ X) atTop (𝓝 κ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ f : Finset ℕ → ℂ,
      (∀ K ∈ (offsetWindow (smallSpan Ψ M X)).powerset.filter (fun K => K.card = M X),
        ‖f K‖ ≤ 1) →
      ‖prefixMean (movingRoughSequence (zPsi Ψ)) X (smallSpan Ψ M X) (M X) f -
        complexMean (smallSpan Ψ M X) (M X)
          (actualRootLaw (zPsi Ψ X) (smallSpan Ψ M X)) f‖ < ε := by
  filter_upwards [eventually_complex_comparison_on_shapes hκ hSlope hC hreg M hM hε,
    eventually_rank_pos hSlope hκ M hM] with X hX hpos
  intro f hf
  have hh := hX f hf
  rw [complexMean_actual_eq_prefix
    (movingRoughSequence_strictMono hSlope.eventually_zPsi_lt) X _ hpos] at hh
  exact hh

/-- The frozen paper's O(sqrt(log Graw)) case, with the same literal
complex prefix average and no additional model/distribution hypotheses. -/
theorem eventually_prefix_comparison_of_sqrt_error {Ψ dΨ : ℝ → ℝ} {κ C D : ℝ}
    (hκ : 0 < κ) (hSlope : HasSlopeBudget Ψ (2000000 * κ)) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (M : ℕ → ℕ) (hD : 0 ≤ D)
    (hM : ∀ᶠ X : ℕ in atTop, |(M X : ℝ) - κ * logGap Ψ X| ≤ D * Real.sqrt (logGap Ψ X))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ f : Finset ℕ → ℂ,
      (∀ K ∈ (offsetWindow (smallSpan Ψ M X)).powerset.filter (fun K => K.card = M X),
        ‖f K‖ ≤ 1) →
      ‖prefixMean (movingRoughSequence (zPsi Ψ)) X (smallSpan Ψ M X) (M X) f -
        complexMean (smallSpan Ψ M X) (M X)
          (actualRootLaw (zPsi Ψ X) (smallSpan Ψ M X)) f‖ < ε :=
  eventually_prefix_comparison hκ hSlope hC hreg M
    (tendsto_rank_ratio_of_sqrt_error hSlope M hD hM) hε

/-- Dirac at the actual cutoff has exact support calibration to Graw. -/
theorem exact_dirac_calibration (Ψ : ℝ → ℝ) (X : ℕ) :
    (eulerProdNat (zPsi Ψ X))⁻¹ / roughGapScale (zPsi Ψ X) = 1 := by
  change roughGapScale (zPsi Ψ X) / roughGapScale (zPsi Ψ X) = 1
  exact div_self (roughGapScale_pos _).ne'

end
end PrimeGapNormality.Prime.CoreRoughEveryWindow
