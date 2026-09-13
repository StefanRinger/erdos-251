import PrimeGapNormality.Prime.CoreCalibratedFactorialRectangle
import PrimeGapNormality.Prime.CoreSelbergRectanglePrecision
import PrimeGapNormality.Prime.CoreCalibratedFrameProbability

/-!
# Sharp rectangles for the actual calibrated auxiliary mixture

The falling-factorial layer estimate is combined with the sharper actual
Selberg candidate cap.  The only scalar input is derived here from the
literal cutoff calibration and the proved Euler product bounds:

`lateRetention S y * G / log G <= 20/9`.

Consequently each rectangle coordinate costs strictly less than eight.
The cutoff weights, the original residue choice, all original cardinality
layers and the completed missing atom remain literal.  In particular the
rank map may vary with the profile index; it is only required to be
injective and valid at that index.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedRectanglePrecision

open Finset Filter MeasureTheory
open CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
  CoreCalibratedMixtureMoments CoreCalibratedAuxiliaryFrame
  CoreCalibratedFrameLimit CoreCalibratedFrameProbability
  CoreActualFrameRectangles CoreActualFrameRectangleLimit
open scoped Classical Topology ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-! ## The sharp retention scale -/

private theorem tendsto_log_log_div_self_atTop :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
  simpa only [pow_one, one_mul, add_zero] using
    Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)

/-- The physical presieve logarithm has its sharp leading coefficient
one.  This is kept public because it is the scalar normalization behind
the displayed rectangle constant. -/
theorem eventually_log_physicalSpan_div_log_le
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ)) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (physicalSpan G M X : ℝ) / Real.log (G X) ≤ 11 / 10 := by
  let c : ℝ := (6 / 5 : ℝ) * (κ + 1)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hlogG : Tendsto (fun X => Real.log (G X)) atTop atTop :=
    Real.tendsto_log_atTop.comp hG
  have hconst : Tendsto (fun X => Real.log c / Real.log (G X)) atTop (nhds 0) := by
    have hi := tendsto_inv_atTop_zero.comp hlogG
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      hi.const_mul (Real.log c)
  have hloglog :
      Tendsto (fun X => Real.log (Real.log (G X)) / Real.log (G X))
        atTop (nhds 0) := by
    exact (tendsto_log_log_div_self_atTop.comp hlogG).congr'
      (Eventually.of_forall fun X => by simp only [Function.comp_apply])
  have hsmall : Tendsto (fun X =>
      Real.log c / Real.log (G X) +
        Real.log (Real.log (G X)) / Real.log (G X)) atTop (nhds 0) := by
    simpa only [zero_add] using hconst.add hloglog
  filter_upwards [
    (tendsto_order.mp hM).2 (κ + 1) (by linarith),
    hG.eventually_gt_atTop 1,
    hsmall.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 10),
    (tendsto_physicalSpan_atTop hG hκ hM).eventually_ge_atTop 1]
      with X hMr hG1 hsmallX hS1
  have hg : 0 < G X := zero_lt_one.trans hG1
  have hlg : 0 < Real.log (G X) := Real.log_pos hG1
  have hMupper : (M X : ℝ) ≤ (κ + 1) * Real.log (G X) := by
    exact ((div_lt_iff₀ hlg).mp hMr).le
  have hspan : (physicalSpan G M X : ℝ) ≤
      c * Real.log (G X) * G X := by
    have hfloor : (physicalSpan G M X : ℝ) ≤
        (6 / 5 : ℝ) * (M X : ℝ) * G X := Nat.floor_le (by positivity)
    calc
      (physicalSpan G M X : ℝ) ≤ (6 / 5 : ℝ) * (M X : ℝ) * G X := hfloor
      _ ≤ (6 / 5 : ℝ) * ((κ + 1) * Real.log (G X)) * G X :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMupper (by norm_num)) hg.le
      _ = c * Real.log (G X) * G X := by dsimp only [c]; ring
  have hSpos : (0 : ℝ) < physicalSpan G M X := Nat.cast_pos.mpr hS1
  have hlogbound := Real.log_le_log hSpos hspan
  have hformula : Real.log (c * Real.log (G X) * G X) =
      Real.log c + Real.log (Real.log (G X)) + Real.log (G X) := by
    rw [Real.log_mul (mul_pos hc hlg).ne' hg.ne',
      Real.log_mul hc.ne' hlg.ne']
  rw [hformula] at hlogbound
  have hdiv := div_le_div_of_nonneg_right hlogbound hlg.le
  calc
    Real.log (physicalSpan G M X : ℝ) / Real.log (G X) ≤
        (Real.log c + Real.log (Real.log (G X)) + Real.log (G X)) /
          Real.log (G X) := hdiv
    _ = 1 + (Real.log c / Real.log (G X) +
        Real.log (Real.log (G X)) / Real.log (G X)) := by
      field_simp [hlg.ne'] <;> ring
    _ ≤ 11 / 10 := by linarith

/-- On every supported calibrated cutoff, the genuine late-retention
factor has the sharp scale needed by the factorial rectangle argument. -/
theorem eventually_scaled_retention_le_twenty_ninths
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop,
      1 < G X ∧ 16 ≤ physicalSpan G M X ∧
      ⌊G X⌋₊ ≤ physicalSpan G M X ∧
      ∀ y : ℕ, 0 < w X y →
        physicalSpan G M X ≤ y ∧
        lateRetention (physicalSpan G M X) y * G X / Real.log (G X) ≤ 20 / 9 := by
  have hS := tendsto_physicalSpan_atTop hG hκ hM
  filter_upwards [
    CoreCalibratedFrameLimit.eventually_profile_log_ratio hG hκ hM,
    eventually_log_physicalSpan_div_log_le hG hκ hM,
    hS.eventually eventually_half_lt_eulerProdNat_mul_log,
    eventually_support_above_span hG hκ hM hcal,
    hcal (1 / 100) (by norm_num)]
      with X hprofile hlogratio hEuler hsupport hcalX
  refine ⟨hprofile.1, hprofile.2.1, hprofile.2.2.1, ?_⟩
  intro y hy
  let S := physicalSpan G M X
  have hS2 : 2 ≤ S := by dsimp only [S]; omega
  have hSy : S ≤ y := (hsupport y hy).le
  have hg : 0 < G X := zero_lt_one.trans hprofile.1
  have hlg : 0 < Real.log (G X) := Real.log_pos hprofile.1
  have hlS : 0 < Real.log (S : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < S by omega))
  have hVS : 0 < eulerProdNat S := eulerProdNat_pos S
  change (1 / 2 : ℝ) < eulerProdNat S * Real.log (S : ℝ) at hEuler
  have hinv : 1 / eulerProdNat S ≤ 2 * Real.log (S : ℝ) := by
    apply (div_le_iff₀ hVS).2
    nlinarith
  have hVy := eulerProd_le_calibrated_fraction hg y (hcalX y hy)
  have hret : lateRetention S y ≤
      (200 / 99 : ℝ) * Real.log (S : ℝ) / G X := by
    calc
      lateRetention S y ≤ eulerProdNat y / eulerProdNat S :=
        rootedEulerProdNat_le_div hSy hS2
      _ = eulerProdNat y * (1 / eulerProdNat S) := by ring
      _ ≤ ((100 / 99 : ℝ) / G X) * (2 * Real.log (S : ℝ)) :=
        mul_le_mul hVy hinv (by positivity) (by positivity)
      _ = (200 / 99 : ℝ) * Real.log (S : ℝ) / G X := by ring
  refine ⟨hSy, ?_⟩
  calc
    lateRetention S y * G X / Real.log (G X) ≤
        ((200 / 99 : ℝ) * Real.log (S : ℝ) / G X) * G X /
          Real.log (G X) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hret hg.le) hlg.le
    _ = (200 / 99 : ℝ) *
        (Real.log (S : ℝ) / Real.log (G X)) := by
      field_simp [hg.ne', hlg.ne'] <;> ring
    _ ≤ (200 / 99 : ℝ) * (11 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_left (by simpa only [S] using hlogratio) (by norm_num)
    _ = 20 / 9 := by norm_num

/-! ## The finite sharp rectangle -/

def precisionRectangleError
    (G : ℕ → ℝ) (M : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (X : ℕ) : ℝ :=
  8 * singletonCap G M X +
    missing (w X) (physicalSpan G M X) (M X)

theorem tendsto_precisionRectangleError_zero
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G) :
    Tendsto (precisionRectangleError G M w) atTop (nhds 0) := by
  have hs := (tendsto_singletonCap_zero hG hκ hM).const_mul 8
  have hm := tendsto_missing_zero hG hκ hM hw hsum hcal
  change Tendsto (fun X =>
    8 * singletonCap G M X + missing (w X) (physicalSpan G M X) (M X))
      atTop (nhds 0)
  simpa only [mul_zero, zero_add] using hs.add hm

/-- The actual one-cutoff auxiliary law obeys the sharp coordinatewise
constant.  The error `8 * lateRetention` is the genuine high-cardinality
layer mass, not an upper-count surrogate. -/
theorem eventually_layer_rectangle_precision
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G)
    (r : ℕ) (a b : Fin r → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᶠ X : ℕ in atTop, ∀ y, 0 < w X y → ∀ q : Fin r → ℕ,
      Function.Injective q → (∀ i, q i + 1 < M X) →
      (∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
        coreAuxiliaryLayerFrameMass (physicalSpan G M X) y (M X) F *
          rectangleTest q (G X) a b F) ≤
        (8 : ℝ) ^ r * ∏ i, (b i - a i) +
          8 * lateRetention (physicalSpan G M X) y := by
  have hcaps : ∀ᶠ x : ℝ in atTop, ∀ i : Fin r,
      1 < x ∧ 1 ≤ rectangleRadius (b i - a i) x ∧
      rectangleRadius (b i - a i) x ≤ intervalLength (x * (b i - a i)) ∧
      rectangleRadius (b i - a i) x ≤ ⌊x⌋₊ ∧
      (candidateCap x (a i) (b i) (rectangleRadius (b i - a i) x) : ℝ) ≤
        3 * x / Real.log x * (b i - a i) :=
    Filter.eventually_all.2 fun i =>
      CoreSelbergRectanglePrecision.eventually_candidateCap_le_three (hab i)
  filter_upwards [hG.eventually hcaps,
    eventually_scaled_retention_le_twenty_ninths hG hκ hM hcal,
    eventually_rank_pos hG hκ hM] with X hcap hscale hM1
  intro y hy q hq hvalid
  let S := physicalSpan G M X
  let J : Finset ℕ := rankSet q
  let I : ℕ → Set ℝ := fun j =>
    Set.Ioo (G X * endpoints q a j) (G X * endpoints q b j)
  let K : ℕ → ℕ := fun j =>
    candidateCap (G X) (endpoints q a j) (endpoints q b j)
      (rectangleRadius (endpoints q b j - endpoints q a j) (G X))
  have hg : 0 < G X := zero_lt_one.trans hscale.1
  have hS2 : 2 ≤ S := by dsimp only [S]; omega
  have hSy : S ≤ y := (hscale.2.2.2 y hy).1
  have hJ : ∀ j ∈ J, j + 1 < M X := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    exact hvalid i
  have hcapRaw : ∀ σ : ResidueChoice S, ∀ j ∈ J, ∀ z : ℝ,
      (CoreUniformGapRectangles.translatedCandidates
        (presieveSurvivors S σ) (I j) z).card ≤ K j := by
    intro σ j hj z
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    dsimp only [I, K]
    simp only [endpoints_apply hq]
    apply translated_candidate_cap _ _ (hcap i).2.1 (hcap i).2.2.1
      (presieve_avoids σ ((hcap i).2.2.2.1.trans hscale.2.2.1)) z
    intro n hn
    exact (Finset.mem_Icc.mp (corePresieveSurvivors_subset_Icc S σ hn)).1
  have hfactor :=
    CoreCalibratedFactorialRectangle.auxiliaryLayer_factorial_rectangle_le
      S y (M X) J I K hS2 hSy hM1 hJ hcapRaw
  have htest :
      (fun F : Finset ℕ =>
        if ∀ j ∈ J, (subsetGap F j : ℝ) ∈ I j then 1 else 0) =
        rectangleTest q (G X) a b := by
    funext F
    unfold rectangleTest
    apply if_congr
    · constructor
      · intro hh i
        have hi : q i ∈ J := by
          dsimp only [J, rankSet]
          exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
        have hz := hh (q i) hi
        dsimp only [I] at hz
        simpa only [endpoints_apply hq, frame, Set.mem_Ioo,
          lt_div_iff₀ hg, div_lt_iff₀ hg, mul_comm] using hz
      · intro hh j hj
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
        have hz := hh i
        dsimp only [I]
        simpa only [endpoints_apply hq, frame, Set.mem_Ioo,
          lt_div_iff₀ hg, div_lt_iff₀ hg, mul_comm] using hz
    · rfl
    · rfl
  have hsum_eq := congrArg
    (fun t : Finset ℕ → ℝ => ∑ F ∈ (offsetWindow S).powerset,
      coreAuxiliaryLayerFrameMass S y (M X) F * t F) htest
  have hfactor' :
      (∑ F ∈ (offsetWindow S).powerset,
        coreAuxiliaryLayerFrameMass S y (M X) F * rectangleTest q (G X) a b F) ≤
      ((8 * lateRetention S y / 7) ^ J.card) * ∏ j ∈ J, (K j : ℝ) +
        8 * lateRetention S y := by
    calc
      _ = ∑ F ∈ (offsetWindow S).powerset,
          coreAuxiliaryLayerFrameMass S y (M X) F *
            (if ∀ j ∈ J, (subsetGap F j : ℝ) ∈ I j then 1 else 0) := hsum_eq.symm
      _ ≤ _ := by
        convert hfactor using 1
        apply Finset.sum_congr rfl
        intro F hF
        apply congrArg (fun t : ℝ => coreAuxiliaryLayerFrameMass S y (M X) F * t)
        split_ifs <;> rfl
  have hfactor := hfactor'
  have hcardJ : J.card = r := by
    dsimp only [J, rankSet]
    rw [card_image_of_injective _ hq, card_univ, Fintype.card_fin]
  have hprodK : (∏ j ∈ J, (K j : ℝ)) =
      ∏ i : Fin r,
        (candidateCap (G X) (a i) (b i)
          (rectangleRadius (b i - a i) (G X)) : ℝ) := by
    dsimp only [J, rankSet]
    rw [prod_image]
    · simp only [K, endpoints_apply hq]
    · intro i hi j hj hij
      exact hq hij
  have hcoord (i : Fin r) :
      (8 * lateRetention S y / 7) *
          (candidateCap (G X) (a i) (b i)
            (rectangleRadius (b i - a i) (G X)) : ℝ) ≤
        8 * (b i - a i) := by
    have htheta := (hscale.2.2.2 y hy).2
    have htheta0 : 0 ≤ lateRetention S y := (rootedEulerProdNat_pos hS2).le
    have hwidth0 : 0 ≤ b i - a i := (sub_pos.mpr (hab i)).le
    calc
      (8 * lateRetention S y / 7) *
          (candidateCap (G X) (a i) (b i)
            (rectangleRadius (b i - a i) (G X)) : ℝ) ≤
        (8 * lateRetention S y / 7) *
          (3 * G X / Real.log (G X) * (b i - a i)) :=
        mul_le_mul_of_nonneg_left (hcap i).2.2.2.2 (by positivity)
      _ = ((24 / 7 : ℝ) *
          (lateRetention S y * G X / Real.log (G X))) * (b i - a i) := by ring
      _ ≤ ((24 / 7 : ℝ) * (20 / 9 : ℝ)) * (b i - a i) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htheta (by norm_num)) hwidth0
      _ ≤ 8 * (b i - a i) := by nlinarith
  have hcoefficient0 : (0 : ℝ) ≤ 8 * lateRetention S y / 7 :=
    div_nonneg (mul_nonneg (by norm_num) (rootedEulerProdNat_pos hS2).le) (by norm_num)
  have hp := Finset.prod_le_prod (s := (univ : Finset (Fin r)))
    (fun i hi => mul_nonneg hcoefficient0
      (Nat.cast_nonneg (candidateCap (G X) (a i) (b i)
        (rectangleRadius (b i - a i) (G X)))))
    (fun i hi => hcoord i)
  have hmain :
      ((8 * lateRetention S y / 7) ^ J.card) * ∏ j ∈ J, (K j : ℝ) ≤
        (8 : ℝ) ^ r * ∏ i, (b i - a i) := by
    rw [hcardJ, hprodK]
    simpa only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
      using hp
  exact hfactor.trans (_root_.add_le_add hmain le_rfl)

/-- The completed actual calibrated mixture has the paper's finite
`8^r` rectangle coefficient.  Both the cutoff average and the missing
mass are evaluated exactly. -/
theorem eventually_completed_rectangle_precision
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G)
    (r : ℕ) (a b : Fin r → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᶠ X : ℕ in atTop, ∀ q : Fin r → ℕ, Function.Injective q →
      (∀ i, q i + 1 < M X) →
      (∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
        completed (w X) (physicalSpan G M X) (M X) F *
          rectangleTest q (G X) a b F) ≤
        (8 : ℝ) ^ r * ∏ i, (b i - a i) +
          precisionRectangleError G M w X := by
  filter_upwards [eventually_layer_rectangle_precision hG hκ hM hcal r a b hab,
    eventually_profile_data hG hκ hM hw hsum hcal,
    eventually_nonzero_support_retention_le hG hκ hM hw hcal]
      with X hlayer hdata hret
  obtain ⟨N, hzero, hsumN⟩ := hdata.2.2.2
  intro q hq hvalid
  rw [completed_expectation, expectation_eq_finite (w X) _ _ hzero]
  let C : ℝ := (8 : ℝ) ^ r * ∏ i, (b i - a i)
  have hmain :
      (∑ y ∈ range N, w X y *
        (∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
          coreAuxiliaryLayerFrameMass (physicalSpan G M X) y (M X) F *
            rectangleTest q (G X) a b F)) ≤
        C + 8 * singletonCap G M X := by
    calc
      _ ≤ ∑ y ∈ range N, w X y *
          (C + 8 * lateRetention (physicalSpan G M X) y) := by
        apply sum_le_sum
        intro y hy
        by_cases hwy : w X y = 0
        · simp only [hwy, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [C] using
              hlayer y (lt_of_le_of_ne (hw X y) (Ne.symm hwy)) q hq hvalid)
            (hw X y)
      _ ≤ ∑ y ∈ range N, w X y *
          (C + 8 * singletonCap G M X) := by
        apply sum_le_sum
        intro y hy
        by_cases hwy : w X y = 0
        · simp only [hwy, zero_mul, le_refl]
        · apply mul_le_mul_of_nonneg_left _ (hw X y)
          exact _root_.add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (hret.2 y hwy).2 (by norm_num))
      _ = C + 8 * singletonCap G M X := by
        rw [← sum_mul, hsumN, one_mul]
  have hmissing :
      missing (w X) (physicalSpan G M X) (M X) * rectangleTest q (G X) a b ∅ ≤
        missing (w X) (physicalSpan G M X) (M X) :=
    mul_le_of_le_one_right
      (missing_nonneg (w X) (hw X) _ _ hdata.2.1)
      (rectangleTest_le_one _ _ _ _ _)
  have hh := _root_.add_le_add hmain hmissing
  exact hh.trans_eq (by dsimp only [C, precisionRectangleError]; ring)

/-! ## Probability and weak-limit packaging -/

/-- The sharp finite rectangle estimate for the actual frame marginal.
The threshold is chosen before the varying injective rank map. -/
theorem eventually_profileLaw_rectangle_precision
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧
      ∀ i, q X i + 1 < M X)
    (theta : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ)))
    (a b : Fin r → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᶠ X in atTop,
      (CoreJointFrameLimit.frameMarginal (profileLaw G M w q theta O X) :
          Measure (Fin r → ℝ))
          (Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))) ≤
        ENNReal.ofReal ((8 : ℝ) ^ r * ∏ i, (b i - a i)) +
          ENNReal.ofReal (precisionRectangleError G M w X) := by
  filter_upwards [eventually_weights hG hκ hM hw hsum hcal, hq,
    eventually_completed_rectangle_precision hG hκ hM hw hsum hcal r a b hab]
      with X hW hqX hrect
  rw [CoreActualFrameRectangleLimit.frame_rectangle_mass_eq_integral]
  have hf : Measurable (fun z : CoreCalibratedFrameProbability.Joint r =>
      if ∀ i, CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i)
      then (1 : ℝ) else 0) := by
    have hs : MeasurableSet {z : CoreCalibratedFrameProbability.Joint r |
        ∀ i, CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i)} := by
      have hi : MeasurableSet (⋂ i : Fin r,
          {z : CoreCalibratedFrameProbability.Joint r | CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i)}) :=
        MeasurableSet.iInter fun i => measurableSet_Ioo.preimage
          ((continuous_apply i).comp CoreJointFrameLimit.continuous_frame).measurable
      simpa only [Set.setOf_forall] using hi
    exact Measurable.ite hs measurable_const measurable_const
  rw [profileLaw, integral_jointLaw _ _ _ hW _ _ _ _ _ hf]
  have he :
      (∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
        completed (w X) (physicalSpan G M X) (M X) F *
          (if ∀ i, CoreJointFrameLimit.frame
              (jointPoint (q X) (G X) (theta X) (O X) F) i ∈
                Set.Ioo (a i) (b i) then (1 : ℝ) else 0)) =
      ∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
        completed (w X) (physicalSpan G M X) (M X) F *
          rectangleTest (q X) (G X) a b F := by
    apply sum_congr rfl
    intro F hF
    unfold rectangleTest jointPoint CoreJointFrameLimit.frame
    congr 1 <;> split_ifs <;> rfl
  rw [he]
  exact (ENNReal.ofReal_le_ofReal (hrect (q X) hqX.1 hqX.2)).trans
    ENNReal.ofReal_add_le

/-- Every weak limit of the actual varying-rank profile laws inherits the
literal `8^r` open-rectangle estimate.  This is the exact finite-density
statement; it precedes any general measurable-set extension. -/
theorem weak_limit_open_rectangle_precision
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧
      ∀ i, q X i + 1 < M X)
    (theta : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ)))
    (nu : ProbabilityMeasure (CoreCalibratedFrameProbability.Joint r)) (phi : ℕ → ℕ)
    (hphi : Tendsto phi atTop atTop)
    (hweak : Tendsto (fun n => profileLaw G M w q theta O (phi n))
      atTop (nhds nu)) :
    ∀ a b : Fin r → ℝ, (∀ i, a i < b i) →
      (CoreJointFrameLimit.frameMarginal nu : Measure (Fin r → ℝ))
          (Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))) ≤
        ENNReal.ofReal ((8 : ℝ) ^ r * ∏ i, (b i - a i)) := by
  apply CoreFrameProbabilityLimit.rectangle_bound_of_weak_limit
    (fun n => CoreJointFrameLimit.frameMarginal
      (profileLaw G M w q theta O (phi n)))
    (CoreJointFrameLimit.frameMarginal nu)
    (CoreJointFrameLimit.frameMarginal_weak _ _ hweak)
    (precisionRectangleError G M w ∘ phi)
    ((tendsto_precisionRectangleError_zero hG hκ hM hw hsum hcal).comp hphi)
  intro a b hab
  exact hphi.eventually
    (eventually_profileLaw_rectangle_precision hG hκ hM hw hsum hcal
      q hq theta O a b hab)

/-- The existing general rectangle-to-volume engine gives an immediate
Lebesgue domination (and hence AC) for every weak limit.  Its generic
cube-enlargement step costs `2^r`; the preceding open-rectangle theorem
retains the sharp paper coefficient exactly. -/
theorem weak_limit_le_volume_from_precision
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧
      ∀ i, q X i + 1 < M X)
    (theta : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ)))
    (nu : ProbabilityMeasure (CoreCalibratedFrameProbability.Joint r)) (phi : ℕ → ℕ)
    (hphi : Tendsto phi atTop atTop)
    (hweak : Tendsto (fun n => profileLaw G M w q theta O (phi n))
      atTop (nhds nu)) :
    (CoreJointFrameLimit.frameMarginal nu : Measure (Fin r → ℝ)) ≤
      ENNReal.ofReal ((16 : ℝ) ^ r) • volume := by
  have hrect := weak_limit_open_rectangle_precision
    hG hκ hM hw hsum hcal q hq theta O nu phi hphi hweak
  have h := CoreRectangleMeasureDomination.le_volume_of_open_rectangle_bound
    (CoreJointFrameLimit.frameMarginal nu : Measure (Fin r → ℝ))
    (pow_pos (by norm_num : (0 : ℝ) < 8) r) hrect
  simpa only [← mul_pow, show (8 : ℝ) * 2 = 16 by norm_num] using h

theorem weak_limit_absolutelyContinuous_from_precision
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (nhds κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y, w X y = 1) (hcal : UniformCalibration w G)
    {r : ℕ} (q : ℕ → Fin r → ℕ)
    (hq : ∀ᶠ X in atTop, Function.Injective (q X) ∧
      ∀ i, q X i + 1 < M X)
    (theta : ℕ → ℝ) (O : ℕ → Finset ℕ → (AddCircle (1 : ℝ)))
    (nu : ProbabilityMeasure (CoreCalibratedFrameProbability.Joint r)) (phi : ℕ → ℕ)
    (hphi : Tendsto phi atTop atTop)
    (hweak : Tendsto (fun n => profileLaw G M w q theta O (phi n))
      atTop (nhds nu)) :
    (CoreJointFrameLimit.frameMarginal nu : Measure (Fin r → ℝ)) ≪ volume :=
  Measure.absolutelyContinuous_of_le_smul
    (weak_limit_le_volume_from_precision
      hG hκ hM hw hsum hcal q hq theta O nu phi hphi hweak)

end

end PrimeGapNormality.Prime.CoreCalibratedRectanglePrecision
