import PrimeGapNormality.Prime.CoreBVOrbitMixing
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Piecewise-linear interval ramps on the circle

The elementary clipped affine ramp is used twice, once at each boundary
of the anchored circle interval.  Short intervals use the zero lower
approximant and near-full intervals use the one upper approximant.  This
keeps all endpoint cases literal.
-/

namespace PrimeGapNormality.Prime.CoreCircleIntervalRamps

open Finset MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CoreBVOrbitMixing

abbrev Circle := CoreBVOrbitMixing.Circle

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Affine ramp clipped to `[0,1]`. -/
def clippedRamp (a δ x : ℝ) : ℝ :=
  max 0 (min 1 ((x - a) / δ))

/-- The decreasing companion of `clippedRamp`. -/
def fallingRamp (a δ x : ℝ) : ℝ := 1 - clippedRamp a δ x

theorem clippedRamp_nonneg (a δ x : ℝ) : 0 ≤ clippedRamp a δ x := by
  unfold clippedRamp
  exact le_max_left _ _

theorem clippedRamp_le_one (a δ x : ℝ) : clippedRamp a δ x ≤ 1 := by
  unfold clippedRamp
  exact max_le (by norm_num) (min_le_left _ _)

theorem fallingRamp_nonneg (a δ x : ℝ) : 0 ≤ fallingRamp a δ x := by
  unfold fallingRamp
  linarith [clippedRamp_le_one a δ x]

theorem fallingRamp_le_one (a δ x : ℝ) : fallingRamp a δ x ≤ 1 := by
  unfold fallingRamp
  linarith [clippedRamp_nonneg a δ x]

theorem clippedRamp_eq_zero_of_le {a δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ a) :
    clippedRamp a δ x = 0 := by
  unfold clippedRamp
  rw [max_eq_left]
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hδ.le)

theorem clippedRamp_eq_one_of_le {a δ x : ℝ} (hδ : 0 < δ) (hx : a + δ ≤ x) :
    clippedRamp a δ x = 1 := by
  unfold clippedRamp
  have hquot : 1 ≤ (x - a) / δ := by
    apply (le_div_iff₀ hδ).2
    linarith
  rw [min_eq_left hquot, max_eq_right (by norm_num)]

theorem clippedRamp_eq_div {a δ x : ℝ} (hδ : 0 < δ)
    (hax : a ≤ x) (hxa : x ≤ a + δ) :
    clippedRamp a δ x = (x - a) / δ := by
  unfold clippedRamp
  have hq0 : 0 ≤ (x - a) / δ := div_nonneg (sub_nonneg.mpr hax) hδ.le
  have hq1 : (x - a) / δ ≤ 1 := by
    apply (div_le_one hδ).2
    linarith
  rw [min_eq_right hq1, max_eq_right hq0]

theorem fallingRamp_eq_one_of_le {a δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ a) :
    fallingRamp a δ x = 1 := by
  rw [fallingRamp, clippedRamp_eq_zero_of_le hδ hx]
  ring

theorem fallingRamp_eq_zero_of_le {a δ x : ℝ} (hδ : 0 < δ) (hx : a + δ ≤ x) :
    fallingRamp a δ x = 0 := by
  rw [fallingRamp, clippedRamp_eq_one_of_le hδ hx]
  ring

theorem clippedRamp_monotone (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Monotone (clippedRamp a δ) := by
  intro x y hxy
  unfold clippedRamp
  gcongr

theorem clippedRamp_continuous (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (clippedRamp a δ) := by
  unfold clippedRamp
  fun_prop

theorem fallingRamp_continuous (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fallingRamp a δ) := by
  unfold fallingRamp
  exact continuous_const.sub (clippedRamp_continuous a hδ)

theorem clippedRamp_lipschitz (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ (clippedRamp a δ) := by
  have haff : LipschitzWith ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
      (fun x : ℝ ↦ (x - a) / δ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |(x - a) / δ - (y - a) / δ| ≤ δ⁻¹ * |x - y|
    have heq : (x - a) / δ - (y - a) / δ = (x - y) / δ := by ring
    rw [heq, abs_div, abs_of_pos hδ, inv_mul_eq_div]
  unfold clippedRamp
  exact (haff.const_min 1).const_max 0

theorem fallingRamp_lipschitz (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ (fallingRamp a δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (clippedRamp_lipschitz a hδ).dist_le_mul x y
  have heq : (1 - clippedRamp a δ x) - (1 - clippedRamp a δ y) =
      -(clippedRamp a δ x - clippedRamp a δ y) := by ring
  simpa only [Real.dist_eq, fallingRamp, heq, abs_neg] using hh

private theorem eVariationOn_neg (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x ↦ -f x) s = eVariationOn f s := by
  unfold eVariationOn
  congr 1 with p
  apply sum_congr rfl
  intro i hi
  exact edist_neg_neg _ _

private theorem eVariationOn_one_sub (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x ↦ 1 - f x) s = eVariationOn f s := by
  have heq : (fun x ↦ 1 - f x) = fun x ↦ -(f x - 1) := by
    funext x
    ring
  rw [heq, eVariationOn_neg, eVariationOn_sub_const]

private theorem eVariationOn_add_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x ↦ f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ range n,
        edist (f (u (i + 1)) + g (u (i + 1)))
          (f (u i) + g (u i))) ≤
        ∑ i ∈ range n,
          (edist (f (u (i + 1))) (f (u i)) +
            edist (g (u (i + 1))) (g (u i))) := by
      apply sum_le_sum
      intro i hi
      exact edist_add_add_le _ _ _ _
    _ = (∑ i ∈ range n, edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ range n, edist (g (u (i + 1))) (g (u i)) := sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
      add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

theorem clippedRamp_unitVariation_eq_one
    {a δ : ℝ} (hδ : 0 < δ) (ha0 : 0 ≤ a) (ha1 : a + δ ≤ 1) :
    unitVariation (clippedRamp a δ) = 1 := by
  have hmono := (clippedRamp_monotone a hδ).monotoneOn (Set.univ : Set ℝ)
  have hv := hmono.eVariationOn_eq (a := (0 : ℝ)) (b := 1) (by simp) (by simp)
  have h0 : clippedRamp a δ 0 = 0 := clippedRamp_eq_zero_of_le hδ ha0
  have h1 : clippedRamp a δ 1 = 1 := clippedRamp_eq_one_of_le hδ ha1
  unfold unitVariation
  simpa only [Set.univ_inter, h0, h1, sub_zero, ENNReal.toReal_ofReal zero_le_one] using
    congrArg ENNReal.toReal hv

theorem fallingRamp_unitVariation_eq_one
    {a δ : ℝ} (hδ : 0 < δ) (ha0 : 0 ≤ a) (ha1 : a + δ ≤ 1) :
    unitVariation (fallingRamp a δ) = 1 := by
  unfold unitVariation fallingRamp
  rw [eVariationOn_one_sub]
  exact clippedRamp_unitVariation_eq_one hδ ha0 ha1

/-- Upper interval ramp on one real period. -/
def upperRampReal (t δ x : ℝ) : ℝ :=
  if t + 2 * δ ≤ 1 then fallingRamp t δ x + clippedRamp (1 - δ) δ x else 1

/-- Lower interval ramp on one real period. -/
def lowerRampReal (t δ x : ℝ) : ℝ :=
  if 2 * δ ≤ t then clippedRamp 0 δ x + fallingRamp (t - δ) δ x - 1 else 0

theorem upperRampReal_nonneg (t δ x : ℝ) : 0 ≤ upperRampReal t δ x := by
  unfold upperRampReal
  split_ifs
  · exact add_nonneg (fallingRamp_nonneg t δ x) (clippedRamp_nonneg (1 - δ) δ x)
  · norm_num

theorem upperRampReal_le_one
    {t δ : ℝ} (hδ : 0 < δ) (x : ℝ) : upperRampReal t δ x ≤ 1 := by
  unfold upperRampReal
  split_ifs with hfar
  · rcases le_total x (t + δ) with hx | hx
    · have hzero : clippedRamp (1 - δ) δ x = 0 :=
        clippedRamp_eq_zero_of_le hδ (by linarith)
      rw [hzero, add_zero]
      exact fallingRamp_le_one _ _ _
    · have hzero : fallingRamp t δ x = 0 := fallingRamp_eq_zero_of_le hδ hx
      rw [hzero, zero_add]
      exact clippedRamp_le_one _ _ _
  · exact le_rfl

theorem lowerRampReal_nonneg
    {t δ : ℝ} (hδ : 0 < δ) (x : ℝ) : 0 ≤ lowerRampReal t δ x := by
  unfold lowerRampReal
  split_ifs with hlong
  · rcases le_total x δ with hx | hx
    · have hone : fallingRamp (t - δ) δ x = 1 :=
        fallingRamp_eq_one_of_le hδ (by linarith)
      rw [hone]
      linarith [clippedRamp_nonneg 0 δ x]
    · have hone : clippedRamp 0 δ x = 1 :=
        clippedRamp_eq_one_of_le hδ (by simpa only [zero_add] using hx)
      rw [hone]
      linarith [fallingRamp_nonneg (t - δ) δ x]
  · norm_num

theorem lowerRampReal_le_one (t δ x : ℝ) : lowerRampReal t δ x ≤ 1 := by
  unfold lowerRampReal
  split_ifs
  · linarith [clippedRamp_le_one 0 δ x, fallingRamp_le_one (t - δ) δ x]
  · norm_num

theorem upperRampReal_eq_one_of_lt
    {t δ x : ℝ} (hδ : 0 < δ) (hx0 : 0 ≤ x) (hxt : x < t) :
    upperRampReal t δ x = 1 := by
  unfold upperRampReal
  split_ifs with hfar
  · have hone := fallingRamp_eq_one_of_le hδ hxt.le
    have hzero := clippedRamp_eq_zero_of_le hδ (show x ≤ 1 - δ by linarith)
    rw [hone, hzero] <;> norm_num
  · rfl

theorem lowerRampReal_eq_zero_of_le
    {t δ x : ℝ} (hδ : 0 < δ) (htx : t ≤ x) :
    lowerRampReal t δ x = 0 := by
  unfold lowerRampReal
  split_ifs with hlong
  · have hzero := fallingRamp_eq_zero_of_le hδ (show t - δ + δ ≤ x by linarith)
    rw [hzero, clippedRamp_eq_one_of_le hδ (show (0 : ℝ) + δ ≤ x by linarith)] <;> norm_num
  · rfl

theorem upperRampReal_continuous (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (upperRampReal t δ) := by
  unfold upperRampReal
  split_ifs
  · exact (fallingRamp_continuous t hδ).add (clippedRamp_continuous (1 - δ) hδ)
  · exact continuous_const

theorem lowerRampReal_continuous (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (lowerRampReal t δ) := by
  unfold lowerRampReal
  split_ifs
  · exact ((clippedRamp_continuous 0 hδ).add
      (fallingRamp_continuous (t - δ) hδ)).sub continuous_const
  · exact continuous_const

theorem upperRampReal_lipschitz (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith
      (⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ + ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩)
      (upperRampReal t δ) := by
  unfold upperRampReal
  split_ifs
  · exact (fallingRamp_lipschitz t hδ).vadd
      (clippedRamp_lipschitz (1 - δ) hδ)
  · exact LipschitzWith.const' 1

theorem lowerRampReal_lipschitz (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith
      (⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ + ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩)
      (lowerRampReal t δ) := by
  unfold lowerRampReal
  split_ifs
  · have hadd : LipschitzWith
        (⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ + ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩)
        (fun x : ℝ => clippedRamp 0 δ x + fallingRamp (t - δ) δ x) :=
      (clippedRamp_lipschitz 0 hδ).vadd (fallingRamp_lipschitz (t - δ) hδ)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hadd.dist_le_mul x y
  · exact LipschitzWith.const' 0

private theorem clippedRamp_boundedVariation
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (s : Set ℝ) :
    BoundedVariationOn (clippedRamp a δ) s :=
  ((clippedRamp_monotone a hδ).monotoneOn s).boundedVariationOn (C := 1) fun x hx ↦ by
    rw [abs_of_nonneg (clippedRamp_nonneg a δ x)]
    exact clippedRamp_le_one a δ x

private theorem fallingRamp_boundedVariation
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (s : Set ℝ) :
    BoundedVariationOn (fallingRamp a δ) s := by
  unfold BoundedVariationOn fallingRamp
  rw [eVariationOn_one_sub]
  exact clippedRamp_boundedVariation a hδ s

theorem upperRampReal_unitVariation_le_two
    {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) :
    unitVariation (upperRampReal t δ) ≤ 2 := by
  unfold upperRampReal
  split_ifs with hfar
  · have ht1 : t + δ ≤ 1 := by linarith
    have hw0 : 0 ≤ 1 - δ := by linarith
    have hw1 : 1 - δ + δ ≤ (1 : ℝ) := by linarith
    have hle := eVariationOn_add_le (fallingRamp t δ)
      (clippedRamp (1 - δ) δ) (Icc (0 : ℝ) 1)
    have hfinite1 := fallingRamp_boundedVariation t hδ (Icc (0 : ℝ) 1)
    have hfinite2 := clippedRamp_boundedVariation (1 - δ) hδ (Icc (0 : ℝ) 1)
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfinite1, hfinite2⟩) hle
    rw [ENNReal.toReal_add hfinite1 hfinite2] at hreal
    change unitVariation (fun x ↦ fallingRamp t δ x + clippedRamp (1 - δ) δ x) ≤
        unitVariation (fallingRamp t δ) + unitVariation (clippedRamp (1 - δ) δ) at hreal
    rw [fallingRamp_unitVariation_eq_one hδ ht0 ht1,
      clippedRamp_unitVariation_eq_one hδ hw0 hw1] at hreal
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hreal
  · unfold unitVariation
    unfold eVariationOn
    simp

theorem lowerRampReal_unitVariation_le_two
    {t δ : ℝ} (hδ : 0 < δ) (ht1 : t ≤ 1) :
    unitVariation (lowerRampReal t δ) ≤ 2 := by
  unfold lowerRampReal
  split_ifs with hlong
  · have hδ1 : δ ≤ 1 := by linarith
    have ha0 : 0 ≤ t - δ := by linarith
    have ha1 : t - δ + δ ≤ (1 : ℝ) := by linarith
    have hle := eVariationOn_add_le (clippedRamp 0 δ)
      (fallingRamp (t - δ) δ) (Icc (0 : ℝ) 1)
    rw [← eVariationOn_sub_const (fun x ↦
      clippedRamp 0 δ x + fallingRamp (t - δ) δ x) 1] at hle
    have hfinite1 := clippedRamp_boundedVariation 0 hδ (Icc (0 : ℝ) 1)
    have hfinite2 := fallingRamp_boundedVariation (t - δ) hδ (Icc (0 : ℝ) 1)
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfinite1, hfinite2⟩) hle
    rw [ENNReal.toReal_add hfinite1 hfinite2] at hreal
    change unitVariation (fun x ↦
        clippedRamp 0 δ x + fallingRamp (t - δ) δ x - 1) ≤
        unitVariation (clippedRamp 0 δ) + unitVariation (fallingRamp (t - δ) δ) at hreal
    have hzero0 : (0 : ℝ) + δ ≤ 1 := by linarith
    rw [clippedRamp_unitVariation_eq_one hδ le_rfl hzero0,
      fallingRamp_unitVariation_eq_one hδ ha0 ha1] at hreal
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hreal
  · unfold unitVariation
    unfold eVariationOn
    simp

theorem upperRampReal_boundedVariation
    {t δ : ℝ} (hδ : 0 < δ) :
    BoundedVariationOn (upperRampReal t δ) (Icc (0 : ℝ) 1) := by
  unfold upperRampReal
  split_ifs
  · exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨fallingRamp_boundedVariation t hδ _,
        clippedRamp_boundedVariation (1 - δ) hδ _⟩)
      (eVariationOn_add_le (fallingRamp t δ) (clippedRamp (1 - δ) δ) _)
  · exact (monotone_const.monotoneOn (Icc (0 : ℝ) 1)).boundedVariationOn (C := 1) fun x hx ↦ by norm_num

theorem lowerRampReal_boundedVariation
    {t δ : ℝ} (hδ : 0 < δ) :
    BoundedVariationOn (lowerRampReal t δ) (Icc (0 : ℝ) 1) := by
  unfold lowerRampReal
  split_ifs
  · unfold BoundedVariationOn
    rw [eVariationOn_sub_const]
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨clippedRamp_boundedVariation 0 hδ _,
        fallingRamp_boundedVariation (t - δ) hδ _⟩)
      (eVariationOn_add_le (clippedRamp 0 δ) (fallingRamp (t - δ) δ) _)
  · exact (monotone_const.monotoneOn (Icc (0 : ℝ) 1)).boundedVariationOn (C := 1) fun x hx ↦ by norm_num

private theorem integral_clippedRamp
    {a δ : ℝ} (hδ : 0 < δ) (ha0 : 0 ≤ a) (ha1 : a + δ ≤ 1) :
    (∫ x in (0 : ℝ)..1, clippedRamp a δ x) = 1 - a - δ / 2 := by
  have hc := clippedRamp_continuous a hδ
  have hzero : (∫ x in (0 : ℝ)..a, clippedRamp a δ x) = 0 := by
    have heq : (∫ x in (0 : ℝ)..a, clippedRamp a δ x) =
        ∫ _x in (0 : ℝ)..a, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le ha0] at hx
      exact clippedRamp_eq_zero_of_le hδ hx.2
    rw [heq, intervalIntegral.integral_const]
    ring
  have hmiddle : (∫ x in a..a + δ, clippedRamp a δ x) = δ / 2 := by
    have heq : (∫ x in a..a + δ, clippedRamp a δ x) =
        ∫ x in a..a + δ, (x - a) / δ := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by linarith : a ≤ a + δ)] at hx
      exact clippedRamp_eq_div hδ hx.1 hx.2
    rw [heq, intervalIntegral.integral_div,
      intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => a)
        (continuous_id.intervalIntegrable a (a + δ)) intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const]
    field_simp [hδ.ne']
    ring
  have hone : (∫ x in a + δ..1, clippedRamp a δ x) = 1 - (a + δ) := by
    have heq : (∫ x in a + δ..1, clippedRamp a δ x) =
        ∫ _x in a + δ..1, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le ha1] at hx
      exact clippedRamp_eq_one_of_le hδ hx.1
    rw [heq, intervalIntegral.integral_const]
    ring
  calc
    (∫ x in (0 : ℝ)..1, clippedRamp a δ x) =
        (∫ x in (0 : ℝ)..a, clippedRamp a δ x) +
          (∫ x in a..a + δ, clippedRamp a δ x) +
          ∫ x in a + δ..1, clippedRamp a δ x := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a (a + δ)),
        intervalIntegral.integral_add_adjacent_intervals
          (hc.intervalIntegrable 0 (a + δ)) (hc.intervalIntegrable (a + δ) 1)]
    _ = 1 - a - δ / 2 := by rw [hzero, hmiddle, hone]; ring

private theorem integral_fallingRamp
    {a δ : ℝ} (hδ : 0 < δ) (ha0 : 0 ≤ a) (ha1 : a + δ ≤ 1) :
    (∫ x in (0 : ℝ)..1, fallingRamp a δ x) = a + δ / 2 := by
  unfold fallingRamp
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((clippedRamp_continuous a hδ).intervalIntegrable 0 1),
    intervalIntegral.integral_const, integral_clippedRamp hδ ha0 ha1]
  ring

theorem integral_upperRampReal_bounds
    {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ (∫ x in (0 : ℝ)..1, upperRampReal t δ x) ∧
      (∫ x in (0 : ℝ)..1, upperRampReal t δ x) ≤ t + 2 * δ := by
  unfold upperRampReal
  split_ifs with hfar
  · have htδ : t + δ ≤ 1 := by linarith
    have hw0 : 0 ≤ 1 - δ := by linarith
    have hw1 : 1 - δ + δ ≤ (1 : ℝ) := by linarith
    rw [intervalIntegral.integral_add
      ((fallingRamp_continuous t hδ).intervalIntegrable 0 1)
      ((clippedRamp_continuous (1 - δ) hδ).intervalIntegrable 0 1),
      integral_fallingRamp hδ ht0 htδ,
      integral_clippedRamp hδ hw0 hw1]
    constructor <;> linarith
  · rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero, one_mul, mul_one, mul_zero]
    constructor <;> linarith

theorem integral_lowerRampReal_bounds
    {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t - 2 * δ ≤ (∫ x in (0 : ℝ)..1, lowerRampReal t δ x) ∧
      (∫ x in (0 : ℝ)..1, lowerRampReal t δ x) ≤ t := by
  unfold lowerRampReal
  split_ifs with hlong
  · have hδ1 : δ ≤ 1 := by linarith
    have ha0 : 0 ≤ t - δ := by linarith
    have ha1 : t - δ + δ ≤ (1 : ℝ) := by linarith
    rw [intervalIntegral.integral_sub
      (((clippedRamp_continuous 0 hδ).intervalIntegrable 0 1).add
        ((fallingRamp_continuous (t - δ) hδ).intervalIntegrable 0 1))
      intervalIntegrable_const,
      intervalIntegral.integral_add
        ((clippedRamp_continuous 0 hδ).intervalIntegrable 0 1)
        ((fallingRamp_continuous (t - δ) hδ).intervalIntegrable 0 1),
      integral_clippedRamp hδ le_rfl (by simpa only [zero_add] using hδ1),
      integral_fallingRamp hδ ha0 ha1, intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero, one_mul, mul_one, mul_zero]
    constructor <;> linarith
  · rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero, one_mul, mul_one, mul_zero]
    constructor <;> linarith

theorem upperRampReal_endpoints
    {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) :
    upperRampReal t δ 0 = upperRampReal t δ 1 := by
  unfold upperRampReal
  split_ifs with hfar
  · have ht1 : t + δ ≤ 1 := by linarith
    have hwrap0 : (0 : ℝ) ≤ 1 - δ := by linarith
    have hwrap1 : 1 - δ + δ ≤ (1 : ℝ) := by linarith
    rw [fallingRamp_eq_one_of_le hδ ht0,
      clippedRamp_eq_zero_of_le hδ hwrap0,
      fallingRamp_eq_zero_of_le hδ ht1,
      clippedRamp_eq_one_of_le hδ hwrap1] <;> norm_num
  · rfl

theorem lowerRampReal_endpoints
    {t δ : ℝ} (hδ : 0 < δ) (ht1 : t ≤ 1) :
    lowerRampReal t δ 0 = lowerRampReal t δ 1 := by
  unfold lowerRampReal
  split_ifs with hlong
  · have htδ0 : 0 ≤ t - δ := by linarith
    have htδ1 : t - δ + δ ≤ (1 : ℝ) := by linarith
    rw [clippedRamp_eq_zero_of_le hδ le_rfl,
      fallingRamp_eq_one_of_le hδ htδ0,
      clippedRamp_eq_one_of_le hδ (by linarith : (0 : ℝ) + δ ≤ 1),
      fallingRamp_eq_zero_of_le hδ htδ1] <;> ring
  · rfl

private theorem liftIoc_zero_coe_apply_Icc
    {f : ℝ → ℝ} (hper : f 0 = f 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    AddCircle.liftIoc (1 : ℝ) 0 f (x : Circle) = f x := by
  by_cases hx0 : x = 0
  · subst x
    have hcoe : ((0 : ℝ) : Circle) = ((1 : ℝ) : Circle) :=
      (AddCircle.coe_period (p := (1 : ℝ))).symm
    rw [hcoe, AddCircle.liftIoc_zero_coe_apply (by simp : (1 : ℝ) ∈ Set.Ioc 0 1)]
    exact hper.symm
  · exact AddCircle.liftIoc_zero_coe_apply
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩

private theorem dist_coe_representatives_eq_min
    {u v : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) (hv : v ∈ Ico (0 : ℝ) 1) :
    dist (u : Circle) (v : Circle) = min |u - v| (1 - |u - v|) := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq,
    inv_one, one_mul, mul_one, abs_sub_round_eq_min]
  by_cases huv : 0 ≤ u - v
  · have hlt : u - v < 1 := by linarith [hu.2, hv.1]
    rw [Int.fract_eq_self.mpr ⟨huv, hlt⟩, abs_of_nonneg huv]
  · have hneg : u - v < 0 := lt_of_not_ge huv
    have he0 : 0 ≤ v - u := by linarith
    have he1 : v - u < 1 := by linarith [hv.2, hu.1]
    have hfractE : Int.fract (v - u) = v - u := Int.fract_eq_self.mpr ⟨he0, he1⟩
    have hfractNe : Int.fract (v - u) ≠ 0 := by rw [hfractE]; linarith
    have hfract := Int.fract_neg hfractNe
    rw [show -(v - u) = u - v by ring, hfractE] at hfract
    rw [hfract, abs_of_neg hneg, min_comm]
    congr 1 <;> ring

/-- An endpoint-matched Lipschitz function on `[0,1]` descends with the
same Lipschitz constant to the unit circle. -/
theorem liftIoc_zero_lipschitz
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (hper : f 0 = f 1) :
    LipschitzWith K (AddCircle.liftIoc (1 : ℝ) 0 f : Circle → ℝ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  let u := (AddCircle.equivIco (1 : ℝ) 0 x : Set.Ico (0 : ℝ) (0 + 1))
  let v := (AddCircle.equivIco (1 : ℝ) 0 y : Set.Ico (0 : ℝ) (0 + 1))
  have hu : (u : ℝ) ∈ Ico (0 : ℝ) 1 := by simpa only [zero_add] using u.property
  have hv : (v : ℝ) ∈ Ico (0 : ℝ) 1 := by simpa only [zero_add] using v.property
  have hxu : ((u : ℝ) : Circle) = x := AddCircle.coe_equivIco
  have hyv : ((v : ℝ) : Circle) = y := AddCircle.coe_equivIco
  have hfu : AddCircle.liftIoc (1 : ℝ) 0 f x = f u := by
    rw [← hxu]
    exact liftIoc_zero_coe_apply_Icc hper ⟨hu.1, hu.2.le⟩
  have hfv : AddCircle.liftIoc (1 : ℝ) 0 f y = f v := by
    rw [← hyv]
    exact liftIoc_zero_coe_apply_Icc hper ⟨hv.1, hv.2.le⟩
  have hdist : dist x y = min |(u : ℝ) - v| (1 - |(u : ℝ) - v|) := by
    rw [← hxu, ← hyv]
    exact dist_coe_representatives_eq_min hu hv
  rw [hfu, hfv, hdist, mul_min_of_nonneg _ _ (NNReal.coe_nonneg K)]
  apply le_min
  · simpa only [Real.dist_eq] using
      (lipschitzWith_iff_dist_le_mul.mp hf (u : ℝ) (v : ℝ))
  · by_cases huv : (v : ℝ) ≤ u
    · have hroute1 := lipschitzWith_iff_dist_le_mul.mp hf (u : ℝ) 1
      have hroute2 := lipschitzWith_iff_dist_le_mul.mp hf 0 (v : ℝ)
      have htri := dist_triangle (f u) (f 1) (f v)
      have hr1 : dist (f u) (f 1) ≤ (K : ℝ) * (1 - u) := by
        simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hu.2.le), neg_sub] using hroute1
      have hr2 : dist (f 1) (f v) ≤ (K : ℝ) * v := by
        rw [← hper]
        simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hv.1] using hroute2
      rw [abs_of_nonneg (sub_nonneg.mpr huv)]
      nlinarith
    · have huv' : (u : ℝ) ≤ v := le_of_not_ge huv
      have hroute1 := lipschitzWith_iff_dist_le_mul.mp hf (u : ℝ) 0
      have hroute2 := lipschitzWith_iff_dist_le_mul.mp hf 1 (v : ℝ)
      have htri := dist_triangle (f u) (f 0) (f v)
      have hr1 : dist (f u) (f 0) ≤ (K : ℝ) * u := by
        simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hu.1] using hroute1
      have hr2 : dist (f 0) (f v) ≤ (K : ℝ) * (1 - v) := by
        rw [hper]
        simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.2.le)] using hroute2
      rw [abs_of_nonpos (sub_nonpos.mpr huv')]
      nlinarith

/-- Continuous circle upper approximant. -/
def upperCircleRamp (t δ : ℝ) (hδ : 0 < δ) (ht0 : 0 ≤ t) : Circle →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨AddCircle.liftIoc (1 : ℝ) 0 (upperRampReal t δ),
      AddCircle.liftIoc_zero_continuous (upperRampReal_endpoints hδ ht0)
        (upperRampReal_continuous t hδ).continuousOn⟩

/-- Continuous circle lower approximant. -/
def lowerCircleRamp (t δ : ℝ) (hδ : 0 < δ) (ht1 : t ≤ 1) : Circle →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨AddCircle.liftIoc (1 : ℝ) 0 (lowerRampReal t δ),
      AddCircle.liftIoc_zero_continuous (lowerRampReal_endpoints hδ ht1)
        (lowerRampReal_continuous t hδ).continuousOn⟩

theorem upperCircleRamp_lipschitz
    (t δ : ℝ) (hδ : 0 < δ) (ht0 : 0 ≤ t) :
    LipschitzWith
      (⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ + ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩)
      (upperCircleRamp t δ hδ ht0) := by
  unfold upperCircleRamp
  exact liftIoc_zero_lipschitz (upperRampReal_lipschitz t hδ)
    (upperRampReal_endpoints hδ ht0)

theorem lowerCircleRamp_lipschitz
    (t δ : ℝ) (hδ : 0 < δ) (ht1 : t ≤ 1) :
    LipschitzWith
      (⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ + ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩)
      (lowerCircleRamp t δ hδ ht1) := by
  unfold lowerCircleRamp
  exact liftIoc_zero_lipschitz (lowerRampReal_lipschitz t hδ)
    (lowerRampReal_endpoints hδ ht1)

theorem upperCircleRamp_coe
    {t δ x : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) (hx : x ∈ Icc (0 : ℝ) 1) :
    upperCircleRamp t δ hδ ht0 (x : Circle) = upperRampReal t δ x := by
  unfold upperCircleRamp
  simp only [BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk]
  by_cases hx0 : x = 0
  · subst x
    have hcoe : ((0 : ℝ) : Circle) = ((1 : ℝ) : Circle) :=
      (AddCircle.coe_period (p := (1 : ℝ))).symm
    rw [hcoe, AddCircle.liftIoc_zero_coe_apply (by simp : (1 : ℝ) ∈ Set.Ioc 0 1)]
    exact (upperRampReal_endpoints hδ ht0).symm
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    exact AddCircle.liftIoc_zero_coe_apply ⟨hxpos, hx.2⟩

theorem lowerCircleRamp_coe
    {t δ x : ℝ} (hδ : 0 < δ) (ht1 : t ≤ 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    lowerCircleRamp t δ hδ ht1 (x : Circle) = lowerRampReal t δ x := by
  unfold lowerCircleRamp
  simp only [BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk]
  by_cases hx0 : x = 0
  · subst x
    have hcoe : ((0 : ℝ) : Circle) = ((1 : ℝ) : Circle) :=
      (AddCircle.coe_period (p := (1 : ℝ))).symm
    rw [hcoe, AddCircle.liftIoc_zero_coe_apply (by simp : (1 : ℝ) ∈ Set.Ioc 0 1)]
    exact (lowerRampReal_endpoints hδ ht1).symm
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    exact AddCircle.liftIoc_zero_coe_apply ⟨hxpos, hx.2⟩

theorem upperCircleRamp_nonneg
    (t δ : ℝ) (hδ : 0 < δ) (ht0 : 0 ≤ t) (x : Circle) :
    0 ≤ upperCircleRamp t δ hδ ht0 x := by
  unfold upperCircleRamp
  change 0 ≤ upperRampReal t δ _
  exact upperRampReal_nonneg _ _ _

theorem upperCircleRamp_le_one
    (t δ : ℝ) (hδ : 0 < δ) (ht0 : 0 ≤ t) (x : Circle) :
    upperCircleRamp t δ hδ ht0 x ≤ 1 := by
  unfold upperCircleRamp
  change upperRampReal t δ _ ≤ 1
  exact upperRampReal_le_one hδ _

theorem lowerCircleRamp_nonneg
    (t δ : ℝ) (hδ : 0 < δ) (ht1 : t ≤ 1) (x : Circle) :
    0 ≤ lowerCircleRamp t δ hδ ht1 x := by
  unfold lowerCircleRamp
  change 0 ≤ lowerRampReal t δ _
  exact lowerRampReal_nonneg hδ _

theorem lowerCircleRamp_le_one
    (t δ : ℝ) (hδ : 0 < δ) (ht1 : t ≤ 1) (x : Circle) :
    lowerCircleRamp t δ hδ ht1 x ≤ 1 := by
  unfold lowerCircleRamp
  change lowerRampReal t δ _ ≤ 1
  exact lowerRampReal_le_one _ _ _

theorem upperCircleRamp_variation_le_two
    {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) :
    circleVariation (upperCircleRamp t δ hδ ht0) ≤ 2 := by
  have heq : EqOn (circleLift (upperCircleRamp t δ hδ ht0))
      (upperRampReal t δ) (Icc (0 : ℝ) 1) := by
    intro x hx
    exact upperCircleRamp_coe hδ ht0 hx
  unfold circleVariation unitVariation
  rw [eVariationOn.eq_of_eqOn heq]
  exact upperRampReal_unitVariation_le_two hδ ht0

theorem lowerCircleRamp_variation_le_two
    {t δ : ℝ} (hδ : 0 < δ) (ht1 : t ≤ 1) :
    circleVariation (lowerCircleRamp t δ hδ ht1) ≤ 2 := by
  have heq : EqOn (circleLift (lowerCircleRamp t δ hδ ht1))
      (lowerRampReal t δ) (Icc (0 : ℝ) 1) := by
    intro x hx
    exact lowerCircleRamp_coe hδ ht1 hx
  unfold circleVariation unitVariation
  rw [eVariationOn.eq_of_eqOn heq]
  exact lowerRampReal_unitVariation_le_two hδ ht1

theorem upperCircleRamp_boundedVariation
    {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) :
    BoundedVariationOn (circleLift (upperCircleRamp t δ hδ ht0))
      (Icc (0 : ℝ) 1) := by
  have heq : EqOn (circleLift (upperCircleRamp t δ hδ ht0))
      (upperRampReal t δ) (Icc (0 : ℝ) 1) := by
    intro x hx
    exact upperCircleRamp_coe hδ ht0 hx
  unfold BoundedVariationOn
  rw [eVariationOn.eq_of_eqOn heq]
  exact upperRampReal_boundedVariation hδ

theorem lowerCircleRamp_boundedVariation
    {t δ : ℝ} (hδ : 0 < δ) (ht1 : t ≤ 1) :
    BoundedVariationOn (circleLift (lowerCircleRamp t δ hδ ht1))
      (Icc (0 : ℝ) 1) := by
  have heq : EqOn (circleLift (lowerCircleRamp t δ hδ ht1))
      (lowerRampReal t δ) (Icc (0 : ℝ) 1) := by
    intro x hx
    exact lowerCircleRamp_coe hδ ht1 hx
  unfold BoundedVariationOn
  rw [eVariationOn.eq_of_eqOn heq]
  exact lowerRampReal_boundedVariation hδ

/-- Anchored half-open interval on the unit circle, expressed using its
canonical representative in `[0,1)`. -/
def anchoredCircleInterval (t : ℝ) : Set Circle :=
  {x | ((AddCircle.equivIco (1 : ℝ) 0 x : Set.Ico (0 : ℝ) (0 + 1)) : ℝ) < t}

theorem upperCircleRamp_eq_one_of_mem
    {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) {x : Circle}
    (hx : x ∈ anchoredCircleInterval t) :
    upperCircleRamp t δ hδ ht0 x = 1 := by
  let y := (AddCircle.equivIco (1 : ℝ) 0 x : Set.Ico (0 : ℝ) (0 + 1))
  have hy : (y : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨y.property.1, by simpa only [zero_add] using y.property.2.le⟩
  have heval := upperCircleRamp_coe hδ ht0 hy
  have hcoe : ((y : ℝ) : Circle) = x := AddCircle.coe_equivIco
  rw [hcoe] at heval
  rw [heval]
  apply upperRampReal_eq_one_of_lt hδ y.property.1
  change (y : ℝ) < t at hx
  exact hx

theorem lowerCircleRamp_eq_zero_of_not_mem
    {t δ : ℝ} (hδ : 0 < δ) (ht1 : t ≤ 1) {x : Circle}
    (hx : x ∉ anchoredCircleInterval t) :
    lowerCircleRamp t δ hδ ht1 x = 0 := by
  let y := (AddCircle.equivIco (1 : ℝ) 0 x : Set.Ico (0 : ℝ) (0 + 1))
  have hy : (y : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨y.property.1, by simpa only [zero_add] using y.property.2.le⟩
  have heval := lowerCircleRamp_coe hδ ht1 hy
  have hcoe : ((y : ℝ) : Circle) = x := AddCircle.coe_equivIco
  rw [hcoe] at heval
  rw [heval]
  apply lowerRampReal_eq_zero_of_le hδ
  change ¬(y : ℝ) < t at hx
  exact le_of_not_gt hx

theorem circleRamp_sandwich
    {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Circle) :
    lowerCircleRamp t δ hδ ht1 x ≤
        (anchoredCircleInterval t).indicator (fun _ ↦ (1 : ℝ)) x ∧
      (anchoredCircleInterval t).indicator (fun _ ↦ (1 : ℝ)) x ≤
        upperCircleRamp t δ hδ ht0 x := by
  by_cases hx : x ∈ anchoredCircleInterval t
  · rw [Set.indicator_of_mem hx, upperCircleRamp_eq_one_of_mem hδ ht0 hx]
    exact ⟨lowerCircleRamp_le_one t δ hδ ht1 x, le_rfl⟩
  · rw [Set.indicator_of_notMem hx, lowerCircleRamp_eq_zero_of_not_mem hδ ht1 hx]
    exact ⟨le_rfl, upperCircleRamp_nonneg t δ hδ ht0 x⟩

private theorem integral_upperCircleRamp_eq
    {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) :
    (∫ x : Circle, upperCircleRamp t δ hδ ht0 x) =
      ∫ x in (0 : ℝ)..1, upperRampReal t δ x := by
  unfold upperCircleRamp
  simpa only [BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk, zero_add] using
    (AddCircle.integral_liftIoc_eq_intervalIntegral
      (T := (1 : ℝ)) (t := (0 : ℝ)) (f := upperRampReal t δ))

private theorem integral_lowerCircleRamp_eq
    {t δ : ℝ} (hδ : 0 < δ) (ht1 : t ≤ 1) :
    (∫ x : Circle, lowerCircleRamp t δ hδ ht1 x) =
      ∫ x in (0 : ℝ)..1, lowerRampReal t δ x := by
  unfold lowerCircleRamp
  simpa only [BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk, zero_add] using
    (AddCircle.integral_liftIoc_eq_intervalIntegral
      (T := (1 : ℝ)) (t := (0 : ℝ)) (f := lowerRampReal t δ))

/-- Haar means sandwich interval length with uniform cost `2δ`. -/
theorem circleRamp_integral_bounds
    {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t - 2 * δ ≤ (∫ x : Circle, lowerCircleRamp t δ hδ ht1 x) ∧
      (∫ x : Circle, lowerCircleRamp t δ hδ ht1 x) ≤ t ∧
      t ≤ (∫ x : Circle, upperCircleRamp t δ hδ ht0 x) ∧
      (∫ x : Circle, upperCircleRamp t δ hδ ht0 x) ≤ t + 2 * δ := by
  rw [integral_lowerCircleRamp_eq hδ ht1, integral_upperCircleRamp_eq hδ ht0]
  exact ⟨(integral_lowerRampReal_bounds hδ ht0 ht1).1,
    (integral_lowerRampReal_bounds hδ ht0 ht1).2,
    (integral_upperRampReal_bounds hδ ht0 ht1).1,
    (integral_upperRampReal_bounds hδ ht0 ht1).2⟩

end

end PrimeGapNormality.Prime.CoreCircleIntervalRamps
