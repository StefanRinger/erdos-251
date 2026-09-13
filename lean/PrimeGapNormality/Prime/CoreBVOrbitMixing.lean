import PrimeGapNormality.Prime.CoreOrbitCovarianceVariance
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Bounded variation and the expanding circle clock

The Riemann estimate in this file is genuinely uniform in the Lipschitz
constant: one point is sampled in each of the `q` equal cells, and the sum
of the cell variations is the total variation.  This is the analytic input
which keeps the interval-ramp width out of the orbit covariance constant.
-/

namespace PrimeGapNormality.Prime.CoreBVOrbitMixing

open Finset Filter MeasureTheory Set
open CoreOrbitCovarianceVariance
open scoped BigOperators Topology ENNReal BoundedContinuousFunction

noncomputable section

/-- Real total variation on the unit interval. -/
def unitVariation (f : ℝ → ℝ) : ℝ :=
  (eVariationOn f (Icc (0 : ℝ) 1)).toReal

/-- Equal-grid sample average with a common relative offset `τ`. -/
def gridMean (q : ℕ) (f : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (∑ j ∈ range q, f (((j : ℝ) + τ) / (q : ℝ))) / (q : ℝ)

private theorem gridCell_subset_unit {q j : ℕ} (hq : 0 < q) (hj : j < q) :
    Icc ((j : ℝ) / (q : ℝ)) (((j + 1 : ℕ) : ℝ) / (q : ℝ)) ⊆
      Icc (0 : ℝ) 1 := by
  intro x hx
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hjR : ((j + 1 : ℕ) : ℝ) ≤ q := Nat.cast_le.mpr hj
  constructor
  · exact (div_nonneg (Nat.cast_nonneg j) hqR.le).trans hx.1
  · exact hx.2.trans ((div_le_one hqR).2 hjR)

private theorem sample_mem_gridCell {q j : ℕ} (hq : 0 < q) (hj : j < q)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ((j : ℝ) + τ) / (q : ℝ) ∈
      Icc ((j : ℝ) / (q : ℝ)) (((j + 1 : ℕ) : ℝ) / (q : ℝ)) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  constructor <;> apply (div_le_div_iff_of_pos_right hqR).2
  · linarith
  · push_cast
    linarith

private theorem abs_gridCell_error_le
    {f : ℝ → ℝ} (hf : Continuous f)
    (hBV : BoundedVariationOn f (Icc (0 : ℝ) 1))
    {q j : ℕ} (hq : 0 < q) (hj : j < q)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    |f (((j : ℝ) + τ) / (q : ℝ)) / (q : ℝ) -
        ∫ x in (j : ℝ) / (q : ℝ)..((j + 1 : ℕ) : ℝ) / (q : ℝ), f x| ≤
      (eVariationOn f
        (Icc ((j : ℝ) / (q : ℝ)) (((j + 1 : ℕ) : ℝ) / (q : ℝ)))).toReal /
        (q : ℝ) := by
  let l : ℝ := (j : ℝ) / (q : ℝ)
  let r : ℝ := ((j + 1 : ℕ) : ℝ) / (q : ℝ)
  let s : ℝ := ((j : ℝ) + τ) / (q : ℝ)
  let V : ℝ := (eVariationOn f (Icc l r)).toReal
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hlr : l ≤ r := by
    dsimp only [l, r]
    apply (div_le_div_iff_of_pos_right hqR).2
    push_cast
    linarith
  have hwidth : r - l = (1 : ℝ) / q := by
    dsimp only [l, r]
    push_cast
    field_simp [hqR.ne'] <;> ring
  have hsub : Icc l r ⊆ Icc (0 : ℝ) 1 := by
    simpa only [l, r] using gridCell_subset_unit hq hj
  have hlocalBV : BoundedVariationOn f (Icc l r) := hBV.mono hsub
  have hs : s ∈ Icc l r := by
    simpa only [s, l, r] using sample_mem_gridCell hq hj hτ0 hτ1
  have hosc : ∀ x ∈ Icc l r, |f s - f x| ≤ V := by
    intro x hx
    have hh := hlocalBV.dist_le hs hx
    simpa only [Real.dist_eq, V] using hh
  have hfInt : IntervalIntegrable f volume l r := hf.intervalIntegrable l r
  have hdiffInt : IntervalIntegrable (fun x ↦ f s - f x) volume l r :=
    intervalIntegrable_const.sub hfInt
  have heq : f s / (q : ℝ) - (∫ x in l..r, f x) =
      ∫ x in l..r, f s - f x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfInt,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    rw [hwidth]
    ring
  have habs := intervalIntegral.abs_integral_le_integral_abs
    (μ := volume) (f := fun x ↦ f s - f x) hlr
  have hmono : (∫ x in l..r, |f s - f x|) ≤ ∫ _x in l..r, V := by
    apply intervalIntegral.integral_mono_on hlr hdiffInt.norm intervalIntegrable_const
    intro x hx
    simpa only [Real.norm_eq_abs] using hosc x hx
  have hconst : (∫ _x in l..r, V) = V / (q : ℝ) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    rw [hwidth]
    ring
  dsimp only [s, l, r, V] at heq ⊢
  rw [heq]
  exact habs.trans (hmono.trans_eq hconst)

private theorem gridVariation_sum
    {f : ℝ → ℝ} (hBV : BoundedVariationOn f (Icc (0 : ℝ) 1))
    {q : ℕ} (hq : 0 < q) :
    (∑ j ∈ range q,
      (eVariationOn f
        (Icc ((j : ℝ) / (q : ℝ)) (((j + 1 : ℕ) : ℝ) / (q : ℝ)))).toReal) =
      unitVariation f := by
  let E : ℕ → ℝ := fun j ↦ (j : ℝ) / (q : ℝ)
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hE : Monotone E := by
    intro i j hij
    dsimp only [E]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) hqR.le
  have hvarENN :
      (∑ j ∈ range q, eVariationOn f (Icc (E j) (E (j + 1)))) =
        eVariationOn f (Icc (0 : ℝ) 1) := by
    have hh := eVariationOn.sum f (s := (Set.univ : Set ℝ)) hE
      (n := q) (by simp)
    simpa only [Set.univ_inter, E, Nat.cast_zero, zero_div,
      Nat.cast_add, Nat.cast_one, div_self hqR.ne'] using hh
  have hfinite : ∀ j ∈ range q,
      eVariationOn f (Icc (E j) (E (j + 1))) ≠ ∞ := by
    intro j hj
    have hsub : Icc (E j) (E (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
      simpa only [E] using gridCell_subset_unit hq (mem_range.mp hj)
    exact (hBV.mono hsub)
  unfold unitVariation
  change (∑ j ∈ range q,
      (eVariationOn f (Icc (E j) (E (j + 1)))).toReal) = _
  rw [← ENNReal.toReal_sum hfinite, hvarENN]

/-- The equal-grid transfer estimate.  Its constant is total variation,
not the Lipschitz constant. -/
theorem abs_gridMean_sub_integral_le_variation
    {f : ℝ → ℝ} (hf : Continuous f)
    (hBV : BoundedVariationOn f (Icc (0 : ℝ) 1))
    {q : ℕ} (hq : 0 < q) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    |gridMean q f τ - ∫ x in (0 : ℝ)..1, f x| ≤
      unitVariation f / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hparts := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (f := f) (a := fun j : ℕ ↦ (j : ℝ) / (q : ℝ)) (n := q)
    (fun j hj ↦ hf.intervalIntegrable _ _)
  have hparts' :
      (∑ j ∈ range q,
        ∫ x in (j : ℝ) / (q : ℝ)..((j + 1 : ℕ) : ℝ) / (q : ℝ), f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    simpa only [Nat.cast_zero, zero_div, div_self hqR.ne'] using hparts
  have hdiff : gridMean q f τ - (∫ x in (0 : ℝ)..1, f x) =
      ∑ j ∈ range q,
        (f (((j : ℝ) + τ) / (q : ℝ)) / (q : ℝ) -
          ∫ x in (j : ℝ) / (q : ℝ)..((j + 1 : ℕ) : ℝ) / (q : ℝ), f x) := by
    unfold gridMean
    rw [sum_sub_distrib, ← hparts', sum_div]
  rw [hdiff]
  calc
    |∑ j ∈ range q,
        (f (((j : ℝ) + τ) / (q : ℝ)) / (q : ℝ) -
          ∫ x in (j : ℝ) / (q : ℝ)..((j + 1 : ℕ) : ℝ) / (q : ℝ), f x)| ≤
        ∑ j ∈ range q,
          |f (((j : ℝ) + τ) / (q : ℝ)) / (q : ℝ) -
            ∫ x in (j : ℝ) / (q : ℝ)..((j + 1 : ℕ) : ℝ) / (q : ℝ), f x| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range q,
        (eVariationOn f
          (Icc ((j : ℝ) / (q : ℝ)) (((j + 1 : ℕ) : ℝ) / (q : ℝ)))).toReal /
          (q : ℝ) := by
      apply sum_le_sum
      intro j hj
      exact abs_gridCell_error_le hf hBV hq (mem_range.mp hj) hτ0 hτ1
    _ = unitVariation f / (q : ℝ) := by
      rw [← sum_div, gridVariation_sum hBV hq]

abbrev Circle := CoreOrbitCovarianceVariance.Circle

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : IsProbabilityMeasure (volume : Measure Circle) := ⟨by simp⟩

/-- The real periodic lift of a circle test. -/
def circleLift (φ : Circle → ℝ) (x : ℝ) : ℝ := φ (x : Circle)

/-- The transfer grid over the `q` preimages of a circle point. -/
def circleTransfer (q : ℕ) (φ : Circle → ℝ) (x : Circle) : ℝ :=
  gridMean q (circleLift φ)
    ((AddCircle.equivIco (1 : ℝ) 0 x : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)

/-- Total variation of the canonical real lift on one period. -/
def circleVariation (φ : Circle → ℝ) : ℝ := unitVariation (circleLift φ)

theorem eVariationOn_sub_const (f : ℝ → ℝ) (c : ℝ) (s : Set ℝ) :
    eVariationOn (fun x ↦ f x - c) s = eVariationOn f s := by
  unfold eVariationOn
  congr 1 with p
  apply sum_congr rfl
  intro i hi
  simp only [edist_dist, Real.dist_eq]
  congr 2
  ring

theorem boundedVariationOn_sub_const_iff
    (f : ℝ → ℝ) (c : ℝ) (s : Set ℝ) :
    BoundedVariationOn (fun x ↦ f x - c) s ↔ BoundedVariationOn f s := by
  unfold BoundedVariationOn
  rw [eVariationOn_sub_const]

/-- The transfer grid is within `TV/q` of Haar mean.  This is the
bounded-variation estimate used in the expanding-clock covariance proof. -/
theorem abs_circleTransfer_sub_integral_le
    (φ : Circle →ᵇ ℝ)
    (hBV : BoundedVariationOn (circleLift φ) (Icc (0 : ℝ) 1))
    {V : ℝ} (hV : circleVariation φ ≤ V)
    {q : ℕ} (hq : 0 < q) (x : Circle) :
    |circleTransfer q φ x - ∫ z : Circle, φ z| ≤ V / (q : ℝ) := by
  let τ : ℝ :=
    ((AddCircle.equivIco (1 : ℝ) 0 x : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)
  have hτ :=
    (AddCircle.equivIco (1 : ℝ) 0 x : Set.Ico (0 : ℝ) (0 + 1)).property
  have hgrid := abs_gridMean_sub_integral_le_variation
    ((φ.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))) :
      Continuous (circleLift φ)) hBV hq hτ.1 (by simpa only [zero_add] using hτ.2.le)
  have hmean : (∫ t in (0 : ℝ)..1, circleLift φ t) =
      ∫ z : Circle, φ z := by
    simpa only [circleLift, zero_add] using
      AddCircle.intervalIntegral_preimage (1 : ℝ) 0 φ
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  calc
    |circleTransfer q φ x - ∫ z : Circle, φ z| =
        |gridMean q (circleLift φ) τ -
          ∫ t in (0 : ℝ)..1, circleLift φ t| := by
      rw [hmean]
      rfl
    _ ≤ unitVariation (circleLift φ) / (q : ℝ) := hgrid
    _ ≤ V / (q : ℝ) := div_le_div_of_nonneg_right hV hq0

private theorem circle_natCast_eq_zero (j : ℕ) :
    ((j : ℝ) : Circle) = 0 := by
  have hh := AddCircle.coe_nsmul (p := (1 : ℝ)) (n := j) (x := (1 : ℝ))
  simpa only [nsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using hh

private theorem circleClock_preimage_eq
    {q : ℕ} (hq : 0 < q) (j : ℕ) (u : ℝ) :
    q • ((((j : ℝ) + u) / (q : ℝ) : ℝ) : Circle) = (u : Circle) := by
  rw [← AddCircle.coe_nsmul]
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have heq : (q : ℝ) * (((j : ℝ) + u) / (q : ℝ)) = (j : ℝ) + u := by
    field_simp [hqR]
  rw [nsmul_eq_mul, heq, AddCircle.coe_add, circle_natCast_eq_zero, zero_add]

private theorem interval_clock_cell
    (φ ψ : Circle →ᵇ ℝ) {q : ℕ} (hq : 0 < q) (j : ℕ) :
    (∫ x in (j : ℝ) / (q : ℝ)..((j + 1 : ℕ) : ℝ) / (q : ℝ),
        φ (x : Circle) * ψ (q • (x : Circle))) =
      (1 / (q : ℝ)) *
        ∫ u in (0 : ℝ)..1,
          φ ((((j : ℝ) + u) / (q : ℝ) : ℝ) : Circle) * ψ (u : Circle) := by
  let H : ℝ → ℝ := fun x ↦ φ (x : Circle) * ψ (q • (x : Circle))
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hcomp : (fun u : ℝ ↦ H ((j : ℝ) / (q : ℝ) + u / (q : ℝ))) =
      fun u : ℝ ↦
        φ ((((j : ℝ) + u) / (q : ℝ) : ℝ) : Circle) * ψ (u : Circle) := by
    funext u
    have harg : (j : ℝ) / (q : ℝ) + u / (q : ℝ) =
        ((j : ℝ) + u) / (q : ℝ) := by ring
    dsimp only [H]
    rw [harg, circleClock_preimage_eq hq j u]
  have hsub := intervalIntegral.integral_comp_add_div
    (a := (0 : ℝ)) (b := 1) H hqR ((j : ℝ) / (q : ℝ))
  rw [hcomp] at hsub
  have hsub' :
      (∫ u in (0 : ℝ)..1,
          φ ((((j : ℝ) + u) / (q : ℝ) : ℝ) : Circle) * ψ (u : Circle)) =
        (q : ℝ) *
          ∫ x in (j : ℝ) / (q : ℝ)..((j + 1 : ℕ) : ℝ) / (q : ℝ), H x := by
    convert hsub using 1 <;> push_cast <;> ring
  dsimp only [H] at hsub' ⊢
  rw [hsub']
  field_simp [hqR]

/-- Exact interval form of transfer duality for the non-injective
multiplication clock. -/
theorem interval_clock_transfer_duality
    (φ ψ : Circle →ᵇ ℝ) {q : ℕ} (hq : 0 < q) :
    (∫ x in (0 : ℝ)..1, φ (x : Circle) * ψ (q • (x : Circle))) =
      ∫ u in (0 : ℝ)..1, gridMean q (circleLift φ) u * ψ (u : Circle) := by
  let H : ℝ → ℝ := fun x ↦ φ (x : Circle) * ψ (q • (x : Circle))
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hcontH : Continuous H :=
    (φ.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))).mul
      (ψ.continuous.comp ((continuous_const_smul q).comp
        (AddCircle.continuous_mk' (1 : ℝ))))
  have hparts := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (f := H) (a := fun j : ℕ ↦ (j : ℝ) / (q : ℝ)) (n := q)
    (fun j hj ↦ hcontH.intervalIntegrable _ _)
  have hparts' :
      (∑ j ∈ range q,
        ∫ x in (j : ℝ) / (q : ℝ)..((j + 1 : ℕ) : ℝ) / (q : ℝ), H x) =
        ∫ x in (0 : ℝ)..1, H x := by
    simpa only [Nat.cast_zero, zero_div, div_self hqR.ne'] using hparts
  calc
    (∫ x in (0 : ℝ)..1, φ (x : Circle) * ψ (q • (x : Circle))) =
        ∑ j ∈ range q,
          ∫ x in (j : ℝ) / (q : ℝ)..((j + 1 : ℕ) : ℝ) / (q : ℝ), H x := by
      dsimp only [H] at hparts'
      exact hparts'.symm
    _ = ∑ j ∈ range q, (1 / (q : ℝ)) *
          ∫ u in (0 : ℝ)..1,
            φ ((((j : ℝ) + u) / (q : ℝ) : ℝ) : Circle) * ψ (u : Circle) := by
      apply sum_congr rfl
      intro j hj
      exact interval_clock_cell φ ψ hq j
    _ = (1 / (q : ℝ)) *
        ∫ u in (0 : ℝ)..1,
          ∑ j ∈ range q,
            φ ((((j : ℝ) + u) / (q : ℝ) : ℝ) : Circle) * ψ (u : Circle) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [intervalIntegral.integral_finsetSum]
      intro j hj
      exact ((φ.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp
        ((continuous_const.add continuous_id).div_const (q : ℝ)))).mul
          (ψ.continuous.comp (AddCircle.continuous_mk' (1 : ℝ)))).intervalIntegrable _ _
    _ = ∫ u in (0 : ℝ)..1, gridMean q (circleLift φ) u * ψ (u : Circle) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      unfold gridMean circleLift
      dsimp only
      rw [← sum_mul]
      ring

/-- Haar mean of a bounded continuous circle test. -/
def circleMean (φ : Circle →ᵇ ℝ) : ℝ := ∫ x : Circle, φ x

/-- Centered bounded continuous test. -/
def centeredCircleTest (φ : Circle →ᵇ ℝ) : Circle →ᵇ ℝ :=
  φ - BoundedContinuousFunction.const Circle (circleMean φ)

theorem centeredCircleTest_apply (φ : Circle →ᵇ ℝ) (x : Circle) :
    centeredCircleTest φ x = φ x - circleMean φ := rfl

theorem centeredCircleTest_boundedVariation
    (φ : Circle →ᵇ ℝ)
    (hBV : BoundedVariationOn (circleLift φ) (Icc (0 : ℝ) 1)) :
    BoundedVariationOn (circleLift (centeredCircleTest φ)) (Icc (0 : ℝ) 1) := by
  have heq : circleLift (centeredCircleTest φ) =
      fun x ↦ circleLift φ x - circleMean φ := rfl
  rw [heq, boundedVariationOn_sub_const_iff]
  exact hBV

theorem centeredCircleTest_variation_eq (φ : Circle →ᵇ ℝ) :
    circleVariation (centeredCircleTest φ) = circleVariation φ := by
  unfold circleVariation unitVariation
  have heq : circleLift (centeredCircleTest φ) =
      fun x ↦ circleLift φ x - circleMean φ := rfl
  rw [heq, eVariationOn_sub_const]

private theorem circleMean_mem_unit
    (φ : Circle →ᵇ ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    circleMean φ ∈ Icc (0 : ℝ) 1 := by
  have hφInt : Integrable φ (volume : Measure Circle) :=
    BoundedContinuousFunction.integrable volume φ
  constructor
  · exact integral_nonneg hφ0
  · have hh := integral_mono_ae hφInt (integrable_const (1 : ℝ))
      (Eventually.of_forall hφ1)
    simpa [circleMean] using hh

theorem centeredCircleTest_abs_le_one
    (φ : Circle →ᵇ ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (x : Circle) : |centeredCircleTest φ x| ≤ 1 := by
  have hm := circleMean_mem_unit φ hφ0 hφ1
  rw [centeredCircleTest_apply, abs_le]
  constructor <;> linarith [hm.1, hm.2, hφ0 x, hφ1 x]

private theorem centeredCircleTest_integral_zero (φ : Circle →ᵇ ℝ) :
    (∫ x : Circle, centeredCircleTest φ x) = 0 := by
  have hφInt : Integrable φ (volume : Measure Circle) :=
    BoundedContinuousFunction.integrable volume φ
  change (∫ x : Circle, φ x - circleMean φ) = 0
  rw [integral_sub hφInt (integrable_const _)]
  simp [circleMean]

/-- Actual covariance bound for the integer multiplication clock, obtained
from the `TV/q` transfer estimate.  The hypotheses on variation concern the
centered lift only; subtracting a constant does not change variation, and
the concrete interval ramps can therefore discharge them with `V = 2`. -/
theorem abs_circleClock_covariance_le
    (φ : Circle →ᵇ ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {V : ℝ}
    (hBV : BoundedVariationOn (circleLift (centeredCircleTest φ))
      (Icc (0 : ℝ) 1))
    (hV : circleVariation (centeredCircleTest φ) ≤ V)
    {q : ℕ} (hq : 0 < q) :
    |∫ x : Circle,
      centeredCircleTest φ x * centeredCircleTest φ (q • x)| ≤
      V / (q : ℝ) := by
  let φ₀ := centeredCircleTest φ
  have hvariation0 : 0 ≤ circleVariation φ₀ := by
    unfold circleVariation unitVariation
    exact ENNReal.toReal_nonneg
  have hV0 : 0 ≤ V := hvariation0.trans (by simpa only [φ₀] using hV)
  have hzeroCircle : (∫ x : Circle, φ₀ x) = 0 := by
    simpa only [φ₀] using centeredCircleTest_integral_zero φ
  have hzeroInterval : (∫ u in (0 : ℝ)..1, circleLift φ₀ u) = 0 := by
    have heq : (∫ u in (0 : ℝ)..1, circleLift φ₀ u) =
        ∫ x : Circle, φ₀ x := by
      simpa only [circleLift, zero_add] using
        AddCircle.intervalIntegral_preimage (1 : ℝ) 0 φ₀
    exact heq.trans hzeroCircle
  have hgrid : ∀ u ∈ Icc (0 : ℝ) 1,
      |gridMean q (circleLift φ₀) u| ≤ V / (q : ℝ) := by
    intro u hu
    have hh := abs_gridMean_sub_integral_le_variation
      (f := circleLift φ₀)
      ((φ₀.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))) :
        Continuous (circleLift φ₀)) hBV hq hu.1 hu.2
    rw [hzeroInterval, sub_zero] at hh
    exact hh.trans (div_le_div_of_nonneg_right hV (Nat.cast_nonneg q))
  have hpoint : ∀ u ∈ Icc (0 : ℝ) 1,
      |gridMean q (circleLift φ₀) u * φ₀ (u : Circle)| ≤ V / (q : ℝ) := by
    intro u hu
    rw [abs_mul]
    have hφabs : |φ₀ (u : Circle)| ≤ 1 := by
      simpa only [φ₀] using centeredCircleTest_abs_le_one φ hφ0 hφ1 (u : Circle)
    calc
      |gridMean q (circleLift φ₀) u| * |φ₀ (u : Circle)| ≤
          (V / (q : ℝ)) * 1 :=
        mul_le_mul (hgrid u hu) hφabs (abs_nonneg _) (div_nonneg hV0 (Nat.cast_nonneg q))
      _ = V / (q : ℝ) := mul_one _
  have hprodCont : Continuous
      (fun u : ℝ ↦ gridMean q (circleLift φ₀) u * φ₀ (u : Circle)) := by
    unfold gridMean circleLift
    fun_prop
  have hpre := AddCircle.intervalIntegral_preimage (1 : ℝ) 0
    (fun x : Circle ↦ φ₀ x * φ₀ (q • x))
  rw [← hpre]
  simp only [zero_add]
  rw [interval_clock_transfer_duality φ₀ φ₀ hq]
  calc
    |∫ u in (0 : ℝ)..1, gridMean q (circleLift φ₀) u * φ₀ (u : Circle)| ≤
        ∫ u in (0 : ℝ)..1,
          |gridMean q (circleLift φ₀) u * φ₀ (u : Circle)| :=
      intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ _u in (0 : ℝ)..1, V / (q : ℝ) := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (hprodCont.intervalIntegrable 0 1).norm intervalIntegrable_const
      exact hpoint
    _ = V / (q : ℝ) := by simp

private theorem integral_circleClock_eq
    {q : ℕ} (hq : 0 < q) (f : Circle → ℝ) (hf : Continuous f) :
    (∫ x : Circle, f (q • x)) = ∫ x : Circle, f x := by
  have hmap := MeasureTheory.integral_map (μ := (volume : Measure Circle)) (f := f)
    (circleClock_continuous q).measurable.aemeasurable
    hf.aestronglyMeasurable
  have hpres := circleClock_measurePreserving hq
  calc
    (∫ x : Circle, f (q • x)) =
        ∫ x : Circle, f x ∂Measure.map (circleClock q) volume := by
      simpa only [circleClock] using hmap.symm
    _ = ∫ x : Circle, f x := by rw [hpres.map_eq]

private theorem pow_sub_mul_pow_eq {B i j : ℕ} (hij : i ≤ j) :
    B ^ (j - i) * B ^ i = B ^ j := by
  rw [← pow_add, Nat.sub_add_cancel hij]

private theorem clock_pair_integral_eq_lag
    (φ : Circle →ᵇ ℝ) {B i j : ℕ} (hB : 0 < B) (hij : i ≤ j) :
    (∫ x : Circle,
      φ (B ^ i • x) * φ (B ^ j • x)) =
      ∫ x : Circle, φ x * φ (B ^ (j - i) • x) := by
  let F : Circle → ℝ := fun x ↦ φ x * φ (B ^ (j - i) • x)
  have hF : Continuous F := φ.continuous.mul
    (φ.continuous.comp (continuous_const_smul (B ^ (j - i))))
  have heq : (fun x : Circle ↦ F (B ^ i • x)) =
      fun x : Circle ↦ φ (B ^ i • x) * φ (B ^ j • x) := by
    funext x
    dsimp only [F]
    rw [smul_smul, pow_sub_mul_pow_eq hij]
  rw [← heq]
  exact integral_circleClock_eq (pow_pos hB i) F hF

private theorem one_div_pow_le_half_pow
    {B h : ℕ} (hB : 2 ≤ B) :
    1 / (((B ^ h : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ h := by
  have hpow : (2 : ℝ) ^ h ≤ (B : ℝ) ^ h := by
    exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hB) h
  have hinv : 1 / (B : ℝ) ^ h ≤ 1 / (2 : ℝ) ^ h :=
    one_div_le_one_div_of_le (pow_pos (by norm_num) h) hpow
  simpa only [Nat.cast_pow, one_div_pow] using hinv

/-- Pairwise covariance decay along the actual `B`-clock. -/
theorem abs_circleClock_pair_covariance_le
    (φ : Circle →ᵇ ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {V : ℝ}
    (hBV : BoundedVariationOn (circleLift (centeredCircleTest φ))
      (Icc (0 : ℝ) 1))
    (hV : circleVariation (centeredCircleTest φ) ≤ V)
    {B i j : ℕ} (hB : 2 ≤ B) :
    |∫ x : Circle,
      centeredCircleTest φ (B ^ i • x) *
        centeredCircleTest φ (B ^ j • x)| ≤
      V * (1 / 2 : ℝ) ^ Nat.dist i j := by
  have hV0 : 0 ≤ V := by
    have hh : 0 ≤ circleVariation (centeredCircleTest φ) := by
      unfold circleVariation unitVariation
      exact ENNReal.toReal_nonneg
    exact hh.trans hV
  rcases le_total i j with hij | hji
  · rw [clock_pair_integral_eq_lag (centeredCircleTest φ) (by omega) hij,
      Nat.dist_eq_sub_of_le hij]
    have hcov := abs_circleClock_covariance_le φ hφ0 hφ1 hBV hV
      (pow_pos (by omega : 0 < B) (j - i))
    exact hcov.trans (by
      have hh := one_div_pow_le_half_pow (h := j - i) hB
      simpa only [Nat.cast_pow, div_eq_mul_inv, one_div, one_mul] using
        mul_le_mul_of_nonneg_left hh hV0)
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji]
    have hswap :
        (∫ x : Circle,
          centeredCircleTest φ (B ^ i • x) * centeredCircleTest φ (B ^ j • x)) =
        ∫ x : Circle,
          centeredCircleTest φ (B ^ j • x) * centeredCircleTest φ (B ^ i • x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ mul_comm _ _
    rw [hswap, clock_pair_integral_eq_lag (centeredCircleTest φ) (by omega) hji]
    have hcov := abs_circleClock_covariance_le φ hφ0 hφ1 hBV hV
      (pow_pos (by omega : 0 < B) (i - j))
    exact hcov.trans (by
      have hh := one_div_pow_le_half_pow (h := i - j) hB
      simpa only [Nat.cast_pow, div_eq_mul_inv, one_div, one_mul] using
        mul_le_mul_of_nonneg_left hh hV0)

/-- Haar `L¹` time fluctuation of an actual expanding circle orbit.  In
particular, a variation-two interval ramp has bound `sqrt (6/T)`. -/
theorem integral_abs_circleClock_timeMean_le
    (φ : Circle →ᵇ ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {V : ℝ} (hVpos : 0 < V)
    (hBV : BoundedVariationOn (circleLift (centeredCircleTest φ))
      (Icc (0 : ℝ) 1))
    (hV : circleVariation (centeredCircleTest φ) ≤ V)
    {B T : ℕ} (hB : 2 ≤ B) (hT : 0 < T) :
    (∫ x : Circle,
      |CoreOrbitCovarianceVariance.finiteTimeMean
        (fun h x ↦ centeredCircleTest φ (B ^ h • x)) T x|) ≤
      Real.sqrt (3 * V / (T : ℝ)) := by
  let g : ℕ → Circle → ℝ := fun h x ↦ centeredCircleTest φ (B ^ h • x)
  have hg : ∀ i ∈ range T, Integrable (g i) (volume : Measure Circle) := by
    intro i hi
    let fi : Circle →ᵇ ℝ := (centeredCircleTest φ).compContinuous
      ⟨fun x ↦ B ^ i • x, continuous_const_smul (B ^ i)⟩
    exact BoundedContinuousFunction.integrable (volume : Measure Circle) fi
  have hprod : ∀ i ∈ range T, ∀ j ∈ range T,
      Integrable (fun x ↦ g i x * g j x) (volume : Measure Circle) := by
    intro i hi j hj
    let fi : Circle →ᵇ ℝ := (centeredCircleTest φ).compContinuous
      ⟨fun x ↦ B ^ i • x, continuous_const_smul (B ^ i)⟩
    let fj : Circle →ᵇ ℝ := (centeredCircleTest φ).compContinuous
      ⟨fun x ↦ B ^ j • x, continuous_const_smul (B ^ j)⟩
    exact BoundedContinuousFunction.integrable (volume : Measure Circle) (fi * fj)
  apply CoreOrbitCovarianceVariance.integral_abs_finiteTimeMean_le
    g hT hVpos hg hprod
  intro i hi j hj
  exact abs_circleClock_pair_covariance_le φ hφ0 hφ1 hBV hV hB

end

end PrimeGapNormality.Prime.CoreBVOrbitMixing
