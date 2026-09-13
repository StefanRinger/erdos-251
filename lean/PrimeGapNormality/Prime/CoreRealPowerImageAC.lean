import PrimeGapNormality.Prime.CorePolynomialImageAC
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Absolutely continuous images of two complementary real powers

Only the actual open fibre (0,W) is mapped. Its two bases are strictly
positive. The derivative has at most one zero, by injectivity of
t/(W-t) and of a nonzero real power on positive numbers. The local
one-dimensional Jacobian argument is the same as CorePolynomialImageAC;
no global clamp, globally nonvanishing derivative, or bounded density is
asserted. The affine a=1 endpoint is handled separately.
-/

namespace PrimeGapNormality.Prime.CoreRealPowerImageAC

open Set Filter MeasureTheory
open scoped Topology ENNReal Polynomial
noncomputable section
set_option maxHeartbeats 1000000

def action (W a A C : ℝ) (t : ℝ) : ℝ := A * t ^ a + C * (W - t) ^ a
def actionDeriv (W a A C : ℝ) (t : ℝ) : ℝ :=
  a * (A * t ^ (a - 1) - C * (W - t) ^ (a - 1))

theorem continuous_action (W A C : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    Continuous (action W a A C) :=
  (continuous_const.mul (Real.continuous_rpow_const ha)).add
    (continuous_const.mul ((Real.continuous_rpow_const ha).comp (continuous_const.sub continuous_id)))

theorem measurable_actionDeriv (W a A C : ℝ) : Measurable (actionDeriv W a A C) := by
  exact measurable_const.mul
    ((measurable_const.mul (measurable_id.pow_const (a - 1))).sub
      (measurable_const.mul ((measurable_const.sub measurable_id).pow_const (a - 1))))

theorem hasDerivAt_action (W a A C : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 W) :
    HasDerivAt (action W a A C) (actionDeriv W a A C t) t := by
  have hleft := ((hasDerivAt_id t).rpow_const
    (Or.inl ht.1.ne' : t ≠ 0 ∨ 1 ≤ a)).const_mul A
  have hright := (((hasDerivAt_const t W).sub (hasDerivAt_id t)).rpow_const
    (Or.inl (sub_pos.mpr ht.2).ne' : W - t ≠ 0 ∨ 1 ≤ a)).const_mul C
  have hsum := hleft.add hright
  change HasDerivAt (action W a A C)
    (A * (1 * a * t ^ (a - 1)) +
      C * ((0 - 1) * a * (W - t) ^ (a - 1))) t at hsum
  have hcoef :
      A * (1 * a * t ^ (a - 1)) +
        C * ((0 - 1) * a * (W - t) ^ (a - 1)) =
      actionDeriv W a A C t := by
    dsimp only [actionDeriv]
    ring
  rw [hcoef] at hsum
  exact hsum

theorem continuousAt_actionDeriv (W a A C : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 W) :
    ContinuousAt (actionDeriv W a A C) t := by
  exact continuousAt_const.mul
    ((continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl ht.1.ne'))).sub
      (continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).rpow_const
        (Or.inl (sub_pos.mpr ht.2).ne'))))

theorem strictMonoOn_ratio {W : ℝ} (hW : 0 < W) :
    StrictMonoOn (fun t : ℝ => t / (W - t)) (Ioo 0 W) := by
  intro x hx y hy hxy
  apply (div_lt_div_iff₀ (sub_pos.mpr hx.2) (sub_pos.mpr hy.2)).2
  have hh := mul_lt_mul_of_pos_left hxy hW
  nlinarith

theorem critical_ratio {W a A C t : ℝ} (ha : 0 < a) (hA : A ≠ 0)
    (ht : t ∈ Ioo 0 W) (hd : actionDeriv W a A C t = 0) :
    (t / (W - t)) ^ (a - 1) = C / A := by
  have hzero : A * t ^ (a - 1) - C * (W - t) ^ (a - 1) = 0 :=
    (mul_eq_zero.mp hd).resolve_left ha.ne'
  have hp : 0 < (W - t) ^ (a - 1) := Real.rpow_pos_of_pos (sub_pos.mpr ht.2) _
  rw [Real.div_rpow ht.1.le (sub_pos.mpr ht.2).le]
  apply (div_eq_div_iff hp.ne' hA).2
  linarith

/-- The entire critical set INSIDE the open fibre has at most one point,
including arbitrary C and either sign of the nonzero A. -/
theorem critical_set_subsingleton {W a A C : ℝ} (hW : 0 < W) (ha : 0 < a)
    (ha1 : a < 1) (hA : A ≠ 0) :
    {t : ℝ | t ∈ Ioo 0 W ∧ actionDeriv W a A C t = 0}.Subsingleton := by
  intro x hx y hy
  apply (strictMonoOn_ratio hW).injOn hx.1 hy.1
  apply (Real.rpow_left_inj (div_nonneg hx.1.1.le (sub_pos.mpr hx.1.2).le)
    (div_nonneg hy.1.1.le (sub_pos.mpr hy.1.2).le) (by linarith : a - 1 ≠ 0)).mp
  exact (critical_ratio ha hA hx.1 hx.2).trans (critical_ratio ha hA hy.1 hy.2).symm

theorem critical_set_null {W a A C : ℝ} (hW : 0 < W) (ha : 0 < a)
    (ha1 : a < 1) (hA : A ≠ 0) :
    volume {t : ℝ | t ∈ Ioo 0 W ∧ actionDeriv W a A C t = 0} = 0 :=
  (critical_set_subsingleton hW ha ha1 hA).finite.measure_zero volume

/-- A noncritical interior point has an injective interval entirely
inside the physical fibre; no regularity at 0 or W is needed. -/
theorem exists_injective_interval {W a A C t : ℝ} (ha : 0 < a)
    (ht : t ∈ Ioo 0 W) (hd : actionDeriv W a A C t ≠ 0) :
    ∃ l r : ℝ, t ∈ Ioo l r ∧ Ioo l r ⊆ Ioo 0 W ∧
      InjOn (action W a A C) (Ioo l r) ∧
      ∀ x ∈ Ioo l r, actionDeriv W a A C x ≠ 0 := by
  have hc := continuousAt_actionDeriv W a A C ht
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hn : {x : ℝ | actionDeriv W a A C x < 0} ∈ 𝓝 t :=
      hc.preimage_mem_nhds (Iio_mem_nhds hneg)
    obtain ⟨l, r, htr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
      (Filter.inter_mem (Ioo_mem_nhds ht.1 ht.2) hn)
    refine ⟨l, r, htr, fun x hx => (hsub hx).1, ?_, fun x hx => (hsub hx).2.ne⟩
    apply StrictAntiOn.injOn
    apply strictAntiOn_of_deriv_neg (convex_Ioo l r) (continuous_action W A C ha.le).continuousOn
    intro x hx
    rw [(hasDerivAt_action W a A C (hsub (interior_subset hx)).1).deriv]
    exact (hsub (interior_subset hx)).2
  · have hn : {x : ℝ | 0 < actionDeriv W a A C x} ∈ 𝓝 t :=
      hc.preimage_mem_nhds (Ioi_mem_nhds hpos)
    obtain ⟨l, r, htr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
      (Filter.inter_mem (Ioo_mem_nhds ht.1 ht.2) hn)
    refine ⟨l, r, htr, fun x hx => (hsub hx).1, ?_, fun x hx => (hsub hx).2.ne'⟩
    apply StrictMonoOn.injOn
    apply strictMonoOn_of_deriv_pos (convex_Ioo l r) (continuous_action W A C ha.le).continuousOn
    intro x hx
    rw [(hasDerivAt_action W a A C (hsub (interior_subset hx)).1).deriv]
    exact (hsub (interior_subset hx)).2

/-- The actual Jacobian formula, with the null target and a derivative
which is nonzero on this injective measurable piece. -/
theorem null_preimage_on_injective_piece {W a A C : ℝ} (ha : 0 < a)
    {I s : Set ℝ} (hI : MeasurableSet I) (hIfibre : I ⊆ Ioo 0 W)
    (hs : MeasurableSet s) (hs0 : volume s = 0)
    (hinj : InjOn (action W a A C) I) (hd : ∀ x ∈ I, actionDeriv W a A C x ≠ 0) :
    volume (I ∩ action W a A C ⁻¹' s) = 0 := by
  let T := I ∩ action W a A C ⁻¹' s
  have hT : MeasurableSet T := hI.inter (hs.preimage (continuous_action W A C ha.le).measurable)
  have himage : volume (action W a A C '' T) = 0 :=
    measure_mono_null (fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact hx.2) hs0
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
    (f := action W a A C) (f' := actionDeriv W a A C) hT
    (fun x hx => (hasDerivAt_action W a A C (hIfibre hx.1)).hasDerivWithinAt)
    (hinj.mono inter_subset_left) (fun _ => (1 : ℝ≥0∞))
  have hlin : (∫⁻ x in T, ENNReal.ofReal |actionDeriv W a A C x|) = 0 := by
    simpa only [mul_one, lintegral_one, Measure.restrict_apply_univ, himage] using hchange.symm
  have hae : ∀ᵐ x ∂volume, x ∈ T → ENNReal.ofReal |actionDeriv W a A C x| = 0 :=
    (setLIntegral_eq_zero_iff hT
      (continuous_abs.measurable.comp (measurable_actionDeriv W a A C)).ennreal_ofReal).1 hlin
  have hnot : ∀ᵐ x ∂volume, x ∉ T := hae.mono fun x hx hxt => by
    have hp : 0 < ENNReal.ofReal |actionDeriv W a A C x| :=
      ENNReal.ofReal_pos.2 (abs_pos.2 (hd x hxt.1))
    exact hp.ne' (hx hxt)
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.1 hnot

theorem null_preimage_off_critical {W a A C : ℝ} (ha : 0 < a)
    {s : Set ℝ} (hs : MeasurableSet s) (hs0 : volume s = 0) :
    volume ((Ioo 0 W ∩ action W a A C ⁻¹' s) \
      {t : ℝ | t ∈ Ioo 0 W ∧ actionDeriv W a A C t = 0}) = 0 := by
  let E := (Ioo 0 W ∩ action W a A C ⁻¹' s) \
    {t : ℝ | t ∈ Ioo 0 W ∧ actionDeriv W a A C t = 0}
  apply measure_null_of_locally_null E
  intro x hx
  have hd : actionDeriv W a A C x ≠ 0 := fun hh => hx.2 ⟨hx.1.1, hh⟩
  obtain ⟨l, r, hxr, hsub, hinj, hder⟩ := exists_injective_interval ha hx.1.1 hd
  refine ⟨E ∩ Ioo l r, inter_mem_nhdsWithin E (Ioo_mem_nhds hxr.1 hxr.2), ?_⟩
  have hsub' : E ∩ Ioo l r ⊆ Ioo l r ∩ action W a A C ⁻¹' s :=
    fun y hy => ⟨hy.2, hy.1.1.2⟩
  exact measure_mono_null hsub'
    (null_preimage_on_injective_piece ha measurableSet_Ioo hsub hs hs0 hinj hder)

theorem null_preimage {W a A C : ℝ} (hW : 0 < W) (ha : 0 < a)
    (ha1 : a < 1) (hA : A ≠ 0) {s : Set ℝ} (hs : MeasurableSet s) (hs0 : volume s = 0) :
    volume (Ioo 0 W ∩ action W a A C ⁻¹' s) = 0 := by
  have hoff := null_preimage_off_critical (W := W) (A := A) (C := C) ha hs hs0
  have hcrit := critical_set_null (C := C) hW ha ha1 hA
  apply measure_mono_null
    (show Ioo 0 W ∩ action W a A C ⁻¹' s ⊆
      ((Ioo 0 W ∩ action W a A C ⁻¹' s) \
        {t : ℝ | t ∈ Ioo 0 W ∧ actionDeriv W a A C t = 0}) ∪
        {t : ℝ | t ∈ Ioo 0 W ∧ actionDeriv W a A C t = 0} from fun x hx => by
      by_cases hd : actionDeriv W a A C x = 0
      · exact Or.inr ⟨hx.1, hd⟩
      · exact Or.inl ⟨hx, fun hh => hd hh.2⟩)
  exact measure_union_null hoff hcrit

/-- The real-power fibre image is absolutely continuous on its actual
open physical interval. There is no derivative/nonconstancy premise left
besides the explicit coefficients and exponent of the requested action. -/
theorem map_interval_absolutelyContinuous {W a A C : ℝ}
    (hW : 0 < W) (ha : 0 < a) (ha1 : a < 1) (hA : A ≠ 0) :
    Measure.map (action W a A C) (volume.restrict (Ioo 0 W)) ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [Measure.map_apply (continuous_action W A C ha.le).measurable hs,
    Measure.restrict_apply (hs.preimage (continuous_action W A C ha.le).measurable), inter_comm]
  exact null_preimage hW ha ha1 hA hs hs0

/-- At exponent one the correct condition is A-C != 0; when A=C the
action is constant and its nonzero interval image is an atom. -/
theorem map_interval_absolutelyContinuous_one (W A C : ℝ) (hAC : A - C ≠ 0) :
    Measure.map (action W 1 A C) (volume.restrict (Ioo 0 W)) ≪ volume := by
  let P : ℝ[X] := Polynomial.C (C * W) + Polynomial.C (A - C) * Polynomial.X
  have hP : ∀ c : ℝ, P ≠ Polynomial.C c := by
    intro c hc
    have hh := congrArg (fun Q : ℝ[X] => Q.coeff 1) hc
    have heq : A - C = 0 := by simpa [P] using hh
    exact hAC heq
  have heval : action W 1 A C = P.eval := by
    funext t
    simp only [action, Real.rpow_one, P, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    ring
  rw [heval]
  exact CorePolynomialImage.map_restrict_absolutelyContinuous_of_nonconstant P hP (Ioo 0 W)

end
end PrimeGapNormality.Prime.CoreRealPowerImageAC
