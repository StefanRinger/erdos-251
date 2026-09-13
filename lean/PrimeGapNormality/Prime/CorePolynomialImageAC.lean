import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Algebra.Polynomial

/-!
The image of Lebesgue measure under a nonconstant real polynomial is
absolutely continuous. Critical points are finite, and away from them the
one-dimensional change-of-variables formula applies on monotone intervals.
The proof makes no uniform bounded-density assertion near critical values.
-/

namespace PrimeGapNormality.Prime.CorePolynomialImage

open Set Filter MeasureTheory
open scoped Polynomial Topology ENNReal

noncomputable section

/-- Nonconstant polynomials have only finitely many critical points. -/
theorem finite_critical_set (P : ℝ[X]) (hP : 0 < P.natDegree) :
    Set.Finite {x : ℝ | P.derivative.eval x = 0} := by
  have hd : P.derivative ≠ 0 := Polynomial.derivative_ne_zero.2 (Nat.ne_of_gt hP)
  simpa only [Polynomial.IsRoot] using Polynomial.finite_setOfPred_isRoot hd

theorem critical_set_null (P : ℝ[X]) (hP : 0 < P.natDegree) :
    volume {x : ℝ | P.derivative.eval x = 0} = 0 :=
  (finite_critical_set P hP).measure_zero volume

/-- The Jacobian formula turns a null image into a null domain on any
injective measurable piece with nonvanishing derivative. -/
theorem null_preimage_on_injective_piece (P : ℝ[X]) {I s : Set ℝ}
    (hI : MeasurableSet I) (hs : MeasurableSet s) (hs0 : volume s = 0)
    (hinj : InjOn P.eval I) (hder : ∀ x ∈ I, P.derivative.eval x ≠ 0) :
    volume (I ∩ P.eval ⁻¹' s) = 0 := by
  let T : Set ℝ := I ∩ P.eval ⁻¹' s
  have hT : MeasurableSet T := hI.inter (hs.preimage P.continuous.measurable)
  have himage : volume (P.eval '' T) = 0 :=
    measure_mono_null (fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := hy
      exact hx.2) hs0
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
    (f := P.eval) (f' := P.derivative.eval) hT
    (fun x _ ↦ (P.hasDerivAt x).hasDerivWithinAt)
    (hinj.mono inter_subset_left) (fun _ ↦ (1 : ℝ≥0∞))
  have hlin : (∫⁻ x in T, ENNReal.ofReal |P.derivative.eval x|) = 0 := by
    simpa only [mul_one, lintegral_one, Measure.restrict_apply_univ, himage] using
      hchange.symm
  have hae : ∀ᵐ x ∂volume, x ∈ T → ENNReal.ofReal |P.derivative.eval x| = 0 :=
    (setLIntegral_eq_zero_iff hT P.derivative.continuous.abs.measurable.ennreal_ofReal).1 hlin
  have hnot : ∀ᵐ x ∂volume, x ∉ T := hae.mono fun x hx hxt ↦ by
    have hpos : 0 < ENNReal.ofReal |P.derivative.eval x| :=
      ENNReal.ofReal_pos.2 (abs_pos.2 (hder x hxt.1))
    exact hpos.ne' (hx hxt)
  simpa only [not_not, Set.setOf_mem_eq] using (ae_iff.1 hnot)

/-- A noncritical point has an open interval on which the polynomial is
injective and its derivative remains nonzero. -/
theorem exists_injective_interval (P : ℝ[X]) {x : ℝ}
    (hx : P.derivative.eval x ≠ 0) :
    ∃ a b : ℝ, x ∈ Ioo a b ∧ InjOn P.eval (Ioo a b) ∧
      ∀ y ∈ Ioo a b, P.derivative.eval y ≠ 0 := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hnhds : {y : ℝ | P.derivative.eval y < 0} ∈ 𝓝 x :=
      (isOpen_lt P.derivative.continuous continuous_const).mem_nhds hneg
    obtain ⟨a, b, hxab, hab⟩ := mem_nhds_iff_exists_Ioo_subset.1 hnhds
    refine ⟨a, b, hxab, ?_, fun y hy ↦ (hab hy).ne⟩
    apply StrictAntiOn.injOn
    apply strictAntiOn_of_deriv_neg (convex_Ioo a b) P.continuous.continuousOn
    intro y hy
    rw [P.deriv]
    exact hab (interior_subset hy)
  · have hnhds : {y : ℝ | 0 < P.derivative.eval y} ∈ 𝓝 x :=
      (isOpen_lt continuous_const P.derivative.continuous).mem_nhds hpos
    obtain ⟨a, b, hxab, hab⟩ := mem_nhds_iff_exists_Ioo_subset.1 hnhds
    refine ⟨a, b, hxab, ?_, fun y hy ↦ (hab hy).ne'⟩
    apply StrictMonoOn.injOn
    apply strictMonoOn_of_deriv_pos (convex_Ioo a b) P.continuous.continuousOn
    intro y hy
    rw [P.deriv]
    exact hab (interior_subset hy)

/-- Preimages of null sets are null away from the critical set. This part
does not even require that the polynomial be nonconstant. -/
theorem null_preimage_off_critical (P : ℝ[X]) {s : Set ℝ}
    (hs : MeasurableSet s) (hs0 : volume s = 0) :
    volume (P.eval ⁻¹' s \ {x : ℝ | P.derivative.eval x = 0}) = 0 := by
  let E : Set ℝ := P.eval ⁻¹' s \ {x : ℝ | P.derivative.eval x = 0}
  apply measure_null_of_locally_null E
  intro x hx
  obtain ⟨a, b, hxab, hinj, hder⟩ := exists_injective_interval P hx.2
  refine ⟨E ∩ Ioo a b, inter_mem_nhdsWithin E (Ioo_mem_nhds hxab.1 hxab.2), ?_⟩
  have hsub : E ∩ Ioo a b ⊆ Ioo a b ∩ P.eval ⁻¹' s :=
    fun y hy ↦ ⟨hy.2, hy.1.1⟩
  exact measure_mono_null hsub
    (null_preimage_on_injective_piece P measurableSet_Ioo hs hs0 hinj hder)

/-- The critical-set exception is finite, so no derivative hypothesis
remains in the null-preimage theorem for a nonconstant polynomial. -/
theorem null_preimage (P : ℝ[X]) (hP : 0 < P.natDegree) {s : Set ℝ}
    (hs : MeasurableSet s) (hs0 : volume s = 0) :
    volume (P.eval ⁻¹' s) = 0 := by
  have hoff := null_preimage_off_critical P hs hs0
  have hcrit := critical_set_null P hP
  apply measure_mono_null
    (show P.eval ⁻¹' s ⊆
      (P.eval ⁻¹' s \ {x : ℝ | P.derivative.eval x = 0}) ∪
        {x : ℝ | P.derivative.eval x = 0} from fun x hx ↦ by
      by_cases hd : P.derivative.eval x = 0
      · exact Or.inr hd
      · exact Or.inl ⟨hx, hd⟩)
  exact measure_union_null hoff hcrit

/-- Global absolute continuity; the pushforward need not have bounded
density at critical values, and no such estimate is used. -/
theorem map_volume_absolutelyContinuous (P : ℝ[X]) (hP : 0 < P.natDegree) :
    Measure.map P.eval volume ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [Measure.map_apply P.continuous.measurable hs]
  exact null_preimage P hP hs hs0

/-- In particular, every restriction to a finite interval has an absolutely
continuous polynomial image. The stronger statement allows any set `I`. -/
theorem map_restrict_absolutelyContinuous (P : ℝ[X]) (hP : 0 < P.natDegree)
    (I : Set ℝ) : Measure.map P.eval (volume.restrict I) ≪ volume :=
  (Measure.map_mono Measure.restrict_le_self P.continuous.measurable).absolutelyContinuous.trans
    (map_volume_absolutelyContinuous P hP)

theorem map_interval_absolutelyContinuous (P : ℝ[X]) (hP : 0 < P.natDegree)
    (a b : ℝ) : Measure.map P.eval (volume.restrict (Icc a b)) ≪ volume :=
  map_restrict_absolutelyContinuous P hP (Icc a b)

/-- Equivalent nonconstancy formulation, with no degree or derivative
condition in the interface. -/
theorem map_restrict_absolutelyContinuous_of_nonconstant (P : ℝ[X])
    (hP : ∀ c : ℝ, P ≠ Polynomial.C c) (I : Set ℝ) :
    Measure.map P.eval (volume.restrict I) ≪ volume := by
  apply map_restrict_absolutelyContinuous
  by_contra hdeg
  exact hP (P.coeff 0) (Polynomial.eq_C_of_natDegree_eq_zero (by omega))

end

end PrimeGapNormality.Prime.CorePolynomialImage
