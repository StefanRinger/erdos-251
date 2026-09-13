import PrimeGapNormality.Prime.CoreResidueDigitalReferenceLimit

/-!
# Exact limiting residue restriction coefficient

The finite count error is at most one, so the ratio of full-window length
to residue count tends to k. We retain this varying ratio until after the
weak limit, instead of replacing it by the coarse finite bound 2k.
The resulting domination uses the original supplied reference measure;
neither invariance nor equality with Haar measure is used here.
-/

namespace PrimeGapNormality.Prime.CoreResidueDominationSharp

open Filter Finset MeasureTheory
open CoreResidueDigitalReference
open scoped Topology NNReal BoundedContinuousFunction

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

/-- Exact asymptotic density of any fixed index residue in moving windows. -/
theorem residueCount_div_length_tendsto {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => (coreResidueWindowCount k r (a j) (N j) : ℝ) / (N j : ℝ))
      atTop (𝓝 ((1 : ℝ) / k)) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hNR : Tendsto (fun j => (N j : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hN
  have hi : Tendsto (fun j => (1 : ℝ) / (N j : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hNR
  have herr : Tendsto (fun j =>
      |(coreResidueWindowCount k r (a j) (N j) : ℝ) / (N j : ℝ) - 1 / k|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hi
    filter_upwards [hNR.eventually_gt_atTop 0] with j hj
    have hc := coreResidueWindowCount_abs_sub_div_le_one k r (a j) (N j) hk
    calc
      |(coreResidueWindowCount k r (a j) (N j) : ℝ) / (N j : ℝ) - 1 / k| =
          |((coreResidueWindowCount k r (a j) (N j) : ℝ) - (N j : ℝ) / k) /
            (N j : ℝ)| := by
        congr 1
        field_simp [hj.ne', hkpos.ne'] <;> ring
      _ = |(coreResidueWindowCount k r (a j) (N j) : ℝ) - (N j : ℝ) / k| /
          (N j : ℝ) := by rw [abs_div, abs_of_pos hj]
      _ ≤ 1 / (N j : ℝ) := div_le_div_of_nonneg_right hc hj.le
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using herr)

/-- The precise restriction factor tends to k, independently of starts. -/
theorem length_div_residueCount_tendsto {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => (N j : ℝ) / coreResidueWindowCount k r (a j) (N j))
      atTop (𝓝 (k : ℝ)) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hh := (residueCount_div_length_tendsto hk r a N hN).inv₀
    (ne_of_gt (div_pos zero_lt_one hkpos))
  simpa only [inv_div, inv_one, div_one] using hh

/-- Every actual residue weak limit inherits coefficient k*A from a
fixed full-window reference bound. The reference is not replaced by Haar. -/
theorem weak_limit_le_reference {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → Circle) (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ProbabilityMeasure Circle)
    (hweak : Tendsto (fun j => residueMeasure hk r u (a j) (N j)) atTop (𝓝 μ))
    (σ : Measure Circle) [IsFiniteMeasure σ] {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ (f : Circle →ᵇ ℝ) (K : ℝ≥0), LipschitzWith K f →
      (∀ x, 0 ≤ f x) → ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * (∫ x, f x ∂σ) + ε) :
    (μ : Measure Circle) ≤ ENNReal.ofReal ((k : ℝ) * A) • σ := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hratio := length_div_residueCount_tendsto hk r a N hN
  have hM := count_tendsto_atTop hk r a N hN
  letI : IsFiniteMeasure (ENNReal.ofReal ((k : ℝ) * A) • σ) :=
    Measure.smul_finite σ ENNReal.ofReal_ne_top
  apply coreDigital_measure_le_of_positive_lipschitz_tests
  intro f K hK hf
  rw [integral_smul_measure, ENNReal.toReal_ofReal (mul_nonneg hkpos.le hA), smul_eq_mul]
  have htest : Tendsto (fun j => coreResidueWindowAverage k r u f (a j) (N j))
      atTop (𝓝 (∫ x, f x ∂(μ : Measure Circle))) := by
    have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f
    apply hh.congr'
    filter_upwards [hM.eventually_gt_atTop 0] with j hj
    exact residueMeasure_integral hk r u (a j) (N j) hj f
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < ε / (k : ℝ) := div_pos hε hkpos
  have hmajor := hratio.mul_const (A * (∫ x, f x ∂σ) + ε / (k : ℝ))
  have hle : (∫ x, f x ∂(μ : Measure Circle)) ≤
      (k : ℝ) * (A * (∫ x, f x ∂σ) + ε / (k : ℝ)) := by
    apply le_of_tendsto_of_tendsto htest hmajor
    filter_upwards [hN.eventually_gt_atTop 0, hM.eventually_gt_atTop 0,
      hbound f K hK hf (ε / (k : ℝ)) hδ] with j hNj hMj hfull
    have hres := coreResidueWindowAverage_le_countRatio_mul_full
      (k := k) (r := r) u f hNj hMj (fun i _ => hf _)
    exact hres.trans (mul_le_mul_of_nonneg_left hfull
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  exact hle.trans_eq (by field_simp [hkpos.ne'] <;> ring)

end
end PrimeGapNormality.Prime.CoreResidueDominationSharp
