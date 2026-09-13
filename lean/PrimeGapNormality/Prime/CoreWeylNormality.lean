import PrimeGapNormality.Prime.CoreCircleDigitCylinders

/-! The generic bridge from the project's Fourier Weyl criterion to its
existing literal digit-cylinder frequency definition of Borel normality.
No arithmetic or new distribution hypothesis occurs in this adapter. -/

namespace PrimeGapNormality.Prime.CoreWeylNormality

open Set Filter MeasureTheory Finset
open scoped Topology ENNReal Classical

noncomputable section

/-- Weyl's criterion implies the actual base-digit frequency predicate
already defined in `BFree.Definitions`, for every base at least two. -/
theorem isNormal_of_weyl {B : ℕ} {α : ℝ} (hB : 2 ≤ B)
    (hW : weylCriterion B α) : PrimeGapNormality.BFree.IsNormal B α := by
  intro K v hv
  by_cases hK : K = 0
  · subst K
    have hv0 : v = 0 := by simpa using hv
    subst v
    simp only [pow_zero, inv_one]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp [PrimeGapNormality.BFree.digitCylinder, Int.fract_nonneg,
      Int.fract_lt_one, Nat.ne_of_gt hN]
  have hBr : 1 < (B : ℝ) := Nat.one_lt_cast.2 (by omega)
  have hd : 1 < (B : ℝ) ^ K := one_lt_pow₀ hBr hK
  have hd0 : 0 < (B : ℝ) ^ K := zero_lt_one.trans hd
  let a : ℝ := (v : ℝ) / (B : ℝ) ^ K
  let b : ℝ := (v + 1 : ℝ) / (B : ℝ) ^ K
  have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hd0.le
  have hb : b ≤ 1 := by
    apply (div_le_one hd0).2
    exact_mod_cast Nat.succ_le_of_lt hv
  have hdiff : b - a = ((B : ℝ) ^ K)⁻¹ := by
    dsimp only [a, b]
    field_simp [hd0.ne']
    <;> ring
  have hwidth : b < a + 1 := by
    have hi : ((B : ℝ) ^ K)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hd
    linarith
  have hmeas := measurableSet_arc hwidth
  have hmass : (volume (arc a b)).toReal = ((B : ℝ) ^ K)⁻¹ := by
    rw [volume_arc hwidth, ENNReal.toReal_ofReal (by rw [hdiff]; positivity), hdiff]
  have hboundary : (coreCircleVolume : Measure (AddCircle (1 : ℝ)))
      (frontier (arc a b)) = 0 := frontier_arc_null a b
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (empirical_tendsto_of_weyl hW) hboundary
  have hreal := (ENNReal.tendsto_toReal
    (measure_ne_top (volume : Measure (AddCircle (1 : ℝ))) (arc a b))).comp hlim
  have hlimit : Tendsto
      (fun N ↦ (empirical B α N : Measure (AddCircle (1 : ℝ))).real (arc a b))
      atTop (𝓝 (((B : ℝ) ^ K)⁻¹)) := by
    simpa only [Measure.real, Function.comp_def, hmass] using hreal
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [empirical_real_apply B α hN (arc a b) hmeas]
  have hfilter : (range N).filter (fun n ↦ orbit B α n ∈ arc a b) =
      (range N).filter (fun n ↦ Int.fract ((B : ℝ) ^ n * α) ∈
        PrimeGapNormality.BFree.digitCylinder B K v) := by
    apply Finset.filter_congr
    intro n _
    exact coe_mem_arc_iff_fract ha hb ((B : ℝ) ^ n * α)
  rw [hfilter]

end

end PrimeGapNormality.Prime.CoreWeylNormality
