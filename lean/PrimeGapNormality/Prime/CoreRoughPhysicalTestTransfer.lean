import PrimeGapNormality.Prime.CoreRoughPhysicalSlices
import PrimeGapNormality.Prime.CoreSequencePatternLaw

/-!
# Bounded tests: scalar normalization and the one discarded interval

The full-cell empirical law has denominator Z, whereas the literal sequence
law has denominator the actual dyadic root count. The finite estimate below
compares these laws on every bounded configuration test uniformly. Its error
is a scalar function of the two masses and the single discarded cell.
No inclusion/Janossy multiplicity is charged to this discarded interval.
-/

namespace PrimeGapNormality.Prime.CoreRoughPhysicalTestTransfer

open Finset Filter
open CoreMovingRoughSequence CoreRoughThreshold CoreRoughCellAsymptotics
  CoreRoughPhysicalSlices CoreRoughSliceLaws CoreSequencePatternLaw
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1000000

private theorem abs_sum_le_card (A : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ n ∈ A, |f n| ≤ 1) : |∑ n ∈ A, f n| ≤ (A.card : ℝ) := by
  calc
    _ ≤ ∑ n ∈ A, |f n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ A, (1 : ℝ) := Finset.sum_le_sum hf
    _ = _ := by simp

/-- General finite sub-sample normalization estimate, allowing an empty
sub-sample but retaining positivity of the two denominators. -/
theorem normalized_subset_test_bound {A B : Finset ℕ} (hAB : A ⊆ B)
    {Z : ℝ} (hZ : 0 < Z) (hB : 0 < B.card) (f : ℕ → ℝ)
    (hf : ∀ n ∈ B, |f n| ≤ 1) :
    |(∑ n ∈ B, f n) / (B.card : ℝ) - (∑ n ∈ A, f n) / Z| ≤
      ((B.card : ℝ) - A.card) / (B.card : ℝ) +
        |(A.card : ℝ) / (B.card : ℝ) - (A.card : ℝ) / Z| := by
  have hN : (0 : ℝ) < B.card := Nat.cast_pos.mpr hB
  have hs := Finset.sum_sdiff (f := f) hAB
  have hdiff : |(∑ n ∈ B, f n) - ∑ n ∈ A, f n| ≤
      (B.card : ℝ) - A.card := by
    rw [← hs, add_sub_cancel_right]
    have hh := abs_sum_le_card (B \ A) f (fun n hn => hf n (mem_sdiff.mp hn).1)
    rw [card_sdiff_of_subset hAB, Nat.cast_sub (card_le_card hAB)] at hh
    exact hh
  have hsum := abs_sum_le_card A f (fun n hn => hf n (hAB hn))
  calc
    _ = |((∑ n ∈ B, f n) - ∑ n ∈ A, f n) / (B.card : ℝ) +
        (∑ n ∈ A, f n) * (1 / (B.card : ℝ) - 1 / Z)| := by congr 1; ring
    _ ≤ |((∑ n ∈ B, f n) - ∑ n ∈ A, f n) / (B.card : ℝ)| +
        |(∑ n ∈ A, f n) * (1 / (B.card : ℝ) - 1 / Z)| := abs_add_le _ _
    _ ≤ ((B.card : ℝ) - A.card) / (B.card : ℝ) +
        (A.card : ℝ) * |1 / (B.card : ℝ) - 1 / Z| := by
      rw [abs_div, abs_of_pos hN, abs_mul]
      exact _root_.add_le_add (div_le_div_of_nonneg_right hdiff hN.le)
        (mul_le_mul_of_nonneg_right hsum (abs_nonneg _))
    _ = _ := by
      congr 1
      calc
        (A.card : ℝ) * |1 / (B.card : ℝ) - 1 / Z| =
            |(A.card : ℝ) * (1 / (B.card : ℝ) - 1 / Z)| := by
          have hAabs : |(A.card : ℝ)| = (A.card : ℝ) :=
            abs_of_nonneg (Nat.cast_nonneg A.card)
          rw [abs_mul, hAabs]
        _ = |(A.card : ℝ) / (B.card : ℝ) - (A.card : ℝ) / Z| := by
          congr 1
          ring

theorem anchors_subset_raw (J X : ℕ) (Ψ : ℝ → ℝ) :
    anchors (zPsi Ψ) (X + 1) (roughCellLength J X) (cellCount J X) ⊆
      rawPhysicalRoots (zPsi Ψ) X := by
  intro n hn
  obtain ⟨hnI, hnR⟩ := mem_filter.mp hn
  have hi := mem_Ico.mp hnI
  have hc := coveredLength_le J X
  change cellCount J X * roughCellLength J X ≤ X at hc
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hnR⟩

theorem rootedPattern_eq_anchorPattern {z : ℕ → ℕ}
    (hz : ∀ᶠ n : ℕ in atTop, z n < n) (Ω : Finset ℕ) (n : ℕ) :
    CoreSequencePatternLaw.rootedPattern (movingRoughSequence z) Ω n =
      anchorPattern z Ω (movingRoughSequence z n) := by
  ext h
  simp only [CoreSequencePatternLaw.rootedPattern, CoreSequencePattern.pattern, anchorPattern, mem_filter]
  exact and_congr_right fun _ => exists_movingRoughSequence_eq_iff hz _

/-- Exact equality between the actual index-window law and its physical
root pushforward. There is no stationary/independence premise. -/
theorem patternMass_eval_raw {z : ℕ → ℕ}
    (hz : ∀ᶠ n : ℕ in atTop, z n < n) (X : ℕ) (Ω : Finset ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ U ∈ Ω.powerset, patternMass (movingRoughSequence z) X Ω U * f U) =
      (∑ n ∈ rawPhysicalRoots z X, f (anchorPattern z Ω n)) /
        ((rawPhysicalRoots z X).card : ℝ) := by
  rw [patternMass_eval, rawPhysicalRoots_card_eq_seqWindow hz,
    rawPhysicalRoots_eq_image_seqWindow hz,
    Finset.sum_image (fun n hn m hm hnm => (movingRoughSequence_strictMono hz).injective hnm)]
  simp only [rootedPattern_eq_anchorPattern hz]

def normalizationError (J : ℕ) (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  (roughCellLength J X : ℝ) / ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) +
    |((anchors (zPsi Ψ) (X + 1) (roughCellLength J X) (cellCount J X)).card : ℝ) /
        ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) -
      ((anchors (zPsi Ψ) (X + 1) (roughCellLength J X) (cellCount J X)).card : ℝ) /
        rootNormalization J Ψ X|

theorem bounded_test_error_le {Ψ : ℝ → ℝ} {A : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (J X S : ℕ)
    (hH : 0 < roughCellLength J X) (hZ : 0 < rootNormalization J Ψ X)
    (hN : 0 < (rawPhysicalRoots (zPsi Ψ) X).card)
    (f : Finset ℕ → ℝ) (hf : ∀ U ∈ (offsetWindow S).powerset, |f U| ≤ 1) :
    |(∑ U ∈ (offsetWindow S).powerset,
        patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow S) U * f U) -
      (∑ U ∈ (offsetWindow S).powerset,
        empiricalLaw (zPsi Ψ) (cellCutoff J Ψ X) (X + 1)
          (roughCellLength J X) (cellCount J X) S U * f U)| ≤ normalizationError J Ψ X := by
  rw [patternMass_eval_raw hSlope.eventually_zPsi_lt, empiricalLaw_eval]
  have hh := normalized_subset_test_bound (anchors_subset_raw J X Ψ) hZ hN
    (fun n => f (anchorPattern (zPsi Ψ) (offsetWindow S) n))
    (fun n _ => hf _ (anchorPattern_mem _ _ _))
  have hcard := full_cell_count_error_le J X Ψ
  have hcard' := (neg_le_abs _).trans hcard
  have hround : ((X % roughCellLength J X : ℕ) : ℝ) ≤ roughCellLength J X :=
    Nat.cast_le.mpr (Nat.mod_lt X hH).le
  have hnreal : (0 : ℝ) < (rawPhysicalRoots (zPsi Ψ) X).card := Nat.cast_pos.mpr hN
  have hd := div_le_div_of_nonneg_right
    (show ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ) -
      (anchors (zPsi Ψ) (X + 1) (roughCellLength J X) (cellCount J X)).card ≤
        (roughCellLength J X : ℝ) by linarith) hnreal.le
  exact hh.trans (_root_.add_le_add hd le_rfl)

theorem tendsto_normalizationError_zero {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) :
    Tendsto (normalizationError J Ψ) atTop (𝓝 0) := by
  have hN := CoreRoughDyadicDensity.tendsto_rawPhysicalRoots_div_main_one hSlope hC hreg
  have hM := tendsto_full_cell_count_div_main_one hSlope hC hreg hJ
  have hZ := tendsto_rootNormalization_div_main_one hSlope hC hreg hJ
  have hδ := tendsto_cellLength_div_main_zero hSlope hJ
  have hδN : Tendsto (fun X : ℕ => (roughCellLength J X : ℝ) /
      ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ)) atTop (𝓝 0) := by
    have hh := hδ.div hN (by norm_num : (1 : ℝ) ≠ 0)
    simp only [zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    change _ / mainMass Ψ X / (_ / mainMass Ψ X) = _
    exact div_div_div_cancel_right₀ (mainMass_pos Ψ (by omega)).ne' _ _
  have hMN : Tendsto (fun X : ℕ =>
      ((anchors (zPsi Ψ) (X + 1) (roughCellLength J X) (cellCount J X)).card : ℝ) /
        ((rawPhysicalRoots (zPsi Ψ) X).card : ℝ)) atTop (𝓝 1) := by
    have hh := hM.div hN (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_self (by norm_num : (1 : ℝ) ≠ 0)] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    change _ / mainMass Ψ X / (_ / mainMass Ψ X) = _
    exact div_div_div_cancel_right₀ (mainMass_pos Ψ (by omega)).ne' _ _
  have hMZ : Tendsto (fun X : ℕ =>
      ((anchors (zPsi Ψ) (X + 1) (roughCellLength J X) (cellCount J X)).card : ℝ) /
        rootNormalization J Ψ X) atTop (𝓝 1) := by
    have hh := hM.div hZ (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_self (by norm_num : (1 : ℝ) ≠ 0)] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    exact div_div_div_cancel_right₀ (mainMass_pos Ψ (by omega)).ne' _ _
  have hh := hδN.add ((hMN.sub hMZ).abs)
  simp only [sub_self, abs_zero, add_zero] at hh
  exact hh

/-- Uniformity is over every bounded configuration test after the physical
scale is chosen, including the failure/first-L observable used in ShapeS. -/
theorem eventually_bounded_test_error {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {J : ℕ} (hJ : 2 < J) (S : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ f : Finset ℕ → ℝ,
      (∀ U ∈ (offsetWindow (S X)).powerset, |f U| ≤ 1) →
      |(∑ U ∈ (offsetWindow (S X)).powerset,
          patternMass (movingRoughSequence (zPsi Ψ)) X (offsetWindow (S X)) U * f U) -
        (∑ U ∈ (offsetWindow (S X)).powerset,
          empiricalLaw (zPsi Ψ) (cellCutoff J Ψ X) (X + 1)
            (roughCellLength J X) (cellCount J X) (S X) U * f U)| < ε := by
  have hsmall := (tendsto_order.mp (tendsto_normalizationError_zero hSlope hC hreg hJ)).2 ε hε
  have hN := (tendsto_order.mp
    (CoreRoughDyadicDensity.tendsto_rawPhysicalRoots_div_main_one hSlope hC hreg)).1
    0 (by norm_num)
  filter_upwards [hsmall, hN, eventually_cellLength_pos hSlope J,
    eventually_rootNormalization_pos hSlope hC hreg hJ, eventually_ge_atTop 1]
    with X herr hratio hH hZ hX
  have hnreal : (0 : ℝ) < (rawPhysicalRoots (zPsi Ψ) X).card :=
    (div_pos_iff_of_pos_right (mainMass_pos Ψ (by omega))).mp hratio
  intro f hf
  exact (bounded_test_error_le hSlope J X (S X) hH hZ
    (Nat.cast_pos.mp hnreal) f hf).trans_lt herr

end
end PrimeGapNormality.Prime.CoreRoughPhysicalTestTransfer
