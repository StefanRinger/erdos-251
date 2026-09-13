import PrimeGapNormality.Prime.RankSelect
import PrimeGapNormality.Prime.StatisticalCriterion
import Mathlib.Analysis.Real.Sqrt

/-!
Critical rank for the actual linear insertion slope. The square-root
reserve is retained, including at the endpoint `κ = 1 / log B`.
-/

namespace PrimeGapNormality.Prime.CoreLinearInsertion

open Finset Filter
open scoped Topology

noncomputable section

def linearProfileL (κ G : ℝ) : ℕ :=
  ⌈κ * Real.log G + Real.sqrt (κ * Real.log G)⌉₊

theorem rankSelect_linear_scale {B : ℕ} (hB : 2 ≤ B) (G : ℝ) (j : ℕ) :
    |1 / (B : ℝ)| * G ^ (1 : ℕ) * (B : ℝ) ^ (-(j : ℤ)) =
      G / (B : ℝ) ^ (j + 1) := by
  have hbpos : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hb0 : (B : ℝ) ≠ 0 := hbpos.ne'
  rw [abs_of_pos (one_div_pos.mpr hbpos), pow_one, zpow_neg, zpow_natCast, pow_succ]
  field_simp [hb0, pow_ne_zero j hb0] <;> ring

/-- The existing finite logarithmic rank selector at the actual insertion
normalization `G / B^(j+1)`, with a fixed additive budget reserve. -/
theorem exists_critical_rank_reserve {B : ℕ} (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∃ G₀ C : ℝ, 0 < C ∧ ∀ G : ℝ, G₀ ≤ G → ∀ L : ℕ,
      κ * Real.log G + C ≤ (L : ℝ) →
      ∃ j : ℕ, 1 ≤ j ∧ j < L ∧
        1 ≤ G / (B : ℝ) ^ (j + 1) ∧ G / (B : ℝ) ^ (j + 1) < B := by
  have hb0 : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hη : (1 / (B : ℝ)) ≠ 0 := div_ne_zero one_ne_zero hb0
  obtain ⟨G₀, C, hC, hselect⟩ := exists_rankSelect_in_range_ge
    (B := B) (k := 1) (r := 1) (R := 1) (η := 1 / (B : ℝ)) (J := 0) (κ := κ)
    hB (by decide) (by simp) hη (by decide) (by simpa only [Nat.cast_one] using hκ)
  refine ⟨G₀, C, hC, ?_⟩
  intro G hG L hL
  obtain ⟨j, hj, _, hlo, hhi, _⟩ := hselect G hG L hL
  refine ⟨j, (Finset.mem_Ico.mp hj).1, (Finset.mem_Ico.mp hj).2, ?_, ?_⟩
  · have h := hlo
    rw [rankSelect_linear_scale hB G j] at h
    simpa using h
  · have h := hhi
    rw [rankSelect_linear_scale hB G j] at h
    simpa using h

/-- The growing square-root reserve discharges the fixed selector cost;
the nonstrict critical profile is therefore sufficient. -/
theorem eventually_critical_rank {B : ℕ} (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∀ᶠ G : ℝ in atTop, ∃ j : ℕ, 1 ≤ j ∧ j < linearProfileL κ G ∧
      1 ≤ G / (B : ℝ) ^ (j + 1) ∧ G / (B : ℝ) ^ (j + 1) < B := by
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr (by omega))
  have hκpos : 0 < κ := (div_pos (by norm_num : (0 : ℝ) < 1) hlog).trans_le hκ
  obtain ⟨G₀, C, hC, hselect⟩ := exists_critical_rank_reserve hB hκ
  have hreserve : Tendsto (fun G : ℝ ↦ Real.sqrt (κ * Real.log G)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Filter.Tendsto.const_mul_atTop hκpos Real.tendsto_log_atTop)
  filter_upwards [eventually_ge_atTop G₀,
    hreserve.eventually (eventually_ge_atTop C)] with G hG hCreserve
  apply hselect G hG (linearProfileL κ G)
  exact (add_le_add le_rfl hCreserve).trans (Nat.le_ceil _)

theorem stdProfileL_eq_linearProfileL (ρ G : ℝ) :
    stdProfileL ρ G = linearProfileL (1 / Real.log ρ) G := by
  unfold stdProfileL logρ linearProfileL
  have h : 1 / Real.log ρ * Real.log G = Real.log G / Real.log ρ := by ring
  rw [h]

theorem eventually_critical_rank_stdProfile {B : ℕ} (hB : 2 ≤ B) {ρ : ℝ}
    (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ)) :
    ∀ᶠ G : ℝ in atTop, ∃ j : ℕ, 1 ≤ j ∧ j < stdProfileL ρ G ∧
      1 ≤ G / (B : ℝ) ^ (j + 1) ∧ G / (B : ℝ) ^ (j + 1) < B := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hlogs : Real.log ρ ≤ Real.log (B : ℝ) := Real.log_le_log hρ0 hρB
  have hκ : 1 / Real.log (B : ℝ) ≤ 1 / Real.log ρ :=
    div_le_div_of_nonneg_left (by norm_num) hlogρ hlogs
  simpa only [stdProfileL_eq_linearProfileL] using eventually_critical_rank hB hκ

/-- Specialization to the actual physical-window profile in the paper. -/
theorem eventually_critical_rank_profileL {B : ℕ} (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∀ᶠ X : ℕ in atTop, ∃ j : ℕ, 1 ≤ j ∧ j < profileL κ X ∧
      1 ≤ windowG X / (B : ℝ) ^ (j + 1) ∧
        windowG X / (B : ℝ) ^ (j + 1) < B := by
  have hG : Tendsto windowG atTop atTop :=
    tendsto_atTop_mono (fun X ↦ le_max_left (Real.log (X : ℝ)) (1 : ℝ))
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact hG.eventually (eventually_critical_rank hB hκ)

theorem scaled_slope_bounds {B j : ℕ} (hB : 2 ≤ B) {G : ℝ}
    (hlo : 1 ≤ G / (B : ℝ) ^ (j + 1)) (hhi : G / (B : ℝ) ^ (j + 1) < B) :
    (B : ℝ) - 1 ≤ G * ((B : ℝ) - 1) / (B : ℝ) ^ (j + 1) ∧
      G * ((B : ℝ) - 1) / (B : ℝ) ^ (j + 1) < (B : ℝ) * ((B : ℝ) - 1) := by
  have hb : (0 : ℝ) < (B : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have heq : G * ((B : ℝ) - 1) / (B : ℝ) ^ (j + 1) =
      ((B : ℝ) - 1) * (G / (B : ℝ) ^ (j + 1)) := by ring
  rw [heq]
  constructor
  · simpa using mul_le_mul_of_nonneg_left hlo hb.le
  · simpa [mul_comm] using mul_lt_mul_of_pos_left hhi hb

end

end PrimeGapNormality.Prime.CoreLinearInsertion
