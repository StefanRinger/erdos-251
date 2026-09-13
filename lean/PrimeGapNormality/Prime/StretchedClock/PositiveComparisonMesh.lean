import PrimeGapNormality.Prime.CoreSelbergInsertionCells
import PrimeGapNormality.Prime.CorePositiveTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! A finite positive mesh adapter reusing the existing cell-average lemma. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset MeasureTheory
open scoped NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1200000

def unitMeshIndex (M : ℕ) (x : ℝ) : ℕ := ⌊x * (M : ℝ)⌋₊

theorem unitMeshIndex_lt {M : ℕ} (hM : 0 < M) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) : unitMeshIndex M x < M := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  apply (Nat.floor_lt (mul_nonneg hx0 hMr.le)).mpr
  simpa only [one_mul] using mul_lt_mul_of_pos_right hx1 hMr

theorem unitMeshIndex_bounds {M : ℕ} (hM : 0 < M) {x : ℝ} (hx : 0 ≤ x) :
    (unitMeshIndex M x : ℝ) / M ≤ x ∧
      x < ((unitMeshIndex M x : ℝ) + 1) / M := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  refine ⟨(div_le_iff₀ hMr).mpr ?_, (lt_div_iff₀ hMr).mpr ?_⟩
  · exact Nat.floor_le (mul_nonneg hx hMr.le)
  · exact Nat.lt_floor_add_one (x * (M : ℝ))

/-- Finite mesh-count domination implies positive-test domination. The
normalizing mass W need not equal the cardinality of E. -/
theorem unit_mesh_positive_mean {ι : Type*} (E : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ E, 0 ≤ z i ∧ z i < 1)
    {M : ℕ} (hM : 0 < M) {A W : ℝ} (hW : 0 < W)
    (hcount : ∀ j < M,
      (((E.filter fun i => (j : ℝ) / M ≤ z i ∧ z i < ((j : ℝ) + 1) / M).card : ℕ) : ℝ) ≤
        A * W / M)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ i ∈ E, f (z i : AddCircle (1 : ℝ))) / W ≤
      A * ((∫ x : AddCircle (1 : ℝ), f x) + (K : ℝ) / M) := by
  classical
  let δ : ℝ := 1 / M
  let F : ℝ → ℝ := fun x => f (x : AddCircle (1 : ℝ))
  let cell : ℕ → Finset ι := fun j => E.filter fun i => unitMeshIndex M (z i) = j
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hδ : 0 < δ := div_pos zero_lt_one hMr
  have hMδ : (M : ℝ) * δ = 1 := by dsimp [δ]; field_simp
  have hF : LipschitzWith K F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hK.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Real.dist_eq] using coreCircle_dist_coe_le x y) K.coe_nonneg)
  have hmaps : ∀ i ∈ E, unitMeshIndex M (z i) ∈ range M :=
    fun i hi => mem_range.mpr (unitMeshIndex_lt hM (hz i hi).1 (hz i hi).2)
  have hpart : (∑ j ∈ range M, ∑ i ∈ cell j, F (z i)) = ∑ i ∈ E, F (z i) :=
    sum_fiberwise_of_maps_to hmaps _
  have hcell : ∀ j ∈ range M,
      δ * (∑ i ∈ cell j, F (z i)) ≤
        (A * W * δ) * ((∫ t in ((j : ℝ) * δ)..((j : ℝ) * δ + δ), F t) +
          (K : ℝ) * δ ^ 2) := by
    intro j hj
    have hb (i : ι) (hi : i ∈ cell j) :
        (j : ℝ) / M ≤ z i ∧ z i < ((j : ℝ) + 1) / M := by
      obtain ⟨hiE, hiidx⟩ := mem_filter.mp hi
      simpa only [hiidx] using unitMeshIndex_bounds hM (hz i hiE).1
    apply CoreSelberg.lipschitz_cell_majorant (cell j) z F hF ((j : ℝ) * δ) δ (A * W * δ) hδ
    · intro i hi
      have hh := hb i hi
      constructor
      · simpa only [δ, div_eq_mul_inv, one_mul] using hh.1
      · simpa only [δ, add_div, div_eq_mul_inv, add_mul, one_mul] using hh.2.le
    · intro t ht
      exact hf _
    · have hsub : cell j ⊆ E.filter
          (fun i => (j : ℝ) / M ≤ z i ∧ z i < ((j : ℝ) + 1) / M) := by
        intro i hi
        exact mem_filter.mpr ⟨(mem_filter.mp hi).1, hb i hi⟩
      have hh := (Nat.cast_le.mpr (card_le_card hsub) :
        ((cell j).card : ℝ) ≤ ((E.filter
          (fun i => (j : ℝ) / M ≤ z i ∧ z i < ((j : ℝ) + 1) / M)).card : ℝ))
      simpa only [δ, div_eq_mul_inv, one_mul] using hh.trans (hcount j (mem_range.mp hj))
  have hsumint : (∑ j ∈ range M,
      ∫ t in ((j : ℝ) * δ)..((j : ℝ) * δ + δ), F t) =
        ∫ t in 0..((M : ℝ) * δ), F t := by
    have hh := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun j : ℕ => (j : ℝ) * δ) (n := M) (μ := volume)
      (fun j hj => hF.continuous.intervalIntegrable _ _)
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_mul, one_mul] using hh
  have hs : δ * (∑ i ∈ E, F (z i)) ≤
      A * W * δ * ((∫ t in 0..((M : ℝ) * δ), F t) + (K : ℝ) * M * δ ^ 2) := by
    calc
      _ = ∑ j ∈ range M, δ * (∑ i ∈ cell j, F (z i)) := by
        rw [← hpart, mul_sum]
      _ ≤ ∑ j ∈ range M, (A * W * δ) *
          ((∫ t in ((j : ℝ) * δ)..((j : ℝ) * δ + δ), F t) + (K : ℝ) * δ ^ 2) :=
        sum_le_sum hcell
      _ = _ := by
        rw [← mul_sum, sum_add_distrib, hsumint]
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring
  have hpre : (∫ t in (0 : ℝ)..1, F t) = ∫ x : AddCircle (1 : ℝ), f x := by
    simpa only [zero_add, F] using AddCircle.intervalIntegral_preimage (1 : ℝ) 0 f
  have herror : (K : ℝ) * M * δ ^ 2 = (K : ℝ) / M := by
    dsimp [δ]
    field_simp [hMr.ne'] <;> ring
  rw [hMδ, hpre, herror] at hs
  have hs' : (∑ i ∈ E, F (z i)) ≤
      W * (A * ((∫ x : AddCircle (1 : ℝ), f x) + (K : ℝ) / M)) := by
    have hright : A * W * δ * ((∫ x : AddCircle (1 : ℝ), f x) + (K : ℝ) / M) =
        δ * (W * (A * ((∫ x : AddCircle (1 : ℝ), f x) + (K : ℝ) / M))) := by ring
    exact (mul_le_mul_iff_right₀ hδ).mp (hs.trans_eq hright)
  apply (div_le_iff₀ hW).mpr
  simpa only [F, mul_comm W] using hs'

end
end PrimeGapNormality.Prime.StretchedClock
