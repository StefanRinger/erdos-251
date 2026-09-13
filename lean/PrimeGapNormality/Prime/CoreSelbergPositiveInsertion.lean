import PrimeGapNormality.Prime.CoreSelbergInsertionCells
import PrimeGapNormality.Prime.CoreSelbergInsertionAsymptotics

/-!
Uniform positive insertion: finite Selberg cell bounds, integration across
the mesh, and the explicit cost of the final padded endpoint cell.
-/

namespace PrimeGapNormality.Prime.CoreSelberg

open Finset Filter
open MeasureTheory (volume)
open scoped Topology NNReal

noncomputable section

def cellCap (H R : ℕ) : ℝ := (H : ℝ) / selbergJR R + (R : ℝ) ^ 2

theorem cellCap_nonneg (H R : ℕ) (hR : 1 ≤ R) : 0 ≤ cellCap H R :=
  add_nonneg (div_nonneg (Nat.cast_nonneg H) (selbergJR_pos hR).le) (sq_nonneg _)

/-- Integrate the Lipschitz majorization over the whole finite mesh. Every
cell count here is derived from the finite Selberg inequality. -/
theorem finite_mesh_majorant {E : Finset ℕ} {a H R M : ℕ} {G : ℝ}
    (hG : 0 < G) (hR : 1 ≤ R) (hRH : R ≤ H)
    (hE : E ⊆ Ioc a (a + M * H)) (havoid : AvoidsResidues E R)
    (f : ℝ → ℝ) {K : ℝ≥0} (hLip : LipschitzWith K f)
    (hf : ∀ t ∈ Set.Icc 0 ((M : ℝ) * ((H : ℝ) / G)), 0 ≤ f t) :
    ((H : ℝ) / G) * (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
      cellCap H R * ((∫ t in 0..((M : ℝ) * ((H : ℝ) / G)), f t) +
        (K : ℝ) * M * ((H : ℝ) / G) ^ 2) := by
  let δ : ℝ := (H : ℝ) / G
  have hH : 0 < H := lt_of_lt_of_le (by omega : 0 < R) hRH
  have hδ : 0 < δ := div_pos (Nat.cast_pos.mpr hH) hG
  have ha : ∀ n ∈ E, a < n := fun n hn ↦ (Finset.mem_Ioc.mp (hE hn)).1
  have hmaps : (E : Set ℕ).MapsTo (cellIndex a H) (Finset.range M) :=
    fun n hn ↦ Finset.mem_range.mpr (cellIndex_lt hH hE hn)
  have hpart : (∑ j ∈ Finset.range M, ∑ n ∈ cell E a H j,
      f (((n : ℝ) - a) / G)) = ∑ n ∈ E, f (((n : ℝ) - a) / G) := by
    exact Finset.sum_fiberwise_of_maps_to hmaps _
  have hcell : ∀ j ∈ Finset.range M,
      δ * (∑ n ∈ cell E a H j, f (((n : ℝ) - a) / G)) ≤
        cellCap H R * ((∫ t in ((j : ℝ) * δ)..((j : ℝ) * δ + δ), f t) +
          (K : ℝ) * δ ^ 2) := by
    intro j hj
    apply lipschitz_cell_majorant (cell E a H j) (fun n ↦ ((n : ℝ) - a) / G)
      f hLip ((j : ℝ) * δ) δ (cellCap H R) hδ
    · intro n hn
      have hncell := Finset.mem_Ioc.mp (cell_subset_interval hH ha hn)
      have hlow : (a : ℝ) + (j : ℝ) * H ≤ n := by exact_mod_cast hncell.1.le
      have hupp : (n : ℝ) ≤ (a : ℝ) + (j : ℝ) * H + H := by exact_mod_cast hncell.2
      constructor
      · have hd := div_le_div_of_nonneg_right (by linarith : (j : ℝ) * H ≤ (n : ℝ) - a) hG.le
        simpa [δ, mul_div_assoc] using hd
      · have hd := div_le_div_of_nonneg_right (by linarith : (n : ℝ) - a ≤ (j : ℝ) * H + H) hG.le
        simpa [δ, add_div, mul_div_assoc] using hd
    · intro t ht
      have hjM : (j : ℝ) + 1 ≤ M := by exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      apply hf t
      constructor <;> nlinarith [ht.1, ht.2, hδ.le]
    · exact cell_card_le hR hRH ha havoid
  have hsumint : (∑ j ∈ Finset.range M,
      ∫ t in ((j : ℝ) * δ)..((j : ℝ) * δ + δ), f t) =
      ∫ t in 0..((M : ℝ) * δ), f t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun j : ℕ ↦ (j : ℝ) * δ) (n := M) (μ := volume)
      (fun j hj ↦ hLip.continuous.intervalIntegrable _ _)
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_mul, one_mul] using h
  change δ * (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤ _
  calc
    δ * (∑ n ∈ E, f (((n : ℝ) - a) / G)) =
        ∑ j ∈ Finset.range M, δ * (∑ n ∈ cell E a H j, f (((n : ℝ) - a) / G)) := by
          rw [← hpart, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range M, cellCap H R *
        ((∫ t in ((j : ℝ) * δ)..((j : ℝ) * δ + δ), f t) + (K : ℝ) * δ ^ 2) :=
      Finset.sum_le_sum hcell
    _ = cellCap H R * ((∫ t in 0..((M : ℝ) * δ), f t) + (K : ℝ) * M * δ ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hsumint]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Explicit endpoint cost: padding the slot by at most one mesh cell costs
at most `C δ`, and the integrated Lipschitz error costs `K (A+1) δ`. -/
theorem padded_integral_majorant (f : ℝ → ℝ) {K : ℝ≥0} (hLip : LipschitzWith K f)
    {A C W δ : ℝ} {M : ℕ} (hC : 0 ≤ C) (hW : 0 ≤ W) (hWA : W ≤ A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hMlow : W ≤ (M : ℝ) * δ)
    (hMhigh : (M : ℝ) * δ ≤ W + δ)
    (hbound : ∀ t ∈ Set.Icc 0 (A + 1), f t ≤ C) :
    (∫ t in 0..((M : ℝ) * δ), f t) + (K : ℝ) * M * δ ^ 2 ≤
      (∫ t in 0..W, f t) + (C + (K : ℝ) * (A + 1)) * δ := by
  have hend : (M : ℝ) * δ ≤ A + 1 := by linarith
  have htail : (∫ t in W..((M : ℝ) * δ), f t) ≤ C * δ := by
    have hm := intervalIntegral.integral_mono_on hMlow
      (hLip.continuous.intervalIntegrable W ((M : ℝ) * δ))
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ C) volume W ((M : ℝ) * δ))
      (fun t ht ↦ hbound t ⟨hW.trans ht.1, ht.2.trans hend⟩)
    have hi : (∫ t in W..((M : ℝ) * δ), f t) ≤ ((M : ℝ) * δ - W) * C := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
    calc
      (∫ t in W..((M : ℝ) * δ), f t) ≤ ((M : ℝ) * δ - W) * C := hi
      _ ≤ δ * C := mul_le_mul_of_nonneg_right (by linarith) hC
      _ = C * δ := mul_comm _ _
  have herr : (K : ℝ) * M * δ ^ 2 ≤ (K : ℝ) * (A + 1) * δ := by
    calc
      (K : ℝ) * M * δ ^ 2 = ((K : ℝ) * ((M : ℝ) * δ)) * δ := by ring
      _ ≤ ((K : ℝ) * (A + 1)) * δ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hend K.coe_nonneg) hδ.le
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hLip.continuous.intervalIntegrable 0 W) (hLip.continuous.intervalIntegrable W ((M : ℝ) * δ))
  rw [← hadd]
  nlinarith

/-- Finite positive insertion with an explicit cell width and endpoint error. -/
theorem finite_positive_insertion {E : Finset ℕ} {a H R : ℕ} {G A C W : ℝ}
    (hG : 0 < G) (hR : 1 ≤ R) (hRH : R ≤ H) (hmesh : (H : ℝ) / G ≤ 1)
    (hC : 0 ≤ C) (hW : 0 ≤ W) (hWA : W ≤ A)
    (hE : ∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G)
    (havoid : AvoidsResidues E R) (f : ℝ → ℝ) {K : ℝ≥0} (hLip : LipschitzWith K f)
    (hf : ∀ t ∈ Set.Icc 0 (A + 1), 0 ≤ f t ∧ f t ≤ C) :
    (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤ cellCap H R / ((H : ℝ) / G) *
      ((∫ t in 0..W, f t) + (C + (K : ℝ) * (A + 1)) * ((H : ℝ) / G)) := by
  let δ : ℝ := (H : ℝ) / G
  let M : ℕ := ⌊W / δ⌋₊ + 1
  have hH : 0 < H := lt_of_lt_of_le (by omega : 0 < R) hRH
  have hδ : 0 < δ := div_pos (Nat.cast_pos.mpr hH) hG
  have hMlow : W ≤ (M : ℝ) * δ := by
    have h := (Nat.lt_floor_add_one (W / δ)).le
    have h' : W / δ ≤ (M : ℝ) := by simpa [M] using h
    exact (div_le_iff₀ hδ).mp h'
  have hMhigh : (M : ℝ) * δ ≤ W + δ := by
    have hflo := Nat.floor_le (div_nonneg hW hδ.le)
    have h' : (M : ℝ) ≤ W / δ + 1 := by dsimp [M]; push_cast; linarith
    calc
      (M : ℝ) * δ ≤ (W / δ + 1) * δ := mul_le_mul_of_nonneg_right h' hδ.le
      _ = W + δ := by field_simp [hδ.ne']
  have hend : (M : ℝ) * δ ≤ A + 1 := by linarith
  have hEgrid : E ⊆ Ioc a (a + M * H) := by
    intro n hn
    have hne := hE n hn
    refine Finset.mem_Ioc.mpr ⟨hne.1, ?_⟩
    have hmul := mul_le_mul_of_nonneg_right hMlow hG.le
    have heq : (M : ℝ) * δ * G = (M : ℝ) * H := by
      dsimp [δ]
      field_simp [hG.ne']
    have hreal : (n : ℝ) ≤ (a : ℝ) + (M : ℝ) * H := by linarith [hne.2]
    exact_mod_cast hreal
  have hgrid := finite_mesh_majorant hG hR hRH hEgrid havoid f hLip
    (fun t ht ↦ (hf t ⟨ht.1, ht.2.trans hend⟩).1)
  have hpad := padded_integral_majorant f hLip hC hW hWA hδ hmesh hMlow hMhigh
    (fun t ht ↦ (hf t ht).2)
  have hscaled : δ * (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤ cellCap H R *
      ((∫ t in 0..W, f t) + (C + (K : ℝ) * (A + 1)) * δ) :=
    hgrid.trans (mul_le_mul_of_nonneg_left hpad (cellCap_nonneg H R hR))
  calc
    (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
        (cellCap H R * ((∫ t in 0..W, f t) + (C + (K : ℝ) * (A + 1)) * δ)) / δ :=
      (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hscaled)
    _ = cellCap H R / ((H : ℝ) / G) *
        ((∫ t in 0..W, f t) + (C + (K : ℝ) * (A + 1)) * ((H : ℝ) / G)) := by
      dsimp [δ]
      ring

/-- The frozen paper's positive insertion bound, uniformly in every
integer location, forbidden-residue presieve, compact slot, and bounded
nonnegative test with a fixed Lipschitz constant. No cell-count or grid
comparison hypothesis is supplied: the density and error are proved above. -/
theorem eventually_positive_insertion {A C : ℝ} {K : ℝ≥0}
    (hA : 0 < A) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ G : ℝ in atTop, ∀ (a : ℕ) (W : ℝ) (E : Finset ℕ) (f : ℝ → ℝ),
      0 ≤ W → W ≤ A →
      (∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G) →
      AvoidsResidues E ⌊G⌋₊ → LipschitzWith K f →
      (∀ t ∈ Set.Icc 0 (A + 1), 0 ≤ f t ∧ f t ≤ C) →
      (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
        3 * G / Real.log G * ((∫ t in 0..W, f t) + ε) := by
  let D : ℝ := C + (K : ℝ) * (A + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hD1 : 0 < D + 1 := by positivity
  let δ : ℝ := min 1 (ε / (D + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : D * δ ≤ ε := by
    have hδeps : δ ≤ ε / (D + 1) := min_le_right _ _
    have hmul := (le_div_iff₀ hD1).mp hδeps
    nlinarith [hδ.le]
  filter_upwards [eventually_mesh_density_le_three hδ hδ1] with G hmesh
  obtain ⟨hG, hH, hR, hRH, hHfloor, hmeshδ, hcap⟩ := hmesh
  intro a W E f hW hWA hE havoid hLip hf
  have hG0 : 0 < G := lt_trans zero_lt_one hG
  have havoidR : AvoidsResidues E (selbergRadius (meshLength δ G)) :=
    havoid.radius_mono (hRH.trans hHfloor)
  have hfinite := finite_positive_insertion hG0 hR hRH (hmeshδ.trans hδ1)
    hC hW hWA hE havoidR f hLip hf
  have hI : 0 ≤ ∫ t in 0..W, f t :=
    intervalIntegral.integral_nonneg hW (fun t ht ↦ (hf t ⟨ht.1, by linarith [ht.2]⟩).1)
  have hmeshnonneg : 0 ≤ (meshLength δ G : ℝ) / G :=
    div_nonneg (Nat.cast_nonneg _) hG0.le
  have herror : D * ((meshLength δ G : ℝ) / G) ≤ ε :=
    (mul_le_mul_of_nonneg_left hmeshδ hD).trans hδε
  have hbracket : 0 ≤ (∫ t in 0..W, f t) + D * ((meshLength δ G : ℝ) / G) :=
    add_nonneg hI (mul_nonneg hD hmeshnonneg)
  have hfactor : 0 ≤ 3 * G / Real.log G := by
    exact div_nonneg (mul_nonneg (by norm_num) hG0.le) (Real.log_pos hG).le
  change cellCap (meshLength δ G) (selbergRadius (meshLength δ G)) /
    ((meshLength δ G : ℝ) / G) ≤ 3 * G / Real.log G at hcap
  calc
    (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
        cellCap (meshLength δ G) (selbergRadius (meshLength δ G)) /
          ((meshLength δ G : ℝ) / G) *
            ((∫ t in 0..W, f t) + D * ((meshLength δ G : ℝ) / G)) := hfinite
    _ ≤ 3 * G / Real.log G *
        ((∫ t in 0..W, f t) + D * ((meshLength δ G : ℝ) / G)) :=
      mul_le_mul_of_nonneg_right hcap hbracket
    _ ≤ 3 * G / Real.log G * ((∫ t in 0..W, f t) + ε) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl herror) hfactor

end

end PrimeGapNormality.Prime.CoreSelberg
