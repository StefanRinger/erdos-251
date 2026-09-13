import PrimeGapNormality.Prime.CoreSelbergPositiveInsertion
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact

/-!
# Positive insertion for compact continuous families

The actual Selberg cells need only an oscillation bound, not a derivative
or Lipschitz constant. The integrated cell error is eta times its length;
the padded endpoint costs C times one cell length. Joint continuity on a
compact parameter set supplies a single oscillation scale before all
parameters, locations, presieves and available spans are chosen.
-/

namespace PrimeGapNormality.Prime.CoreCompactContinuousInsertion

open Finset Filter CoreSelberg
open MeasureTheory (volume)
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1500000

theorem oscillation_cell_majorant {ι : Type*} (E : Finset ι) (z : ι → ℝ)
    (f : ℝ → ℝ) {l δ η cap : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η)
    (hc : ContinuousOn f (Set.Icc l (l + δ)))
    (hz : ∀ n ∈ E, z n ∈ Set.Icc l (l + δ))
    (hf : ∀ t ∈ Set.Icc l (l + δ), 0 ≤ f t)
    (hosc : ∀ t ∈ Set.Icc l (l + δ), ∀ u ∈ Set.Icc l (l + δ), |f t - f u| ≤ η)
    (hcard : (E.card : ℝ) ≤ cap) :
    δ * (∑ n ∈ E, f (z n)) ≤ cap * ((∫ t in l..(l + δ), f t) + η * δ) := by
  have hl : l ≤ l + δ := by linarith
  have hint : IntervalIntegrable f volume l (l + δ) := hc.intervalIntegrable_of_Icc hl
  have hp : ∀ n ∈ E, δ * f (z n) ≤ (∫ t in l..(l + δ), f t) + η * δ := by
    intro n hn
    have hpoint : ∀ t ∈ Set.Icc l (l + δ), f (z n) ≤ f t + η := by
      intro t ht
      have hh := (abs_le.mp (hosc (z n) (hz n hn) t ht)).2
      linarith
    have hm := intervalIntegral.integral_mono_on hl
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f (z n)) volume l (l + δ))
      (hint.add intervalIntegrable_const) hpoint
    calc
      δ * f (z n) = ∫ t in l..(l + δ), f (z n) := by
        simp [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ t in l..(l + δ), f t + η := hm
      _ = (∫ t in l..(l + δ), f t) + η * δ := by
        rw [intervalIntegral.integral_add hint intervalIntegrable_const, intervalIntegral.integral_const]
        simp only [add_sub_cancel_left, smul_eq_mul]
        ring
  have hnon : 0 ≤ (∫ t in l..(l + δ), f t) + η * δ :=
    add_nonneg (intervalIntegral.integral_nonneg hl hf) (mul_nonneg hη hδ.le)
  calc
    δ * (∑ n ∈ E, f (z n)) = ∑ n ∈ E, δ * f (z n) := Finset.mul_sum ..
    _ ≤ ∑ _n ∈ E, ((∫ t in l..(l + δ), f t) + η * δ) := sum_le_sum hp
    _ = (E.card : ℝ) * ((∫ t in l..(l + δ), f t) + η * δ) := by simp <;> ring
    _ ≤ cap * ((∫ t in l..(l + δ), f t) + η * δ) :=
      mul_le_mul_of_nonneg_right hcard hnon

theorem finite_mesh_majorant {E : Finset ℕ} {a H R M : ℕ} {G η : ℝ}
    (hG : 0 < G) (hR : 1 ≤ R) (hRH : R ≤ H) (hη : 0 ≤ η)
    (hE : E ⊆ Ioc a (a + M * H)) (havoid : AvoidsResidues E R)
    (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Icc 0 ((M : ℝ) * ((H : ℝ) / G))))
    (hf : ∀ t ∈ Set.Icc 0 ((M : ℝ) * ((H : ℝ) / G)), 0 ≤ f t)
    (hosc : ∀ t ∈ Set.Icc 0 ((M : ℝ) * ((H : ℝ) / G)),
      ∀ u ∈ Set.Icc 0 ((M : ℝ) * ((H : ℝ) / G)),
        dist t u ≤ (H : ℝ) / G → |f t - f u| ≤ η) :
    ((H : ℝ) / G) * (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
      cellCap H R * ((∫ t in 0..((M : ℝ) * ((H : ℝ) / G)), f t) +
        η * ((M : ℝ) * ((H : ℝ) / G))) := by
  let δ := (H : ℝ) / G
  have hH : 0 < H := lt_of_lt_of_le (by omega : 0 < R) hRH
  have hδ : 0 < δ := div_pos (Nat.cast_pos.mpr hH) hG
  have ha : ∀ n ∈ E, a < n := fun n hn => (Finset.mem_Ioc.mp (hE hn)).1
  have hsub (j : ℕ) (hj : j ∈ range M) :
      Set.Icc ((j : ℝ) * δ) ((j : ℝ) * δ + δ) ⊆ Set.Icc 0 ((M : ℝ) * δ) := by
    intro t ht
    have hjM : (j : ℝ) + 1 ≤ M := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hj)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    constructor <;> nlinarith [ht.1, ht.2]
  have hmaps : (E : Set ℕ).MapsTo (cellIndex a H) (range M) :=
    fun n hn => mem_range.mpr (cellIndex_lt hH hE hn)
  have hpart : (∑ j ∈ range M, ∑ n ∈ cell E a H j, f (((n : ℝ) - a) / G)) =
      ∑ n ∈ E, f (((n : ℝ) - a) / G) := sum_fiberwise_of_maps_to hmaps _
  have hcell : ∀ j ∈ range M,
      δ * (∑ n ∈ cell E a H j, f (((n : ℝ) - a) / G)) ≤
        cellCap H R * ((∫ t in ((j : ℝ) * δ)..((j : ℝ) * δ + δ), f t) + η * δ) := by
    intro j hj
    apply oscillation_cell_majorant (cell E a H j) (fun n => ((n : ℝ) - a) / G) f hδ hη
      (hc.mono (hsub j hj))
    · intro n hn
      have hi := Finset.mem_Ioc.mp (cell_subset_interval hH ha hn)
      have hlo : (a : ℝ) + (j : ℝ) * H ≤ n := by exact_mod_cast hi.1.le
      have hhi : (n : ℝ) ≤ (a : ℝ) + (j : ℝ) * H + H := by exact_mod_cast hi.2
      constructor
      · have hh := div_le_div_of_nonneg_right (by linarith : (j : ℝ) * H ≤ (n : ℝ) - a) hG.le
        simpa only [δ, mul_div_assoc] using hh
      · have hh := div_le_div_of_nonneg_right (by linarith : (n : ℝ) - a ≤ (j : ℝ) * H + H) hG.le
        simpa only [δ, add_div, mul_div_assoc] using hh
    · exact fun t ht => hf t (hsub j hj ht)
    · intro t ht u hu
      apply hosc t (hsub j hj ht) u (hsub j hj hu)
      rw [Real.dist_eq]
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
    · exact cell_card_le hR hRH ha havoid
  have hint : ∀ j ∈ range M,
      IntervalIntegrable f volume ((j : ℝ) * δ) (((j + 1 : ℕ) : ℝ) * δ) := by
    intro j hj
    have hh : IntervalIntegrable f volume ((j : ℝ) * δ) ((j : ℝ) * δ + δ) :=
      (hc.mono (hsub j hj)).intervalIntegrable_of_Icc (by linarith)
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hh
  have hsumint : (∑ j ∈ range M, ∫ t in ((j : ℝ) * δ)..((j : ℝ) * δ + δ), f t) =
      ∫ t in 0..((M : ℝ) * δ), f t := by
    have hh := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun j : ℕ => (j : ℝ) * δ) (n := M) (μ := volume)
      (fun j hj => hint j (mem_range.mpr hj))
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_mul, one_mul] using hh
  calc
    δ * (∑ n ∈ E, f (((n : ℝ) - a) / G)) =
        ∑ j ∈ range M, δ * (∑ n ∈ cell E a H j, f (((n : ℝ) - a) / G)) := by
      rw [← hpart, mul_sum]
    _ ≤ ∑ j ∈ range M, cellCap H R *
        ((∫ t in ((j : ℝ) * δ)..((j : ℝ) * δ + δ), f t) + η * δ) := sum_le_sum hcell
    _ = cellCap H R * ((∫ t in 0..((M : ℝ) * δ), f t) + η * ((M : ℝ) * δ)) := by
      rw [← mul_sum, sum_add_distrib, hsumint]
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring

theorem finite_positive_insertion {E : Finset ℕ} {a H R : ℕ} {G A C W η : ℝ}
    (hG : 0 < G) (hR : 1 ≤ R) (hRH : R ≤ H) (hmesh : (H : ℝ) / G ≤ 1)
    (hC : 0 ≤ C) (hη : 0 ≤ η) (hW : 0 ≤ W) (hWA : W ≤ A)
    (hE : ∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G) (havoid : AvoidsResidues E R)
    (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Icc 0 (A + 1)))
    (hf : ∀ t ∈ Set.Icc 0 (A + 1), 0 ≤ f t ∧ f t ≤ C)
    (hosc : ∀ t ∈ Set.Icc 0 (A + 1), ∀ u ∈ Set.Icc 0 (A + 1),
      dist t u ≤ (H : ℝ) / G → |f t - f u| ≤ η) :
    (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤ cellCap H R / ((H : ℝ) / G) *
      ((∫ t in 0..W, f t) + C * ((H : ℝ) / G) + η * (A + 1)) := by
  let δ := (H : ℝ) / G
  let M : ℕ := ⌊W / δ⌋₊ + 1
  have hH : 0 < H := lt_of_lt_of_le (by omega : 0 < R) hRH
  have hδ : 0 < δ := div_pos (Nat.cast_pos.mpr hH) hG
  have hlow : W ≤ (M : ℝ) * δ := by
    have hh := (Nat.lt_floor_add_one (W / δ)).le
    have hh' : W / δ ≤ (M : ℝ) := by simpa only [M, Nat.cast_add, Nat.cast_one] using hh
    exact (div_le_iff₀ hδ).mp hh'
  have hhigh : (M : ℝ) * δ ≤ W + δ := by
    have hh := Nat.floor_le (div_nonneg hW hδ.le)
    have hm : (M : ℝ) ≤ W / δ + 1 := by dsimp only [M]; push_cast; linarith
    have hmul := mul_le_mul_of_nonneg_right hm hδ.le
    exact hmul.trans_eq (by field_simp [hδ.ne'])
  have hend : (M : ℝ) * δ ≤ A + 1 := by linarith
  have hEgrid : E ⊆ Ioc a (a + M * H) := by
    intro n hn
    have hne := hE n hn
    refine Finset.mem_Ioc.mpr ⟨hne.1, ?_⟩
    have hh := mul_le_mul_of_nonneg_right hlow hG.le
    have heq : (M : ℝ) * δ * G = (M : ℝ) * H := by dsimp [δ]; field_simp [hG.ne']
    have hnreal : (n : ℝ) ≤ (a : ℝ) + (M : ℝ) * H := by linarith [hne.2]
    exact_mod_cast hnreal
  have hsub : Set.Icc 0 ((M : ℝ) * δ) ⊆ Set.Icc 0 (A + 1) := fun t ht => ⟨ht.1, ht.2.trans hend⟩
  have hgrid := finite_mesh_majorant hG hR hRH hη hEgrid havoid f (hc.mono hsub)
    (fun t ht => (hf t (hsub ht)).1)
    (fun t ht u hu htu => hosc t (hsub ht) u (hsub hu) htu)
  have hi0 : IntervalIntegrable f volume 0 W :=
    (hc.mono (fun t ht => ⟨ht.1, ht.2.trans (by linarith : W ≤ A + 1)⟩)).intervalIntegrable_of_Icc hW
  have hit : IntervalIntegrable f volume W ((M : ℝ) * δ) :=
    (hc.mono (fun t ht => ⟨hW.trans ht.1, ht.2.trans hend⟩)).intervalIntegrable_of_Icc hlow
  have htail : (∫ t in W..((M : ℝ) * δ), f t) ≤ C * δ := by
    have hh := intervalIntegral.integral_mono_on hlow hit
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume W ((M : ℝ) * δ))
      (fun t ht => (hf t ⟨hW.trans ht.1, ht.2.trans hend⟩).2)
    have heq : (∫ t in W..((M : ℝ) * δ), (C : ℝ)) = ((M : ℝ) * δ - W) * C := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
    rw [heq] at hh
    exact hh.trans (by nlinarith)
  have herror : η * ((M : ℝ) * δ) ≤ η * (A + 1) := mul_le_mul_of_nonneg_left hend hη
  have hpad : (∫ t in 0..((M : ℝ) * δ), f t) + η * ((M : ℝ) * δ) ≤
      (∫ t in 0..W, f t) + C * δ + η * (A + 1) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hit]
    linarith
  have hscaled := hgrid.trans (mul_le_mul_of_nonneg_left hpad (cellCap_nonneg H R hR))
  have hh : (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
      (cellCap H R * ((∫ t in 0..W, f t) + C * δ + η * (A + 1))) / δ :=
    (le_div_iff₀ hδ).2 (by simpa only [δ, mul_comm] using hscaled)
  exact hh.trans_eq (by dsimp only [δ]; ring)

/-- Compact joint continuity supplies a single oscillation scale on all
fibres. No global Lipschitz extension or derivative estimate is needed. -/
theorem eventually_positive_insertion {α : Type*} [PseudoMetricSpace α]
    (K : Set α) (hK : IsCompact K) (F : α × ℝ → ℝ) {A : ℝ} (hA : 0 < A)
    (hc : ContinuousOn F (K ×ˢ Set.Icc 0 (A + 1)))
    (hf : ∀ y ∈ K, ∀ t ∈ Set.Icc 0 (A + 1), 0 ≤ F (y, t))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ G : ℝ in atTop, ∀ y ∈ K, ∀ (a : ℕ) (W : ℝ) (E : Finset ℕ),
      0 ≤ W → W ≤ A →
      (∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G) →
      AvoidsResidues E ⌊G⌋₊ →
      (∑ n ∈ E, F (y, ((n : ℝ) - a) / G)) ≤
        3 * G / Real.log G * ((∫ t in 0..W, F (y, t)) + ε) := by
  have hcompact : IsCompact (K ×ˢ Set.Icc 0 (A + 1)) := hK.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hcompact.bddAbove_image hc
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound : ∀ y ∈ K, ∀ t ∈ Set.Icc 0 (A + 1), F (y, t) ≤ C :=
    fun y hy t ht => (hC0 (Set.mem_image_of_mem F ⟨hy, ht⟩)).trans (le_max_left _ _)
  let η := ε / (2 * (A + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have huc := hcompact.uniformContinuousOn_of_continuous hc
  obtain ⟨δ0, hδ0, hosc⟩ := Metric.uniformContinuousOn_iff_le.mp huc η hη
  let δ := min 1 (min δ0 (ε / (2 * (C + 1))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ0' : δ ≤ δ0 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : C * δ + η * (A + 1) ≤ ε := by
    have hh : δ ≤ ε / (2 * (C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp hh
    have heq : η * (A + 1) = ε / 2 := by dsimp [η]; field_simp [ne_of_gt (by positivity : 0 < A + 1)]
    rw [heq]
    nlinarith [hδ.le]
  filter_upwards [eventually_mesh_density_le_three hδ hδ1] with G hmesh
  obtain ⟨hG, hH, hR, hRH, hHfloor, hmeshδ, hcap⟩ := hmesh
  intro y hy a W E hW hWA hE havoid
  have hg : 0 < G := zero_lt_one.trans hG
  have hcont : ContinuousOn (fun t => F (y, t)) (Set.Icc 0 (A + 1)) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hy, ht⟩)
  have hlocal : ∀ t ∈ Set.Icc 0 (A + 1), ∀ u ∈ Set.Icc 0 (A + 1),
      dist t u ≤ (meshLength δ G : ℝ) / G → |F (y, t) - F (y, u)| ≤ η := by
    intro t ht u hu htu
    have hd : dist (y, t) (y, u) ≤ δ0 := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist t u)] using
        htu.trans (hmeshδ.trans hδ0')
    simpa only [Real.dist_eq] using hosc (y, t) ⟨hy, ht⟩ (y, u) ⟨hy, hu⟩ hd
  have hfinite := finite_positive_insertion hg hR hRH (hmeshδ.trans hδ1) hC hη.le hW hWA hE
    (havoid.radius_mono (hRH.trans hHfloor)) (fun t => F (y, t)) hcont
    (fun t ht => ⟨hf y hy t ht, hbound y hy t ht⟩) hlocal
  have hi : 0 ≤ ∫ t in 0..W, F (y, t) :=
    intervalIntegral.integral_nonneg hW (fun t ht => hf y hy t ⟨ht.1, ht.2.trans (by linarith)⟩)
  have hmeshnonneg : 0 ≤ (meshLength δ G : ℝ) / G := div_nonneg (Nat.cast_nonneg _) hg.le
  have herr : C * ((meshLength δ G : ℝ) / G) + η * (A + 1) ≤ ε :=
    (add_le_add (mul_le_mul_of_nonneg_left hmeshδ hC) le_rfl).trans hδε
  have hbracket : 0 ≤ (∫ t in 0..W, F (y, t)) + C * ((meshLength δ G : ℝ) / G) + η * (A + 1) := by
    positivity
  have hfactor : 0 ≤ 3 * G / Real.log G := div_nonneg (by positivity) (Real.log_pos hG).le
  change cellCap (meshLength δ G) (selbergRadius (meshLength δ G)) /
    ((meshLength δ G : ℝ) / G) ≤ 3 * G / Real.log G at hcap
  exact hfinite.trans ((mul_le_mul_of_nonneg_right hcap hbracket).trans
    (mul_le_mul_of_nonneg_left (by linarith) hfactor))

end
end PrimeGapNormality.Prime.CoreCompactContinuousInsertion
