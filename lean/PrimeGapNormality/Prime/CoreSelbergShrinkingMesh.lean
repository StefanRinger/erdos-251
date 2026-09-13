import PrimeGapNormality.Prime.CoreSelbergPositiveInsertion

/-!
# Selberg insertion on the shrinking square-root mesh

The quantitative orbit argument needs a mesh which shrinks with the Euler
scale, rather than the earlier two-stage limit with a fixed mesh ratio.
Here

`H = floor(sqrt G)`, `R = selbergRadius H`, and `delta = H/G`.

All asymptotics below are proved directly along this diagonal choice.  In
particular, no theorem whose eventual threshold depends on a fixed `delta`
is specialized to a varying value.
-/

namespace PrimeGapNormality.Prime.CoreSelbergShrinkingMesh

open Filter Finset Asymptotics
open CoreSelberg
open scoped Topology NNReal Classical

noncomputable section

def shrinkingMeshLength (G : ℝ) : ℕ := ⌊Real.sqrt G⌋₊

def shrinkingMeshRadius (G : ℝ) : ℕ :=
  selbergRadius (shrinkingMeshLength G)

def shrinkingMeshDelta (G : ℝ) : ℝ :=
  (shrinkingMeshLength G : ℝ) / G

theorem tendsto_shrinkingMeshLength_atTop :
    Tendsto shrinkingMeshLength atTop atTop := by
  change Tendsto (fun G : ℝ ↦ ⌊Real.sqrt G⌋₊) atTop atTop
  simpa only [Function.comp_def] using
    tendsto_nat_floor_atTop.comp Real.tendsto_sqrt_atTop

theorem isEquivalent_shrinkingMeshLength_sqrt :
    (fun G : ℝ ↦ (shrinkingMeshLength G : ℝ)) ~[atTop]
      (fun G : ℝ ↦ Real.sqrt G) := by
  simpa only [Function.comp_def, shrinkingMeshLength] using
    Asymptotics.isEquivalent_nat_floor.comp_tendsto Real.tendsto_sqrt_atTop

private theorem tendsto_log_sqrt_div_log :
    Tendsto (fun G : ℝ ↦ Real.log (Real.sqrt G) / Real.log G)
      atTop (nhds (1 / 2 : ℝ)) := by
  refine (tendsto_const_nhds : Tendsto (fun _G : ℝ ↦ (1 / 2 : ℝ))
    atTop (nhds (1 / 2 : ℝ))).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with G hG
  have hG0 : 0 < G := zero_lt_one.trans hG
  have hlogG : Real.log G ≠ 0 := (Real.log_pos hG).ne'
  rw [Real.log_sqrt hG0.le]
  field_simp [hlogG]

theorem tendsto_log_shrinkingMesh_div_log :
    Tendsto (fun G : ℝ ↦
      Real.log (shrinkingMeshLength G : ℝ) / Real.log G)
      atTop (nhds (1 / 2 : ℝ)) := by
  have hlogEq := isEquivalent_shrinkingMeshLength_sqrt.log
    Real.tendsto_sqrt_atTop
  have hlogSqrt : Tendsto (fun G : ℝ ↦ Real.log (Real.sqrt G))
      atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_sqrt_atTop
  have hneSqrt := hlogSqrt.eventually_ne_atTop 0
  have hratio : Tendsto (fun G : ℝ ↦
      Real.log (shrinkingMeshLength G : ℝ) /
        Real.log (Real.sqrt G)) atTop (nhds 1) := by
    rw [isEquivalent_iff_tendsto_one hneSqrt] at hlogEq
    exact hlogEq
  have hprod : Tendsto (fun G : ℝ ↦
      (Real.log (shrinkingMeshLength G : ℝ) /
        Real.log (Real.sqrt G)) *
          (Real.log (Real.sqrt G) / Real.log G))
      atTop (nhds (1 / 2 : ℝ)) := by
    simpa only [one_mul] using hratio.mul tendsto_log_sqrt_div_log
  refine hprod.congr' ?_
  filter_upwards [hneSqrt,
    Real.tendsto_log_atTop.eventually_ne_atTop 0] with G hsqrt hG
  field_simp [hsqrt, hG]

theorem tendsto_log_div_log_shrinkingMesh :
    Tendsto (fun G : ℝ ↦ Real.log G /
      Real.log (shrinkingMeshLength G : ℝ)) atTop (nhds 2) := by
  have h := tendsto_log_shrinkingMesh_div_log
  have hinv := h.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  simpa [inv_div] using hinv

/-- Direct diagonal density coefficient: the Selberg constant two at scale H
is multiplied by `log G/log H -> 2`. -/
theorem tendsto_shrinkingMesh_densityCoefficient :
    Tendsto (fun G : ℝ ↦
      densityUpper (shrinkingMeshLength G) * Real.log G)
      atTop (nhds 4) := by
  have hcoef := tendsto_densityCoefficient.comp
    tendsto_shrinkingMeshLength_atTop
  have hprod : Tendsto (fun G : ℝ ↦
      densityCoefficient (shrinkingMeshLength G) *
        (Real.log G / Real.log (shrinkingMeshLength G : ℝ)))
      atTop (nhds 4) := by
    convert hcoef.mul tendsto_log_div_log_shrinkingMesh using 1 <;> norm_num
  refine hprod.congr' ?_
  filter_upwards [tendsto_shrinkingMeshLength_atTop.eventually
    (eventually_gt_atTop 1)] with G hH
  have hlogH : Real.log (shrinkingMeshLength G : ℝ) ≠ 0 :=
    (Real.log_pos (Nat.one_lt_cast.mpr hH)).ne'
  rw [densityCoefficient_eq]
  field_simp [hlogH]

theorem eventually_one_le_shrinkingMeshRadius :
    ∀ᶠ G : ℝ in atTop, 1 ≤ shrinkingMeshRadius G := by
  exact tendsto_shrinkingMeshLength_atTop.eventually
    eventually_one_le_selbergRadius

theorem eventually_shrinkingMeshRadius_le_length :
    ∀ᶠ G : ℝ in atTop,
      shrinkingMeshRadius G ≤ shrinkingMeshLength G := by
  exact tendsto_shrinkingMeshLength_atTop.eventually
    eventually_selbergRadius_le_self

theorem eventually_shrinkingMeshLength_le_floor :
    ∀ᶠ G : ℝ in atTop, shrinkingMeshLength G ≤ ⌊G⌋₊ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with G hG
  unfold shrinkingMeshLength
  apply Nat.floor_mono
  exact Real.sqrt_le_self_iff.mpr (Or.inr hG)

theorem eventually_shrinkingMeshDelta_le_rpow :
    ∀ᶠ G : ℝ in atTop, shrinkingMeshDelta G ≤ G ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with G hG
  have hG0 : 0 < G := zero_lt_one.trans hG
  have hfloor : (shrinkingMeshLength G : ℝ) ≤ Real.sqrt G := by
    unfold shrinkingMeshLength
    exact Nat.floor_le (Real.sqrt_nonneg G)
  have hdiv := div_le_div_of_nonneg_right hfloor hG0.le
  calc
    shrinkingMeshDelta G ≤ Real.sqrt G / G := by
      simpa only [shrinkingMeshDelta] using hdiv
    _ = G ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hG0.ne']
      congr 1
      ring

/-- Complete diagonal mesh package. The constant six is a deliberately
generous eventual form of the limiting coefficient four. -/
theorem eventually_shrinkingMesh_data :
    ∀ᶠ G : ℝ in atTop,
      1 < G ∧
      1 ≤ shrinkingMeshRadius G ∧
      shrinkingMeshRadius G ≤ shrinkingMeshLength G ∧
      shrinkingMeshLength G ≤ ⌊G⌋₊ ∧
      shrinkingMeshDelta G ≤ G ^ (-(1 / 2 : ℝ)) ∧
      cellCap (shrinkingMeshLength G) (shrinkingMeshRadius G) /
          shrinkingMeshDelta G ≤ 6 * G / Real.log G := by
  have hcoef := (tendsto_order.mp tendsto_shrinkingMesh_densityCoefficient).2
    6 (by norm_num : (4 : ℝ) < 6)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_one_le_shrinkingMeshRadius,
    eventually_shrinkingMeshRadius_le_length,
    eventually_shrinkingMeshLength_le_floor,
    eventually_shrinkingMeshDelta_le_rpow, hcoef]
      with G hG hR hRH hHG hδ hcoefG
  have hG0 : 0 < G := zero_lt_one.trans hG
  have hH : 1 ≤ shrinkingMeshLength G := hR.trans hRH
  have hfinite := finite_density_upper hG0 hH hR
  change cellCap (shrinkingMeshLength G) (shrinkingMeshRadius G) /
      shrinkingMeshDelta G ≤
        G * densityUpper (shrinkingMeshLength G) at hfinite
  have hlogG : 0 < Real.log G := Real.log_pos hG
  have hdensity : densityUpper (shrinkingMeshLength G) ≤ 6 / Real.log G :=
    (le_div_iff₀ hlogG).2 hcoefG.le
  have hscaled := mul_le_mul_of_nonneg_left hdensity hG0.le
  refine ⟨hG, hR, hRH, hHG, hδ, hfinite.trans ?_⟩
  exact hscaled.trans_eq (by ring)

/-- Finite positive insertion with complete cells and a genuinely separate
last partial cell. The endpoint costs `C*delta`; it is not padded into the
Lipschitz integral, so the oscillation cost is only `K*W*delta`. The test is
globally nonnegative and bounded, and no compact-slot parameter or
test-dependent threshold occurs. -/
theorem finite_positive_insertion_with_last_cell
    {E : Finset ℕ} {a H R : ℕ} {G C W : ℝ}
    (hG : 0 < G) (hR : 1 ≤ R) (hRH : R ≤ H)
    (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hE : ∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G)
    (havoid : AvoidsResidues E R)
    (f : ℝ → ℝ) {K : ℝ≥0} (hLip : LipschitzWith K f)
    (hf : ∀ t : ℝ, 0 ≤ f t ∧ f t ≤ C) :
    (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
      cellCap H R / ((H : ℝ) / G) *
        ((∫ t in 0..W, f t) + (K : ℝ) * W * ((H : ℝ) / G) +
          C * ((H : ℝ) / G)) := by
  let δ : ℝ := (H : ℝ) / G
  let M : ℕ := ⌊W / δ⌋₊
  let Efull : Finset ℕ := E.filter (fun n ↦ n ≤ a + M * H)
  let Elast : Finset ℕ := E.filter (fun n ↦ a + M * H < n)
  have hH : 0 < H := lt_of_lt_of_le (by omega : 0 < R) hRH
  have hδ : 0 < δ := div_pos (Nat.cast_pos.mpr hH) hG
  have hMlow : (M : ℝ) * δ ≤ W := by
    have hh := Nat.floor_le (div_nonneg hW hδ.le)
    have hmul := mul_le_mul_of_nonneg_right hh hδ.le
    exact hmul.trans_eq (by field_simp [hδ.ne'])
  have hMhigh : W < (((M + 1 : ℕ) : ℝ)) * δ := by
    have hh := Nat.lt_floor_add_one (W / δ)
    have hh' : W / δ < (((M + 1 : ℕ) : ℝ)) := by
      simpa only [M, Nat.cast_add, Nat.cast_one] using hh
    exact (div_lt_iff₀ hδ).mp hh'
  have hsumSplit :
      (∑ n ∈ E, f (((n : ℝ) - a) / G)) =
        (∑ n ∈ Efull, f (((n : ℝ) - a) / G)) +
          ∑ n ∈ Elast, f (((n : ℝ) - a) / G) := by
    have hh := (sum_filter_add_sum_filter_not
      (s := E) (p := fun n ↦ n ≤ a + M * H)
      (f := fun n ↦ f (((n : ℝ) - a) / G))).symm
    simpa only [Efull, Elast, not_le] using hh
  have hEfull : Efull ⊆ Finset.Ioc a (a + M * H) := by
    intro n hn
    have hn' := mem_filter.mp hn
    exact Finset.mem_Ioc.mpr ⟨(hE n hn'.1).1, hn'.2⟩
  have havoidFull : AvoidsResidues Efull R :=
    havoid.mono (filter_subset _ _)
  have hgrid := CoreSelberg.finite_mesh_majorant hG hR hRH
    hEfull havoidFull f hLip (fun t _ ↦ (hf t).1)
  change δ * (∑ n ∈ Efull, f (((n : ℝ) - a) / G)) ≤
      cellCap H R * ((∫ t in 0..((M : ℝ) * δ), f t) +
        (K : ℝ) * M * δ ^ 2) at hgrid
  have hInt :
      (∫ t in 0..((M : ℝ) * δ), f t) ≤ ∫ t in 0..W, f t := by
    have hfirst : IntervalIntegrable f MeasureTheory.volume 0 ((M : ℝ) * δ) :=
      hLip.continuous.intervalIntegrable 0 ((M : ℝ) * δ)
    have hlast : IntervalIntegrable f MeasureTheory.volume ((M : ℝ) * δ) W :=
      hLip.continuous.intervalIntegrable ((M : ℝ) * δ) W
    have hadd := intervalIntegral.integral_add_adjacent_intervals hfirst hlast
    have hnon : 0 ≤ ∫ t in ((M : ℝ) * δ)..W, f t :=
      intervalIntegral.integral_nonneg hMlow (fun t _ ↦ (hf t).1)
    linarith
  have hLipTerm : (K : ℝ) * M * δ ^ 2 ≤ (K : ℝ) * W * δ := by
    calc
      (K : ℝ) * M * δ ^ 2 = ((K : ℝ) * ((M : ℝ) * δ)) * δ := by ring
      _ ≤ ((K : ℝ) * W) * δ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMlow K.coe_nonneg) hδ.le
      _ = (K : ℝ) * W * δ := rfl
  have hfullBracket :
      (∫ t in 0..((M : ℝ) * δ), f t) + (K : ℝ) * M * δ ^ 2 ≤
        (∫ t in 0..W, f t) + (K : ℝ) * W * δ :=
    _root_.add_le_add hInt hLipTerm
  have hfullScaled :
      δ * (∑ n ∈ Efull, f (((n : ℝ) - a) / G)) ≤
        cellCap H R * ((∫ t in 0..W, f t) + (K : ℝ) * W * δ) := by
    exact hgrid.trans (mul_le_mul_of_nonneg_left hfullBracket
      (cellCap_nonneg H R hR))
  have hδG : δ * G = (H : ℝ) := by
    dsimp only [δ]
    field_simp [hG.ne']
  have hEupper : ∀ n ∈ E, n ≤ a + (M + 1) * H := by
    intro n hn
    have hnData := hE n hn
    have hWG := mul_lt_mul_of_pos_right hMhigh hG
    have hright : (((M + 1 : ℕ) : ℝ)) * δ * G =
        (((M + 1) * H : ℕ) : ℝ) := by
      rw [mul_assoc, hδG]
      push_cast
      rfl
    rw [hright] at hWG
    have hnReal : (n : ℝ) < ((a + (M + 1) * H : ℕ) : ℝ) := by
      push_cast at hWG ⊢
      nlinarith [hnData.2]
    have hnNat : n < a + (M + 1) * H := Nat.cast_lt.mp hnReal
    exact hnNat.le
  have hElast : Elast ⊆ Finset.Ioc (a + M * H) ((a + M * H) + H) := by
    intro n hn
    have hn' := mem_filter.mp hn
    apply Finset.mem_Ioc.mpr
    refine ⟨hn'.2, ?_⟩
    have hu := hEupper n hn'.1
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hu
  have havoidLast : AvoidsResidues Elast R :=
    havoid.mono (filter_subset _ _)
  have hlastCard := CoreSelberg.translated_card_le hR hRH hElast havoidLast
  change (Elast.card : ℝ) ≤ cellCap H R at hlastCard
  have hlastSum :
      (∑ n ∈ Elast, f (((n : ℝ) - a) / G)) ≤ C * cellCap H R := by
    calc
      (∑ n ∈ Elast, f (((n : ℝ) - a) / G)) ≤ ∑ _n ∈ Elast, C :=
        sum_le_sum fun n _ ↦ (hf (((n : ℝ) - a) / G)).2
      _ = (Elast.card : ℝ) * C := by simp
      _ ≤ cellCap H R * C := mul_le_mul_of_nonneg_right hlastCard hC
      _ = C * cellCap H R := mul_comm _ _
  have hlastScaled :
      δ * (∑ n ∈ Elast, f (((n : ℝ) - a) / G)) ≤
        cellCap H R * (C * δ) := by
    have hh := mul_le_mul_of_nonneg_left hlastSum hδ.le
    exact hh.trans_eq (by ring)
  have hcombined :
      δ * (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
        cellCap H R *
          ((∫ t in 0..W, f t) + (K : ℝ) * W * δ + C * δ) := by
    rw [hsumSplit, mul_add]
    calc
      δ * (∑ n ∈ Efull, f (((n : ℝ) - a) / G)) +
          δ * (∑ n ∈ Elast, f (((n : ℝ) - a) / G)) ≤
        cellCap H R * ((∫ t in 0..W, f t) + (K : ℝ) * W * δ) +
          cellCap H R * (C * δ) := _root_.add_le_add hfullScaled hlastScaled
      _ = cellCap H R *
          ((∫ t in 0..W, f t) + (K : ℝ) * W * δ + C * δ) := by ring
  calc
    (∑ n ∈ E, f (((n : ℝ) - a) / G)) ≤
        (cellCap H R *
          ((∫ t in 0..W, f t) + (K : ℝ) * W * δ + C * δ)) / δ :=
      (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hcombined)
    _ = cellCap H R / ((H : ℝ) / G) *
        ((∫ t in 0..W, f t) + (K : ℝ) * W * ((H : ℝ) / G) +
          C * ((H : ℝ) / G)) := by
      dsimp only [δ]
      ring

end

end PrimeGapNormality.Prime.CoreSelbergShrinkingMesh
