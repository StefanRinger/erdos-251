import PrimeGapNormality.Prime.CoreSelbergInsertionCells

/-! Numerical mesh asymptotics for the positive insertion majorant. -/

namespace PrimeGapNormality.Prime.CoreSelberg

open Filter Asymptotics
open scoped Topology

noncomputable section

def meshLength (δ G : ℝ) : ℕ := ⌊δ * G⌋₊

theorem tendsto_meshLength_atTop {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (meshLength δ) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Filter.Tendsto.const_mul_atTop hδ tendsto_id)

theorem isEquivalent_meshLength {δ : ℝ} (hδ : 0 < δ) :
    (fun G : ℝ ↦ (meshLength δ G : ℝ)) ~[atTop] (fun G ↦ δ * G) := by
  exact Asymptotics.isEquivalent_nat_floor.comp_tendsto
    (Filter.Tendsto.const_mul_atTop hδ tendsto_id)

theorem tendsto_log_scaled_div_log {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun G : ℝ ↦ Real.log (δ * G) / Real.log G) atTop (nhds 1) := by
  have hsmall : Tendsto (fun G : ℝ ↦ Real.log δ / Real.log G) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := Real.log δ)).mul Real.tendsto_log_atTop.inv_tendsto_atTop
  have hlim : Tendsto (fun G : ℝ ↦ Real.log δ / Real.log G + 1) atTop (nhds 1) := by
    simpa using hsmall.add_const 1
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with G hG
  have hg0 : G ≠ 0 := (lt_trans zero_lt_one hG).ne'
  have hlog : Real.log G ≠ 0 := (Real.log_pos hG).ne'
  rw [Real.log_mul hδ.ne' hg0]
  field_simp [hlog] <;> ring

theorem tendsto_log_mesh_div_log {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun G : ℝ ↦ Real.log (meshLength δ G : ℝ) / Real.log G) atTop (nhds 1) := by
  have hlog := (isEquivalent_meshLength hδ).log
    (Filter.Tendsto.const_mul_atTop hδ tendsto_id)
  have hquot : (fun G : ℝ ↦ Real.log (meshLength δ G : ℝ) / Real.log G) ~[atTop]
      (fun G : ℝ ↦ Real.log (δ * G) / Real.log G) := hlog.div IsEquivalent.refl
  exact hquot.tendsto_nhds_iff.mpr (tendsto_log_scaled_div_log hδ)

theorem tendsto_log_div_log_mesh {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun G : ℝ ↦ Real.log G / Real.log (meshLength δ G : ℝ)) atTop (nhds 1) := by
  simpa [inv_div] using (tendsto_log_mesh_div_log hδ).inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)

def densityUpper (H : ℕ) : ℝ :=
  1 / Real.log (selbergRadius H + 1 : ℝ) + (selbergRadius H : ℝ) ^ 2 / H

def densityCoefficient (H : ℕ) : ℝ :=
  Real.log (H : ℝ) / Real.log (selbergRadius H + 1 : ℝ) +
    (selbergRadius H : ℝ) ^ 2 * Real.log (H : ℝ) / H

theorem densityCoefficient_eq (H : ℕ) :
    densityCoefficient H = Real.log (H : ℝ) * densityUpper H := by
  unfold densityCoefficient densityUpper
  ring

theorem tendsto_densityCoefficient : Tendsto densityCoefficient atTop (nhds 2) := by
  change Tendsto (fun H : ℕ ↦ Real.log (H : ℝ) / Real.log (selbergRadius H + 1 : ℝ) +
    (selbergRadius H : ℝ) ^ 2 * Real.log (H : ℝ) / (H : ℝ)) atTop (nhds (2 : ℝ))
  simpa only [Nat.cast_add, Nat.cast_one, add_zero] using
    tendsto_log_div_log_selbergRadius_add_one.add tendsto_selbergRadius_sq_mul_log_div

theorem tendsto_mesh_density_log {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun G : ℝ ↦ densityUpper (meshLength δ G) * Real.log G) atTop (nhds 2) := by
  have hprod := (tendsto_densityCoefficient.comp (tendsto_meshLength_atTop hδ)).mul
    (tendsto_log_div_log_mesh hδ)
  have hprod' : Tendsto (fun G : ℝ ↦ densityCoefficient (meshLength δ G) *
      (Real.log G / Real.log (meshLength δ G : ℝ))) atTop (nhds 2) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [(tendsto_meshLength_atTop hδ).eventually (eventually_gt_atTop 1)] with G hH
  have hlog : Real.log (meshLength δ G : ℝ) ≠ 0 :=
    (Real.log_pos (Nat.one_lt_cast.mpr hH)).ne'
  rw [densityCoefficient_eq]
  field_simp [hlog] <;> ring

theorem finite_density_upper {G : ℝ} {H : ℕ} (hG : 0 < G) (hH : 1 ≤ H)
    (hR : 1 ≤ selbergRadius H) :
    (((H : ℝ) / selbergJR (selbergRadius H) + (selbergRadius H : ℝ) ^ 2) /
      ((H : ℝ) / G)) ≤ G * densityUpper H := by
  have hH0 : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hJ0 : selbergJR (selbergRadius H) ≠ 0 := (selbergJR_pos hR).ne'
  have hlog : 0 < Real.log (selbergRadius H + 1 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (Nat.lt_succ_of_le hR)
  have hrecip : 1 / selbergJR (selbergRadius H) ≤
      1 / Real.log (selbergRadius H + 1 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hlog (selbergJR_ge_log_add_one _)
  calc
    (((H : ℝ) / selbergJR (selbergRadius H) + (selbergRadius H : ℝ) ^ 2) /
        ((H : ℝ) / G)) = G * (1 / selbergJR (selbergRadius H) +
          (selbergRadius H : ℝ) ^ 2 / H) := by
      field_simp [hH0, hG.ne', hJ0] <;> ring
    _ ≤ G * densityUpper H :=
      mul_le_mul_of_nonneg_left (add_le_add hrecip le_rfl) hG.le

/-- Fixed normalized mesh sizes give a uniform `3G/log G` density cap;
all sieve-radius and floor-cutoff side conditions are also derived here. -/
theorem eventually_mesh_density_le_three {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ G : ℝ in atTop,
      1 < G ∧ 1 ≤ meshLength δ G ∧ 1 ≤ selbergRadius (meshLength δ G) ∧
      selbergRadius (meshLength δ G) ≤ meshLength δ G ∧
      meshLength δ G ≤ ⌊G⌋₊ ∧ (meshLength δ G : ℝ) / G ≤ δ ∧
      (((meshLength δ G : ℝ) / selbergJR (selbergRadius (meshLength δ G)) +
          (selbergRadius (meshLength δ G) : ℝ) ^ 2) / ((meshLength δ G : ℝ) / G)) ≤
        3 * G / Real.log G := by
  have hlim := tendsto_mesh_density_log hδ
  have hlt : ∀ᶠ G : ℝ in atTop, densityUpper (meshLength δ G) * Real.log G < 3 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (2 : ℝ) < 3))
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_meshLength_atTop hδ).eventually (eventually_ge_atTop 1),
    (tendsto_meshLength_atTop hδ).eventually eventually_one_le_selbergRadius,
    (tendsto_meshLength_atTop hδ).eventually eventually_selbergRadius_le_self, hlt]
      with G hG hH hR hRH hcoef
  have hG0 : 0 < G := lt_trans zero_lt_one hG
  have hmesh : meshLength δ G ≤ ⌊G⌋₊ :=
    Nat.floor_mono (by nlinarith)
  have hmeshδ : (meshLength δ G : ℝ) / G ≤ δ := by
    apply (div_le_iff₀ hG0).2
    exact Nat.floor_le (mul_nonneg hδ.le hG0.le)
  refine ⟨hG, hH, hR, hRH, hmesh, hmeshδ, ?_⟩
  calc
    _ ≤ G * densityUpper (meshLength δ G) := finite_density_upper hG0 hH hR
    _ ≤ G * (3 / Real.log G) := mul_le_mul_of_nonneg_left
      ((le_div_iff₀ (Real.log_pos hG)).2 hcoef.le) hG0.le
    _ = 3 * G / Real.log G := by ring

theorem AvoidsResidues.radius_mono {E : Finset ℕ} {R S : ℕ}
    (hE : AvoidsResidues E S) (hRS : R ≤ S) : AvoidsResidues E R :=
  fun p hp ↦ hE p (Nat.primesLE_mono hRS hp)

end

end PrimeGapNormality.Prime.CoreSelberg
