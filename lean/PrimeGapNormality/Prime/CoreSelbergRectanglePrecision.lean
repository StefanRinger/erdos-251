import PrimeGapNormality.Prime.CoreActualFrameRectangleLimit

/-!
# Sharper padded rectangle caps from the existing finite Selberg bound

The earlier factor eight paid a factor two for integer padding. Padding
is asymptotically negligible for any fixed positive interval length.
Keeping this slack explicit gives a factor three, with the SAME actual
radius and no new sieve estimate. Source pending central compilation.
-/

namespace PrimeGapNormality.Prime.CoreSelbergRectanglePrecision

open Filter
open CoreActualFrameRectangles CoreActualFrameRectangleLimit
open scoped Topology
noncomputable section

private theorem log_div_self_tendsto_zero :
    Tendsto (fun G : ℝ => Real.log G / G) atTop (𝓝 0) := by
  simpa only [pow_one, one_mul, add_zero] using
    Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)

theorem eventually_candidateCap_le_three {a b : ℝ} (hab : a < b) :
    ∀ᶠ G : ℝ in atTop,
      1 < G ∧ 1 ≤ rectangleRadius (b - a) G ∧
      rectangleRadius (b - a) G ≤ intervalLength (G * (b - a)) ∧
      rectangleRadius (b - a) G ≤ ⌊G⌋₊ ∧
      (candidateCap G a b (rectangleRadius (b - a) G) : ℝ) ≤
        3 * G / Real.log G * (b - a) := by
  let Δ := b - a
  let δ := min Δ 1
  have hΔ : 0 < Δ := sub_pos.mpr hab
  have hδ : 0 < δ := lt_min hΔ zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδΔ : δ ≤ Δ := min_le_left _ _
  have hc := (CoreSelberg.tendsto_mesh_density_log hδ).eventually_le_const
    (by norm_num : (2 : ℝ) < 5 / 2)
  filter_upwards [CoreSelberg.eventually_mesh_density_le_three hδ hδ1, hc,
    eventually_ge_atTop (20 / Δ),
    log_div_self_tendsto_zero.eventually_le_const (div_pos hΔ (by norm_num : (0 : ℝ) < 4))]
    with G hmesh hcoef hlarge hlogsmall
  obtain ⟨hG, hh, hR, hRh, hfloor, _, _⟩ := hmesh
  let h := CoreSelberg.meshLength δ G
  let R := selbergRadius h
  let H := intervalLength (G * Δ)
  have hg : 0 < G := zero_lt_one.trans hG
  have hl : 0 < Real.log G := Real.log_pos hG
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hJ : selbergJR R ≠ 0 := (selbergJR_pos hR).ne'
  have hHh : h ≤ H := by
    have hmδ : (h : ℝ) ≤ δ * G := Nat.floor_le (mul_nonneg hδ.le hg.le)
    have hm : (h : ℝ) ≤ G * Δ := by nlinarith
    have hcH := Nat.le_ceil (G * Δ)
    have hreal : (h : ℝ) ≤ (H : ℝ) := by
      dsimp only [H, intervalLength]
      push_cast
      linarith
    exact_mod_cast hreal
  have hHsmall : (H : ℝ) ≤ (11 / 10 : ℝ) * G * Δ := by
    have hsize : 20 ≤ G * Δ := (div_le_iff₀ hΔ).mp hlarge
    have hcH := (Nat.ceil_lt_add_one (mul_nonneg hg.le hΔ.le)).le
    dsimp only [H, intervalLength]
    push_cast
    nlinarith
  have hscale : 1 ≤ (H : ℝ) / h := (le_div_iff₀ hhpos).mpr
    (by simpa only [one_mul] using (Nat.cast_le.mpr hHh : (h : ℝ) ≤ H))
  have hbase : CoreSelberg.cellCap h R / ((h : ℝ) / G) ≤
      (5 / 2 : ℝ) * G / Real.log G := by
    calc
      _ ≤ G * CoreSelberg.densityUpper h := CoreSelberg.finite_density_upper hg hh hR
      _ ≤ G * ((5 / 2 : ℝ) / Real.log G) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ hl).mpr hcoef) hg.le
      _ = _ := by ring
  have hmeshcap : CoreSelberg.cellCap h R ≤
      ((5 / 2 : ℝ) * G / Real.log G) * ((h : ℝ) / G) :=
    (div_le_iff₀ (div_pos hhpos hg)).mp hbase
  have hpad : CoreSelberg.cellCap H R ≤ (5 / 2 : ℝ) * H / Real.log G := by
    calc
      _ = (H : ℝ) / selbergJR R + (R : ℝ) ^ 2 := rfl
      _ ≤ (H : ℝ) / selbergJR R + ((H : ℝ) / h) * (R : ℝ) ^ 2 :=
        _root_.add_le_add le_rfl (by nlinarith [sq_nonneg (R : ℝ)])
      _ = ((H : ℝ) / h) * CoreSelberg.cellCap h R := by
        unfold CoreSelberg.cellCap
        field_simp [hhpos.ne', hJ] <;> ring
      _ ≤ ((H : ℝ) / h) *
          (((5 / 2 : ℝ) * G / Real.log G) * ((h : ℝ) / G)) :=
        mul_le_mul_of_nonneg_left hmeshcap (div_nonneg (Nat.cast_nonneg _) hhpos.le)
      _ = (5 / 2 : ℝ) * H / Real.log G := by
        field_simp [hhpos.ne', hg.ne', hl.ne'] <;> ring
  have hone : 1 ≤ (1 / 4 : ℝ) * G * Δ / Real.log G := by
    have hsmall := (div_le_iff₀ hg).mp hlogsmall
    apply (le_div_iff₀ hl).mpr
    nlinarith
  have hrounded : (candidateCap G a b R : ℝ) ≤ CoreSelberg.cellCap H R + 1 :=
    (Nat.ceil_lt_add_one (CoreSelberg.cellCap_nonneg H R hR)).le
  have hmain : (5 / 2 : ℝ) * (H : ℝ) / Real.log G ≤
      (11 / 4 : ℝ) * G * Δ / Real.log G :=
    div_le_div_of_nonneg_right (by nlinarith only [hHsmall]) hl.le
  have hfinal : (candidateCap G a b R : ℝ) ≤ 3 * G / Real.log G * Δ := by
    calc
      _ ≤ (5 / 2 : ℝ) * H / Real.log G + 1 :=
        hrounded.trans (_root_.add_le_add hpad le_rfl)
      _ ≤ (11 / 4 : ℝ) * G * Δ / Real.log G +
          (1 / 4 : ℝ) * G * Δ / Real.log G := _root_.add_le_add hmain hone
      _ = _ := by ring
  exact ⟨hG, hR, hRh.trans hHh, hRh.trans hfloor, hfinal⟩

end
end PrimeGapNormality.Prime.CoreSelbergRectanglePrecision
