import PrimeGapNormality.Prime.CoreLinearCriticalRank

/-!
# Critical rank with both local-width margins

The supplied arithmetic depth κ is retained, including equality at the
degree/base threshold. The square-root reserve absorbs the fixed width and
period; neither an L+w window nor a strict κ inequality is introduced.
-/

namespace PrimeGapNormality.Prime.CoreLocalCriticalRank
open Filter Finset
open scoped Topology
noncomputable section

private theorem rank_scale {B j d : ℕ} (hB : 2 ≤ B) (G : ℝ) :
    |1 / (B : ℝ)| * G ^ d * (B : ℝ) ^ (-(j : ℤ)) =
      G ^ d / (B : ℝ) ^ (j + 1) := by
  have hb : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  rw [abs_of_pos (one_div_pos.mpr hb), zpow_neg, zpow_natCast, pow_succ]
  field_simp [hb.ne', pow_ne_zero j hb.ne'] <;> ring

/-- A residue-constrained rank with both finite local-width margins. -/
theorem eventually_critical_rank
    {B k d r : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hr : r ∈ Icc 1 k) (w : ℕ) {κ : ℝ}
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    ∀ᶠ G : ℝ in atTop, ∃ j : ℕ,
      w + 1 ≤ j ∧ j + w < CoreLinearInsertion.linearProfileL κ G ∧
      Nat.ModEq k j r ∧
      1 ≤ G ^ d / (B : ℝ) ^ (j + 1) ∧
      G ^ d / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k := by
  have hb : (1 : ℝ) < B := Nat.one_lt_cast.mpr (by omega)
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos hb
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hκpos : 0 < κ := (div_pos hdpos hlog).trans_le hκ
  have hb0 : (B : ℝ) ≠ 0 := (zero_lt_one.trans hb).ne'
  obtain ⟨G₀, C, hC, hselect⟩ := exists_rankSelect_in_range_ge
    (B := B) (k := k) (r := r) (R := d) (η := 1 / (B : ℝ)) (J := 0)
    hB hk hr (div_ne_zero one_ne_zero hb0) hd hκ
  have hreserve : Tendsto (fun G : ℝ ↦ Real.sqrt (κ * Real.log G)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Filter.Tendsto.const_mul_atTop hκpos Real.tendsto_log_atTop)
  filter_upwards [eventually_ge_atTop G₀, eventually_ge_atTop (1 : ℝ),
    eventually_gt_atTop ((B : ℝ) ^ (w + k + 1)),
    hreserve.eventually (eventually_ge_atTop (C + (w : ℝ) + 1))]
      with G hGG₀ hG1 hGbig hres
  let L := CoreLinearInsertion.linearProfileL κ G
  have hκlog : 0 ≤ κ * Real.log G := mul_nonneg hκpos.le (Real.log_nonneg hG1)
  have hceil : κ * Real.log G + Real.sqrt (κ * Real.log G) ≤ (L : ℝ) := Nat.le_ceil _
  have hwL : w ≤ L := by
    have hreal : (w : ℝ) ≤ (L : ℝ) := by linarith
    exact_mod_cast hreal
  have hbudget : κ * Real.log G + C ≤ ((L - w : ℕ) : ℝ) := by
    rw [Nat.cast_sub hwL]
    linarith
  obtain ⟨j, hj, _hmod, hlo, hhi, hjdef⟩ := hselect G hGG₀ (L - w) hbudget
  have hjN := mem_Ico.mp hj
  have hmod : Nat.ModEq k j r := by
    rw [hjdef]
    exact rankSelect_modEq
  have hlo' : 1 ≤ G ^ d / (B : ℝ) ^ (j + 1) := by
    simpa only [zpow_zero, rank_scale hB] using hlo
  have hhi' : G ^ d / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k := by
    simpa only [zero_add, zpow_natCast, rank_scale hB] using hhi
  have hjlower : w + 1 ≤ j := by
    by_contra hn
    have hjw : j ≤ w := by omega
    have hpowj : (B : ℝ) ^ (j + 1) ≤ (B : ℝ) ^ (w + 1) :=
      pow_le_pow_right₀ hb.le (by omega)
    have hmul := (div_lt_iff₀ (pow_pos (zero_lt_one.trans hb) (j + 1))).mp hhi'
    have hu : (B : ℝ) ^ k * (B : ℝ) ^ (j + 1) ≤ (B : ℝ) ^ (w + k + 1) := by
      calc
        (B : ℝ) ^ k * (B : ℝ) ^ (j + 1) ≤ (B : ℝ) ^ k * (B : ℝ) ^ (w + 1) :=
          mul_le_mul_of_nonneg_left hpowj (pow_nonneg (zero_lt_one.trans hb).le k)
        _ = (B : ℝ) ^ (w + k + 1) := by
          rw [← pow_add]
          congr 1
          omega
    have hGpow : G ≤ G ^ d := le_self_pow₀ hG1 (by omega : d ≠ 0)
    linarith
  exact ⟨j, hjlower, by dsimp only [L] at *; omega, hmod, hlo', hhi'⟩

/-- Actual physical-window specialization; the depth and width are unchanged. -/
theorem eventually_critical_rank_profile
    {B k d r : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hr : r ∈ Icc 1 k) (w : ℕ) {κ : ℝ}
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) :
    ∀ᶠ X : ℕ in atTop, ∃ j : ℕ,
      w + 1 ≤ j ∧ j + w < profileL κ X ∧ Nat.ModEq k j r ∧
      1 ≤ windowG X ^ d / (B : ℝ) ^ (j + 1) ∧
      windowG X ^ d / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k := by
  have hG : Tendsto windowG atTop atTop :=
    tendsto_atTop_mono (fun X ↦ le_max_left (Real.log (X : ℝ)) (1 : ℝ))
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact hG.eventually (eventually_critical_rank hB hk hd hr w hκ)

end
end PrimeGapNormality.Prime.CoreLocalCriticalRank
