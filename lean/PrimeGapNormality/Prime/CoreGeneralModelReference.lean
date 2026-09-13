import PrimeGapNormality.Prime.CoreCalibratedModelSubsequence
import PrimeGapNormality.Prime.CoreCyclicLabels
import PrimeGapNormality.Prime.CoreLocalTailAtProfile

/-! Canonical positive square-root reserve for the genuinely arbitrary
calibrated model. The nonstrict degree threshold is retained. -/

namespace PrimeGapNormality.Prime.CoreGeneralModelReference
open Filter MeasureTheory CoreCyclic CoreLocalReferencePassage
open CoreCalibratedMixtureFiniteSupport CoreCalibratedModelSubsequence
open scoped Classical Topology NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1000000

def rank (κ : ℝ) (G : ℕ → ℝ) (X : ℕ) : ℕ :=
  CoreLinearInsertion.linearProfileL κ (G X)

theorem rank_eq_stdProfile {κ : ℝ} (hκ : 0 < κ) (G : ℕ → ℝ) (X : ℕ) :
    rank κ G X = stdProfileL (localTailBase κ) (G X) := by
  simp only [rank, CoreLinearInsertion.stdProfileL_eq_linearProfileL,
    localTailBase_profileCoefficient hκ]

/-- The literal ceil(κ log G + sqrt(κ log G)) has the required ratio,
without deleting its positive reserve. -/
theorem tendsto_rank_ratio {κ : ℝ} (hκ : 0 < κ) {G : ℕ → ℝ}
    (hG : Tendsto G atTop atTop) :
    Tendsto (fun X => (rank κ G X : ℝ) / Real.log (G X)) atTop (𝓝 κ) := by
  have hl : Tendsto (fun X => Real.log (G X)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp hG
  have ht : Tendsto (fun X => κ * Real.log (G X)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hκ hl
  have hs : Tendsto (fun X => κ / Real.sqrt (κ * Real.log (G X))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp ht)).const_mul κ
  have hi : Tendsto (fun X => (Real.log (G X))⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp hl
  have herr : Tendsto (fun X => (rank κ G X : ℝ) / Real.log (G X) - κ) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa only [add_zero] using hs.add hi)
    · filter_upwards [hG.eventually_gt_atTop 1] with X hx
      have hlp := Real.log_pos hx
      have hc : κ * Real.log (G X) ≤ (rank κ G X : ℝ) :=
        (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (Nat.le_ceil _)
      exact sub_nonneg.mpr ((le_div_iff₀ hlp).2 hc)
    · filter_upwards [hG.eventually_gt_atTop 1] with X hx
      have hlp := Real.log_pos hx
      have htp : 0 < κ * Real.log (G X) := mul_pos hκ hlp
      have hsp : 0 < Real.sqrt (κ * Real.log (G X)) := Real.sqrt_pos.2 htp
      have hsquare := Real.sq_sqrt htp.le
      have hc : (rank κ G X : ℝ) ≤ κ * Real.log (G X) + Real.sqrt (κ * Real.log (G X)) + 1 :=
        (Nat.ceil_lt_add_one (add_nonneg htp.le (Real.sqrt_nonneg _))).le
      have hquot : Real.sqrt (κ * Real.log (G X)) / Real.log (G X) =
          κ / Real.sqrt (κ * Real.log (G X)) := by
        apply (div_eq_div_iff hlp.ne' hsp.ne').2
        nlinarith
      have hc' := div_le_div_of_nonneg_right hc hlp.le
      have he : (κ * Real.log (G X) + Real.sqrt (κ * Real.log (G X)) + 1) /
          Real.log (G X) = κ + κ / Real.sqrt (κ * Real.log (G X)) + (Real.log (G X))⁻¹ := by
        rw [add_div, add_div, mul_div_cancel_right₀ _ hlp.ne', hquot, one_div]
      rw [he] at hc'
      linarith
  have hh := herr.add_const κ
  simpa only [sub_add_cancel, zero_add] using hh

theorem tendsto_rank_atTop {κ : ℝ} (hκ : 0 < κ) {G : ℕ → ℝ}
    (hG : Tendsto G atTop atTop) : Tendsto (rank κ G) atTop atTop := by
  change Tendsto (fun X : ℕ => rank κ G X) atTop atTop
  apply tendsto_atTop.mpr
  intro n
  have hlog : Tendsto (fun X => Real.log (G X)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp hG
  have hl := (Filter.Tendsto.const_mul_atTop hκ hlog).eventually_ge_atTop (n : ℝ)
  filter_upwards [hl] with X hx
  have hc : (n : ℝ) ≤ (rank κ G X : ℝ) := hx.trans
    ((le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (Nat.le_ceil _))
  exact_mod_cast hc

/-- Exact action-label matching at every eventually large arbitrary G,
including κ=d/log B. -/
theorem exists_admissible_ranks {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (hd : 1 ≤ d) (r s : Fin k) (w : ℕ) {κ : ℝ}
    (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ) {G : ℕ → ℝ}
    (hG : Tendsto G atTop atTop) :
    ∃ J : ℕ → ℕ, ∀ᶠ X in atTop, RankAdmissible B hk r s w d G (rank κ G) J X := by
  obtain ⟨a, ha, hlabel⟩ := exists_insertion_residue hk r s
  have hex : ∀ᶠ X in atTop, ∃ j : ℕ,
      w + 1 ≤ j ∧ j + w < rank κ G X ∧ phaseAt hk r (j - 1) = s ∧
        1 ≤ G X ^ d / (B : ℝ) ^ (j + 1) ∧ G X ^ d / (B : ℝ) ^ (j + 1) ≤ (B : ℝ) ^ k := by
    filter_upwards [hG.eventually (CoreLocalCriticalRank.eventually_critical_rank hB hk hd ha w hκ)] with X hx
    obtain ⟨j, hj, hjM, hmod, hlo, hhi⟩ := hx
    exact ⟨j, hj, hjM, hlabel j (by omega) hmod, hlo, hhi.le⟩
  let p (X j : ℕ) : Prop := w + 1 ≤ j ∧ j + w < rank κ G X ∧ phaseAt hk r (j - 1) = s ∧
    1 ≤ G X ^ d / (B : ℝ) ^ (j + 1) ∧ G X ^ d / (B : ℝ) ^ (j + 1) ≤ (B : ℝ) ^ k
  let J : ℕ → ℕ := fun X => if h : ∃ j, p X j then Classical.choose h else 0
  refine ⟨J, ?_⟩
  filter_upwards [hex] with X hx
  have hpx : ∃ j, p X j := hx
  have hj : p X (J X) := by
    dsimp only [J]
    rw [dif_pos hpx]
    exact Classical.choose_spec hpx
  exact hj

/-- Canonical-reserve model theorem. No rank-admissibility premise remains. -/
theorem exists_reference_subsequence
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ s i, i ∈ (N s).vars → i ≤ w)
    {κ : ℝ} (hκ : (topDegree N : ℝ) / Real.log (B : ℝ) ≤ κ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    {ω : ℕ → ℕ → ℝ} (hω : ∀ X y, 0 ≤ ω X y)
    (hsum : ∀ X, ∑' y, ω X y = 1) (hcal : UniformCalibration ω G) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ σ : Measure (AddCircle (1 : ℝ)),
      IsFiniteMeasure σ ∧ σ ≪ volume ∧ σ Set.univ ≤ ENNReal.ofReal 4 ∧
      ∀ (f : (AddCircle (1 : ℝ)) →ᵇ ℝ) (Kf : ℝ≥0), LipschitzWith Kf f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          modelMean B hk r N w G (rank κ G) ω (φ n) f ≤
            CoreCalibratedModelFinite.modelConstant * (∫ x, f x ∂σ) + ε := by
  have hd := one_le_topDegree_of_rooted hk N hroot hN
  have hb : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hκp : 0 < κ := (div_pos (Nat.cast_pos.2 (show 0 < topDegree N by omega))
    (Real.log_pos hb)).trans_le hκ
  obtain ⟨s, hs⟩ := exists_rooted_model_reference hB hk r w N hroot hN hw
  obtain ⟨J, hJ⟩ := exists_admissible_ranks hB hk hd r s w hκ hG
  exact hs G (rank κ G) κ hG hκp (tendsto_rank_ratio hκp hG) ω hω hsum hcal J hJ

end
end PrimeGapNormality.Prime.CoreGeneralModelReference
