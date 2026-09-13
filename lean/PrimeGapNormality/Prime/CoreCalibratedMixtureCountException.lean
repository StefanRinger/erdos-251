import PrimeGapNormality.Prime.CoreCalibratedMixtureMoments
import PrimeGapNormality.Prime.CorePresieveGlobalCountLimit
import PrimeGapNormality.Prime.CoreFiniteRootMixUpperException

/-!
# Missing and high counts in arbitrary calibrated rooted mixtures

The actual full presieve is concentrated before the supported final cutoff
is chosen. Calibration puts its late mean above a fixed 1.12M threshold.
Exact conditional variance then handles N<M and N>2|A|theta. The latter
event keeps the exposed residue environment; it is not replaced by a
threshold in an unconditioned surrogate law.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedMixtureCountException

open Finset Filter CoreCalibratedMixtureProfile CoreCalibratedMixtureFiniteSupport
  CoreCalibratedMixtureMoments CoreRoughSyntheticScale
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1500000

theorem tendsto_rank_atTop {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ)) :
    Tendsto (fun X => (M X : ℝ)) atTop atTop := by
  have hlog : Tendsto (fun X => Real.log (G X)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp hG
  have hh := Filter.Tendsto.pos_mul_atTop hκ hM hlog
  apply hh.congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with X hl
  exact div_mul_cancel₀ _ hl.ne'

theorem eulerProd_mul_gap_ge {G : ℝ} (hG : 0 < G) (y : ℕ)
    (hcal : |roughGapScale y / G - 1| ≤ 1 / 100) :
    (100 / 101 : ℝ) ≤ eulerProdNat y * G := by
  have hh : roughGapScale y ≤ (101 / 100 : ℝ) * G :=
    (div_le_iff₀ hG).mp (by have := (abs_le.mp hcal).2; linarith)
  have hm := mul_le_mul_of_nonneg_right hh (eulerProdNat_pos y).le
  unfold roughGapScale at hm
  rw [inv_mul_cancel₀ (eulerProdNat_pos y).ne'] at hm
  nlinarith

/-- Quantitative coarse lower calibration of the full presieve main term.
It uses only fixed tolerances, not an error rate multiplied by M. -/
theorem eventually_main_mean_ge {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, 0 < w X y →
      (28 / 25 : ℝ) * (M X : ℝ) ≤
        ((physicalSpan G M X : ℝ) * eulerProdNat (physicalSpan G M X)) *
          lateRetention (physicalSpan G M X) y := by
  filter_upwards [eventually_rank_pos hG hκ hM,
    (tendsto_physicalSpan_atTop hG hκ hM).eventually_ge_atTop 400,
    hG.eventually_ge_atTop 100, eventually_support_above_span hG hκ hM hcal,
    hcal (1 / 100) (by norm_num)] with X hm hS hg hsup hcalX
  intro y hy
  let S := physicalSpan G M X
  have hS400 : 400 ≤ S := hS
  have hS2 : 2 ≤ S := by omega
  have hSp : (0 : ℝ) < S := Nat.cast_pos.mpr (by omega)
  have hgp : 0 < G X := by linarith
  have hmr : (1 : ℝ) ≤ M X := by exact_mod_cast hm
  have hmg : (100 : ℝ) ≤ (M X : ℝ) * G X := by nlinarith
  have hfloor : (6 / 5 : ℝ) * (M X : ℝ) * G X < (S : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hSlow : (119 / 100 : ℝ) * (M X : ℝ) * G X ≤ S := by nlinarith
  have hVS := eulerProdNat_pos S
  have hVy := eulerProdNat_pos y
  have hsmall : (4 : ℝ) / S ≤ 1 / 100 := by
    apply (div_le_iff₀ hSp).mpr
    have hh : (400 : ℝ) ≤ S := by exact_mod_cast hS400
    linarith
  have hroot : (99 / 100 : ℝ) * (eulerProdNat y / eulerProdNat S) ≤ lateRetention S y := by
    have hh := (abs_le.mp (rootedEulerProdNat_rel_div hS2 (hsup y hy).le)).1
    have hq : 0 ≤ eulerProdNat y / eulerProdNat S := div_nonneg hVy.le hVS.le
    have hmul := mul_le_mul_of_nonneg_right hsmall hq
    change _ ≤ rootedEulerProdNat S y
    nlinarith
  have hscale := eulerProd_mul_gap_ge hgp y (hcalX y hy)
  calc
    (28 / 25 : ℝ) * (M X : ℝ) ≤
        ((99 / 100 : ℝ) * (119 / 100) * (100 / 101)) * (M X : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (M X : ℝ) from Nat.cast_nonneg _]
    _ ≤ ((99 / 100 : ℝ) * (119 / 100) * (M X : ℝ)) * (eulerProdNat y * G X) := by
      have hh := mul_le_mul_of_nonneg_left hscale
        (by positivity : 0 ≤ (99 / 100 : ℝ) * (119 / 100) * (M X : ℝ))
      exact (show ((99 / 100 : ℝ) * (119 / 100) * (100 / 101)) * (M X : ℝ) =
        ((99 / 100 : ℝ) * (119 / 100) * (M X : ℝ)) * (100 / 101) by ring).le.trans hh
    _ = ((119 / 100 : ℝ) * (M X : ℝ) * G X) * ((99 / 100 : ℝ) * eulerProdNat y) := by ring
    _ ≤ (S : ℝ) * ((99 / 100 : ℝ) * eulerProdNat y) :=
      mul_le_mul_of_nonneg_right hSlow (by positivity)
    _ = ((S : ℝ) * eulerProdNat S) *
        ((99 / 100 : ℝ) * (eulerProdNat y / eulerProdNat S)) := by
      field_simp [hVS.ne'] <;> ring
    _ ≤ ((S : ℝ) * eulerProdNat S) * lateRetention S y :=
      mul_le_mul_of_nonneg_left hroot (mul_nonneg (Nat.cast_nonneg S) hVS.le)

def lowerPresieveMass (S : ℕ) : ℝ :=
  presieveSmallGlobalLowerMass S ((1 - (1 / 100 : ℝ)) * ((S : ℝ) * eulerProdNat S))

theorem tendsto_lowerPresieveMass_zero : Tendsto lowerPresieveMass atTop (𝓝 0) := by
  change Tendsto (fun S : ℕ => presieveSmallGlobalLowerMass S
    ((1 - (1 / 100 : ℝ)) * ((S : ℝ) * eulerProdNat S))) atTop (𝓝 0)
  exact CorePresieveGlobalCountLimit.tendsto_presieve_lower_mass
    (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (1 / 100 : ℝ) ≤ 1)

theorem lowerFibreMass_le {S y m : ℕ} (hS : 2 ≤ S) (hm : 0 < m)
    (hmain : (28 / 25 : ℝ) * m ≤ ((S : ℝ) * eulerProdNat S) * lateRetention S y) :
    finiteRootMixSmallLowerFibreMass S y m ≤ lowerPresieveMass S := by
  have hθ : 0 ≤ lateRetention S y := (rootedEulerProdNat_pos hS).le
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hsub : finiteRootMixSmallLowerFibreSet S y m ⊆
      (univ : Finset (ResidueChoice S)).filter (fun σ =>
        ((presieveSurvivors S σ).card : ℝ) <
          (1 - (1 / 100 : ℝ)) * ((S : ℝ) * eulerProdNat S)) := by
    intro σ hσ
    have hlow := (Finset.mem_filter.mp hσ).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hnot
    have hN := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hθ
    have hb := mul_le_mul_of_nonneg_left hmain (by norm_num : (0 : ℝ) ≤ 1 - 1 / 100)
    change ((presieveSurvivors S σ).card : ℝ) * lateRetention S y < (11 / 10 : ℝ) * m at hlow
    nlinarith
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub)) (Nat.cast_nonneg _)

def countError (G : ℕ → ℝ) (M : ℕ → ℕ) (X : ℕ) : ℝ :=
  500 / (M X : ℝ) + lowerPresieveMass (physicalSpan G M X)

theorem countError_nonneg (G : ℕ → ℝ) (M : ℕ → ℕ) (X : ℕ) : 0 ≤ countError G M X :=
  add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) (presieveSmallGlobalLowerMass_nonneg _ _)

theorem tendsto_countError_zero {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ)) :
    Tendsto (countError G M) atTop (𝓝 0) := by
  have hi := (tendsto_inv_atTop_zero.comp (tendsto_rank_atTop hG hκ hM)).const_mul 500
  have hp := tendsto_lowerPresieveMass_zero.comp (tendsto_physicalSpan_atTop hG hκ hM)
  have hh := hi.add hp
  simp only [mul_zero, add_zero] at hh
  exact hh.congr' (Eventually.of_forall fun X => by simp only [countError, Function.comp_apply, div_eq_mul_inv])

/-- Both actual missing-count and exposed-environment high-count masses
are uniformly small on calibrated support. The same error works before y. -/
theorem eventually_support_count_bounds {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, 0 < w X y →
      Stopped.failureMass (offsetWindow (physicalSpan G M X))
        (actualRootLaw y (physicalSpan G M X)) (M X) ≤ countError G M X ∧
      coreFiniteRootMixUpperRootMass (physicalSpan G M X) y ≤ countError G M X := by
  filter_upwards [eventually_presieve_mean_le_five hG hκ hM hcal,
    eventually_main_mean_ge hG hκ hM hcal, eventually_rank_pos hG hκ hM] with X hmean hmain hm
  intro y hy
  have hmpos : 0 < M X := by omega
  have hlo := lowerFibreMass_le hmean.1 hmpos (hmain y hy)
  constructor
  · exact (finiteRootMixSmall_actual_failureMass_le_lowerFibreMass
      _ y (M X) (hmean.2 y hy).1 hmpos (hmean.2 y hy).2).trans
        (add_le_add le_rfl hlo)
  · have hh := (coreFiniteRootMixUpperRootMass_le _ y (M X) (hmean.2 y hy).1 hmpos).trans
      (add_le_add le_rfl hlo)
    apply hh.trans
    unfold countError
    apply add_le_add _ le_rfl
    rw [← one_div]
    exact div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)

/-- High-count mass retains BOTH original cutoff and exposed presieve,
with the exact conditional threshold 2*card(A)*lateRetention. -/
def highMass (w : ℕ → ℝ) (S : ℕ) : ℝ :=
  ∑' y : ℕ, w y * coreFiniteRootMixUpperRootMass S y

theorem highMass_nonneg (w : ℕ → ℝ) (hw : ∀ y, 0 ≤ w y) (S : ℕ) : 0 ≤ highMass w S :=
  tsum_nonneg fun y => mul_nonneg (hw y) (coreFiniteRootMixUpperRootMass_nonneg S y)

theorem failureMass_eq_finite (w : ℕ → ℝ) (S m : ℕ) {N : ℕ}
    (hzero : ∀ y : ℕ, N ≤ y → w y = 0) :
    Stopped.failureMass (offsetWindow S) (law w S) m =
      ∑ y ∈ range N, w y * Stopped.failureMass (offsetWindow S) (actualRootLaw y S) m := by
  unfold Stopped.failureMass law
  simp_rw [weighted_tsum_eq_sum_of_tail_zero w _ hzero]
  rw [Finset.sum_comm]
  simp only [mul_sum]

theorem eventually_mixture_count_bounds {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop,
      Stopped.failureMass (offsetWindow (physicalSpan G M X))
        (law (w X) (physicalSpan G M X)) (M X) ≤ countError G M X ∧
      highMass (w X) (physicalSpan G M X) ≤ countError G M X := by
  filter_upwards [eventually_support_count_bounds hG hκ hM hcal,
    hcal 1 (by norm_num), hG.eventually_gt_atTop 0] with X hbound hcalX hg
  obtain ⟨N, hzero, hsumN, heval⟩ := exists_real_finite_representation
    (w X) (hw X) (hsum X) hg hcalX
  have havg (f : ℕ → ℝ) (hf : ∀ y, 0 < w X y → f y ≤ countError G M X) :
      (∑ y ∈ range N, w X y * f y) ≤ countError G M X := by
    calc
      _ ≤ ∑ y ∈ range N, w X y * countError G M X := by
        apply sum_le_sum
        intro y hy
        by_cases hwy : w X y = 0
        · simp only [hwy, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left (hf y (lt_of_le_of_ne (hw X y) (Ne.symm hwy))) (hw X y)
      _ = _ := by rw [← Finset.sum_mul, hsumN, one_mul]
  constructor
  · rw [failureMass_eq_finite (w X) _ (M X) hzero]
    exact havg _ (fun y hy => (hbound y hy).1)
  · unfold highMass
    rw [heval]
    exact havg _ (fun y hy => (hbound y hy).2)

/-- Missing original configurations vanish for the actual calibrated
probability mixture, without a concentration or moment premise. -/
theorem tendsto_mixture_failure_zero {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G) :
    Tendsto (fun X => Stopped.failureMass (offsetWindow (physicalSpan G M X))
      (law (w X) (physicalSpan G M X)) (M X)) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun X => ?_)
    ((eventually_mixture_count_bounds hG hκ hM hw hsum hcal).mono fun X hX => hX.1)
    (tendsto_countError_zero hG hκ hM)
  unfold Stopped.failureMass
  exact sum_nonneg fun U _ => law_nonneg (w X) (hw X) _ U

/-- Self-normalized high counts vanish in the same genuine exposed
cutoff/presieve mixture. No independence beyond the actual finite law. -/
theorem tendsto_mixture_high_zero {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G) :
    Tendsto (fun X => highMass (w X) (physicalSpan G M X)) atTop (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall fun X => highMass_nonneg (w X) (hw X) _)
    ((eventually_mixture_count_bounds hG hκ hM hw hsum hcal).mono fun X hX => hX.2)
    (tendsto_countError_zero hG hκ hM)

end
end PrimeGapNormality.Prime.CoreCalibratedMixtureCountException
