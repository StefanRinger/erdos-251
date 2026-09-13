import PrimeGapNormality.Prime.CoreLocalDSubsequence
import PrimeGapNormality.Prime.CoreLocalReferencePassage
import PrimeGapNormality.Prime.CoreLocalModelMixture
import PrimeGapNormality.Prime.CoreCyclicLabels

/-!
# Actual admissible profiles and the local-model subsequence

The action label is selected from the fixed rooted tuple, before the
critical ranks, auxiliary laws, subsequence, tests, or compact cutoffs.
All finite admissibility conditions below are supplied by the actual
profile, including at the nonstrict degree/base threshold.
-/

namespace PrimeGapNormality.Prime.CoreLocalModelSubsequence

open Filter MeasureTheory
open CoreCyclic CoreLocalReferencePassage
open scoped Topology NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Finite facts used by the actual model, not additional asymptotic inputs. -/
structure Admissible (B : ℕ) {k : ℕ} (hk : 0 < k) (phase s : Fin k)
    (w d : ℕ) (κ : ℝ) (X J : ℕ) : Prop where
  one_le : 1 ≤ X
  gap_gt : 1 < windowG X
  small_ge : 16 ≤ ahlSmall_window κ X
  floor_le : ⌊windowG X⌋₊ ≤ ahlSmall_window κ X
  lower : w + 1 ≤ J
  upper : J + w < profileL κ X
  label : phaseAt hk phase (J - 1) = s
  scale_lower : 1 ≤ windowG X ^ d / (B : ℝ) ^ (J + 1)
  scale_upper : windowG X ^ d / (B : ℝ) ^ (J + 1) ≤ (B : ℝ) ^ k
  cutoff : ∀ t ∈ mixScale X, ahlSmall_window κ X ≤ sieveCutoff (t : ℝ)
  retention_pos : ∀ t ∈ mixScale X,
    0 < lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ))
  retention_small : ∀ t ∈ mixScale X,
    lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) ≤ (1 / 4 : ℝ)
  retention_bound : ∀ t ∈ mixScale X,
    lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) *
      windowG X / Real.log (windowG X) ≤ 3 / eulerProdLowerConst
  calibration : ∀ t ∈ mixScale X,
    (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / windowG X ≤ 4
  normalization_pos : 0 < mixZ X

private theorem mixZ_pos {X : ℕ} (hX : 1 ≤ X) : 0 < mixZ X := by
  unfold mixZ
  apply Finset.sum_pos'
  · intro t _
    exact mixWeightV_nonneg t
  · refine ⟨2 * X, ?_, ?_⟩
    · simp only [mixScale, Finset.mem_Ioc]
      omega
    · exact eulerProdNat_pos (sieveCutoff ((2 * X : ℕ) : ℝ))

theorem profile_pos {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    {κ : ℝ} (hκ : (topDegree N : ℝ) / Real.log (B : ℝ) ≤ κ) : 0 < κ := by
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  exact (div_pos (Nat.cast_pos.mpr (topDegree_pos_of_rooted hk N hroot hN)) hlog).trans_le hκ

/-- The exact selected label and every scale condition hold together,
without a strict inequality in the allowed logarithmic profile. -/
theorem eventually_admissible {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (N : PeriodicLocal k) (w : ℕ)
    (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ s i, i ∈ (N s).vars → i ≤ w)
    {κ : ℝ} (hκ : (topDegree N : ℝ) / Real.log (B : ℝ) ≤ κ) :
    ∀ᶠ X : ℕ in atTop, ∃ J,
      Admissible B hk phase (selectedLabel hB hk w N hroot hN hw)
        w (topDegree N) κ X J := by
  have hκ0 := profile_pos hB hk N hroot hN hκ
  filter_upwards [eventually_critical_rank_with_label hB hk
    (one_le_topDegree_of_rooted hk N hroot hN) phase
    (selectedLabel hB hk w N hroot hN hw) w hκ,
    eventually_coreLinearMixtureScales hκ0,
    coreFRMUpper_eventually_lateRetention_le_quarter hκ0,
    eventually_ge_atTop (1 : ℕ)] with X hr hs hret hX
  obtain ⟨J, hJ, hL, hlabel, hlo, hhi⟩ := hr
  refine ⟨J, ⟨hX, hs.1, hs.2.2.1, hs.2.2.2.1,
    hJ, hL, hlabel, hlo, hhi.le, ?_, ?_, hret, ?_, ?_, mixZ_pos hX⟩⟩
  · exact fun t ht => (hs.2.2.2.2 t ht).1
  · intro t ht
    exact rootedEulerProdNat_pos (show 2 ≤ ahlSmall_window κ X by have := hs.2.2.1; omega)
  · exact fun t ht => (hs.2.2.2.2 t ht).2.2.2.1
  · exact fun t ht => (hs.2.2.2.2 t ht).2.2.2.2

/-- Remove one finite prefix of any proposed subsequence. The shift and
all critical ranks are chosen before the auxiliary limit or any test. -/
theorem exists_admissible_shift {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (N : PeriodicLocal k) (w : ℕ)
    (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ s i, i ∈ (N s).vars → i ≤ w)
    {κ : ℝ} (hκ : (topDegree N : ℝ) / Real.log (B : ℝ) ≤ κ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∃ n₀ : ℕ, ∃ j : ℕ → ℕ, ∀ n,
      Admissible B hk phase (selectedLabel hB hk w N hroot hN hw)
        w (topDegree N) κ (φ (n + n₀)) (j n) := by
  have he := hφ.tendsto_atTop.eventually
    (eventually_admissible hB hk phase N w hroot hN hw hκ)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 he
  have hj : ∀ n : ℕ, ∃ J,
      Admissible B hk phase (selectedLabel hB hk w N hroot hN hw)
        w (topDegree N) κ (φ (n + n₀)) J :=
    fun n => hn₀ (n + n₀) (Nat.le_add_left _ _)
  exact ⟨n₀, fun n => Classical.choose (hj n), fun n => Classical.choose_spec (hj n)⟩

/-- The outer phase is chosen in the universal offset slot. In particular
it does not depend on a presieve fibre which has already been averaged out. -/
def profileOuter (B : ℕ) {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (N : PeriodicLocal k) (w : ℕ) (κ : ℝ) (X J : ℕ) :
    Finset ℕ → AddCircle (1 : ℝ) :=
  CoreLocalModelMixture.outerMap B hk phase N (profileL κ X - w) w J
    (ahlSmall_window κ X)

def profileScale (B d X J : ℕ) : ℝ :=
  windowG X ^ d / (B : ℝ) ^ (J + 1)

/-- The genuine completed auxiliary law, with no independence assumption. -/
def profileLaw (B : ℕ) {k : ℕ} (hk : 0 < k) (phase s : Fin k)
    (N : PeriodicLocal k) (w d : ℕ) (κ : ℝ) (X J : ℕ)
    (h : Admissible B hk phase s w d κ X J) :
    ProbabilityMeasure (Joint w) :=
  CoreActualFrameJoint.jointLaw X (ahlSmall_window κ X) (profileL κ X)
    w J (windowG X) (profileScale B d X J)
    (profileOuter B hk phase N w κ X J) h.cutoff h.normalization_pos

/-- Actual joint/reference extraction from the admissible shifted profile.
The reference and its law are fixed before all positive tests and cutoffs. -/
theorem exists_shifted_profile_reference
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (N : PeriodicLocal k) (w : ℕ) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ s i, i ∈ (N s).vars → i ≤ w)
    {κ : ℝ} (hκ : (topDegree N : ℝ) / Real.log (B : ℝ) ≤ κ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    let s := selectedLabel hB hk w N hroot hN hw
    let p := OnePoint.action B hk w s N
    ∃ n₀ : ℕ, ∃ j : ℕ → ℕ,
      ∃ ha : ∀ n, Admissible B hk phase s w (topDegree N) κ (φ (n + n₀)) (j n),
      ∃ ν : ProbabilityMeasure (Joint w), ∃ χ : ℕ → ℕ,
        StrictMono χ ∧
        Tendsto (fun n => profileLaw B hk phase s N w (topDegree N) κ
          (φ (χ n + n₀)) (j (χ n)) (ha (χ n))) atTop (𝓝 ν) ∧
        (∀ᵐ z ∂(ν : Measure (Joint w)), 0 ≤ CoreLocalModelPositive.jointWidth w z) ∧
        Integrable (CoreLocalModelPositive.jointWidth w) (ν : Measure (Joint w)) ∧
        IsFiniteMeasure (reference w (topDegree N) p ν) ∧
        reference w (topDegree N) p ν ≪ volume ∧
        reference w (topDegree N) p ν Set.univ ≤ ENNReal.ofReal 8 := by
  dsimp only
  obtain ⟨n₀, j, ha⟩ := exists_admissible_shift hB hk phase N w hroot hN hw hκ φ hφ
  let X : ℕ → ℕ := fun n => φ (n + n₀)
  have hX : Tendsto X atTop atTop :=
    hφ.tendsto_atTop.comp (tendsto_add_atTop_nat n₀)
  obtain ⟨ν, χ, hχ, hweak, hW0, hWi, hfinite, hac, hmass⟩ :=
    exists_actual_profile_reference hB hk w N hroot hN hw
      (profile_pos hB hk N hroot hN hκ) X hX j
      (fun n => profileScale B (topDegree N) (X n) (j n))
      (fun n => profileOuter B hk phase N w κ (X n) (j n))
      (fun n => (ha n).cutoff) (fun n => (ha n).normalization_pos)
      (fun n => zero_lt_one.trans (ha n).gap_gt)
      (fun n => (ha n).lower) (fun n => (ha n).upper)
      (fun n => (ha n).calibration)
      (fun n => ⟨(ha n).scale_lower, (ha n).scale_upper⟩)
  exact ⟨n₀, j, ha, ν, χ, hχ, hweak, hW0, hWi, hfinite, hac, hmass⟩

def mainConstant : ℝ := 12 * (3 / eulerProdLowerConst)

theorem mainConstant_nonneg : 0 ≤ mainConstant :=
  mul_nonneg (by norm_num) coreLinearScales_retentionConst_pos.le

def tailConstant (w : ℕ) : ℝ := 8 * (2 * w + 1 : ℕ)

theorem tailConstant_nonneg (w : ℕ) : 0 ≤ tailConstant w := by
  unfold tailConstant
  positivity

/-- Insert the actual finite mixture inequality on varying critical ranks.
The error is charged in the original law, before auxiliary reweighting. -/
theorem eventually_profile_compact_bound
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase s : Fin k)
    (N : PeriodicLocal k) (w d : ℕ)
    (hw : ∀ s i, i ∈ (N s).vars → i ≤ w)
    (hd : (OnePoint.action B hk w s N).totalDegree ≤ d)
    (κ : ℝ) (X j : ℕ → ℕ) (hX : Tendsto X atTop atTop)
    (ha : ∀ n, Admissible B hk phase s w d κ (X n) (j n))
    (R : ℝ) (hR : 0 < R) (f : AddCircle (1 : ℝ) →ᵇ ℝ) (K : ℝ≥0)
    (hK : LipschitzWith K f) (hf : ∀ x, 0 ≤ f x) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      coreLocalStoppedMean B (ahlSmall_window κ (X n)) (profileL κ (X n)) w
        hk phase N (finiteRootMix (X n) (ahlSmall_window κ (X n))) f ≤
      mainConstant * (∫ z,
        CoreLocalModelPositive.compactInsertionTest hR.le w d
          (OnePoint.action B hk w s N) hd (windowG (X n))⁻¹ f z
        ∂(profileLaw B hk phase s N w d κ (X n) (j n) (ha n) : Measure (Joint w))) +
      tailConstant w * ‖f‖ / R +
      coreFiniteRootMixUpperException κ (X n) * ‖f‖ + mainConstant * δ := by
  have he := (tendsto_windowG_atTop.comp hX).eventually
    (CoreLocalModelMixture.eventually_finiteRootMean_le_joint_add_errors
      hB hk phase N w d s hw hd hR coreLinearScales_retentionConst_pos.le
      f hK hf hδ)
  filter_upwards [he] with n hn
  have hJn := (ha n).upper
  have hmain := hn (profileL κ (X n) - w) (j n) (X n)
    (ahlSmall_window κ (X n)) (profileL κ (X n))
    (ha n).lower (by omega) (ha n).label (ha n).gap_gt (ha n).floor_le
    (by omega) (ha n).cutoff (ha n).normalization_pos (ha n).retention_pos
    (ha n).retention_small (ha n).scale_lower (ha n).scale_upper
    (ha n).retention_bound
  have herr := CoreLocalModelMixture.nonMainTerm_frameRanks_le
    κ (X n) (profileL κ (X n)) w (j n) (ha n).normalization_pos
    (ha n).lower (ha n).upper (zero_lt_one.trans (ha n).gap_gt)
    hR (norm_nonneg f) (ha n).calibration
  rw [coreLocalStoppedMean_eq_fullConfiguration B (X n)
    (ahlSmall_window κ (X n)) hk phase N (by omega : w ≤ profileL κ (X n)) hw f]
  let I : ℝ := ∫ z,
    CoreLocalModelPositive.compactInsertionTest hR.le w d
      (OnePoint.action B hk w s N) hd (windowG (X n))⁻¹ f z
      ∂(profileLaw B hk phase s N w d κ (X n) (j n) (ha n) : Measure (Joint w))
  change corePositiveFiniteRootMean (X n) (ahlSmall_window κ (X n))
    (profileL κ (X n))
    (CoreLocalModelPositive.actualTest B hk phase N (profileL κ (X n) - w) f) ≤
    mainConstant * I + tailConstant w * ‖f‖ / R +
      coreFiniteRootMixUpperException κ (X n) * ‖f‖ + mainConstant * δ
  change corePositiveFiniteRootMean (X n) (ahlSmall_window κ (X n))
    (profileL κ (X n))
    (CoreLocalModelPositive.actualTest B hk phase N (profileL κ (X n) - w) f) ≤
    mainConstant * (I + δ) +
      CoreLocalModelMixture.nonMainTerm (X n) (ahlSmall_window κ (X n))
        (profileL κ (X n)) (OnePoint.FiniteExterior.frameRanks w (j n))
        (j n - 1) (windowG (X n)) R ‖f‖ at hmain
  have htotal := hmain.trans (_root_.add_le_add le_rfl herr)
  calc
    _ ≤ mainConstant * (I + δ) +
        (‖f‖ * coreFiniteRootMixUpperException κ (X n) + tailConstant w * ‖f‖ / R) := htotal
    _ = _ := by ring

/-- The actual local model supplies the reference-subsequence contract
from the rooted nonzero tuple and the allowed profile alone. In particular
there is no rectangle, mean, or reference hypothesis in this endpoint. -/
theorem coreLocalModelSubsequenceBounds_of_rooted
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (N : PeriodicLocal k) (w : ℕ) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ s i, i ∈ (N s).vars → i ≤ w)
    {κ : ℝ} (hκ : (topDegree N : ℝ) / Real.log (B : ℝ) ≤ κ) :
    CoreLocalModelSubsequenceBounds B κ hk phase N w := by
  intro φ hφ
  let s := selectedLabel hB hk w N hroot hN hw
  let p := OnePoint.action B hk w s N
  have hd : p.totalDegree ≤ topDegree N := action_totalDegree_le_topDegree B hk w s N
  obtain ⟨n₀, j, ha, ν, χ, hχ, hweak, hW0, hWi, hfinite, hac, _hmass⟩ :=
    exists_shifted_profile_reference hB hk phase N w hroot hN hw hκ φ hφ
  let Y : ℕ → ℕ := fun n => φ (χ n + n₀)
  have hY : Tendsto Y atTop atTop :=
    hφ.tendsto_atTop.comp ((tendsto_add_atTop_nat n₀).comp hχ.tendsto_atTop)
  let μ : ℕ → ProbabilityMeasure (Joint w) := fun n =>
    profileLaw B hk phase s N w (topDegree N) κ (Y n) (j (χ n)) (ha (χ n))
  let mean : ℕ → (AddCircle (1 : ℝ) →ᵇ ℝ) → ℝ := fun n f =>
    coreLocalStoppedMean B (ahlSmall_window κ (Y n)) (profileL κ (Y n)) w hk phase N
      (finiteRootMix (Y n) (ahlSmall_window κ (Y n))) f
  have hη : Tendsto (fun n => coreFiniteRootMixUpperException κ (Y n)) atTop (𝓝 0) :=
    (tendsto_coreFiniteRootMixUpperException (profile_pos hB hk N hroot hN hκ)).comp hY
  have hbound := reference_domination_of_finite_compact_bounds
    w (topDegree N) p hd (fun n => windowG (Y n)) (tendsto_windowG_atTop.comp hY)
    μ ν hweak hW0 hWi mean mainConstant_nonneg (tailConstant_nonneg w)
    (fun n => coreFiniteRootMixUpperException κ (Y n)) hη (by
      intro R hR f K hK hf δ hδ
      exact eventually_profile_compact_bound hB hk phase s N w (topDegree N) hw hd κ
        Y (fun n => j (χ n)) hY (fun n => ha (χ n)) R hR f K hK hf δ hδ)
  refine ⟨fun n => χ n + n₀, ?_, reference w (topDegree N) p ν,
    hfinite, hac, mainConstant, mainConstant_nonneg, ?_⟩
  · intro m n hmn
    exact Nat.add_lt_add_right (hχ hmn) n₀
  · exact hbound

end
end PrimeGapNormality.Prime.CoreLocalModelSubsequence
