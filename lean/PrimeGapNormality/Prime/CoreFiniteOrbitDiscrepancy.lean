import PrimeGapNormality.Prime.CoreCircleIntervalRamps
import PrimeGapNormality.Prime.CoreFiniteOrbitBoundary

/-!
# Finite positive domination implies orbit discrepancy

This is the finite analytic assembly of the quantitative orbit lemma.  The
only external hypothesis is the displayed positive domination inequality;
the interval ramps, covariance, Haar variance, and endpoint loss are all
theorems in the imported core files.
-/

namespace PrimeGapNormality.Prime.CoreFiniteOrbitDiscrepancy

open Finset MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

noncomputable section

open CoreBVOrbitMixing CoreCircleIntervalRamps CoreOrbitCovarianceVariance
  CoreFiniteOrbitBoundary

abbrev Circle := CoreBVOrbitMixing.Circle

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local instance : IsProbabilityMeasure (volume : Measure Circle) :=
  ⟨by simp⟩

/-- Empirical mean on a finite block of the actual `B`-orbit. -/
def orbitBlockMean (B : ℕ) (β : Circle) (f : Circle → ℝ) (a m : ℕ) : ℝ :=
  blockMean (fun n ↦ f (B ^ n • β)) a m

/-- The literal finite positive-comparison input. -/
def FinitePositiveDomination
    (B : ℕ) (β : Circle) (a m : ℕ) (A ε η : ℝ) : Prop :=
  ∀ (f : Circle →ᵇ ℝ) (K : ℝ≥0), (∀ x, 0 ≤ f x) → LipschitzWith K f →
    orbitBlockMean B β f a m ≤
      A * (∫ x : Circle, f x) + ε * ‖f‖ + η * (K : ℝ)

/-- Absolute centered time average as a bounded continuous circle test. -/
def orbitTimeFluctuation (B T : ℕ) (φ : Circle →ᵇ ℝ) : Circle →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ |finiteTimeMean
        (fun h x ↦ centeredCircleTest φ (B ^ h • x)) T x|, by
      unfold finiteTimeMean centeredCircleTest circleMean
      fun_prop⟩

theorem orbitTimeFluctuation_nonneg
    (B T : ℕ) (φ : Circle →ᵇ ℝ) (x : Circle) :
    0 ≤ orbitTimeFluctuation B T φ x := by
  simpa only [orbitTimeFluctuation,
    BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] using
      abs_nonneg
        (finiteTimeMean (fun h x => centeredCircleTest φ (B ^ h • x)) T x)

private theorem abs_finiteTimeMean_le_one
    (φ : Circle →ᵇ ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {B T : ℕ} (hT : 0 < T) (x : Circle) :
    |finiteTimeMean (fun h x ↦ centeredCircleTest φ (B ^ h • x)) T x| ≤ 1 := by
  have hsum : |∑ h ∈ range T, centeredCircleTest φ (B ^ h • x)| ≤ (T : ℝ) := by
    calc
      |∑ h ∈ range T, centeredCircleTest φ (B ^ h • x)| ≤
          ∑ h ∈ range T, |centeredCircleTest φ (B ^ h • x)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ range T, (1 : ℝ) := by
        apply sum_le_sum
        intro h hh
        exact centeredCircleTest_abs_le_one φ hφ0 hφ1 _
      _ = (T : ℝ) := by rw [sum_const, card_range, nsmul_eq_mul, mul_one]
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  unfold finiteTimeMean
  rw [abs_div, abs_of_pos hTR]
  exact (div_le_one hTR).2 hsum

theorem orbitTimeFluctuation_norm_le_one
    (φ : Circle →ᵇ ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {B T : ℕ} (hT : 0 < T) :
    ‖orbitTimeFluctuation B T φ‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)]
  intro x
  simpa only [orbitTimeFluctuation,
    BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
    Real.norm_eq_abs, abs_abs] using abs_finiteTimeMean_le_one (B := B) φ hφ0 hφ1 hT x

private theorem circleClock_pow_dist_le
    {B h T : ℕ} (hB : 1 ≤ B) (hh : h ≤ T) (x y : Circle) :
    dist (B ^ h • x) (B ^ h • y) ≤ (B ^ T : ℕ) * dist x y := by
  rw [dist_eq_norm, ← nsmul_sub]
  calc
    ‖B ^ h • (x - y)‖ ≤ (B ^ h : ℕ) * ‖x - y‖ := norm_nsmul_le
    _ ≤ (B ^ T : ℕ) * ‖x - y‖ := by
      gcongr
    _ = (B ^ T : ℕ) * dist x y := by rw [dist_eq_norm]

/-- The finite fluctuation has Lipschitz constant at most `K*B^T`. -/
theorem orbitTimeFluctuation_lipschitz
    {B T : ℕ} (hB : 1 ≤ B) (hT : 0 < T)
    (φ : Circle →ᵇ ℝ) {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    LipschitzWith (K * (B ^ T : ℕ)) (orbitTimeFluctuation B T φ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hsum :
      |(∑ h ∈ range T, centeredCircleTest φ (B ^ h • x)) -
        ∑ h ∈ range T, centeredCircleTest φ (B ^ h • y)| ≤
        (T : ℝ) * ((K : ℝ) * (B ^ T : ℕ) * dist x y) := by
    rw [← sum_sub_distrib]
    calc
      |∑ h ∈ range T,
          (centeredCircleTest φ (B ^ h • x) -
            centeredCircleTest φ (B ^ h • y))| ≤
          ∑ h ∈ range T,
            |centeredCircleTest φ (B ^ h • x) -
              centeredCircleTest φ (B ^ h • y)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ range T, ((K : ℝ) * (B ^ T : ℕ) * dist x y) := by
        apply sum_le_sum
        intro h hh
        rw [centeredCircleTest_apply, centeredCircleTest_apply,
          sub_sub_sub_cancel_right, ← Real.dist_eq]
        simpa only [mul_assoc] using
          (hφ.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
            (circleClock_pow_dist_le hB (mem_range.mp hh).le x y) (NNReal.coe_nonneg K))
      _ = (T : ℝ) * ((K : ℝ) * (B ^ T : ℕ) * dist x y) := by
        rw [sum_const, card_range, nsmul_eq_mul]
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  change dist
      |finiteTimeMean (fun h x ↦ centeredCircleTest φ (B ^ h • x)) T x|
      |finiteTimeMean (fun h x ↦ centeredCircleTest φ (B ^ h • x)) T y| ≤ _
  rw [Real.dist_eq]
  refine (abs_abs_sub_abs_le _ _).trans ?_
  unfold finiteTimeMean
  rw [← sub_div, abs_div, abs_of_pos hTR]
  apply (div_le_iff₀ hTR).2
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Actual Haar first moment of the fluctuation for a variation-two test. -/
theorem orbitTimeFluctuation_integral_le
    (φ : Circle →ᵇ ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hBV : BoundedVariationOn (circleLift φ) (Icc (0 : ℝ) 1))
    (hvar : circleVariation φ ≤ 2)
    {B T : ℕ} (hB : 2 ≤ B) (hT : 0 < T) :
    (∫ x : Circle, orbitTimeFluctuation B T φ x) ≤
      Real.sqrt (6 / (T : ℝ)) := by
  have hh := integral_abs_circleClock_timeMean_le φ hφ0 hφ1
    (by norm_num : (0 : ℝ) < 2)
    (centeredCircleTest_boundedVariation φ hBV)
    (by simpa only [centeredCircleTest_variation_eq] using hvar) hB hT
  have hfun : (fun x : Circle => orbitTimeFluctuation B T φ x) =
      fun x : Circle =>
        |finiteTimeMean (fun h x => centeredCircleTest φ (B ^ h • x)) T x| := by
    funext x
    rfl
  rw [hfun]
  simpa only [show (3 : ℝ) * 2 = 6 by norm_num] using hh

private theorem sequence_timeFluctuation_eq_orbit
    (B T n : ℕ) (β : Circle) (φ : Circle →ᵇ ℝ) (hT : 0 < T) :
    timeFluctuation (fun m ↦ φ (B ^ m • β)) (circleMean φ) T n =
      orbitTimeFluctuation B T φ (B ^ n • β) := by
  change |(∑ h ∈ range T, φ (B ^ (n + h) • β)) / (T : ℝ) - circleMean φ| =
    |(∑ h ∈ range T, centeredCircleTest φ (B ^ h • (B ^ n • β))) / (T : ℝ)|
  congr 1
  have hterms : (∑ h ∈ range T, centeredCircleTest φ (B ^ h • (B ^ n • β))) =
      ∑ h ∈ range T, (φ (B ^ (n + h) • β) - circleMean φ) := by
    apply sum_congr rfl
    intro h hh
    rw [centeredCircleTest_apply, smul_smul, ← pow_add, Nat.add_comm h n]
  rw [hterms, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sub_div,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hT.ne')]

/-- One bounded variation test under the literal positive domination
input, including the exact finite block-boundary cost. -/
theorem abs_orbitBlockMean_sub_integral_le
    {B a m T : ℕ} (hB : 2 ≤ B) (hm : 0 < m) (hT : 0 < T)
    {β : Circle} {A ε η : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hdom : FinitePositiveDomination B β a m A ε η)
    (φ : Circle →ᵇ ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {K : ℝ≥0} (hLip : LipschitzWith K φ)
    (hBV : BoundedVariationOn (circleLift φ) (Icc (0 : ℝ) 1))
    (hvar : circleVariation φ ≤ 2) :
    |orbitBlockMean B β φ a m - ∫ x : Circle, φ x| ≤
      A * Real.sqrt (6 / (T : ℝ)) + ε +
        η * ((K : ℝ) * (B ^ T : ℕ)) + 2 * (T : ℝ) / (m : ℝ) := by
  let F := orbitTimeFluctuation B T φ
  have hboundary := abs_blockMean_sub_le_timeFluctuation
    (f := fun n ↦ φ (B ^ n • β))
    (C := (1 : ℝ)) (by norm_num)
    (fun n ↦ by
      rw [abs_of_nonneg (hφ0 (B ^ n • β))]
      exact hφ1 (B ^ n • β))
    a hT hm (circleMean φ)
  have hidentify : blockMean
      (timeFluctuation (fun n ↦ φ (B ^ n • β)) (circleMean φ) T) a m =
      orbitBlockMean B β F a m := by
    unfold orbitBlockMean blockMean
    apply congrArg (fun z : ℝ ↦ z / (m : ℝ))
    apply sum_congr rfl
    intro n hn
    exact sequence_timeFluctuation_eq_orbit B T (a + n) β φ hT
  rw [hidentify] at hboundary
  have hFdom := hdom F (K * (B ^ T : ℕ))
    (orbitTimeFluctuation_nonneg B T φ)
    (orbitTimeFluctuation_lipschitz (by omega) hT φ hLip)
  have hFint := orbitTimeFluctuation_integral_le φ hφ0 hφ1 hBV hvar hB hT
  have hFnorm := orbitTimeFluctuation_norm_le_one (B := B) φ hφ0 hφ1 hT
  have hdomBound : orbitBlockMean B β F a m ≤
      A * Real.sqrt (6 / (T : ℝ)) + ε +
        η * ((K : ℝ) * (B ^ T : ℕ)) := by
    have hAI := mul_le_mul_of_nonneg_left hFint hA
    have hεN := mul_le_mul_of_nonneg_left hFnorm hε
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, mul_one] using
      hFdom.trans (_root_.add_le_add (_root_.add_le_add hAI hεN) le_rfl)
  have hfinal := hboundary.trans (_root_.add_le_add hdomBound le_rfl)
  simpa only [orbitBlockMean, circleMean, one_mul, mul_one, add_assoc] using hfinal

/-- Empirical mass of the anchored half-open circle interval. -/
def orbitIntervalMass (B : ℕ) (β : Circle) (a m : ℕ) (t : ℝ) : ℝ :=
  orbitBlockMean B β
    ((anchoredCircleInterval t).indicator (fun _ ↦ (1 : ℝ))) a m

private theorem orbitBlockMean_mono
    {B a m : ℕ} (hm : 0 < m) {β : Circle} {f g : Circle → ℝ}
    (hfg : ∀ x, f x ≤ g x) :
    orbitBlockMean B β f a m ≤ orbitBlockMean B β g a m := by
  unfold orbitBlockMean blockMean
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  apply div_le_div_of_nonneg_right _ hmR
  apply sum_le_sum
  intro n hn
  exact hfg _

/-- Finite star-discrepancy bound from the literal positive domination
input.  All constants are explicit; the harmless ramp constants are `2`
for variation, Lipschitz, and Haar approximation. -/
theorem abs_orbitIntervalMass_sub_le
    {B a m T : ℕ} (hB : 2 ≤ B) (hm : 0 < m) (hT : 0 < T)
    {β : Circle} {A ε η : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hdom : FinitePositiveDomination B β a m A ε η)
    {t δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hδ : 0 < δ) :
    |orbitIntervalMass B β a m t - t| ≤
      A * Real.sqrt (6 / (T : ℝ)) + ε +
        η * ((2 / δ) * (B ^ T : ℕ)) +
          2 * (T : ℝ) / (m : ℝ) + 2 * δ := by
  let Kδ : ℝ≥0 :=
    ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ + ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
  let upper := upperCircleRamp t δ hδ ht0
  let lower := lowerCircleRamp t δ hδ ht1
  have hu := abs_orbitBlockMean_sub_integral_le hB hm hT hA hε hη hdom
    upper (upperCircleRamp_nonneg t δ hδ ht0)
    (upperCircleRamp_le_one t δ hδ ht0) (K := Kδ)
    (by simpa only [upper, Kδ] using upperCircleRamp_lipschitz t δ hδ ht0)
    (by simpa only [upper] using upperCircleRamp_boundedVariation hδ ht0)
    (by simpa only [upper] using upperCircleRamp_variation_le_two hδ ht0)
  have hl := abs_orbitBlockMean_sub_integral_le hB hm hT hA hε hη hdom
    lower (lowerCircleRamp_nonneg t δ hδ ht1)
    (lowerCircleRamp_le_one t δ hδ ht1) (K := Kδ)
    (by simpa only [lower, Kδ] using lowerCircleRamp_lipschitz t δ hδ ht1)
    (by simpa only [lower] using lowerCircleRamp_boundedVariation hδ ht1)
    (by simpa only [lower] using lowerCircleRamp_variation_le_two hδ ht1)
  have hint := circleRamp_integral_bounds hδ ht0 ht1
  have hsand : ∀ x,
      lower x ≤ (anchoredCircleInterval t).indicator (fun _ ↦ (1 : ℝ)) x ∧
        (anchoredCircleInterval t).indicator (fun _ ↦ (1 : ℝ)) x ≤ upper x := by
    intro x
    simpa only [lower, upper] using circleRamp_sandwich hδ ht0 ht1 x
  have hlowMass : orbitBlockMean B β lower a m ≤ orbitIntervalMass B β a m t := by
    unfold orbitIntervalMass
    exact orbitBlockMean_mono hm fun x ↦ (hsand x).1
  have huppMass : orbitIntervalMass B β a m t ≤ orbitBlockMean B β upper a m := by
    unfold orbitIntervalMass
    exact orbitBlockMean_mono hm fun x ↦ (hsand x).2
  let E : ℝ := A * Real.sqrt (6 / (T : ℝ)) + ε +
    η * ((2 / δ) * (B ^ T : ℕ)) + 2 * (T : ℝ) / (m : ℝ)
  have hKcoe : (Kδ : ℝ) = 2 / δ := by
    change δ⁻¹ + δ⁻¹ = 2 / δ
    rw [div_eq_mul_inv]
    ring
  rw [hKcoe] at hu hl
  have huE : |orbitBlockMean B β upper a m - ∫ x : Circle, upper x| ≤ E := by
    simpa only [upper, E, mul_assoc] using hu
  have hlE : |orbitBlockMean B β lower a m - ∫ x : Circle, lower x| ≤ E := by
    simpa only [lower, E, mul_assoc] using hl
  rw [abs_le] at huE hlE ⊢
  dsimp only [E] at huE hlE
  constructor
  · have hmeanLow : t - 2 * δ ≤ ∫ x : Circle, lower x := by
      simpa only [lower] using hint.1
    linarith [hlE.1]
  · have hmeanUpp : (∫ x : Circle, upper x) ≤ t + 2 * δ := by
      simpa only [upper] using hint.2.2.2
    linarith [huE.2]

end

end PrimeGapNormality.Prime.CoreFiniteOrbitDiscrepancy
