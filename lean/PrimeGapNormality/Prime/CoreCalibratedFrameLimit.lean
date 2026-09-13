import PrimeGapNormality.Prime.CoreCalibratedAuxiliaryFrame

/-!
# Actual calibrated auxiliary rectangle bounds

Every coordinate rank is arbitrary and distinct; contiguous frames are
not required. Actual finite Selberg caps are averaged over the retained
original-count layers and cutoff weights. The completed missing atom and
the actual high-count exception are paid additively. The resulting
constant (192/c_Euler)^r is sufficient for AC, but is deliberately NOT
claimed to be the sharper displayed paper constant 8^r.

This module supplies the actual rectangle asymptotic on the completed
finite masses. Probability pushforward/Prokhorov packaging is a subsequent
step; no unproved frame-AC or model-reference conclusion is asserted here.
-/

namespace PrimeGapNormality.Prime.CoreCalibratedFrameLimit

open Finset Filter CoreCalibratedAuxiliaryFrame CoreCalibratedMixtureProfile
  CoreCalibratedMixtureFiniteSupport CoreCalibratedMixtureCountException
  CoreActualFrameRectangles CoreActualFrameRectangleLimit
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def rankSet {r : ℕ} (q : Fin r → ℕ) : Finset ℕ := univ.image q
def endpoints {r : ℕ} (q : Fin r → ℕ) (a : Fin r → ℝ) : ℕ → ℝ :=
  Function.extend q a (fun _ => 0)

theorem endpoints_apply {r : ℕ} {q : Fin r → ℕ} (hq : Function.Injective q)
    (a : Fin r → ℝ) (i : Fin r) : endpoints q a (q i) = a i := hq.extend_apply a (fun _ => 0) i

def rectangleTest {r : ℕ} (q : Fin r → ℕ) (G : ℝ) (a b : Fin r → ℝ) (F : Finset ℕ) : ℝ :=
  if ∀ i, frame q G F i ∈ Set.Ioo (a i) (b i) then 1 else 0

theorem rectangleTest_nonneg {r : ℕ} (q : Fin r → ℕ) (G : ℝ) (a b : Fin r → ℝ) (F : Finset ℕ) :
    0 ≤ rectangleTest q G a b F := by unfold rectangleTest; split_ifs <;> norm_num

theorem rectangleTest_le_one {r : ℕ} (q : Fin r → ℕ) (G : ℝ) (a b : Fin r → ℝ) (F : Finset ℕ) :
    rectangleTest q G a b F ≤ 1 := by unfold rectangleTest; split_ifs <;> norm_num

theorem rectangleIndicator_eq {r : ℕ} (q : Fin r → ℕ) (hq : Function.Injective q)
    (G : ℝ) (a b : Fin r → ℝ) :
    rectangleIndicator (rankSet q) G (endpoints q a) (endpoints q b) = rectangleTest q G a b := by
  funext F
  unfold rectangleIndicator rectangleTest
  congr 1
  apply propext
  constructor
  · intro h i
    have hi : q i ∈ rankSet q :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simpa only [endpoints_apply hq, frame] using h (q i) hi
  · intro h n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    simpa only [endpoints_apply hq, frame] using h i

/-- Exact finite arbitrary-rank version of the actual presieve rectangle
bound. The candidate caps on the right come from Selberg, not a grid law. -/
theorem presieve_good_rectangle_le {r : ℕ} (q : Fin r → ℕ) (hq : Function.Injective q)
    (S y M n : ℕ) (σ : ResidueChoice S) (a b : Fin r → ℝ) (R : Fin r → ℕ)
    {G : ℝ} (hG : 0 < G) (hM : 1 ≤ M) (hMn : M ≤ n)
    (hn : n ≤ (presieveSurvivors S σ).card) (hvalid : ∀ i, q i + 1 < M)
    (hcount : (n : ℝ) ≤ 2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y)
    (hθ : 0 < lateRetention S y) (hθ4 : lateRetention S y ≤ (1 : ℝ) / 4)
    (hR : ∀ i, 1 ≤ R i ∧ R i ≤ intervalLength (G * (b i - a i)) ∧ R i ≤ S) :
    auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) (rectangleTest q G a b) ≤
      (4 * lateRetention S y) ^ r * ∏ i : Fin r, (candidateCap G (a i) (b i) (R i) : ℝ) := by
  let radii := Function.extend q R (fun _ => 1)
  have hRi (i : Fin r) : radii (q i) = R i := hq.extend_apply R (fun _ => 1) i
  have hJ : ∀ j ∈ rankSet q, j + 1 < M := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact hvalid i
  have hRad : ∀ j ∈ rankSet q, 1 ≤ radii j ∧
      radii j ≤ intervalLength (G * (endpoints q b j - endpoints q a j)) ∧ radii j ≤ S := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    simpa only [hRi, endpoints_apply hq] using hR i
  have hh := presieve_good_layer_rectangle_le S y M n σ (rankSet q)
    (endpoints q a) (endpoints q b) radii hG hM hMn hn hJ hcount hθ hθ4 hRad
  rw [rectangleIndicator_eq q hq] at hh
  have hcard : (rankSet q).card = r := by
    rw [rankSet, Finset.card_image_of_injective _ hq, Finset.card_univ,
      Fintype.card_fin]
  have hprod : (∏ j ∈ rankSet q, (candidateCap G (endpoints q a j) (endpoints q b j) (radii j) : ℝ)) =
      ∏ i : Fin r, (candidateCap G (a i) (b i) (R i) : ℝ) := by
    rw [rankSet, prod_image]
    · simp only [endpoints_apply hq, hRi]
    · exact fun i _ j _ hij => hq hij
  rwa [hcard, hprod] at hh

theorem eventually_profile_log_ratio {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ)) :
    ∀ᶠ X : ℕ in atTop,
      1 < G X ∧ 16 ≤ physicalSpan G M X ∧ ⌊G X⌋₊ ≤ physicalSpan G M X ∧
      Real.log (physicalSpan G M X : ℝ) ≤ 3 * Real.log (G X) := by
  let c := 2 * (κ + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [eventually_physicalSpan_le_quadratic hG hκ hM,
    (tendsto_physicalSpan_atTop hG hκ hM).eventually_ge_atTop 16,
    eventually_rank_pos hG hκ hM, hG.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp hG).eventually_ge_atTop (Real.log c)] with X hSbound hS hm hg hlog
  simp only [Function.comp_apply] at hlog
  have hgp : 0 < G X := zero_lt_one.trans hg
  have hfloor : ⌊G X⌋₊ ≤ physicalSpan G M X := by
    apply Nat.floor_mono
    have hmr : (1 : ℝ) ≤ M X := by exact_mod_cast hm
    have hcoef : (1 : ℝ) ≤ (6 / 5 : ℝ) * (M X : ℝ) := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hgp.le
  have hSp : (0 : ℝ) < physicalSpan G M X := Nat.cast_pos.mpr (by omega)
  have hl := Real.log_le_log hSp hSbound
  have heq : Real.log (c * G X ^ 2) = Real.log c + 2 * Real.log (G X) := by
    rw [Real.log_mul hc.ne' (pow_ne_zero _ hgp.ne'), Real.log_pow]
    norm_num
  rw [heq] at hl
  exact ⟨hg, hS, hfloor, by linarith⟩

theorem eventually_scaled_retention {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop, 1 < G X ∧ 16 ≤ physicalSpan G M X ∧ ⌊G X⌋₊ ≤ physicalSpan G M X ∧
      ∀ y, 0 < w X y → physicalSpan G M X ≤ y ∧
        0 < lateRetention (physicalSpan G M X) y ∧ lateRetention (physicalSpan G M X) y ≤ (1 : ℝ) / 4 ∧
        lateRetention (physicalSpan G M X) y * G X / Real.log (G X) ≤ 6 / eulerProdLowerConst := by
  filter_upwards [eventually_profile_log_ratio hG hκ hM,
    eventually_support_retention_le hG hκ hM hcal,
    (tendsto_singletonCap_zero hG hκ hM).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)]
    with X hscale hret hsmall
  refine ⟨hscale.1, hscale.2.1, hscale.2.2.1, ?_⟩
  intro y hy
  refine ⟨(hret.2 y hy).1.le, rootedEulerProdNat_pos (by have hh := hscale.2.1; omega),
    (hret.2 y hy).2.trans hsmall, ?_⟩
  have hg : 0 < G X := zero_lt_one.trans hscale.1
  have hl : 0 < Real.log (G X) := Real.log_pos hscale.1
  have h1 := mul_le_mul_of_nonneg_right (hret.2 y hy).2 (div_nonneg hg.le hl.le)
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscale.2.2.2
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) eulerProdLowerConst_pos.le)) hl.le
  have heq : singletonCap G M X * (G X / Real.log (G X)) =
      ((2 / eulerProdLowerConst) * Real.log (physicalSpan G M X : ℝ)) / Real.log (G X) := by
    unfold singletonCap
    field_simp [hg.ne', hl.ne']
  rw [heq] at h1
  have h3 := h1.trans h2
  have heqleft : lateRetention (physicalSpan G M X) y * (G X / Real.log (G X)) =
      lateRetention (physicalSpan G M X) y * G X / Real.log (G X) := by ring
  have heqright : ((2 / eulerProdLowerConst) * (3 * Real.log (G X))) / Real.log (G X) =
      6 / eulerProdLowerConst := by
    field_simp [hl.ne', eulerProdLowerConst_pos.ne']
    ring
  rw [heqleft, heqright] at h3
  exact h3

def rectangleConstant (r : ℕ) : ℝ := ((192 : ℝ) / eulerProdLowerConst) ^ r

theorem rectangleConstant_pos (r : ℕ) : 0 < rectangleConstant r :=
  pow_pos (div_pos (by norm_num) eulerProdLowerConst_pos) _

/-- Actual support-uniform finite layer bound for every injective rank
map, with the threshold chosen only from the fixed rectangle. -/
theorem eventually_layer_rectangle {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hcal : UniformCalibration w G)
    (r : ℕ) (a b : Fin r → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᶠ X : ℕ in atTop, ∀ y, 0 < w X y → ∀ q : Fin r → ℕ,
      Function.Injective q → (∀ i, q i + 1 < M X) →
      (∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
        coreAuxiliaryLayerFrameMass (physicalSpan G M X) y (M X) F * rectangleTest q (G X) a b F) ≤
        rectangleConstant r * ∏ i, (b i - a i) + coreFiniteRootMixUpperRootMass (physicalSpan G M X) y := by
  have hcaps : ∀ᶠ x : ℝ in atTop, ∀ i : Fin r,
      1 < x ∧ 1 ≤ rectangleRadius (b i - a i) x ∧
      rectangleRadius (b i - a i) x ≤ intervalLength (x * (b i - a i)) ∧
      rectangleRadius (b i - a i) x ≤ ⌊x⌋₊ ∧
      (candidateCap x (a i) (b i) (rectangleRadius (b i - a i) x) : ℝ) ≤
        8 * x / Real.log x * (b i - a i) := Filter.eventually_all.2 fun i => eventually_candidateCap_le (hab i)
  filter_upwards [hG.eventually hcaps, eventually_scaled_retention hG hκ hM hcal,
    eventually_rank_pos hG hκ hM] with X hcap hscale hMX
  intro y hy q hq hvalid
  have hs := hscale.2.2.2 y hy
  let S := physicalSpan G M X
  let θ := lateRetention S y
  have hθpos : 0 < θ := hs.2.1
  apply layer_le_good_add_high S y (M X) hs.1 (rectangleTest q (G X) a b)
    (rectangleTest_le_one q (G X) a b)
    (mul_nonneg (rectangleConstant_pos r).le (prod_nonneg fun i _ => (sub_pos.mpr (hab i)).le))
  intro σ n hn hcount
  have hf := presieve_good_rectangle_le q hq S y (M X) n σ a b
    (fun i => rectangleRadius (b i - a i) (G X)) (zero_lt_one.trans hscale.1) hMX
    (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 hvalid hcount hs.2.1 hs.2.2.1
    (fun i => ⟨(hcap i).2.1, (hcap i).2.2.1, (hcap i).2.2.2.1.trans hscale.2.2.1⟩)
  have hcoord (i : Fin r) : (4 * θ) *
      (candidateCap (G X) (a i) (b i) (rectangleRadius (b i - a i) (G X)) : ℝ) ≤
      ((192 : ℝ) / eulerProdLowerConst) * (b i - a i) := by
    calc
      _ ≤ (4 * θ) * (8 * G X / Real.log (G X) * (b i - a i)) :=
        mul_le_mul_of_nonneg_left (hcap i).2.2.2.2
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hθpos.le)
      _ = (32 * (θ * G X / Real.log (G X))) * (b i - a i) := by ring
      _ ≤ (32 * (6 / eulerProdLowerConst)) * (b i - a i) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs.2.2.2 (by norm_num)) (sub_pos.mpr (hab i)).le
      _ = _ := by ring
  have hp := Finset.prod_le_prod (s := (univ : Finset (Fin r)))
    (fun i _ => mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hθpos.le)
      (Nat.cast_nonneg (candidateCap (G X) (a i) (b i)
        (rectangleRadius (b i - a i) (G X))) : (0 : ℝ) ≤ _))
    (fun i _ => hcoord i)
  have hp' : (4 * θ) ^ r *
      (∏ i : Fin r, (candidateCap (G X) (a i) (b i) (rectangleRadius (b i - a i) (G X)) : ℝ)) ≤
      rectangleConstant r * ∏ i, (b i - a i) := by
    rw [mul_pow]
    simpa only [prod_mul_distrib, prod_const, Finset.card_univ,
      Fintype.card_fin, rectangleConstant] using hp
  exact hf.trans hp'

def rectangleError (G : ℕ → ℝ) (M : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (X : ℕ) : ℝ :=
  highMass (w X) (physicalSpan G M X) + missing (w X) (physicalSpan G M X) (M X)

theorem tendsto_rectangleError_zero {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G) :
    Tendsto (rectangleError G M w) atTop (𝓝 0) := by
  change Tendsto (fun X => highMass (w X) (physicalSpan G M X) +
    missing (w X) (physicalSpan G M X) (M X)) atTop (𝓝 0)
  simpa only [add_zero] using
    (tendsto_mixture_high_zero hG hκ hM hw hsum hcal).add
    (tendsto_missing_zero hG hκ hM hw hsum hcal)

/-- The actual completed auxiliary-frame rectangle supplier: arbitrary
distinct valid ranks, common fixed-dimensional constant, actual vanishing
high/missing error. No rectangle law is assumed. -/
theorem eventually_completed_rectangle_bound {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1) (hcal : UniformCalibration w G)
    (r : ℕ) (a b : Fin r → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᶠ X : ℕ in atTop, ∀ q : Fin r → ℕ, Function.Injective q → (∀ i, q i + 1 < M X) →
      (∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
        completed (w X) (physicalSpan G M X) (M X) F * rectangleTest q (G X) a b F) ≤
        rectangleConstant r * ∏ i, (b i - a i) + rectangleError G M w X := by
  filter_upwards [eventually_layer_rectangle hG hκ hM hcal r a b hab,
    eventually_profile_data hG hκ hM hw hsum hcal] with X hlayer hdata
  obtain ⟨N, hzero, hsumN⟩ := hdata.2.2.2
  intro q hq hvalid
  rw [completed_expectation, expectation_eq_finite (w X) _ _ hzero]
  have hmain : (∑ y ∈ range N, w X y *
      (∑ F ∈ (offsetWindow (physicalSpan G M X)).powerset,
        coreAuxiliaryLayerFrameMass (physicalSpan G M X) y (M X) F * rectangleTest q (G X) a b F)) ≤
      rectangleConstant r * ∏ i, (b i - a i) + highMass (w X) (physicalSpan G M X) := by
    calc
      _ ≤ ∑ y ∈ range N, w X y *
          (rectangleConstant r * ∏ i, (b i - a i) + coreFiniteRootMixUpperRootMass (physicalSpan G M X) y) := by
        apply sum_le_sum
        intro y hy
        by_cases hwy : w X y = 0
        · simp only [hwy, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left
            (hlayer y (lt_of_le_of_ne (hw X y) (Ne.symm hwy)) q hq hvalid) (hw X y)
      _ = _ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsumN, one_mul, highMass,
          weighted_tsum_eq_sum_of_tail_zero (w X) _ hzero]
  have hmissing : missing (w X) (physicalSpan G M X) (M X) * rectangleTest q (G X) a b ∅ ≤
      missing (w X) (physicalSpan G M X) (M X) :=
    mul_le_of_le_one_right (missing_nonneg (w X) (hw X) _ _ hdata.2.1) (rectangleTest_le_one _ _ _ _ _)
  have hh := _root_.add_le_add hmain hmissing
  exact hh.trans_eq (by unfold rectangleError; ring)

end
end PrimeGapNormality.Prime.CoreCalibratedFrameLimit
