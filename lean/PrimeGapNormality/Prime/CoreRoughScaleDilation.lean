import PrimeGapNormality.Prime.CoreRoughDyadicDensity
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Every fixed positive dilation of the actual rough gap scale

The weighted derivative condition first gives eventual monotonicity of
the literal cutoff. The proved coarse prime-loss estimate gives stability
under doubling. A finite dyadic sandwich then handles every fixed real
`c > 0`, including `c < 1`, with both integer floors retained.

The final real-endpoint theorem uses exactly
`floor(exp(Psi(log x)))`, not a replacement interpolated scale. Its bridge
to natural anchors is another monotone dyadic sandwich. No slowly varying
function, density, or distributional hypothesis is an input; no uniformity
in the dilation parameter is claimed.
-/

namespace PrimeGapNormality.Prime.CoreRoughScaleDilation

open Filter Finset
open CoreRoughThreshold CoreRoughSyntheticScale CoreRoughCutoffLocality
  CoreRoughGlobalCutoff CoreRoughDyadicDensity
open scoped Topology

noncomputable section

private theorem gapScale_mono {a b : ℕ} (hab : a ≤ b) :
    roughGapScale a ≤ roughGapScale b := by
  unfold roughGapScale
  exact inv_anti₀ (eulerProdNat_pos b) (eulerProdNat_mono hab)

/-- Eventual monotonicity is derived from the literal derivative input,
on the whole positive tail rather than only one dyadic interval. -/
theorem eventually_realEndpointCutoff_mono
    {Ψ dΨ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      realEndpointCutoff Ψ x ≤ realEndpointCutoff Ψ y := by
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp hreg
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop t₀,
    eventually_gt_atTop (1 : ℝ)] with x hxlog hx
  intro y hxy
  have hlogxy : Real.log x ≤ Real.log y :=
    Real.log_le_log (zero_lt_one.trans hx) hxy
  have hdata : ∀ t ∈ Set.Icc (Real.log x) (Real.log y),
      0 < Ψ t ∧ HasDerivAt Ψ (dΨ t) t ∧
        0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t := by
    intro t ht
    exact ht₀ t (hxlog.trans ht.1)
  have hcmp := CoreRoughThresholdRegularity.psi_interval_comparison
    (Real.log_pos hx) hlogxy hC (fun t ht => (hdata t ht).1)
    (fun t ht => (hdata t ht).2.1) (fun t ht => (hdata t ht).2.2)
  unfold realEndpointCutoff
  exact Nat.floor_le_floor (Real.exp_le_exp.mpr hcmp.1)

private theorem eventually_gapScale_mono
    {Ψ dΨ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, X ≤ Y →
      roughGapScale (zPsi Ψ X) ≤ roughGapScale (zPsi Ψ Y) := by
  have hm := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_realEndpointCutoff_mono hC hreg)
  filter_upwards [hm] with X hX
  intro Y hXY
  exact gapScale_mono (hX (Y : ℝ) (Nat.cast_le.mpr hXY))

private theorem tendsto_eulerProd_two_ratio_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun X : ℕ =>
      eulerProdNat (zPsi Ψ (2 * X)) / eulerProdNat (zPsi Ψ X)) atTop (𝓝 1) := by
  have hglobalReg : CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative Ψ dΨ C := by
    simpa only [CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative,
      CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative] using hreg
  have hglobal := eventually_global_cutoff_and_primeLoss hSlope hC hglobalReg
  have hbounds : ∀ᶠ X : ℕ in atTop,
      (1 - dyadicRootHazard C Ψ X) * eulerProdNat (zPsi Ψ X) ≤
          eulerProdNat (zPsi Ψ (2 * X)) ∧
      eulerProdNat (zPsi Ψ (2 * X)) ≤ eulerProdNat (zPsi Ψ X) := by
    filter_upwards [hglobal] with X hX
    have hc := hX (2 * X) (by constructor <;> omega)
    have hband : (∑ p ∈ Nat.primesLE (zPsi Ψ (2 * X)) \
        Nat.primesLE (zPsi Ψ X),
        (residueCount ({0} : Finset ℕ) p : ℝ) / (p : ℝ)) ≤
        dyadicRootHazard C Ψ X := by
      simpa only [residueCount, Finset.image_singleton, Finset.card_singleton,
        Nat.cast_one, one_div, cutoffPrimeReciprocalLoss, dyadicRootHazard] using hc.2.2
    have hb := CoreRoughEulerStability.finiteTupleSieveProduct_bounds
      ({0} : Finset ℕ) hc.1 hband
    simpa only [CoreRoughRootCount.singleton_tupleProduct] using hb
  have hlower : Tendsto (fun X : ℕ => 1 - dyadicRootHazard C Ψ X)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_dyadicRootHazard_zero (C := C) hSlope)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower (tendsto_const_nhds (x := (1 : ℝ))) ?_ ?_
  · filter_upwards [hbounds] with X hX
    exact (le_div_iff₀ (eulerProdNat_pos _)).2 hX.1
  · filter_upwards [hbounds] with X hX
    exact (div_le_one (eulerProdNat_pos _)).2 hX.2

/-- Actual doubling stability, with the gap-scale rather than Euler-factor
orientation. -/
theorem tendsto_gapScale_two_ratio_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun X : ℕ =>
      roughGapScale (zPsi Ψ (2 * X)) / roughGapScale (zPsi Ψ X))
      atTop (𝓝 1) := by
  have hh := (tendsto_eulerProd_two_ratio_one hSlope hC hreg).inv₀
    (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [roughGapScale, inv_one, inv_div, inv_div_inv] using hh

private theorem tendsto_nat_const_mul_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => k * n) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro N
  exact ⟨N, fun n hn => hn.trans (Nat.le_mul_of_pos_left n hk)⟩

private theorem tendsto_gapScale_two_pow_ratio_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    (m : ℕ) :
    Tendsto (fun X : ℕ =>
      roughGapScale (zPsi Ψ (2 ^ m * X)) / roughGapScale (zPsi Ψ X))
      atTop (𝓝 1) := by
  induction m with
  | zero =>
      apply (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).congr'
      exact Eventually.of_forall fun X => by
        simp only [pow_zero, one_mul, div_self (roughGapScale_pos (zPsi Ψ X)).ne']
  | succ m ih =>
      have hd := (tendsto_gapScale_two_ratio_one hSlope hC hreg).comp
        (tendsto_nat_const_mul_atTop (2 ^ m) (pow_pos (by norm_num) _))
      have hh := hd.mul ih
      simp only [one_mul] at hh
      apply hh.congr'
      exact Eventually.of_forall fun X => by
        simp only [Function.comp_apply]
        rw [show 2 * (2 ^ m * X) = 2 ^ (m + 1) * X by rw [pow_succ]; ring]
        field_simp [(roughGapScale_pos (zPsi Ψ (2 ^ m * X))).ne',
          (roughGapScale_pos (zPsi Ψ X)).ne']

private theorem tendsto_gapScale_ratio_of_bounded_anchors
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {ι : Type*} {l : Filter ι} (u v : ι → ℕ)
    (hu : Tendsto u l atTop) (hv : Tendsto v l atTop) (m : ℕ)
    (hbounded : ∀ᶠ x in l, v x ≤ 2 ^ m * u x ∧ u x ≤ 2 ^ m * v x) :
    Tendsto (fun x => roughGapScale (zPsi Ψ (v x)) /
      roughGapScale (zPsi Ψ (u x))) l (𝓝 1) := by
  have hpow := tendsto_gapScale_two_pow_ratio_one hSlope hC hreg m
  have hlower : Tendsto (fun x => roughGapScale (zPsi Ψ (v x)) /
      roughGapScale (zPsi Ψ (2 ^ m * v x))) l (𝓝 1) := by
    simpa only [Function.comp_apply, inv_one, inv_div] using
      (hpow.comp hv).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hupper : Tendsto (fun x => roughGapScale (zPsi Ψ (2 ^ m * u x)) /
      roughGapScale (zPsi Ψ (u x))) l (𝓝 1) := hpow.comp hu
  have hm := eventually_gapScale_mono hC hreg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [hbounded, hu.eventually hm] with x hx hmono
    exact div_le_div_of_nonneg_left (roughGapScale_pos _).le
      (roughGapScale_pos _) (hmono _ hx.2)
  · filter_upwards [hbounded, hv.eventually hm] with x hx hmono
    exact div_le_div_of_nonneg_right (hmono _ hx.1) (roughGapScale_pos _).le

/-- Both natural anchors are floored explicitly; this real-parameter
version also supplies the integer-parameter endpoint below. -/
theorem tendsto_gapScale_floor_dilation_ratio_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => roughGapScale (zPsi Ψ ⌊c * x⌋₊) /
      roughGapScale (zPsi Ψ ⌊x⌋₊)) atTop (𝓝 1) := by
  have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 tendsto_id
  have hu : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hv : Tendsto (fun x : ℝ => ⌊c * x⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hcx
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (max (2 * c) (2 / c))
    (by norm_num : (1 : ℝ) < 2)
  have hm1 : 2 * c ≤ (2 : ℝ) ^ m := (le_max_left _ _).trans hm.le
  have hm2 : 2 / c ≤ (2 : ℝ) ^ m := (le_max_right _ _).trans hm.le
  apply tendsto_gapScale_ratio_of_bounded_anchors hSlope hC hreg
    (fun x => ⌊x⌋₊) (fun x => ⌊c * x⌋₊) hu hv m
  filter_upwards [eventually_ge_atTop (2 : ℝ), hcx.eventually_ge_atTop 2]
    with x hx hcx2
  have hx0 : 0 ≤ x := by linarith
  have hnle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hxlt := Nat.lt_floor_add_one x
  have hxupper : x ≤ 2 * (⌊x⌋₊ : ℝ) := by nlinarith
  have hqle : (⌊c * x⌋₊ : ℝ) ≤ c * x := Nat.floor_le (mul_nonneg hc.le hx0)
  have hqxlt := Nat.lt_floor_add_one (c * x)
  have hqLower : c * x / 2 ≤ (⌊c * x⌋₊ : ℝ) := by nlinarith
  have hfirst : (⌊c * x⌋₊ : ℝ) ≤ (2 : ℝ) ^ m * (⌊x⌋₊ : ℝ) := by
    calc
      (⌊c * x⌋₊ : ℝ) ≤ c * x := hqle
      _ ≤ c * (2 * (⌊x⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left hxupper hc.le
      _ = (2 * c) * (⌊x⌋₊ : ℝ) := by ring
      _ ≤ (2 : ℝ) ^ m * (⌊x⌋₊ : ℝ) :=
        mul_le_mul_of_nonneg_right hm1 (Nat.cast_nonneg _)
  have hsecond : (⌊x⌋₊ : ℝ) ≤ (2 : ℝ) ^ m * (⌊c * x⌋₊ : ℝ) := by
    have hdiv : x ≤ (2 / c) * (⌊c * x⌋₊ : ℝ) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc).2
      nlinarith
    exact hnle.trans (hdiv.trans
      (mul_le_mul_of_nonneg_right hm2 (Nat.cast_nonneg _)))
  constructor
  · exact_mod_cast hfirst
  · exact_mod_cast hsecond

/-- The requested natural-anchor dilation: `X ↦ floor(c*X)` with every
fixed real `c > 0`, under the unchanged original slope budget. -/
theorem tendsto_gapScale_nat_dilation_ratio_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℕ => roughGapScale (zPsi Ψ ⌊c * (X : ℝ)⌋₊) /
      roughGapScale (zPsi Ψ X)) atTop (𝓝 1) := by
  simpa only [Function.comp_def, Nat.floor_natCast] using
    (tendsto_gapScale_floor_dilation_ratio_one hSlope hC hreg hc).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Evaluating the cutoff at a real endpoint or its natural floor has the
same limiting gap scale. This does not identify the two cutoffs exactly. -/
theorem tendsto_realEndpoint_div_natAnchor_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun x : ℝ => roughGapScale (realEndpointCutoff Ψ x) /
      roughGapScale (zPsi Ψ ⌊x⌋₊)) atTop (𝓝 1) := by
  have hf : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hfr : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hf
  have hm := eventually_realEndpointCutoff_mono hC hreg
  have hupper : Tendsto (fun x : ℝ => roughGapScale (zPsi Ψ (2 * ⌊x⌋₊)) /
      roughGapScale (zPsi Ψ ⌊x⌋₊)) atTop (𝓝 1) :=
    (tendsto_gapScale_two_ratio_one hSlope hC hreg).comp hf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (1 : ℝ))) hupper ?_ ?_
  · filter_upwards [hfr.eventually hm, eventually_ge_atTop (2 : ℝ)] with x hx hx2
    have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hmono := gapScale_mono (hx x hfloor)
    apply (le_div_iff₀ (roughGapScale_pos _)).2
    simpa only [one_mul, realEndpointCutoff, zPsi] using hmono
  · filter_upwards [hm, eventually_ge_atTop (2 : ℝ)] with x hx hx2
    have hfloor := Nat.lt_floor_add_one x
    have hupper : x ≤ ((2 * ⌊x⌋₊ : ℕ) : ℝ) := by
      push_cast
      nlinarith
    have hmono := gapScale_mono (hx ((2 * ⌊x⌋₊ : ℕ) : ℝ) hupper)
    simpa only [realEndpointCutoff, zPsi] using
      div_le_div_of_nonneg_right hmono (roughGapScale_pos (zPsi Ψ ⌊x⌋₊)).le

/-- Literal real-endpoint convention of the paper: the fixed-dilation
ratio for `floor(exp(Psi(log x)))` tends to one. -/
theorem tendsto_gapScale_real_dilation_ratio_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => roughGapScale (realEndpointCutoff Ψ (c * x)) /
      roughGapScale (realEndpointCutoff Ψ x)) atTop (𝓝 1) := by
  have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 tendsto_id
  have hbridge := tendsto_realEndpoint_div_natAnchor_one hSlope hC hreg
  have hmiddle := tendsto_gapScale_floor_dilation_ratio_one hSlope hC hreg hc
  have hh := ((hbridge.comp hcx).mul hmiddle).mul
    (hbridge.inv₀ (by norm_num : (1 : ℝ) ≠ 0))
  simp only [one_mul, inv_one] at hh
  apply hh.congr'
  exact Eventually.of_forall fun x => by
    simp only [Function.comp_apply, inv_div]
    field_simp [(roughGapScale_pos (zPsi Ψ ⌊c * x⌋₊)).ne',
      (roughGapScale_pos (zPsi Ψ ⌊x⌋₊)).ne',
      (roughGapScale_pos (realEndpointCutoff Ψ x)).ne']

end
end PrimeGapNormality.Prime.CoreRoughScaleDilation
