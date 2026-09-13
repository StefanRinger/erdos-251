import PrimeGapNormality.Prime.CoreRoughScaleDilation
import Mathlib.Topology.Order.Compact

/-! Uniform compact dilation of the literal moving-rough gap scale.
Only the previously proved fixed-dilation limits and eventual monotonicity
are used.  The eventual height threshold precedes every dilation c in K.
-/
namespace PrimeGapNormality.Prime.CoreRoughUniformDilation

open Filter CoreRoughThreshold CoreRoughSyntheticScale CoreRoughCutoffLocality
  CoreRoughScaleDilation
open scoped Topology Classical
noncomputable section

theorem roughGapScale_mono {u v : ℕ} (huv : u ≤ v) :
    roughGapScale u ≤ roughGapScale v := by
  unfold roughGapScale
  exact inv_anti₀ (eulerProdNat_pos v) (eulerProdNat_mono huv)

/-- A monotone sandwich between two fixed dilations supplies uniformity
on the entire compact interval between them. -/
theorem eventually_uniform_interval_of_mono (F : ℝ → ℝ)
    (hF : ∀ x, 0 < F x)
    (hmono : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → F x ≤ F y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : Tendsto (fun x : ℝ => F (a * x) / F x) atTop (𝓝 1))
    (hhi : Tendsto (fun x : ℝ => F (b * x) / F x) atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ c ∈ Set.Icc a b,
      |F (c * x) / F x - 1| < ε := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hmono
  have hax : Tendsto (fun x : ℝ => a * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).2 tendsto_id
  filter_upwards [hax.eventually_ge_atTop x₀, eventually_ge_atTop (0 : ℝ),
    (tendsto_order.mp hlo).1 (1 - ε) (by linarith),
    (tendsto_order.mp hhi).2 (1 + ε) (by linarith)] with x hx hx0 hlow hupp
  intro c hc
  have haxcx : a * x ≤ c * x := mul_le_mul_of_nonneg_right hc.1 hx0
  have hcxbx : c * x ≤ b * x := mul_le_mul_of_nonneg_right hc.2 hx0
  have hleft := div_le_div_of_nonneg_right (hx₀ (a * x) hx (c * x) haxcx) (hF x).le
  have hright := div_le_div_of_nonneg_right
    (hx₀ (c * x) (hx.trans haxcx) (b * x) hcxbx) (hF x).le
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Compact-set version; empty compact sets are included. -/
theorem eventually_uniform_compact_of_mono (F : ℝ → ℝ)
    (hF : ∀ x, 0 < F x)
    (hmono : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → F x ≤ F y)
    (hlimit : ∀ c : ℝ, 0 < c →
      Tendsto (fun x : ℝ => F (c * x) / F x) atTop (𝓝 1))
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ c ∈ K, |F (c * x) / F x - 1| < ε := by
  by_cases hne : K.Nonempty
  · have ha : 0 < sInf K := hKpos (hK.sInf_mem hne)
    have hb : 0 < sSup K := hKpos (hK.sSup_mem hne)
    filter_upwards [eventually_uniform_interval_of_mono F hF hmono ha hb
      (hlimit (sInf K) ha) (hlimit (sSup K) hb) hε] with x hx
    intro c hc
    exact hx c ⟨csInf_le hK.bddBelow hc, le_csSup hK.bddAbove hc⟩
  · exact Eventually.of_forall fun x c hc => (hne ⟨c, hc⟩).elim

/-- Literal real endpoints floor(exp(Ψ(log x))), uniformly for c in any
fixed compact subset of (0,∞).  A is the original arbitrary slope budget. -/
theorem eventually_uniform_real_compact
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ c ∈ K,
      |roughGapScale (realEndpointCutoff Ψ (c * x)) /
        roughGapScale (realEndpointCutoff Ψ x) - 1| < ε := by
  apply eventually_uniform_compact_of_mono
    (fun x => roughGapScale (realEndpointCutoff Ψ x)) (fun x => roughGapScale_pos _)
    ?_ (fun c hc => tendsto_gapScale_real_dilation_ratio_one hSlope hC hreg hc) hK hKpos hε
  filter_upwards [eventually_realEndpointCutoff_mono hC hreg] with x hx
  exact fun y hxy => roughGapScale_mono (hx y hxy)

/-- The exact alternative convention with both natural anchors floored,
again with one height threshold before every c in the compact set. -/
theorem eventually_uniform_floor_compact
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ c ∈ K,
      |roughGapScale (zPsi Ψ ⌊c * x⌋₊) /
        roughGapScale (zPsi Ψ ⌊x⌋₊) - 1| < ε := by
  have hf : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_nat_floor_atTop
  apply eventually_uniform_compact_of_mono
    (fun x => roughGapScale (zPsi Ψ ⌊x⌋₊)) (fun x => roughGapScale_pos _)
    ?_ (fun c hc => tendsto_gapScale_floor_dilation_ratio_one hSlope hC hreg hc) hK hKpos hε
  filter_upwards [hf.eventually (eventually_realEndpointCutoff_mono hC hreg)] with x hx
  intro y hxy
  have hfloor : (⌊x⌋₊ : ℝ) ≤ (⌊y⌋₊ : ℝ) := Nat.cast_le.mpr (Nat.floor_mono hxy)
  have hm := roughGapScale_mono (hx (⌊y⌋₊ : ℝ) hfloor)
  simpa only [realEndpointCutoff, zPsi] using hm

/-- Natural X with numerator at floor(cX), matching the original sequence
enumeration convention; all c in K share the eventual X threshold. -/
theorem eventually_uniform_nat_compact
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C)
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ c ∈ K,
      |roughGapScale (zPsi Ψ ⌊c * (X : ℝ)⌋₊) /
        roughGapScale (zPsi Ψ X) - 1| < ε := by
  have hh := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_uniform_floor_compact hSlope hC hreg hK hKpos hε)
  simpa only [Nat.floor_natCast] using hh

end
end PrimeGapNormality.Prime.CoreRoughUniformDilation
