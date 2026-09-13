import PrimeGapNormality.Prime.CoreFrameMeasureDomination
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
Open rectangle bounds imply actual finite-dimensional Lebesgue domination.
A set of finite diameter lies in every slightly enlarged coordinate cube
about one of its points. Letting the enlargement decrease to zero gives
the local diameter estimate consumed by the Hausdorff-measure comparison.
No absolute-continuity hypothesis is imposed on the input measure.
-/

namespace PrimeGapNormality.Prime.CoreRectangleMeasureDomination

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

noncomputable section

/-- Raw diameter estimate derived from the actual open-rectangle bounds.
The measured set need not be measurable. -/
theorem measure_le_diameter_power {n : ℕ} (μ : Measure (Fin n → ℝ)) {K : ℝ}
    (hrect : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      μ (Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)))
    (s : Set (Fin n → ℝ)) (hs : Metric.ediam s ≠ ⊤) :
    μ s ≤ ENNReal.ofReal (K * (2 * Metric.diam s) ^ n) := by
  rcases s.eq_empty_or_nonempty with rfl | hnonempty
  · simp only [measure_empty, zero_le]
  obtain ⟨a, ha⟩ := hnonempty
  let d : ℝ := Metric.diam s
  have hd : 0 ≤ d := Metric.diam_nonneg
  have henlarge (ε : ℝ) (hε : 0 < ε) :
      μ s ≤ ENNReal.ofReal (K * (2 * (d + ε)) ^ n) := by
    let lower : Fin n → ℝ := fun i ↦ a i - (d + ε)
    let upper : Fin n → ℝ := fun i ↦ a i + (d + ε)
    have hwidth : ∀ i, lower i < upper i := by
      intro i
      dsimp only [lower, upper]
      linarith
    have hsub : s ⊆ Set.pi Set.univ (fun i ↦ Ioo (lower i) (upper i)) := by
      intro x hx i _hi
      have hdist : dist x a ≤ d := Metric.dist_le_diam_of_mem' hs hx ha
      have hcoord : |x i - a i| ≤ d := by
        simpa only [Real.dist_eq] using (dist_le_pi_dist x a i).trans hdist
      have hbounds := abs_le.1 hcoord
      constructor <;> dsimp only [lower, upper] <;> linarith [hbounds.1, hbounds.2]
    have hlen (i : Fin n) : upper i - lower i = 2 * (d + ε) := by
      dsimp only [lower, upper]
      ring
    have h := (measure_mono hsub).trans (hrect lower upper hwidth)
    simpa only [hlen, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hcont : Continuous (fun ε : ℝ ↦ ENNReal.ofReal (K * (2 * (d + ε)) ^ n)) := by
    exact ENNReal.continuous_ofReal.comp
      (continuous_const.mul ((continuous_const.mul (continuous_const.add continuous_id)).pow n))
  have hlim : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (K * (2 * (d + ε)) ^ n))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (K * (2 * d) ^ n))) := by
    simpa only [add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (eventually_nhdsWithin_of_forall fun ε hε ↦ henlarge ε hε)

/-- Open rectangles control every small-diameter set, with only the
harmless cube-enlargement factor `2^n` in the constant. -/
theorem ediameter_bound_of_open_rectangles {n : ℕ}
    (μ : Measure (Fin n → ℝ)) {K : ℝ} (hK : 0 < K)
    (hrect : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      μ (Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)))
    (s : Set (Fin n → ℝ)) (hs : Metric.ediam s ≤ 1) :
    μ s ≤ ENNReal.ofReal (K * (2 : ℝ) ^ n) * Metric.ediam s ^ (n : ℝ) := by
  have hfinite : Metric.ediam s ≠ ⊤ := ne_top_of_le_ne_top (by simp) hs
  have h := measure_le_diameter_power μ hrect s hfinite
  have hreal : K * (2 * Metric.diam s) ^ n =
      (K * (2 : ℝ) ^ n) * Metric.diam s ^ n := by rw [mul_pow]; ring
  rw [hreal, ENNReal.ofReal_mul (mul_nonneg hK.le (pow_nonneg (by norm_num) _)),
    ENNReal.ofReal_pow Metric.diam_nonneg, Metric.diam,
    ENNReal.ofReal_toReal hfinite, ← ENNReal.rpow_natCast] at h
  exact h

/-- The actual measure domination supplied by open rectangle bounds.
Finiteness of μ is not needed; the hypothesis itself provides the local
control used by the exact Hausdorff/Lebesgue identification. -/
theorem le_volume_of_open_rectangle_bound {n : ℕ}
    (μ : Measure (Fin n → ℝ)) {K : ℝ} (hK : 0 < K)
    (hrect : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      μ (Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i))) :
    μ ≤ ENNReal.ofReal (K * (2 : ℝ) ^ n) • (volume : Measure (Fin n → ℝ)) :=
  CoreFrameMeasureDomination.le_volume_of_diameter_bound μ
    (mul_pos hK (pow_pos (by norm_num) _))
    (ediameter_bound_of_open_rectangles μ hK hrect)

theorem absolutelyContinuous_of_open_rectangle_bound {n : ℕ}
    (μ : Measure (Fin n → ℝ)) {K : ℝ} (hK : 0 < K)
    (hrect : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      μ (Set.pi Set.univ (fun i ↦ Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i))) : μ ≪ volume :=
  Measure.absolutelyContinuous_of_le_smul
    (le_volume_of_open_rectangle_bound μ hK hrect)

end

end PrimeGapNormality.Prime.CoreRectangleMeasureDomination
