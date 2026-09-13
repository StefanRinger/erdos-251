import PrimeGapNormality.Prime.CoreRectangleMeasureDomination
import Mathlib.Topology.Order.Bornology

/-!
# Sharp measure domination from open rectangles

The earlier diameter reduction centered a cube at one point of the set,
which doubled every side length.  Here each coordinate is enclosed between
the infimum and supremum of its actual projection.  The projected diameter
is at most the ambient sup-norm diameter, so an epsilon enlargement has
side length at most `diam s + 2 * epsilon`.  Sending epsilon to zero removes
the geometric `2^n` loss.

This argument also covers `n = 0`: the coordinate products and all
coordinate conditions are then vacuous, while the unique open rectangle is
the whole singleton space.
-/

namespace PrimeGapNormality.Prime.CoreRectangleMeasureDominationSharp

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1000000

/-- A set of finite diameter is enclosed in its coordinate hull.  An
epsilon enlargement makes the hull an open rectangle while each side is
at most `diam s + 2 epsilon`. -/
theorem measure_le_diameter_power_sharp {n : ℕ}
    (mu : Measure (Fin n → ℝ)) {K : ℝ} (hK : 0 ≤ K)
    (hrect : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      mu (Set.pi Set.univ (fun i => Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)))
    (s : Set (Fin n → ℝ)) (hs : Metric.ediam s ≠ ⊤) :
    mu s ≤ ENNReal.ofReal (K * Metric.diam s ^ n) := by
  rcases s.eq_empty_or_nonempty with rfl | hnonempty
  · simp only [measure_empty, zero_le]
  let d : ℝ := Metric.diam s
  have hd : 0 ≤ d := Metric.diam_nonneg
  have hsBounded : Bornology.IsBounded s := Metric.isBounded_iff_ediam_ne_top.mpr hs
  let coord : Fin n → Set ℝ := fun i => Function.eval i '' s
  have hcoordNonempty (i : Fin n) : (coord i).Nonempty := hnonempty.image _
  have hcoordBounded (i : Fin n) : Bornology.IsBounded (coord i) := by
    dsimp only [coord]
    exact hsBounded.image_eval i
  have hcoordDiam (i : Fin n) :
      sSup (coord i) - sInf (coord i) ≤ d := by
    rw [← Real.diam_eq (hcoordBounded i)]
    have hh := (LipschitzWith.eval i).diam_image_le s hsBounded
    simpa only [NNReal.coe_one, one_mul, coord, d] using hh
  have henlarge (epsilon : ℝ) (hepsilon : 0 < epsilon) :
      mu s ≤ ENNReal.ofReal (K * (d + 2 * epsilon) ^ n) := by
    let lower : Fin n → ℝ := fun i => sInf (coord i) - epsilon
    let upper : Fin n → ℝ := fun i => sSup (coord i) + epsilon
    have hwidth (i : Fin n) : lower i < upper i := by
      have hinfsup : sInf (coord i) ≤ sSup (coord i) :=
        csInf_le_csSup (hcoordNonempty i)
          (hcoordBounded i).bddBelow (hcoordBounded i).bddAbove
      dsimp only [lower, upper]
      linarith
    have hsub : s ⊆ Set.pi Set.univ (fun i => Ioo (lower i) (upper i)) := by
      intro x hx i hi
      have hxi : x i ∈ coord i := ⟨x, hx, rfl⟩
      have hlo : sInf (coord i) ≤ x i :=
        csInf_le (hcoordBounded i).bddBelow hxi
      have hhi : x i ≤ sSup (coord i) :=
        le_csSup (hcoordBounded i).bddAbove hxi
      dsimp only [lower, upper]
      constructor <;> linarith
    have hside (i : Fin n) : upper i - lower i ≤ d + 2 * epsilon := by
      dsimp only [upper, lower]
      linarith [hcoordDiam i]
    have hside0 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ upper i - lower i := by
      intro i hi
      exact sub_nonneg.mpr (hwidth i).le
    have hprod : (∏ i : Fin n, (upper i - lower i)) ≤
        (d + 2 * epsilon) ^ n := by
      have hh := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
        hside0 (fun i hi => hside i)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh
    calc
      mu s ≤ mu (Set.pi Set.univ (fun i => Ioo (lower i) (upper i))) :=
        measure_mono hsub
      _ ≤ ENNReal.ofReal (K * ∏ i, (upper i - lower i)) :=
        hrect lower upper hwidth
      _ ≤ ENNReal.ofReal (K * (d + 2 * epsilon) ^ n) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hprod hK)
  have hcont : Continuous
      (fun epsilon : ℝ => ENNReal.ofReal (K * (d + 2 * epsilon) ^ n)) := by
    exact ENNReal.continuous_ofReal.comp
      (continuous_const.mul
        ((continuous_const.add (continuous_const.mul continuous_id)).pow n))
  have hlim : Tendsto
      (fun epsilon : ℝ => ENNReal.ofReal (K * (d + 2 * epsilon) ^ n))
      (nhdsWithin 0 (Ioi 0))
      (nhds (ENNReal.ofReal (K * d ^ n))) := by
    simpa only [mul_zero, add_zero] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (eventually_nhdsWithin_of_forall fun epsilon hepsilon =>
      henlarge epsilon hepsilon)

/-- Sharp local Hausdorff input: no coordinate factor is lost when the
open-rectangle estimate is converted to an emetric-diameter estimate. -/
theorem ediameter_bound_of_open_rectangles_sharp {n : ℕ}
    (mu : Measure (Fin n → ℝ)) {K : ℝ} (hK : 0 < K)
    (hrect : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      mu (Set.pi Set.univ (fun i => Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i)))
    (s : Set (Fin n → ℝ)) (hs : Metric.ediam s ≤ 1) :
    mu s ≤ ENNReal.ofReal K * Metric.ediam s ^ (n : ℝ) := by
  have hfinite : Metric.ediam s ≠ ⊤ := ne_top_of_le_ne_top (by simp) hs
  have hh := measure_le_diameter_power_sharp mu hK.le hrect s hfinite
  rw [ENNReal.ofReal_mul hK.le,
    ENNReal.ofReal_pow Metric.diam_nonneg, Metric.diam,
    ENNReal.ofReal_toReal hfinite, ← ENNReal.rpow_natCast] at hh
  exact hh

/-- Exact Lebesgue domination from all open axis-parallel rectangles.
Unlike the older cube-centered adapter, the scalar is exactly `K`. -/
theorem le_volume_of_open_rectangle_bound_sharp {n : ℕ}
    (mu : Measure (Fin n → ℝ)) {K : ℝ} (hK : 0 < K)
    (hrect : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      mu (Set.pi Set.univ (fun i => Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i))) :
    mu ≤ ENNReal.ofReal K • (volume : Measure (Fin n → ℝ)) :=
  CoreFrameMeasureDomination.le_volume_of_diameter_bound mu hK
    (ediameter_bound_of_open_rectangles_sharp mu hK hrect)

theorem absolutelyContinuous_of_open_rectangle_bound_sharp {n : ℕ}
    (mu : Measure (Fin n → ℝ)) {K : ℝ} (hK : 0 < K)
    (hrect : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      mu (Set.pi Set.univ (fun i => Ioo (a i) (b i))) ≤
        ENNReal.ofReal (K * ∏ i, (b i - a i))) :
    mu ≪ volume :=
  Measure.absolutelyContinuous_of_le_smul
    (le_volume_of_open_rectangle_bound_sharp mu hK hrect)

end

end PrimeGapNormality.Prime.CoreRectangleMeasureDominationSharp
