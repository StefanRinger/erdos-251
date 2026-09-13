import PrimeGapNormality.Prime.StretchedClock.TailAndPositions
import PrimeGapNormality.Prime.StretchedClock.ClockAsymptotics
import PrimeGapNormality.Prime.CoreDigitalLipschitz
import PrimeGapNormality.Prime.CoreWeylNormality

/-!
# From complete stretched-clock prefixes to literal base-B normality

The positive Lipschitz bound below is an explicit intermediate premise.
Its arithmetic supplier is not assumed to have been proved in this file.
All clock and final-incomplete-block estimates, however, concern the actual
`position` and `step` and are derived from their existing asymptotics.

The completed prefixes contain every digit position below `position B N`,
not only the insertion positions. The last lemma concludes the existing
literal digit-frequency predicate for the actual prime-coefficient value.
-/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

noncomputable section

theorem orbit_recurrence (B n : ℕ) : orbit B (n + 1) = B • orbit B n := by
  unfold orbit
  rw [← AddCircle.coe_nsmul]
  congr 1
  simp only [nsmul_eq_mul, pow_succ]
  ring

theorem orbit_character (B : ℕ) (q : ℤ) (n : ℕ) :
    fourier q (orbit B n) = e ((q : ℝ) * (B : ℝ) ^ n * value B) :=
  CoreWeylNormality.fourier_orbit B (value B) q n

/-- The current insertion block, as well as its successor, is negligible
relative to the preceding complete clock prefix. -/
theorem step_div_position_tendsto_zero {B : ℕ} (hB : 2 ≤ B) :
    Tendsto (fun N => (step B N : ℝ) / (position B N : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Eventually.of_forall fun N => ?_) (step_succ_div_position_tendsto_zero hB)
  exact div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (step_mono hB (Nat.le_succ N))) (Nat.cast_nonneg _)

private theorem norm_prefix_average_le (f : ℕ → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1)
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    ‖(∑ i ∈ range n, f i) / (n : ℂ)‖ ≤
      ‖(∑ i ∈ range m, f i) / (m : ℂ)‖ + (n - m : ℕ) / (m : ℝ) := by
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmnr : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  have htail : ‖∑ i ∈ range (n - m), f (m + i)‖ ≤ (n - m : ℕ) := by
    calc
      ‖∑ i ∈ range (n - m), f (m + i)‖ ≤
          ∑ i ∈ range (n - m), ‖f (m + i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ range (n - m), (1 : ℝ) := sum_le_sum fun i _ => hf (m + i)
      _ = (n - m : ℕ) := by simp
  have hsum : ‖∑ i ∈ range n, f i‖ ≤
      ‖∑ i ∈ range m, f i‖ + (n - m : ℕ) := by
    have heq : (∑ i ∈ range n, f i) =
        (∑ i ∈ range m, f i) + ∑ i ∈ range (n - m), f (m + i) := by
      simpa only [Nat.add_sub_of_le hmn] using (sum_range_add f m (n - m))
    rw [heq]
    exact (norm_add_le _ _).trans (_root_.add_le_add le_rfl htail)
  simp only [norm_div, Complex.norm_natCast]
  calc
    ‖∑ i ∈ range n, f i‖ / (n : ℝ) ≤
        ‖∑ i ∈ range n, f i‖ / (m : ℝ) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hmr hmnr
    _ ≤ (‖∑ i ∈ range m, f i‖ + (n - m : ℕ)) / (m : ℝ) :=
      div_le_div_of_nonneg_right hsum hmr.le
    _ = ‖∑ i ∈ range m, f i‖ / (m : ℝ) + (n - m : ℕ) / (m : ℝ) :=
      add_div _ _ _

/-- Vanishing bounded character means on all complete clock prefixes
imply vanishing means at every natural prefix, with no gap hypothesis. -/
theorem prefix_average_tendsto_zero_of_clockPrefixes
    {B : ℕ} (hB : 2 ≤ B) (f : ℕ → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1)
    (hclock : Tendsto (fun N =>
      (∑ i ∈ range (position B N), f i) / (position B N : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun n => (∑ i ∈ range n, f i) / (n : ℂ)) atTop (𝓝 0) := by
  classical
  have hpartition : ∀ n : ℕ, ∃ j : ℕ,
      position B j ≤ n ∧ n < position B (j + 1) := by
    intro n
    have hn : n < position B (n + 1) :=
      (Nat.lt_succ_self n).trans_le (le_position hB (n + 1))
    obtain ⟨j, _hj, r, hr, he⟩ := exists_position_block hB (n + 1) hn
    refine ⟨j, ?_, ?_⟩
    · omega
    · rw [position_succ]
      omega
  choose j hjlo hjhi using hpartition
  have hjtop : Tendsto j atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [eventually_ge_atTop (position B a)] with n hn
    by_contra hja
    have hja' : j n + 1 ≤ a := by omega
    have hp := position_mono hB hja'
    have hn' := hjhi n
    omega
  have hmajor : Tendsto (fun n =>
      ‖(∑ i ∈ range (position B (j n)), f i) / (position B (j n) : ℂ)‖ +
        (step B (j n) : ℝ) / (position B (j n) : ℝ)) atTop (𝓝 0) := by
    have hc := hclock.norm.comp hjtop
    have hs := (step_div_position_tendsto_zero hB).comp hjtop
    simpa only [Function.comp_def, norm_zero, zero_add] using hc.add hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hmajor
  filter_upwards [hjtop.eventually (eventually_gt_atTop (0 : ℕ))] with n hjpos
  have hp : 0 < position B (j n) := position_pos hB hjpos
  have hrem : n - position B (j n) ≤ step B (j n) := by
    have hh := hjhi n
    rw [position_succ] at hh
    omega
  exact (norm_prefix_average_le f hf hp (hjlo n)).trans
    (_root_.add_le_add le_rfl
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr hrem) (Nat.cast_nonneg _)))

/-- Positive Lipschitz domination on every complete clock prefix implies
the actual Weyl criterion. The majorant remains an explicit premise. -/
theorem value_weyl_of_clockPrefix_lipschitz_bounds
    {B : ℕ} (hB : 2 ≤ B) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : Circle →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        coreDigitalWindowAverage (orbit B) f 0 (position B N) ≤
          A * ∫ x, f x ∂volume + ε) :
    weylCriterion B (value B) := by
  intro q hq
  have hshift := coreDigital_window_character_tendsto_zero_of_lipschitz_bounds hB
    (orbit B) (orbit_recurrence B) (fun _ => 0) (fun j => position B (j + 1))
    ((position_tendsto_atTop hB).comp (tendsto_add_atTop_nat 1))
    (fun j => position_pos hB (by omega)) hA
    (fun f K hK hf ε hε =>
      (tendsto_add_atTop_nat 1).eventually (hbound f K hK hf ε hε)) hq
  have hclock : Tendsto (fun N =>
      (∑ i ∈ range (position B N), fourier q (orbit B i)) /
        (position B N : ℂ)) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Nat.zero_add] using hshift
  have hfull := prefix_average_tendsto_zero_of_clockPrefixes hB
    (fun i => fourier q (orbit B i))
    (fun i => (show ‖fourier q (orbit B i)‖ = 1 from _root_.Circle.norm_coe _).le) hclock
  simpa only [orbit_character] using hfull

/-- Literal normality of the stretched prime-coefficient value from the
explicit positive bound, without an extra asymptotic or tail premise. -/
theorem value_isNormal_of_clockPrefix_lipschitz_bounds
    {B : ℕ} (hB : 2 ≤ B) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : Circle →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        coreDigitalWindowAverage (orbit B) f 0 (position B N) ≤
          A * ∫ x, f x ∂volume + ε) :
    PrimeGapNormality.BFree.IsNormal B (value B) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (value_weyl_of_clockPrefix_lipschitz_bounds hB hA hbound)

end
end PrimeGapNormality.Prime.StretchedClock
