import PrimeGapNormality.Prime.StretchedClock.PositiveComparisonArcLimits
import PrimeGapNormality.Prime.StretchedClock.PositiveComparisonLimits
import PrimeGapNormality.Prime.StretchedClock.PositiveComparisonMesh

/-! Unconditional positive domination of every actual stretched-clock digit
prefix. The constant is chosen before the test and its accuracy. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1200000

/-- Literal arithmetic-free endpoint for the existing digital consumer.
There is no residual prime-pattern, AP-bound, tail, clock, or model premise. -/
theorem exists_positive_prefix_bound {B : ℕ} (hB : 2 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : Circle →ᵇ ℝ) (K : ℝ≥0), LipschitzWith K f → (∀ x, 0 ≤ f x) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
          coreDigitalWindowAverage (orbit B) f 0 (position B N) ≤
            C * (∫ x : Circle, f x) + ε := by
  obtain ⟨A, hA, hgrid⟩ := exists_surrogate_mesh_bound hB
  refine ⟨A, hA.le, ?_⟩
  intro f K hK hf ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hmeshSmall := (tendsto_const_div_atTop_nhds_zero_nat (A * (K : ℝ))).eventually_le_const hε3
  obtain ⟨M, hM, hMsmall⟩ := ((eventually_ge_atTop (1 : ℕ)).and hmeshSmall).exists
  have hMpos : 0 < M := by omega
  have herror : Tendsto (fun N =>
      (K : ℝ) * prefixComparisonError B N (freezeLength N) / (position B N : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      (prefixComparisonError_div_position_tendsto_zero hB).const_mul (K : ℝ)
  have hbad : Tendsto (fun N =>
      2 * ‖f‖ * ((position B (Nat.sqrt N) + 2 * freezeLength N * step B N : ℕ) : ℝ) /
        (position B N : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      (prefixBadWeight_div_position_tendsto_zero hB).const_mul (2 * ‖f‖)
  filter_upwards [hgrid M hMpos, herror.eventually_le_const hε3,
    hbad.eventually_le_const hε3, eventually_gt_atTop (0 : ℕ)] with N hgridN herrN hbadN hN
  have hP : (0 : ℝ) < position B N := Nat.cast_pos.mpr (position_pos hB hN)
  have hsample (i : DigitPair) (hi : i ∈ digitPairs B N) :
      0 ≤ digitFract B i ∧ digitFract B i < 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hcounts : ∀ j < M,
      ((((digitPairs B N).filter fun i => (j : ℝ) / M ≤ digitFract B i ∧
        digitFract B i < ((j : ℝ) + 1) / M).card : ℕ) : ℝ) ≤
          A * (position B N : ℝ) / M := hgridN
  have hs := unit_mesh_positive_mean (digitPairs B N) (digitFract B) hsample
    hMpos hP hcounts f hK hf
  rw [← surrogatePrefixSum_eq_digitPairs B N f] at hs
  have hactual := actual_prefix_le_surrogate hB N (freezeLength N) f hK
  have he : A * ((∫ x : Circle, f x) + (K : ℝ) / M) =
      A * (∫ x : Circle, f x) + A * K / M := by ring
  rw [he] at hs
  linarith

end
end PrimeGapNormality.Prime.StretchedClock
