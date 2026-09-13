import PrimeGapNormality.Prime.CorePrimeGlobalDiscrepancy
import PrimeGapNormality.Prime.CorePrimeBlockDiscrepancy

/-!
# Quantitative normality of the actual prime-position series

The discrepancy supremum is over ALL anchored intervals simultaneously.
Every word length and every word shares the same eventual threshold and
error constant. The only arithmetic hypothesis is genuine Kuperberg.
The final global passage uses integer-halving at floor(sqrt N), and only
the accepted unconditional quadratic nth-prime upper bound.
-/

namespace PrimeGapNormality.Prime.CorePrimeQuantitativeEnd
open Filter Finset CorePrimeGlobalDiscrepancy
open scoped Topology Classical
noncomputable section

/-- Literal fractional-part definition of the displayed star discrepancy. -/
theorem starDiscrepancy_eq_fractional_counts (B : ℕ) (α : ℝ) (N : ℕ) :
    starDiscrepancy B α N =
      sSup ((fun t : ℝ =>
        |(((range N).filter (fun n => Int.fract ((B : ℝ) ^ n * α) < t)).card : ℝ) / N - t|) ''
          Set.Icc 0 1) := by
  unfold starDiscrepancy
  simp only [prefixMass_eq_count]

/-- Frozen quantitative headline: D*_N(Σ p_n/B^n;B) ≪_B
1/sqrt(log log N), with no block-discrepancy or normalization assumption. -/
theorem primePosition_starDiscrepancy_rate (B : ℕ) (hB : 2 ≤ B) (hK : KuperbergConj13) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      starDiscrepancy B (primePosSeries B) N ≤ C / Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  obtain ⟨C, hC, hblock⟩ := CorePrimeBlockDiscrepancy.primePositionBlock_discrepancy_of_kuperberg B hB hK
  refine ⟨2 * C + 1, by positivity, ?_⟩
  apply star_rate_of_prime_blocks B (primePosSeries B) hC
  filter_upwards [hblock] with X hx
  intro t ht
  exact hx t ht.1 ht.2

/-- One error bound for EVERY base-B word, with no length-dependent
constant or threshold. Empty words are included by the literal cylinder. -/
theorem primePosition_digitWordCount_rate (B : ℕ) (hB : 2 ≤ B) (hK : KuperbergConj13) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ r v : ℕ, v < B ^ r →
      |(digitWordCount B (primePosSeries B) N r v : ℝ) - (N : ℝ) * ((B : ℝ) ^ r)⁻¹| ≤
        C * (N : ℝ) / Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  obtain ⟨C, hC, hstar⟩ := primePosition_starDiscrepancy_rate B hB hK
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hstar, eventually_gt_atTop 0] with N hN hNp
  intro r v hv
  have hword := digitWordCount_error_le B hB (primePosSeries B) hNp r v hv
  have hh := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2 * (N : ℝ) by positivity)
  exact (hword.trans hh).trans_eq (by ring)

/-- The same statement with the existing digitCylinder and actual range-N
count fully exposed, so no weaker notion of word frequency is substituted. -/
theorem primePosition_literal_digit_counts (B : ℕ) (hB : 2 ≤ B) (hK : KuperbergConj13) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ r v : ℕ, v < B ^ r →
      |(((range N).filter (fun n => Int.fract ((B : ℝ) ^ n * primePosSeries B) ∈
        PrimeGapNormality.BFree.digitCylinder B r v)).card : ℝ) -
          (N : ℝ) * ((B : ℝ) ^ r)⁻¹| ≤
        C * (N : ℝ) / Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  primePosition_digitWordCount_rate B hB hK

end
end PrimeGapNormality.Prime.CorePrimeQuantitativeEnd
