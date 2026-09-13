import PrimeGapNormality.Prime.StretchedClock.PrimeArcMajorant
import PrimeGapNormality.Prime.StretchedClock.PrimeArcScales
import PrimeGapNormality.Prime.PrimeIndex

/-! The unconditional first-N-primes arc majorant. The threshold is fixed
before all moduli, unit multipliers and endpoints. No AP-distribution,
Hardy--Littlewood, PNT, or empirical-law premise remains. -/

namespace PrimeGapNormality.Prime.StretchedClock

open Filter Finset
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1500000

def primeIndexArcSet (N a v : ℕ) (s t : ℝ) : Finset ℕ :=
  (range N).filter fun n =>
    s ≤ (((v * nthPrime n) % a : ℕ) : ℝ) / a ∧
      (((v * nthPrime n) % a : ℕ) : ℝ) / a < t

theorem primeIndexArcSet_card_le_height (N a v : ℕ) (s t : ℝ) :
    (primeIndexArcSet N a v s t).card ≤ (primeArcSet (nthPrime N) a v s t).card := by
  have hsub : (primeIndexArcSet N a v s t).image nthPrime ⊆
      primeArcSet (nthPrime N) a v s t := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hp
    obtain ⟨hnN, hns, hnt⟩ := mem_filter.mp hn
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, prime_nthPrime n, hns, hnt⟩
    · exact (show 1 ≤ n + 2 by omega).trans (nthPrime_ge_add_two n)
    · exact nthPrime_mono (Nat.le_of_lt (mem_range.mp hnN))
  have hc := card_le_card hsub
  rwa [card_image_of_injective _ nthPrime_strictMono.injective] at hc

private theorem main_coefficient_le {N a : ℕ} (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ)) (ha : 0 < a) (hR : 1 ≤ arcSieveLevel N)
    (hquot : Real.log (N : ℝ) / 8 ≤
      Real.log (((arcSieveLevel N / a : ℕ) : ℝ) + 1)) :
    (a.totient : ℝ) * ((nthPrime N : ℝ) /
      ((a : ℝ) * restrictedJ a (arcSieveLevel N))) ≤ 192 * (N : ℝ) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hphi : (0 : ℝ) < a.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr ha)
  have hlog0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hden0 : 0 < (a : ℝ) * restrictedJ a (arcSieveLevel N) :=
    mul_pos haR (restrictedJ_pos a hR)
  have hJ := (mul_le_mul_of_nonneg_left hquot (div_nonneg hphi.le haR.le)).trans
    (restrictedJ_ge_totient_log ha (arcSieveLevel N))
  have hscaled := mul_le_mul_of_nonneg_left hJ haR.le
  have hcancel : (a : ℝ) * (((a.totient : ℝ) / a) * (Real.log (N : ℝ) / 8)) =
      (a.totient : ℝ) * Real.log (N : ℝ) / 8 := by
    field_simp [haR.ne'] <;> ring
  rw [hcancel] at hscaled
  have hratio : (a.totient : ℝ) / ((a : ℝ) * restrictedJ a (arcSieveLevel N)) ≤
      8 / Real.log (N : ℝ) := by
    apply (div_le_div_iff₀ hden0 hlog0).mpr
    linarith
  have hp := nthPrime_le_twentyFour_mul_log hN hlog
  have hmajor := mul_le_mul hp hratio (div_nonneg hphi.le hden0.le)
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N)) hlog0.le)
  have he : (24 * (N : ℝ) * Real.log (N : ℝ)) * (8 / Real.log (N : ℝ)) =
      192 * (N : ℝ) := by field_simp [hlog0.ne'] <;> ring
  rw [he] at hmajor
  calc
    (a.totient : ℝ) * ((nthPrime N : ℝ) /
        ((a : ℝ) * restrictedJ a (arcSieveLevel N))) =
      (nthPrime N : ℝ) * ((a.totient : ℝ) /
        ((a : ℝ) * restrictedJ a (arcSieveLevel N))) := by ring
    _ ≤ 192 * (N : ℝ) := hmajor

/-- A fixed explicit constant, before every allowed arithmetic parameter. -/
theorem eventually_primeIndexArcSet_card_le :
    ∀ᶠ N : ℕ in atTop, ∀ a v : ℕ,
      2 ≤ a → (a : ℝ) ≤ Real.log (N : ℝ) ^ 2 → v.Coprime a →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
        ((primeIndexArcSet N a v s t).card : ℝ) ≤
          4096 * (N : ℝ) * (t - s + 1 / Real.sqrt a) +
          4096 * (a : ℝ) * Real.sqrt (N : ℝ) := by
  filter_upwards [eventually_arcSieveLevel_data] with N hdata
  obtain ⟨hN, hlog, hR, hRsmall, hall⟩ := hdata
  intro a v ha haUpper hv s t hs hst ht
  obtain ⟨haLevel, hquot⟩ := hall a ha haUpper
  have ha0 : 0 < a := by omega
  have hheight := primeArcSet_card_le (nthPrime N) a (arcSieveLevel N) v
    ha0 hR haLevel hv hs hst ht
  have hindex : ((primeIndexArcSet N a v s t).card : ℝ) ≤
      ((primeArcSet (nthPrime N) a v s t).card : ℝ) :=
    Nat.cast_le.mpr (primeIndexArcSet_card_le_height N a v s t)
  have hactual := hindex.trans hheight
  have hmain := main_coefficient_le hN hlog ha0 hR hquot
  have hlength : 0 ≤ t - s := sub_nonneg.mpr hst
  have hsqrtA : 0 < Real.sqrt (a : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr ha0)
  have harc0 : 0 ≤ t - s + 16 / Real.sqrt (a : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmain harc0
  have herr1 := mul_le_mul_of_nonneg_left (arcSieveLevel_sq_le_sqrt N) (Nat.cast_nonneg a)
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have herr2 := mul_le_mul_of_nonneg_right ha1 (Real.sqrt_nonneg (N : ℝ))
  have hNlen := mul_nonneg (Nat.cast_nonneg N) hlength
  have hNinv := mul_nonneg (Nat.cast_nonneg N) (inv_nonneg.mpr hsqrtA.le)
  have haSqrt := mul_nonneg (Nat.cast_nonneg a) (Real.sqrt_nonneg (N : ℝ))
  simp only [div_eq_mul_inv] at hactual hscaled ⊢
  nlinarith

/-- Literal first-N-primes fractional-part statement, with an absolute
constant and an absolute threshold preceding all moduli and all arcs. -/
theorem exists_prime_fract_arc_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ a v : ℕ, 2 ≤ a → (a : ℝ) ≤ Real.log (N : ℝ) ^ 2 → v.Coprime a →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
        ((((range N).filter fun n =>
          s ≤ Int.fract ((v : ℝ) * (nthPrime n : ℝ) / a) ∧
          Int.fract ((v : ℝ) * (nthPrime n : ℝ) / a) < t).card : ℕ) : ℝ) ≤
            C * (N : ℝ) * (t - s + 1 / Real.sqrt a) +
            C * (a : ℝ) * Real.sqrt (N : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_primeIndexArcSet_card_le
  refine ⟨4096, by norm_num, N₀, ?_⟩
  intro N hN a v ha haUpper hv s t hs hst ht
  simpa only [fract_mul_div_eq, primeIndexArcSet] using
    hN₀ N hN a v ha haUpper hv s t hs hst ht

end
end PrimeGapNormality.Prime.StretchedClock
