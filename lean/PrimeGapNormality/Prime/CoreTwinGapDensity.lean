import PrimeGapNormality.Prime.CoreTwinCountUpper
import PrimeGapNormality.Prime.CoreSparseBinarySeries
import PrimeGapNormality.Prime.ChebyshevNthPrime

/-!
# Zero density of two-gaps in prime-index space

The unconditional physical prime-pair upper bound is transferred to the
actual zero-based prime-gap indicator.  Only the proved Chebyshev upper
bound for `nthPrime` and the elementary lower bound `n+2 ≤ nthPrime n` are
used.  No twin-prime infinitude statement is made.
-/

namespace PrimeGapNormality.Prime.CoreTwinGapDensity

open Finset Filter CoreTwinCountUpper CoreSparseBinarySeries
open scoped Topology Classical

noncomputable section

/-- Literal bit attached to the event that the next prime gap is two. -/
def twinGapBit (n : ℕ) : ℕ :=
  if primeGap n = 2 then 1 else 0

theorem twinGapBit_isBitSequence : IsBitSequence twinGapBit := by
  intro n
  unfold twinGapBit
  split_ifs <;> simp

private theorem twinGapBit_eq_one_iff (n : ℕ) :
    twinGapBit n = 1 ↔ primeGap n = 2 := by
  unfold twinGapBit
  split_ifs with h <;> simp [h]

/-- The first `N` two-gaps inject into physical twin-prime starts no larger
than `nthPrime N`. -/
theorem twinGap_oneCount_le_pairCount (N : ℕ) :
    oneCount twinGapBit N ≤ twinPrimeStartCount (nthPrime N) := by
  let source := (range N).filter (fun n ↦ twinGapBit n = 1)
  let target := (Ico 1 (nthPrime N + 1)).filter
    (fun m ↦ Nat.Prime m ∧ Nat.Prime (m + 2))
  let embed : ↑source → ↑target := fun n ↦ ⟨nthPrime n.1, by
    apply mem_filter.mpr
    have hn : n.1 < N := mem_range.mp (mem_filter.mp n.2).1
    have hgap : primeGap n.1 = 2 :=
      (twinGapBit_eq_one_iff n.1).mp (mem_filter.mp n.2).2
    have hmono : nthPrime n.1 < nthPrime (n.1 + 1) :=
      nthPrime_strictMono (Nat.lt_succ_self n.1)
    have hnext : nthPrime (n.1 + 1) = nthPrime n.1 + 2 := by
      unfold primeGap at hgap
      omega
    refine ⟨mem_Ico.mpr ⟨(prime_nthPrime n.1).pos,
      Nat.lt_succ_of_le (nthPrime_mono (Nat.le_of_lt hn))⟩, ?_⟩
    exact ⟨prime_nthPrime n.1, by rw [← hnext]; exact prime_nthPrime (n.1 + 1)⟩⟩
  have hinj : Function.Injective embed := by
    intro m n hmn
    apply Subtype.ext
    have hv := congrArg Subtype.val hmn
    exact nthPrime_strictMono.injective hv
  change source.card ≤ target.card
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective embed hinj

private theorem tendsto_nthPrime_atTop : Tendsto nthPrime atTop atTop :=
  tendsto_atTop_atTop_of_monotone nthPrime_mono fun b ↦
    ⟨b, (Nat.le_add_right b 2).trans (nthPrime_ge_add_two b)⟩

/-- The actual prime-index bit sequence has zero one-density. -/
theorem twinGapBit_hasZeroOneDensity : HasZeroOneDensity twinGapBit := by
  obtain ⟨A, hA, hupper⟩ := twinPrimeStartCount_isBigO
  have hupperN := tendsto_nthPrime_atTop.eventually hupper
  have hlogN : Tendsto (fun N : ℕ ↦ Real.log ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2))
  have hmajor : Tendsto (fun N : ℕ ↦ 16 * A /
      Real.log ((N + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hlogN
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using hinv.const_mul (16 * A)
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hupperN, hlogN.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℕ)] with N hcount hlog1 hN
    have hindex := twinGap_oneCount_le_pairCount N
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hpLower : ((N + 2 : ℕ) : ℝ) ≤ (nthPrime N : ℝ) :=
      Nat.cast_le.mpr (nthPrime_ge_add_two N)
    have hlogp : Real.log ((N + 2 : ℕ) : ℝ) ≤
        Real.log (nthPrime N : ℝ) :=
      Real.log_le_log (by positivity) hpLower
    have hlogpPos : 0 < Real.log (nthPrime N : ℝ) :=
      zero_lt_one.trans_le (hlog1.trans hlogp)
    have hpUpper := nthPrime_le_succ_mul_log N
    have hNratio : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      push_cast
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hlogratio : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤
        2 * Real.log ((N + 2 : ℕ) : ℝ) := by linarith
    have hpSimple : (nthPrime N : ℝ) ≤
        16 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) := by
      calc
        (nthPrime N : ℝ) ≤
            4 * ((N + 1 : ℕ) : ℝ) *
              (Real.log ((N + 2 : ℕ) : ℝ) + 1) := hpUpper
        _ ≤ 4 * (2 * (N : ℝ)) *
              (2 * Real.log ((N + 2 : ℕ) : ℝ)) := by
          gcongr
        _ = _ := by ring
    have hden : Real.log ((N + 2 : ℕ) : ℝ) ^ 2 ≤
        Real.log (nthPrime N : ℝ) ^ 2 :=
      pow_le_pow_left₀ (zero_le_one.trans hlog1) hlogp 2
    have htarget : A * ((nthPrime N : ℝ) /
        Real.log (nthPrime N : ℝ) ^ 2) / (N : ℝ) ≤
          16 * A / Real.log ((N + 2 : ℕ) : ℝ) := by
      have hlog0 : 0 < Real.log ((N + 2 : ℕ) : ℝ) :=
        zero_lt_one.trans_le hlog1
      have hA0 : 0 ≤ A := hA.le
      have hfrac : (nthPrime N : ℝ) / Real.log (nthPrime N : ℝ) ^ 2 ≤
          (16 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) /
            Real.log ((N + 2 : ℕ) : ℝ) ^ 2 := by
        calc
          (nthPrime N : ℝ) / Real.log (nthPrime N : ℝ) ^ 2 ≤
              (16 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) /
                Real.log (nthPrime N : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hpSimple (sq_nonneg _)
          _ ≤ (16 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) /
                Real.log ((N + 2 : ℕ) : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left
              (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
                hlog0.le)
              (sq_pos_of_pos hlog0) hden
      have hscaled := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfrac hA0) hNpos.le
      calc
        A * ((nthPrime N : ℝ) / Real.log (nthPrime N : ℝ) ^ 2) /
            (N : ℝ) ≤
          A * ((16 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) /
            Real.log ((N + 2 : ℕ) : ℝ) ^ 2) / (N : ℝ) := hscaled
        _ = 16 * A / Real.log ((N + 2 : ℕ) : ℝ) := by
          field_simp [hNpos.ne', hlog0.ne'] <;> ring
    have hcast : (oneCount twinGapBit N : ℝ) ≤
        (twinPrimeStartCount (nthPrime N) : ℝ) := by exact_mod_cast hindex
    have hchain := hcast.trans hcount
    exact (div_le_div_of_nonneg_right hchain (Nat.cast_nonneg N)).trans htarget
  · exact hmajor

/-- Consequently the literal twin-gap indicator series is unconditionally
not normal in base two.  This conclusion does not use twin-prime infinitude. -/
theorem twinGapBinarySeries_not_isNormal_two :
    ¬ PrimeGapNormality.BFree.IsNormal 2 (binarySeries twinGapBit) :=
  binarySeries_not_isNormal_two twinGapBit_isBitSequence twinGapBit_hasZeroOneDensity

end

end PrimeGapNormality.Prime.CoreTwinGapDensity
