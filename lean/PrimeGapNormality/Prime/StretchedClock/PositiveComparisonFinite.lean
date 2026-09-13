import PrimeGapNormality.Prime.StretchedClock.PositiveComparisonExceptions
import PrimeGapNormality.Prime.StretchedClock.BlockTailComparison
import PrimeGapNormality.Prime.StretchedClock.TailBounds

/-! Complete-prefix comparison with proved exceptional anchor weight. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset
open scoped NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1200000

def freezeError (N H : ℕ) : ℝ :=
  864 * ((N + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ H

def prefixGapBound (N : ℕ) : ℝ :=
  48 * ((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1)

def prefixComparisonError (B N H : ℕ) : ℝ :=
  (N : ℝ) * ((localBase B N : ℝ) / ((B : ℝ) - 1) * freezeError N H) +
    prefixGapBound N / ((localBase B (Nat.sqrt N) : ℝ) * ((B : ℝ) - 1))

def surrogatePrefixSum (B N : ℕ) (f : Circle →ᵇ ℝ) : ℝ :=
  ∑ n ∈ range N, ∑ r ∈ range (step B n), f (surrogate B n r)

theorem freezeError_nonneg (N H : ℕ) : 0 ≤ freezeError N H := by
  unfold freezeError
  positivity

theorem good_anchor_freeze_error {B N H n : ℕ} (hB : 2 ≤ B)
    (hn : n ∈ range N) (hgood : n ∉ prefixBadAnchors B N H) :
    |actualTail B n - frozenTail (localBase B n) n| ≤ freezeError N H := by
  obtain ⟨hnlo, hend, hconstant⟩ := good_anchor_data hB hn hgood
  have hraw := abs_actualTail_sub_frozenTail_le hB hconstant
  have hs : (((n + H + 1 : ℕ) : ℝ) ^ 2) ≤ (((N + 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast Nat.pow_le_pow_left (by omega : n + H + 1 ≤ N + 1) 2
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by norm_num)) (by positivity))

theorem block_test_error_le_common {B N H n : ℕ} (hB : 2 ≤ B)
    (hn : n ∈ range N) (hgood : n ∉ prefixBadAnchors B N H)
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    (∑ r ∈ range (step B n),
      |f (orbit B (position B n + r)) - f (surrogate B n r)|) ≤
      (K : ℝ) * ((localBase B N : ℝ) / ((B : ℝ) - 1) * freezeError N H +
        gapMajorant n / ((localBase B (Nat.sqrt N) : ℝ) * ((B : ℝ) - 1))) := by
  have hh := block_test_error_le hB f hK (good_anchor_freeze_error hB hn hgood)
  have hd : 0 < (B : ℝ) - 1 := sub_pos.mpr (one_lt_base hB)
  have hqmax : (localBase B n : ℝ) ≤ localBase B N :=
    Nat.cast_le.mpr (localBase_mono hB (Nat.le_of_lt (mem_range.mp hn)))
  have hqmin : (localBase B (Nat.sqrt N) : ℝ) ≤ localBase B n :=
    Nat.cast_le.mpr (localBase_mono hB (good_anchor_data hB hn hgood).1)
  have hqpos : (0 : ℝ) < localBase B (Nat.sqrt N) := by
    have hh := localBase_two_le hB (Nat.sqrt N)
    exact_mod_cast (show 0 < localBase B (Nat.sqrt N) by omega)
  have hfreeze : ((localBase B n : ℝ) - 1) / ((B : ℝ) - 1) * freezeError N H ≤
      (localBase B N : ℝ) / ((B : ℝ) - 1) * freezeError N H :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by linarith) hd.le) (freezeError_nonneg N H)
  have hgap : gapMajorant n / ((localBase B n : ℝ) * ((B : ℝ) - 1)) ≤
      gapMajorant n / ((localBase B (Nat.sqrt N) : ℝ) * ((B : ℝ) - 1)) :=
    div_le_div_of_nonneg_left (gapMajorant_nonneg n) (mul_pos hqpos hd)
      (mul_le_mul_of_nonneg_right hqmin hd.le)
  exact hh.trans (mul_le_mul_of_nonneg_left (_root_.add_le_add hfreeze hgap) K.coe_nonneg)

theorem block_test_error_le_two_norm (B n : ℕ) (f : Circle →ᵇ ℝ) :
    (∑ r ∈ range (step B n),
      |f (orbit B (position B n + r)) - f (surrogate B n r)|) ≤
      2 * ‖f‖ * (step B n : ℝ) := by
  calc
    _ ≤ ∑ r ∈ range (step B n), 2 * ‖f‖ := by
      apply sum_le_sum
      intro r hr
      simpa only [Real.dist_eq] using
        f.dist_le_two_norm (orbit B (position B n + r)) (surrogate B n r)
    _ = _ := by simp [mul_comm]

theorem full_prefix_test_error_le {B : ℕ} (hB : 2 ≤ B) (N H : ℕ)
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    (∑ n ∈ range N, ∑ r ∈ range (step B n),
      |f (orbit B (position B n + r)) - f (surrogate B n r)|) ≤
      (K : ℝ) * prefixComparisonError B N H +
        2 * ‖f‖ * ((position B (Nat.sqrt N) + 2 * H * step B N : ℕ) : ℝ) := by
  let E := prefixBadAnchors B N H
  let common : ℕ → ℝ := fun n =>
    (localBase B N : ℝ) / ((B : ℝ) - 1) * freezeError N H +
      gapMajorant n / ((localBase B (Nat.sqrt N) : ℝ) * ((B : ℝ) - 1))
  have hc0 (n : ℕ) : 0 ≤ common n := by
    have hd : 0 < (B : ℝ) - 1 := sub_pos.mpr (one_lt_base hB)
    have hgap := gapMajorant_nonneg n
    have hf := freezeError_nonneg N H
    dsimp [common]
    positivity
  have hp (n : ℕ) (hn : n ∈ range N) :
      (∑ r ∈ range (step B n),
        |f (orbit B (position B n + r)) - f (surrogate B n r)|) ≤
        (K : ℝ) * common n + if n ∈ E then 2 * ‖f‖ * (step B n : ℝ) else 0 := by
    by_cases hbad : n ∈ E
    · rw [if_pos hbad]
      exact (block_test_error_le_two_norm B n f).trans
        (le_add_of_nonneg_left (mul_nonneg K.coe_nonneg (hc0 n)))
    · rw [if_neg hbad, add_zero]
      exact block_test_error_le_common hB hn hbad f hK
  have hsum := sum_le_sum hp
  rw [sum_add_distrib, ← mul_sum] at hsum
  have hcommon : (∑ n ∈ range N, common n) ≤ prefixComparisonError B N H := by
    dsimp [common, prefixComparisonError]
    rw [sum_add_distrib, ← sum_div]
    have hZ := sum_gapMajorant_le N
    have hd : 0 ≤ (localBase B (Nat.sqrt N) : ℝ) * ((B : ℝ) - 1) := by
      have := (sub_pos.mpr (one_lt_base hB)).le
      positivity
    have hh := _root_.add_le_add
      (le_refl ((N : ℝ) * ((localBase B N : ℝ) / ((B : ℝ) - 1) * freezeError N H)))
      (div_le_div_of_nonneg_right hZ hd)
    simpa only [sum_const, card_range, nsmul_eq_mul, prefixGapBound] using hh
  have hbadSum : (∑ n ∈ range N,
      if n ∈ E then 2 * ‖f‖ * (step B n : ℝ) else 0) ≤
        2 * ‖f‖ * ((position B (Nat.sqrt N) + 2 * H * step B N : ℕ) : ℝ) := by
    have hsub : E ⊆ range N := prefixBadAnchors_subset B N H
    have hfilter : (range N).filter (fun n => n ∈ E) = E := by
      ext n
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    rw [← sum_filter, hfilter, ← mul_sum, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (prefixBadAnchors_weight_le hB N H))
      (mul_nonneg (by norm_num) (norm_nonneg f))
  exact hsum.trans (_root_.add_le_add
    (mul_le_mul_of_nonneg_left hcommon K.coe_nonneg) hbadSum)

/-- Comparison of literal consecutive base-B orbit positions with all
surrogate digits; the exceptional cost uses the original prefix denominator. -/
theorem actual_prefix_le_surrogate {B : ℕ} (hB : 2 ≤ B) (N H : ℕ)
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    coreDigitalWindowAverage (orbit B) f 0 (position B N) ≤
      surrogatePrefixSum B N f / (position B N : ℝ) +
        (K : ℝ) * prefixComparisonError B N H / (position B N : ℝ) +
        2 * ‖f‖ * ((position B (Nat.sqrt N) + 2 * H * step B N : ℕ) : ℝ) /
          (position B N : ℝ) := by
  have he := full_prefix_test_error_le hB N H f hK
  have hp : (∑ n ∈ range N, ∑ r ∈ range (step B n),
      f (orbit B (position B n + r))) ≤ surrogatePrefixSum B N f +
        ∑ n ∈ range N, ∑ r ∈ range (step B n),
          |f (orbit B (position B n + r)) - f (surrogate B n r)| := by
    unfold surrogatePrefixSum
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro n hn
    rw [← sum_add_distrib]
    exact sum_le_sum fun r hr => by
      linarith [le_abs_self (f (orbit B (position B n + r)) - f (surrogate B n r))]
  have hs := hp.trans (_root_.add_le_add le_rfl he)
  rw [sum_variable_blocks (step B) (position B) (position_zero B) (position_succ B)
    (fun j => f (orbit B j)) N] at hs
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (position B N))
  simpa only [coreDigitalWindowAverage, Nat.zero_add, add_div, add_assoc] using hh

end
end PrimeGapNormality.Prime.StretchedClock
