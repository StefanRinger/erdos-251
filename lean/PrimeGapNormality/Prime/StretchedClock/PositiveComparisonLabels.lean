import PrimeGapNormality.Prime.StretchedClock.PositiveComparisonFinite
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Finite two-label domination for all surrogate digit positions. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset
open scoped BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1200000

abbrev DigitPair := Σ _n : ℕ, ℕ

def digitPairs (B N : ℕ) : Finset DigitPair :=
  (range N).sigma fun n => range (step B n)

def digitFract (B : ℕ) (i : DigitPair) : ℝ :=
  Int.fract ((B : ℝ) ^ i.2 * (nthPrime i.1 : ℝ) / ((localBase B i.1 : ℝ) - 1))

def labelFract (B k r n : ℕ) : ℝ :=
  Int.fract ((B : ℝ) ^ r * (nthPrime n : ℝ) / ((B : ℝ) ^ k - 1))

def surrogateArcSet (B N : ℕ) (s t : ℝ) : Finset DigitPair :=
  (digitPairs B N).filter fun i => s ≤ digitFract B i ∧ digitFract B i < t

def labelArcSet (B N k r : ℕ) (s t : ℝ) : Finset ℕ :=
  (range N).filter fun n => s ≤ labelFract B k r n ∧ labelFract B k r n < t

def labelDigitPairs (B N k : ℕ) (s t : ℝ) : Finset DigitPair :=
  (range (step B N)).sigma fun r => labelArcSet B N k r s t

def digitSwap (i : DigitPair) : DigitPair := ⟨i.2, i.1⟩

theorem digitSwap_injective : Function.Injective digitSwap := by
  have h : Function.LeftInverse digitSwap digitSwap := by
    rintro ⟨n, r⟩
    rfl
  exact h.injective

theorem digitPairs_card (B N : ℕ) : (digitPairs B N).card = position B N := by
  simp only [digitPairs, card_sigma, card_range, position]

theorem digitFract_eq_label {B n k r : ℕ} (hk : step B n = k) :
    digitFract B ⟨n, r⟩ = labelFract B k r n := by
  simp only [digitFract, labelFract, localBase, Nat.cast_pow, hk]

theorem surrogatePrefixSum_eq_digitPairs (B N : ℕ) (f : Circle →ᵇ ℝ) :
    surrogatePrefixSum B N f =
      ∑ i ∈ digitPairs B N, f (digitFract B i : Circle) := by
  rw [digitPairs, sum_sigma]
  simp only [digitFract, AddCircle.coe_fract, surrogatePrefixSum, surrogate]

theorem labelDigitPairs_card_le (B N k : ℕ) (s t : ℝ) {C : ℝ}
    (hC : ∀ r < step B N, ((labelArcSet B N k r s t).card : ℝ) ≤ C) :
    ((labelDigitPairs B N k s t).card : ℝ) ≤ (step B N : ℝ) * C := by
  rw [labelDigitPairs, card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ r ∈ range (step B N), C :=
      sum_le_sum fun r hr => hC r (mem_range.mp hr)
    _ = _ := by simp

/-- Every noninitial surrogate arc hit belongs, after swapping (n,r), to
one of two full-N label sets. No label population is used as denominator. -/
theorem surrogateArcSet_card_le_labels {B : ℕ} (hB : 2 ≤ B) (N : ℕ) (s t : ℝ) :
    (surrogateArcSet B N s t).card ≤ position B (Nat.sqrt N) +
      (labelDigitPairs B N (step B (Nat.sqrt N)) s t).card +
      (labelDigitPairs B N (step B (Nat.sqrt N) + 1) s t).card := by
  let E := (digitPairs B (Nat.sqrt N)).image digitSwap
  let L₀ := labelDigitPairs B N (step B (Nat.sqrt N)) s t
  let L₁ := labelDigitPairs B N (step B (Nat.sqrt N) + 1) s t
  have hsub : (surrogateArcSet B N s t).image digitSwap ⊆ (E ∪ L₀) ∪ L₁ := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    rcases j with ⟨n, r⟩
    obtain ⟨hjpair, harc⟩ := mem_filter.mp hj
    obtain ⟨hn, hr⟩ := mem_sigma.mp hjpair
    have hnN : n < N := mem_range.mp hn
    have hrN : r ∈ range (step B N) := mem_range.mpr
      ((mem_range.mp hr).trans_le (step_mono hB (Nat.le_of_lt hnN)))
    by_cases hfirst : n < Nat.sqrt N
    · apply mem_union_left
      apply mem_union_left
      exact mem_image.mpr ⟨⟨n, r⟩, mem_sigma.mpr ⟨mem_range.mpr hfirst, hr⟩, rfl⟩
    · rcases step_eq_or_eq_succ_on_sqrt_window hB (by omega : Nat.sqrt N ≤ n)
        (Nat.le_of_lt hnN) with hlabel | hlabel
      · apply mem_union_left
        apply mem_union_right
        apply mem_sigma.mpr
        refine ⟨hrN, mem_filter.mpr ⟨hn, ?_⟩⟩
        simpa only [digitFract_eq_label hlabel, digitSwap] using harc
      · apply mem_union_right
        apply mem_sigma.mpr
        refine ⟨hrN, mem_filter.mpr ⟨hn, ?_⟩⟩
        simpa only [digitFract_eq_label hlabel, digitSwap] using harc
  have hc := (card_le_card hsub).trans (card_union_le (E ∪ L₀) L₁)
  have hc' := hc.trans (Nat.add_le_add (card_union_le E L₀) le_rfl)
  rw [card_image_of_injective _ digitSwap_injective] at hc'
  have hE : E.card = position B (Nat.sqrt N) := by
    dsimp only [E]
    rw [card_image_of_injective _ digitSwap_injective, digitPairs_card]
  simpa only [hE, L₀, L₁] using hc'

theorem surrogateArcSet_card_le {B : ℕ} (hB : 2 ≤ B) (N : ℕ) (s t : ℝ)
    {C₀ C₁ : ℝ}
    (hC₀ : ∀ r < step B N,
      ((labelArcSet B N (step B (Nat.sqrt N)) r s t).card : ℝ) ≤ C₀)
    (hC₁ : ∀ r < step B N,
      ((labelArcSet B N (step B (Nat.sqrt N) + 1) r s t).card : ℝ) ≤ C₁) :
    ((surrogateArcSet B N s t).card : ℝ) ≤
      (position B (Nat.sqrt N) : ℝ) + (step B N : ℝ) * (C₀ + C₁) := by
  have hn : ((surrogateArcSet B N s t).card : ℝ) ≤
      ((position B (Nat.sqrt N) : ℝ) +
        ((labelDigitPairs B N (step B (Nat.sqrt N)) s t).card : ℝ)) +
        ((labelDigitPairs B N (step B (Nat.sqrt N) + 1) s t).card : ℝ) := by
    exact_mod_cast surrogateArcSet_card_le_labels hB N s t
  have h₀ := labelDigitPairs_card_le B N (step B (Nat.sqrt N)) s t hC₀
  have h₁ := labelDigitPairs_card_le B N (step B (Nat.sqrt N) + 1) s t hC₁
  nlinarith

end
end PrimeGapNormality.Prime.StretchedClock
