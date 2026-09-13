import PrimeGapNormality.Prime.CoreAuxiliaryGapMean

/-!
# Original-law tails of a fixed-rank deleted frame

Every expectation below uses `actualRootLaw y S`, before any auxiliary
change of measure. The deleted point is the fixed order statistic `j`,
not a uniformly chosen point. Exact rooted first-gap means and the
deterministic two-neighbour deletion bound give the cutoff error.
-/

namespace PrimeGapNormality.Prime.CoreOriginalDeletedFrame

open Finset
open scoped Classical BigOperators

noncomputable section

/-- Original rooted expectation, discarding (not renormalizing) `|U| < L`. -/
def highMean (y S L : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U *
    if L ≤ U.card then f U else 0

private theorem rootLaw_nonneg (y S : ℕ) (U : Finset ℕ) :
    0 ≤ actualRootLaw y S U := by
  unfold actualRootLaw
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem highMean_nonneg (y S L : ℕ) {f : Finset ℕ → ℝ}
    (hf : ∀ U, 0 ≤ f U) : 0 ≤ highMean y S L f := by
  apply sum_nonneg
  intro U _
  apply mul_nonneg (rootLaw_nonneg y S U)
  split_ifs
  · exact hf U
  · exact le_rfl

theorem highMean_mono (y S L : ℕ) {f g : Finset ℕ → ℝ}
    (hfg : ∀ U, L ≤ U.card → f U ≤ g U) :
    highMean y S L f ≤ highMean y S L g := by
  apply sum_le_sum
  intro U _
  apply mul_le_mul_of_nonneg_left _ (rootLaw_nonneg y S U)
  split_ifs with h
  · exact hfg U h
  · exact le_rfl

theorem highMean_add (y S L : ℕ) (f g : Finset ℕ → ℝ) :
    highMean y S L (fun U => f U + g U) =
      highMean y S L f + highMean y S L g := by
  unfold highMean
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro U _
  split_ifs <;> ring

theorem highMean_sum (y S L : ℕ) (I : Finset ℕ)
    (f : ℕ → Finset ℕ → ℝ) :
    highMean y S L (fun U => ∑ i ∈ I, f i U) =
      ∑ i ∈ I, highMean y S L (f i) := by
  unfold highMean
  rw [sum_comm]
  apply sum_congr rfl
  intro U _
  by_cases h : L ≤ U.card
  · simp only [if_pos h, mul_sum]
  · simp only [if_neg h, mul_zero, sum_const_zero]

theorem highMean_div (y S L : ℕ) (f : Finset ℕ → ℝ) (c : ℝ) :
    highMean y S L (fun U => f U / c) = highMean y S L f / c := by
  unfold highMean
  rw [sum_div]
  apply sum_congr rfl
  intro U _
  split_ifs <;> ring

private theorem sievePoint_mono (y : ℕ) (σ : ResidueChoice y) :
    Monotone (sievePoint y (residueOfChoice y σ)) := by
  intro a b hab
  rw [core_sievePoint_eq_periodicPoint, core_sievePoint_eq_periodicPoint]
  exact (corePeriodicPoint_strictMono (coreRootedPeriod y)
    (coreSievePeriodSurvivors y σ) (coreSievePeriod_card y σ)
    (coreSievePeriodSurvivors_subset y σ)).monotone hab

/-- A valid original gap, with only the high-cardinality mass retained,
has expectation at most the exact infinite rooted-gap mean. -/
theorem original_gap_mean_le (y S L i : ℕ) (hi : i + 1 ≤ L) :
    highMean y S L (fun U => (subsetGap U i : ℝ)) ≤ (eulerProdNat y)⁻¹ := by
  rw [highMean, coreAux_actualRootLaw_expectation]
  calc
    (∑ σ : ResidueChoice y,
        if L ≤ (sieveSurvivorsFin y σ S).card then
          (subsetGap (sieveSurvivorsFin y σ S) i : ℝ) else 0) /
        (Fintype.card (ResidueChoice y) : ℝ) ≤
      (∑ σ : ResidueChoice y,
        ((sievePoint y (residueOfChoice y σ) (i + 1) : ℝ) -
          (sievePoint y (residueOfChoice y σ) i : ℝ))) /
        (Fintype.card (ResidueChoice y) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro σ _
      by_cases h : L ≤ (sieveSurvivorsFin y σ S).card
      · rw [if_pos h, coreAux_subsetGap_sieveSurvivorsFin y S σ i (hi.trans h)]
      · rw [if_neg h]
        exact sub_nonneg.mpr (Nat.cast_le.mpr
          (sievePoint_mono y σ (Nat.le_succ i)))
    _ = (eulerProdNat y)⁻¹ := core_rooted_sieve_gap_mean y i

/-- The literal deletion of the fixed `j`th positive point. -/
def deleted (j : ℕ) (U : Finset ℕ) : Finset ℕ := U.erase (orderStat U j)

theorem deleted_gap_le {L j i : ℕ} (hj0 : 1 ≤ j) (hjL : j ≤ L)
    (hi : i + 1 < L) (U : Finset ℕ) (hU : L ≤ U.card) :
    (subsetGap (deleted j U) i : ℝ) ≤
      (subsetGap U i : ℝ) + (subsetGap U (i + 1) : ℝ) := by
  exact_mod_cast coreAux_subsetGap_erase_le_neighbor_sum
    (auxDel_orderStat_mem hj0 (hjL.trans hU)) (hi.trans_le hU)

theorem deleted_gap_mean_le (y S L j i : ℕ)
    (hj0 : 1 ≤ j) (hjL : j ≤ L) (hi : i + 1 < L) :
    highMean y S L (fun U => (subsetGap (deleted j U) i : ℝ)) ≤
      (2 : ℝ) * (eulerProdNat y)⁻¹ := by
  calc
    highMean y S L (fun U => (subsetGap (deleted j U) i : ℝ)) ≤
        highMean y S L (fun U =>
          (subsetGap U i : ℝ) + (subsetGap U (i + 1) : ℝ)) :=
      highMean_mono y S L (deleted_gap_le hj0 hjL hi)
    _ = highMean y S L (fun U => (subsetGap U i : ℝ)) +
        highMean y S L (fun U => (subsetGap U (i + 1) : ℝ)) :=
      highMean_add y S L _ _
    _ ≤ (eulerProdNat y)⁻¹ + (eulerProdNat y)⁻¹ :=
      add_le_add (original_gap_mean_le y S L i hi.le)
        (original_gap_mean_le y S L (i + 1) (by omega))
    _ = (2 : ℝ) * (eulerProdNat y)⁻¹ := by ring

def frameSum (I : Finset ℕ) (j : ℕ) (U : Finset ℕ) : ℝ :=
  ∑ i ∈ I, (subsetGap (deleted j U) i : ℝ)

theorem frameSum_nonneg (I : Finset ℕ) (j : ℕ) (U : Finset ℕ) :
    0 ≤ frameSum I j U := sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- The original fixed-rank deletion frame first moment. There is no
auxiliary law or conditional frame-moment premise in this bound. -/
theorem normalized_frame_mean_le (y S L j : ℕ) (I : Finset ℕ)
    (hj0 : 1 ≤ j) (hjL : j ≤ L) (hI : ∀ i ∈ I, i + 1 < L)
    {G : ℝ} (hG : 0 < G) :
    highMean y S L (fun U => frameSum I j U / G) ≤
      (2 * (I.card : ℝ)) / (G * eulerProdNat y) := by
  rw [highMean_div]
  have hraw : highMean y S L (frameSum I j) ≤
      (I.card : ℝ) * (2 * (eulerProdNat y)⁻¹) := by
    change highMean y S L (fun U => ∑ i ∈ I,
      (subsetGap (deleted j U) i : ℝ)) ≤ _
    rw [highMean_sum]
    calc
      (∑ i ∈ I, highMean y S L (fun U => (subsetGap (deleted j U) i : ℝ))) ≤
          ∑ _i ∈ I, (2 : ℝ) * (eulerProdNat y)⁻¹ :=
        sum_le_sum fun i hi => deleted_gap_mean_le y S L j i hj0 hjL (hI i hi)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  calc
    highMean y S L (frameSum I j) / G ≤
        ((I.card : ℝ) * (2 * (eulerProdNat y)⁻¹)) / G :=
      div_le_div_of_nonneg_right hraw hG.le
    _ = (2 * (I.card : ℝ)) / (G * eulerProdNat y) := by
      field_simp [(eulerProdNat_pos y).ne', hG.ne']
      <;> ring

/-- Finite Markov under the original high-cardinality law. -/
theorem highMean_markov (y S L : ℕ) (f : Finset ℕ → ℝ)
    (hf : ∀ U, 0 ≤ f U) {A : ℝ} (hA : 0 < A) :
    highMean y S L (fun U => if A < f U then 1 else 0) ≤
      highMean y S L f / A := by
  rw [← highMean_div]
  apply highMean_mono
  intro U _
  by_cases h : A < f U
  · rw [if_pos h]
    exact (le_div_iff₀ hA).2 (by simpa using h.le)
  · rw [if_neg h]
    exact div_nonneg (hf U) hA.le

/-- Literal discarded mass outside the coordinate box `[0,A]^I`, measured
under the original rooted law before any insertion reweighting. -/
theorem original_bad_frame_mass_le (y S L j : ℕ) (I : Finset ℕ)
    (hj0 : 1 ≤ j) (hjL : j ≤ L) (hI : ∀ i ∈ I, i + 1 < L)
    {G A : ℝ} (hG : 0 < G) (hA : 0 < A) :
    highMean y S L (fun U =>
      if ∃ i ∈ I, A < (subsetGap (deleted j U) i : ℝ) / G then 1 else 0) ≤
      (2 * (I.card : ℝ)) / (A * G * eulerProdNat y) := by
  have hmono : highMean y S L (fun U =>
      if ∃ i ∈ I, A < (subsetGap (deleted j U) i : ℝ) / G then 1 else 0) ≤
      highMean y S L (fun U => if A < frameSum I j U / G then 1 else 0) := by
    apply highMean_mono
    intro U _
    by_cases h : ∃ i ∈ I, A < (subsetGap (deleted j U) i : ℝ) / G
    · obtain ⟨i, hi, hAi⟩ := h
      have hcoord : (subsetGap (deleted j U) i : ℝ) ≤ frameSum I j U :=
        single_le_sum (fun i _ => Nat.cast_nonneg (subsetGap (deleted j U) i)) hi
      have hsum : A < frameSum I j U / G :=
        hAi.trans_le (div_le_div_of_nonneg_right hcoord hG.le)
      have hbad : ∃ i ∈ I, A < (subsetGap (deleted j U) i : ℝ) / G :=
        ⟨i, hi, hAi⟩
      simp only [if_pos hbad, if_pos hsum]
      exact le_rfl
    · simp only [if_neg h]
      split_ifs <;> norm_num
  calc
    highMean y S L (fun U =>
        if ∃ i ∈ I, A < (subsetGap (deleted j U) i : ℝ) / G then 1 else 0) ≤
        highMean y S L (fun U => if A < frameSum I j U / G then 1 else 0) := hmono
    _ ≤ highMean y S L (fun U => frameSum I j U / G) / A :=
      highMean_markov y S L _ (fun U => div_nonneg (frameSum_nonneg I j U) hG.le) hA
    _ ≤ ((2 * (I.card : ℝ)) / (G * eulerProdNat y)) / A :=
      div_le_div_of_nonneg_right
        (normalized_frame_mean_le y S L j I hj0 hjL hI hG) hA.le
    _ = (2 * (I.card : ℝ)) / (A * G * eulerProdNat y) := by ring

end

end PrimeGapNormality.Prime.CoreOriginalDeletedFrame
