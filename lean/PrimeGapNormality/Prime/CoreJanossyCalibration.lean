import PrimeGapNormality.Prime.CorePrimeComparisonInput
import Mathlib.Data.Nat.Choose.Bounds

/-! A coarse finite calibration bound, used only for the power-saving
model/main-term calibration, never to weaken the actual arithmetic D input.
For S and r polylogarithmic, its combinatorial cost is X^{o(1)}. -/

open Finset

namespace PrimeGapNormality.Prime

theorem core_card_truncated_powerset_le (Ω : Finset ℕ) (r : ℕ) :
    (Ω.powerset.filter (fun H => H.card ≤ r)).card ≤
      (r + 1) * (Ω.card + 1) ^ r := by
  classical
  have heq : Ω.powerset.filter (fun H => H.card ≤ r) =
      (range (r + 1)).biUnion (fun j => Ω.powersetCard j) := by
    ext H
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · rintro ⟨hsub, hcard⟩
      exact ⟨H.card, by omega, hsub, rfl⟩
    · rintro ⟨j, hj, hsub, he⟩
      exact ⟨hsub, by omega⟩
  rw [heq]
  calc
    _ ≤ ∑ j ∈ range (r + 1), (Ω.powersetCard j).card := card_biUnion_le
    _ ≤ ∑ j ∈ range (r + 1), (Ω.card + 1) ^ r := by
      apply sum_le_sum
      intro j hj
      rw [card_powersetCard]
      have hjr : j ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hj)
      exact (Nat.choose_le_pow Ω.card j).trans
        ((pow_le_pow_left' (Nat.le_succ _) j).trans
          (pow_le_pow_right' (by omega : 1 ≤ Ω.card + 1) hjr))
    _ = (r + 1) * (Ω.card + 1) ^ r := by simp

theorem coreJanossyTransform_sub_le
    (Ω : Finset ℕ) {a b : Finset ℕ → ℝ} {L r : ℕ} {ε : ℝ}
    (hr : L ≤ r) (hε : 0 ≤ ε)
    (hab : ∀ H ⊆ Ω, H.card ≤ r → |a H - b H| ≤ ε)
    {K : Finset ℕ} (hKΩ : K ⊆ Ω) (hKL : K.card = L) :
    |coreJanossyTransform Ω a L r K - coreJanossyTransform Ω b L r K| ≤
      (((r + 1) * (Ω.card + 1) ^ r : ℕ) : ℝ) * ε := by
  classical
  unfold coreJanossyTransform
  split_ifs with hK
  · let T := (Stopped.beforeOutside Ω K hK).powerset.filter
      (fun D => D.card ≤ r - L)
    have hT : T ⊆ Ω.powerset.filter (fun D => D.card ≤ r) := by
      intro D hD
      have hd := mem_filter.mp hD
      exact mem_filter.mpr ⟨mem_powerset.mpr
        ((mem_powerset.mp hd.1).trans (filter_subset _ _)),
        hd.2.trans (Nat.sub_le _ _)⟩
    have hc : T.card ≤ (r + 1) * (Ω.card + 1) ^ r :=
      (card_le_card hT).trans (core_card_truncated_powerset_le Ω r)
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ D ∈ T, |(-1 : ℝ) ^ D.card * a (K ∪ D) -
          (-1 : ℝ) ^ D.card * b (K ∪ D)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ D ∈ T, ε := by
        apply sum_le_sum
        intro D hD
        have hd := mem_filter.mp hD
        have hDΩ : D ⊆ Ω := (mem_powerset.mp hd.1).trans (filter_subset _ _)
        have hcard : (K ∪ D).card ≤ r := by
          have hu := card_union_le K D
          rw [hKL] at hu
          omega
        simpa only [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
          one_mul] using hab (K ∪ D) (union_subset hKΩ hDΩ) hcard
      _ = (T.card : ℝ) * ε := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hε
  · simp only [sub_self, abs_zero]
    positivity

theorem coreJanossyTransform_sum_sub_le
    (Ω : Finset ℕ) {a b : Finset ℕ → ℝ} {L r : ℕ} {ε : ℝ}
    (hr : L ≤ r) (hε : 0 ≤ ε)
    (hab : ∀ H ⊆ Ω, H.card ≤ r → |a H - b H| ≤ ε) :
    (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
      |coreJanossyTransform Ω a L r K - coreJanossyTransform Ω b L r K|) ≤
        ((((r + 1) * (Ω.card + 1) ^ r : ℕ) : ℝ)) ^ 2 * ε := by
  classical
  let C := (r + 1) * (Ω.card + 1) ^ r
  have hc : (Ω.powerset.filter (fun K => K.card = L)).card ≤ C := by
    refine (card_le_card ?_).trans (core_card_truncated_powerset_le Ω r)
    intro K hK
    have hk := mem_filter.mp hK
    exact mem_filter.mpr ⟨hk.1, by simpa only [hk.2] using hr⟩
  calc
    _ ≤ ∑ K ∈ Ω.powerset.filter (fun K => K.card = L), (C : ℝ) * ε := by
      apply sum_le_sum
      intro K hK
      exact coreJanossyTransform_sub_le Ω hr hε hab
        (mem_powerset.mp (mem_filter.mp hK).1) (mem_filter.mp hK).2
    _ = ((Ω.powerset.filter (fun K => K.card = L)).card : ℝ) * ((C : ℝ) * ε) :=
      by simp
    _ ≤ (C : ℝ) * ((C : ℝ) * ε) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (mul_nonneg (Nat.cast_nonneg _) hε)
    _ = _ := by dsimp [C]; ring

end PrimeGapNormality.Prime
