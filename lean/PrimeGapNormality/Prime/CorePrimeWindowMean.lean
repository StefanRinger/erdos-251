import PrimeGapNormality.Prime.CorePrimeFirstL
import PrimeGapNormality.Prime.SubsetSpacing

/-! Exact physical-to-index pushforward of the stopped prime-pattern law.
This is finite algebra/enumeration, with no density or PNT hypothesis. -/

open Finset

namespace PrimeGapNormality.Prime

theorem corePrimePrefix_sort (n L : ℕ) :
    (corePrimePrefix n L).sort (· ≤ ·) = (List.range L).map (corePrimeOffset n) := by
  let e : ℕ ↪ ℕ := ⟨corePrimeOffset n, (corePrimeOffset_strictMono n).injective⟩
  have h := Finset.map_sort e (range L) (· ≤ ·) (· ≤ ·)
    (fun i _ j _ => (corePrimeOffset_strictMono n).le_iff_le.symm)
  rw [sort_range, map_eq_image] at h
  exact h.symm

theorem corePrimePrefix_orderStat (n L j : ℕ) (hj : j ≤ L) :
    orderStat (corePrimePrefix n L) j = nthPrime (n + j) - nthPrime n := by
  by_cases hz : j = 0
  · subst j
    simp [orderStat_zero]
  · have hp : 0 < j := Nat.pos_of_ne_zero hz
    have hc : j ≤ (corePrimePrefix n L).card := by rwa [corePrimePrefix_card]
    rw [orderStat_pos_eq_sort hp hc]
    simp only [corePrimePrefix_sort, List.getElem_map, List.getElem_range, corePrimeOffset]
    congr 2
    omega

theorem corePrimePrefix_gap (n L j : ℕ) (hj : j < L) :
    subsetGap (corePrimePrefix n L) j = primeGap (n + j) := by
  unfold subsetGap primeGap
  rw [corePrimePrefix_orderStat n L (j + 1) (by omega),
    corePrimePrefix_orderStat n L j hj.le]
  have h0 := nthPrime_mono (show n ≤ n + j by omega)
  have h1 := nthPrime_mono (show n + j ≤ n + (j + 1) by omega)
  have heq : n + (j + 1) = n + j + 1 := by omega
  rw [heq] at *
  omega

theorem corePrimeRoots_eq_image_index (X : ℕ) :
    corePrimeRoots X =
      (Ico (Nat.primeCounting X) (Nat.primeCounting (2 * X))).image nthPrime := by
  classical
  ext p
  constructor
  · intro hp
    have hp' := mem_filter.mp hp
    obtain ⟨n, _, hn⟩ := Nat.exists_lt_card_nth_eq hp'.2
    change nthPrime n = p at hn
    exact mem_image.mpr ⟨n, mem_dyadic_prime_index_iff.mpr (by
      rw [hn]; exact mem_Ioc.mp hp'.1), hn⟩
  · intro hp
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr (mem_dyadic_prime_index_iff.mp hn), prime_nthPrime n⟩

theorem corePrimeRoots_sum {E : Type*} [AddCommMonoid E] (X : ℕ) (f : ℕ → E) :
    (∑ p ∈ corePrimeRoots X, f p) =
      ∑ n ∈ Ico (Nat.primeCounting X) (Nat.primeCounting (2 * X)), f (nthPrime n) := by
  classical
  rw [corePrimeRoots_eq_image_index, sum_image]
  intro n _ m _ h
  exact nthPrime_strictMono.injective h

theorem coreStopped_positive_test_eq_pushforward
    (Ω : Finset ℕ) (μ : Finset ℕ → ℝ) (L : ℕ) (f : Finset ℕ → ℝ) :
    (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
      f K * Stopped.shortShapeMass Ω μ L K) =
    ∑ U ∈ Ω.powerset, μ U *
      if L ≤ U.card then f (Stopped.firstL L U) else 0 := by
  classical
  unfold Stopped.shortShapeMass
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro U hU
  by_cases hL : L ≤ U.card
  · have hmem : Stopped.firstL L U ∈ Ω.powerset.filter (fun K => K.card = L) :=
      mem_filter.mpr ⟨mem_powerset.mpr
        (Stopped.firstL_subset.trans (mem_powerset.mp hU)), Stopped.firstL_card hL⟩
    simp only [hL, true_and, if_true, mul_ite, mul_zero]
    rw [sum_ite_eq, if_pos hmem, mul_comm]
  · simp [hL]

theorem coreActual_firstL_test_eq_index_average
    (X S : ℕ) {L : ℕ} (hL : 1 ≤ L) (f : Finset ℕ → ℝ) :
    (∑ K ∈ (Icc 1 S).powerset.filter (fun K => K.card = L),
      f K * Stopped.shortShapeMass (Icc 1 S) (coreActualPatternMass X (Icc 1 S)) L K) =
    (∑ n ∈ Ico (Nat.primeCounting X) (Nat.primeCounting (2 * X)),
      if nthPrime (n + L) - nthPrime n ≤ S then f (corePrimePrefix n L) else 0) /
        (windowNX X : ℝ) := by
  classical
  rw [coreStopped_positive_test_eq_pushforward, coreActualPatternMass_eval,
    corePrimeRoots_sum]
  congr 1
  apply sum_congr rfl
  intro n _
  by_cases hspan : nthPrime (n + L) - nthPrime n ≤ S
  · rw [if_pos ((coreActualPattern_card_ge_iff_span hL).mpr hspan), if_pos hspan,
      coreActualPattern_firstL_eq_prefix hL hspan]
  · have hnot : ¬L ≤ (coreActualPattern (Icc 1 S) (nthPrime n)).card :=
      fun h => hspan ((coreActualPattern_card_ge_iff_span hL).mp h)
    rw [if_neg hnot, if_neg hspan]

end PrimeGapNormality.Prime
