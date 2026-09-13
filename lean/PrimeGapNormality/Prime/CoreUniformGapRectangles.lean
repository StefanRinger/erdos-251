import PrimeGapNormality.Prime.AuxFrameDelete
import PrimeGapNormality.Prime.UniformAuxFrame
import Mathlib.Data.Finset.Max

/-!
The frozen paper's finite rectangle-count kernel for uniform subsets.
Delete selected right endpoints in decreasing rank order. Every earlier
selected gap is unchanged, so reconstruction runs in increasing rank order
and adjacent selected ranks require no separation assumption.
-/

namespace PrimeGapNormality.Prime.CoreUniformGapRectangles

open Finset
open scoped BigOperators Classical

noncomputable section

/-- Actual exact-cardinality configurations satisfying the selected gaps.
Real sets allow the later normalized interval specialization directly. -/
def goodSubsets (A : Finset ℕ) (m : ℕ) (J : Finset ℕ)
    (I : ℕ → Set ℝ) : Finset (Finset ℕ) := by
  classical
  exact (A.powersetCard m).filter fun U ↦ ∀ j ∈ J, (subsetGap U j : ℝ) ∈ I j

@[simp] theorem mem_goodSubsets {A U : Finset ℕ} {m : ℕ} {J : Finset ℕ}
    {I : ℕ → Set ℝ} :
    U ∈ goodSubsets A m J I ↔
      U ⊆ A ∧ U.card = m ∧ ∀ j ∈ J, (subsetGap U j : ℝ) ∈ I j := by
  classical
  simp only [goodSubsets, mem_filter, mem_powersetCard, and_assoc]

/-- Removing the right endpoint of gap `j` leaves every order statistic
through rank `j` unchanged. This includes the rooted statistic at zero and
deletion of the last actual point. -/
theorem orderStat_erase_right_eq {U : Finset ℕ} {j i : ℕ}
    (hj : j < U.card) (hi : i ≤ j) :
    orderStat (U.erase (orderStat U (j + 1))) i = orderStat U i := by
  by_cases hi0 : i = 0
  · subst i
    simp only [orderStat_zero]
  have hipos : 0 < i := Nat.pos_of_ne_zero hi0
  have hiU : i ≤ U.card := by omega
  have hiF : i ≤ (U.erase (orderStat U (j + 1))).card := by
    rw [auxDel_erase_card hj]
    omega
  rw [orderStat_pos_eq_sort hipos hiF, orderStat_pos_eq_sort hipos hiU]
  simp only [auxDel_sort_erase hj]
  exact List.getElem_eraseIdx_of_lt _ (by omega : i - 1 < j)

theorem subsetGap_erase_later_eq {U : Finset ℕ} {j i : ℕ}
    (hj : j < U.card) (hi : i < j) :
    subsetGap (U.erase (orderStat U (j + 1))) i = subsetGap U i := by
  unfold subsetGap
  rw [orderStat_erase_right_eq hj (by omega : i + 1 ≤ j),
    orderStat_erase_right_eq hj hi.le]

/-- The literal candidates in a translate of the gap constraint. No
artificial terminal point or slot-cardinality normalization is used. -/
def translatedCandidates (A : Finset ℕ) (I : Set ℝ) (a : ℝ) : Finset ℕ := by
  classical
  exact A.filter fun u ↦ (u : ℝ) - a ∈ I

@[simp] theorem mem_translatedCandidates {A : Finset ℕ} {I : Set ℝ} {a : ℝ} {u : ℕ} :
    u ∈ translatedCandidates A I a ↔ u ∈ A ∧ (u : ℝ) - a ∈ I := by
  classical
  simp only [translatedCandidates, mem_filter]

/-- One genuine deletion step, counted by an injective encoding into the
reduced frame and its candidate endpoint. -/
theorem card_goodSubsets_insert_le (A : Finset ℕ) (m j : ℕ) (J : Finset ℕ)
    (I : ℕ → Set ℝ) (K : ℕ) (hj : j < m)
    (hJ : ∀ i ∈ J, i < j)
    (hcap : ∀ a : ℝ, (translatedCandidates A (I j) a).card ≤ K) :
    (goodSubsets A m (insert j J) I).card ≤
      (goodSubsets A (m - 1) J I).card * K := by
  classical
  let encode : Finset ℕ → (Σ _F : Finset ℕ, ℕ) := fun U ↦
    ⟨U.erase (orderStat U (j + 1)), orderStat U (j + 1)⟩
  let target : Finset (Σ _F : Finset ℕ, ℕ) :=
    (goodSubsets A (m - 1) J I).sigma fun F ↦
      translatedCandidates A (I j) (orderStat F j : ℝ)
  have hmaps : Set.MapsTo encode (goodSubsets A m (insert j J) I) target := by
    intro U hU
    obtain ⟨hUA, hUm, hUI⟩ := mem_goodSubsets.1 hU
    have hjU : j < U.card := by omega
    have huU : orderStat U (j + 1) ∈ U :=
      auxDel_orderStat_mem (Nat.succ_pos j) (Nat.succ_le_of_lt hjU)
    apply mem_sigma.2
    constructor
    · apply mem_goodSubsets.2
      refine ⟨(erase_subset _ _).trans hUA, ?_, ?_⟩
      · rw [auxDel_erase_card hjU, hUm]
      · intro i hi
        rw [subsetGap_erase_later_eq hjU (hJ i hi)]
        exact hUI i (mem_insert_of_mem hi)
    · apply mem_translatedCandidates.2
      refine ⟨hUA huU, ?_⟩
      change (orderStat U (j + 1) : ℝ) -
        (orderStat (U.erase (orderStat U (j + 1))) j : ℝ) ∈ I j
      have hgap := hUI j (mem_insert_self j J)
      rw [orderStat_erase_right_eq hjU le_rfl]
      simpa only [subsetGap, Nat.cast_sub (auxDel_orderStat_le_succ hjU)] using hgap
  have hinj : Set.InjOn encode (goodSubsets A m (insert j J) I) := by
    intro U hU V hV hUV
    have hUm := (mem_goodSubsets.1 hU).2.1
    have hVm := (mem_goodSubsets.1 hV).2.1
    have huU : orderStat U (j + 1) ∈ U :=
      auxDel_orderStat_mem (Nat.succ_pos j) (by omega)
    have hvV : orderStat V (j + 1) ∈ V :=
      auxDel_orderStat_mem (Nat.succ_pos j) (by omega)
    have hframes : U.erase (orderStat U (j + 1)) = V.erase (orderStat V (j + 1)) :=
      congrArg Sigma.fst hUV
    have hpoints : orderStat U (j + 1) = orderStat V (j + 1) :=
      congrArg (fun p : (Σ _F : Finset ℕ, ℕ) ↦ p.2) hUV
    calc
      U = insert (orderStat U (j + 1)) (U.erase (orderStat U (j + 1))) :=
        (insert_erase huU).symm
      _ = insert (orderStat V (j + 1)) (V.erase (orderStat V (j + 1))) := by
        rw [hframes, hpoints]
      _ = V := insert_erase hvV
  calc
    (goodSubsets A m (insert j J) I).card ≤ target.card :=
      card_le_card_of_injOn encode hmaps hinj
    _ = ∑ F ∈ goodSubsets A (m - 1) J I,
        (translatedCandidates A (I j) (orderStat F j : ℝ)).card := card_sigma _ _
    _ ≤ ∑ _F ∈ goodSubsets A (m - 1) J I, K :=
      sum_le_sum fun F _ ↦ hcap (orderStat F j)
    _ = (goodSubsets A (m - 1) J I).card * K := by simp

/-- The paper's finite rectangle count, for distinct valid actual gap
ranks. The raw count holds even if the exact-cardinality layer is empty. -/
theorem card_goodSubsets_le (A : Finset ℕ) (I : ℕ → Set ℝ) (K : ℕ → ℕ)
    (J : Finset ℕ) : ∀ m : ℕ,
    (∀ j ∈ J, j < m) →
    (∀ j ∈ J, ∀ a : ℝ, (translatedCandidates A (I j) a).card ≤ K j) →
    (goodSubsets A m J I).card ≤ A.card.choose (m - J.card) * ∏ j ∈ J, K j := by
  classical
  induction J using Finset.induction_on_max with
  | empty =>
    intro m _ _
    simp [goodSubsets]
  | insert j J hmax ih =>
    intro m hm hcap
    have hj : j < m := hm j (mem_insert_self j J)
    have hjnot : j ∉ J := fun hjJ ↦ (hmax j hjJ).false
    have hJsmall : ∀ i ∈ J, i < m - 1 := by
      intro i hi
      have := hmax i hi
      omega
    have hcapJ : ∀ i ∈ J, ∀ a : ℝ,
        (translatedCandidates A (I i) a).card ≤ K i :=
      fun i hi ↦ hcap i (mem_insert_of_mem hi)
    calc
      (goodSubsets A m (insert j J) I).card ≤
          (goodSubsets A (m - 1) J I).card * K j :=
        card_goodSubsets_insert_le A m j J I (K j) hj hmax
          (hcap j (mem_insert_self j J))
      _ ≤ (A.card.choose (m - 1 - J.card) * ∏ i ∈ J, K i) * K j :=
        Nat.mul_le_mul_right (K j) (ih (m - 1) hJsmall hcapJ)
      _ = A.card.choose (m - (insert j J).card) * ∏ i ∈ insert j J, K i := by
        rw [card_insert_of_notMem hjnot, prod_insert hjnot]
        have hsub : m - 1 - J.card = m - (J.card + 1) := by omega
        rw [hsub]
        ac_rfl

/-- Uniform rectangle probability, with a positive binomial denominator.
This is only the finite combinatorial kernel, not a limiting AC claim. -/
theorem uniform_rectangle_probability_le (A : Finset ℕ) (m : ℕ)
    (J : Finset ℕ) (I : ℕ → Set ℝ) (K : ℕ → ℕ)
    (hm : m ≤ A.card) (hJ : ∀ j ∈ J, j < m)
    (hcap : ∀ j ∈ J, ∀ a : ℝ, (translatedCandidates A (I j) a).card ≤ K j) :
    ((goodSubsets A m J I).card : ℝ) / (A.card.choose m : ℝ) ≤
      ((A.card.choose (m - J.card) : ℝ) / (A.card.choose m : ℝ)) *
        ∏ j ∈ J, (K j : ℝ) := by
  have hden : (0 : ℝ) < A.card.choose m := Nat.cast_pos.2 (Nat.choose_pos hm)
  have hc : ((goodSubsets A m J I).card : ℝ) ≤
      (A.card.choose (m - J.card) : ℝ) * ∏ j ∈ J, (K j : ℝ) := by
    exact_mod_cast card_goodSubsets_le A I K J m hJ hcap
  calc
    ((goodSubsets A m J I).card : ℝ) / (A.card.choose m : ℝ) ≤
        ((A.card.choose (m - J.card) : ℝ) * ∏ j ∈ J, (K j : ℝ)) /
          (A.card.choose m : ℝ) := div_le_div_of_nonneg_right hc hden.le
    _ = _ := by ring

/-- The same finite bound as the actual uniform mean of the rectangle
indicator, ready for averaging against cardinality-layer masses. -/
theorem uniformMean_rectangle_indicator_le (A : Finset ℕ) (m : ℕ)
    (J : Finset ℕ) (I : ℕ → Set ℝ) (K : ℕ → ℕ)
    (hm : m ≤ A.card) (hJ : ∀ j ∈ J, j < m)
    (hcap : ∀ j ∈ J, ∀ a : ℝ, (translatedCandidates A (I j) a).card ≤ K j) :
    auxFrame_uniformMean A m
      (fun U ↦ if ∀ j ∈ J, (subsetGap U j : ℝ) ∈ I j then 1 else 0) ≤
      ((A.card.choose (m - J.card) : ℝ) / (A.card.choose m : ℝ)) *
        ∏ j ∈ J, (K j : ℝ) := by
  simpa only [auxFrame_uniformMean, Finset.sum_boole, goodSubsets] using
    uniform_rectangle_probability_le A m J I K hm hJ hcap

end

end PrimeGapNormality.Prime.CoreUniformGapRectangles
