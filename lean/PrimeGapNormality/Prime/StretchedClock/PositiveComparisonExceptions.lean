import PrimeGapNormality.Prime.StretchedClock.ClockBounds

/-! Explicit finite exceptional anchors for the stretched-clock prefix. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset
noncomputable section
set_option maxHeartbeats 800000

def clockChanges (B N : ℕ) : Finset ℕ :=
  (Ico (Nat.sqrt N) N).filter fun n => step B n < step B (n + 1)

def clockBadAnchors (B N H : ℕ) : Finset ℕ :=
  (Ico (Nat.sqrt N) N).filter fun n =>
    N < n + H ∨ ∃ t ∈ clockChanges B N, n ≤ t ∧ t < n + H

def prefixBadAnchors (B N H : ℕ) : Finset ℕ :=
  range (Nat.sqrt N) ∪ clockBadAnchors B N H

theorem clockChanges_card_le_one {B : ℕ} (hB : 2 ≤ B) (N : ℕ) :
    (clockChanges B N).card ≤ 1 := by
  apply card_le_one.mpr
  intro m hm n hn
  obtain ⟨hmI, hmc⟩ := mem_filter.mp hm
  obtain ⟨hnI, hnc⟩ := mem_filter.mp hn
  exact clock_changes_subsingleton hB
    ⟨(mem_Ico.mp hmI).1, (mem_Ico.mp hmI).2, hmc⟩
    ⟨(mem_Ico.mp hnI).1, (mem_Ico.mp hnI).2, hnc⟩

/-- At most H anchors precede the unique possible jump and at most H
more meet the right edge. This is a proved finite count, not a supplier premise. -/
theorem clockBadAnchors_card_le {B : ℕ} (hB : 2 ≤ B) (N H : ℕ) :
    (clockBadAnchors B N H).card ≤ 2 * H := by
  obtain ⟨t, ht⟩ := card_le_one_iff_subset_singleton.mp (clockChanges_card_le_one hB N)
  have hsub : clockBadAnchors B N H ⊆
      Ico (N - H) N ∪ Ico (t + 1 - H) (t + 1) := by
    intro n hn
    obtain ⟨hnI, hbad⟩ := mem_filter.mp hn
    have hnN := (mem_Ico.mp hnI).2
    rcases hbad with hend | ⟨s, hs, hns, hsn⟩
    · exact mem_union_left _ (mem_Ico.mpr ⟨by omega, hnN⟩)
    · have hst : s = t := mem_singleton.mp (ht hs)
      subst s
      exact mem_union_right _ (mem_Ico.mpr ⟨by omega, by omega⟩)
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  rw [Nat.card_Ico, Nat.card_Ico] at hcard
  omega

theorem prefixBadAnchors_subset (B N H : ℕ) :
    prefixBadAnchors B N H ⊆ range N := by
  intro n hn
  rcases mem_union.mp hn with hfirst | hbad
  · exact mem_range.mpr ((mem_range.mp hfirst).trans_le (Nat.sqrt_le_self N))
  · exact mem_range.mpr (mem_Ico.mp (mem_filter.mp hbad).1).2

theorem good_anchor_data {B N H n : ℕ} (hB : 2 ≤ B)
    (hn : n ∈ range N) (hgood : n ∉ prefixBadAnchors B N H) :
    Nat.sqrt N ≤ n ∧ n + H ≤ N ∧ ∀ i < H, step B (n + i) = step B n := by
  have hnN : n < N := mem_range.mp hn
  have hnlo : Nat.sqrt N ≤ n := by
    by_contra hh
    exact hgood (mem_union_left _ (mem_range.mpr (by omega)))
  have hbad : n ∉ clockBadAnchors B N H :=
    fun hh => hgood (mem_union_right _ hh)
  have hnI : n ∈ Ico (Nat.sqrt N) N := mem_Ico.mpr ⟨hnlo, hnN⟩
  have hend : n + H ≤ N := by
    by_contra hh
    exact hbad (mem_filter.mpr ⟨hnI, Or.inl (by omega)⟩)
  refine ⟨hnlo, hend, ?_⟩
  intro i
  induction i with
  | zero => intro hi; simp
  | succ i ih =>
    intro hi
    have hiH : i < H := by omega
    have hprev := ih hiH
    have heq : step B (n + i) = step B (n + i + 1) := by
      have hle := step_mono hB (Nat.le_succ (n + i))
      by_contra hh
      have hlt : step B (n + i) < step B (n + i + 1) := lt_of_le_of_ne hle hh
      have hchange : n + i ∈ clockChanges B N := by
        exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hlt⟩
      exact hbad (mem_filter.mpr ⟨hnI, Or.inr ⟨n + i, hchange, by omega, by omega⟩⟩)
    simpa only [Nat.add_assoc] using heq.symm.trans hprev

/-- Exceptional digit weight, including the exact initial prefix. -/
theorem prefixBadAnchors_weight_le {B : ℕ} (hB : 2 ≤ B) (N H : ℕ) :
    (∑ n ∈ prefixBadAnchors B N H, step B n) ≤
      position B (Nat.sqrt N) + 2 * H * step B N := by
  have hdis : Disjoint (range (Nat.sqrt N)) (clockBadAnchors B N H) := by
    apply disjoint_left.mpr
    intro n hn hb
    have hlt := mem_range.mp hn
    have hge := (mem_Ico.mp (mem_filter.mp hb).1).1
    omega
  have htail : (∑ n ∈ clockBadAnchors B N H, step B n) ≤
      (clockBadAnchors B N H).card * step B N := by
    calc
      _ ≤ ∑ n ∈ clockBadAnchors B N H, step B N := by
        exact sum_le_sum fun n hn => step_mono hB
          (Nat.le_of_lt (mem_Ico.mp (mem_filter.mp hn).1).2)
      _ = _ := by simp
  have htail' := htail.trans (Nat.mul_le_mul_right (step B N) (clockBadAnchors_card_le hB N H))
  unfold prefixBadAnchors
  rw [sum_union hdis]
  exact Nat.add_le_add le_rfl htail'

end
end PrimeGapNormality.Prime.StretchedClock
