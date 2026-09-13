import PrimeGapNormality.Prime.CoreAuxiliaryRectangleBound

/-!
# Rectangle deletion with the falling factorial retained

The coarser bound by a power of the one-step ratio is sufficient for
absolute continuity. The paper's explicit density bound also needs to
average original survivor counts before discarding their factorial
structure. This finite lemma retains that structure. Its denominator
floor may be arbitrarily close to the original candidate count.

Source pending central compilation. No model or arithmetic assertion is
an input to these finite identities/inequalities.
-/

namespace PrimeGapNormality.Prime.CoreAuxiliaryFactorialRectangle

open Finset
open scoped Classical
noncomputable section

private theorem choose_pos {M m : ℕ} (hm : m ≤ M) :
    (0 : ℝ) < M.choose m := Nat.cast_pos.mpr (Nat.choose_pos hm)

/-- Retain `(m)_r`, rather than replacing each factor by `m`. -/
theorem choose_sub_ratio_le_descFactorial
    (M m r : ℕ) (hm : m ≤ M) (hr : r ≤ m)
    {R : ℝ} (hR : 0 < R) (hden : R ≤ (M : ℝ) - m + 1) :
    (M.choose (m - r) : ℝ) / (M.choose m : ℝ) ≤
      (m.descFactorial r : ℝ) / R ^ r := by
  induction r with
  | zero => simp [(choose_pos hm).ne']
  | succ r ih =>
      have hr' : r ≤ m := (Nat.le_succ r).trans hr
      have hn : 1 ≤ m - r := by omega
      have hnM : m - r ≤ M := (Nat.sub_le m r).trans hm
      have hnr : ((m - r : ℕ) : ℝ) ≤ m := Nat.cast_le.mpr (Nat.sub_le m r)
      have hd : R ≤ (M : ℝ) - (m - r : ℕ) + 1 := by linarith
      have hstep := auxFrame_choose_ratio hn hnM
      have hstepLe :
          (M.choose ((m - r) - 1) : ℝ) / (M.choose (m - r) : ℝ) ≤
            ((m - r : ℕ) : ℝ) / R := by
        rw [hstep]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hR hd
      have hfactor :
          (M.choose (m - (r + 1)) : ℝ) / (M.choose m : ℝ) =
            ((M.choose ((m - r) - 1) : ℝ) / (M.choose (m - r) : ℝ)) *
              ((M.choose (m - r) : ℝ) / (M.choose m : ℝ)) := by
        rw [show m - (r + 1) = (m - r) - 1 by omega]
        field_simp [(choose_pos hm).ne', (choose_pos hnM).ne']
      calc
        _ = ((M.choose ((m - r) - 1) : ℝ) / (M.choose (m - r) : ℝ)) *
              ((M.choose (m - r) : ℝ) / (M.choose m : ℝ)) := hfactor
        _ ≤ (((m - r : ℕ) : ℝ) / R) * ((m.descFactorial r : ℝ) / R ^ r) :=
          mul_le_mul hstepLe (ih hr')
            (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (div_nonneg (Nat.cast_nonneg _) hR.le)
        _ = (m.descFactorial (r + 1) : ℝ) / R ^ (r + 1) := by
          rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
          ring

/-- The exact uniform-subset rectangle estimate with a freely chosen
denominator floor, ready to be averaged over survivor-count layers. -/
theorem uniformMean_rectangle_le_descFactorial
    (A : Finset ℕ) (m : ℕ) (J : Finset ℕ)
    (I : ℕ → Set ℝ) (K : ℕ → ℕ)
    (hm : m ≤ A.card) (hJ : ∀ j ∈ J, j < m)
    (hcap : ∀ j ∈ J, ∀ a : ℝ,
      (CoreUniformGapRectangles.translatedCandidates A (I j) a).card ≤ K j)
    {R : ℝ} (hR : 0 < R) (hden : R ≤ (A.card : ℝ) - m + 1) :
    auxFrame_uniformMean A m
        (fun U => if ∀ j ∈ J, (subsetGap U j : ℝ) ∈ I j then 1 else 0) ≤
      ((m.descFactorial J.card : ℝ) / R ^ J.card) *
        ∏ j ∈ J, (K j : ℝ) := by
  have hsub : J ⊆ range m := fun j hj => mem_range.mpr (hJ j hj)
  have hcard : J.card ≤ m := by
    simpa only [card_range] using card_le_card hsub
  have hr := CoreUniformGapRectangles.uniformMean_rectangle_indicator_le A m J I K hm hJ hcap
  exact hr.trans (mul_le_mul_of_nonneg_right
    (choose_sub_ratio_le_descFactorial A.card m J.card hm hcard hR hden)
    (prod_nonneg fun j _ => Nat.cast_nonneg _))

/-- A small survivor-density cutoff gives a denominator factor arbitrarily
close to one. No bound of the form N≤constant*M*theta is needed here. -/
theorem denominator_floor_of_sparse_layer
    {M m : ℕ} {ε : ℝ} (hε : ε < 1) (hM : 0 < M)
    (hm : (m : ℝ) ≤ ε * (M : ℝ)) :
    0 < (1 - ε) * (M : ℝ) ∧
      (1 - ε) * (M : ℝ) ≤ (M : ℝ) - m + 1 := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  refine ⟨mul_pos (sub_pos.mpr hε) hMr, ?_⟩
  nlinarith

end
end PrimeGapNormality.Prime.CoreAuxiliaryFactorialRectangle
