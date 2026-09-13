import PrimeGapNormality.Prime.AuxThetaBound
import PrimeGapNormality.Prime.CoreUniformGapRectangles

/-!
# Good-count auxiliary rectangle bound

Iterating the exact adjacent-binomial quotient controls the loss of any
fixed number of points from a uniform exact-cardinality layer.  Combined
with the proved rectangle count, this gives the paper's fixed-dimensional
rectangle bound on every good-count layer.  No new factorial-moment input
is used.
-/

namespace PrimeGapNormality.Prime.CoreAuxiliaryRectangleBound

open Finset
open scoped BigOperators Classical

noncomputable section

private theorem choose_cast_pos {M n : ℕ} (hn : n ≤ M) :
    (0 : ℝ) < M.choose n :=
  Nat.cast_pos.mpr (Nat.choose_pos hn)

private theorem adjacent_ratio_mono {M m r : ℕ}
    (hmM : m ≤ M) (hrm : r ≤ m) :
    ((m - r : ℕ) : ℝ) /
        ((M : ℝ) - (m - r : ℕ) + 1) ≤
      (m : ℝ) / ((M : ℝ) - m + 1) := by
  have hmr : m - r ≤ m := Nat.sub_le _ _
  have hnrM : m - r ≤ M := hmr.trans hmM
  have hdenLeft : 0 < (M : ℝ) - (m - r : ℕ) + 1 := by
    rw [← auxFrame_cast_sub hnrM]
    exact_mod_cast Nat.succ_pos (M - (m - r))
  have hdenRight : 0 < (M : ℝ) - m + 1 := by
    rw [← auxFrame_cast_sub hmM]
    exact_mod_cast Nat.succ_pos (M - m)
  apply (div_le_div_iff₀ hdenLeft hdenRight).2
  have hcast : ((m - r : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmr
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hprod : 0 ≤ ((m : ℝ) - (m - r : ℕ)) * ((M : ℝ) + 1) :=
    mul_nonneg (sub_nonneg.mpr hcast) (by linarith)
  nlinarith

/-- Iterated exact choose quotient. -/
theorem choose_sub_ratio_le_pow (M m r : ℕ) (hmM : m ≤ M) (hrm : r ≤ m) :
    (M.choose (m - r) : ℝ) / (M.choose m : ℝ) ≤
      ((m : ℝ) / ((M : ℝ) - m + 1)) ^ r := by
  induction r with
  | zero => simp [(choose_cast_pos hmM).ne']
  | succ r ih =>
      have hrm' : r ≤ m := (Nat.le_succ r).trans hrm
      have hn : 1 ≤ m - r := by omega
      have hnm : m - r ≤ M := (Nat.sub_le m r).trans hmM
      have hsub : m - (r + 1) = (m - r) - 1 := by omega
      have hfactor :
          (M.choose (m - (r + 1)) : ℝ) / (M.choose m : ℝ) =
            ((M.choose ((m - r) - 1) : ℝ) / (M.choose (m - r) : ℝ)) *
              ((M.choose (m - r) : ℝ) / (M.choose m : ℝ)) := by
        rw [hsub]
        field_simp [(choose_cast_pos hnm).ne', (choose_cast_pos hmM).ne']
      have hstep := auxFrame_choose_ratio hn hnm
      have hstepLe :
          (M.choose ((m - r) - 1) : ℝ) / (M.choose (m - r) : ℝ) ≤
            (m : ℝ) / ((M : ℝ) - m + 1) := by
        rw [hstep]
        exact adjacent_ratio_mono hmM hrm'
      have hq0 : 0 ≤ (m : ℝ) / ((M : ℝ) - m + 1) := by
        apply div_nonneg (Nat.cast_nonneg _)
        rw [← auxFrame_cast_sub hmM]
        exact Nat.cast_nonneg _
      have hprev0 : 0 ≤
          (M.choose (m - r) : ℝ) / (M.choose m : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      calc
        (M.choose (m - (r + 1)) : ℝ) / (M.choose m : ℝ) =
            ((M.choose ((m - r) - 1) : ℝ) / (M.choose (m - r) : ℝ)) *
              ((M.choose (m - r) : ℝ) / (M.choose m : ℝ)) := hfactor
        _ ≤ ((m : ℝ) / ((M : ℝ) - m + 1)) *
              (((m : ℝ) / ((M : ℝ) - m + 1)) ^ r) :=
          mul_le_mul hstepLe (ih hrm') hprev0 hq0
        _ = ((m : ℝ) / ((M : ℝ) - m + 1)) ^ (r + 1) := by
          rw [pow_succ]
          ring

/-- Insert any available upper bound for the one-step quotient. -/
theorem choose_sub_ratio_le_bound_pow
    (M m r : ℕ) (hmM : m ≤ M) (hrm : r ≤ m)
    {q : ℝ} (hq0 : 0 ≤ q)
    (hq : (m : ℝ) / ((M : ℝ) - m + 1) ≤ q) :
    (M.choose (m - r) : ℝ) / (M.choose m : ℝ) ≤ q ^ r := by
  exact (choose_sub_ratio_le_pow M m r hmM hrm).trans
    (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (by
      rw [← auxFrame_cast_sub hmM]
      exact Nat.cast_nonneg _)) hq r)

/-- Fixed-dimensional rectangle probability on a good exact-cardinality
layer. -/
theorem uniformMean_rectangle_indicator_le_fourTheta
    (A : Finset ℕ) (m : ℕ) (J : Finset ℕ)
    (I : ℕ → Set ℝ) (K : ℕ → ℕ) {θ : ℝ}
    (hm : m ≤ A.card) (hr : J.card ≤ m)
    (hJ : ∀ j ∈ J, j < m)
    (hcap : ∀ j ∈ J, ∀ a : ℝ,
      (CoreUniformGapRectangles.translatedCandidates A (I j) a).card ≤ K j)
    (hcount : (m : ℝ) ≤ 2 * (A.card : ℝ) * θ)
    (hθ : 0 < θ) (hθ4 : θ ≤ (1 : ℝ) / 4) :
    auxFrame_uniformMean A m
        (fun U ↦ if ∀ j ∈ J, (subsetGap U j : ℝ) ∈ I j then 1 else 0) ≤
      ((4 : ℝ) * θ) ^ J.card * ∏ j ∈ J, (K j : ℝ) := by
  have hrect := CoreUniformGapRectangles.uniformMean_rectangle_indicator_le
    A m J I K hm hJ hcap
  have hratio :
      (A.card.choose (m - J.card) : ℝ) / (A.card.choose m : ℝ) ≤
        ((4 : ℝ) * θ) ^ J.card := by
    apply choose_sub_ratio_le_bound_pow A.card m J.card hm hr
    · exact mul_nonneg (by norm_num) hθ.le
    · by_cases hm0 : m = 0
      · subst m
        simp [hθ.le]
      · apply auxTheta_ratio_le_four_theta
        · exact_mod_cast Nat.pos_of_ne_zero hm0
        · exact_mod_cast hm
        · exact hcount
        · exact hθ
        · exact hθ4
  have hprod0 : 0 ≤ ∏ j ∈ J, (K j : ℝ) :=
    prod_nonneg fun j _ ↦ Nat.cast_nonneg _
  exact hrect.trans (mul_le_mul_of_nonneg_right hratio hprod0)

end

end PrimeGapNormality.Prime.CoreAuxiliaryRectangleBound
