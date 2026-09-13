import PrimeGapNormality.Prime.Fourier
import PrimeGapNormality.Prime.RankDelete
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic presieve grid comparison (paper `lem:gridcompare`)

Finite comparison of relative cell counts on a single G-grid of width
`h = ⌊G⌋` (or `h = ⌊δ G⌋`) against a continuous slot length. Occupancy
of a complete frame in the geometric slot `(a,c)` is compared with
`v * (c-a)`. Cellwise Riemann replacement (phase frozen at the left
endpoint) is the discrete step used by resampling; the oscillatory
integral bound itself lives in `Oscillatory` / `Fourier`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex`
subsection "Complete frames and the deterministic grid comparison",
`lem:gridcompare`; relative counts (eq:relativegrid), (eq:gridspan).
Contract: API
Audit: GREEN
-/

open Finset

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000

/-! ### Grid width `h = ⌊G⌋` and aligned span -/

/-- Paper cell width `h = ⌊G⌋` on the presieve G-grid. -/
noncomputable def gridWidth (G : ℝ) : ℕ :=
  ⌊G⌋₊

/-- Scaled cell width `h = ⌊δ G⌋` from (eq:gridspan). -/
noncomputable def gridWidthScaled (δ G : ℝ) : ℕ :=
  ⌊δ * G⌋₊

/-- Right endpoint aligned down to a multiple of `h`: `h ⌊X / h⌋`.
Paper `S' = h ⌊4 L G / h⌋`. -/
noncomputable def alignedSpan (h : ℕ) (X : ℝ) : ℕ :=
  h * ⌊X / (h : ℝ)⌋₊

/-- Absolute constant in the occupancy-versus-length remainder. -/
def gridCompareC : ℝ := 4

theorem gridWidth_le {G : ℝ} (hG : 0 ≤ G) : (gridWidth G : ℝ) ≤ G :=
  Nat.floor_le hG

theorem lt_gridWidth_add_one (G : ℝ) : G < (gridWidth G : ℝ) + 1 :=
  Nat.lt_floor_add_one G

theorem one_le_gridWidth {G : ℝ} (hG : 1 ≤ G) : 1 ≤ gridWidth G :=
  (Nat.one_le_floor_iff G).mpr hG

theorem gridWidth_pos {G : ℝ} (hG : 1 ≤ G) : 0 < gridWidth G :=
  Nat.floor_pos.mpr hG

theorem gridWidthScaled_le {δ G : ℝ} (h : 0 ≤ δ * G) :
    (gridWidthScaled δ G : ℝ) ≤ δ * G :=
  Nat.floor_le h

theorem gridWidthScaled_pos {δ G : ℝ} (h : 1 ≤ δ * G) :
    0 < gridWidthScaled δ G :=
  Nat.floor_pos.mpr h

theorem alignedSpan_le {h : ℕ} {X : ℝ} (hh : 0 < h) (hX : 0 ≤ X) :
    (alignedSpan h X : ℝ) ≤ X := by
  have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hdiv : 0 ≤ X / (h : ℝ) := div_nonneg hX hh0.le
  have hfl : (⌊X / (h : ℝ)⌋₊ : ℝ) ≤ X / (h : ℝ) := Nat.floor_le hdiv
  have hcast : ((h * ⌊X / (h : ℝ)⌋₊ : ℕ) : ℝ) =
      (h : ℝ) * (⌊X / (h : ℝ)⌋₊ : ℝ) :=
    Nat.cast_mul _ _
  have hmul : (h : ℝ) * (⌊X / (h : ℝ)⌋₊ : ℝ) ≤ (h : ℝ) * (X / (h : ℝ)) :=
    mul_le_mul_of_nonneg_left hfl hh0.le
  have hcancel : (h : ℝ) * (X / (h : ℝ)) = X := mul_div_cancel₀ X hh0.ne'
  unfold alignedSpan
  linarith [hcast, hmul, hcancel]

/-! ### Cells of width `h` (`Fourier.cell`) -/

/-- Integer points in cell `r` of width `h`. -/
def cellIco (r h : ℕ) : Finset ℕ :=
  Ico (r * h) ((r + 1) * h)

/-- Occupancy of `A` in cell `r`. -/
def cellOccupancy (A : Finset ℕ) (r h : ℕ) : ℕ :=
  (A.filter (cell r h)).card

/-- Relative cell-count hypothesis of `lem:gridcompare`: every full cell
has count `(1+O(η)) v h`. -/
def RelativeCellCounts (A : Finset ℕ) (h : ℕ) (v η : ℝ) : Prop :=
  ∀ r : ℕ, |((A.filter (cell r h)).card : ℝ) - v * h| ≤ η * v * h

theorem mem_cell_iff (r h u : ℕ) :
    cell r h u ↔ u ∈ Ico (r * h) ((r + 1) * h) := by
  simp [cell, mem_Ico]

theorem cellIco_card (r h : ℕ) : (cellIco r h).card = h := by
  unfold cellIco
  rw [Nat.card_Ico, Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]

theorem abs_cellIco_card_sub_width (r h : ℕ) :
    |((cellIco r h).card : ℝ) - (h : ℝ)| = 0 := by
  simp [cellIco_card]

theorem filter_cell_eq_inter (A : Finset ℕ) (r h : ℕ) :
    A.filter (cell r h) = A ∩ Ico (r * h) ((r + 1) * h) := by
  ext u
  simp [mem_filter, mem_inter, cell, mem_Ico]

theorem cellOccupancy_eq (A : Finset ℕ) (r h : ℕ) :
    cellOccupancy A r h = (A.filter (cell r h)).card :=
  rfl

private theorem mul_div_eq_sub_mod (n d : ℕ) :
    d * (n / d) = n - n % d := by
  calc
    d * (n / d) = d * (n / d) + n % d - n % d :=
      (Nat.add_sub_cancel _ _).symm
    _ = n - n % d := by rw [Nat.div_add_mod n d]

private theorem add_one_mul_div (n d : ℕ) :
    (n / d + 1) * d = n - n % d + d := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d), mul_div_eq_sub_mod]

private theorem lt_mul_succ_div {u d : ℕ} (hd : 0 < d) :
    u < (u / d + 1) * d := by
  have hmod : u % d < d := Nat.mod_lt u hd
  have hsum : d * (u / d) + u % d = u := Nat.div_add_mod u d
  have hlt : u < d * (u / d) + d := by
    have := Nat.add_lt_add_left hmod (d * (u / d))
    rwa [hsum] at this
  have hrw : (u / d + 1) * d = d * (u / d) + d := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  rwa [hrw]

private theorem mul_div_le_comm (u d : ℕ) : u / d * d ≤ u := by
  simpa [Nat.mul_comm] using Nat.mul_div_le u d

/-- Every `u` lies in cell `u / h` of width `h`. -/
theorem cell_div {h u : ℕ} (hh : 0 < h) : cell (u / h) h u :=
  ⟨mul_div_le_comm u h, lt_mul_succ_div hh⟩

theorem cell_div_eq {r h u : ℕ} (hu : cell r h u) : u / h = r :=
  Nat.div_eq_of_lt_le hu.1 hu.2

theorem cell_unique {r s h u : ℕ} (hr : cell r h u) (hs : cell s h u) :
    r = s :=
  (cell_div_eq hr).symm.trans (cell_div_eq hs)

theorem cell_pairwise_disjoint (A : Finset ℕ) (h : ℕ) (s : Finset ℕ) :
    Set.PairwiseDisjoint (s : Set ℕ) (fun r => A.filter (cell r h)) := by
  intro r _ s' _ hrs
  refine disjoint_left.mpr fun u hur hut => ?_
  exact hrs (cell_unique (mem_filter.mp hur).2 (mem_filter.mp hut).2)

/-- Coordinates in a cell of width `h` differ from the left endpoint by
at most `h`. -/
theorem cell_coord_sub_le {r h u : ℕ} (hu : cell r h u) :
    |(u : ℝ) - (r : ℝ) * h| ≤ h := by
  rcases hu with ⟨hlo, hhi⟩
  have hloR : (r : ℝ) * h ≤ u := by exact_mod_cast hlo
  have hhiR : (u : ℝ) < ((r + 1 : ℕ) : ℝ) * h := by exact_mod_cast hhi
  have hs : ((r + 1 : ℕ) : ℝ) * h = (r : ℝ) * h + h := by
    push_cast
    ring
  rw [abs_of_nonneg (sub_nonneg.mpr hloR)]
  linarith

/-- `|n/h − n/h|` for integer division versus real division: strictly
less than one cell. -/
theorem abs_nat_div_sub_div {n h : ℕ} (hh : 0 < h) :
    |((n / h : ℕ) : ℝ) - (n : ℝ) / (h : ℝ)| < 1 := by
  have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hdecomp : (n : ℝ) =
      (h : ℝ) * ((n / h : ℕ) : ℝ) + ((n % h : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod n h).symm
  have hmod : ((n % h : ℕ) : ℝ) < (h : ℝ) :=
    Nat.cast_lt.mpr (Nat.mod_lt n hh)
  have hmod0 : (0 : ℝ) ≤ ((n % h : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdiff :
      (n : ℝ) / (h : ℝ) - ((n / h : ℕ) : ℝ) =
        ((n % h : ℕ) : ℝ) / (h : ℝ) := by
    have hhne : (h : ℝ) ≠ 0 := hh0.ne'
    calc
      (n : ℝ) / (h : ℝ) - ((n / h : ℕ) : ℝ)
          = ((h : ℝ) * ((n / h : ℕ) : ℝ) + ((n % h : ℕ) : ℝ)) / (h : ℝ) -
              ((n / h : ℕ) : ℝ) := by
            rw [hdecomp]
      _ = ((h : ℝ) * ((n / h : ℕ) : ℝ)) / (h : ℝ) +
              ((n % h : ℕ) : ℝ) / (h : ℝ) - ((n / h : ℕ) : ℝ) := by
            rw [add_div]
      _ = ((n / h : ℕ) : ℝ) + ((n % h : ℕ) : ℝ) / (h : ℝ) -
              ((n / h : ℕ) : ℝ) := by
            rw [mul_div_cancel_left₀ _ hhne]
      _ = ((n % h : ℕ) : ℝ) / (h : ℝ) := by
            ring
  rw [abs_sub_comm, hdiff, abs_of_nonneg (div_nonneg hmod0 hh0.le)]
  exact (div_lt_one hh0).mpr hmod

theorem relativeCellCounts_bounds {A : Finset ℕ} {h : ℕ} {v η : ℝ}
    {r : ℕ} (hcell : RelativeCellCounts A h v η) :
    (1 - η) * v * h ≤ ((A.filter (cell r h)).card : ℝ) ∧
      ((A.filter (cell r h)).card : ℝ) ≤ (1 + η) * v * h := by
  have hle := abs_le.mp (hcell r)
  exact ⟨by linarith, by linarith⟩

/-! ### Interior cells versus length `/ h` -/

/-- Full interior cells of the open slot `(a,c)`. -/
def interiorCells (a c h : ℕ) : Finset ℕ :=
  Ico (a / h + 1) (c / h)

/-- Number of full interior cells. Paper: about `|W|/h`. -/
def interiorCellCount (a c h : ℕ) : ℕ :=
  c / h - (a / h + 1)

theorem interiorCellCount_eq_card (a c h : ℕ) :
    interiorCellCount a c h = (interiorCells a c h).card := by
  simp [interiorCellCount, interiorCells, Nat.card_Ico]

private theorem card_Ico_cast {a b : ℕ} (h : a ≤ b) :
    ((Ico a b).card : ℝ) = (b : ℝ) - a := by
  rw [Nat.card_Ico, Nat.cast_sub h]

private theorem rMin_mul_h_gt {h a : ℕ} (hh : 0 < h) :
    a < (a / h + 1) * h := by
  have hform : (a / h + 1) * h = a - a % h + h := add_one_mul_div a h
  rw [hform]
  have hm : a % h ≤ a := Nat.mod_le a h
  have hsplit : a = a - a % h + a % h := (Nat.sub_add_cancel hm).symm
  have : a - a % h + a % h < a - a % h + h :=
    Nat.add_lt_add_left (Nat.mod_lt a hh) _
  rwa [← hsplit] at this

private theorem slot_rMin_lt {a c h : ℕ} (hh : 0 < h)
    (hle4 : a + 4 * h ≤ c) : a / h + 1 < c / h := by
  have hdiv : (a + 4 * h) / h ≤ c / h := Nat.div_le_div_right hle4
  have hdiv' : a / h + 4 ≤ c / h := by
    rwa [Nat.add_mul_div_right a 4 hh] at hdiv
  have hlt : a / h + 1 < a / h + 4 :=
    Nat.add_lt_add_left (by norm_num : (1 : ℕ) < 4) _
  exact hlt.trans_le hdiv'

private theorem cell_block_subset {h a c r : ℕ} (hh : 0 < h)
    (hr : r ∈ Ico (a / h + 1) (c / h)) :
    Ico (r * h) ((r + 1) * h) ⊆ Ioo a c := by
  intro u hu
  rw [mem_Ico] at hu hr
  rw [mem_Ioo]
  constructor
  · have h1 : a < (a / h + 1) * h := rMin_mul_h_gt hh
    have h2 : (a / h + 1) * h ≤ r * h := Nat.mul_le_mul_right h hr.1
    exact h1.trans_le (h2.trans hu.1)
  · have h1 : r + 1 ≤ c / h := Nat.succ_le_of_lt hr.2
    have h2 : (r + 1) * h ≤ (c / h) * h := Nat.mul_le_mul_right h h1
    have h3 : (c / h) * h ≤ c := by
      simpa [Nat.mul_comm] using Nat.mul_div_le c h
    exact hu.2.trans_le (h2.trans h3)

private theorem grid_cell_span_eq {h a c : ℕ}
    (_hh : 0 < h) (_hIco : a / h + 1 ≤ c / h) :
    h * (c / h - (a / h + 1)) =
      c - c % h - (a - a % h) - h := by
  have hmul :
      h * (c / h - (a / h + 1)) = h * (c / h) - h * (a / h + 1) :=
    Nat.mul_sub_left_distrib h (c / h) (a / h + 1)
  have hW : h * (c / h) = c - c % h := mul_div_eq_sub_mod c h
  have hL0 : h * (a / h) = a - a % h := mul_div_eq_sub_mod a h
  have hL : h * (a / h + 1) = h * (a / h) + h := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hmul, hL, hW, hL0]
  exact Nat.sub_add_eq (c - c % h) (a - a % h) h

private theorem grid_span_cast {h a c : ℕ} (hh : 0 < h)
    (hIco : a / h + 1 ≤ c / h) :
    ((h * (c / h - (a / h + 1)) : ℕ) : ℝ) =
      (c : ℝ) - (c % h : ℝ) - ((a : ℝ) - (a % h : ℝ)) - (h : ℝ) := by
  have heq := grid_cell_span_eq hh hIco
  have hWmod : c % h ≤ c := Nat.mod_le c h
  have hLmod : a % h ≤ a := Nat.mod_le a h
  have hmid : a - a % h ≤ c - c % h := by
    have hdiv : a / h ≤ c / h :=
      Nat.le_trans (Nat.le_succ (a / h)) hIco
    have := Nat.mul_le_mul_left h hdiv
    simpa [mul_div_eq_sub_mod] using this
  have hmidh : h ≤ c - c % h - (a - a % h) := by
    have hmul := Nat.mul_le_mul_left h hIco
    have hL1 : h * (a / h + 1) = a - a % h + h := by
      rw [Nat.mul_comm]
      exact add_one_mul_div a h
    have hW : h * (c / h) = c - c % h := mul_div_eq_sub_mod c h
    rw [hL1, hW] at hmul
    exact (Nat.le_sub_iff_add_le' hmid).mpr hmul
  rw [heq, Nat.cast_sub hmidh, Nat.cast_sub hmid, Nat.cast_sub hWmod,
    Nat.cast_sub hLmod]

private theorem mod_cast_pred {n h : ℕ} (hh : 0 < h) :
    ((n % h : ℕ) : ℝ) ≤ (h : ℝ) - 1 := by
  have hle : n % h ≤ h - 1 := Nat.le_pred_of_lt (Nat.mod_lt n hh)
  have h1 : 1 ≤ h := Nat.succ_le_of_lt hh
  have : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  exact (Nat.cast_le.mpr hle).trans_eq this

private theorem grid_span_ge {h a c : ℕ} (hh : 0 < h)
    (hIco : a / h + 1 ≤ c / h) :
    ((c : ℝ) - a) - 2 * (h : ℝ) + 1 ≤
      (h : ℝ) * (((c / h : ℕ) : ℝ) - ((a / h + 1 : ℕ) : ℝ)) := by
  have hcast := grid_span_cast hh hIco
  have hWm : ((c % h : ℕ) : ℝ) ≤ (h : ℝ) - 1 := mod_cast_pred hh
  have hLm : (0 : ℝ) ≤ ((a % h : ℕ) : ℝ) := Nat.cast_nonneg _
  have hw : ((h * (c / h - (a / h + 1)) : ℕ) : ℝ) =
      (h : ℝ) * (((c / h : ℕ) : ℝ) - ((a / h + 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_sub hIco]
  linarith [hcast, hw, hWm, hLm]

private theorem grid_span_le {h a c : ℕ} (hh : 0 < h)
    (hIco : a / h + 1 ≤ c / h) :
    (h : ℝ) * (((c / h : ℕ) : ℝ) - ((a / h + 1 : ℕ) : ℝ)) ≤
      (c : ℝ) - a := by
  have hcast := grid_span_cast hh hIco
  have hWm : (0 : ℝ) ≤ ((c % h : ℕ) : ℝ) := Nat.cast_nonneg _
  have hLm : ((a % h : ℕ) : ℝ) ≤ (h : ℝ) - 1 := mod_cast_pred hh
  have hw : ((h * (c / h - (a / h + 1)) : ℕ) : ℝ) =
      (h : ℝ) * (((c / h : ℕ) : ℝ) - ((a / h + 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_sub hIco]
  linarith [hcast, hw, hWm, hLm]

/-- Interior cell count versus geometric length `/ h`. At most two
cells of discrepancy. -/
theorem abs_interior_cell_count_sub_div {a c h : ℕ} (hh : 0 < h)
    (hac : a ≤ c) :
    |((interiorCellCount a c h : ℝ) - ((c : ℝ) - a) / (h : ℝ))| ≤ 2 := by
  have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hw0 : (0 : ℝ) ≤ (c : ℝ) - a := sub_nonneg.mpr (Nat.cast_le.mpr hac)
  by_cases hIco : a / h + 1 ≤ c / h
  · have hn : interiorCellCount a c h = c / h - (a / h + 1) := rfl
    have hcast := grid_span_cast hh hIco
    have hmul : ((h * (c / h - (a / h + 1)) : ℕ) : ℝ) =
        (h : ℝ) * (interiorCellCount a c h : ℝ) := by
      rw [hn, Nat.cast_mul, Nat.cast_sub hIco]
    have heq :
        (h : ℝ) * ((interiorCellCount a c h : ℝ) - ((c : ℝ) - a) / (h : ℝ)) =
          ((a % h : ℕ) : ℝ) - ((c % h : ℕ) : ℝ) - (h : ℝ) := by
      have hcancel : (h : ℝ) * (((c : ℝ) - a) / (h : ℝ)) = (c : ℝ) - a :=
        mul_div_cancel₀ _ hh0.ne'
      linarith [hcast, hmul, hcancel]
    have habs :
        (h : ℝ) * |((interiorCellCount a c h : ℝ) - ((c : ℝ) - a) / (h : ℝ))| =
          |((a % h : ℕ) : ℝ) - ((c % h : ℕ) : ℝ) - (h : ℝ)| := by
      calc
        (h : ℝ) * |((interiorCellCount a c h : ℝ) - ((c : ℝ) - a) / (h : ℝ))|
            = |(h : ℝ)| *
                |((interiorCellCount a c h : ℝ) - ((c : ℝ) - a) / (h : ℝ))| := by
              rw [abs_of_pos hh0]
        _ = |(h : ℝ) *
              ((interiorCellCount a c h : ℝ) - ((c : ℝ) - a) / (h : ℝ))| :=
              (abs_mul _ _).symm
        _ = |((a % h : ℕ) : ℝ) - ((c % h : ℕ) : ℝ) - (h : ℝ)| := by
              rw [heq]
    have hnum :
        |((a % h : ℕ) : ℝ) - ((c % h : ℕ) : ℝ) - (h : ℝ)| ≤
          2 * (h : ℝ) := by
      rw [abs_le]
      constructor
      · linarith [Nat.cast_nonneg (α := ℝ) (a % h),
          mod_cast_pred (n := c) hh]
      · linarith [Nat.cast_nonneg (α := ℝ) (c % h),
          mod_cast_pred (n := a) hh]
    have hbound :
        (h : ℝ) * |((interiorCellCount a c h : ℝ) - ((c : ℝ) - a) / (h : ℝ))| ≤
          2 * (h : ℝ) := by
      linarith [habs, hnum]
    have hdiv :
        |((interiorCellCount a c h : ℝ) - ((c : ℝ) - a) / (h : ℝ))| ≤
          (2 * (h : ℝ)) / (h : ℝ) :=
      (le_div_iff₀ hh0).mpr (by linarith [hbound])
    have hsimp : (2 * (h : ℝ)) / (h : ℝ) = 2 := by
      field_simp [hh0.ne']
    linarith [hdiv, hsimp]
  · have hle : c / h ≤ a / h :=
      Nat.lt_succ_iff.mp (Nat.not_le.mp hIco)
    have hle' : c / h ≤ a / h + 1 := Nat.le_succ_of_le hle
    have hn0 : interiorCellCount a c h = 0 := Nat.sub_eq_zero_of_le hle'
    have hdivle : a / h ≥ c / h := hle
    have hmul : h * (c / h) ≤ h * (a / h) := Nat.mul_le_mul_left h hdivle
    have hsub : c - c % h ≤ a - a % h := by
      simpa [mul_div_eq_sub_mod] using hmul
    have ha : c - c % h ≤ a :=
      hsub.trans (Nat.sub_le a (a % h))
    have hadd : c ≤ a + c % h := Nat.sub_le_iff_le_add.mp ha
    have hca : c - a ≤ c % h := Nat.sub_le_iff_le_add'.mpr hadd
    have hca' : c - a ≤ h - 1 :=
      hca.trans (Nat.le_pred_of_lt (Nat.mod_lt c hh))
    have hw : ((c : ℝ) - a) / (h : ℝ) ≤ ((h : ℝ) - 1) / (h : ℝ) := by
      have h1 : 1 ≤ h := Nat.succ_le_of_lt hh
      have hcast : ((c - a : ℕ) : ℝ) ≤ ((h - 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr hca'
      have hcaR : ((c - a : ℕ) : ℝ) = (c : ℝ) - a := Nat.cast_sub hac
      have hh1 : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
        rw [Nat.cast_sub h1, Nat.cast_one]
      have : (c : ℝ) - a ≤ (h : ℝ) - 1 := by linarith [hcast, hcaR, hh1]
      exact div_le_div_of_nonneg_right this hh0.le
    have hlt : ((h : ℝ) - 1) / (h : ℝ) < 1 := by
      have : (h : ℝ) - 1 < h := by linarith
      exact (div_lt_one hh0).mpr this
    have hwlt : ((c : ℝ) - a) / (h : ℝ) < 1 := hw.trans_lt hlt
    have : |((interiorCellCount a c h : ℝ) - ((c : ℝ) - a) / (h : ℝ))| =
        ((c : ℝ) - a) / (h : ℝ) := by
      rw [hn0, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg
        (div_nonneg hw0 hh0.le)]
    linarith [this, hwlt]

/-! ### Geometric slot occupancy -/

/-- Candidates of `A` in the open geometric slot `(a,c)`. -/
def slotOccupancy (A : Finset ℕ) (a c : ℕ) : Finset ℕ :=
  A.filter (fun u => a < u ∧ u < c)

/-- Continuous slot length `w = c - a`. -/
noncomputable def slotLength (a c : ℕ) : ℝ :=
  (c : ℝ) - a

theorem mem_slotOccupancy_iff (A : Finset ℕ) (a c u : ℕ) :
    u ∈ slotOccupancy A a c ↔ u ∈ A ∧ a < u ∧ u < c := by
  simp [slotOccupancy, mem_filter]

theorem slotOccupancy_eq_inter (A : Finset ℕ) (a c : ℕ) :
    slotOccupancy A a c = A ∩ Ioo a c := by
  ext u
  simp [slotOccupancy, mem_filter, mem_inter, mem_Ioo]

/-- Full integer occupancy of `(a,c)` versus geometric length: one
point of discrepancy (the missing endpoint). -/
theorem abs_Ioo_card_sub_length {a c : ℕ} (hac : a < c) :
    |((Ioo a c).card : ℝ) - ((c : ℝ) - a)| = 1 := by
  have hle : a ≤ c := hac.le
  have hpos : 1 ≤ c - a := Nat.succ_le_iff.mp (Nat.sub_pos_of_lt hac)
  rw [Nat.card_Ioo]
  have hcast : ((c - a - 1 : ℕ) : ℝ) = (c : ℝ) - (a : ℝ) - 1 := by
    rw [Nat.cast_sub hpos, Nat.cast_sub hle, Nat.cast_one]
  rw [hcast]
  have hdiff : (c : ℝ) - (a : ℝ) - 1 - ((c : ℝ) - a) = (-1 : ℝ) := by
    ring
  rw [hdiff, abs_neg, abs_one]

private theorem four_mul_h_le {a c h : ℕ} (_hh : 0 < h)
    (hlen : (h : ℝ) ≤ ((c : ℝ) - a) / 4) : a + 4 * h ≤ c := by
  have hR : (a : ℝ) + 4 * (h : ℝ) ≤ (c : ℝ) := by
    have : (h : ℝ) * 4 ≤ (c : ℝ) - a :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hlen
    linarith
  have hcast : ((a + 4 * h : ℕ) : ℝ) = (a : ℝ) + 4 * (h : ℝ) := by
    push_cast
    rfl
  have : ((a + 4 * h : ℕ) : ℝ) ≤ (c : ℝ) := by linarith [hR, hcast]
  exact Nat.cast_le.mp this

private theorem slot_length_pos {a c h : ℕ} (hh : 0 < h)
    (hlen : (h : ℝ) ≤ ((c : ℝ) - a) / 4) : (0 : ℝ) < (c : ℝ) - a := by
  have : (0 : ℝ) < 4 * (h : ℝ) :=
    mul_pos (by norm_num : (0 : ℝ) < 4) (Nat.cast_pos.mpr hh)
  linarith

private theorem slot_subset_covering {A : Finset ℕ} {a c h : ℕ}
    (hh : 0 < h) (_hac : a < c) :
    slotOccupancy A a c ⊆
      (Icc (a / h) (c / h)).biUnion (fun r => A.filter (cell r h)) := by
  intro u hu
  have ⟨huA, hau, huc⟩ := mem_filter.mp hu
  have hcellu : cell (u / h) h u := cell_div hh
  have hlo : a / h ≤ u / h := Nat.div_le_div_right (Nat.le_of_lt hau)
  have hhi : u / h ≤ c / h := Nat.div_le_div_right (Nat.le_of_lt huc)
  exact mem_biUnion.mpr ⟨u / h, mem_Icc.mpr ⟨hlo, hhi⟩,
    mem_filter.mpr ⟨huA, hcellu⟩⟩

/-- Covering cells of `(a,c)` have real width at most `w + 2h`. -/
private theorem covering_width_le {a c h : ℕ} (hh : 0 < h)
    (hac : a ≤ c) :
    (h : ℝ) * ((Icc (a / h) (c / h)).card : ℝ) ≤
      ((c : ℝ) - a) + 2 * (h : ℝ) := by
  have hdiv : a / h ≤ c / h := Nat.div_le_div_right hac
  have hcard : ((Icc (a / h) (c / h)).card : ℝ) =
      ((c / h : ℕ) : ℝ) - ((a / h : ℕ) : ℝ) + 1 := by
    have hle : a / h ≤ c / h + 1 := Nat.le_succ_of_le hdiv
    rw [Nat.card_Icc, Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
    ring
  have hcdiv : ((c / h : ℕ) : ℝ) * (h : ℝ) =
      (c : ℝ) - ((c % h : ℕ) : ℝ) := by
    have hnat : (c / h) * h = c - c % h := by
      rw [Nat.mul_comm]
      exact mul_div_eq_sub_mod c h
    have hmod : c % h ≤ c := Nat.mod_le c h
    rw [← Nat.cast_mul, hnat, Nat.cast_sub hmod]
  have hadiv : ((a / h : ℕ) : ℝ) * (h : ℝ) =
      (a : ℝ) - ((a % h : ℕ) : ℝ) := by
    have hnat : (a / h) * h = a - a % h := by
      rw [Nat.mul_comm]
      exact mul_div_eq_sub_mod a h
    have hmod : a % h ≤ a := Nat.mod_le a h
    rw [← Nat.cast_mul, hnat, Nat.cast_sub hmod]
  have hprod : (h : ℝ) * ((Icc (a / h) (c / h)).card : ℝ) =
      ((c / h : ℕ) : ℝ) * (h : ℝ) - ((a / h : ℕ) : ℝ) * (h : ℝ) +
        (h : ℝ) := by
    rw [hcard]
    ring
  rw [hprod, hcdiv, hadiv]
  linarith [Nat.cast_nonneg (α := ℝ) (c % h),
    mod_cast_pred (n := a) hh]

/-- Upper occupancy bound: interior plus at most two boundary cells. -/
theorem slot_occupancy_le {A : Finset ℕ} {h : ℕ} (hh : 0 < h) {v η : ℝ}
    (hη : 0 ≤ η) (hv : 0 < v) (hcell : RelativeCellCounts A h v η)
    {a c : ℕ} (hlen : (h : ℝ) ≤ ((c : ℝ) - a) / 4) :
    ((slotOccupancy A a c).card : ℝ) ≤
      (1 + η) * v * (((c : ℝ) - a) + 2 * (h : ℝ)) := by
  have hw := slot_length_pos hh hlen
  have hac : a < c := Nat.cast_lt.mp (by linarith [hw] : (a : ℝ) < (c : ℝ))
  have hcov := slot_subset_covering (A := A) hh hac
  have hcard : ((slotOccupancy A a c).card : ℝ) ≤
      (((Icc (a / h) (c / h)).biUnion (fun r => A.filter (cell r h))).card : ℝ) :=
    Nat.cast_le.mpr (card_le_card hcov)
  have hbu :
      ((((Icc (a / h) (c / h)).biUnion (fun r => A.filter (cell r h))).card : ℝ)) ≤
        ∑ r ∈ Icc (a / h) (c / h), ((A.filter (cell r h)).card : ℝ) := by
    have hnat :=
      card_biUnion_le (s := Icc (a / h) (c / h))
        (t := fun r => A.filter (cell r h))
    have hcast :
        ((∑ r ∈ Icc (a / h) (c / h), (A.filter (cell r h)).card : ℕ) : ℝ) =
          ∑ r ∈ Icc (a / h) (c / h), ((A.filter (cell r h)).card : ℝ) :=
      Nat.cast_sum _ _
    exact (Nat.cast_le.mpr hnat).trans_eq hcast
  have hterm : ∀ r ∈ Icc (a / h) (c / h),
      ((A.filter (cell r h)).card : ℝ) ≤ (1 + η) * v * (h : ℝ) := fun r _ =>
    (relativeCellCounts_bounds hcell).2
  have hsum :
      ∑ r ∈ Icc (a / h) (c / h), ((A.filter (cell r h)).card : ℝ) ≤
        ∑ r ∈ Icc (a / h) (c / h), (1 + η) * v * (h : ℝ) :=
    sum_le_sum hterm
  have hconst :
      ∑ r ∈ Icc (a / h) (c / h), (1 + η) * v * (h : ℝ) =
        (1 + η) * v * (h : ℝ) * ((Icc (a / h) (c / h)).card : ℝ) := by
    simp only [sum_const, nsmul_eq_mul]
    ring
  have hwidth := covering_width_le hh hac.le
  have hη0 : 0 ≤ 1 + η := add_nonneg (by norm_num) hη
  have hfac : 0 ≤ (1 + η) * v := mul_nonneg hη0 hv.le
  have hmulw : (1 + η) * v * (h : ℝ) * ((Icc (a / h) (c / h)).card : ℝ) ≤
      (1 + η) * v * (((c : ℝ) - a) + 2 * (h : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hwidth hfac
    have hrw :
        (1 + η) * v * ((h : ℝ) * ((Icc (a / h) (c / h)).card : ℝ)) =
          (1 + η) * v * (h : ℝ) * ((Icc (a / h) (c / h)).card : ℝ) := by
      ring
    linarith [this, hrw]
  linarith [hcard, hbu, hsum, hconst, hmulw]

/-- Lower occupancy bound from full interior cells. -/
theorem slot_occupancy_ge {A : Finset ℕ} {h : ℕ} (hh : 0 < h) {v η : ℝ}
    (_hη : 0 ≤ η) (hη1 : η ≤ 1) (hv : 0 < v)
    (hcell : RelativeCellCounts A h v η)
    {a c : ℕ} (hlen : (h : ℝ) ≤ ((c : ℝ) - a) / 4) :
    (1 - η) * v * (((c : ℝ) - a) - 2 * (h : ℝ)) ≤
      ((slotOccupancy A a c).card : ℝ) := by
  set w : ℝ := (c : ℝ) - a
  set rMin : ℕ := a / h + 1
  set rMax : ℕ := c / h
  have hw := slot_length_pos hh hlen
  have hle4 := four_mul_h_le hh hlen
  have hrMin : rMin < rMax := slot_rMin_lt hh hle4
  have hinterPts :
      (Ico rMin rMax).biUnion (fun r => A.filter (cell r h)) ⊆
        slotOccupancy A a c := by
    intro u hu
    obtain ⟨r, hr, huA⟩ := mem_biUnion.mp hu
    have huI : u ∈ Ico (r * h) ((r + 1) * h) := by
      simpa [cell, mem_Ico] using (mem_filter.mp huA).2
    have huW : u ∈ Ioo a c := cell_block_subset hh hr huI
    exact mem_filter.mpr ⟨(mem_filter.mp huA).1, mem_Ioo.mp huW⟩
  have hcard_cell_ge : ∀ r,
      (1 - η) * v * (h : ℝ) ≤ ((A.filter (cell r h)).card : ℝ) := fun r =>
    (relativeCellCounts_bounds hcell).1
  have hdisj := cell_pairwise_disjoint A h (Ico rMin rMax)
  have hinter_ge :
      (1 - η) * v * ((h : ℝ) * ((rMax : ℝ) - rMin)) ≤
        (((Ico rMin rMax).biUnion (fun r => A.filter (cell r h))).card : ℝ) := by
    have hsum : (∑ r ∈ Ico rMin rMax, ((A.filter (cell r h)).card : ℝ)) ≥
        ∑ r ∈ Ico rMin rMax, (1 - η) * v * (h : ℝ) :=
      sum_le_sum fun r _ => hcard_cell_ge r
    have hsumc : (∑ r ∈ Ico rMin rMax, (1 - η) * v * (h : ℝ)) =
        (1 - η) * v * (h : ℝ) * ((rMax : ℝ) - rMin) := by
      simp only [sum_const, nsmul_eq_mul]
      rw [card_Ico_cast hrMin.le]
      ring
    have hcast :
        (((Ico rMin rMax).biUnion (fun r => A.filter (cell r h))).card : ℝ) =
          ∑ r ∈ Ico rMin rMax, ((A.filter (cell r h)).card : ℝ) := by
      rw [card_biUnion hdisj]
      exact Nat.cast_sum _ _
    have hrw : (1 - η) * v * (h : ℝ) * ((rMax : ℝ) - rMin) =
        (1 - η) * v * ((h : ℝ) * ((rMax : ℝ) - rMin)) := by ring
    linarith
  have hinter_le :
      (((Ico rMin rMax).biUnion (fun r => A.filter (cell r h))).card : ℝ) ≤
        ((slotOccupancy A a c).card : ℝ) :=
    Nat.cast_le.mpr (card_le_card hinterPts)
  have hspan : w - 2 * (h : ℝ) ≤ (h : ℝ) * ((rMax : ℝ) - rMin) := by
    have h1 := grid_span_ge hh hrMin.le
    linarith [h1]
  have hnn : 0 ≤ (1 - η) * v :=
    mul_nonneg (sub_nonneg.mpr hη1) hv.le
  have hmid : (1 - η) * v * (w - 2 * (h : ℝ)) ≤
      (1 - η) * v * ((h : ℝ) * ((rMax : ℝ) - rMin)) :=
    mul_le_mul_of_nonneg_left hspan hnn
  linarith [hinter_ge, hinter_le, hmid]

/-- Occupancy of `A ∩ (a,c)` versus `v` times geometric length. -/
theorem abs_slot_occupancy_sub_geom {A : Finset ℕ} {h : ℕ} (hh : 0 < h)
    {v η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hv : 0 < v)
    (hcell : RelativeCellCounts A h v η)
    {a c : ℕ} (hlen : (h : ℝ) ≤ ((c : ℝ) - a) / 4) :
    |((slotOccupancy A a c).card : ℝ) - v * ((c : ℝ) - a)| ≤
      η * v * ((c : ℝ) - a) + gridCompareC * v * (h : ℝ) := by
  set w : ℝ := (c : ℝ) - a
  set N : ℝ := ((slotOccupancy A a c).card : ℝ)
  have hge := slot_occupancy_ge hh hη hη1 hv hcell hlen
  have hle := slot_occupancy_le hh hη hv hcell hlen
  have hup : N - v * w ≤ η * v * w + 2 * (1 + η) * v * (h : ℝ) := by
    unfold N w
    linarith [hle]
  have hdn : v * w - N ≤ η * v * w + 2 * (1 - η) * v * (h : ℝ) := by
    unfold N w
    linarith [hge]
  have hup' : N - v * w ≤ η * v * w + gridCompareC * v * (h : ℝ) := by
    unfold gridCompareC
    have hvh : 0 ≤ v * (h : ℝ) := mul_nonneg hv.le (Nat.cast_nonneg h)
    have hcoef : (2 : ℝ) * (1 + η) ≤ 4 := by linarith [hη1]
    have hrwL : (2 : ℝ) * (1 + η) * v * (h : ℝ) =
        ((2 : ℝ) * (1 + η)) * (v * (h : ℝ)) := by ring
    have hrwR : (4 : ℝ) * v * (h : ℝ) = (4 : ℝ) * (v * (h : ℝ)) := by ring
    have hmul : (2 : ℝ) * (1 + η) * v * (h : ℝ) ≤ (4 : ℝ) * v * (h : ℝ) := by
      rw [hrwL, hrwR]
      exact mul_le_mul_of_nonneg_right hcoef hvh
    linarith [hup, hmul]
  have hdn' : v * w - N ≤ η * v * w + gridCompareC * v * (h : ℝ) := by
    unfold gridCompareC
    have hvh : 0 ≤ v * (h : ℝ) := mul_nonneg hv.le (Nat.cast_nonneg h)
    have hcoef : (2 : ℝ) * (1 - η) ≤ 4 := by linarith [hη]
    have hrwL : (2 : ℝ) * (1 - η) * v * (h : ℝ) =
        ((2 : ℝ) * (1 - η)) * (v * (h : ℝ)) := by ring
    have hrwR : (4 : ℝ) * v * (h : ℝ) = (4 : ℝ) * (v * (h : ℝ)) := by ring
    have hmul : (2 : ℝ) * (1 - η) * v * (h : ℝ) ≤ (4 : ℝ) * v * (h : ℝ) := by
      rw [hrwL, hrwR]
      exact mul_le_mul_of_nonneg_right hcoef hvh
    linarith [hdn, hmul]
  exact abs_le.mpr ⟨by linarith [hdn'], by linarith [hup']⟩

/-- Denominator of `lem:gridcompare`: interior cells supply `≫ v w`. -/
theorem slot_occupancy_ge_quarter {A : Finset ℕ} {h : ℕ} (hh : 0 < h)
    {v η : ℝ} (_hη : 0 ≤ η) (hv : 0 < v) (hηlt : η < 1 / 2)
    (hcell : RelativeCellCounts A h v η)
    {a c : ℕ} (hlen : (h : ℝ) ≤ ((c : ℝ) - a) / 4) :
    v * ((c : ℝ) - a) / 4 ≤ ((slotOccupancy A a c).card : ℝ) := by
  set w : ℝ := (c : ℝ) - a
  set rMin : ℕ := a / h + 1
  set rMax : ℕ := c / h
  have hw := slot_length_pos hh hlen
  have hle4 := four_mul_h_le hh hlen
  have hrMin : rMin < rMax := slot_rMin_lt hh hle4
  have hinterPts :
      (Ico rMin rMax).biUnion (fun r => A.filter (cell r h)) ⊆
        slotOccupancy A a c := by
    intro u hu
    obtain ⟨r, hr, huA⟩ := mem_biUnion.mp hu
    have huI : u ∈ Ico (r * h) ((r + 1) * h) := by
      simpa [cell, mem_Ico] using (mem_filter.mp huA).2
    have huW : u ∈ Ioo a c := cell_block_subset hh hr huI
    exact mem_filter.mpr ⟨(mem_filter.mp huA).1, mem_Ioo.mp huW⟩
  have hcard_cell_ge : ∀ r,
      (1 - η) * v * (h : ℝ) ≤ ((A.filter (cell r h)).card : ℝ) := fun r =>
    (relativeCellCounts_bounds hcell).1
  have hdisj := cell_pairwise_disjoint A h (Ico rMin rMax)
  have hinter_ge :
      (1 - η) * v * ((h : ℝ) * ((rMax : ℝ) - rMin)) ≤
        (((Ico rMin rMax).biUnion (fun r => A.filter (cell r h))).card : ℝ) := by
    have hsum : (∑ r ∈ Ico rMin rMax, ((A.filter (cell r h)).card : ℝ)) ≥
        ∑ r ∈ Ico rMin rMax, (1 - η) * v * (h : ℝ) :=
      sum_le_sum fun r _ => hcard_cell_ge r
    have hsumc : (∑ r ∈ Ico rMin rMax, (1 - η) * v * (h : ℝ)) =
        (1 - η) * v * (h : ℝ) * ((rMax : ℝ) - rMin) := by
      simp only [sum_const, nsmul_eq_mul]
      rw [card_Ico_cast hrMin.le]
      ring
    have hcast :
        (((Ico rMin rMax).biUnion (fun r => A.filter (cell r h))).card : ℝ) =
          ∑ r ∈ Ico rMin rMax, ((A.filter (cell r h)).card : ℝ) := by
      rw [card_biUnion hdisj]
      exact Nat.cast_sum _ _
    have hrw : (1 - η) * v * (h : ℝ) * ((rMax : ℝ) - rMin) =
        (1 - η) * v * ((h : ℝ) * ((rMax : ℝ) - rMin)) := by ring
    linarith
  have hinter_le :
      (((Ico rMin rMax).biUnion (fun r => A.filter (cell r h))).card : ℝ) ≤
        ((slotOccupancy A a c).card : ℝ) :=
    Nat.cast_le.mpr (card_le_card hinterPts)
  have hspan : w / 2 ≤ (h : ℝ) * ((rMax : ℝ) - rMin) := by
    have h1 := grid_span_ge hh hrMin.le
    have h2 : w / 2 ≤ w - 2 * (h : ℝ) + 1 := by
      have : (4 : ℝ) * (h : ℝ) ≤ w := by linarith [hlen]
      linarith
    linarith [h1, h2]
  have hnn : 0 ≤ (1 - η) * v :=
    mul_nonneg (by linarith [hηlt] : (0 : ℝ) ≤ 1 - η) hv.le
  have hmid : (1 - η) * v * (w / 2) ≤
      (1 - η) * v * ((h : ℝ) * ((rMax : ℝ) - rMin)) :=
    mul_le_mul_of_nonneg_left hspan hnn
  have hquarter : v * w / 4 ≤ (1 - η) * v * (w / 2) := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - η := by linarith [hηlt]
    have hvw : 0 ≤ v * (w / 2) :=
      mul_nonneg hv.le (div_nonneg hw.le (by norm_num))
    have := mul_le_mul_of_nonneg_right hhalf hvw
    have hL : (1 / 2 : ℝ) * (v * (w / 2)) = v * w / 4 := by ring
    have hR : (1 - η) * (v * (w / 2)) = (1 - η) * v * (w / 2) := by ring
    linarith
  linarith [hinter_ge, hinter_le, hmid, hquarter]

/-- Relative density of occupancy versus the geometric slot. -/
theorem abs_slot_occupancy_div_sub_one {A : Finset ℕ} {h : ℕ} (hh : 0 < h)
    {v η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hv : 0 < v)
    (hcell : RelativeCellCounts A h v η)
    {a c : ℕ} (hlen : (h : ℝ) ≤ ((c : ℝ) - a) / 4) :
    |((slotOccupancy A a c).card : ℝ) / (v * ((c : ℝ) - a)) - 1| ≤
      η + gridCompareC * (h : ℝ) / ((c : ℝ) - a) := by
  set w : ℝ := (c : ℝ) - a
  set N : ℝ := ((slotOccupancy A a c).card : ℝ)
  have hw := slot_length_pos hh hlen
  have hvw : 0 < v * w := mul_pos hv hw
  have habs := abs_slot_occupancy_sub_geom hh hη hη1 hv hcell hlen
  have hdiv : |N - v * w| / (v * w) ≤
      (η * v * w + gridCompareC * v * (h : ℝ)) / (v * w) :=
    div_le_div_of_nonneg_right habs hvw.le
  have hL : |N - v * w| / (v * w) = |N / (v * w) - 1| := by
    have h1 : |N - v * w| / (v * w) = |N - v * w| / |v * w| := by
      rw [abs_of_pos hvw]
    rw [h1, ← abs_div]
    congr 1
    rw [sub_div, div_self hvw.ne']
  have hR : (η * v * w + gridCompareC * v * (h : ℝ)) / (v * w) =
      η + gridCompareC * (h : ℝ) / w := by
    rw [add_div]
    have h1 : η * v * w / (v * w) = η := by
      have hrw : η * v * w = η * (v * w) := by ring
      rw [hrw, mul_div_cancel_right₀ η hvw.ne']
    have h2 : gridCompareC * v * (h : ℝ) / (v * w) =
        gridCompareC * (h : ℝ) / w := by
      have hrw : gridCompareC * v * (h : ℝ) =
          v * (gridCompareC * (h : ℝ)) := by ring
      rw [hrw, mul_div_mul_left _ _ hv.ne']
    rw [h1, h2]
  unfold N w at hL hR hdiv
  linarith [hL, hR, hdiv]

/-! ### Complete frames versus the geometric slot `(a,c)` -/

/-- Open geometric slot of a complete frame after deleting rank `j`.
Paper `W_F = (a,c)`. -/
def completeFrameSlot (F : List ℕ) (j : ℕ) : ℕ × ℕ :=
  deletionSlot F j

/-- Occupancy of `A` in the complete-frame slot. -/
def completeFrameOccupancy (A : Finset ℕ) (F : List ℕ) (j : ℕ) : Finset ℕ :=
  slotOccupancy A (deletionSlot F j).1 (deletionSlot F j).2

theorem completeFrameSlot_eq (F : List ℕ) (j : ℕ) :
    completeFrameSlot F j = deletionSlot F j :=
  rfl

theorem completeFrameOccupancy_eq (A : Finset ℕ) (F : List ℕ) (j : ℕ) :
    completeFrameOccupancy A F j =
      slotOccupancy A (completeFrameSlot F j).1 (completeFrameSlot F j).2 :=
  rfl

/-- Neighbours of a strictly increasing complete frame form a genuine
open slot. -/
theorem completeFrameSlot_lt {F : List ℕ} {j : ℕ}
    (hF : F.Pairwise (· < ·)) (hj : j < F.length)
    (h0 : j = 0 → 0 < F[j]) :
    (completeFrameSlot F j).1 < (completeFrameSlot F j).2 := by
  unfold completeFrameSlot
  by_cases hj0 : j = 0
  · subst hj0
    rw [deletionSlot_left_zero, deletionSlot_right_eq hj]
    exact h0 rfl
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hleft := deletionSlot_left_eq_of_pos hjpos
      (Nat.lt_of_le_of_lt (Nat.sub_le j 1) hj)
    have hright := deletionSlot_right_eq hj
    have hlt : F[j - 1] < F[j] :=
      (List.pairwise_iff_getElem.mp hF) (j - 1) j
        (Nat.lt_of_le_of_lt (Nat.sub_le j 1) hj) hj
        (Nat.sub_lt hjpos Nat.zero_lt_one)
    rw [hleft, hright]
    exact hlt

/-- Occupancy of a complete frame versus the geometric slot `(a,c)`.
Paper `lem:gridcompare` denominator, used by uniform reinsertion. -/
theorem complete_frame_occupancy_vs_slot {A : Finset ℕ} {h : ℕ}
    (hh : 0 < h) {v η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hv : 0 < v)
    (hcell : RelativeCellCounts A h v η) (F : List ℕ) (j : ℕ)
    (hlen : (h : ℝ) ≤
      (((deletionSlot F j).2 : ℝ) - (deletionSlot F j).1) / 4) :
    |((completeFrameOccupancy A F j).card : ℝ) -
        v * (((deletionSlot F j).2 : ℝ) - (deletionSlot F j).1)| ≤
      η * v * (((deletionSlot F j).2 : ℝ) - (deletionSlot F j).1) +
        gridCompareC * v * (h : ℝ) :=
  abs_slot_occupancy_sub_geom hh hη hη1 hv hcell hlen

theorem complete_frame_occupancy_ge_quarter {A : Finset ℕ} {h : ℕ}
    (hh : 0 < h) {v η : ℝ} (hη : 0 ≤ η) (hv : 0 < v) (hηlt : η < 1 / 2)
    (hcell : RelativeCellCounts A h v η) (F : List ℕ) (j : ℕ)
    (hlen : (h : ℝ) ≤
      (((deletionSlot F j).2 : ℝ) - (deletionSlot F j).1) / 4) :
    v * (((deletionSlot F j).2 : ℝ) - (deletionSlot F j).1) / 4 ≤
      ((completeFrameOccupancy A F j).card : ℝ) :=
  slot_occupancy_ge_quarter hh hη hv hηlt hcell hlen

/-! ### Cellwise Riemann replacement (resampling) -/

/-- On one cell, freeze the phase at the left endpoint. Paper proof of
`lem:gridcompare`: cost `O(h sup |ψ'|)` per unit mass. -/
theorem cell_sum_sub_rep {A : Finset ℕ} {r h : ℕ} (f : ℕ → ℂ) {δ : ℝ}
    (hf : ∀ u, cell r h u → ‖f u - f (r * h)‖ ≤ δ) :
    ‖∑ u ∈ A.filter (cell r h), f u -
        ((A.filter (cell r h)).card : ℂ) * f (r * h)‖ ≤
      δ * (A.filter (cell r h)).card := by
  set s := A.filter (cell r h)
  have hrew : ∑ u ∈ s, f u - (s.card : ℂ) * f (r * h) =
      ∑ u ∈ s, (f u - f (r * h)) := by
    calc
      ∑ u ∈ s, f u - (s.card : ℂ) * f (r * h)
          = ∑ u ∈ s, f u - ∑ u ∈ s, (fun _ => f (r * h)) u := by
            simp [sum_const, nsmul_eq_mul]
      _ = ∑ u ∈ s, (f u - (fun _ => f (r * h)) u) :=
          (sum_sub_distrib (fun u => f u) (fun _ => f (r * h))).symm
      _ = ∑ u ∈ s, (f u - f (r * h)) := rfl
  rw [hrew]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ u ∈ s, ‖f u - f (r * h)‖ ≤ δ := fun u hu =>
    hf u (mem_filter.mp hu).2
  have hsum := sum_le_sum hterm
  have hδs : ∑ u ∈ s, δ = δ * (s.card : ℝ) := by
    simp [sum_const, nsmul_eq_mul, mul_comm]
  exact hsum.trans_eq hδs

/-- Lipschitz form: variation across a cell of width `h` is at most
`Lip * h`. -/
theorem cell_sum_sub_rep_lip {A : Finset ℕ} {r h : ℕ} (f : ℕ → ℂ)
    {Lip : ℝ} (hLip : 0 ≤ Lip)
    (hf : ∀ u, cell r h u → ‖f u - f (r * h)‖ ≤ Lip * |(u : ℝ) - (r : ℝ) * h|) :
    ‖∑ u ∈ A.filter (cell r h), f u -
        ((A.filter (cell r h)).card : ℂ) * f (r * h)‖ ≤
      Lip * h * (A.filter (cell r h)).card := by
  refine cell_sum_sub_rep (δ := Lip * (h : ℝ)) f fun u hu => ?_
  have hcoord := cell_coord_sub_le hu
  have := hf u hu
  have hmul : Lip * |(u : ℝ) - (r : ℝ) * h| ≤ Lip * (h : ℝ) :=
    mul_le_mul_of_nonneg_left hcoord hLip
  exact this.trans hmul

end PrimeGapNormality.Prime
