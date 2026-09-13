import PrimeGapNormality.Prime.ModelConcentration
import PrimeGapNormality.Prime.ModelMoments
import PrimeGapNormality.Prime.EulerProd
import PrimeGapNormality.Prime.GridCompare
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Geometric G-grid cell counts (open CRT/Bonferroni remainder)

`ModelConcentration` left open the CRT / neighbouring-Bonferroni cell
counts that produce `N₀ ≤ (1+o(1)) S̄ V(S̄)`. This module compiles the
purely geometric side, using `GridCompare` occupancy and
`EulerProd.eulerProd` (`V(y) = ∏ (1-1/p)`).

Finite bounds:

* number of width-`h` cells meeting `[0, S)` is `S/h + O(1)`;
* covering cells of `[a, c]` are `(c-a)/h + O(1)`;
* on an `h`-aligned prefix the occupancies sum exactly, hence
  `cellProb` (relative cell counts at density `v`) yields
  `N₀ ≤ (1+η) v S`;
* independent Bernoulli thinning of a full cell has mean `ρ h`, and
  with `ρ = V(h)` this is `h V(h)`.

Not proved: CRT and two neighbouring Bonferroni truncations that
produce `cellProb` with `v = V(S̄)` for the actual presieve; sieve
cutoff `V(y)⁻¹/G → 1`; the full B.2 `Q_j` band (that lives in
`ModelConcentration`).

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:relativegrid),
  (eq:bruncell), (eq:middlemoment);
`GridCompare` occupancy; `EulerProd.eulerProd`;
`ModelMoments.bernoulliThin_choose_moment`.
Contract: API
Audit: GREEN
-/

open Finset

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ### Density hypothesis (`v` is typically paper `V`) -/

/-- Occupancy-versus-density hypothesis on full G-cells: every cell of
width `h` has count `(1+O(η)) v h`. Paper takes `v = V(y) = eulerProd y`.
CRT and neighbouring Bonferroni that produce this for the actual
presieve are not proved here. -/
abbrev cellProb (A : Finset ℕ) (h : ℕ) (v η : ℝ) : Prop :=
  RelativeCellCounts A h v η

/-! ### Prefix cells on `[0, S)` -/

/-- Indices `r` of width-`h` cells that meet `[0, S)`. Empty if `h = 0`.
The count is `⌈S / h⌉`. -/
def prefixCells (S h : ℕ) : Finset ℕ :=
  if h = 0 then ∅ else Ico 0 ((S + h - 1) / h)

/-- Occupancy of `A` in the half-open prefix `[0, S)`. Paper `N₀` on an
aligned window is this cardinality. -/
def prefixOccupancy (A : Finset ℕ) (S : ℕ) : Finset ℕ :=
  A.filter (fun u => u < S)

private theorem nat_div_le_self_div {n h : ℕ} (_hh : 0 < h) :
    ((n / h : ℕ) : ℝ) ≤ (n : ℝ) / (h : ℝ) :=
  Nat.cast_div_le

private theorem nat_div_frac_lt {n h : ℕ} (hh : 0 < h) :
    (n : ℝ) / (h : ℝ) - ((n / h : ℕ) : ℝ) < 1 := by
  have hle : ((n / h : ℕ) : ℝ) ≤ (n : ℝ) / (h : ℝ) := Nat.cast_div_le
  have habs := abs_nat_div_sub_div (n := n) hh
  have hdiff :
      (n : ℝ) / (h : ℝ) - ((n / h : ℕ) : ℝ) =
        |((n / h : ℕ) : ℝ) - (n : ℝ) / (h : ℝ)| := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
  rwa [hdiff]

private theorem lt_prefix_bound_iff {S h r : ℕ} (hh : 0 < h) :
    r < (S + h - 1) / h ↔ r * h < S := by
  have h1 : 1 ≤ h := Nat.succ_le_of_lt hh
  have hSH : S + h - 1 = S + (h - 1) := Nat.add_sub_assoc h1 S
  have hsplit : h = 1 + (h - 1) :=
    (Nat.sub_add_cancel h1).symm.trans (Nat.add_comm (h - 1) 1)
  constructor
  · intro hr
    have hle : r + 1 ≤ (S + h - 1) / h := Nat.succ_le_of_lt hr
    have hmul : (r + 1) * h ≤ S + h - 1 := (Nat.le_div_iff_mul_le hh).mp hle
    have heq : (r + 1) * h = r * h + h := by
      rw [Nat.add_mul, Nat.one_mul]
    have hmul' : r * h + 1 + (h - 1) ≤ S + (h - 1) := by
      have hre : r * h + h = r * h + 1 + (h - 1) :=
        (congrArg (Nat.add (r * h)) hsplit).trans
          (Nat.add_assoc (r * h) 1 (h - 1)).symm
      rw [heq, hre, hSH] at hmul
      exact hmul
    exact Nat.lt_iff_add_one_le.mpr (Nat.le_of_add_le_add_right hmul')
  · intro hr
    have hle' : r * h + 1 ≤ S := Nat.lt_iff_add_one_le.mp hr
    have hmul : (r + 1) * h ≤ S + h - 1 := by
      have heq : (r + 1) * h = r * h + h := by
        rw [Nat.add_mul, Nat.one_mul]
      have hre : r * h + h = r * h + 1 + (h - 1) :=
        (congrArg (Nat.add (r * h)) hsplit).trans (Nat.add_assoc (r * h) 1 (h - 1)).symm
      rw [heq, hSH, hre]
      exact Nat.add_le_add_right hle' (h - 1)
    exact Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le hh).mpr hmul)

theorem mem_prefixCells_iff {S h r : ℕ} (hh : 0 < h) :
    r ∈ prefixCells S h ↔ r * h < S := by
  have hne : h ≠ 0 := Nat.ne_zero_of_lt hh
  constructor
  · intro hr
    rw [prefixCells, if_neg hne, mem_Ico] at hr
    exact (lt_prefix_bound_iff hh).mp hr.2
  · intro hr
    rw [prefixCells, if_neg hne, mem_Ico]
    exact ⟨Nat.zero_le r, (lt_prefix_bound_iff hh).mpr hr⟩

theorem prefixCells_card {S h : ℕ} (hh : 0 < h) :
    (prefixCells S h).card = (S + h - 1) / h := by
  have hne : h ≠ 0 := Nat.ne_zero_of_lt hh
  rw [prefixCells, if_neg hne, Nat.card_Ico, Nat.sub_zero]

private theorem prefix_div_eq {S h : ℕ} (hh : 0 < h) :
    (S + h - 1) / h = S / h + if S % h = 0 then 0 else 1 := by
  have h1 : 1 ≤ h := Nat.succ_le_of_lt hh
  generalize hq : S / h = q
  generalize hm : S % h = m
  by_cases hr : m = 0
  · have hS : S = h * q := by
      have hmod := Nat.div_add_mod S h
      rw [hq, hm, hr, add_zero] at hmod
      exact hmod.symm
    have hsum : S + h - 1 = (h - 1) + q * h := by
      rw [hS]
      have hassoc : h * q + h - 1 = h * q + (h - 1) :=
        Nat.add_sub_assoc h1 (h * q)
      rw [hassoc, Nat.mul_comm h q, Nat.add_comm]
    rw [hsum, Nat.add_mul_div_right (h - 1) q hh]
    have : (h - 1) / h = 0 :=
      Nat.div_eq_of_lt (Nat.sub_lt hh Nat.zero_lt_one)
    rw [this, Nat.zero_add, if_pos hr, Nat.add_zero]
  · have hmod1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr)
    have hsum : S + h - 1 = (m - 1) + (q + 1) * h := by
      have hmodh : 1 ≤ m + h :=
        Nat.le_trans h1 (Nat.le_add_left h m)
      have hdecomp : S = h * q + m := by
        have hmod := Nat.div_add_mod S h
        rw [hq, hm] at hmod
        exact hmod.symm
      rw [hdecomp]
      calc
        h * q + m + h - 1
            = h * q + (m + h - 1) := by
              rw [Nat.add_assoc, Nat.add_sub_assoc hmodh]
        _ = h * q + (h + (m - 1)) := by
              rw [Nat.add_comm m h, Nat.add_sub_assoc hmod1]
        _ = q * h + h + (m - 1) := by
              rw [← Nat.add_assoc, Nat.mul_comm]
        _ = (q + 1) * h + (m - 1) := by
              have hfac : q * h + h = (q + 1) * h := by
                rw [Nat.add_mul, Nat.one_mul]
              rw [hfac]
        _ = (m - 1) + (q + 1) * h := Nat.add_comm _ _
    rw [hsum, Nat.add_mul_div_right (m - 1) (q + 1) hh]
    have hlt : m - 1 < h :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by rw [← hm]; exact Nat.mod_lt S hh)
    have : (m - 1) / h = 0 := Nat.div_eq_of_lt hlt
    rw [this, Nat.zero_add, if_neg hr]

private theorem prefix_real_div {S h : ℕ} (hh : 0 < h) :
    (S : ℝ) / (h : ℝ) =
      ((S / h : ℕ) : ℝ) + ((S % h : ℕ) : ℝ) / (h : ℝ) := by
  have hh0 : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr hh
  have hhne : (h : ℝ) ≠ 0 := hh0.ne'
  have hdecomp : (S : ℝ) =
      (h : ℝ) * ((S / h : ℕ) : ℝ) + ((S % h : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod S h).symm
  calc
    (S : ℝ) / (h : ℝ)
        = ((h : ℝ) * ((S / h : ℕ) : ℝ) + ((S % h : ℕ) : ℝ)) / (h : ℝ) := by
          rw [hdecomp]
    _ = ((h : ℝ) * ((S / h : ℕ) : ℝ)) / (h : ℝ) +
          ((S % h : ℕ) : ℝ) / (h : ℝ) := add_div _ _ _
    _ = ((S / h : ℕ) : ℝ) + ((S % h : ℕ) : ℝ) / (h : ℝ) := by
          rw [mul_div_cancel_left₀ _ hhne]

/-- Number of G-grid cells meeting an interval of length `S` is
`S/h + O(1)` (strictly `|·| < 1`). -/
theorem abs_prefix_cell_count_sub_div {S h : ℕ} (hh : 0 < h) :
    |((prefixCells S h).card : ℝ) - (S : ℝ) / (h : ℝ)| < 1 := by
  have hh0 : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr hh
  rw [prefixCells_card hh, prefix_div_eq hh, prefix_real_div hh]
  by_cases hr : S % h = 0
  · rw [if_pos hr, Nat.add_zero, hr, Nat.cast_zero, zero_div, add_zero, sub_self,
      abs_zero]
    exact zero_lt_one
  · rw [if_neg hr]
    have hrpos : (0 : ℝ) < ((S % h : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
    have hrlt : ((S % h : ℕ) : ℝ) < (h : ℝ) :=
      Nat.cast_lt.mpr (Nat.mod_lt S hh)
    have hfracpos : 0 < ((S % h : ℕ) : ℝ) / (h : ℝ) := div_pos hrpos hh0
    have hfraclt : ((S % h : ℕ) : ℝ) / (h : ℝ) < 1 :=
      (div_lt_one hh0).mpr hrlt
    have hdiff :
        ((S / h + 1 : ℕ) : ℝ) -
            (((S / h : ℕ) : ℝ) + ((S % h : ℕ) : ℝ) / (h : ℝ)) =
          1 - ((S % h : ℕ) : ℝ) / (h : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [hdiff, abs_of_nonneg (sub_nonneg.mpr hfraclt.le)]
    linarith [hfracpos]

theorem prefixCells_card_of_dvd {S h : ℕ} (hh : 0 < h) (hS : h ∣ S) :
    (prefixCells S h).card = S / h := by
  have hr : S % h = 0 := Nat.dvd_iff_mod_eq_zero.mp hS
  rw [prefixCells_card hh, prefix_div_eq hh, hr, if_pos rfl, Nat.add_zero]

theorem prefixCells_card_eq_div {S h : ℕ} (hh : 0 < h) (hS : h ∣ S) :
    ((prefixCells S h).card : ℝ) = (S : ℝ) / (h : ℝ) := by
  have hhne : (h : ℝ) ≠ 0 := (Nat.cast_pos.mpr hh).ne'
  rw [prefixCells_card_of_dvd hh hS, Nat.cast_div hS hhne]

/-! ### Covering cells of a closed integer interval -/

/-- Cells of width `h` whose index range covers `[a, c]` in the G-grid. -/
def coveringCells (a c h : ℕ) : Finset ℕ :=
  Icc (a / h) (c / h)

theorem coveringCells_card {a c h : ℕ} (_hac : a ≤ c) :
    (coveringCells a c h).card = c / h + 1 - a / h := by
  rw [coveringCells, Nat.card_Icc]

/-- Covering cells of an interval of length `c - a` versus geometric
length `/ h`. At most two cells of discrepancy. -/
theorem abs_covering_cell_count_sub_div {a c h : ℕ} (hh : 0 < h)
    (hac : a ≤ c) :
    |((coveringCells a c h).card : ℝ) - ((c : ℝ) - (a : ℝ)) / (h : ℝ)| ≤ 2 := by
  have hdiv : a / h ≤ c / h := Nat.div_le_div_right hac
  have hle : a / h ≤ c / h + 1 := Nat.le_succ_of_le hdiv
  have hcard : ((coveringCells a c h).card : ℝ) =
      ((c / h : ℕ) : ℝ) - ((a / h : ℕ) : ℝ) + 1 := by
    rw [coveringCells, Nat.card_Icc, Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
    ring
  have hsplit : ((c : ℝ) - (a : ℝ)) / (h : ℝ) =
      (c : ℝ) / (h : ℝ) - (a : ℝ) / (h : ℝ) :=
    (div_sub_div_same (c : ℝ) (a : ℝ) (h : ℝ)).symm
  have hcle := nat_div_le_self_div (n := c) hh
  have hale := nat_div_le_self_div (n := a) hh
  have hcx : (c : ℝ) / (h : ℝ) - ((c / h : ℕ) : ℝ) < 1 := nat_div_frac_lt hh
  have hax : (a : ℝ) / (h : ℝ) - ((a / h : ℕ) : ℝ) < 1 := nat_div_frac_lt hh
  have hexpr :
      ((coveringCells a c h).card : ℝ) - ((c : ℝ) - (a : ℝ)) / (h : ℝ) =
        1 - ((c : ℝ) / (h : ℝ) - ((c / h : ℕ) : ℝ)) +
          ((a : ℝ) / (h : ℝ) - ((a / h : ℕ) : ℝ)) := by
    rw [hcard, hsplit]
    ring
  have hfracc : 0 ≤ (c : ℝ) / (h : ℝ) - ((c / h : ℕ) : ℝ) := sub_nonneg.mpr hcle
  have hfraca : 0 ≤ (a : ℝ) / (h : ℝ) - ((a / h : ℕ) : ℝ) := sub_nonneg.mpr hale
  have hup :
      1 - ((c : ℝ) / (h : ℝ) - ((c / h : ℕ) : ℝ)) +
          ((a : ℝ) / (h : ℝ) - ((a / h : ℕ) : ℝ)) ≤ 2 := by
    linarith [hfracc, hax.le]
  have hdn :
      -2 ≤ 1 - ((c : ℝ) / (h : ℝ) - ((c / h : ℕ) : ℝ)) +
          ((a : ℝ) / (h : ℝ) - ((a / h : ℕ) : ℝ)) := by
    linarith [hcx.le, hfraca]
  rw [hexpr]
  exact abs_le.mpr ⟨hdn, hup⟩

/-! ### Aligned partition of `[0, S)` -/

theorem cellIco_subset_range_of_mem_prefix {S h r : ℕ} (hh : 0 < h)
    (hS : h ∣ S) (hr : r ∈ prefixCells S h) :
    cellIco r h ⊆ range S := by
  intro u hu
  have hr' : r < S / h := by
    have hne : h ≠ 0 := Nat.ne_zero_of_lt hh
    rw [prefixCells, if_neg hne, mem_Ico] at hr
    have heq : (S + h - 1) / h = S / h :=
      (prefixCells_card hh).symm.trans (prefixCells_card_of_dvd hh hS)
    have hr2 := hr.2
    rwa [heq] at hr2
  have hbound : (r + 1) * h ≤ S := by
    have : r + 1 ≤ S / h := Nat.succ_le_of_lt hr'
    have hmul := Nat.mul_le_mul_right h this
    rwa [Nat.div_mul_cancel hS] at hmul
  rw [cellIco, mem_Ico] at hu
  exact mem_range.mpr (hu.2.trans_le hbound)

theorem prefixOccupancy_subset_biUnion {A : Finset ℕ} {S h : ℕ}
    (hh : 0 < h) :
    prefixOccupancy A S ⊆
      (prefixCells S h).biUnion (fun r => A.filter (cell r h)) := by
  intro u hu
  have ⟨huA, huS⟩ := mem_filter.mp hu
  have hcellu : cell (u / h) h u := cell_div hh
  have hr : u / h ∈ prefixCells S h :=
    (mem_prefixCells_iff hh).mpr
      (lt_of_le_of_lt (Nat.div_mul_le_self u h) huS)
  exact mem_biUnion.mpr ⟨u / h, hr, mem_filter.mpr ⟨huA, hcellu⟩⟩

theorem prefixOccupancy_eq_biUnion_of_dvd {A : Finset ℕ} {S h : ℕ}
    (hh : 0 < h) (hS : h ∣ S) :
    prefixOccupancy A S =
      (prefixCells S h).biUnion (fun r => A.filter (cell r h)) := by
  apply Subset.antisymm (prefixOccupancy_subset_biUnion hh)
  intro u hu
  obtain ⟨r, hr, huA⟩ := mem_biUnion.mp hu
  have ⟨hA, hcell⟩ := mem_filter.mp huA
  have huI : u ∈ cellIco r h :=
    (mem_cell_iff r h u).mp hcell
  have huR : u ∈ range S := cellIco_subset_range_of_mem_prefix hh hS hr huI
  exact mem_filter.mpr ⟨hA, mem_range.mp huR⟩

theorem prefixOccupancy_card_eq_sum {A : Finset ℕ} {S h : ℕ}
    (hh : 0 < h) (hS : h ∣ S) :
    (prefixOccupancy A S).card =
      ∑ r ∈ prefixCells S h, (A.filter (cell r h)).card := by
  rw [prefixOccupancy_eq_biUnion_of_dvd hh hS]
  exact card_biUnion (cell_pairwise_disjoint A h _)

/-! ### Occupancy from `cellProb` -/

/-- On an `h`-aligned prefix, `cellProb` gives `N₀ ≤ (1+η) v S`. -/
theorem prefixOccupancy_le_of_cellProb {A : Finset ℕ} {S h : ℕ} {v η : ℝ}
    (hh : 0 < h) (hS : h ∣ S) (hη : 0 ≤ η) (hv : 0 ≤ v)
    (hcell : cellProb A h v η) :
    ((prefixOccupancy A S).card : ℝ) ≤ (1 + η) * v * S := by
  have hsum := prefixOccupancy_card_eq_sum (A := A) hh hS
  have hterm : ∀ r ∈ prefixCells S h,
      ((A.filter (cell r h)).card : ℝ) ≤ (1 + η) * v * h := fun r _ =>
    (relativeCellCounts_bounds hcell).2
  have hle :
      ∑ r ∈ prefixCells S h, ((A.filter (cell r h)).card : ℝ) ≤
        ∑ r ∈ prefixCells S h, (1 + η) * v * h :=
    sum_le_sum hterm
  have hconst :
      ∑ r ∈ prefixCells S h, (1 + η) * v * h =
        (1 + η) * v * h * (prefixCells S h).card := by
    simp only [sum_const, nsmul_eq_mul]
    ring
  have hcast : ((prefixOccupancy A S).card : ℝ) =
      ∑ r ∈ prefixCells S h, ((A.filter (cell r h)).card : ℝ) := by
    rw [hsum]
    exact Nat.cast_sum _ _
  have hnum := prefixCells_card_eq_div hh hS
  have hh0 : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr hh
  have hprod : (1 + η) * v * h * (prefixCells S h).card =
      (1 + η) * v * S := by
    calc
      (1 + η) * v * h * (prefixCells S h).card
          = (1 + η) * v * (h : ℝ) * ((S : ℝ) / (h : ℝ)) := by rw [hnum]
      _ = (1 + η) * v * ((h : ℝ) * ((S : ℝ) / (h : ℝ))) := by ring
      _ = (1 + η) * v * S := by rw [mul_div_cancel₀ _ hh0.ne']
  calc
    ((prefixOccupancy A S).card : ℝ)
        = ∑ r ∈ prefixCells S h, ((A.filter (cell r h)).card : ℝ) := hcast
    _ ≤ ∑ r ∈ prefixCells S h, (1 + η) * v * h := hle
    _ = (1 + η) * v * h * (prefixCells S h).card := hconst
    _ = (1 + η) * v * S := hprod

/-- Matching lower bound on an aligned prefix, once `η ≤ 1`. -/
theorem prefixOccupancy_ge_of_cellProb {A : Finset ℕ} {S h : ℕ} {v η : ℝ}
    (hh : 0 < h) (hS : h ∣ S) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hv : 0 ≤ v)
    (hcell : cellProb A h v η) :
    (1 - η) * v * S ≤ ((prefixOccupancy A S).card : ℝ) := by
  have hsum := prefixOccupancy_card_eq_sum (A := A) hh hS
  have hterm : ∀ r ∈ prefixCells S h,
      (1 - η) * v * h ≤ ((A.filter (cell r h)).card : ℝ) := fun r _ =>
    (relativeCellCounts_bounds hcell).1
  have hge :
      ∑ r ∈ prefixCells S h, (1 - η) * v * h ≤
        ∑ r ∈ prefixCells S h, ((A.filter (cell r h)).card : ℝ) :=
    sum_le_sum hterm
  have hconst :
      ∑ r ∈ prefixCells S h, (1 - η) * v * h =
        (1 - η) * v * h * (prefixCells S h).card := by
    simp only [sum_const, nsmul_eq_mul]
    ring
  have hcast : ((prefixOccupancy A S).card : ℝ) =
      ∑ r ∈ prefixCells S h, ((A.filter (cell r h)).card : ℝ) := by
    rw [hsum]
    exact Nat.cast_sum _ _
  have hnum := prefixCells_card_eq_div hh hS
  have hh0 : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr hh
  have hprod : (1 - η) * v * h * (prefixCells S h).card =
      (1 - η) * v * S := by
    calc
      (1 - η) * v * h * (prefixCells S h).card
          = (1 - η) * v * (h : ℝ) * ((S : ℝ) / (h : ℝ)) := by rw [hnum]
      _ = (1 - η) * v * ((h : ℝ) * ((S : ℝ) / (h : ℝ))) := by ring
      _ = (1 - η) * v * S := by rw [mul_div_cancel₀ _ hh0.ne']
  calc
    (1 - η) * v * S
        = (1 - η) * v * h * (prefixCells S h).card := hprod.symm
    _ = ∑ r ∈ prefixCells S h, (1 - η) * v * h := hconst.symm
    _ ≤ ∑ r ∈ prefixCells S h, ((A.filter (cell r h)).card : ℝ) := hge
    _ = ((prefixOccupancy A S).card : ℝ) := hcast.symm

theorem abs_prefixOccupancy_sub_geom {A : Finset ℕ} {S h : ℕ} {v η : ℝ}
    (hh : 0 < h) (hS : h ∣ S) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hv : 0 ≤ v)
    (hcell : cellProb A h v η) :
    |((prefixOccupancy A S).card : ℝ) - v * S| ≤ η * v * S := by
  have hle := prefixOccupancy_le_of_cellProb hh hS hη hv hcell
  have hge := prefixOccupancy_ge_of_cellProb hh hS hη hη1 hv hcell
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [hge]
  · linarith [hle]

/-- Unaligned prefix: at most one extra cell, hence an `O(v h)` remainder. -/
theorem prefixOccupancy_le_of_cellProb_add {A : Finset ℕ} {S h : ℕ} {v η : ℝ}
    (hh : 0 < h) (hη : 0 ≤ η) (hv : 0 ≤ v)
    (hcell : cellProb A h v η) :
    ((prefixOccupancy A S).card : ℝ) ≤
      (1 + η) * v * S + (1 + η) * v * h := by
  have hsub := prefixOccupancy_subset_biUnion (A := A) (S := S) hh
  have hcard : ((prefixOccupancy A S).card : ℝ) ≤
      (((prefixCells S h).biUnion (fun r => A.filter (cell r h))).card : ℝ) :=
    Nat.cast_le.mpr (card_le_card hsub)
  have hbu :
      ((((prefixCells S h).biUnion (fun r => A.filter (cell r h))).card : ℝ)) ≤
        ∑ r ∈ prefixCells S h, ((A.filter (cell r h)).card : ℝ) := by
    have hnat :=
      card_biUnion_le (s := prefixCells S h)
        (t := fun r => A.filter (cell r h))
    have hcast :
        ((∑ r ∈ prefixCells S h, (A.filter (cell r h)).card : ℕ) : ℝ) =
          ∑ r ∈ prefixCells S h, ((A.filter (cell r h)).card : ℝ) :=
      Nat.cast_sum _ _
    exact (Nat.cast_le.mpr hnat).trans_eq hcast
  have hterm : ∀ r ∈ prefixCells S h,
      ((A.filter (cell r h)).card : ℝ) ≤ (1 + η) * v * h := fun r _ =>
    (relativeCellCounts_bounds hcell).2
  have hsum :
      ∑ r ∈ prefixCells S h, ((A.filter (cell r h)).card : ℝ) ≤
        ∑ r ∈ prefixCells S h, (1 + η) * v * h :=
    sum_le_sum hterm
  have hconst :
      ∑ r ∈ prefixCells S h, (1 + η) * v * h =
        (1 + η) * v * h * (prefixCells S h).card := by
    simp only [sum_const, nsmul_eq_mul]
    ring
  have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hcells : ((prefixCells S h).card : ℝ) < (S : ℝ) / h + 1 := by
    have habs := abs_prefix_cell_count_sub_div (S := S) hh
    have : ((prefixCells S h).card : ℝ) - (S : ℝ) / h < 1 :=
      (abs_lt.mp habs).2
    linarith
  have hη0 : 0 ≤ 1 + η := add_nonneg (by norm_num) hη
  have hfac : 0 ≤ (1 + η) * v := mul_nonneg hη0 hv
  have hfac' : 0 ≤ (1 + η) * v * h := mul_nonneg hfac (Nat.cast_nonneg _)
  have hmul :
      (1 + η) * v * h * (prefixCells S h).card ≤
        (1 + η) * v * h * ((S : ℝ) / h + 1) :=
    mul_le_mul_of_nonneg_left hcells.le hfac'
  have hsimp : (1 + η) * v * h * ((S : ℝ) / h + 1) =
      (1 + η) * v * S + (1 + η) * v * h := by
    have hcancel : (h : ℝ) * ((S : ℝ) / (h : ℝ) + 1) =
        (S : ℝ) + (h : ℝ) := by
      rw [mul_add, mul_div_cancel₀ _ hh0.ne', mul_one]
    calc
      (1 + η) * v * h * ((S : ℝ) / h + 1)
          = (1 + η) * v * ((h : ℝ) * ((S : ℝ) / (h : ℝ) + 1)) := by ring
      _ = (1 + η) * v * ((S : ℝ) + (h : ℝ)) := by rw [hcancel]
      _ = (1 + η) * v * S + (1 + η) * v * h := by ring
  linarith [hcard, hbu, hsum, hconst, hmul, hsimp]

/-! ### Bernoulli occupancy versus `V(h)` -/

theorem eulerProdNat_le_one (n : ℕ) : eulerProdNat n ≤ 1 := by
  have h0 : eulerProdNat 0 = 1 := by
    rw [eulerProdNat, Nat.primesLE_zero, prod_empty]
  exact (eulerProdNat_mono (Nat.zero_le n)).trans_eq h0

theorem eulerProd_le_one (y : ℝ) : eulerProd y ≤ 1 :=
  eulerProdNat_le_one _

/-- Exact independent mean occupancy: `E[|B|] = ρ |A|`. -/
theorem bernoulliThin_occupancy_expect (A : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∑ B ∈ A.powerset, bernoulliThin A ρ hρ0 hρ1 B * (B.card : ℝ)
      = ρ * A.card := by
  have h := bernoulliThin_choose_moment A hρ0 hρ1 1
  have hL :
      ∑ B ∈ A.powerset, bernoulliThin A ρ hρ0 hρ1 B * (B.card.choose 1 : ℝ) =
        ∑ B ∈ A.powerset, bernoulliThin A ρ hρ0 hρ1 B * (B.card : ℝ) :=
    sum_congr rfl fun B _ => by simp [Nat.choose_one_right]
  have hR : ρ ^ 1 * (A.card.choose 1 : ℝ) = ρ * A.card := by
    simp [Nat.choose_one_right]
  rw [← hL, h, hR]

theorem bernoulliThin_cell_occupancy_expect {r h : ℕ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∑ B ∈ (cellIco r h).powerset,
        bernoulliThin (cellIco r h) ρ hρ0 hρ1 B * (B.card : ℝ)
      = ρ * h := by
  rw [bernoulliThin_occupancy_expect, cellIco_card]

/-- Bernoulli/presieve comparison against paper `V(y)`. -/
theorem bernoulliThin_cell_occupancy_eulerProd (r h : ℕ) (y : ℝ) :
    ∑ B ∈ (cellIco r h).powerset,
        bernoulliThin (cellIco r h) (eulerProd y)
          (eulerProd_pos y).le (eulerProd_le_one y) B * (B.card : ℝ)
      = eulerProd y * h :=
  bernoulliThin_cell_occupancy_expect (eulerProd_pos y).le (eulerProd_le_one y)

/-- Bernoulli occupancy of a width-`h` cell versus `V(h)`. -/
theorem bernoulliThin_cell_occupancy_V_width (r h : ℕ) :
    ∑ B ∈ (cellIco r h).powerset,
        bernoulliThin (cellIco r h) (eulerProd h)
          (eulerProd_pos h).le (eulerProd_le_one h) B * (B.card : ℝ)
      = eulerProd h * h :=
  bernoulliThin_cell_occupancy_eulerProd r h h

/-! ### Paper `S̄` packaging -/

theorem modelCellWidth_eq_gridWidth (G : ℝ) :
    modelCellWidth G = gridWidth G :=
  rfl

theorem modelCellWidth_dvd_modelSpanBar {L : ℕ} {G : ℝ} (hG : 1 ≤ G) :
    modelCellWidth G ∣ modelSpanBar L G := by
  have hpos : 1 ≤ modelCellWidth G := modelCellWidth_pos hG
  have hne : modelCellWidth G ≠ 0 := Nat.ne_zero_of_lt (Nat.succ_le_iff.mp hpos)
  have heq : modelSpanBar L G =
      modelCellWidth G * ⌈((4 : ℝ) * L * G / (modelCellWidth G : ℝ))⌉₊ := by
    simp [modelSpanBar, hne]
  rw [heq]
  exact Nat.dvd_mul_right _ _

theorem prefixCells_modelSpanBar {L : ℕ} {G : ℝ} (hG : 1 ≤ G) :
    (prefixCells (modelSpanBar L G) (modelCellWidth G)).card =
      modelSpanBar L G / modelCellWidth G :=
  prefixCells_card_of_dvd
    (Nat.succ_le_iff.mp (modelCellWidth_pos hG))
    (modelCellWidth_dvd_modelSpanBar hG)

/-- Aligned G-grid on the paper window: exactly `S̄ / h` cells. -/
theorem prefixCells_modelSpanBar_eq_div {L : ℕ} {G : ℝ} (hG : 1 ≤ G) :
    ((prefixCells (modelSpanBar L G) (modelCellWidth G)).card : ℝ) =
      (modelSpanBar L G : ℝ) / modelCellWidth G :=
  prefixCells_card_eq_div
    (Nat.succ_le_iff.mp (modelCellWidth_pos hG))
    (modelCellWidth_dvd_modelSpanBar hG)

/-- Finite form of `N₀ ≤ (1+η) S̄ v` on the paper window. -/
theorem occupancy_le_spanBar {A : Finset ℕ} {L : ℕ} {G v η : ℝ}
    (hG : 1 ≤ G) (hη : 0 ≤ η) (hv : 0 ≤ v)
    (hcell : cellProb A (modelCellWidth G) v η) :
    ((prefixOccupancy A (modelSpanBar L G)).card : ℝ) ≤
      (1 + η) * v * modelSpanBar L G :=
  prefixOccupancy_le_of_cellProb
    (Nat.succ_le_iff.mp (modelCellWidth_pos hG))
    (modelCellWidth_dvd_modelSpanBar hG) hη hv hcell

/-- Finite form of `N₀ ≤ (1+η) S̄ V(S̄)`, with density `cellProb`.
CRT/Bonferroni producing that hypothesis are not proved here. -/
theorem occupancy_le_spanBar_eulerProd {A : Finset ℕ} {L : ℕ} {G η : ℝ}
    (hG : 1 ≤ G) (hη : 0 ≤ η)
    (hcell : cellProb A (modelCellWidth G)
      (eulerProd (modelSpanBar L G)) η) :
    ((prefixOccupancy A (modelSpanBar L G)).card : ℝ) ≤
      (1 + η) * eulerProd (modelSpanBar L G) * modelSpanBar L G :=
  occupancy_le_spanBar hG hη (eulerProd_pos _).le hcell

/-- Geometric slot occupancy versus `v (c-a)`, from `GridCompare`.
Requires `h ≤ (c-a)/4`. -/
theorem slot_occupancy_le_of_cellProb {A : Finset ℕ} {h : ℕ} (hh : 0 < h)
    {v η : ℝ} (hη : 0 ≤ η) (hv : 0 < v) (hcell : cellProb A h v η)
    {a c : ℕ} (hlen : (h : ℝ) ≤ ((c : ℝ) - a) / 4) :
    ((slotOccupancy A a c).card : ℝ) ≤
      (1 + η) * v * (((c : ℝ) - a) + 2 * (h : ℝ)) :=
  slot_occupancy_le hh hη hv hcell hlen

end PrimeGapNormality.Prime
