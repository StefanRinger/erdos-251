import PrimeGapNormality.Prime.GridCompare
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Linarith

/-!
# G0c — finite presieve grid (window cells only)

`RelativeCellCounts` quantifies over every `r : ℕ`. For finite `A` and
`η < 1` this is impossible: cells past `max A` have occupancy 0.
Consumers must use the window form `RelativeCellCountsOn` on a prescribed
index set of **full** cells. Pay at most two cells for the paper/Lean
endpoint mismatch: Lean `cell`/`cellIco` is `[rh,(r+1)h)`; the paper uses
`(rh,(r+1)h]`.

This leaf does not import `SieveCellProb`. `RelativeCellCountsOn` here is
the G0c owner; the copy in `SieveCellProb` is a leftover.

R105 G0c.

Source: `rounds/round105/00_grok_repair_priorities.md` G0c;
`GridCompare.cellIco`; paper vs Lean cell endpoints.
Contract: API
Audit: GREEN
-/

open Finset
open scoped symmDiff

namespace PrimeGapNormality.Prime

/-- Relative cell counts on a prescribed index set of full cells. -/
def RelativeCellCountsOn (A : Finset ℕ) (h : ℕ) (v η : ℝ) (R : Finset ℕ) :
    Prop :=
  ∀ r ∈ R, |((A.filter (cell r h)).card : ℝ) - v * h| ≤ η * v * h

/-- Paper cell `(r h, (r + 1) h]`. -/
def cellIoc (r h : ℕ) : Finset ℕ :=
  Ioc (r * h) ((r + 1) * h)

theorem cellIoc_card (r h : ℕ) : (cellIoc r h).card = h := by
  simp [cellIoc, Nat.card_Ioc, Nat.add_mul, Nat.one_mul]

theorem relativeCellCountsOn_of_relativeCellCounts {A : Finset ℕ} {h : ℕ}
    {v η : ℝ} (hcell : RelativeCellCounts A h v η) (R : Finset ℕ) :
    RelativeCellCountsOn A h v η R :=
  fun r _ => hcell r

theorem relativeCellCountsOn_bounds {A : Finset ℕ} {h : ℕ} {v η : ℝ}
    {R : Finset ℕ} {r : ℕ} (hcell : RelativeCellCountsOn A h v η R)
    (hr : r ∈ R) :
    (1 - η) * v * h ≤ ((A.filter (cell r h)).card : ℝ) ∧
      ((A.filter (cell r h)).card : ℝ) ≤ (1 + η) * v * h := by
  have hle := abs_le.mp (hcell r hr)
  exact ⟨by linarith, by linarith⟩

/-- Lean `[rh,(r+1)h)` versus paper `(rh,(r+1)h]`: at most the two
endpoints `{rh}` and `{(r+1)h}`. -/
theorem cellIco_cellIoc_symmDiff_card_le_two (r h : ℕ) :
    ((cellIco r h) ∆ (cellIoc r h)).card ≤ 2 := by
  let a := r * h
  let b := (r + 1) * h
  have hsub :
      (cellIco r h) ∆ (cellIoc r h) ⊆ ({a, b} : Finset ℕ) := by
    intro x hx
    have hx' :
        x ∈ cellIco r h ∧ x ∉ cellIoc r h ∨
          x ∈ cellIoc r h ∧ x ∉ cellIco r h :=
      (mem_symmDiff.mp hx)
    simp only [cellIco, cellIoc, mem_Ico, mem_Ioc, mem_insert, mem_singleton]
      at hx' ⊢
    omega
  exact (card_le_card hsub).trans (card_insert_le _ _)

/-- Full cells of `[0,S)` whose right endpoint stays inside the window.
Partial edge cells are excluded; pay them separately (at most two). -/
def fullPrefixCells (S h : ℕ) : Finset ℕ :=
  if h = 0 then ∅
  else (Ico 0 ((S + h - 1) / h)).filter (fun r => (r + 1) * h ≤ S)

end PrimeGapNormality.Prime
