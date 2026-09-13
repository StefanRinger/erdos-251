import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Physical gaps of a finite periodic survivor set

For an actual sorted nonempty subset of one period, take consecutive
physical distances, including the wraparound distance. Their sum is the
period, and a uniform root has the same gap mean at every successor rank.

This finite cyclic lemma is the combinatorial supplier for the frozen
paper's root-gap mean. Its remaining arithmetic interface is the CRT
identification of `ResidueChoice y` with uniform reduced residues and the
identification of their translated enumeration with `sievePoint`.
-/

open Finset
open scoped BigOperators

namespace PrimeGapNormality.Prime

/-- Physical distance to the next sorted survivor, wrapping once at the last
survivor. `hcard` expresses nonemptiness without an artificial dummy point. -/
noncomputable def coreCyclicPhysicalGap (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (i : Fin (n + 1)) : ℝ :=
  (A.orderEmbOfFin hcard (finRotate (n + 1) i) : ℝ) -
    (A.orderEmbOfFin hcard i : ℝ) + if i = Fin.last n then (P : ℝ) else 0

/-- These really are positive physical distances when the sites belong to
`[0,P)`, including a singleton survivor set and its wrap gap P. -/
theorem coreCyclicPhysicalGap_pos (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) (i : Fin (n + 1)) :
    0 < coreCyclicPhysicalGap P A hcard i := by
  unfold coreCyclicPhysicalGap
  by_cases hi : i = Fin.last n
  · rw [if_pos hi]
    have hx : A.orderEmbOfFin hcard i < P :=
      mem_range.mp (hA (A.orderEmbOfFin_mem hcard i))
    have hx' : (A.orderEmbOfFin hcard i : ℝ) < P := by exact_mod_cast hx
    have hy : (0 : ℝ) ≤ A.orderEmbOfFin hcard (finRotate (n + 1) i) :=
      Nat.cast_nonneg _
    linarith
  · rw [if_neg hi, add_zero]
    apply sub_pos.mpr
    exact_mod_cast (A.orderEmbOfFin hcard).strictMono
      ((lt_finRotate_iff_ne_last i).mpr hi)

/-- Telescoping around the actual sorted survivor cycle gives exactly P. -/
theorem coreCyclicPhysicalGap_sum (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) :
    ∑ i : Fin (n + 1), coreCyclicPhysicalGap P A hcard i = (P : ℝ) := by
  unfold coreCyclicPhysicalGap
  rw [sum_add_distrib, sum_sub_distrib]
  have hperm := Equiv.sum_comp (finRotate (n + 1))
    (fun i : Fin (n + 1) => (A.orderEmbOfFin hcard i : ℝ))
  rw [hperm, sub_self, zero_add]
  simp

/-- Repeated successor steps preserve the total of every test, since the
successor is an explicit permutation of all sorted roots. -/
theorem coreCyclicPhysicalGap_rank_sum (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (r : ℕ) :
    ∑ i : Fin (n + 1),
      coreCyclicPhysicalGap P A hcard ((finRotate (n + 1) ^ r) i) = (P : ℝ) := by
  rw [Equiv.sum_comp (finRotate (n + 1) ^ r)]
  exact coreCyclicPhysicalGap_sum P A hcard

/-- Uniform roots have physical gap mean P/card(A) at every rank.
Neither a mean identity nor rank stationarity is assumed. -/
theorem coreCyclicPhysicalGap_rank_mean (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (r : ℕ) :
    (∑ i : Fin (n + 1),
      coreCyclicPhysicalGap P A hcard ((finRotate (n + 1) ^ r) i)) /
        (A.card : ℝ) = (P : ℝ) / (A.card : ℝ) := by
  rw [coreCyclicPhysicalGap_rank_sum]

end PrimeGapNormality.Prime
