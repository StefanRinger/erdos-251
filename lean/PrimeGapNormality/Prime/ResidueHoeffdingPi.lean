import PrimeGapNormality.Prime.ResidueHoeffding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

/-!
# Arbitrary-index reindex of categorical residue Hoeffding

`ResidueHoeffding.PiCoordBoundedDiffOneSided` is the one-sided product
tail on a finite index `ι` (the shape of
`ResidueChoice y = Π_{p≤y} Fin(p-1)`). This leaf is
`piFin_bounded_diff_one_sided` after `Fintype.equivFin ι`. It is not a
Boolean rename and does not encode a `p`-valued coordinate as `log p`
bits. Widths stay `residueWidth = 2(h/p+1)` at the consumer.

Does not repeat the `Fin.snoc` induction.

Source: ResidueHoeffding remaining reindex comment; R106/09 Paket 4.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 800000

/-- Product mass is invariant under reindexing the coordinates. -/
private theorem piCoord_mass_reindex {ι : Type*} [Fintype ι]
    {n : ℕ} (e : ι ≃ Fin n) {α : ι → Type} [∀ i, Fintype (α i)]
    (μ : ∀ i, α i → ℝ) (x : ∀ i, α i) :
    (∏ i, μ i (x i)) =
      piMass (fun (j : Fin n) (a : α (e.symm j)) => μ (e.symm j) a)
        (e.piCongrLeft' α x) := by
  unfold piMass
  refine (Equiv.prod_comp e.symm (fun i => μ i (x i))).symm.trans ?_
  refine prod_congr (s₁ := univ) (s₂ := univ) rfl fun j _ => ?_
  rfl

/-- Mean of `F` equals the `Fin n`-indexed `piExpect` after `piCongrLeft'`. -/
private theorem piCoord_expect_reindex {ι : Type*} [Fintype ι]
    {n : ℕ} (e : ι ≃ Fin n) {α : ι → Type}
    [∀ i, Fintype (α i)] [Fintype (∀ i, α i)]
    (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) :
    ∑ y : (∀ i, α i), (∏ i, μ i (y i)) * F y =
      piExpect (fun (j : Fin n) (a : α (e.symm j)) => μ (e.symm j) a)
        (fun z => F ((e.piCongrLeft' α).symm z)) := by
  unfold piExpect
  refine Eq.trans ?_
    (Equiv.sum_comp (e.piCongrLeft' α)
      (fun z =>
        piMass (fun (j : Fin n) (a : α (e.symm j)) => μ (e.symm j) a) z *
          F ((e.piCongrLeft' α).symm z)))
  refine sum_congr (s₁ := univ) (s₂ := univ) rfl fun y _ => ?_
  rw [piCoord_mass_reindex e μ y, Equiv.symm_apply_apply]

/-- Quadratic form `∑ c i²` is invariant under `e`. -/
private theorem piCoord_sqSum_reindex {ι : Type*} [Fintype ι]
    {n : ℕ} (e : ι ≃ Fin n) (c : ι → ℝ) :
    ∑ i : ι, c i ^ 2 = ∑ j : Fin n, c (e.symm j) ^ 2 :=
  (Equiv.sum_comp e.symm (fun i => c i ^ 2)).symm

/-- Coordinate Lipschitz transports along `piCongrLeft'_symm_update`. -/
private theorem piCoord_lipschitz_reindex {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (e : ι ≃ Fin n) {α : ι → Type} (F : (∀ i, α i) → ℝ) (c : ι → ℝ)
    (hLip : ∀ (x : ∀ i, α i) (i : ι) (a b : α i),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i)
    (y : ∀ j : Fin n, α (e.symm j)) (j : Fin n) (a b : α (e.symm j)) :
    |F ((e.piCongrLeft' α).symm (Function.update y j a)) -
        F ((e.piCongrLeft' α).symm (Function.update y j b))| ≤
      c (e.symm j) := by
  rw [Function.piCongrLeft'_symm_update α e y j a,
    Function.piCongrLeft'_symm_update α e y j b]
  exact hLip ((e.piCongrLeft' α).symm y) (e.symm j) a b

/-- One-sided product tail on an arbitrary finite index: reindex of
`piFin_bounded_diff_one_sided` along `Fintype.equivFin ι`. -/
theorem piCoord_bounded_diff_one_sided {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] [Fintype (∀ i, α i)]
    (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) (c : ι → ℝ) {u : ℝ}
    (hμ0 : ∀ i a, 0 ≤ μ i a)
    (hμ1 : ∀ i, ∑ a : α i, μ i a = 1)
    (hc : ∀ i, 0 ≤ c i)
    (hLip : ∀ (x : ∀ i, α i) (i : ι) (a b : α i),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i)
    (hu : 0 < u) :
    PiCoordBoundedDiffOneSided μ F c u := by
  unfold PiCoordBoundedDiffOneSided
  let e := Fintype.equivFin ι
  let ePi := e.piCongrLeft' α
  let μFin := fun (j : Fin (Fintype.card ι)) (a : α (e.symm j)) =>
    μ (e.symm j) a
  let FFin := fun z => F (ePi.symm z)
  let cFin := fun (j : Fin (Fintype.card ι)) => c (e.symm j)
  have hmass : ∀ x : ∀ i, α i, (∏ i, μ i (x i)) = piMass μFin (ePi x) :=
    fun x => piCoord_mass_reindex e μ x
  have hE :
      ∑ y : (∀ i, α i), (∏ i, μ i (y i)) * F y = piExpect μFin FFin :=
    piCoord_expect_reindex e μ F
  have hσ : ∑ i : ι, c i ^ 2 = ∑ j : Fin (Fintype.card ι), cFin j ^ 2 :=
    piCoord_sqSum_reindex e c
  have hμ0Fin : ∀ j a, 0 ≤ μFin j a := fun j a => hμ0 (e.symm j) a
  have hμ1Fin : ∀ j, ∑ a : α (e.symm j), μFin j a = 1 := fun j => by
    convert hμ1 (e.symm j)
  have hcFin : ∀ j, 0 ≤ cFin j := fun j => hc (e.symm j)
  have hLipFin :
      ∀ (y : ∀ j, α (e.symm j)) (j : Fin (Fintype.card ι))
        (a b : α (e.symm j)),
        |FFin (Function.update y j a) - FFin (Function.update y j b)| ≤
          cFin j :=
    fun y j a b => piCoord_lipschitz_reindex e F c hLip y j a b
  have hfilter :
      ∑ x ∈ univ.filter (fun x : (∀ i, α i) =>
          u ≤ F x - ∑ y : (∀ i, α i), (∏ i, μ i (y i)) * F y),
        (∏ i, μ i (x i))
      = ∑ z ∈ univ.filter (fun z : (∀ j, α (e.symm j)) =>
          u ≤ FFin z - piExpect μFin FFin),
        piMass μFin z := by
    refine Finset.sum_equiv ePi ?_ ?_
    · intro x
      simp only [mem_filter, mem_univ, true_and]
      have hFx : FFin (ePi x) = F x := by
        change F (ePi.symm (ePi x)) = F x
        rw [Equiv.symm_apply_apply]
      apply Iff.of_eq
      rw [hFx, hE]
    · intro x _hx
      exact hmass x
  have htail :=
    piFin_bounded_diff_one_sided μFin FFin cFin hμ0Fin hμ1Fin hcFin hLipFin hu
  rw [hfilter]
  simp only [hσ]
  exact htail

end PrimeGapNormality.Prime
