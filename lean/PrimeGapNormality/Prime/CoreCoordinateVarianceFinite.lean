import PrimeGapNormality.Prime.CoreCoordinateVariance
import Mathlib.Data.Fintype.EquivFin

namespace PrimeGapNormality.Prime

open Finset
open scoped Classical

set_option maxHeartbeats 800000

/-- Chebyshev for the actual mass of a finite two-sided deviation event. -/
theorem finVariance_deviation_mass_le {Ω : Type*} [Fintype Ω]
    (μ F : Ω → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) {t : ℝ} (ht : 0 < t) :
    (∑ x ∈ univ.filter (fun x => t ≤ |F x - finExpect μ F|), μ x) ≤
      finVariance μ F / t ^ 2 := by
  have hs : (∑ x ∈ univ.filter (fun x => t ≤ |F x - finExpect μ F|), μ x) * t ^ 2
      ≤ finVariance μ F := by
    rw [sum_mul]
    calc
      _ ≤ ∑ x ∈ univ.filter (fun x => t ≤ |F x - finExpect μ F|),
          μ x * (F x - finExpect μ F) ^ 2 := by
        apply sum_le_sum
        intro x hx
        apply mul_le_mul_of_nonneg_left _ (hμ0 x)
        have hx := (mem_filter.mp hx).2
        have hsq := sq_le_sq₀ ht.le (abs_nonneg (F x - finExpect μ F))
        simpa only [sq_abs] using hsq.mpr hx
      _ ≤ finVariance μ F := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro x _ _
        exact mul_nonneg (hμ0 x) (sq_nonneg _)
  exact (le_div_iff₀ (sq_pos_of_pos ht)).mpr hs

/-- The exact finite-coordinate quarter-variance inequality, on any finite index type. -/
theorem piCoord_centered_square_le_quarter {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] [Fintype (∀ i, α i)]
    (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) (c : ι → ℝ)
    (hμ0 : ∀ i a, 0 ≤ μ i a) (hμ1 : ∀ i, ∑ a : α i, μ i a = 1)
    (hc : ∀ i, 0 ≤ c i)
    (hLip : ∀ (x : ∀ i, α i) (i : ι) (a b : α i),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i) :
    (∑ x : (∀ i, α i), (∏ i, μ i (x i)) *
      (F x - ∑ y : (∀ i, α i), (∏ i, μ i (y i)) * F y) ^ 2) ≤
      (∑ i : ι, c i ^ 2) / 4 := by
  let e := Fintype.equivFin ι
  let ePi := e.piCongrLeft' α
  let μ' := fun (j : Fin (Fintype.card ι)) (a : α (e.symm j)) => μ (e.symm j) a
  let F' := fun z => F (ePi.symm z)
  have hmass : ∀ x : ∀ i, α i, (∏ i, μ i (x i)) = piMass μ' (ePi x) := by
    intro x
    unfold piMass
    exact (Equiv.prod_comp e.symm (fun i => μ i (x i))).symm
  have hmean : (∑ x : (∀ i, α i), (∏ i, μ i (x i)) * F x) = piExpect μ' F' := by
    unfold piExpect
    refine Eq.trans ?_ (Equiv.sum_comp ePi (fun z => piMass μ' z * F' z))
    apply sum_congr rfl
    intro x _
    rw [hmass]
    simp [F']
  have hvar :
      (∑ x : (∀ i, α i), (∏ i, μ i (x i)) *
        (F x - ∑ y : (∀ i, α i), (∏ i, μ i (y i)) * F y) ^ 2) =
        piVariance μ' F' := by
    rw [hmean]
    change _ = ∑ z, piMass μ' z * (F' z - piExpect μ' F') ^ 2
    refine Eq.trans ?_ (Equiv.sum_comp ePi
      (fun z => piMass μ' z * (F' z - piExpect μ' F') ^ 2))
    apply sum_congr rfl
    intro x _
    rw [hmass]
    simp [F']
  have hLip' : ∀ (y : ∀ j, α (e.symm j)) (j : Fin (Fintype.card ι))
      (a b : α (e.symm j)),
      |F' (Function.update y j a) - F' (Function.update y j b)| ≤ c (e.symm j) := by
    intro y j a b
    dsimp [F', ePi]
    rw [Function.piCongrLeft'_symm_update α e y j a,
      Function.piCongrLeft'_symm_update α e y j b]
    exact hLip _ _ a b
  rw [hvar, ← Equiv.sum_comp e.symm (fun i => c i ^ 2)]
  exact piFin_bounded_diff_variance _ _ μ' F' (fun j => c (e.symm j))
    (fun j a => hμ0 (e.symm j) a) (fun j => hμ1 (e.symm j))
    (fun j => hc (e.symm j)) hLip'

/-- Two-sided polynomial tail with the same exact quarter constant. -/
theorem piCoord_deviation_mass_le_quarter {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] [Fintype (∀ i, α i)]
    (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) (c : ι → ℝ)
    (hμ0 : ∀ i a, 0 ≤ μ i a) (hμ1 : ∀ i, ∑ a : α i, μ i a = 1)
    (hc : ∀ i, 0 ≤ c i)
    (hLip : ∀ (x : ∀ i, α i) (i : ι) (a b : α i),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i)
    {t : ℝ} (ht : 0 < t) :
    (∑ x ∈ univ.filter (fun x : (∀ i, α i) =>
        t ≤ |F x - ∑ y : (∀ i, α i), (∏ i, μ i (y i)) * F y|),
      (∏ i, μ i (x i))) ≤ (∑ i : ι, c i ^ 2) / (4 * t ^ 2) := by
  have hcheb := finVariance_deviation_mass_le (fun x : ∀ i, α i => ∏ i, μ i (x i)) F
    (fun x => prod_nonneg fun i _ => hμ0 i (x i)) ht
  have hvar := piCoord_centered_square_le_quarter μ F c hμ0 hμ1 hc hLip
  have hdiv := div_le_div_of_nonneg_right hvar (sq_nonneg t)
  have hden : ((∑ i : ι, c i ^ 2) / 4) / t ^ 2 =
      (∑ i : ι, c i ^ 2) / (4 * t ^ 2) := by rw [div_div]
  exact hcheb.trans (hdiv.trans_eq hden)

end PrimeGapNormality.Prime
