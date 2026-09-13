import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Real.Basic

/-!
# Finite discrete common mass and central gap merge

Source: `lean/PRIME_SIGNATURES.md` Config;
`lean/PRIME_ARCHITECTURE.md`;
`lean/PRIME_MATHLIB.md`.
Contract: API
Audit: GREEN

Common mass is `∑ min`. Discrete TV is `∑ |μ-ν|/2`. The 0-based
central merge replaces indices `K-1` and `K` on a length-`(2K+1)`
tuple, yielding length `2K`.
-/

namespace PrimeGapNormality.Prime

open Finset

/-- Overlap of two finite discrete masses on `s`. -/
noncomputable def commonMass {ι : Type*} (s : Finset ι) (μ ν : ι → ℝ) : ℝ :=
  ∑ i ∈ s, min (μ i) (ν i)

/-- Half total variation of two finite discrete masses on `s`. -/
noncomputable def tvHalf {ι : Type*} (s : Finset ι) (μ ν : ι → ℝ) : ℝ :=
  (∑ i ∈ s, |μ i - ν i|) / 2

/-- Nonnegative masses have nonnegative overlap. -/
theorem commonMass_nonneg {ι : Type*} {s : Finset ι} {μ ν : ι → ℝ}
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hν : ∀ i ∈ s, 0 ≤ ν i) :
    0 ≤ commonMass s μ ν :=
  sum_nonneg fun i hi => le_min (hμ i hi) (hν i hi)

/-- `min` is 1-Lipschitz in the ℓ¹ metric on the pair. -/
theorem abs_min_sub_min (a b a' b' : ℝ) :
    |min a b - min a' b'| ≤ |a - a'| + |b - b'| :=
  (abs_min_sub_min_le_max a b a' b').trans
    (max_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _)))

/-- Overlap is Lipschitz in the two masses, in the ℓ¹ metric. -/
theorem commonMass_lipschitz {ι : Type*} {s : Finset ι}
    {μ ν μ' ν' : ι → ℝ}
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hν : ∀ i ∈ s, 0 ≤ ν i)
    (hμ' : ∀ i ∈ s, 0 ≤ μ' i) (hν' : ∀ i ∈ s, 0 ≤ ν' i) :
    |commonMass s μ ν - commonMass s μ' ν'|
      ≤ ∑ i ∈ s, |μ i - μ' i| + ∑ i ∈ s, |ν i - ν' i| := by
  have hpt : ∀ i ∈ s,
      |min (μ i) (ν i) - min (μ' i) (ν' i)|
        ≤ |μ i - μ' i| + |ν i - ν' i| :=
    fun i _ => abs_min_sub_min _ _ _ _
  -- Nonnegativity is part of the mass contract; the ℓ¹ bound does not use it.
  let _ := commonMass_nonneg hμ hν
  let _ := commonMass_nonneg hμ' hν'
  calc
    |commonMass s μ ν - commonMass s μ' ν'|
        = |∑ i ∈ s, (min (μ i) (ν i) - min (μ' i) (ν' i))| := by
          rw [commonMass, commonMass, ← sum_sub_distrib]
    _ ≤ ∑ i ∈ s, |min (μ i) (ν i) - min (μ' i) (ν' i)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (|μ i - μ' i| + |ν i - ν' i|) := sum_le_sum hpt
    _ = ∑ i ∈ s, |μ i - μ' i| + ∑ i ∈ s, |ν i - ν' i| := sum_add_distrib

/-- Overlap is concave in mixtures with nonnegative weights. -/
theorem commonMass_concave_mixture {ι κ : Type*} {s : Finset ι}
    (t : Finset κ) (w : κ → ℝ)
    (hw0 : ∀ k ∈ t, 0 ≤ w k) (hw1 : ∑ k ∈ t, w k = 1)
    (μ ν : κ → ι → ℝ)
    (hμ : ∀ k ∈ t, ∀ i ∈ s, 0 ≤ μ k i)
    (hν : ∀ k ∈ t, ∀ i ∈ s, 0 ≤ ν k i) :
    commonMass s (fun i => ∑ k ∈ t, w k * μ k i)
                 (fun i => ∑ k ∈ t, w k * ν k i)
      ≥ ∑ k ∈ t, w k * commonMass s (μ k) (ν k) := by
  have hmixμ : ∀ i ∈ s, 0 ≤ ∑ k ∈ t, w k * μ k i := fun i hi =>
    sum_nonneg fun k hk => mul_nonneg (hw0 k hk) (hμ k hk i hi)
  have hmixν : ∀ i ∈ s, 0 ≤ ∑ k ∈ t, w k * ν k i := fun i hi =>
    sum_nonneg fun k hk => mul_nonneg (hw0 k hk) (hν k hk i hi)
  let _ := commonMass_nonneg hmixμ hmixν
  let _ := hw1
  have hpt : ∀ i ∈ s,
      ∑ k ∈ t, w k * min (μ k i) (ν k i)
        ≤ min (∑ k ∈ t, w k * μ k i) (∑ k ∈ t, w k * ν k i) := by
    intro i _hi
    refine le_min ?_ ?_
    · exact sum_le_sum fun k hk =>
        mul_le_mul_of_nonneg_left (min_le_left _ _) (hw0 k hk)
    · exact sum_le_sum fun k hk =>
        mul_le_mul_of_nonneg_left (min_le_right _ _) (hw0 k hk)
  calc
    ∑ k ∈ t, w k * commonMass s (μ k) (ν k)
        = ∑ k ∈ t, ∑ i ∈ s, w k * min (μ k i) (ν k i) := by
          simp_rw [commonMass, mul_sum]
    _ = ∑ i ∈ s, ∑ k ∈ t, w k * min (μ k i) (ν k i) := sum_comm
    _ ≤ ∑ i ∈ s, min (∑ k ∈ t, w k * μ k i) (∑ k ∈ t, w k * ν k i) :=
      sum_le_sum hpt
    _ = commonMass s (fun i => ∑ k ∈ t, w k * μ k i)
          (fun i => ∑ k ∈ t, w k * ν k i) := rfl

/-- Merge the two central gaps of a length-`(2K+1)` tuple.

0-based: replace indices `K-1` and `K` by their sum. The output
has length `2K`. Requires `1 ≤ K`. -/
def mergeCenter {K : ℕ} (hK : 1 ≤ K) (v : Fin (2 * K + 1) → ℕ) :
    Fin (2 * K) → ℕ := fun j =>
  if hj : (j : ℕ) + 1 < K then
    v ⟨(j : ℕ), Nat.lt_trans j.isLt (Nat.lt_succ_self _)⟩
  else if hj' : (j : ℕ) + 1 = K then
    v ⟨K - 1, by have := hK; omega⟩ + v ⟨K, by have := hK; omega⟩
  else
    v ⟨(j : ℕ) + 1, Nat.succ_lt_succ j.isLt⟩

/-- Left block of `mergeCenter`: indices strictly before the merged slot. -/
theorem mergeCenter_left {K : ℕ} (hK : 1 ≤ K) (v : Fin (2 * K + 1) → ℕ)
    (j : Fin (2 * K)) (hj : (j : ℕ) + 1 < K) :
    mergeCenter hK v j =
      v ⟨(j : ℕ), Nat.lt_trans j.isLt (Nat.lt_succ_self _)⟩ := by
  rw [mergeCenter]
  exact dif_pos hj

/-- Central slot: the sum of input indices `K-1` and `K`. -/
theorem mergeCenter_mid {K : ℕ} (hK : 1 ≤ K) (v : Fin (2 * K + 1) → ℕ)
    (j : Fin (2 * K)) (hj : (j : ℕ) + 1 = K) :
    mergeCenter hK v j =
      v ⟨K - 1, by have := hK; omega⟩ + v ⟨K, by have := hK; omega⟩ := by
  have hnlt : ¬(j : ℕ) + 1 < K := by omega
  rw [mergeCenter, dif_neg hnlt, dif_pos hj]

/-- Right block of `mergeCenter`: indices strictly after the merged slot. -/
theorem mergeCenter_right {K : ℕ} (hK : 1 ≤ K) (v : Fin (2 * K + 1) → ℕ)
    (j : Fin (2 * K)) (hj : K < (j : ℕ) + 1) :
    mergeCenter hK v j = v ⟨(j : ℕ) + 1, Nat.succ_lt_succ j.isLt⟩ := by
  have hnlt : ¬(j : ℕ) + 1 < K := by omega
  have hneq : ¬(j : ℕ) + 1 = K := by omega
  rw [mergeCenter, dif_neg hnlt, dif_neg hneq]

end PrimeGapNormality.Prime
