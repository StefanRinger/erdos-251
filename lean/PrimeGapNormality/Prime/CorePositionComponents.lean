import PrimeGapNormality.Prime.CorePeriodicPositionEnd
import PrimeGapNormality.Prime.JointWeyl

/-!
# Joint periodic prime-position components

The scalar periodic-position theorem already treats every nonzero rational
periodic weight.  Here it is applied to every nonzero integer character of
the literal residue components.  This gives the common-`B^k` joint Weyl
statement in the paper without assuming independence of an auxiliary family.

Lean's prime index is zero based: `nthPrime n` is the paper's `p_(n+1)`.
Consequently the component labelled by `s : Fin k` uses the one-based
condition `(n + 1) % k = s.val`.
-/

namespace PrimeGapNormality.Prime.CorePositionComponents

open Finset Filter Function
open scoped Topology

noncomputable section

/-- The rational periodic indicator of one one-based position residue. -/
def positionResidueWeight {k : ℕ} (s : Fin k) (n : ℕ) : ℚ :=
  if n % k = s.val then 1 else 0

theorem positionResidueWeight_periodic {k : ℕ} (s : Fin k) :
    Periodic (positionResidueWeight s) k := by
  intro n
  simp only [positionResidueWeight, Nat.add_mod_right]

private theorem coe_positionResidueWeight {k : ℕ} (s : Fin k) (n : ℕ) :
    (positionResidueWeight s n : ℝ) =
      if n % k = s.val then 1 else 0 := by
  by_cases h : n % k = s.val <;> simp [positionResidueWeight, h]

/-- The literal position component
`sum_{n >= 0} 1[(n+1) mod k = s] p_(n+1) / B^(n+1)`.
-/
def positionResidueComponent (B : ℕ) {k : ℕ} (s : Fin k) : ℝ :=
  ∑' n : ℕ,
    (if (n + 1) % k = s.val then (1 : ℝ) else 0) *
      (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)

theorem positionResidueComponent_eq_primePositionSeries
    (B : ℕ) {k : ℕ} (s : Fin k) :
    positionResidueComponent B s =
      primePosWeightedSeries (fun n ↦ (positionResidueWeight s n : ℝ)) B := by
  unfold positionResidueComponent primePosWeightedSeries
  apply tsum_congr
  intro n
  change
    (if (n + 1) % k = s.val then (1 : ℝ) else 0) *
        (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) =
      (positionResidueWeight s (n + 1) : ℝ) *
        (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)
  rw [coe_positionResidueWeight]

theorem positionResidueComponent_summable {B k : ℕ} (hB : 2 ≤ B)
    (hk : 0 < k) (s : Fin k) :
    Summable (fun n : ℕ ↦
      (if (n + 1) % k = s.val then (1 : ℝ) else 0) *
        (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)) := by
  have hp : Periodic (fun n : ℕ ↦ (positionResidueWeight s n : ℝ)) k :=
    periodic_cast_rat (positionResidueWeight_periodic s)
  simpa only [coe_positionResidueWeight] using
    (primePosWeightedSeries_summable hB (by omega : 1 ≤ k)
      (fun n : ℕ ↦ (positionResidueWeight s n : ℝ)) hp)

/-- The rational periodic weight represented by an integer character of all
residue components. -/
def positionResidueCombination {k : ℕ} (t : Fin k → ℤ) (n : ℕ) : ℚ :=
  ∑ s : Fin k, (t s : ℚ) * positionResidueWeight s n

theorem positionResidueCombination_periodic {k : ℕ} (t : Fin k → ℤ) :
    Periodic (positionResidueCombination t) k := by
  intro n
  unfold positionResidueCombination
  apply sum_congr rfl
  intro s hs
  rw [positionResidueWeight_periodic s n]

theorem positionResidueCombination_apply_label {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℤ) (s : Fin k) :
    positionResidueCombination t s.val = (t s : ℚ) := by
  unfold positionResidueCombination
  rw [Fintype.sum_eq_single s]
  · simp [positionResidueWeight, Nat.mod_eq_of_lt s.isLt]
  · intro u hus
    have hv : s.val ≠ u.val := fun h ↦ hus (Fin.ext h.symm)
    simp [positionResidueWeight, Nat.mod_eq_of_lt s.isLt, hv]

theorem positionResidueCombination_ne_zero {k : ℕ} (hk : 0 < k)
    {t : Fin k → ℤ} (ht : ∃ s, t s ≠ 0) :
    positionResidueCombination t ≠ 0 := by
  obtain ⟨s, hs⟩ := ht
  intro hzero
  have heval := congrFun hzero s.val
  rw [positionResidueCombination_apply_label hk t s] at heval
  simp only [Pi.zero_apply] at heval
  exact hs (Int.cast_eq_zero.mp heval)

/-- A finite integer combination of the literal components is exactly the
position series with the corresponding periodic residue weight. -/
theorem primePositionSeries_residueCombination
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (t : Fin k → ℤ) :
    primePosWeightedSeries
        (fun n ↦ (positionResidueCombination t n : ℝ)) B =
      ∑ s : Fin k, (t s : ℝ) * positionResidueComponent B s := by
  unfold primePosWeightedSeries positionResidueCombination positionResidueComponent
  have hs : ∀ s : Fin k, Summable (fun n : ℕ ↦
      (t s : ℝ) *
        ((if (n + 1) % k = s.val then (1 : ℝ) else 0) *
          (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1))) := by
    intro s
    exact (positionResidueComponent_summable hB hk s).mul_left (t s : ℝ)
  have hterm (n : ℕ) :
      ((∑ s : Fin k,
          (t s : ℚ) * positionResidueWeight s (n + 1) : ℚ) : ℝ) *
          (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1) =
        ∑ s : Fin k, (t s : ℝ) *
          ((if (n + 1) % k = s.val then (1 : ℝ) else 0) *
            (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)) := by
    rw [Rat.cast_sum, Finset.sum_mul, Finset.sum_div]
    apply sum_congr rfl
    intro s hs
    unfold positionResidueWeight
    rw [Rat.cast_mul, Rat.cast_intCast]
    split_ifs <;> simp [mul_div_assoc]
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun s _ ↦ hs s)]
  apply sum_congr rfl
  intro s hsfin
  rw [(positionResidueComponent_summable hB hk s).tsum_mul_left]

private theorem positionClock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    2 ≤ B ^ k := by
  have hsplit : k = k - 1 + 1 :=
    (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [hsplit, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

/-- The `k` literal periodic position components have the common-`B^k`
joint Weyl property.  Each nonzero character is one nonzero rational
periodic position weight, so this requires no family-independence input. -/
theorem positionResidue_jointWeyl_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {κ d0 C : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hC : 1 ≤ C) (hD : CoreLinearD κ d0 C) :
    JointWeyl (fun _ : Fin k ↦ B ^ k)
      (fun s ↦ positionResidueComponent B s) := by
  intro t ht
  have hc : Periodic (positionResidueCombination t) k :=
    positionResidueCombination_periodic t
  have hc0 : positionResidueCombination t ≠ 0 :=
    positionResidueCombination_ne_zero hk ht
  have hW := CorePeriodicPositionEnd.primePositionSeries_weyl_clock_of_D
    hB hk (positionResidueCombination t) hc hc0 hκ hd0 hC hD
  rw [primePositionSeries_residueCombination hB hk t] at hW
  have hchar := hW 1 (by norm_num)
  have heq (n : ℕ) :
      (∑ s : Fin k, (t s : ℝ) * ((B ^ k : ℕ) : ℝ) ^ n *
          positionResidueComponent B s) =
        ((1 : ℤ) : ℝ) * ((B ^ k : ℕ) : ℝ) ^ n *
          (∑ s : Fin k, (t s : ℝ) * positionResidueComponent B s) := by
    simp only [Int.cast_one, one_mul, Finset.mul_sum]
    apply sum_congr rfl
    intro s hs
    ring
  simpa only [heq] using hchar

/-- Hence `1` and all periodic position residue components are actually
linearly independent over `Q`. -/
theorem positionResidue_one_linearIndependent_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {κ d0 C : ℝ} (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hC : 1 ≤ C) (hD : CoreLinearD κ d0 C) :
    LinearIndependent ℚ (fun i : Option (Fin k) => match i with
      | none => (1 : ℝ)
      | some s => positionResidueComponent B s) := by
  convert linearIndependent_one_jointWeyl (positionClock_ge hB hk)
    (positionResidue_jointWeyl_of_D hB hk hκ hd0 hC hD) using 1
  funext i
  cases i <;> rfl

/-- Kuperberg supplies the degree-one profile for every fixed base and
positive period. -/
theorem positionResidue_jointWeyl_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (hK : KuperbergConj13) :
    JointWeyl (fun _ : Fin k ↦ B ^ k)
      (fun s ↦ positionResidueComponent B s) := by
  have hlog : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hκ : 0 < 1 / Real.log (B : ℝ) := div_pos zero_lt_one hlog
  exact positionResidue_jointWeyl_of_D hB hk le_rfl (by norm_num) (by norm_num)
    (coreLinearD_of_kuperberg hK hκ)

theorem positionResidue_one_linearIndependent_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (hK : KuperbergConj13) :
    LinearIndependent ℚ (fun i : Option (Fin k) => match i with
      | none => (1 : ℝ)
      | some s => positionResidueComponent B s) := by
  convert linearIndependent_one_jointWeyl (positionClock_ge hB hk)
    (positionResidue_jointWeyl_of_kuperberg hB hk hK) using 1
  funext i
  cases i <;> rfl

end
end PrimeGapNormality.Prime.CorePositionComponents
