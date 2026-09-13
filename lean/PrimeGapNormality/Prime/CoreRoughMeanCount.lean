import PrimeGapNormality.Prime.PresieveSelbergCap
import PrimeGapNormality.Prime.CrtNestedCutoffFirstMoment
import PrimeGapNormality.Prime.CrtPhysicalRetentionLeEulerQuot
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An unconditional first-moment bound for the rough rooted law

The exact CRT first-moment identity is combined with the uniform Selberg
cap on every presieve fibre and the proved lower bound for the Euler
product.  No good-event, cardinality, or mean hypothesis remains.
-/

namespace PrimeGapNormality.Prime.CoreRoughMeanCount

open Filter Finset
open scoped Topology

noncomputable section

private theorem countMoment_one_eq_meanCard (z S : ℕ) :
    Stopped.countMoment (offsetWindow S) (actualRootLaw z S) 1 =
      ∑ U ∈ (offsetWindow S).powerset,
        (U.card : ℝ) * actualRootLaw z S U := by
  unfold Stopped.countMoment
  apply sum_congr rfl
  intro U _
  rw [Nat.choose_one_right]
  ring

private theorem residue_average_card_le
    {S : ℕ}
    (hcap : ∀ σ : ResidueChoice S,
      ((presieveSurvivors S σ).card : ℝ) ≤
        3 * (S : ℝ) / Real.log (S : ℝ)) :
    (∑ σ ∈ (univ : Finset (ResidueChoice S)),
        ((lateCandidateSet S S σ).card : ℝ)) /
        (Fintype.card (ResidueChoice S) : ℝ) ≤
      3 * (S : ℝ) / Real.log (S : ℝ) := by
  let C : ℝ := Fintype.card (ResidueChoice S)
  let M : ℝ := 3 * (S : ℝ) / Real.log (S : ℝ)
  have hCpos : 0 < C := by
    dsimp only [C]
    exact Nat.cast_pos.mpr (crtNestFM_residueChoice_card_pos S)
  have hpoint : ∀ σ ∈ (univ : Finset (ResidueChoice S)),
      ((lateCandidateSet S S σ).card : ℝ) ≤ M := by
    intro σ _
    dsimp only [M]
    simpa only [show presieveSurvivors S σ = lateCandidateSet S S σ from rfl]
      using hcap σ
  have hsum :
      ∑ σ ∈ (univ : Finset (ResidueChoice S)),
          ((lateCandidateSet S S σ).card : ℝ) ≤ C * M := by
    calc
      ∑ σ ∈ (univ : Finset (ResidueChoice S)),
          ((lateCandidateSet S S σ).card : ℝ) ≤
        ∑ _σ ∈ (univ : Finset (ResidueChoice S)), M :=
          sum_le_sum hpoint
      _ = C * M := by
        dsimp only [C]
        rw [sum_const, nsmul_eq_mul, card_univ]
  apply (div_le_iff₀ hCpos).2
  simpa only [C, M, mul_comm] using hsum

/-- Concrete unconditional first-moment estimate, uniform in every later
cutoff `z≥S`. -/
theorem eventually_countMoment_one_le :
    ∀ᶠ S : ℕ in atTop, ∀ z : ℕ, S ≤ z →
      Stopped.countMoment (offsetWindow S) (actualRootLaw z S) 1 ≤
        (3 / eulerProdLowerConst) * (S : ℝ) * eulerProdNat z := by
  have hcap :=
    eventually_presieveSurvivors_card_le_two_add_eps
      (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hcap, eventually_ge_atTop 16] with S hcapS hS16
  intro z hSz
  have hS2 : 2 ≤ S := le_trans (by norm_num) hS16
  have hlogS : 0 < Real.log (S : ℝ) := by
    have hSR : (16 : ℝ) ≤ S := Nat.cast_le.mpr hS16
    exact Real.log_pos
      (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) hSR)
  have hcapThree : ∀ σ : ResidueChoice S,
      ((presieveSurvivors S σ).card : ℝ) ≤
        3 * (S : ℝ) / Real.log (S : ℝ) := by
    intro σ
    simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using hcapS σ
  have havg := residue_average_card_le hcapThree
  have hret0 : 0 ≤ lateRetention S z :=
    crtNestFM_lateRetention_nonneg S z
  have hret := crtPhysRet_le_eulerProd_mul_log hS2 hS16 hSz
  have hM0 : 0 ≤ 3 * (S : ℝ) / Real.log (S : ℝ) := by positivity
  have hmeanEq := crtNestFM_meanCard_eq_theta_avg S z S le_rfl hSz
  have hmeanLe :
      ∑ U ∈ (offsetWindow S).powerset,
          (U.card : ℝ) * actualRootLaw z S U ≤
        (eulerProdNat z * Real.log (S : ℝ) / eulerProdLowerConst) *
          (3 * (S : ℝ) / Real.log (S : ℝ)) := by
    rw [hmeanEq]
    exact (mul_le_mul_of_nonneg_left havg hret0).trans
      (mul_le_mul_of_nonneg_right hret hM0)
  have hcancel :
      (eulerProdNat z * Real.log (S : ℝ) / eulerProdLowerConst) *
          (3 * (S : ℝ) / Real.log (S : ℝ)) =
        (3 / eulerProdLowerConst) * (S : ℝ) * eulerProdNat z := by
    field_simp [hlogS.ne', eulerProdLowerConst_pos.ne'] <;> ring
  rw [countMoment_one_eq_meanCard, ← hcancel]
  exact hmeanLe

/-- Existential absolute-constant packaging of the same theorem. -/
theorem exists_countMoment_one_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ S : ℕ in atTop, ∀ z : ℕ, S ≤ z →
        Stopped.countMoment (offsetWindow S) (actualRootLaw z S) 1 ≤
          C * (S : ℝ) * eulerProdNat z := by
  refine ⟨3 / eulerProdLowerConst,
    div_pos (by norm_num) eulerProdLowerConst_pos, ?_⟩
  exact eventually_countMoment_one_le

end

end PrimeGapNormality.Prime.CoreRoughMeanCount
