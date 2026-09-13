import PrimeGapNormality.Prime.FiniteSelbergIntervalCap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Asymptotic finite Selberg cap

The radius is the paper cutoff `floor(sqrt S / log S)`.  This module first
records its escape to infinity and the exact specialization of the finite
Selberg cap.  The remaining quantitative step is the pair of logarithmic
and quadratic-error limits needed for the constant two.
-/

open Filter Finset
open scoped Topology
open Asymptotics

namespace PrimeGapNormality.Prime

noncomputable section

/-- Paper Selberg cutoff `floor(sqrt S / log S)`. -/
def selbergRadius (S : ℕ) : ℕ :=
  ⌊Real.sqrt (S : ℝ) / Real.log (S : ℝ)⌋₊

private theorem tendsto_sqrt_div_log_atTop :
    Tendsto (fun x : ℝ => Real.sqrt x / Real.log x) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x ^ (1 / 2 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) _)
  have hwithin : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_inf.2 ⟨hzero, ?_⟩
    rw [tendsto_principal]
    exact hpos
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp only [Pi.inv_apply, inv_div]
  rw [Real.sqrt_eq_rpow]

theorem tendsto_selbergRadius_atTop : Tendsto selbergRadius atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (tendsto_sqrt_div_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem isEquivalent_selbergRadius_profile :
    (fun S : ℕ => (selbergRadius S : ℝ)) ~[atTop]
      (fun S : ℕ => Real.sqrt (S : ℝ) / Real.log (S : ℝ)) := by
  simpa [Function.comp_def, selbergRadius] using
    Asymptotics.isEquivalent_nat_floor.comp_tendsto
      (tendsto_sqrt_div_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem isEquivalent_log_selbergRadius_profile :
    (fun S : ℕ => Real.log (selbergRadius S : ℝ)) ~[atTop]
      (fun S : ℕ =>
        Real.log (Real.sqrt (S : ℝ) / Real.log (S : ℝ))) :=
  isEquivalent_selbergRadius_profile.log
    (tendsto_sqrt_div_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem tendsto_log_profile_div_log :
    Tendsto (fun S : ℕ =>
      Real.log (Real.sqrt (S : ℝ) / Real.log (S : ℝ)) /
        Real.log (S : ℝ)) atTop (nhds (1 / 2 : ℝ)) := by
  have hlog : Tendsto (fun S : ℕ => Real.log (S : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun S : ℕ =>
      Real.log (Real.log (S : ℝ)) / Real.log (S : ℝ)) atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hlog
  have hlim : Tendsto (fun S : ℕ =>
      (1 / 2 : ℝ) - Real.log (Real.log (S : ℝ)) / Real.log (S : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hloglog
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with S hS
  have hSpos : (0 : ℝ) < S := Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one hS)
  have hlogpos : 0 < Real.log (S : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hS)
  rw [Real.log_div (Real.sqrt_pos.2 hSpos).ne' hlogpos.ne',
    Real.log_sqrt hSpos.le]
  symm
  calc
    (Real.log (S : ℝ) / 2 - Real.log (Real.log (S : ℝ))) /
        Real.log (S : ℝ) =
      (1 / 2 : ℝ) *
          (Real.log (S : ℝ) * (Real.log (S : ℝ))⁻¹) -
        Real.log (Real.log (S : ℝ)) * (Real.log (S : ℝ))⁻¹ := by
      ring
    _ = (1 / 2 : ℝ) -
        Real.log (Real.log (S : ℝ)) * (Real.log (S : ℝ))⁻¹ := by
      rw [mul_inv_cancel₀ hlogpos.ne']
      ring
    _ = (1 / 2 : ℝ) -
        Real.log (Real.log (S : ℝ)) / Real.log (S : ℝ) := by
      simpa [div_eq_mul_inv]

theorem tendsto_log_selbergRadius_add_one_div_log :
    Tendsto (fun S : ℕ => Real.log (selbergRadius S + 1 : ℝ) /
      Real.log (S : ℝ)) atTop (nhds (1 / 2 : ℝ)) := by
  have hprofile : Tendsto (fun S : ℕ =>
      Real.sqrt (S : ℝ) / Real.log (S : ℝ)) atTop atTop :=
    tendsto_sqrt_div_log_atTop.comp tendsto_natCast_atTop_atTop
  have hone : (fun _S : ℕ => (1 : ℝ)) =o[atTop]
      (fun S : ℕ => Real.sqrt (S : ℝ) / Real.log (S : ℝ)) :=
    (isLittleO_const_id_atTop 1).comp_tendsto hprofile
  have hadd : (fun S : ℕ => (selbergRadius S : ℝ) + 1) ~[atTop]
      (fun S : ℕ => Real.sqrt (S : ℝ) / Real.log (S : ℝ)) :=
    isEquivalent_selbergRadius_profile.add_isLittleO hone
  have hlogeq := hadd.log hprofile
  have hlogprofile : Tendsto (fun S : ℕ =>
      Real.log (Real.sqrt (S : ℝ) / Real.log (S : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hprofile
  have hne := hlogprofile.eventually_ne_atTop 0
  have hratio : Tendsto (fun S : ℕ =>
      Real.log ((selbergRadius S : ℝ) + 1) /
        Real.log (Real.sqrt (S : ℝ) / Real.log (S : ℝ)))
      atTop (nhds 1) := by
    rw [isEquivalent_iff_tendsto_one hne] at hlogeq
    exact hlogeq
  have hmul : Tendsto (fun S : ℕ =>
      (Real.log ((selbergRadius S : ℝ) + 1) /
          Real.log (Real.sqrt (S : ℝ) / Real.log (S : ℝ))) *
        (Real.log (Real.sqrt (S : ℝ) / Real.log (S : ℝ)) /
          Real.log (S : ℝ))) atTop (nhds (1 / 2 : ℝ)) := by
    simpa using hratio.mul tendsto_log_profile_div_log
  refine hmul.congr' ?_
  filter_upwards [hne,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ne_atTop 0]
      with S hp hS
  field_simp

theorem tendsto_log_div_log_selbergRadius_add_one :
    Tendsto (fun S : ℕ => Real.log (S : ℝ) /
      Real.log (selbergRadius S + 1 : ℝ)) atTop (nhds 2) := by
  have h := tendsto_log_selbergRadius_add_one_div_log
  have hinv := h.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  convert hinv using 1 <;> norm_num [inv_div]

theorem tendsto_selbergRadius_sq_mul_log_div :
    Tendsto (fun S : ℕ => (selbergRadius S : ℝ) ^ 2 *
      Real.log (S : ℝ) / (S : ℝ)) atTop (nhds 0) := by
  have heq :
      (fun S : ℕ => (selbergRadius S : ℝ) ^ 2 * Real.log (S : ℝ) / (S : ℝ))
        ~[atTop]
      (fun S : ℕ => (Real.sqrt (S : ℝ) / Real.log (S : ℝ)) ^ 2 *
        Real.log (S : ℝ) / (S : ℝ)) :=
    ((isEquivalent_selbergRadius_profile.pow 2).mul IsEquivalent.refl).div
      IsEquivalent.refl
  have hlog : Tendsto (fun S : ℕ => Real.log (S : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun S : ℕ =>
      (Real.sqrt (S : ℝ) / Real.log (S : ℝ)) ^ 2 *
        Real.log (S : ℝ) / (S : ℝ)) atTop (nhds 0) := by
    refine hlog.inv_tendsto_atTop.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with S hS
    have hSpos : (0 : ℝ) < S := Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one hS)
    have hlogpos : 0 < Real.log (S : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hS)
    rw [div_pow, Real.sq_sqrt hSpos.le]
    symm
    calc
      ((S : ℝ) / Real.log (S : ℝ) ^ 2) * Real.log (S : ℝ) /
          (S : ℝ) =
        (Real.log (S : ℝ))⁻¹ * Real.log (S : ℝ) *
            ((S : ℝ) * (S : ℝ)⁻¹) * (Real.log (S : ℝ))⁻¹ := by
        simp only [div_eq_mul_inv, inv_pow, pow_two]
        ring
      _ = (Real.log (S : ℝ))⁻¹ := by
        rw [inv_mul_cancel₀ hlogpos.ne', mul_inv_cancel₀ hSpos.ne']
        ring
  exact (heq.tendsto_nhds_iff).mpr hbase

theorem eventually_one_le_selbergRadius :
    ∀ᶠ S : ℕ in atTop, 1 ≤ selbergRadius S :=
  tendsto_selbergRadius_atTop.eventually (eventually_ge_atTop 1)

theorem eventually_selbergRadius_le_self :
    ∀ᶠ S : ℕ in atTop, selbergRadius S ≤ S := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (Real.exp 1))] with S hS
  have hSpos : (0 : ℝ) < S := lt_of_lt_of_le (Real.exp_pos 1) hS
  have hSone : (1 : ℝ) ≤ S :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hS
  have hlog : (1 : ℝ) ≤ Real.log (S : ℝ) :=
    (Real.le_log_iff_exp_le hSpos).mpr hS
  have hsqrt : Real.sqrt (S : ℝ) ≤ (S : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hSone)
  have hprofile0 : 0 ≤ Real.sqrt (S : ℝ) / Real.log (S : ℝ) :=
    div_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans hlog)
  have hprofile : Real.sqrt (S : ℝ) / Real.log (S : ℝ) ≤ (S : ℝ) := by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hlog)).mpr
    exact hsqrt.trans (le_mul_of_one_le_right hSpos.le hlog)
  have hfloor : (selbergRadius S : ℝ) ≤ (S : ℝ) :=
    (Nat.floor_le hprofile0).trans hprofile
  exact_mod_cast hfloor

/-- Exact finite cap at the asymptotic radius, separated from the remaining
real asymptotic estimates. -/
theorem finiteSelberg_card_le_at_radius {A : Finset ℕ} {S : ℕ}
    (hR : 1 ≤ selbergRadius S) (hRS : selbergRadius S ≤ S)
    (hA : A ⊆ Icc 1 S)
    (havoid : ∀ p ∈ Nat.primesLE (selbergRadius S), ∃ c : ℕ,
      ∀ n ∈ A, n % p ≠ c % p) :
    (A.card : ℝ) ≤
      (S : ℝ) / selbergJR (selbergRadius S) + (selbergRadius S : ℝ) ^ 2 :=
  finiteSelberg_card_le hR hRS hA havoid

theorem eventually_finiteSelberg_card_le_at_radius :
    ∀ᶠ S : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Icc 1 S →
      (∀ p ∈ Nat.primesLE (selbergRadius S), ∃ c : ℕ,
        ∀ n ∈ A, n % p ≠ c % p) →
      (A.card : ℝ) ≤
        (S : ℝ) / selbergJR (selbergRadius S) + (selbergRadius S : ℝ) ^ 2 := by
  filter_upwards [eventually_one_le_selbergRadius,
    eventually_selbergRadius_le_self] with S hR hRS
  intro A hA havoid
  exact finiteSelberg_card_le_at_radius hR hRS hA havoid

theorem eventually_finiteSelberg_card_le_two_add_eps
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Icc 1 S →
      (∀ p ∈ Nat.primesLE (selbergRadius S), ∃ c : ℕ,
        ∀ n ∈ A, n % p ≠ c % p) →
      (A.card : ℝ) ≤ (2 + ε) * S / Real.log S := by
  have hcoef : Tendsto (fun S : ℕ =>
      Real.log (S : ℝ) / Real.log (selbergRadius S + 1 : ℝ) +
        (selbergRadius S : ℝ) ^ 2 * Real.log (S : ℝ) / S)
      atTop (nhds 2) := by
    convert tendsto_log_div_log_selbergRadius_add_one.add
      tendsto_selbergRadius_sq_mul_log_div using 1 <;> norm_num
  have hcoef_le : ∀ᶠ S : ℕ in atTop,
      Real.log (S : ℝ) / Real.log (selbergRadius S + 1 : ℝ) +
        (selbergRadius S : ℝ) ^ 2 * Real.log (S : ℝ) / S < 2 + ε :=
    hcoef.eventually (gt_mem_nhds (by linarith))
  filter_upwards [eventually_one_le_selbergRadius,
    eventually_selbergRadius_le_self, eventually_gt_atTop (1 : ℕ), hcoef_le]
      with S hR hRS hS hcoefS
  intro A hA havoid
  have hfinite := finiteSelberg_card_le_at_radius hR hRS hA havoid
  have hlogS : 0 < Real.log (S : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hS)
  have hlogR : 0 < Real.log (selbergRadius S + 1 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (Nat.lt_succ_of_le hR)
  have hmain : (S : ℝ) / selbergJR (selbergRadius S) ≤
      (S : ℝ) / Real.log (selbergRadius S + 1 : ℝ) := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg S) hlogR
      (selbergJR_ge_log_add_one (selbergRadius S))
  calc
    (A.card : ℝ) ≤ (S : ℝ) / selbergJR (selbergRadius S) +
        (selbergRadius S : ℝ) ^ 2 := hfinite
    _ ≤ (S : ℝ) / Real.log (selbergRadius S + 1 : ℝ) +
        (selbergRadius S : ℝ) ^ 2 := add_le_add hmain le_rfl
    _ = (Real.log (S : ℝ) / Real.log (selbergRadius S + 1 : ℝ) +
          (selbergRadius S : ℝ) ^ 2 * Real.log (S : ℝ) / S) *
        ((S : ℝ) / Real.log S) := by
      have hS0 : (S : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hS))
      field_simp
    _ ≤ (2 + ε) * ((S : ℝ) / Real.log S) := by
      exact mul_le_mul_of_nonneg_right hcoefS.le (div_nonneg (Nat.cast_nonneg S) hlogS.le)
    _ = (2 + ε) * S / Real.log S := by ring

end

end PrimeGapNormality.Prime
