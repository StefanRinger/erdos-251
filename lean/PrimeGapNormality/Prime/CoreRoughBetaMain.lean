import PrimeGapNormality.Prime.CoreRoughRealCutDimension
import PrimeGapNormality.Prime.CoreBetaRemainderBound

/-!
# A finite rough beta fundamental lemma with an absolute constant

The actual parity-stopped sublist weights are used, with β=9k+1.
The prime-band dimension estimate and the finite remainder bound are
proved suppliers, not hypotheses of the endpoint below. Constants are
deliberately nonoptimal: the relative error is exp(299k-log R/log Z).
-/

namespace PrimeGapNormality.Prime.CoreRoughBetaMain

open CoreBetaBuchstab CoreBetaLevelSupport CoreRoughDimensionProduct
open CoreRoughRealCutDimension
open scoped Classical
noncomputable section

set_option maxHeartbeats 600000

/-- Absorb the dimension constant, the beta threshold, and the leading
factor two into a single absolute-linear dimension constant. -/
theorem error_coefficient_le {k : ℕ} (hk : 1 ≤ k) (s : ℝ) :
    2 * (Real.exp (32 * (k : ℝ))) ^ 9 *
        Real.exp (((9 * k + 1 : ℕ) : ℝ) - s) ≤
      Real.exp (299 * (k : ℝ) - s) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ = 2 * Real.exp (297 * (k : ℝ) + 1 - s) := by
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 1
      push_cast
      congr 1
      ring
    _ ≤ Real.exp 1 * Real.exp (297 * (k : ℝ) + 1 - s) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (297 * (k : ℝ) + 2 - s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (299 * (k : ℝ) - s) := Real.exp_le_exp.mpr (by linarith)

/-- Genuine finite fundamental lemma on the rough prime pool. The only
local-density premise is ν(p)≤k, not an Euler-product or remainder bound.
The list is the actual decreasing enumeration of that pool. -/
theorem main_abs_sub_euler_le
    {a y k : ℕ} (ha : a ≤ y) (hy : 16 ≤ y) (hk : 1 ≤ k)
    (ν : ℕ → ℕ) (hν : ∀ p ∈ dimensionPrimeBand a y k, ν p ≤ k)
    (ps : List ℕ) (hdec : ps.Pairwise (fun p q => q < p))
    (hps : ps.toFinset = dimensionPrimeBand a y k)
    {Z R : ℝ} (hZlo : (y : ℝ) < Z) (hZhi : Z ≤ (y : ℝ) + 1)
    (hlevel : Z ^ (9 * k + 1) ≤ R) (upper : Bool) :
    |main upper (test (9 * k + 1) R) [] ps
        (fun p : ℕ => (ν p : ℝ) / (p : ℝ)) -
      euler (fun p : ℕ => (ν p : ℝ) / (p : ℝ)) ps| ≤
        Real.exp (299 * (k : ℝ) - Real.log R / Real.log Z) *
          euler (fun p : ℕ => (ν p : ℝ) / (p : ℝ)) ps := by
  have hyR : (16 : ℝ) ≤ y := by exact_mod_cast hy
  have hZ : 2 < Z := by linarith
  have hn : ps.Nodup := hdec.imp (fun h => Ne.symm h.ne)
  have hmem : ∀ p ∈ ps, p ∈ dimensionPrimeBand a y k := by
    intro p hp
    rw [← hps]
    exact List.mem_toFinset.mpr hp
  have hprime : ∀ p ∈ ps, Nat.Prime p :=
    fun p hp => (mem_dimensionPrimeBand_iff.mp (hmem p hp)).1
  have hbelow : ∀ p ∈ ps, (p : ℝ) < Z := by
    intro p hp
    exact (Nat.cast_le.mpr (mem_dimensionPrimeBand_iff.mp (hmem p hp)).2.2).trans_lt hZlo
  have hg : ∀ p ∈ ps, 0 ≤ (ν p : ℝ) / (p : ℝ) ∧ (ν p : ℝ) / (p : ℝ) < 1 := by
    intro p hp
    exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      local_rank_ratio_lt_one hk ν (hmem p hp) (hν p (hmem p hp))⟩
  have hK : 1 ≤ Real.exp (32 * (k : ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  have hdim := list_euler_dimension ha hy hk ν hν ps hn hps hZlo.le hZhi
  have hmain := CoreBetaRemainderBound.main_abs_sub_euler_le hk hZ hlevel hK
    upper ps hdec hprime hbelow (fun p : ℕ => (ν p : ℝ) / (p : ℝ)) hg hdim
  have hV := CoreBetaRemainderBound.euler_pos
    (fun p : ℕ => (ν p : ℝ) / (p : ℝ)) ps (fun p hp => (hg p hp).2)
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (error_coefficient_le hk (Real.log R / Real.log Z)) hV.le)

/-- Both signs use the same error and the same unaltered Euler main term. -/
theorem upper_lower_relative_error
    {a y k : ℕ} (ha : a ≤ y) (hy : 16 ≤ y) (hk : 1 ≤ k)
    (ν : ℕ → ℕ) (hν : ∀ p ∈ dimensionPrimeBand a y k, ν p ≤ k)
    (ps : List ℕ) (hdec : ps.Pairwise (fun p q => q < p))
    (hps : ps.toFinset = dimensionPrimeBand a y k)
    {Z R : ℝ} (hZlo : (y : ℝ) < Z) (hZhi : Z ≤ (y : ℝ) + 1)
    (hlevel : Z ^ (9 * k + 1) ≤ R) :
    let g := fun p : ℕ => (ν p : ℝ) / (p : ℝ)
    let V := euler g ps
    let ε := Real.exp (299 * (k : ℝ) - Real.log R / Real.log Z)
    (1 - ε) * V ≤ main false (test (9 * k + 1) R) [] ps g ∧
      main true (test (9 * k + 1) R) [] ps g ≤ (1 + ε) * V := by
  dsimp only
  have hlo := (abs_le.mp (main_abs_sub_euler_le ha hy hk ν hν ps hdec hps hZlo hZhi hlevel false)).1
  have hhi := (abs_le.mp (main_abs_sub_euler_le ha hy hk ν hν ps hdec hps hZlo hZhi hlevel true)).2
  constructor <;> nlinarith

end
end PrimeGapNormality.Prime.CoreRoughBetaMain
