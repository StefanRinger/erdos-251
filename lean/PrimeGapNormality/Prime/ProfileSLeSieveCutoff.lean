import PrimeGapNormality.Prime.CrtFailureMassLimit
import PrimeGapNormality.Prime.ProfileInequalities
import PrimeGapNormality.Prime.SieveCutoffCal
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic

/-!
# Eventual `profileS ≤ sieveCutoff` (not Chebyshev)

`ActualCrtFibreOffBandVanishes` still packages eventual
`profileS κ X ≤ sieveCutoff X`. That comparison is **not** a Chebyshev
bound and is **not** faked from `G(X) = X`.

Lake-green `EulerProd.isSieveCutoff_rpow` says a sieve cutoff `y` of
`t` with `e^{16} ≤ t` satisfies `t ^ eulerProdLowerConst ≤ y`.
`SieveCutoffCal.sieveCutoff_spec` and `tendsto_sieveCutoff_atTop` give
the canonical cutoff. Paper `profileS κ X = ⌊4 L_X windowG X⌋` is
`O(L log X)` with `L = profileL → ∞` slowly
(`ProfileInequalities.eventually_one_le_profileL`,
`CrtFailureMassLimit.tendsto_profileL_atTop`). Polynomial-in-log is
eventually `≤ X^c` for `c = eulerProdLowerConst > 0`.

Does **not** import MixZeta, ExactRootWindowClose,
RootedCutoffTypicalOsc, TypicalOsc*, FibreSlotFromProfile, or Weyl
leaves. CRT + EulerProd only. `G(X) = X` is not the remainder scale
(`windowG`, not linear Chebyshev).

**Compiled.**
1. Eventual `(profileS κ X : ℝ) ≤ sieveCutoff (X : ℝ)` for `0 < κ`.
2. Same at `κ = stdKappa ρ` (`1 < ρ`).
3. `ActualCrtFibreOffBandVanishes κ` from `0 < κ` and a named
   `Tendsto (lateFibreOffBandMass …) 0`, using compiled
   `profileS ≤ sieveCutoff` and `eventually_one_le_profileL`
   (`actualCrtFibreOffBandVanishes_of_offBandMass`).

**Not compiled.** The off-band mass limit itself. Fibre mean-band
for every residue. Kernel close.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `t ^ eulerProdLowerConst ≤ y` at a sieve cutoff | theorem (`isSieveCutoff_rpow`) |
| canonical `sieveCutoff` | theorem (`sieveCutoff_spec`, `tendsto_sieveCutoff_atTop`) |
| `profileS = O(L · windowG)` | theorem (`⌊4 L G⌋`, `windowG = log X`) |
| `L → ∞` slowly | theorem (`tendsto_profileL_atTop`, `eventually_one_le_profileL`) |
| eventual `profileS ≤ sieveCutoff` (`0 < κ`) | theorem |
| same at `stdKappa ρ` (`1 < ρ`) | theorem |
| `ActualCrtFibreOffBandVanishes` from off-band mass | theorem (`profileS ≤ sieveCutoff` and `0 < profileL` discharged) |
| `Tendsto lateFibreOffBandMass 0` | remains |
| Chebyshev / `G(X) = X` remainder scale | not used |
| kernel closed | not claimed |

Progress: the `profileS ≤ sieveCutoff` conjunct of
`ActualCrtFibreOffBandVanishes` disappears. Off-band mass `→ 0`
remains named. Does not claim the kernel is closed.

Source: `EulerProd.isSieveCutoff_rpow`, `eulerProdLowerConst_pos`;
`SieveCutoffCal.sieveCutoff_spec`, `tendsto_sieveCutoff_atTop`;
`ProfileInequalities.eventually_one_le_profileL`;
`CrtFailureMassLimit.ActualCrtFibreOffBandVanishes`,
`tendsto_profileL_atTop`.
Contract: API
-/

open Filter Asymptotics
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000

noncomputable section

/-! ### Window and profile comparisons -/

private theorem windowG_one_le (X : ℕ) : (1 : ℝ) ≤ windowG X :=
  le_max_right _ _

private theorem windowG_nonneg (X : ℕ) : (0 : ℝ) ≤ windowG X :=
  le_trans (by norm_num : (0 : ℝ) ≤ 1) (windowG_one_le X)

private theorem windowG_log_nonneg (X : ℕ) : 0 ≤ Real.log (windowG X) :=
  Real.log_nonneg (windowG_one_le X)

private theorem tendsto_windowG : Tendsto windowG atTop atTop :=
  tendsto_atTop_mono (fun X => le_max_left (Real.log (X : ℝ)) (1 : ℝ))
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem windowG_eq_log_of_exp_sixteen {X : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) : windowG X = Real.log (X : ℝ) := by
  have hx0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 16) hX
  have hexp1 : Real.exp 1 < (X : ℝ) :=
    (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16)).trans_le hX
  have hlog : (1 : ℝ) < Real.log (X : ℝ) :=
    (Real.lt_log_iff_exp_lt hx0).mpr hexp1
  exact max_eq_left hlog.le

private theorem one_lt_of_exp_sixteen_le {X : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) : (1 : ℝ) < X :=
  (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hX

private theorem profileL_cast_le_add_one {κ : ℝ} (hκ : 0 ≤ κ) (X : ℕ) :
    (profileL κ X : ℝ) ≤
      κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X)) + 1 := by
  set a := κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X))
  have ha : 0 ≤ a :=
    add_nonneg (mul_nonneg hκ (windowG_log_nonneg X)) (Real.sqrt_nonneg _)
  exact (Nat.ceil_lt_add_one (R := ℝ) ha).le

private theorem profileS_cast_le_four (κ : ℝ) (X : ℕ) :
    (profileS κ X : ℝ) ≤ 4 * (profileL κ X : ℝ) * windowG X := by
  have hnn : 0 ≤ (4 : ℝ) * (profileL κ X : ℝ) * windowG X :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (windowG_nonneg X)
  exact Nat.floor_le hnn

private theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have hx0 : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 1) hx
  have hsq : x ≤ x ^ 2 := le_self_pow₀ hx (Nat.succ_ne_zero 1)
  have hsqrt : Real.sqrt x ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hx0] at hsqrt

/-! ### `4 (κ log G + √(κ log G) + 1) ≤ G` for large `G` -/

private theorem eventually_four_mul_profileArg_le {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ g : ℝ in atTop,
      4 * (κ * Real.log g + Real.sqrt (κ * Real.log g) + 1) ≤ g := by
  have hlog : Tendsto (fun g : ℝ => Real.log g / g) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  have h1 := hlog.const_mul (8 * κ)
  have h2 : Tendsto (fun g : ℝ => (4 : ℝ) / g) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (4 : ℝ)
  have hsum :
      Tendsto (fun g : ℝ => (8 * κ) * (Real.log g / g) + 4 / g)
        atTop (nhds 0) := by
    simpa [add_zero] using h1.add h2
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (Real.exp (max 1 (1 / κ))),
    hsum.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))] with
    g hg0 hgexp hball
  have hmaxpos : (0 : ℝ) < max 1 (1 / κ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hexp1 : (1 : ℝ) < Real.exp (max 1 (1 / κ)) :=
    Real.one_lt_exp_iff.mpr hmaxpos
  have hg1 : (1 : ℝ) < g := hexp1.trans_le hgexp
  have hlog1 : (1 : ℝ) ≤ Real.log g :=
    (Real.le_log_iff_exp_le (lt_trans (by norm_num : (0 : ℝ) < 1) hg1)).mpr
      (le_trans (Real.exp_le_exp.mpr (le_max_left 1 (1 / κ))) hgexp)
  have hlogκ : 1 / κ ≤ Real.log g :=
    (Real.le_log_iff_exp_le (lt_trans (by norm_num : (0 : ℝ) < 1) hg1)).mpr
      (le_trans (Real.exp_le_exp.mpr (le_max_right 1 (1 / κ))) hgexp)
  have hκlog : (1 : ℝ) ≤ κ * Real.log g := by
    have hiden : (1 : ℝ) = κ * (1 / κ) := (mul_one_div_cancel hκ.ne').symm
    exact hiden.le.trans (mul_le_mul_of_nonneg_left hlogκ hκ.le)
  have hsqrt : Real.sqrt (κ * Real.log g) ≤ κ * Real.log g :=
    sqrt_le_self_of_one_le hκlog
  have hadd :
      κ * Real.log g + Real.sqrt (κ * Real.log g) + 1 ≤
        2 * κ * Real.log g + 1 := by
    have hsum :
        κ * Real.log g + Real.sqrt (κ * Real.log g) ≤
          κ * Real.log g + κ * Real.log g :=
      add_le_add le_rfl hsqrt
    have h2 : κ * Real.log g + κ * Real.log g = 2 * κ * Real.log g := by
      ring
    have hsum' :
        κ * Real.log g + Real.sqrt (κ * Real.log g) ≤ 2 * κ * Real.log g :=
      h2 ▸ hsum
    exact add_le_add hsum' (le_refl (1 : ℝ))
  have h4 :
      4 * (κ * Real.log g + Real.sqrt (κ * Real.log g) + 1) ≤
        4 * (2 * κ * Real.log g + 1) :=
    mul_le_mul_of_nonneg_left hadd (by norm_num)
  have hring : 4 * (2 * κ * Real.log g + 1) = 8 * κ * Real.log g + 4 := by
    ring
  rw [hring] at h4
  have hnn :
      0 ≤ (8 * κ) * (Real.log g / g) + 4 / g :=
    add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hκ.le)
        (div_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog1) hg0.le))
      (div_nonneg (by norm_num) hg0.le)
  have hdist :
      dist ((8 * κ) * (Real.log g / g) + 4 / g) 0 < 1 :=
    Metric.mem_ball.mp hball
  have habs : |(8 * κ) * (Real.log g / g) + 4 / g| < 1 := by
    rwa [Real.dist_eq, sub_zero] at hdist
  have hlt : (8 * κ) * (Real.log g / g) + 4 / g < 1 := by
    rwa [abs_of_nonneg hnn] at habs
  have heq :
      (8 * κ * Real.log g + 4) / g =
        (8 * κ) * (Real.log g / g) + 4 / g := by
    rw [add_div, mul_div_assoc]
  have hmain : 8 * κ * Real.log g + 4 < g :=
    (div_lt_one hg0).mp (heq.symm ▸ hlt)
  exact h4.trans hmain.le

/-! ### Polynomial-in-log versus `X^c` and the cutoff power -/

private theorem eventually_log_sq_le_rpow :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ x ^ eulerProdLowerConst := by
  have ht :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      eulerProdLowerConst_pos).tendsto_div_nhds_zero
  filter_upwards [
    ht.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with x hball hx1
  have hx0 : (0 : ℝ) < x := lt_trans (by norm_num : (0 : ℝ) < 1) hx1
  have hlog0 : (0 : ℝ) ≤ Real.log x := (Real.log_pos hx1).le
  have hden : (0 : ℝ) < x ^ eulerProdLowerConst :=
    Real.rpow_pos_of_pos hx0 _
  have hnum : (0 : ℝ) ≤ Real.log x ^ (2 : ℝ) :=
    Real.rpow_nonneg hlog0 _
  have hnn : 0 ≤ Real.log x ^ (2 : ℝ) / x ^ eulerProdLowerConst :=
    div_nonneg hnum hden.le
  have hdist :
      dist (Real.log x ^ (2 : ℝ) / x ^ eulerProdLowerConst) 0 < 1 :=
    Metric.mem_ball.mp hball
  have habs : |Real.log x ^ (2 : ℝ) / x ^ eulerProdLowerConst| < 1 := by
    rwa [Real.dist_eq, sub_zero] at hdist
  have hlt : Real.log x ^ (2 : ℝ) / x ^ eulerProdLowerConst < 1 := by
    rwa [abs_of_nonneg hnn] at habs
  have hlt' : Real.log x ^ (2 : ℝ) < x ^ eulerProdLowerConst :=
    (div_lt_one hden).mp hlt
  rw [Real.rpow_two] at hlt'
  exact hlt'.le

private theorem eventually_exp_sixteen_le :
    ∀ᶠ X : ℕ in atTop, Real.exp 16 ≤ (X : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 16))

private theorem eventually_rpow_le_sieveCutoff :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ) ^ eulerProdLowerConst ≤ sieveCutoff (X : ℝ) := by
  filter_upwards [eventually_exp_sixteen_le] with X hX
  have hx1 : (1 : ℝ) < X := one_lt_of_exp_sixteen_le hX
  exact isSieveCutoff_rpow hX (sieveCutoff_spec hx1)

private theorem eventually_profileS_le_windowG_sq {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, (profileS κ X : ℝ) ≤ windowG X ^ 2 := by
  filter_upwards [tendsto_windowG.eventually (eventually_four_mul_profileArg_le hκ)] with
    X hfours
  have hL := profileL_cast_le_add_one hκ.le X
  have hS := profileS_cast_le_four κ X
  have hGnn := windowG_nonneg X
  have h4L :
      4 * (profileL κ X : ℝ) ≤
        4 * (κ * Real.log (windowG X) +
          Real.sqrt (κ * Real.log (windowG X)) + 1) :=
    mul_le_mul_of_nonneg_left hL (by norm_num)
  have h4LG :
      4 * (profileL κ X : ℝ) * windowG X ≤ windowG X * windowG X :=
    mul_le_mul_of_nonneg_right (h4L.trans hfours) hGnn
  have hsq : windowG X * windowG X = windowG X ^ 2 := by ring
  exact (hS.trans h4LG).trans_eq hsq

/-! ### Eventual `profileS ≤ sieveCutoff` -/

/-- Eventual real comparison `(profileS κ X : ℝ) ≤ sieveCutoff X`.
Not Chebyshev; the cutoff power is `isSieveCutoff_rpow`. -/
theorem eventually_profileS_le_sieveCutoff {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, (profileS κ X : ℝ) ≤ sieveCutoff (X : ℝ) := by
  filter_upwards [eventually_exp_sixteen_le,
    eventually_profileS_le_windowG_sq hκ,
    tendsto_natCast_atTop_atTop.eventually eventually_log_sq_le_rpow,
    eventually_rpow_le_sieveCutoff] with X hXexp hSG2 hlogsq hcut
  have hGeq : windowG X = Real.log (X : ℝ) :=
    windowG_eq_log_of_exp_sixteen hXexp
  have hG2 : windowG X ^ 2 ≤ (X : ℝ) ^ eulerProdLowerConst := by
    rw [hGeq]
    exact hlogsq
  exact hSG2.trans (hG2.trans hcut)

/-- Same comparison at the standard clock `κ = 1 / log ρ`. -/
theorem eventually_profileS_le_sieveCutoff_stdKappa {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      (profileS (stdKappa ρ) X : ℝ) ≤ sieveCutoff (X : ℝ) :=
  eventually_profileS_le_sieveCutoff (stdKappa_pos hρ)

private theorem eventually_profileS_nat_le_sieveCutoff {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, profileS κ X ≤ sieveCutoff (X : ℝ) := by
  filter_upwards [eventually_profileS_le_sieveCutoff hκ] with X h
  exact Nat.cast_le.mp h

/-! ### Off-band package: `profileS ≤ sieveCutoff` discharged -/

/-- `ActualCrtFibreOffBandVanishes` from off-band mass vanishing.
The averaging hypotheses `profileS ≤ sieveCutoff` and `0 < profileL`
are theorems for `κ > 0`. Does **not** claim the mass limit. -/
theorem actualCrtFibreOffBandVanishes_of_offBandMass {κ : ℝ} (hκ : 0 < κ)
    (hmass : Tendsto (fun X : ℕ =>
        lateFibreOffBandMass (profileS κ X) (sieveCutoff (X : ℝ))
          (profileS κ X) (profileL κ X))
      atTop (nhds 0)) :
    ActualCrtFibreOffBandVanishes κ := by
  refine ⟨?hsy, hmass⟩
  filter_upwards [eventually_profileS_nat_le_sieveCutoff hκ,
    eventually_one_le_profileL hκ] with X hSy hL
  exact ⟨hSy, Nat.succ_le_iff.mp hL⟩

end

end PrimeGapNormality.Prime
