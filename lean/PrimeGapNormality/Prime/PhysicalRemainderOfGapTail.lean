import PrimeGapNormality.Prime.CharacterRemainder
import PrimeGapNormality.Prime.PhysicalPhaseRoute
import PrimeGapNormality.Prime.PrimeSTD
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Basic

/-!
# Physical character remainder from `GapTailT` (`P = X`)

Paper remainder on the physical window: if `|Φ-Φ_L| ≤ s` with
`s = ρ^{-L} T_ρ(n+L)` (`scaledGapTail`), then

  `‖e(Φ)-e(Φ_L)‖ ≤ (2 + 2π) s`.

`GapTailT` supplies `Avg_{I_X} T_ρ(n+L_X) = O_ρ(G_X)`. That is **O(G)**,
not `o(1)`. For `G(X) = X` and `G(X) = log X` one does **not** have
`G → 0`. Vanishing of the window mean of the character remainder comes
from the profile length `L_X = stdProfileL ρ (G X) → ∞` when `G → ∞`:

  `ρ^{-L_X} G_X ≤ ρ^{-√(log_ρ G_X)} → 0`.

Compiled here, for the constant family `fun _ => Polynomial.X`:

1. Pointwise: `Φ-Φ_L = gapPowerRemainder` of `g j = (seqGap a j : ℝ)`,
   and `scaledGapTail = ρ^{-L} seqGapTail`.
2. Window: the character remainder averages at most `(2+2π)` times the
   scaled-tail average. Empty windows (`card = 0`) evaluate to `0`.
3. Unscaled `O(G)` comparison; vanishing under the extra `G → 0`,
   which is false for `G = X` and `G = log`. Named vanishing from
   `Tendsto` of the scaled-tail window average.
4. `GapTailT` plus `1 < ρ ≤ B` closes
   `PhysicalPhaseRemainderVanishingProfile` by the geometric rate.
5. `nthPrime` at linear scale `G X = X` is a theorem
   (`gapTailT_nthPrime_linear`). The same profile at `windowG`
   still needs `GapTailT nthPrime ρ windowG` (blocked in `PrimeSTD`
   without PNT-scale density). Do not claim log-scale `GapTailT`.

Not compiled: `UniformOrbitTail`, rank-shift, `hU`/`hmatch`, `D`.

Source: `CharacterRemainder`; `PhysicalPhaseRoute`;
`StatisticalCriterion.GapTailT`; `PrimeSTD.gapTailT_nthPrime_linear`.
Contract: API
Audit: GREEN
-/

open Finset Filter Polynomial
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ### Elementary comparisons -/

private theorem rho_pos {ρ : ℝ} (hρ : 1 < ρ) : 0 < ρ :=
  lt_trans (by norm_num : (0 : ℝ) < 1) hρ

private theorem seqGap_cast_nonneg (a : ℕ → ℕ) (n : ℕ) :
    (0 : ℝ) ≤ seqGap a n :=
  Nat.cast_nonneg _

private theorem seqGap_cast_le_succ (a : ℕ → ℕ) (k : ℕ) :
    (seqGap a k : ℝ) ≤ (a (k + 1) : ℝ) :=
  Nat.cast_le.mpr (Nat.sub_le _ _)

private theorem characterRemainderCoeffX_nonneg :
    (0 : ℝ) ≤ 2 + 2 * Real.pi :=
  add_nonneg (by norm_num) (mul_nonneg (by norm_num) Real.pi_pos.le)

/-! ### Window averages -/

private theorem windowAvgReal_nonneg (s : Finset ℕ) {f : ℕ → ℝ}
    (hf : ∀ n ∈ s, 0 ≤ f n) : 0 ≤ windowAvgReal s f :=
  div_nonneg (sum_nonneg hf) (Nat.cast_nonneg _)

private theorem windowAvgReal_mono (s : Finset ℕ) {f g : ℕ → ℝ}
    (h : ∀ n ∈ s, f n ≤ g n) :
    windowAvgReal s f ≤ windowAvgReal s g :=
  div_le_div_of_nonneg_right (sum_le_sum h) (Nat.cast_nonneg _)

private theorem windowAvgReal_const_mul (s : Finset ℕ) (c : ℝ)
    (f : ℕ → ℝ) :
    windowAvgReal s (fun n => c * f n) = c * windowAvgReal s f := by
  unfold windowAvgReal
  rw [← mul_sum, mul_div_assoc]

/-! ### Summability of linear and base-`B` gap tails -/

private theorem summable_shift_div_pow {a : ℕ → ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    (hsm : Summable fun n : ℕ => (a n : ℝ) / ρ ^ n) (k : ℕ) :
    Summable fun j : ℕ => (a (k + j) : ℝ) / ρ ^ (j + 1) := by
  have hρ0 : ρ ≠ 0 := (rho_pos hρ).ne'
  have hshift : Summable fun j : ℕ => (a (j + k) : ℝ) / ρ ^ (j + k) :=
    (summable_nat_add_iff
        (f := fun n : ℕ => (a n : ℝ) / ρ ^ n) k).mpr hsm
  have hshift' : Summable fun j : ℕ => (a (k + j) : ℝ) / ρ ^ (k + j) := by
    simpa [add_comm k] using hshift
  refine (hshift'.mul_left (ρ ^ k / ρ)).congr fun j => ?_
  have hk : ρ ^ (k + j) = ρ ^ k * ρ ^ j := pow_add _ _ _
  have hj : ρ ^ (j + 1) = ρ ^ j * ρ := pow_succ _ _
  field_simp [hρ0, hk, hj, pow_ne_zero k hρ0, pow_ne_zero j hρ0]
  ring

theorem summable_seqGap_div_pow {a : ℕ → ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    (hsm : Summable fun n : ℕ => (a n : ℝ) / ρ ^ n) (n : ℕ) :
    Summable fun j : ℕ => (seqGap a (n + j) : ℝ) / ρ ^ (j + 1) := by
  have hdom := summable_shift_div_pow hρ hsm (n + 1)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hdom
  · exact div_nonneg (seqGap_cast_nonneg a _) (pow_nonneg (rho_pos hρ).le _)
  · have hle : (seqGap a (n + j) : ℝ) ≤ (a (n + j + 1) : ℝ) :=
      seqGap_cast_le_succ a (n + j)
    have hden : 0 ≤ ρ ^ (j + 1) := pow_nonneg (rho_pos hρ).le _
    have hidx : n + j + 1 = n + 1 + j := by
      simp [add_assoc, add_left_comm, add_comm]
    simpa [hidx] using div_le_div_of_nonneg_right hle hden

theorem summable_seqGap_div_base {a : ℕ → ℕ} {ρ : ℝ} {B : ℕ}
    (hρ : 1 < ρ) (_hB : 2 ≤ B) (hρB : ρ ≤ (B : ℝ))
    (hsm : Summable fun n : ℕ => (a n : ℝ) / ρ ^ n) (n : ℕ) :
    Summable fun j : ℕ =>
      (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1) := by
  have hρsm := summable_seqGap_div_pow hρ hsm n
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hρsm
  · exact div_nonneg (seqGap_cast_nonneg a _)
      (pow_nonneg (Nat.cast_nonneg _) _)
  · have hpow : ρ ^ (j + 1) ≤ (B : ℝ) ^ (j + 1) :=
      pow_le_pow_left₀ (rho_pos hρ).le hρB (j + 1)
    have hnn : (0 : ℝ) ≤ seqGap a (n + j) := seqGap_cast_nonneg a _
    exact div_le_div_of_nonneg_left hnn (pow_pos (rho_pos hρ) _) hpow

/-! ### Profile length and `ρ^{-L} G → 0` -/

theorem tendsto_stdProfileL_atTop {ρ : ℝ} (hρ : 1 < ρ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) :
    Tendsto (fun X : ℕ => stdProfileL ρ (G X)) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun N => ?_
  have hlog : Tendsto (fun X : ℕ => logρ ρ (G X)) atTop atTop :=
    (Real.tendsto_log_atTop.comp hG).atTop_div_const (Real.log_pos hρ)
  have hφ :
      Tendsto (fun X : ℕ => logρ ρ (G X) + Real.sqrt (logρ ρ (G X)))
        atTop atTop :=
    tendsto_atTop_mono
      (fun X => le_add_of_nonneg_right (Real.sqrt_nonneg _)) hlog
  obtain ⟨X0, hX0⟩ := Filter.tendsto_atTop_atTop.mp hφ (N : ℝ)
  refine ⟨X0, fun X hX => ?_⟩
  have hle : (N : ℝ) ≤ (stdProfileL ρ (G X) : ℝ) :=
    (hX0 X hX).trans (Nat.le_ceil _)
  exact Nat.cast_le.mp hle

private theorem tendsto_windowG_atTop :
    Tendsto windowG atTop atTop :=
  tendsto_atTop_mono
    (fun X => le_max_left (Real.log (X : ℝ)) (1 : ℝ))
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Local copy of `TruncatedPhaseWindowMatch.tendsto_stdProfileL_windowG_atTop`. -/
theorem tendsto_stdProfileL_windowG_atTop {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto (fun X : ℕ => stdProfileL ρ (windowG X)) atTop atTop :=
  tendsto_stdProfileL_atTop hρ tendsto_windowG_atTop

private theorem rho_rpow_logρ {ρ G : ℝ} (hρ : 1 < ρ) (hG : 0 < G) :
    ρ ^ logρ ρ G = G := by
  have hρpos := rho_pos hρ
  have hlogρ : Real.log ρ ≠ 0 := (Real.log_pos hρ).ne'
  unfold logρ
  rw [Real.rpow_def_of_pos hρpos]
  have hmul : Real.log ρ * (Real.log G / Real.log ρ) = Real.log G := by
    field_simp [hlogρ]
  rw [hmul, Real.exp_log hG]

/-- Profile comparison: `G / ρ^{L} ≤ ρ^{-√(log_ρ G)}` once `1 ≤ G`. -/
theorem G_mul_inv_pow_stdProfileL_le {ρ G : ℝ} (hρ : 1 < ρ)
    (hG : 1 ≤ G) :
    G * (ρ ^ stdProfileL ρ G)⁻¹ ≤
      ρ ^ (-Real.sqrt (logρ ρ G)) := by
  have hρpos := rho_pos hρ
  have hρ1 : (1 : ℝ) ≤ ρ := hρ.le
  have hGpos : (0 : ℝ) < G :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hG
  have hφ :
      logρ ρ G + Real.sqrt (logρ ρ G) ≤ (stdProfileL ρ G : ℝ) :=
    Nat.le_ceil _
  have hmono :
      ρ ^ (logρ ρ G + Real.sqrt (logρ ρ G)) ≤
        ρ ^ (stdProfileL ρ G : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hρ1 hφ
  have hsplit :
      ρ ^ (logρ ρ G + Real.sqrt (logρ ρ G)) =
        ρ ^ logρ ρ G * ρ ^ Real.sqrt (logρ ρ G) :=
    Real.rpow_add hρpos _ _
  have hLnat :
      ρ ^ (stdProfileL ρ G : ℝ) = (ρ : ℝ) ^ stdProfileL ρ G :=
    Real.rpow_natCast _ _
  have hprod : G * ρ ^ Real.sqrt (logρ ρ G) ≤
      (ρ : ℝ) ^ stdProfileL ρ G := by
    rw [hsplit, rho_rpow_logρ hρ hGpos] at hmono
    rwa [hLnat] at hmono
  have hLpos : (0 : ℝ) < (ρ : ℝ) ^ stdProfileL ρ G :=
    pow_pos hρpos _
  have hsqrtpos : (0 : ℝ) < ρ ^ Real.sqrt (logρ ρ G) :=
    Real.rpow_pos_of_pos hρpos _
  have hdiv :
      G * ((ρ : ℝ) ^ stdProfileL ρ G)⁻¹ ≤
        1 / (ρ ^ Real.sqrt (logρ ρ G)) := by
    have hrew :
        G * ((ρ : ℝ) ^ stdProfileL ρ G)⁻¹ =
          G / (ρ : ℝ) ^ stdProfileL ρ G :=
      (div_eq_mul_inv _ _).symm
    rw [hrew, div_le_div_iff₀ hLpos hsqrtpos, one_mul]
    exact hprod
  have hneg : 1 / (ρ ^ Real.sqrt (logρ ρ G)) =
      ρ ^ (-Real.sqrt (logρ ρ G)) := by
    rw [one_div, Real.rpow_neg hρpos.le]
  exact hdiv.trans_eq hneg

/-- Geometric killing factor: `G_X ρ^{-L_X} → 0` when `G → ∞` and `1 < ρ`. -/
theorem tendsto_G_mul_inv_pow_stdProfileL {ρ : ℝ} (hρ : 1 < ρ)
    {G : ℕ → ℝ} (hG : Tendsto G atTop atTop) :
    Tendsto (fun X : ℕ => G X * (ρ ^ stdProfileL ρ (G X))⁻¹)
      atTop (𝓝 0) := by
  have hρpos := rho_pos hρ
  have hinv1 : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  have hinv0 : (-1 : ℝ) < ρ⁻¹ :=
    lt_trans (by norm_num : (-1 : ℝ) < 0) (inv_pos.mpr hρpos)
  have hrpow :=
    tendsto_rpow_atTop_of_base_lt_one (ρ⁻¹) hinv0 hinv1
  have hlog : Tendsto (fun X : ℕ => logρ ρ (G X)) atTop atTop :=
    (Real.tendsto_log_atTop.comp hG).atTop_div_const (Real.log_pos hρ)
  have hsqrt :
      Tendsto (fun X : ℕ => Real.sqrt (logρ ρ (G X))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hbound :
      Tendsto (fun X : ℕ => ρ ^ (-Real.sqrt (logρ ρ (G X))))
        atTop (𝓝 0) := by
    have hfun :
        (fun X : ℕ => ρ ^ (-Real.sqrt (logρ ρ (G X)))) =
          fun X => (ρ⁻¹) ^ Real.sqrt (logρ ρ (G X)) := by
      funext X
      rw [Real.rpow_neg hρpos.le, ← Real.inv_rpow hρpos.le]
    rw [hfun]
    exact hrpow.comp hsqrt
  have hGe : ∀ᶠ X : ℕ in atTop, 1 ≤ G X :=
    hG.eventually_ge_atTop 1
  have hle : ∀ᶠ X : ℕ in atTop,
      G X * (ρ ^ stdProfileL ρ (G X))⁻¹ ≤
        ρ ^ (-Real.sqrt (logρ ρ (G X))) := by
    filter_upwards [hGe] with X hGX
    exact G_mul_inv_pow_stdProfileL_le hρ hGX
  refine squeeze_zero' ?_ hle hbound
  filter_upwards [hGe] with X hGX
  exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hGX)
    (inv_nonneg.mpr (pow_nonneg hρpos.le _))

/-! ### Pointwise remainder for `P = Polynomial.X` -/

theorem seqGapPolyTail_polynomialX (a : ℕ → ℕ) (B n : ℕ) :
    seqGapPolyTail a (fun _ => Polynomial.X) B n =
      ∑' j : ℕ, (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1) := by
  unfold seqGapPolyTail
  refine tsum_congr fun j => ?_
  rw [eval_X]

theorem seqGapPolyTailTrunc_polynomialX (a : ℕ → ℕ) (B L n : ℕ) :
    seqGapPolyTailTrunc a (fun _ => Polynomial.X) B L n =
      ∑ j ∈ range L,
        (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1) := by
  unfold seqGapPolyTailTrunc
  refine sum_congr rfl fun j _ => ?_
  rw [eval_X]

theorem scaledGapTail_seqGap (ρ : ℝ) (a : ℕ → ℕ) (n L : ℕ) :
    scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L =
      (ρ ^ L)⁻¹ * seqGapTail ρ a (n + L) :=
  rfl

theorem seqGapTail_nonneg {ρ : ℝ} (hρ : 1 < ρ) (a : ℕ → ℕ) (n : ℕ) :
    0 ≤ seqGapTail ρ a n :=
  tsum_nonneg fun h =>
    div_nonneg (seqGap_cast_nonneg a _) (pow_nonneg (rho_pos hρ).le _)

theorem scaledGapTail_seqGap_nonneg {ρ : ℝ} (hρ : 1 < ρ)
    (a : ℕ → ℕ) (n L : ℕ) :
    0 ≤ scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L := by
  rw [scaledGapTail_seqGap]
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (rho_pos hρ).le _))
    (seqGapTail_nonneg hρ a _)

theorem seqGapPolyTail_sub_trunc_polynomialX {a : ℕ → ℕ} {B L n : ℕ}
    (_hB : 2 ≤ B)
    (hsm : Summable fun j : ℕ =>
      (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1)) :
    seqGapPolyTail a (fun _ => Polynomial.X) B n -
        seqGapPolyTailTrunc a (fun _ => Polynomial.X) B L n =
      gapPowerRemainder (fun j => (seqGap a j : ℝ)) B 1 n L := by
  have hsplit := hsm.sum_add_tsum_nat_add L
  rw [seqGapPolyTail_polynomialX, seqGapPolyTailTrunc_polynomialX]
  have hsub :
      (∑' j : ℕ, (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1)) -
          ∑ j ∈ range L, (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1) =
        ∑' i : ℕ, (seqGap a (n + (i + L)) : ℝ) / (B : ℝ) ^ (i + L + 1) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [hsub]
  unfold gapPowerRemainder
  refine tsum_congr fun j => ?_
  have hidx : n + (j + L) = n + L + j := by
    simp [add_assoc, add_left_comm, add_comm]
  have hpow : j + L + 1 = L + j + 1 := by
    simp [add_assoc, add_left_comm, add_comm]
  rw [hidx, hpow, pow_one]

theorem gapPowerRemainder_seqGap_nonneg (a : ℕ → ℕ) (B n L : ℕ) :
    0 ≤ gapPowerRemainder (fun j => (seqGap a j : ℝ)) B 1 n L :=
  tsum_nonneg fun j =>
    div_nonneg (pow_nonneg (seqGap_cast_nonneg a _) _)
      (pow_nonneg (Nat.cast_nonneg _) _)

theorem abs_seqGapPolyTail_sub_trunc_polynomialX_eq
    {a : ℕ → ℕ} {B L n : ℕ} (hB : 2 ≤ B)
    (hsm : Summable fun j : ℕ =>
      (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1)) :
    |seqGapPolyTail a (fun _ => Polynomial.X) B n -
        seqGapPolyTailTrunc a (fun _ => Polynomial.X) B L n| =
      gapPowerRemainder (fun j => (seqGap a j : ℝ)) B 1 n L := by
  have hrem :=
    seqGapPolyTail_sub_trunc_polynomialX (a := a) (B := B) (L := L) (n := n)
      hB hsm
  have hnn := gapPowerRemainder_seqGap_nonneg a B n L
  rw [hrem, abs_of_nonneg hnn]

theorem abs_seqGapPolyTail_sub_trunc_le_scaledGapTail
    {a : ℕ → ℕ} {B L n : ℕ} {ρ : ℝ}
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hsmB : Summable fun j : ℕ =>
      (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1))
    (hsmρ : Summable fun j : ℕ =>
      (seqGap a (n + L + j) : ℝ) / ρ ^ (j + 1)) :
    |seqGapPolyTail a (fun _ => Polynomial.X) B n -
        seqGapPolyTailTrunc a (fun _ => Polynomial.X) B L n| ≤
      scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L := by
  have habs :=
    abs_seqGapPolyTail_sub_trunc_polynomialX_eq (a := a) (B := B) (L := L)
      (n := n) hB hsmB
  have hBD : ρ ^ (1 : ℕ) ≤ (B : ℝ) := by
    simpa [pow_one] using hρB
  have hle :=
    gapPowerRemainder_le_pow_scaledGapTail
      (fun j => (seqGap a j : ℝ)) (B := B) (D := 1) (d := 1) (n := n)
      (L := L) hρ hB hBD le_rfl le_rfl (fun j => seqGap_cast_nonneg a j) hsmρ
  have hpow :
      scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L ^ 1 =
        scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L :=
    pow_one _
  rw [habs]
  exact hle.trans_eq hpow

/-! ### Character remainder (T2) for `P = X` -/

theorem norm_e_seqGapPolyTail_sub_trunc_le_scaled
    {a : ℕ → ℕ} {B L n : ℕ} {ρ : ℝ}
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hsmB : Summable fun j : ℕ =>
      (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1))
    (hsmρ : Summable fun j : ℕ =>
      (seqGap a (n + L + j) : ℝ) / ρ ^ (j + 1)) :
    ‖e (seqGapPolyTail a (fun _ => Polynomial.X) B n) -
        e (seqGapPolyTailTrunc a (fun _ => Polynomial.X) B L n)‖ ≤
      (2 + 2 * Real.pi) *
        scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L := by
  set u := seqGapPolyTail a (fun _ => Polynomial.X) B n
  set v := seqGapPolyTailTrunc a (fun _ => Polynomial.X) B L n
  set s := scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L
  have hs0 : 0 ≤ s := scaledGapTail_seqGap_nonneg hρ a n L
  have huv0 :
      |u - v| ≤ s :=
    abs_seqGapPolyTail_sub_trunc_le_scaledGapTail (a := a) (B := B) (L := L)
      (n := n) hB hρ hρB hsmB hsmρ
  have huv :
      |u - v| ≤
        ∑ i ∈ ({1} : Finset ℕ), (1 : ℝ) * s ^ (1 : ℕ) := by
    simpa [sum_singleton, pow_one, mul_one] using huv0
  have hA : ∀ i ∈ ({1} : Finset ℕ), (0 : ℝ) ≤ (1 : ℝ) :=
    fun _ _ => by norm_num
  have hd : ∀ i ∈ ({1} : Finset ℕ), 1 ≤ (1 : ℕ) :=
    fun _ _ => le_rfl
  have hbound :=
    norm_e_sub_le_linear_of_natPower_bound_finset
      ({1} : Finset ℕ) (fun _ => (1 : ℝ)) (fun _ => 1)
      hA hd hs0 huv
  have hsum : ∑ i ∈ ({1} : Finset ℕ), (1 : ℝ) = 1 :=
    sum_singleton (fun _ : ℕ => (1 : ℝ)) (1 : ℕ)
  have hcoeff :
      (2 + 2 * Real.pi * ∑ i ∈ ({1} : Finset ℕ), (1 : ℝ)) * s =
        (2 + 2 * Real.pi) * s := by
    rw [hsum, mul_one]
  exact hbound.trans_eq hcoeff

/-! ### Window comparison -/

theorem windowAvgReal_scaledGapTail_eq {a : ℕ → ℕ} {ρ : ℝ}
    (X L : ℕ) :
    windowAvgReal (seqWindow a X) (fun n =>
      scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L) =
      (ρ ^ L)⁻¹ *
        windowAvgReal (seqWindow a X)
          (fun n => seqGapTail ρ a (n + L)) := by
  have hfun :
      (fun n => scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L) =
        fun n => (ρ ^ L)⁻¹ * seqGapTail ρ a (n + L) := by
    funext n
    rw [scaledGapTail_seqGap]
  rw [hfun, windowAvgReal_const_mul]

theorem windowAvgReal_characterRemainder_le_scaled
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} {L : ℕ → ℕ}
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hsm : Summable fun n : ℕ => (a n : ℝ) / ρ ^ n) (X : ℕ) :
    windowAvgReal (seqWindow a X) (fun n =>
      ‖e (seqGapPolyTail a (fun _ => Polynomial.X) B n) -
          e (seqGapPolyTailTrunc a (fun _ => Polynomial.X) B
            (L X) n)‖) ≤
      (2 + 2 * Real.pi) *
        windowAvgReal (seqWindow a X) (fun n =>
          scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n (L X)) := by
  have hpt : ∀ n ∈ seqWindow a X,
      ‖e (seqGapPolyTail a (fun _ => Polynomial.X) B n) -
          e (seqGapPolyTailTrunc a (fun _ => Polynomial.X) B
            (L X) n)‖ ≤
        (2 + 2 * Real.pi) *
          scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n (L X) := by
    intro n _hn
    exact norm_e_seqGapPolyTail_sub_trunc_le_scaled hB hρ hρB
      (summable_seqGap_div_base hρ hB hρB hsm n)
      (summable_seqGap_div_pow hρ hsm (n + L X))
  have hmono := windowAvgReal_mono (seqWindow a X) hpt
  have hmul :=
    windowAvgReal_const_mul (seqWindow a X) (2 + 2 * Real.pi)
      (fun n => scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n (L X))
  exact hmono.trans_eq hmul

private theorem inv_pow_le_one {ρ : ℝ} (hρ : 1 < ρ) (L : ℕ) :
    (ρ ^ L)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ hρ.le)

theorem windowAvgReal_scaledGapTail_le_seqGapTail
    {a : ℕ → ℕ} {ρ : ℝ} (hρ : 1 < ρ) (X L : ℕ) :
    windowAvgReal (seqWindow a X) (fun n =>
      scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L) ≤
      windowAvgReal (seqWindow a X)
        (fun n => seqGapTail ρ a (n + L)) := by
  rw [windowAvgReal_scaledGapTail_eq]
  have hinv : (ρ ^ L)⁻¹ ≤ 1 := inv_pow_le_one hρ L
  have hT0 :
      0 ≤ windowAvgReal (seqWindow a X)
        (fun n => seqGapTail ρ a (n + L)) :=
    windowAvgReal_nonneg (seqWindow a X) fun n _ =>
      seqGapTail_nonneg hρ a _
  have hmul :
      (ρ ^ L)⁻¹ *
          windowAvgReal (seqWindow a X)
            (fun n => seqGapTail ρ a (n + L)) ≤
        1 *
          windowAvgReal (seqWindow a X)
            (fun n => seqGapTail ρ a (n + L)) :=
    mul_le_mul_of_nonneg_right hinv hT0
  simpa using hmul

/-! ### Honest unscaled `O(G)` bound; `G → 0` is false for `X` and `log` -/

/-- Character remainder averages at most a constant times the unscaled
gap-tail average. Combined with `GapTailT` this is `O(G)`, not `o(1)`. -/
theorem windowAvgReal_characterRemainder_le_seqGapTail
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} {L : ℕ → ℕ}
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hsm : Summable fun n : ℕ => (a n : ℝ) / ρ ^ n) (X : ℕ) :
    windowAvgReal (seqWindow a X) (fun n =>
      ‖e (seqGapPolyTail a (fun _ => Polynomial.X) B n) -
          e (seqGapPolyTailTrunc a (fun _ => Polynomial.X) B
            (L X) n)‖) ≤
      (2 + 2 * Real.pi) *
        windowAvgReal (seqWindow a X)
          (fun n => seqGapTail ρ a (n + L X)) :=
  (windowAvgReal_characterRemainder_le_scaled hB hρ hρB hsm X).trans
    (mul_le_mul_of_nonneg_left
      (windowAvgReal_scaledGapTail_le_seqGapTail hρ X (L X))
      characterRemainderCoeffX_nonneg)

/-- Comparison: `GapTailT` yields an `O(G)` bound on the remainder
average. This does not tend to `0` when `G ↛ 0`. -/
theorem windowAvgReal_characterRemainder_O_G_of_GapTailT
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hB : 2 ≤ B) (hρB : ρ ≤ (B : ℝ))
    (hT : GapTailT a ρ G) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ X : ℕ in atTop,
        windowAvgReal (seqWindow a X) (fun n =>
          ‖e (seqGapPolyTail a (fun _ => Polynomial.X) B n) -
              e (seqGapPolyTailTrunc a (fun _ => Polynomial.X) B
                (stdProfileL ρ (G X)) n)‖) ≤
          K * G X := by
  rcases hT with ⟨hρ, _hGtop, hsm, ⟨C, hC0, hC⟩⟩
  refine ⟨(2 + 2 * Real.pi) * C,
    mul_nonneg characterRemainderCoeffX_nonneg hC0, ?_⟩
  filter_upwards [hC] with X hX
  have hchar :=
    windowAvgReal_characterRemainder_le_seqGapTail (L := fun Y =>
      stdProfileL ρ (G Y)) hB hρ hρB hsm X
  have hTavg := hX.2
  have hmul :
      (2 + 2 * Real.pi) *
          windowAvgReal (seqWindow a X)
            (fun n => seqGapTail ρ a (n + stdProfileL ρ (G X))) ≤
        (2 + 2 * Real.pi) * (C * G X) :=
    mul_le_mul_of_nonneg_left hTavg characterRemainderCoeffX_nonneg
  have hassoc : (2 + 2 * Real.pi) * (C * G X) =
      (2 + 2 * Real.pi) * C * G X := by
    ring
  exact hchar.trans (hmul.trans_eq hassoc)

/-- Vanishing from an unscaled `O(G)` tail bound plus `G → 0`.

This extra hypothesis is **false** for `G X = X` and for
`G X = log X` (and is incompatible with `GapTailT`, which requires
`G → ∞`). The compiled vanishing theorems use `ρ^{-L}` instead. -/
theorem physicalPhaseRemainderVanishing_of_unscaledGapTail_G_zero
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ} {C : ℝ} {L : ℕ → ℕ}
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ)) (_hC0 : 0 ≤ C)
    (hsm : Summable fun n : ℕ => (a n : ℝ) / ρ ^ n)
    (hT : ∀ᶠ X : ℕ in atTop,
      windowAvgReal (seqWindow a X)
          (fun n => seqGapTail ρ a (n + L X)) ≤
        C * G X)
    (hG0 : Tendsto G atTop (𝓝 0)) :
    PhysicalPhaseRemainderVanishing a (fun _ => Polynomial.X) B L := by
  unfold PhysicalPhaseRemainderVanishing
  let bound : ℕ → ℝ := fun X => (2 + 2 * Real.pi) * C * G X
  have hmaj : Tendsto bound atTop (𝓝 0) := by
    have hmul :
        Tendsto (fun X : ℕ => (2 + 2 * Real.pi) * C * G X)
          atTop (𝓝 ((2 + 2 * Real.pi) * C * 0)) :=
      hG0.const_mul ((2 + 2 * Real.pi) * C)
    simpa [bound] using hmul
  refine squeeze_zero' ?nn ?le hmaj
  · exact Eventually.of_forall fun X =>
      windowAvgReal_nonneg (seqWindow a X) fun n _ =>
        norm_nonneg _
  · filter_upwards [hT] with X hTX
    have hchar :=
      windowAvgReal_characterRemainder_le_seqGapTail (a := a) (B := B)
        (ρ := ρ) (L := L) hB hρ hρB hsm X
    have hmul :
        (2 + 2 * Real.pi) *
            windowAvgReal (seqWindow a X)
              (fun n => seqGapTail ρ a (n + L X)) ≤
          (2 + 2 * Real.pi) * (C * G X) :=
      mul_le_mul_of_nonneg_left hTX characterRemainderCoeffX_nonneg
    have hassoc : (2 + 2 * Real.pi) * (C * G X) = bound X := by
      unfold bound
      ring
    exact hchar.trans (hmul.trans_eq hassoc)

/-! ### Named vanishing from the scaled-tail window average -/

/-- If the window average of `scaledGapTail` tends to `0`, the physical
character remainder vanishes. This is the honest extra hypothesis when
the unscaled tail is only `O(G)` with `G ↛ 0`. -/
theorem physicalPhaseRemainderVanishing_of_tendsto_scaledGapTail_avg
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} {L : ℕ → ℕ}
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hsm : Summable fun n : ℕ => (a n : ℝ) / ρ ^ n)
    (havg : Tendsto (fun X : ℕ =>
      windowAvgReal (seqWindow a X) (fun n =>
        scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n (L X)))
      atTop (𝓝 0)) :
    PhysicalPhaseRemainderVanishing a (fun _ => Polynomial.X) B L := by
  unfold PhysicalPhaseRemainderVanishing
  let bound : ℕ → ℝ := fun X =>
    (2 + 2 * Real.pi) *
      windowAvgReal (seqWindow a X) (fun n =>
        scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n (L X))
  have hmaj : Tendsto bound atTop (𝓝 0) := by
    have hmul :
        Tendsto (fun X : ℕ =>
          (2 + 2 * Real.pi) *
            windowAvgReal (seqWindow a X) (fun n =>
              scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n
                (L X)))
          atTop (𝓝 ((2 + 2 * Real.pi) * 0)) :=
      havg.const_mul (2 + 2 * Real.pi)
    simpa [bound] using hmul
  refine squeeze_zero' ?nn ?le hmaj
  · exact Eventually.of_forall fun X =>
      windowAvgReal_nonneg (seqWindow a X) fun n _ =>
        norm_nonneg _
  · exact Eventually.of_forall fun X =>
      windowAvgReal_characterRemainder_le_scaled hB hρ hρB hsm X

/-! ### `GapTailT` plus profile rate `ρ^{-L} G → 0` -/

theorem tendsto_scaledGapTail_avg_of_GapTailT
    {a : ℕ → ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hT : GapTailT a ρ G) :
    Tendsto (fun X : ℕ =>
      windowAvgReal (seqWindow a X) (fun n =>
        scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n
          (stdProfileL ρ (G X))))
      atTop (𝓝 0) := by
  rcases hT with ⟨hρ, hGtop, _hsm, ⟨C, _hC0, hC⟩⟩
  let bound : ℕ → ℝ := fun X =>
    C * G X * (ρ ^ stdProfileL ρ (G X))⁻¹
  have hmaj : Tendsto bound atTop (𝓝 0) := by
    have hcore := tendsto_G_mul_inv_pow_stdProfileL hρ hGtop
    have hmul :
        Tendsto (fun X : ℕ =>
          C * (G X * (ρ ^ stdProfileL ρ (G X))⁻¹))
          atTop (𝓝 (C * 0)) :=
      hcore.const_mul C
    have hfun :
        (fun X : ℕ => C * (G X * (ρ ^ stdProfileL ρ (G X))⁻¹)) =
          bound := by
      funext X
      unfold bound
      ring
    simpa [hfun] using hmul
  refine squeeze_zero' ?nn ?le hmaj
  · exact Eventually.of_forall fun X =>
      windowAvgReal_nonneg (seqWindow a X) fun n _ =>
        scaledGapTail_seqGap_nonneg hρ a _ _
  · filter_upwards [hC] with X hX
    have heq :=
      windowAvgReal_scaledGapTail_eq (a := a) (ρ := ρ) X
        (stdProfileL ρ (G X))
    have hinv0 : 0 ≤ (ρ ^ stdProfileL ρ (G X))⁻¹ :=
      inv_nonneg.mpr (pow_nonneg (rho_pos hρ).le _)
    have hmul :
        (ρ ^ stdProfileL ρ (G X))⁻¹ *
            windowAvgReal (seqWindow a X)
              (fun n => seqGapTail ρ a (n + stdProfileL ρ (G X))) ≤
          (ρ ^ stdProfileL ρ (G X))⁻¹ * (C * G X) :=
      mul_le_mul_of_nonneg_left hX.2 hinv0
    have hassoc :
        (ρ ^ stdProfileL ρ (G X))⁻¹ * (C * G X) = bound X := by
      unfold bound
      ring
    rw [heq]
    exact hmul.trans_eq hassoc

/-- `GapTailT` plus `1 < ρ ≤ B` closes the profile remainder. The
vanishing is from `L_X → ∞` / `ρ^{-L_X} G_X → 0`, not from `G → 0`. -/
theorem physicalPhaseRemainderVanishingProfile_of_GapTailT
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hB : 2 ≤ B) (hρB : ρ ≤ (B : ℝ))
    (hT : GapTailT a ρ G) :
    PhysicalPhaseRemainderVanishingProfile a
      (fun _ => Polynomial.X) B ρ G := by
  rcases hT with ⟨hρ, hGtop, hsm, hC⟩
  have hT' : GapTailT a ρ G := ⟨hρ, hGtop, hsm, hC⟩
  exact physicalPhaseRemainderVanishing_of_tendsto_scaledGapTail_avg
    hB hρ hρB hsm (tendsto_scaledGapTail_avg_of_GapTailT hT')

/-! ### `nthPrime`, linear scale `G X = X` -/

/-- Linear-scale remainder vanishing on `nthPrime`. Uses
`gapTailT_nthPrime_linear` (`G X = X`, not `log X`). Empty windows
are `0`; for `X > 0` one also has `card_seqWindow_nthPrime_pos`. -/
theorem physicalPhaseRemainderVanishingProfile_nthPrime_polynomialX_linear
    {B : ℕ} {ρ : ℝ} (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ)) :
    PhysicalPhaseRemainderVanishingProfile nthPrime
      (fun _ => Polynomial.X) B ρ (fun X => (X : ℝ)) :=
  physicalPhaseRemainderVanishingProfile_of_GapTailT hB hρB
    (gapTailT_nthPrime_linear hρ)

/-! ### `windowG`: implication only (no Chebyshev `GapTailT` at log scale) -/

/-- If `GapTailT` held at `windowG`, the profile remainder would vanish.
`PrimeSTD` does **not** prove `GapTailT nthPrime ρ windowG`; the dyadic
average is `O_ρ(X)`, not `O_ρ(log X)`. -/
theorem physicalPhaseRemainderVanishingProfile_nthPrime_polynomialX_windowG_of_GapTailT
    {B : ℕ} {ρ : ℝ} (hB : 2 ≤ B) (hρB : ρ ≤ (B : ℝ))
    (hT : GapTailT nthPrime ρ windowG) :
    PhysicalPhaseRemainderVanishingProfile nthPrime
      (fun _ => Polynomial.X) B ρ windowG :=
  physicalPhaseRemainderVanishingProfile_of_GapTailT hB hρB hT

/-! ### Constant multiple `C c * Polynomial.X` -/

theorem eval_C_mul_polynomialX (c x : ℝ) :
    eval x (C c * Polynomial.X) = c * x := by
  simp [eval_mul, eval_C, eval_X]

theorem seqGapPolyTail_C_mul_polynomialX {a : ℕ → ℕ} {B n : ℕ} (c : ℝ)
    (hsm : Summable fun j : ℕ =>
      (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1)) :
    seqGapPolyTail a (fun _ => C c * Polynomial.X) B n =
      c * seqGapPolyTail a (fun _ => Polynomial.X) B n := by
  unfold seqGapPolyTail
  have hfun :
      (fun j : ℕ =>
          eval (seqGap a (n + j) : ℝ) (C c * Polynomial.X) /
            (B : ℝ) ^ (j + 1)) =
        fun j =>
          c * ((seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1)) := by
    funext j
    rw [eval_C_mul_polynomialX, mul_div_assoc]
  rw [hfun, hsm.tsum_mul_left]
  refine congrArg (fun t => c * t) ?_
  exact tsum_congr fun j => by rw [eval_X]

theorem seqGapPolyTailTrunc_C_mul_polynomialX (a : ℕ → ℕ)
    (c : ℝ) (B L n : ℕ) :
    seqGapPolyTailTrunc a (fun _ => C c * Polynomial.X) B L n =
      c * seqGapPolyTailTrunc a (fun _ => Polynomial.X) B L n := by
  unfold seqGapPolyTailTrunc
  have hfun :
      (fun j : ℕ =>
          eval (seqGap a (n + j) : ℝ) (C c * Polynomial.X) /
            (B : ℝ) ^ (j + 1)) =
        fun j =>
          c * ((seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1)) := by
    funext j
    rw [eval_C_mul_polynomialX, mul_div_assoc]
  rw [hfun, ← mul_sum]
  refine congrArg (fun t => c * t) ?_
  exact sum_congr rfl fun j _ => by rw [eval_X]

theorem abs_seqGapPolyTail_C_mul_sub_le_mul_scaled
    {a : ℕ → ℕ} {B L n : ℕ} {ρ : ℝ} (c : ℝ)
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hsmB : Summable fun j : ℕ =>
      (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1))
    (hsmρ : Summable fun j : ℕ =>
      (seqGap a (n + L + j) : ℝ) / ρ ^ (j + 1)) :
    |seqGapPolyTail a (fun _ => C c * Polynomial.X) B n -
        seqGapPolyTailTrunc a (fun _ => C c * Polynomial.X) B L n| ≤
      |c| * scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L := by
  have hfull := seqGapPolyTail_C_mul_polynomialX (a := a) (B := B)
    (n := n) c hsmB
  have htrunc :=
    seqGapPolyTailTrunc_C_mul_polynomialX a c B L n
  have hX :=
    abs_seqGapPolyTail_sub_trunc_le_scaledGapTail (a := a) (B := B) (L := L)
      (n := n) hB hρ hρB hsmB hsmρ
  have hdiff :
      seqGapPolyTail a (fun _ => C c * Polynomial.X) B n -
          seqGapPolyTailTrunc a (fun _ => C c * Polynomial.X) B L n =
        c *
          (seqGapPolyTail a (fun _ => Polynomial.X) B n -
            seqGapPolyTailTrunc a (fun _ => Polynomial.X) B L n) := by
    rw [hfull, htrunc]
    ring
  rw [hdiff, abs_mul]
  exact mul_le_mul_of_nonneg_left hX (abs_nonneg _)

theorem norm_e_seqGapPolyTail_C_mul_sub_le_scaled
    {a : ℕ → ℕ} {B L n : ℕ} {ρ : ℝ} (c : ℝ)
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hsmB : Summable fun j : ℕ =>
      (seqGap a (n + j) : ℝ) / (B : ℝ) ^ (j + 1))
    (hsmρ : Summable fun j : ℕ =>
      (seqGap a (n + L + j) : ℝ) / ρ ^ (j + 1)) :
    ‖e (seqGapPolyTail a (fun _ => C c * Polynomial.X) B n) -
        e (seqGapPolyTailTrunc a (fun _ => C c * Polynomial.X) B
          L n)‖ ≤
      (2 + 2 * Real.pi * |c|) *
        scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L := by
  set u := seqGapPolyTail a (fun _ => C c * Polynomial.X) B n
  set v := seqGapPolyTailTrunc a (fun _ => C c * Polynomial.X) B L n
  set s := scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n L
  have hs0 : 0 ≤ s := scaledGapTail_seqGap_nonneg hρ a n L
  have hc0 : 0 ≤ |c| := abs_nonneg _
  have huv0 : |u - v| ≤ |c| * s :=
    abs_seqGapPolyTail_C_mul_sub_le_mul_scaled c hB hρ hρB hsmB hsmρ
  have huv :
      |u - v| ≤
        ∑ i ∈ ({1} : Finset ℕ), |c| * s ^ (1 : ℕ) := by
    simpa [sum_singleton, pow_one] using huv0
  have hA : ∀ i ∈ ({1} : Finset ℕ), (0 : ℝ) ≤ |c| :=
    fun _ _ => hc0
  have hd : ∀ i ∈ ({1} : Finset ℕ), 1 ≤ (1 : ℕ) :=
    fun _ _ => le_rfl
  have hbound :=
    norm_e_sub_le_linear_of_natPower_bound_finset
      ({1} : Finset ℕ) (fun _ => |c|) (fun _ => 1)
      hA hd hs0 huv
  have hsum : ∑ i ∈ ({1} : Finset ℕ), |c| = |c| :=
    sum_singleton (fun _ : ℕ => |c|) (1 : ℕ)
  have hcoeff :
      (2 + 2 * Real.pi * ∑ i ∈ ({1} : Finset ℕ), |c|) * s =
        (2 + 2 * Real.pi * |c|) * s := by
    rw [hsum]
  exact hbound.trans_eq hcoeff

theorem windowAvgReal_characterRemainder_C_mul_le_scaled
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} {L : ℕ → ℕ} (c : ℝ)
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hsm : Summable fun n : ℕ => (a n : ℝ) / ρ ^ n) (X : ℕ) :
    windowAvgReal (seqWindow a X) (fun n =>
      ‖e (seqGapPolyTail a (fun _ => C c * Polynomial.X) B n) -
          e (seqGapPolyTailTrunc a (fun _ => C c * Polynomial.X) B
            (L X) n)‖) ≤
      (2 + 2 * Real.pi * |c|) *
        windowAvgReal (seqWindow a X) (fun n =>
          scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n (L X)) := by
  have hpt : ∀ n ∈ seqWindow a X,
      ‖e (seqGapPolyTail a (fun _ => C c * Polynomial.X) B n) -
          e (seqGapPolyTailTrunc a (fun _ => C c * Polynomial.X) B
            (L X) n)‖ ≤
        (2 + 2 * Real.pi * |c|) *
          scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n (L X) := by
    intro n _hn
    exact norm_e_seqGapPolyTail_C_mul_sub_le_scaled c hB hρ hρB
      (summable_seqGap_div_base hρ hB hρB hsm n)
      (summable_seqGap_div_pow hρ hsm (n + L X))
  have hmono := windowAvgReal_mono (seqWindow a X) hpt
  have hmul :=
    windowAvgReal_const_mul (seqWindow a X) (2 + 2 * Real.pi * |c|)
      (fun n => scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n (L X))
  exact hmono.trans_eq hmul

theorem physicalPhaseRemainderVanishing_C_mul_of_tendsto_scaledGapTail_avg
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} {L : ℕ → ℕ} (c : ℝ)
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ))
    (hsm : Summable fun n : ℕ => (a n : ℝ) / ρ ^ n)
    (havg : Tendsto (fun X : ℕ =>
      windowAvgReal (seqWindow a X) (fun n =>
        scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n (L X)))
      atTop (𝓝 0)) :
    PhysicalPhaseRemainderVanishing a
      (fun _ => C c * Polynomial.X) B L := by
  unfold PhysicalPhaseRemainderVanishing
  let bound : ℕ → ℝ := fun X =>
    (2 + 2 * Real.pi * |c|) *
      windowAvgReal (seqWindow a X) (fun n =>
        scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n (L X))
  have hmaj : Tendsto bound atTop (𝓝 0) := by
    have hmul :
        Tendsto (fun X : ℕ =>
          (2 + 2 * Real.pi * |c|) *
            windowAvgReal (seqWindow a X) (fun n =>
              scaledGapTail ρ (fun j => (seqGap a j : ℝ)) n
                (L X)))
          atTop (𝓝 ((2 + 2 * Real.pi * |c|) * 0)) :=
      havg.const_mul (2 + 2 * Real.pi * |c|)
    simpa [bound] using hmul
  refine squeeze_zero' ?nn ?le hmaj
  · exact Eventually.of_forall fun X =>
      windowAvgReal_nonneg (seqWindow a X) fun n _ =>
        norm_nonneg _
  · exact Eventually.of_forall fun X =>
      windowAvgReal_characterRemainder_C_mul_le_scaled c hB hρ hρB hsm X

theorem physicalPhaseRemainderVanishingProfile_C_mul_of_GapTailT
    {a : ℕ → ℕ} {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ} (c : ℝ)
    (hB : 2 ≤ B) (hρB : ρ ≤ (B : ℝ))
    (hT : GapTailT a ρ G) :
    PhysicalPhaseRemainderVanishingProfile a
      (fun _ => C c * Polynomial.X) B ρ G := by
  rcases hT with ⟨hρ, hGtop, hsm, hC⟩
  have hT' : GapTailT a ρ G := ⟨hρ, hGtop, hsm, hC⟩
  exact physicalPhaseRemainderVanishing_C_mul_of_tendsto_scaledGapTail_avg
    c hB hρ hρB hsm (tendsto_scaledGapTail_avg_of_GapTailT hT')

theorem physicalPhaseRemainderVanishingProfile_nthPrime_C_mul_linear
    {B : ℕ} {ρ : ℝ} (c : ℝ)
    (hB : 2 ≤ B) (hρ : 1 < ρ) (hρB : ρ ≤ (B : ℝ)) :
    PhysicalPhaseRemainderVanishingProfile nthPrime
      (fun _ => C c * Polynomial.X) B ρ (fun X => (X : ℝ)) :=
  physicalPhaseRemainderVanishingProfile_C_mul_of_GapTailT c hB hρB
    (gapTailT_nthPrime_linear hρ)

end PrimeGapNormality.Prime
