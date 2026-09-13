import PrimeGapNormality.Prime.CrtPhysicalRetentionLeEulerQuot
import PrimeGapNormality.Prime.CrtSieveCutoffEulerProdLeInvLog
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.MetricSpace.Basic

/-!
# Physical `lateRetention → 0` from a `log S / log X → 0` binder

Lake-green `CrtPhysicalRetentionLeEulerQuot` gives

  `lateRetention S y ≤ V(y) · log S / eulerProdLowerConst`

at the physical pair `S = profileS`, `y = sieveCutoff X`.
Lake-green `CrtSieveCutoffEulerProdLeInvLog` gives

  `V(sieveCutoff X) ≤ 1 / log X`

once `e^{16} ≤ X`. Substituting (nonnegative `log S`, positive
`c = eulerProdLowerConst`) reconstructs

  `θ ≤ V(y) · log S / c ≤ (1 / c) · (log S / log X)`.

Lake-green `CrtLateRetentionAtCutoff` supplies eventual `0 ≤ θ`.
The sandwich `0 ≤ θ ≤ (1 / c) · (log S / log X)` and a
`log S / log X → 0` **binder** squeeze `θ → 0`.

Does **not** claim the log-ratio tendsto (remaining binder).
Does **not** import `CrtPhysicalRetentionLeLogSOverLogX` or
`CrtLogProfileSDivLogX`. Does **not** claim `hoff`, `hcard`, or
Weyl. No MixZeta. `G(X) = X` is not the remainder scale.
Unique names `crtPhysRetZero_*`.

Does not import MixZeta, TypicalOsc*, ExactRootWindowClose,
ExactLawTypicalSetMassLeOne, WeylOf*, or SingletonLi.

**Compiled.**
1. Algebra: `θ ≤ V · logS / c` and `V ≤ 1 / logX` give
   `θ ≤ (1 / c) · (logS / logX)` (`0 ≤ logS`, `0 < c`,
   `0 < logX`).
2. Eventual `0 ≤ θ` at the physical pair (`0 < κ`).
3. Eventual sandwich `0 ≤ θ ≤ (1 / c) · (log S / log X)`.
4. `Tendsto (log S / log X) 0` ⇒ `Tendsto θ 0` by squeeze.
5. Same at `κ = stdKappa ρ` (`1 < ρ`).

**Not compiled.** The log-ratio tendsto itself. `hoff`. `hcard`.
MixZeta. Weyl. Kernel close.

**Remaining hyps.** The log-ratio tendsto (binder; not claimed).
Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `θ ≤ V log S / c` at the physical pair | theorem (`crtPhysRet_eventually`) |
| `V(sieveCutoff X) ≤ 1 / log X` | theorem (`e^{16} ≤ X`) |
| `θ ≤ (1 / c) · (log S / log X)` | theorem (reconstructed here) |
| eventual `0 ≤ θ` | theorem (`crtLateRet_eventually_nonneg`) |
| eventual sandwich | theorem (`0 < κ`) |
| `lateRetention → 0` | theorem (log-ratio tendsto remaining) |
| same at `stdKappa ρ` | theorem (`1 < ρ`, tendsto remaining) |
| `log S / log X → 0` | remaining (binder) |
| `hoff` / `hcard` / Weyl | not claimed |
| Chebyshev / `G(X) = X` remainder scale | not used |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `CrtPhysicalRetentionLeEulerQuot.crtPhysRet_le_eulerProd_mul_log`,
`crtPhysRet_eventually`, `crtPhysRet_eventually_sixteen_le_profileS`;
`CrtSieveCutoffEulerProdLeInvLog.crtCutV_eulerProdNat_nat_le_inv_log`;
`CrtLateRetentionAtCutoff.crtLateRet_eventually_nonneg`.
Contract: API
-/

open Filter
open scoped Topology

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Algebra: `θ ≤ (1 / c) · (log S / log X)` -/

/-- `θ ≤ V · logS / c` and `V ≤ 1 / logX` give
`θ ≤ (1 / c) · (logS / logX)`. Remaining: `0 ≤ logS`, `0 < c`,
`0 < logX`. Does **not** send `θ` to `0`. -/
theorem crtPhysRetZero_le_of_eulerProd {θ V logS logX c : ℝ}
    (hθ : θ ≤ V * logS / c) (hV : V ≤ 1 / logX) (hlogS : 0 ≤ logS)
    (hc : 0 < c) (hlogX : 0 < logX) :
    θ ≤ (1 / c) * (logS / logX) := by
  have hlogXne : logX ≠ 0 := hlogX.ne'
  have hcne : c ≠ 0 := hc.ne'
  have hmul : V * logS ≤ (1 / logX) * logS :=
    mul_le_mul_of_nonneg_right hV hlogS
  have hdiv : V * logS / c ≤ (1 / logX) * logS / c :=
    div_le_div_of_nonneg_right hmul hc.le
  have hmid : (1 / logX) * logS / c = logS / (c * logX) := by
    rw [div_eq_div_iff hcne (mul_ne_zero hcne hlogXne)]
    calc
      (1 / logX * logS) * (c * logX)
          = logS / logX * (c * logX) := by rw [one_div_mul_eq_div]
      _ = logS / logX * (logX * c) := by rw [mul_comm c]
      _ = logS / logX * logX * c := by rw [← mul_assoc]
      _ = logS * c := by rw [div_mul_cancel₀ logS hlogXne]
  have hform : logS / (c * logX) = (1 / c) * (logS / logX) := by
    calc
      logS / (c * logX)
          = logS / (logX * c) := by rw [mul_comm c]
      _ = logS / logX / c := div_mul_eq_div_div logS logX c
      _ = (logS / logX) * (1 / c) := by rw [div_eq_mul_one_div]
      _ = (1 / c) * (logS / logX) := by rw [mul_comm]
  exact hθ.trans (hdiv.trans_eq (hmid.trans hform))

/-- `e^{16} ≤ X` forces `1 < X` and `0 < log X`. -/
theorem crtPhysRetZero_logX_pos {X : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) : 0 < Real.log (X : ℝ) := by
  have hx1 : (1 : ℝ) < X :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 16)).trans_le hX
  exact Real.log_pos hx1

/-- `16 ≤ S` forces `0 ≤ log S`. -/
theorem crtPhysRetZero_logS_nonneg {S : ℕ} (hS : 16 ≤ S) :
    0 ≤ Real.log (S : ℝ) :=
  Real.log_nonneg
    (Nat.one_le_cast.mpr (le_trans (by decide : (1 : ℕ) ≤ 16) hS))

/-- Physical pair: `lateRetention S (sieveCutoff X)` versus
`(1 / c) · (log S / log X)`. Remaining: `2 ≤ S`, `16 ≤ S`,
`S ≤ sieveCutoff X`, `e^{16} ≤ X`. Does **not** claim `θ → 0`. -/
theorem crtPhysRetZero_le {S X : ℕ} (hS2 : 2 ≤ S) (hS16 : 16 ≤ S)
    (hSy : S ≤ sieveCutoff (X : ℝ)) (hX : Real.exp 16 ≤ (X : ℝ)) :
    lateRetention S (sieveCutoff (X : ℝ)) ≤
      (1 / eulerProdLowerConst) *
        (Real.log (S : ℝ) / Real.log (X : ℝ)) :=
  crtPhysRetZero_le_of_eulerProd
    (crtPhysRet_le_eulerProd_mul_log hS2 hS16 hSy)
    (crtCutV_eulerProdNat_nat_le_inv_log hX)
    (crtPhysRetZero_logS_nonneg hS16) eulerProdLowerConst_pos
    (crtPhysRetZero_logX_pos hX)

/-! ### Eventual sandwich at the physical pair -/

/-- Eventual `e^{16} ≤ X`. -/
theorem crtPhysRetZero_eventually_exp_sixteen :
    ∀ᶠ X : ℕ in atTop, Real.exp 16 ≤ (X : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 16))

/-- Eventual `θ ≤ (1 / c) · (log S / log X)` at the physical pair.
Remaining: `0 < κ`. Does **not** claim `lateRetention → 0`. -/
theorem crtPhysRetZero_eventually_le {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ≤
        (1 / eulerProdLowerConst) *
          (Real.log (profileS κ X : ℝ) / Real.log (X : ℝ)) := by
  filter_upwards [crtPhysRet_eventually hκ,
    crtPhysRet_eventually_sixteen_le_profileS hκ,
    crtPhysRetZero_eventually_exp_sixteen] with X hθ hS16 hX
  exact crtPhysRetZero_le_of_eulerProd hθ
    (crtCutV_eulerProdNat_nat_le_inv_log hX)
    (crtPhysRetZero_logS_nonneg hS16) eulerProdLowerConst_pos
    (crtPhysRetZero_logX_pos hX)

/-- Eventual sandwich `0 ≤ θ ≤ (1 / c) · (log S / log X)`.
Remaining: `0 < κ`. Does **not** claim the log-ratio tendsto. -/
theorem crtPhysRetZero_eventually {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      0 ≤ lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ∧
        lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ≤
          (1 / eulerProdLowerConst) *
            (Real.log (profileS κ X : ℝ) / Real.log (X : ℝ)) := by
  filter_upwards [crtLateRet_eventually_nonneg hκ,
    crtPhysRetZero_eventually_le hκ] with X hθ0 hθle
  exact ⟨hθ0, hθle⟩

/-! ### Squeeze: log-ratio binder ⇒ `lateRetention → 0` -/

/-- Scale a vanishing ratio by `1 / c`. Remaining: the ratio
tendsto. -/
theorem crtPhysRetZero_tendsto_const_mul {r : ℕ → ℝ} {c : ℝ}
    (hr : Tendsto r atTop (nhds 0)) :
    Tendsto (fun X : ℕ => (1 / c) * r X) atTop (nhds 0) :=
  mul_zero (1 / c) ▸ (tendsto_const_nhds (x := (1 / c : ℝ))).mul hr

/-- Squeeze `0 ≤ θ ≤ (1 / c) · r` with `r → 0`. Remaining: the
ratio tendsto. -/
theorem crtPhysRetZero_squeeze {θ r : ℕ → ℝ} {c : ℝ}
    (hθ0 : ∀ᶠ X : ℕ in atTop, 0 ≤ θ X)
    (hle : ∀ᶠ X : ℕ in atTop, θ X ≤ (1 / c) * r X)
    (hr : Tendsto r atTop (nhds 0)) :
    Tendsto θ atTop (nhds 0) :=
  squeeze_zero' hθ0 hle (crtPhysRetZero_tendsto_const_mul hr)

/-- Physical `lateRetention → 0` at
`(profileS κ X, sieveCutoff X)`. Remaining: `0 < κ` and the
log-ratio tendsto binder. Does **not** claim that tendsto.
Does **not** claim `hoff` or `hcard`. -/
theorem crtPhysRetZero_tendsto {κ : ℝ} (hκ : 0 < κ)
    (hlog : Tendsto (fun X : ℕ =>
        Real.log (profileS κ X : ℝ) / Real.log (X : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun X : ℕ =>
        lateRetention (profileS κ X) (sieveCutoff (X : ℝ)))
      atTop (nhds 0) :=
  crtPhysRetZero_squeeze
    (crtLateRet_eventually_nonneg hκ)
    (crtPhysRetZero_eventually_le hκ) hlog

/-- Same `lateRetention → 0` at `κ = stdKappa ρ`. Remaining:
`1 < ρ` and the log-ratio tendsto binder. Does **not** claim
that tendsto, `hoff`, or `hcard`. -/
theorem crtPhysRetZero_tendsto_stdKappa {ρ : ℝ} (hρ : 1 < ρ)
    (hlog : Tendsto (fun X : ℕ =>
        Real.log (profileS (stdKappa ρ) X : ℝ) / Real.log (X : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun X : ℕ =>
        lateRetention (profileS (stdKappa ρ) X) (sieveCutoff (X : ℝ)))
      atTop (nhds 0) :=
  crtPhysRetZero_tendsto (stdKappa_pos hρ) hlog

/-- Same sandwich at `κ = stdKappa ρ`. Remaining: `1 < ρ`. -/
theorem crtPhysRetZero_eventually_stdKappa {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      0 ≤ lateRetention (profileS (stdKappa ρ) X)
          (sieveCutoff (X : ℝ)) ∧
        lateRetention (profileS (stdKappa ρ) X)
            (sieveCutoff (X : ℝ)) ≤
          (1 / eulerProdLowerConst) *
            (Real.log (profileS (stdKappa ρ) X : ℝ) /
              Real.log (X : ℝ)) :=
  crtPhysRetZero_eventually (stdKappa_pos hρ)

end

end PrimeGapNormality.Prime
