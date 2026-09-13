import PrimeGapNormality.Prime.CrtMixUnnormStopped
import PrimeGapNormality.Prime.CrtProfileRParity
import PrimeGapNormality.Prime.ProfileInequalities
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Mix-Unnorm Stopped comparison without profile-parity binders

Lake-green `CrtMixUnnormStopped.crtMixUnnorm_stoppedShapeL1_le`
still takes `L ≤ r` and `Odd (r − L)` as binders; those lemmas
are private in `StoppedPrime`. Lake-green `CrtProfileRParity`
republishes both facts for every `L`, `d0` as `crtMixProf_le_at`
and `crtMixProf_odd_at`. This leaf feeds them, so the Stopped
inequality remains only with `1 ≤ profileL` and `0 < windowNX`.

Eventual `1 ≤ profileL` is already
`ProfileInequalities.eventually_one_le_profileL` (`0 < κ`).
`0 < windowNX` is **not** discharged here: this file does not
import `SingletonLi` (Kuperberg ⇒ PNT density) and does not
import `MixZeta`. Unique names `crtMixUnnormClosed_*`.

Does **not** import MixZeta, SingletonLi, ExactRootWindowClose,
RootedCutoffTypicalOsc, WeylOf*, CrtHLMismatchVanishing,
CrtMixtureTransfer, CrtFailureMassLimit, or CrtNestedCutoffL1.

Does **not** claim `MixZetaTendstoOne`, AHL, vanishing of mix
`modelRemainder` / `failureMass`, or kernel close.

**Compiled.**
1. Pointwise Stopped L¹ + failure vs unnorm + additive `|1−ζ|`,
   without `L ≤ r` and `Odd (r − L)` binders
   (`crtMixProf_le_at`, `crtMixProf_odd_at`).
2. Eventual form (`0 < κ`): `1 ≤ profileL` is a theorem;
   remaining binder is eventual `0 < windowNX`.

**Not compiled.** `MixZetaTendstoOne`. AHL. Mix
`modelRemainder` / `failureMass` vanish. `0 < windowNX` from
Kuperberg. Kernel close.

**Remaining hyps.** Pointwise `1 ≤ profileL` and `0 < windowNX`
on the pointwise theorem. Eventual `0 < windowNX` on the
eventual theorem (honest; not discharged). Mix `failureMass` /
`modelRemainder`; `adverseBudget` / AHL; `MixZetaTendstoOne`
(not claimed). Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `L ≤ profileR L d0` | theorem (`crtMixProf_le_at`) |
| `Odd (profileR L d0 − L)` | theorem (`crtMixProf_odd_at`) |
| Stopped L¹ without `L ≤ r` and Odd | theorem (`crtMixUnnormClosed_stoppedShapeL1_le`) |
| eventual `1 ≤ profileL` (`0 < κ`) | theorem (`eventually_one_le_profileL`) |
| eventual Stopped L¹ | theorem (`crtMixUnnormClosed_eventually`; remaining eventual `0 < windowNX`) |
| `0 < windowNX` from Kuperberg | remaining (not imported) |
| mix `failureMass` / `modelRemainder` vanish | remaining |
| `adverseBudget` / AHL | remaining |
| `MixZetaTendstoOne` | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `CrtMixUnnormStopped.crtMixUnnorm_stoppedShapeL1_le`;
`CrtProfileRParity.crtMixProf_le_at`, `crtMixProf_odd_at`;
`ProfileInequalities.eventually_one_le_profileL`;
`rounds/round115/09_grok_mixture_gate_and_cutoff_bridge.md` M1.
Contract: API
Audit: GREEN
-/

open Filter

namespace PrimeGapNormality.Prime

/-! ### Pointwise: feed public `profileR` parity -/

/-- Finite stopped comparison of the empirical configuration mass
against the unnormalized V-mix, with `L ≤ r` and `Odd (r − L)`
discharged by `crtMixProf_*_at`. Remaining: `1 ≤ profileL` and
`0 < windowNX`. Does **not** claim MixZeta, AHL, or kernel close. -/
theorem crtMixUnnormClosed_stoppedShapeL1_le
    {κ d0 : ℝ} {X : ℕ}
    (hL : 1 ≤ profileL κ X)
    (hN : 0 < windowNX X) :
    Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X)
        (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) +
      Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
        (profileL κ X) ≤
      Stopped.failureMass (windowOmega κ X)
          (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) +
        2 * Stopped.modelRemainder (windowOmega κ X)
          (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
          (profileR (profileL κ X) d0) +
        2 * Stopped.adverseBudget (windowOmega κ X)
          (actualConfigMass κ X)
          (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
          (profileR (profileL κ X) d0) +
        |1 - mixZeta X| :=
  crtMixUnnorm_stoppedShapeL1_le hL (crtMixProf_le_at κ d0 X)
    (crtMixProf_odd_at κ d0 X) hN

/-! ### Eventual: `1 ≤ profileL` is a theorem; `windowNX` remains -/

/-- Eventual Stopped comparison (`0 < κ`). `1 ≤ profileL` is
`eventually_one_le_profileL`. Remaining binder: eventual
`0 < windowNX` (not discharged from Kuperberg; `SingletonLi` is
not imported). Does **not** claim `MixZetaTendstoOne`, AHL, or
kernel close. -/
theorem crtMixUnnormClosed_eventually
    {κ d0 : ℝ} (hκ : 0 < κ)
    (hN : ∀ᶠ X : ℕ in atTop, 0 < windowNX X) :
    ∀ᶠ X : ℕ in atTop,
      Stopped.shapeL1 (windowOmega κ X) (actualConfigMass κ X)
          (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) +
        Stopped.failureMass (windowOmega κ X) (actualConfigMass κ X)
          (profileL κ X) ≤
        Stopped.failureMass (windowOmega κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X) +
          2 * Stopped.modelRemainder (windowOmega κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) +
          2 * Stopped.adverseBudget (windowOmega κ X)
            (actualConfigMass κ X)
            (finiteRootMixUnnorm X (profileS κ X)) (profileL κ X)
            (profileR (profileL κ X) d0) +
          |1 - mixZeta X| := by
  filter_upwards [eventually_one_le_profileL hκ, hN] with X hL hNX
  exact crtMixUnnormClosed_stoppedShapeL1_le hL hNX

end PrimeGapNormality.Prime
