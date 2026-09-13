import PrimeGapNormality.Prime.EulerProd
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic

/-!
# Early `m_X → ∞` from singleton survival (general S/T)

Paper (R118/14 §1, confirmed R118/17): for a fixed site
`1 ≤ d ≤ S`, survival through the remaining primes is at most

    ∏_{S < p ≤ y} (1 − 1/(p−1)) ≤ V(y)/V(S) = O(log S / G_X).

The comparison `ϑ ≤ V(y)/V(S)` is
`EulerProd.rootedEulerProdNat_le_div` (`2 ≤ S ≤ y`). The weak
Euler-product lower bound `eulerProdLowerConst = exp(-30)` inverts
to `1/V(S) ≤ log S / c` once `16 ≤ S`. No sharp Mertens
(`V(S) log S > 1/2`) is used; that is a different supplier.

The `O(log S / G)` rim is honest about EulerProd's actual binders:

* EulerProd itself gives `V(y) ≤ 1 / log y` (`2 ≤ y`), hence
  `V(y)/V(S) ≤ (1/c) · (log S / log y)`.
* The paper scale `G_X` (mixture calibration
  `|V(y)⁻¹ / G − 1| → 0`, or a named comparison `V(y) ≤ C / G`)
  remains a binder. Under `|V⁻¹/G − 1| ≤ 1/2` one may take
  `C = 2`, so `V(y)/V(S) ≤ (2/c) · (log S / G)`.

Paper `1/m_X ≤ ε_X + C log S / G`: occupancy of a good actual
root (`1/m ≤` actual average of `1[x_1 = d_X, x_L ≤ S]`) and the
uniform S-error `ε_X` are **binders**. This leaf does not compile
condition S, does not import a spacing hull, and does not use
`ModesImplyWindowCount` as an early window-count supplier.

Does **not** import MixZeta, SingletonLi, EndAPI, AHLSmall,
SieveCirc, SubsetSpacingJoint, PrimeCountingNormalization, kernel files,
or (C4). Does **not** add density or doubling hypotheses to S/T.
Unique names `earlyMx_`.

**Compiled.**
1. Site geometry: `1 ≤ d ≤ S < p` ⇒ `d < p`.
2. `ϑ ≤ V(y)/V(S)` from EulerProd (`2 ≤ S ≤ y`).
3. `1/V(S) ≤ log S / exp(-30)` (`16 ≤ S`).
4. `V(y)/V(S) ≤ V(y) · log S / c` and the same for `ϑ`.
5. EulerProd upper: `V(y) ≤ 1/log y` (`2 ≤ y`), hence
   `V(y)/V(S) ≤ (1/c) · (log S / log y)`.
6. Binder `V(y) ≤ C/G`: `V(y)/V(S) ≤ (C/c) · (log S / G)`.
7. Calibration `|V⁻¹/G − 1| ≤ 1/2` ⇒ `V ≤ 2/G`, hence
   `V(y)/V(S) ≤ (2/c) · (log S / G)`.
8. Algebra `1/m ≤ ε + bound` from occupancy and a one-sided
   S-error; same with the Euler / calibration rims.
9. `ε → 0` and `log S / G → 0` squeeze `1/m → 0`; then
   `m → ∞` (`0 < m` eventually).

**Not compiled.** Sharp `V(S) log S > 1/2`. Condition S as a
theorem. Occupancy of a good actual root. Joint spacing hull.
AC cluster. Kernel close. (C4). AHLSmall. `ModesImplyWindowCount`.
PrimeCountingNormalization. MixZeta. SingletonLi. Density / doubling for T.
`log a_n / n → 0`.

**Remaining hyps.** Uniform S-error `ε_X → 0` (binder). Occupancy
`1/m_X ≤` actual average of the singleton first-`L` test (good
root; binder). Model mean `≤ ϑ` (binder). Cutoff `S ≤ y`. Mixture
calibration `V(y) ≤ C/G` or `|V⁻¹/G − 1| ≤ 1/2` (binder; EulerProd
closes the `1/log y` form instead). `log S / G → 0` (binder; not
claimed from `profileS`, whose public factor is not this leaf).
Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `d < p` from `1 ≤ d ≤ S < p` | theorem (`earlyMx_site_lt`) |
| `ϑ ≤ V(y)/V(S)` | theorem (`rootedEulerProdNat_le_div`; `2 ≤ S ≤ y`) |
| `c / log S ≤ V(S)` (`c = exp(-30)`) | theorem (`eulerProdNat_ge_mul_inv_log`; `16 ≤ S`) |
| `V(y)/V(S) ≤ V(y) log S / c` | theorem (`16 ≤ S`) |
| `ϑ ≤ V(y) log S / c` | theorem (`2 ≤ S`, `16 ≤ S`, `S ≤ y`) |
| `V(y) ≤ 1 / log y` | theorem (`eulerProd_le_inv_log`; `2 ≤ y`) |
| `V(y)/V(S) ≤ (1/c) · (log S / log y)` | theorem (`16 ≤ S`, `2 ≤ y`) |
| `V(y)/V(S) ≤ (C/c) · (log S / G)` | theorem (`V ≤ C/G` remaining) |
| `V ≤ 2/G` from `|V⁻¹/G − 1| ≤ 1/2` | theorem (`0 < V`, `0 < G`) |
| `1/m ≤ ε + ϑ` | theorem (occupancy + one-sided S-error remaining) |
| `1/m ≤ ε + (2/c) · (log S / G)` | theorem (those binders + calibration) |
| `1/m → 0` from `ε → 0` and `log S / G → 0` | theorem (those tendsto remaining) |
| `m_X → ∞` from `1/m → 0` | theorem (`0 < m` eventually) |
| uniform S-error `ε_X → 0` | remaining (binder) |
| occupancy / good actual root | remaining (binder) |
| `V(S) log S > 1/2` | not claimed |
| `ModesImplyWindowCount` | not used |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round118/14_grok_v013_delta.md` §1;
`rounds/round118/17_grok_single_window_delta.md`;
`EulerProd.rootedEulerProdNat_le_div`, `eulerProdNat_ge_mul_inv_log`,
`eulerProd_le_inv_log`, `eulerProdLowerConst`.
Contract: API
-/

open Filter
open scoped Topology

namespace PrimeGapNormality.Prime

set_option linter.unusedVariables false

noncomputable section

/-! ### Site geometry: `1 ≤ d ≤ S < p` forces `d < p` -/

/-- A paper site `1 ≤ d ≤ S` is strictly smaller than every remaining
sieve prime `p > S`. Hence the forbidden class is one of the `p−1`
nonzero residues, and the survival factor is `1 − 1/(p−1)` rather
than `1`. -/
theorem earlyMx_site_lt {d S p : ℕ} (hd : 1 ≤ d) (hdS : d ≤ S)
    (hSp : S < p) : d < p :=
  lt_of_le_of_lt hdS hSp

/-! ### Weak Euler-product constant `exp(-30)` -/

/-- Unfolded weak constant. Not the sharp Mertens value. -/
theorem earlyMx_lowerConst_eq :
    eulerProdLowerConst = Real.exp (-(30 : ℝ)) :=
  rfl

theorem earlyMx_lowerConst_pos : 0 < eulerProdLowerConst :=
  eulerProdLowerConst_pos

/-- `16 ≤ S` forces `0 < log S`. -/
theorem earlyMx_log_S_pos {S : ℕ} (hS : 16 ≤ S) :
    0 < Real.log (S : ℝ) :=
  Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16)
    (Nat.cast_le.mpr hS))

theorem earlyMx_log_S_nonneg {S : ℕ} (hS : 16 ≤ S) :
    0 ≤ Real.log (S : ℝ) :=
  (earlyMx_log_S_pos hS).le

/-! ### `ϑ ≤ V(y)/V(S)` from EulerProd -/

/-- Paper survival product versus the unsigned quotient.
Remaining: `2 ≤ S` and `S ≤ y`. -/
theorem earlyMx_rooted_le_div {S y : ℕ} (hS : 2 ≤ S) (hSy : S ≤ y) :
    rootedEulerProdNat S y ≤ eulerProdNat y / eulerProdNat S :=
  rootedEulerProdNat_le_div hSy hS

/-! ### Invert `c / log S ≤ V(S)` -/

/-- Invert `eulerProdNat_ge_mul_inv_log`. Remaining: `16 ≤ S`.
Does **not** claim `V(S) log S > 1/2`. -/
theorem earlyMx_inv_V_le_log_div_const {S : ℕ} (hS : 16 ≤ S) :
    1 / eulerProdNat S ≤
      Real.log (S : ℝ) / eulerProdLowerConst := by
  have hlo :
      0 < eulerProdLowerConst / Real.log (S : ℝ) :=
    div_pos earlyMx_lowerConst_pos (earlyMx_log_S_pos hS)
  have hle :
      1 / eulerProdNat S ≤
        1 / (eulerProdLowerConst / Real.log (S : ℝ)) :=
    one_div_le_one_div_of_le hlo (eulerProdNat_ge_mul_inv_log hS)
  have hrw :
      1 / (eulerProdLowerConst / Real.log (S : ℝ)) =
        Real.log (S : ℝ) / eulerProdLowerConst :=
    one_div_div _ _
  exact hle.trans_eq hrw

/-- Unsigned quotient versus `V(y) · log S / c`. Remaining: `16 ≤ S`. -/
theorem earlyMx_div_le_V_mul_log {S y : ℕ} (hS : 16 ≤ S) :
    eulerProdNat y / eulerProdNat S ≤
      eulerProdNat y * Real.log (S : ℝ) / eulerProdLowerConst := by
  have hV : 0 ≤ eulerProdNat y := (eulerProdNat_pos y).le
  calc
    eulerProdNat y / eulerProdNat S
        = eulerProdNat y * (1 / eulerProdNat S) :=
          div_eq_mul_one_div _ _
    _ ≤ eulerProdNat y *
          (Real.log (S : ℝ) / eulerProdLowerConst) :=
          mul_le_mul_of_nonneg_left
            (earlyMx_inv_V_le_log_div_const hS) hV
    _ = eulerProdNat y * Real.log (S : ℝ) / eulerProdLowerConst :=
          (mul_div_assoc _ _ _).symm

/-- Rooted product versus `V(y) · log S / c`. Remaining: `2 ≤ S`,
`16 ≤ S`, `S ≤ y`. -/
theorem earlyMx_rooted_le_V_mul_log {S y : ℕ} (hS2 : 2 ≤ S)
    (hS16 : 16 ≤ S) (hSy : S ≤ y) :
    rootedEulerProdNat S y ≤
      eulerProdNat y * Real.log (S : ℝ) / eulerProdLowerConst :=
  (earlyMx_rooted_le_div hS2 hSy).trans (earlyMx_div_le_V_mul_log hS16)

/-! ### EulerProd upper bound `V(y) ≤ 1 / log y` -/

/-- EulerProd's paper-scale upper bound on naturals. Remaining:
`2 ≤ y`. -/
theorem earlyMx_V_le_inv_log {y : ℕ} (hy : 2 ≤ y) :
    eulerProdNat y ≤ 1 / Real.log (y : ℝ) := by
  have hyR : (2 : ℝ) ≤ y := Nat.cast_le.mpr hy
  have h := eulerProd_le_inv_log hyR
  rwa [eulerProd_coe_nat] at h

/-- `V(y)/V(S) ≤ (1/c) · (log S / log y)` with only EulerProd
binders. Remaining: `16 ≤ S` and `2 ≤ y`. -/
theorem earlyMx_div_le_log_div_log {S y : ℕ} (hS : 16 ≤ S)
    (hy : 2 ≤ y) :
    eulerProdNat y / eulerProdNat S ≤
      (1 / eulerProdLowerConst) *
        (Real.log (S : ℝ) / Real.log (y : ℝ)) := by
  have hlogS : 0 ≤ Real.log (S : ℝ) := earlyMx_log_S_nonneg hS
  have hc : 0 < eulerProdLowerConst := earlyMx_lowerConst_pos
  have hmid :
      eulerProdNat y * Real.log (S : ℝ) / eulerProdLowerConst ≤
        (1 / Real.log (y : ℝ)) * Real.log (S : ℝ) /
          eulerProdLowerConst :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (earlyMx_V_le_inv_log hy) hlogS) hc.le
  have hform :
      (1 / Real.log (y : ℝ)) * Real.log (S : ℝ) / eulerProdLowerConst =
        (1 / eulerProdLowerConst) *
          (Real.log (S : ℝ) / Real.log (y : ℝ)) := by
    simp only [div_eq_mul_inv]
    ring
  exact (earlyMx_div_le_V_mul_log (y := y) hS).trans (hmid.trans_eq hform)

/-- Rooted form of `earlyMx_div_le_log_div_log`. Remaining: `2 ≤ S`,
`16 ≤ S`, `S ≤ y`. The hypothesis `2 ≤ y` follows from `16 ≤ S ≤ y`. -/
theorem earlyMx_rooted_le_log_div_log {S y : ℕ} (hS2 : 2 ≤ S)
    (hS16 : 16 ≤ S) (hSy : S ≤ y) :
    rootedEulerProdNat S y ≤
      (1 / eulerProdLowerConst) *
        (Real.log (S : ℝ) / Real.log (y : ℝ)) := by
  have hy : 2 ≤ y :=
    le_trans (le_trans (by norm_num : (2 : ℕ) ≤ 16) hS16) hSy
  exact (earlyMx_rooted_le_div hS2 hSy).trans
    (earlyMx_div_le_log_div_log hS16 hy)

/-! ### Binder `V(y) ≤ C / G` (paper `G_X`, e.g. `windowG`) -/

private theorem earlyMx_mul_log_div_rewrite {C logS G : ℝ} :
    C / G * logS / eulerProdLowerConst =
      (C / eulerProdLowerConst) * (logS / G) := by
  simp only [div_eq_mul_inv]
  ring

/-- Unsigned quotient under a linear comparison `V(y) ≤ C / G`.
Remaining: `16 ≤ S`, `0 ≤ C`, `0 < G`, and `V(y) ≤ C / G`. -/
theorem earlyMx_div_le_of_V_le {S y : ℕ} {G C : ℝ} (hS : 16 ≤ S)
    (hC : 0 ≤ C) (hG : 0 < G) (hV : eulerProdNat y ≤ C / G) :
    eulerProdNat y / eulerProdNat S ≤
      (C / eulerProdLowerConst) * (Real.log (S : ℝ) / G) := by
  have hlogS : 0 ≤ Real.log (S : ℝ) := earlyMx_log_S_nonneg hS
  have hc : 0 < eulerProdLowerConst := earlyMx_lowerConst_pos
  have hmid :
      eulerProdNat y * Real.log (S : ℝ) / eulerProdLowerConst ≤
        (C / G) * Real.log (S : ℝ) / eulerProdLowerConst :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hV hlogS) hc.le
  exact (earlyMx_div_le_V_mul_log (y := y) hS).trans
    (hmid.trans_eq earlyMx_mul_log_div_rewrite)

/-- Rooted form. Remaining: `2 ≤ S`, `16 ≤ S`, `S ≤ y`, `0 ≤ C`,
`0 < G`, and `V(y) ≤ C / G`. -/
theorem earlyMx_rooted_le_of_V_le {S y : ℕ} {G C : ℝ} (hS2 : 2 ≤ S)
    (hS16 : 16 ≤ S) (hSy : S ≤ y) (hC : 0 ≤ C) (hG : 0 < G)
    (hV : eulerProdNat y ≤ C / G) :
    rootedEulerProdNat S y ≤
      (C / eulerProdLowerConst) * (Real.log (S : ℝ) / G) :=
  (earlyMx_rooted_le_div hS2 hSy).trans
    (earlyMx_div_le_of_V_le hS16 hC hG hV)

/-! ### Mixture calibration `|V⁻¹ / G − 1| ≤ δ` -/

/-- Rearrange `|V⁻¹ / G − 1| ≤ δ` with `δ < 1`. Remaining: `0 < V`,
`0 < G`, `δ < 1`. -/
theorem earlyMx_V_le_of_calib {V G δ : ℝ} (hV : 0 < V) (hG : 0 < G)
    (hδ1 : δ < 1) (hδ : |V⁻¹ / G - 1| ≤ δ) :
    V ≤ 1 / (G * (1 - δ)) := by
  have h1δ : 0 < 1 - δ := sub_pos.mpr hδ1
  have hx : 1 - δ ≤ V⁻¹ / G := by
    have hlo := (abs_le.mp hδ).1
    linarith
  have hinv : (1 - δ) * G ≤ V⁻¹ := (le_div_iff₀ hG).mp hx
  have hden : 0 < G * (1 - δ) := mul_pos hG h1δ
  have hle : G * (1 - δ) ≤ V⁻¹ := by rwa [mul_comm]
  have hgoal : (V⁻¹)⁻¹ ≤ (G * (1 - δ))⁻¹ :=
    (inv_le_inv₀ (inv_pos.mpr hV) hden).mpr hle
  rw [inv_inv] at hgoal
  rwa [inv_eq_one_div] at hgoal

private theorem earlyMx_one_div_G_half {G : ℝ} :
    1 / (G * ((1 : ℝ) - 1 / 2)) = (2 : ℝ) / G := by
  have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h12, ← div_eq_mul_one_div G (2 : ℝ), one_div_div]

/-- Calibration `≤ 1/2` gives `V ≤ 2 / G`. Remaining: `0 < V`,
`0 < G`. -/
theorem earlyMx_V_le_two_div_G {V G : ℝ} (hV : 0 < V) (hG : 0 < G)
    (hcalib : |V⁻¹ / G - 1| ≤ (1 / 2 : ℝ)) :
    V ≤ (2 : ℝ) / G := by
  have h :=
    earlyMx_V_le_of_calib hV hG (by norm_num : (1 / 2 : ℝ) < 1) hcalib
  exact h.trans_eq earlyMx_one_div_G_half

/-- `V(y)/V(S) ≤ (2/c) · (log S / G)` from a `1/2`-calibration.
Remaining: `16 ≤ S`, `0 < G`, and the calibration on `V(y)`. -/
theorem earlyMx_div_le_of_calib_half {S y : ℕ} {G : ℝ} (hS : 16 ≤ S)
    (hG : 0 < G)
    (hcalib : |(eulerProdNat y)⁻¹ / G - 1| ≤ (1 / 2 : ℝ)) :
    eulerProdNat y / eulerProdNat S ≤
      ((2 : ℝ) / eulerProdLowerConst) *
        (Real.log (S : ℝ) / G) :=
  earlyMx_div_le_of_V_le hS (by norm_num : (0 : ℝ) ≤ 2) hG
    (earlyMx_V_le_two_div_G (eulerProdNat_pos y) hG hcalib)

/-- Rooted form. Remaining: `2 ≤ S`, `16 ≤ S`, `S ≤ y`, `0 < G`,
and the `1/2`-calibration. -/
theorem earlyMx_rooted_le_of_calib_half {S y : ℕ} {G : ℝ}
    (hS2 : 2 ≤ S) (hS16 : 16 ≤ S) (hSy : S ≤ y) (hG : 0 < G)
    (hcalib : |(eulerProdNat y)⁻¹ / G - 1| ≤ (1 / 2 : ℝ)) :
    rootedEulerProdNat S y ≤
      ((2 : ℝ) / eulerProdLowerConst) *
        (Real.log (S : ℝ) / G) :=
  (earlyMx_rooted_le_div hS2 hSy).trans
    (earlyMx_div_le_of_calib_half hS16 hG hcalib)

/-! ### Algebra: `1/m ≤ ε + bound` -/

/-- One-sided comparison from a two-sided S-error. -/
theorem earlyMx_le_add_of_abs {avg model ε : ℝ}
    (h : |avg - model| ≤ ε) : avg ≤ model + ε := by
  have hsub : avg - model ≤ ε := (abs_le.mp h).2
  linarith

/-- Occupancy plus a one-sided S-error and a model ceiling.
Remaining: `0 < m`, `1/m ≤ avg` (good root), `avg ≤ model + ε`,
and `model ≤ bound`. The uniform S-error is a binder. -/
theorem earlyMx_inv_le_err_add {m : ℕ} {avg model ε bound : ℝ}
    (hm : 0 < m) (hocc : (1 : ℝ) / m ≤ avg)
    (hclose : avg ≤ model + ε) (hmodel : model ≤ bound) :
    (1 : ℝ) / m ≤ ε + bound := by
  have hbound : model + ε ≤ ε + bound := by linarith
  exact hocc.trans (hclose.trans hbound)

/-- Same with the Euler quotient `V(y)/V(S)` as ceiling.
Remaining: occupancy, one-sided S-error, `model ≤ ϑ`, `2 ≤ S ≤ y`. -/
theorem earlyMx_inv_le_err_add_div {m S y : ℕ} {avg model ε : ℝ}
    (hm : 0 < m) (hS2 : 2 ≤ S) (hSy : S ≤ y)
    (hocc : (1 : ℝ) / m ≤ avg) (hclose : avg ≤ model + ε)
    (hmodel : model ≤ rootedEulerProdNat S y) :
    (1 : ℝ) / m ≤ ε + eulerProdNat y / eulerProdNat S :=
  earlyMx_inv_le_err_add hm hocc hclose
    (hmodel.trans (earlyMx_rooted_le_div hS2 hSy))

/-- Paper rim `1/m ≤ ε + (C/c) · (log S / G)`. Remaining: occupancy,
one-sided S-error, `model ≤ ϑ`, `2 ≤ S`, `16 ≤ S`, `S ≤ y`,
`0 ≤ C`, `0 < G`, and `V(y) ≤ C / G`. -/
theorem earlyMx_inv_le_err_add_log_div_G {m S y : ℕ}
    {avg model ε G C : ℝ} (hm : 0 < m) (hS2 : 2 ≤ S) (hS16 : 16 ≤ S)
    (hSy : S ≤ y) (hC : 0 ≤ C) (hG : 0 < G)
    (hocc : (1 : ℝ) / m ≤ avg) (hclose : avg ≤ model + ε)
    (hmodel : model ≤ rootedEulerProdNat S y)
    (hV : eulerProdNat y ≤ C / G) :
    (1 : ℝ) / m ≤
      ε + (C / eulerProdLowerConst) * (Real.log (S : ℝ) / G) :=
  earlyMx_inv_le_err_add hm hocc hclose
    (hmodel.trans (earlyMx_rooted_le_of_V_le hS2 hS16 hSy hC hG hV))

/-- Same with the `1/2`-calibration in place of `V ≤ C/G`.
Remaining: occupancy, one-sided S-error, `model ≤ ϑ`, `2 ≤ S`,
`16 ≤ S`, `S ≤ y`, `0 < G`, and the calibration. -/
theorem earlyMx_inv_le_err_add_calib_half {m S y : ℕ}
    {avg model ε G : ℝ} (hm : 0 < m) (hS2 : 2 ≤ S) (hS16 : 16 ≤ S)
    (hSy : S ≤ y) (hG : 0 < G) (hocc : (1 : ℝ) / m ≤ avg)
    (hclose : avg ≤ model + ε)
    (hmodel : model ≤ rootedEulerProdNat S y)
    (hcalib : |(eulerProdNat y)⁻¹ / G - 1| ≤ (1 / 2 : ℝ)) :
    (1 : ℝ) / m ≤
      ε + ((2 : ℝ) / eulerProdLowerConst) *
        (Real.log (S : ℝ) / G) :=
  earlyMx_inv_le_err_add hm hocc hclose
    (hmodel.trans (earlyMx_rooted_le_of_calib_half hS2 hS16 hSy hG hcalib))

/-- Two-sided S-error form of `earlyMx_inv_le_err_add`. Remaining:
occupancy and `|avg − model| ≤ ε`. -/
theorem earlyMx_inv_le_abs_err_add {m : ℕ} {avg model ε bound : ℝ}
    (hm : 0 < m) (hocc : (1 : ℝ) / m ≤ avg)
    (herr : |avg - model| ≤ ε) (hmodel : model ≤ bound) :
    (1 : ℝ) / m ≤ ε + bound :=
  earlyMx_inv_le_err_add hm hocc (earlyMx_le_add_of_abs herr) hmodel

/-! ### Limits: `1/m → 0` then `m → ∞` -/

theorem earlyMx_inv_nonneg (m : ℕ) : 0 ≤ (1 : ℝ) / m :=
  div_nonneg zero_le_one (Nat.cast_nonneg _)

/-- Sum of a vanishing S-error and a vanishing scaled ratio. -/
theorem earlyMx_tendsto_err_add {ε r : ℕ → ℝ} {C : ℝ}
    (hε : Tendsto ε atTop (nhds 0))
    (hr : Tendsto r atTop (nhds 0)) :
    Tendsto (fun X : ℕ => ε X + C * r X) atTop (nhds 0) :=
  add_zero (0 : ℝ) ▸
    hε.add (mul_zero C ▸ (tendsto_const_nhds (x := C)).mul hr)

/-- Squeeze `0 ≤ 1/m ≤ ε + C · r` with both summands vanishing.
Remaining: the two tendsto binders (uniform S-error and
`log S / G → 0`). -/
theorem earlyMx_inv_tendsto_zero {m : ℕ → ℕ} {ε r : ℕ → ℝ} {C : ℝ}
    (hle : ∀ᶠ X : ℕ in atTop,
      (1 : ℝ) / m X ≤ ε X + C * r X)
    (hε : Tendsto ε atTop (nhds 0))
    (hr : Tendsto r atTop (nhds 0)) :
    Tendsto (fun X : ℕ => (1 : ℝ) / m X) atTop (nhds 0) :=
  squeeze_zero'
    (Eventually.of_forall fun X => earlyMx_inv_nonneg (m X))
    hle (earlyMx_tendsto_err_add hε hr)

/-- `1/m → 0` and eventual positivity force `m → ∞`. This is not
`ModesImplyWindowCount`. -/
theorem earlyMx_card_tendsto_atTop {m : ℕ → ℕ}
    (hpos : ∀ᶠ X : ℕ in atTop, 0 < m X)
    (hinv : Tendsto (fun X : ℕ => (1 : ℝ) / m X) atTop (nhds 0)) :
    Tendsto m atTop atTop := by
  refine tendsto_atTop.mpr fun N => ?_
  have εpos : (0 : ℝ) < 1 / ((N + 1 : ℕ) : ℝ) :=
    one_div_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos N))
  have hdist := (Metric.tendsto_nhds.mp hinv) _ εpos
  filter_upwards [hpos, hdist] with X hm hd
  have hnn : 0 ≤ (1 : ℝ) / m X := earlyMx_inv_nonneg (m X)
  have hlt : (1 : ℝ) / m X < 1 / ((N + 1 : ℕ) : ℝ) := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hd
    exact hd
  have hmpos : (0 : ℝ) < m X := Nat.cast_pos.mpr hm
  have hNpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos N)
  have hlt' : (m X : ℝ)⁻¹ < ((N + 1 : ℕ) : ℝ)⁻¹ := by
    rw [← one_div, ← one_div]
    exact hlt
  have hNmR : ((N + 1 : ℕ) : ℝ) < m X :=
    (inv_lt_inv₀ hmpos hNpos).mp hlt'
  have hNm : N + 1 < m X := Nat.cast_lt.mp hNmR
  exact (Nat.le_succ N).trans (le_of_lt hNm)

/-- Paper growth: the S-error tendsto and `log S / G → 0` force
`m_X → ∞`. Remaining: occupancy packaged into `hle`, the two
tendsto binders, and eventual `0 < m`. -/
theorem earlyMx_card_tendsto_atTop_of_err_add {m : ℕ → ℕ}
    {ε r : ℕ → ℝ} {C : ℝ}
    (hpos : ∀ᶠ X : ℕ in atTop, 0 < m X)
    (hle : ∀ᶠ X : ℕ in atTop,
      (1 : ℝ) / m X ≤ ε X + C * r X)
    (hε : Tendsto ε atTop (nhds 0))
    (hr : Tendsto r atTop (nhds 0)) :
    Tendsto m atTop atTop :=
  earlyMx_card_tendsto_atTop hpos (earlyMx_inv_tendsto_zero hle hε hr)

end

end PrimeGapNormality.Prime
