import PrimeGapNormality.Prime.SieveCutoffCal
import PrimeGapNormality.Prime.EulerProd
import PrimeGapNormality.Prime.ExactRootMix
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Nested cutoffs: `1 − R` from the exact jump, not `(C4)`

R115/09 §3, before `(C4)`. For `X < t ≤ 2X` set
`y₁ = sieveCutoff X`, `y₂ = sieveCutoff t`. The least calibrated
cutoff is monotone. The exact jump

  `(1 − 1/y) / log t < V(y) ≤ 1 / log t`

gives

  `V(y(t)) / V(y(X)) > (1 − 1/y(t)) · log X / log t`,

hence uniformly

  `1 − R ≤ log 2 / log X + 1 / y(t)`.

This is `O(1/G)` with `G = log X`. It is **not** the L¹ bound
`∑ |μ_{y(t)} − μ_{y(X)}| = O(L/G)`, which still needs the model
first moment `M₁ ≤ 12 L`.

Does **not** import MixZeta, SingletonLi, ExactRootWindowClose,
RootedCutoffTypicalOsc, WeylOf*, CrtHLMismatchVanishing, or
CrtMixtureTransfer. Does **not** claim `HLMismatchVanishes`, kernel
closed, or `mixZeta → 1`.

**Compiled.**
1. `1 < X` and `X < t` ⇒ `sieveCutoff X ≤ sieveCutoff t`
   (larger `t` ⇒ smaller `1 / log t` ⇒ cutoff cannot decrease).
2. Jump ratio `R = V(y₂)/V(y₁) > (1 − 1/y₂) · log X / log t`
   (`e^{16} ≤ X`, `X < t`; `y₂ ≥ 2` from primality).
3. Algebra: `1 − (1 − 1/y₂) · log X / log t ≤ log 2 / log X + 1/y₂`
   once `t ≤ 2X`.
4. Hence `1 − R ≤ log 2 / log X + 1/y(t)` pointwise, on
   `t ∈ mixScale X = Ioc X (2X)`, and eventually along `ℕ`.

**Not compiled.** `∑ |μ_{y(t)} − μ_{y(X)}| = O(L/G)`. `M₁ ≤ 12 L`.
`(C1)`–`(C4)`. `HLMismatchVanishes`. Kernel close. `mixZeta → 1`.

**Remaining hyps.** Pointwise `Real.exp 16 ≤ X` (binder) for the
jump; `X < t ≤ 2X` for the `log 2` comparison. Eventual form
discharges the size of `X`. Model first moment remains. Kernel not
closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| least cutoff monotone | theorem (`crtNestVR_sieveCutoff_mono`) |
| jump `R > (1−1/y₂) log X / log t` | theorem (`crtNestVR_ratio_gt`) |
| `1−R ≤ log 2 / log X + 1/y(t)` | theorem (`crtNestVR_one_sub_le_of`) |
| same on `mixScale X = Ioc X (2X)` | theorem (`crtNestVR_one_sub_le_mixScale`) |
| eventual `∀ t ∈ Ioc X (2X)` | theorem (`crtNestVR_one_sub_le`) |
| `Real.exp 16 ≤ X` | remaining hyp (binder; eventual discharges) |
| `M₁ ≤ 12 L` | remaining (not claimed) |
| `∑ \|μ_{y(t)}−μ_{y(X)}\| = O(L/G)` | not claimed |
| `HLMismatchVanishes` / kernel closed | not claimed |
| `mixZeta → 1` | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round115/09_grok_mixture_gate_and_cutoff_bridge.md` §3
before `(C4)`; `EulerProd.isSieveCutoff_jump`;
`SieveCutoffCal.sieveCutoff_spec`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Filter

noncomputable section

/-! ### Elementary comparisons -/

private theorem crtNestVR_one_lt_of_exp_sixteen_le {t : ℝ}
    (ht : Real.exp 16 ≤ t) : 1 < t :=
  lt_of_lt_of_le
    (lt_trans (by norm_num : (1 : ℝ) < 2)
      (lt_trans Real.exp_one_gt_two
        (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 16))))
    ht

private theorem crtNestVR_mul_div (c a b : ℝ) :
    c * (a / b) = c / b * a := by
  rw [div_eq_mul_inv, ← mul_assoc, mul_comm c, mul_assoc, ← div_eq_mul_inv,
    mul_comm]

private theorem crtNestVR_expand (δ r : ℝ) :
    1 - (1 - δ) * r = 1 - r + δ * r := by
  ring

private theorem crtNestVR_one_sub_div {a b : ℝ} (hb : b ≠ 0) :
    1 - a / b = (b - a) / b := by
  rw [sub_div, div_self hb]

private theorem crtNestVR_mem_Ioc {X t : ℕ} (ht : t ∈ Finset.Ioc X (2 * X)) :
    (X : ℝ) < t ∧ (t : ℝ) ≤ 2 * (X : ℝ) := by
  have h := Finset.mem_Ioc.mp ht
  refine ⟨Nat.cast_lt.mpr h.1, ?_⟩
  have hle : (t : ℝ) ≤ ((2 * X : ℕ) : ℝ) := Nat.cast_le.mpr h.2
  simpa [Nat.cast_mul, Nat.cast_ofNat] using hle

/-! ### Monotonicity of the least cutoff -/

/-- Larger `t` makes `1 / log t` smaller, so the least prime with
`V(y) ≤ 1 / log t` cannot decrease. Remaining hyps: `1 < X`, `X < t`. -/
theorem crtNestVR_sieveCutoff_mono {X t : ℝ} (hX : 1 < X) (hXt : X < t) :
    sieveCutoff X ≤ sieveCutoff t := by
  have ht : 1 < t := lt_trans hX hXt
  have hyX : IsSieveCutoff X (sieveCutoff X) := sieveCutoff_spec hX
  have hyt : IsSieveCutoff t (sieveCutoff t) := sieveCutoff_spec ht
  have hX0 : (0 : ℝ) < X := lt_trans (by norm_num : (0 : ℝ) < 1) hX
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hloglt : Real.log X < Real.log t := Real.log_lt_log hX0 hXt
  have hinv : 1 / Real.log t < 1 / Real.log X :=
    one_div_lt_one_div_of_lt hlogX hloglt
  refine le_of_not_gt ?_
  intro hlt
  have hmin : 1 / Real.log X < eulerProd (sieveCutoff t) :=
    hyX.2.2 (sieveCutoff t) hyt.1 hlt
  exact lt_asymm (hmin.trans_le hyt.2.1) hinv

/-- Nonnegativity `0 ≤ 1 − R` from monotonicity and
`eulerProdNat_mono`. Remaining hyps: `1 < X`, `X < t`. -/
theorem crtNestVR_one_sub_nonneg {X t : ℝ} (hX : 1 < X) (hXt : X < t) :
    0 ≤ 1 - eulerProdNat (sieveCutoff t) / eulerProdNat (sieveCutoff X) := by
  have hV : eulerProdNat (sieveCutoff t) ≤ eulerProdNat (sieveCutoff X) :=
    eulerProdNat_mono (crtNestVR_sieveCutoff_mono hX hXt)
  have hpos : 0 < eulerProdNat (sieveCutoff X) := eulerProdNat_pos _
  exact sub_nonneg.mpr ((div_le_one hpos).mpr hV)

/-! ### Jump ratio -/

/-- Paper jump: `R = V(y(t)) / V(y(X)) > (1 − 1/y(t)) · log X / log t`.
Remaining hyps: `Real.exp 16 ≤ X`, `X < t`. Uses
`isSieveCutoff_jump` and the cutoff upper bound `V(y(X)) ≤ 1 / log X`.
Does not claim `O(L/G)`. -/
theorem crtNestVR_ratio_gt {X t : ℝ} (hX : Real.exp 16 ≤ X) (hXt : X < t) :
    (1 - (sieveCutoff t : ℝ)⁻¹) * (Real.log X / Real.log t)
      < eulerProdNat (sieveCutoff t) / eulerProdNat (sieveCutoff X) := by
  have hX1 : 1 < X := crtNestVR_one_lt_of_exp_sixteen_le hX
  have ht16 : Real.exp 16 ≤ t := hX.trans hXt.le
  have ht1 : 1 < t := lt_trans hX1 hXt
  have hyX : IsSieveCutoff X (sieveCutoff X) := sieveCutoff_spec hX1
  have hyt : IsSieveCutoff t (sieveCutoff t) := sieveCutoff_spec ht1
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hV1pos : 0 < eulerProdNat (sieveCutoff X) := eulerProdNat_pos _
  have hfac : 0 < 1 - (sieveCutoff t : ℝ)⁻¹ := one_sub_inv_pos hyt.1
  have hlo : (1 - (sieveCutoff t : ℝ)⁻¹) / Real.log t
      < eulerProdNat (sieveCutoff t) := by
    have h := isSieveCutoff_jump ht16 hyt
    rwa [eulerProd_coe_nat] at h
  have hup : eulerProdNat (sieveCutoff X) ≤ 1 / Real.log X := by
    have h := hyX.2.1
    rwa [← eulerProd_coe_nat]
  have hlog_le_inv : Real.log X ≤ 1 / eulerProdNat (sieveCutoff X) :=
    (le_one_div hV1pos hlogX).mp hup
  have hmid :
      ((1 - (sieveCutoff t : ℝ)⁻¹) / Real.log t)
          / eulerProdNat (sieveCutoff X)
        < eulerProdNat (sieveCutoff t) / eulerProdNat (sieveCutoff X) :=
    div_lt_div_of_pos_right hlo hV1pos
  have hfac_div :
      0 ≤ (1 - (sieveCutoff t : ℝ)⁻¹) / Real.log t :=
    (div_pos hfac hlogt).le
  have hLHS :
      (1 - (sieveCutoff t : ℝ)⁻¹) * (Real.log X / Real.log t)
        = ((1 - (sieveCutoff t : ℝ)⁻¹) / Real.log t) * Real.log X :=
    crtNestVR_mul_div _ _ _
  have hRHS :
      ((1 - (sieveCutoff t : ℝ)⁻¹) / Real.log t)
          / eulerProdNat (sieveCutoff X)
        = ((1 - (sieveCutoff t : ℝ)⁻¹) / Real.log t)
          * (1 / eulerProdNat (sieveCutoff X)) := by
    rw [div_eq_mul_inv, one_div]
  have hle :
      (1 - (sieveCutoff t : ℝ)⁻¹) * (Real.log X / Real.log t)
        ≤ ((1 - (sieveCutoff t : ℝ)⁻¹) / Real.log t)
            / eulerProdNat (sieveCutoff X) := by
    rw [hLHS, hRHS]
    exact mul_le_mul_of_nonneg_left hlog_le_inv hfac_div
  exact hle.trans_lt hmid

/-- Subtracting the jump from `1`. Remaining hyps: `Real.exp 16 ≤ X`,
`X < t`. -/
theorem crtNestVR_one_sub_lt {X t : ℝ} (hX : Real.exp 16 ≤ X)
    (hXt : X < t) :
    1 - eulerProdNat (sieveCutoff t) / eulerProdNat (sieveCutoff X)
      < 1 - (1 - (sieveCutoff t : ℝ)⁻¹) * (Real.log X / Real.log t) :=
  sub_lt_sub_left (crtNestVR_ratio_gt hX hXt) (1 : ℝ)

/-! ### `t ≤ 2X` algebra -/

/-- Paper comparison `log t ≤ log X + log 2` from `t ≤ 2X`.
Remaining hyps: `0 < X`, `0 < t`, `t ≤ 2 * X`. -/
theorem crtNestVR_log_le_add {X t : ℝ} (hX0 : 0 < X) (ht0 : 0 < t)
    (ht2 : t ≤ 2 * X) :
    Real.log t ≤ Real.log X + Real.log 2 := by
  have hle : Real.log t ≤ Real.log (2 * X) :=
    Real.log_le_log ht0 ht2
  have hmul : Real.log (2 * X) = Real.log 2 + Real.log X :=
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'
  rwa [hmul, add_comm] at hle

/-- `1 − (1 − 1/y) · log X / log t ≤ log 2 / log X + 1/y` for
`X < t ≤ 2X`. Remaining hyps: `1 < X`, `X < t`, `t ≤ 2 * X`. -/
theorem crtNestVR_algebra_le {X t : ℝ} {y : ℕ} (hX : 1 < X) (hXt : X < t)
    (ht2 : t ≤ 2 * X) :
    1 - (1 - (y : ℝ)⁻¹) * (Real.log X / Real.log t)
      ≤ Real.log 2 / Real.log X + (y : ℝ)⁻¹ := by
  have hX0 : (0 : ℝ) < X := lt_trans (by norm_num : (0 : ℝ) < 1) hX
  have ht1 : 1 < t := lt_trans hX hXt
  have ht0 : (0 : ℝ) < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht1
  have ha : 0 < Real.log X := Real.log_pos hX
  have hb : 0 < Real.log t := Real.log_pos ht1
  have hab : Real.log X ≤ Real.log t :=
    (Real.log_lt_log hX0 hXt).le
  have hlog2 : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hnum : Real.log t - Real.log X ≤ Real.log 2 := by
    have hle := crtNestVR_log_le_add hX0 ht0 ht2
    rw [add_comm] at hle
    exact (sub_le_iff_le_add).mpr hle
  have hr : Real.log X / Real.log t ≤ 1 := (div_le_one hb).mpr hab
  have hδ : 0 ≤ (y : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hexpand :
      1 - (1 - (y : ℝ)⁻¹) * (Real.log X / Real.log t)
        = 1 - Real.log X / Real.log t
          + (y : ℝ)⁻¹ * (Real.log X / Real.log t) :=
    crtNestVR_expand _ _
  have hrew : 1 - Real.log X / Real.log t =
      (Real.log t - Real.log X) / Real.log t :=
    crtNestVR_one_sub_div hb.ne'
  have hfrac :
      (Real.log t - Real.log X) / Real.log t ≤ Real.log 2 / Real.log t :=
    div_le_div_of_nonneg_right hnum hb.le
  have hba : Real.log 2 / Real.log t ≤ Real.log 2 / Real.log X :=
    div_le_div_of_nonneg_left hlog2.le ha hab
  have hδr :
      (y : ℝ)⁻¹ * (Real.log X / Real.log t) ≤ (y : ℝ)⁻¹ :=
    mul_le_of_le_one_right hδ hr
  calc
    1 - (1 - (y : ℝ)⁻¹) * (Real.log X / Real.log t)
        = (Real.log t - Real.log X) / Real.log t
          + (y : ℝ)⁻¹ * (Real.log X / Real.log t) := by
          rw [hexpand, hrew]
    _ ≤ Real.log 2 / Real.log t
          + (y : ℝ)⁻¹ * (Real.log X / Real.log t) :=
          add_le_add hfrac (le_refl _)
    _ ≤ Real.log 2 / Real.log X
          + (y : ℝ)⁻¹ * (Real.log X / Real.log t) :=
          add_le_add hba (le_refl _)
    _ ≤ Real.log 2 / Real.log X + (y : ℝ)⁻¹ :=
          add_le_add (le_refl (Real.log 2 / Real.log X)) hδr

/-! ### Pointwise `1 − R` bound -/

/-- Paper: `1 − R ≤ log 2 / log X + 1 / y(t)` for `e^{16} ≤ X` and
`X < t ≤ 2X`. Does **not** claim `O(L/G)`. -/
theorem crtNestVR_one_sub_le_of {X t : ℝ} (hX : Real.exp 16 ≤ X)
    (hXt : X < t) (ht2 : t ≤ 2 * X) :
    1 - eulerProdNat (sieveCutoff t) / eulerProdNat (sieveCutoff X)
      ≤ Real.log 2 / Real.log X + (sieveCutoff t : ℝ)⁻¹ :=
  (crtNestVR_one_sub_lt hX hXt).le.trans
    (crtNestVR_algebra_le (crtNestVR_one_lt_of_exp_sixteen_le hX) hXt ht2)

/-- Same bound on `t ∈ mixScale X = Ioc X (2X)`. Remaining hyp:
`Real.exp 16 ≤ (X : ℝ)` (this forces `2 ≤ X` and log positivity). -/
theorem crtNestVR_one_sub_le_mixScale {X t : ℕ}
    (hX : Real.exp 16 ≤ (X : ℝ)) (ht : t ∈ mixScale X) :
    1 - eulerProdNat (sieveCutoff (t : ℝ))
          / eulerProdNat (sieveCutoff (X : ℝ))
      ≤ Real.log 2 / Real.log (X : ℝ) + (sieveCutoff (t : ℝ) : ℝ)⁻¹ := by
  have htI : t ∈ Finset.Ioc X (2 * X) := by
    simpa [mixScale] using ht
  have h := crtNestVR_mem_Ioc htI
  exact crtNestVR_one_sub_le_of hX h.1 h.2

/-! ### Eventual form -/

/-- Eventual `e^{16} ≤ X` along `ℕ`. -/
theorem crtNestVR_eventually_exp_sixteen :
    ∀ᶠ X : ℕ in atTop, Real.exp 16 ≤ (X : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 16))

/-- Eventual `1 − R ≤ log 2 / log X + 1 / y(t)` on the mix support
`Ioc X (2X)`. Remaining: none (size of `X` is eventual). Does **not**
claim `∑ |μ_{y(t)} − μ_{y(X)}| = O(L/G)`. -/
theorem crtNestVR_one_sub_le :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ Finset.Ioc X (2 * X),
      1 - eulerProdNat (sieveCutoff (t : ℝ))
            / eulerProdNat (sieveCutoff (X : ℝ))
        ≤ Real.log 2 / Real.log (X : ℝ) + (sieveCutoff (t : ℝ) : ℝ)⁻¹ := by
  filter_upwards [crtNestVR_eventually_exp_sixteen] with X hX
  intro t ht
  exact crtNestVR_one_sub_le_mixScale hX (by simpa [mixScale] using ht)

end

end PrimeGapNormality.Prime
