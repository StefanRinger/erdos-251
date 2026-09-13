import PrimeGapNormality.Prime.CrtFailureMassLimit
import PrimeGapNormality.Prime.CrtLateRetentionAtCutoff
import PrimeGapNormality.Prime.EulerProd

/-!
# Physical `lateRetention` versus the paper Euler quotient

`lateRetention S y = rootedEulerProdNat S y` (paper `ϑ`). Lake-green
`EulerProd.rootedEulerProdNat_le_div` bounds the rooted product by
the unsigned quotient `V(y) / V(S)` once `2 ≤ S ≤ y`. The weak
Mertens lower bound `eulerProdNat_ge_mul_inv_log` (`16 ≤ S`) inverts
to `1 / V(S) ≤ log S / eulerProdLowerConst`. Combining gives

  `lateRetention S y ≤ eulerProdNat y * log S / eulerProdLowerConst`.

The physical pair is `(profileS κ X, sieveCutoff X)`. Eventual
`2 ≤ profileS` and `profileS ≤ sieveCutoff` are lake-green
`CrtLateRetentionAtCutoff`. Eventual `16 ≤ profileS` follows from
`profileS = ⌊4 L G⌋` with `1 ≤ G` once `4 ≤ profileL`, using
`CrtFailureMassLimit.tendsto_profileL_atTop`.

This leaf does **not** claim `lateRetention → 0`. It does **not**
replace `eulerProdNat (sieveCutoff X)` by `1 / log X` (the module
`CrtSieveCutoffEulerProdLeInvLog` is not assumed lake-green). It
does **not** claim `hoff`, `hcard`, or Weyl. `G(X) = X` is not the
remainder scale (`windowG`, not linear Chebyshev).

Does **not** import MixZeta, TypicalOsc*, ExactRootWindowClose,
ExactLawTypicalSetMassLeOne, WeylOf*, SingletonLi, or
`CrtSieveCutoffEulerProdLeInvLog`. Kernel not closed.

**Compiled.**
1. Pointwise `lateRetention S y ≤ V(y) / V(S)` from `2 ≤ S ≤ y`.
2. `16 ≤ S` ⇒ `1 / V(S) ≤ log S / eulerProdLowerConst`.
3. Combining: `lateRetention S y ≤ V(y) * log S / eulerProdLowerConst`
   under `2 ≤ S`, `16 ≤ S`, `S ≤ y`.
4. Eventual `16 ≤ profileS` from `4 ≤ profileL` and `1 ≤ windowG`.
5. Eventual bound at `(profileS κ X, sieveCutoff X)` for `0 < κ`.
6. Same at `κ = stdKappa ρ` (`1 < ρ`).

**Not compiled.** `lateRetention → 0`.
`eulerProdNat (sieveCutoff X) ≤ 1 / log X`. `hoff`. `hcard`. Weyl.
Kernel close.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `lateRetention = rootedEulerProdNat` | theorem (`CardinalitySymMass`) |
| `ϑ ≤ V(y)/V(S)` | theorem (`rootedEulerProdNat_le_div`) |
| `c / log S ≤ V(S)` (`16 ≤ S`) | theorem (`eulerProdNat_ge_mul_inv_log`) |
| `1 / V(S) ≤ log S / c` | theorem (invert a positive bound) |
| `ϑ ≤ V(y) log S / c` | theorem (`2 ≤ S`, `16 ≤ S`, `S ≤ y`) |
| eventual `2 ≤ profileS` | theorem (`crtLateRet_eventually_two_le_profileS`) |
| eventual `profileS ≤ sieveCutoff` | theorem (`crtLateRet_eventually_profileS_nat_le_sieveCutoff`) |
| eventual `16 ≤ profileS` | theorem (`tendsto_profileL_atTop`, `⌊4 L G⌋`) |
| eventual physical Euler-quotient bound | theorem (`0 < κ`) |
| same at `stdKappa ρ` | theorem (`1 < ρ`) |
| `lateRetention → 0` | not claimed |
| `V(sieveCutoff X) ≤ 1 / log X` | not claimed |
| `hoff` / `hcard` / Weyl | not claimed |
| Chebyshev / `G(X) = X` remainder scale | not used |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `EulerProd.rootedEulerProdNat_le_div`,
`eulerProdNat_ge_mul_inv_log`, `eulerProdLowerConst_pos`;
`CrtLateRetentionAtCutoff.crtLateRet_eventually_two_le_profileS`,
`crtLateRet_eventually_profileS_nat_le_sieveCutoff`;
`CrtFailureMassLimit.tendsto_profileL_atTop`.
Contract: API
-/

open Filter

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Pointwise Euler-quotient comparisons -/

/-- Unfolded `lateRetention ≤ V(y)/V(S)`. Remaining: `2 ≤ S` and
`S ≤ y`. -/
theorem crtPhysRet_le_div {S y : ℕ} (hS : 2 ≤ S) (hSy : S ≤ y) :
    lateRetention S y ≤ eulerProdNat y / eulerProdNat S := by
  unfold lateRetention
  exact rootedEulerProdNat_le_div hSy hS

/-- Invert the Mertens-lower comparison `c / log S ≤ V(S)`.
Remaining: `16 ≤ S`. -/
theorem crtPhysRet_inv_le_log_div_const {S : ℕ} (hS : 16 ≤ S) :
    1 / eulerProdNat S ≤ Real.log (S : ℝ) / eulerProdLowerConst := by
  have hn16 : (16 : ℝ) ≤ S := Nat.cast_le.mpr hS
  have hlog : 0 < Real.log (S : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) hn16)
  have hlo : 0 < eulerProdLowerConst / Real.log (S : ℝ) :=
    div_pos eulerProdLowerConst_pos hlog
  have hle :
      1 / eulerProdNat S ≤
        1 / (eulerProdLowerConst / Real.log (S : ℝ)) :=
    one_div_le_one_div_of_le hlo (eulerProdNat_ge_mul_inv_log hS)
  have hrw :
      1 / (eulerProdLowerConst / Real.log (S : ℝ)) =
        Real.log (S : ℝ) / eulerProdLowerConst :=
    one_div_div _ _
  exact hle.trans_eq hrw

/-- Combined paper Euler quotient. Remaining: `2 ≤ S`, `16 ≤ S`,
and `S ≤ y`. Does **not** send `lateRetention` to `0`. -/
theorem crtPhysRet_le_eulerProd_mul_log {S y : ℕ} (hS2 : 2 ≤ S)
    (hS16 : 16 ≤ S) (hSy : S ≤ y) :
    lateRetention S y ≤
      eulerProdNat y * Real.log (S : ℝ) / eulerProdLowerConst := by
  have hV : 0 ≤ eulerProdNat y := (eulerProdNat_pos y).le
  calc
    lateRetention S y ≤ eulerProdNat y / eulerProdNat S :=
      crtPhysRet_le_div hS2 hSy
    _ = eulerProdNat y * (1 / eulerProdNat S) :=
      div_eq_mul_one_div _ _
    _ ≤ eulerProdNat y *
          (Real.log (S : ℝ) / eulerProdLowerConst) :=
      mul_le_mul_of_nonneg_left (crtPhysRet_inv_le_log_div_const hS16) hV
    _ = eulerProdNat y * Real.log (S : ℝ) / eulerProdLowerConst :=
      (mul_div_assoc _ _ _).symm

/-! ### Eventual `16 ≤ profileS` from `L → ∞` and `1 ≤ G` -/

private theorem crtPhysRet_windowG_one_le (X : ℕ) :
    (1 : ℝ) ≤ windowG X :=
  le_max_right _ _

/-- `S = ⌊4 L G⌋` with `4 ≤ L` and `1 ≤ G` meets `16`. Remaining:
`4 ≤ profileL`. -/
theorem crtPhysRet_sixteen_le_profileS_of_four_le_profileL {κ : ℝ}
    {X : ℕ} (hL : 4 ≤ profileL κ X) : 16 ≤ profileS κ X := by
  have hLre : (4 : ℝ) ≤ (profileL κ X : ℝ) := Nat.cast_le.mpr hL
  have hG : (1 : ℝ) ≤ windowG X := crtPhysRet_windowG_one_le X
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have hL0 : (0 : ℝ) ≤ (profileL κ X : ℝ) := Nat.cast_nonneg _
  have h4L : (16 : ℝ) ≤ 4 * (profileL κ X : ℝ) := by
    calc
      (16 : ℝ) = 4 * 4 := by norm_num
      _ ≤ 4 * (profileL κ X : ℝ) :=
        mul_le_mul_of_nonneg_left hLre h4
  have h4LG :
      (4 : ℝ) * (profileL κ X : ℝ) ≤
        4 * (profileL κ X : ℝ) * windowG X := by
    have hmul :=
      mul_le_mul_of_nonneg_left hG (mul_nonneg h4 hL0)
    rwa [mul_one] at hmul
  have hprod : (16 : ℝ) ≤ 4 * (profileL κ X : ℝ) * windowG X :=
    h4L.trans h4LG
  exact Nat.le_floor hprod

/-- Eventual `4 ≤ profileL` from `L → ∞`. Remaining: `0 < κ`. -/
theorem crtPhysRet_eventually_four_le_profileL {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, 4 ≤ profileL κ X :=
  (tendsto_profileL_atTop hκ).eventually_ge_atTop 4

/-- Eventual `16 ≤ profileS`. Remaining: `0 < κ`. -/
theorem crtPhysRet_eventually_sixteen_le_profileS {κ : ℝ}
    (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, 16 ≤ profileS κ X := by
  filter_upwards [crtPhysRet_eventually_four_le_profileL hκ] with X hL
  exact crtPhysRet_sixteen_le_profileS_of_four_le_profileL hL

/-- Same `16 ≤ profileS` at `κ = stdKappa ρ`. Remaining: `1 < ρ`. -/
theorem crtPhysRet_eventually_sixteen_le_profileS_stdKappa {ρ : ℝ}
    (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop, 16 ≤ profileS (stdKappa ρ) X :=
  crtPhysRet_eventually_sixteen_le_profileS (stdKappa_pos hρ)

/-! ### Physical pair `(profileS, sieveCutoff)` -/

/-- Eventual Euler-quotient bound at
`(profileS κ X, sieveCutoff X)`. Remaining: `0 < κ`. Does **not**
claim `lateRetention → 0` and does **not** substitute
`V(sieveCutoff X) ≤ 1 / log X`. -/
theorem crtPhysRet_eventually {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ≤
        eulerProdNat (sieveCutoff (X : ℝ)) *
          Real.log (profileS κ X : ℝ) / eulerProdLowerConst := by
  filter_upwards [crtLateRet_eventually_two_le_profileS hκ,
    crtPhysRet_eventually_sixteen_le_profileS hκ,
    crtLateRet_eventually_profileS_nat_le_sieveCutoff hκ] with
    X hS2 hS16 hSy
  exact crtPhysRet_le_eulerProd_mul_log hS2 hS16 hSy

/-- Same Euler-quotient bound at `κ = stdKappa ρ`. Remaining:
`1 < ρ`. -/
theorem crtPhysRet_eventually_stdKappa {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      lateRetention (profileS (stdKappa ρ) X)
          (sieveCutoff (X : ℝ)) ≤
        eulerProdNat (sieveCutoff (X : ℝ)) *
          Real.log (profileS (stdKappa ρ) X : ℝ) /
            eulerProdLowerConst :=
  crtPhysRet_eventually (stdKappa_pos hρ)

end

end PrimeGapNormality.Prime
