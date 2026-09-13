import PrimeGapNormality.Prime.ProfileSLeSieveCutoff

/-!
# Eventual `0 < lateRetention ≤ 1` at the physical cutoff pair

`lateRetention S y` is `rootedEulerProdNat S y` (paper `ϑ`).
EulerProd / ModelShortPattern give `0 < rootedEulerProdNat z y`
and `rootedEulerProdNat z y ≤ 1` once `2 ≤ z`. This leaf
instantiates those comparisons at the physical CRT pair

  `(profileS κ X, sieveCutoff (X : ℝ))`

for `0 < κ`. Eventual `2 ≤ profileS` follows from compiled
`eventually_one_le_profileL` (`1 ≤ L` and `1 ≤ windowG` already
force `4 ≤ 4 L G`). Eventual `(profileS : ℝ) ≤ sieveCutoff` is
lake-green `ProfileSLeSieveCutoff.eventually_profileS_le_sieveCutoff`
(reused, not re-proved).

Unconditional `0 ≤ lateRetention S y` is already
`ModelPhaseForallOmega.lateRetention_nonneg` (and a private copy in
`CardinalitySymMass`). This leaf does **not** duplicate that name.
Under `2 ≤ S` it records `0 ≤` as `(rootedEulerProdNat_pos).le`.

Does **not** import MixZeta, TypicalOsc*, ExactRootWindowClose,
ExactLawTypicalSetMassLeOne, or any WeylOf* file. Does **not** claim
fibrewise mean in `[3L, 5L]`. Does not claim card-`hoff`. Does not
claim Chebyshev / `G(X) = X` (`windowG`, not linear remainder).
Kernel not closed.

**Compiled.**
1. `1 ≤ profileL` ⇒ `2 ≤ profileS`.
2. Eventual `2 ≤ profileS κ X` for `0 < κ`.
3. `2 ≤ S` ⇒ `0 < lateRetention S y` and `lateRetention S y ≤ 1`.
4. Eventual `(profileS : ℝ) ≤ sieveCutoff` (reused lake-green).
5. Eventual `0 < lateRetention` and `lateRetention ≤ 1` at the
   physical pair, and the same at `κ = stdKappa ρ` (`1 < ρ`).

**Not compiled.** Fibrewise mean in `[3L, 5L]`. Card-`hoff`.
Unconditional `lateRetention_nonneg` (already compiled elsewhere).
MixZeta. Typical osc. Weyl. Kernel close.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `0 ≤ lateRetention S y` | theorem elsewhere (`lateRetention_nonneg`; not restated) |
| `2 ≤ S` ⇒ `0 < lateRetention S y` | theorem (`rootedEulerProdNat_pos`) |
| `2 ≤ S` ⇒ `lateRetention S y ≤ 1` | theorem (`rootedEulerProdNat_le_one`) |
| eventual `2 ≤ profileS` (`0 < κ`) | theorem |
| eventual `profileS ≤ sieveCutoff` | theorem (reused `eventually_profileS_le_sieveCutoff`) |
| eventual `0 < lateRetention` at the physical pair | theorem |
| eventual `lateRetention ≤ 1` at the physical pair | theorem |
| fibrewise mean in `[3L, 5L]` | not claimed |
| card-`hoff` / RemCard | not claimed |
| Chebyshev / `G(X) = X` remainder scale | not used |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `EulerProd.rootedEulerProdNat_pos`;
`ModelShortPattern.rootedEulerProdNat_le_one`;
`ProfileSLeSieveCutoff.eventually_profileS_le_sieveCutoff`;
`ProfileInequalities.eventually_one_le_profileL`;
`CardinalitySymMass.lateRetention`.
Contract: API
-/

open Filter

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### `2 ≤ profileS` from `1 ≤ profileL` -/

private theorem crtLateRet_windowG_one_le (X : ℕ) :
    (1 : ℝ) ≤ windowG X :=
  le_max_right _ _

/-- `S = ⌊4 L G⌋` with `1 ≤ L` and `1 ≤ G` meets `2`. Remaining:
`1 ≤ profileL`. -/
theorem crtLateRet_two_le_profileS_of_one_le_profileL {κ : ℝ} {X : ℕ}
    (hL : 1 ≤ profileL κ X) : 2 ≤ profileS κ X := by
  have hLre : (1 : ℝ) ≤ (profileL κ X : ℝ) := Nat.one_le_cast.mpr hL
  have hG : (1 : ℝ) ≤ windowG X := crtLateRet_windowG_one_le X
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have hL0 : (0 : ℝ) ≤ (profileL κ X : ℝ) := Nat.cast_nonneg _
  have h4L : (4 : ℝ) ≤ 4 * (profileL κ X : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hLre h4
    rwa [mul_one] at hmul
  have h4LG :
      (4 : ℝ) * (profileL κ X : ℝ) ≤
        4 * (profileL κ X : ℝ) * windowG X := by
    have hmul :=
      mul_le_mul_of_nonneg_left hG (mul_nonneg h4 hL0)
    rwa [mul_one] at hmul
  have hprod : (2 : ℝ) ≤ 4 * (profileL κ X : ℝ) * windowG X :=
    (by norm_num : (2 : ℝ) ≤ 4).trans (h4L.trans h4LG)
  exact Nat.le_floor hprod

/-- Eventual `2 ≤ profileS`. Remaining: `0 < κ`. -/
theorem crtLateRet_eventually_two_le_profileS {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, 2 ≤ profileS κ X := by
  filter_upwards [eventually_one_le_profileL hκ] with X hL
  exact crtLateRet_two_le_profileS_of_one_le_profileL hL

/-! ### Euler product at `lateRetention = rootedEulerProdNat` -/

/-- `2 ≤ S` ⇒ `0 < lateRetention S y`. Unfolds the name
`lateRetention`. Remaining: `2 ≤ S`. -/
theorem crtLateRet_pos_of_two_le {S y : ℕ} (hS : 2 ≤ S) :
    0 < lateRetention S y := by
  unfold lateRetention
  exact rootedEulerProdNat_pos hS

/-- `2 ≤ S` ⇒ `lateRetention S y ≤ 1`. Remaining: `2 ≤ S`. -/
theorem crtLateRet_le_one_of_two_le {S y : ℕ} (hS : 2 ≤ S) :
    lateRetention S y ≤ 1 := by
  unfold lateRetention
  exact rootedEulerProdNat_le_one hS

/-- `2 ≤ S` ⇒ `0 ≤ lateRetention S y`. Does **not** restate
`lateRetention_nonneg` (all `S`, `y`). Remaining: `2 ≤ S`. -/
theorem crtLateRet_nonneg_of_two_le {S y : ℕ} (hS : 2 ≤ S) :
    0 ≤ lateRetention S y :=
  (crtLateRet_pos_of_two_le hS).le

/-! ### Physical pair `(profileS, sieveCutoff)` -/

/-- Eventual averaging comparison at the physical pair, in `ℕ`.
Reuses lake-green `eventually_profileS_le_sieveCutoff`. Remaining:
`0 < κ`. -/
theorem crtLateRet_eventually_profileS_nat_le_sieveCutoff {κ : ℝ}
    (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, profileS κ X ≤ sieveCutoff (X : ℝ) := by
  filter_upwards [eventually_profileS_le_sieveCutoff hκ] with X h
  exact Nat.cast_le.mp h

/-- Eventual `2 ≤ profileS` and `profileS ≤ sieveCutoff` together.
Remaining: `0 < κ`. -/
theorem crtLateRet_eventually_two_le_and_le_cutoff {κ : ℝ}
    (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      2 ≤ profileS κ X ∧
        (profileS κ X : ℝ) ≤ sieveCutoff (X : ℝ) := by
  filter_upwards [crtLateRet_eventually_two_le_profileS hκ,
    eventually_profileS_le_sieveCutoff hκ] with X hS hSy
  exact ⟨hS, hSy⟩

/-- Eventual `0 < lateRetention` at
`(profileS κ X, sieveCutoff X)`. Remaining: `0 < κ`. -/
theorem crtLateRet_eventually_pos {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      0 < lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) := by
  filter_upwards [crtLateRet_eventually_two_le_profileS hκ] with X hS
  exact crtLateRet_pos_of_two_le hS

/-- Eventual `lateRetention ≤ 1` at the physical pair.
Remaining: `0 < κ`. -/
theorem crtLateRet_eventually_le_one {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ≤ 1 := by
  filter_upwards [crtLateRet_eventually_two_le_profileS hκ] with X hS
  exact crtLateRet_le_one_of_two_le hS

/-- Eventual `0 ≤ lateRetention` at the physical pair, from
`rootedEulerProdNat_pos`. Remaining: `0 < κ`. -/
theorem crtLateRet_eventually_nonneg {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      0 ≤ lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) := by
  filter_upwards [crtLateRet_eventually_pos hκ] with X hpos
  exact hpos.le

/-- Eventual `0 < lateRetention ≤ 1` at the physical pair.
Remaining: `0 < κ`. Does **not** claim fibrewise mean in `[3L, 5L]`. -/
theorem crtLateRet_eventually_pos_and_le_one {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      0 < lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ∧
        lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ≤ 1 := by
  filter_upwards [crtLateRet_eventually_two_le_profileS hκ] with X hS
  exact ⟨crtLateRet_pos_of_two_le hS, crtLateRet_le_one_of_two_le hS⟩

/-- Physical cutoff package: `2 ≤ profileS`, `profileS ≤ sieveCutoff`,
and `0 < lateRetention ≤ 1`. Remaining: `0 < κ`. -/
theorem crtLateRet_eventually_physical {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      2 ≤ profileS κ X ∧
        (profileS κ X : ℝ) ≤ sieveCutoff (X : ℝ) ∧
          0 < lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ∧
            lateRetention (profileS κ X) (sieveCutoff (X : ℝ)) ≤ 1 := by
  filter_upwards [crtLateRet_eventually_two_le_and_le_cutoff hκ] with
    X hpair
  exact ⟨hpair.1, hpair.2, crtLateRet_pos_of_two_le hpair.1,
    crtLateRet_le_one_of_two_le hpair.1⟩

/-! ### Standard clock `κ = 1 / log ρ` -/

/-- Same `2 ≤ profileS` at `κ = stdKappa ρ`. Remaining: `1 < ρ`. -/
theorem crtLateRet_eventually_two_le_profileS_stdKappa {ρ : ℝ}
    (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop, 2 ≤ profileS (stdKappa ρ) X :=
  crtLateRet_eventually_two_le_profileS (stdKappa_pos hρ)

/-- Eventual `0 < lateRetention ≤ 1` at the physical pair with
`κ = stdKappa ρ`. Remaining: `1 < ρ`. -/
theorem crtLateRet_eventually_pos_and_le_one_stdKappa {ρ : ℝ}
    (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      0 < lateRetention (profileS (stdKappa ρ) X)
          (sieveCutoff (X : ℝ)) ∧
        lateRetention (profileS (stdKappa ρ) X)
          (sieveCutoff (X : ℝ)) ≤ 1 :=
  crtLateRet_eventually_pos_and_le_one (stdKappa_pos hρ)

/-- Physical cutoff package at `κ = stdKappa ρ`. Remaining: `1 < ρ`. -/
theorem crtLateRet_eventually_physical_stdKappa {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      2 ≤ profileS (stdKappa ρ) X ∧
        (profileS (stdKappa ρ) X : ℝ) ≤ sieveCutoff (X : ℝ) ∧
          0 < lateRetention (profileS (stdKappa ρ) X)
            (sieveCutoff (X : ℝ)) ∧
            lateRetention (profileS (stdKappa ρ) X)
              (sieveCutoff (X : ℝ)) ≤ 1 :=
  crtLateRet_eventually_physical (stdKappa_pos hρ)

end

end PrimeGapNormality.Prime
