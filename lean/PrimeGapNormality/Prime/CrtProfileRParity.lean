import PrimeGapNormality.Prime.EndAPI
import Mathlib.Algebra.Ring.Parity

/-!
# Public `profileR` lower bound and odd gap

`StoppedPrime` already uses `L ≤ profileR L d0` and
`Odd (profileR L d0 − L)`, but those lemmas are **private**.
`KuperbergAHL.profileR_ge` is the lower bound, but Mix-Unnorm
must not import that file. This leaf republishes both facts
under unique `crtMixProf_*` names from `EndAPI` only.

Does **not** claim MixZeta, Stopped L¹, `hoff`, or Weyl.
Does **not** import MixZeta or SingletonLi.
`G(X) = X` is not the remainder scale.

**Compiled.**
1. `L ≤ profileR L d0`.
2. `Odd (profileR L d0 − L)`.
3. Instantiated at `L = profileL κ X`.

**Not compiled.** MixZeta. Kernel close. Additive `|1−ζ|` glue.

**Remaining hyps.** Pointwise `1 ≤ profileL` (eventual theorem
already exists). Mix-Unnorm Stopped comparison (separate leaf).

Does not claim the kernel is closed.

Source: `EndAPI.profileR`; private proofs in `StoppedPrime`.
Contract: API
-/

namespace PrimeGapNormality.Prime

/-- `profileR` is at least `L`. Unique name; does not clash with
`KuperbergAHL.profileR_ge`. -/
theorem crtMixProf_le (L : ℕ) (d0 : ℝ) : L ≤ profileR L d0 := by
  dsimp [profileR]
  split_ifs <;> omega

/-- The defining odd gap of `profileR`. Unique name. -/
theorem crtMixProf_odd (L : ℕ) (d0 : ℝ) :
    Odd (profileR L d0 - L) := by
  dsimp [profileR]
  split_ifs with h
  · exact h
  · have heq : max L ⌈d0 * (L : ℝ)⌉₊ + 1 - L =
        max L ⌈d0 * (L : ℝ)⌉₊ - L + 1 := by omega
    rw [heq]
    have heven : Even (max L ⌈d0 * (L : ℝ)⌉₊ - L) :=
      Nat.not_odd_iff_even.mp h
    have hmod : (max L ⌈d0 * (L : ℝ)⌉₊ - L) % 2 = 0 :=
      Nat.even_iff.mp heven
    rw [Nat.odd_iff, Nat.add_mod, hmod, zero_add]

/-- Same lower bound at `L = profileL κ X`. -/
theorem crtMixProf_le_at (κ d0 : ℝ) (X : ℕ) :
    profileL κ X ≤ profileR (profileL κ X) d0 :=
  crtMixProf_le _ _

/-- Same odd gap at `L = profileL κ X`. -/
theorem crtMixProf_odd_at (κ d0 : ℝ) (X : ℕ) :
    Odd (profileR (profileL κ X) d0 - profileL κ X) :=
  crtMixProf_odd _ _

end PrimeGapNormality.Prime
