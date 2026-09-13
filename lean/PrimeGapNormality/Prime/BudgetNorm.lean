import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite aggregated error-budget normalisation

Primitive one-sided inequality for weighted positive parts. Uses
mathlib `posPart` (`·⁺`); does not redeclare Stopped masses or
`adverseBudget`. No arithmetic rate, no PNT, no new prime hypothesis.

Source: `rounds/round103/07_grok_minimal_budget_small_addendum.md` (1.1)–(1.2);
`rounds/round99/06_gpt_transfer_independent_audit.md` (5.1);
`rounds/round103/04_paper_architecture_minimal_input_v2.md` §3.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 400000

private theorem posPart_le_abs (x : ℝ) : x⁺ ≤ |x| :=
  sup_le (le_abs_self x) (abs_nonneg x)

private theorem posPart_add_le (x y : ℝ) : (x + y)⁺ ≤ x⁺ + y⁺ :=
  sup_le (add_le_add (le_posPart x) (le_posPart y))
    (add_nonneg (posPart_nonneg x) (posPart_nonneg y))

private theorem posPart_add₃_le (x y z : ℝ) : (x + y + z)⁺ ≤ x⁺ + y⁺ + z⁺ := by
  have h1 := posPart_add_le (x + y) z
  have h2 := posPart_add_le x y
  linarith

private theorem posPart_mul_nonneg {c x : ℝ} (hc : 0 ≤ c) : (c * x)⁺ = c * x⁺ := by
  change max (c * x) 0 = c * max x 0
  rw [mul_max_of_nonneg x 0 hc, mul_zero]

private theorem posPart_scale_abs {σ x : ℝ} (hσ : |σ| ≤ 1) : (σ * x)⁺ ≤ |x| :=
  calc
    (σ * x)⁺ ≤ |σ * x| := posPart_le_abs _
    _ = |σ| * |x| := abs_mul _ _
    _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
    _ = |x| := one_mul _

/-- Pointwise (5.1): 1-Lipschitz positive part plus triangle.

Source: `rounds/round99/06_gpt_transfer_independent_audit.md` (5.1).
Contract: API
Audit: GREEN -/
theorem posPart_signed_normed_le {C M q σ N Z : ℝ} (hN : 0 < N) (hσ : |σ| ≤ 1) :
    (σ * (C / N - q))⁺
      ≤ (1 / N) * (σ * (C - M))⁺ + |M / N - M / Z| + |M / Z - q| := by
  have hN0 : (0 : ℝ) ≤ 1 / N := one_div_nonneg.mpr hN.le
  have hsplit :
      C / N - q = (C - M) / N + (M / N - M / Z) + (M / Z - q) := by
    ring
  have hσsplit :
      σ * (C / N - q)
        = σ * ((C - M) / N) + σ * (M / N - M / Z) + σ * (M / Z - q) := by
    rw [hsplit]
    ring
  have hscale : σ * ((C - M) / N) = (1 / N) * (σ * (C - M)) := by
    field_simp [hN.ne']
  have hmain := posPart_add₃_le (σ * ((C - M) / N))
    (σ * (M / N - M / Z)) (σ * (M / Z - q))
  have hx : (σ * ((C - M) / N))⁺ = (1 / N) * (σ * (C - M))⁺ := by
    rw [hscale, posPart_mul_nonneg hN0]
  have hy : (σ * (M / N - M / Z))⁺ ≤ |M / N - M / Z| :=
    posPart_scale_abs hσ
  have hz : (σ * (M / Z - q))⁺ ≤ |M / Z - q| := posPart_scale_abs hσ
  rw [hσsplit]
  calc
    (σ * ((C - M) / N) + σ * (M / N - M / Z) + σ * (M / Z - q))⁺
        ≤ (σ * ((C - M) / N))⁺ + (σ * (M / N - M / Z))⁺ +
            (σ * (M / Z - q))⁺ := hmain
    _ ≤ (1 / N) * (σ * (C - M))⁺ + |M / N - M / Z| + |M / Z - q| := by
        rw [hx]
        linarith [hy, hz]

/-- Finite aggregated normalisation (1.1).

Source: `rounds/round103/07_grok_minimal_budget_small_addendum.md` (1.1).
Contract: API
Audit: GREEN -/
theorem posPart_budget_normed_le {ι : Type*} (I : Finset ι)
    (w C M q σ : ι → ℝ) {N Z : ℝ} (hN : 0 < N)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hσ : ∀ i ∈ I, |σ i| ≤ 1) :
    ∑ i ∈ I, w i * (σ i * (C i / N - q i))⁺
      ≤ (1 / N) * ∑ i ∈ I, w i * (σ i * (C i - M i))⁺
        + ∑ i ∈ I, w i * |M i / N - M i / Z|
        + ∑ i ∈ I, w i * |M i / Z - q i| := by
  have hpt :
      ∀ i ∈ I,
        w i * (σ i * (C i / N - q i))⁺
          ≤ w i * ((1 / N) * (σ i * (C i - M i))⁺)
            + w i * |M i / N - M i / Z|
            + w i * |M i / Z - q i| := by
    intro i hi
    have h := posPart_signed_normed_le (C := C i) (M := M i) (q := q i)
      (σ := σ i) (N := N) (Z := Z) hN (hσ i hi)
    have hw' : 0 ≤ w i := hw i hi
    have := mul_le_mul_of_nonneg_left h hw'
    linarith
  have hsum := sum_le_sum hpt
  have hred :
      ∑ i ∈ I,
          (w i * ((1 / N) * (σ i * (C i - M i))⁺)
            + w i * |M i / N - M i / Z|
            + w i * |M i / Z - q i|)
        = (1 / N) * ∑ i ∈ I, w i * (σ i * (C i - M i))⁺
          + ∑ i ∈ I, w i * |M i / N - M i / Z|
          + ∑ i ∈ I, w i * |M i / Z - q i| := by
    have hA : ∀ i, w i * ((1 / N) * (σ i * (C i - M i))⁺) =
        (1 / N) * (w i * (σ i * (C i - M i))⁺) := fun _ => mul_left_comm _ _ _
    simp_rw [hA]
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
  exact hsum.trans_eq hred

/-- Sign restriction `σ ∈ {±1}` is the paper variant of (1.1).

Source: `rounds/round103/07_grok_minimal_budget_small_addendum.md` §1.
Contract: API
Audit: GREEN -/
theorem posPart_budget_normed_le_pm {ι : Type*} (I : Finset ι)
    (w C M q σ : ι → ℝ) {N Z : ℝ} (hN : 0 < N)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hσ : ∀ i ∈ I, σ i = 1 ∨ σ i = -1) :
    ∑ i ∈ I, w i * (σ i * (C i / N - q i))⁺
      ≤ (1 / N) * ∑ i ∈ I, w i * (σ i * (C i - M i))⁺
        + ∑ i ∈ I, w i * |M i / N - M i / Z|
        + ∑ i ∈ I, w i * |M i / Z - q i| :=
  posPart_budget_normed_le I w C M q σ hN hw fun i hi => by
    rcases hσ i hi with h | h <;> simp [h]

/-- Relative calibration form (1.2). No PNT rate is inserted.

Source: `rounds/round103/07_grok_minimal_budget_small_addendum.md` (1.2);
`rounds/round103/04_paper_architecture_minimal_input_v2.md` (3.2).
Contract: API
Audit: GREEN -/
theorem posPart_budget_rel_le {ι : Type*} (I : Finset ι)
    (w C M q σ : ι → ℝ) {N Z δ : ℝ} (hN : 0 < N) (hZ : 0 < Z)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hσ : ∀ i ∈ I, |σ i| ≤ 1)
    (hM : ∀ i ∈ I, 0 ≤ M i) (hq : ∀ i ∈ I, 0 ≤ q i)
    (hrel : ∀ i ∈ I, |q i - M i / Z| ≤ δ * (M i / Z)) :
    ∑ i ∈ I, w i * (σ i * (C i / N - q i))⁺
      ≤ (1 / N) * ∑ i ∈ I, w i * (σ i * (C i - M i))⁺
        + (|Z / N - 1| + δ) / (1 - δ) * ∑ i ∈ I, w i * q i := by
  have hcore := posPart_budget_normed_le (Z := Z) I w C M q σ hN hw hσ
  have hden : 0 < 1 - δ := sub_pos.mpr hδ1
  have hmass :
      ∑ i ∈ I, w i * |M i / N - M i / Z| + ∑ i ∈ I, w i * |M i / Z - q i|
        ≤ (|Z / N - 1| + δ) / (1 - δ) * ∑ i ∈ I, w i * q i := by
    have hterm :
        ∀ i ∈ I,
          w i * |M i / N - M i / Z| + w i * |M i / Z - q i|
            ≤ (|Z / N - 1| + δ) / (1 - δ) * (w i * q i) := by
      intro i hi
      have hMi : 0 ≤ M i := hM i hi
      have hm : 0 ≤ M i / Z := div_nonneg hMi hZ.le
      have habs :
          |M i / N - M i / Z| = (M i / Z) * |Z / N - 1| := by
        have : M i / N - M i / Z = (M i / Z) * (Z / N - 1) := by
          field_simp [hN.ne', hZ.ne']
        rw [this, abs_mul, abs_of_nonneg hm]
      have hcal : |M i / Z - q i| = |q i - M i / Z| := abs_sub_comm _ _
      have hcal' : |q i - M i / Z| ≤ δ * (M i / Z) := hrel i hi
      have hlow : (1 - δ) * (M i / Z) ≤ q i := by
        have := (abs_le.mp hcal').1
        linarith
      have hquot : M i / Z ≤ q i / (1 - δ) := by
        rw [le_div_iff₀ hden]
        linarith
      have hw' : 0 ≤ w i := hw i hi
      have hq' : 0 ≤ q i := hq i hi
      have hbound :
          w i * |M i / N - M i / Z| + w i * |M i / Z - q i|
            ≤ w i * ((|Z / N - 1| + δ) * (M i / Z)) := by
        rw [habs, hcal]
        have hδterm :
            w i * |q i - M i / Z| ≤ w i * (δ * (M i / Z)) :=
          mul_le_mul_of_nonneg_left hcal' hw'
        linarith
      have hfac :
          w i * ((|Z / N - 1| + δ) * (M i / Z))
            ≤ (|Z / N - 1| + δ) / (1 - δ) * (w i * q i) := by
        have hnn : 0 ≤ |Z / N - 1| + δ := add_nonneg (abs_nonneg _) hδ0
        calc
          w i * ((|Z / N - 1| + δ) * (M i / Z))
              = (|Z / N - 1| + δ) * (w i * (M i / Z)) := by ring
          _ ≤ (|Z / N - 1| + δ) * (w i * (q i / (1 - δ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hquot hw') hnn
          _ = (|Z / N - 1| + δ) / (1 - δ) * (w i * q i) := by
            field_simp [hden.ne']
      exact hbound.trans hfac
    have hsum := sum_le_sum hterm
    have hsplit :
        ∑ i ∈ I, (w i * |M i / N - M i / Z| + w i * |M i / Z - q i|)
          = ∑ i ∈ I, w i * |M i / N - M i / Z|
            + ∑ i ∈ I, w i * |M i / Z - q i| :=
      sum_add_distrib
    have hrhs :
        ∑ i ∈ I, (|Z / N - 1| + δ) / (1 - δ) * (w i * q i)
          = (|Z / N - 1| + δ) / (1 - δ) * ∑ i ∈ I, w i * q i := by
      exact (mul_sum I (fun i => w i * q i) _).symm
    rw [← hsplit]
    exact hsum.trans_eq hrhs
  linarith [hcore, hmass]

end PrimeGapNormality.Prime
