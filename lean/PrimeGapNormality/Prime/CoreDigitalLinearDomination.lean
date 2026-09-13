import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Direct linear insertion integrals

The P1a simplification of the frozen paper: a nonnegative one-periodic test
along a linear action with absolute slope at least one is dominated by
`(W+1)` times its circle mean. Averaging then needs only the first moment
of the physical insertion span, not a joint frame/outer-phase limit.
The discrete Selberg insertion majorant and the auxiliary gap mean remain
separate suppliers; this module proves the continuous integral step.
-/

open MeasureTheory Set

namespace PrimeGapNormality.Prime

/-- An interval is covered by at most its length plus one periods. -/
theorem coreDigital_periodic_integral_le (f : ℝ → ℝ) (hf : Continuous f)
    (hp : Function.Periodic f 1) (hpos : ∀ x, 0 ≤ f x)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x) ≤ (b - a + 1) * ∫ x in (0 : ℝ)..1, f x := by
  let n : ℤ := ⌈b - a⌉
  have hn : b ≤ a + (n : ℝ) := by
    have := Int.le_ceil (b - a)
    dsimp [n]
    linarith
  have hn' : (n : ℝ) ≤ b - a + 1 := (Int.ceil_lt_add_one (b - a)).le
  have hmean : 0 ≤ ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => hpos x)
  have hfull : (∫ x in a..a + (n : ℝ), f x) =
      (n : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
    have heq := hp.intervalIntegral_add_zsmul_eq n a
      (fun s t => hf.intervalIntegrable s t)
    have hbase := hp.intervalIntegral_add_eq a 0
    simpa only [zsmul_eq_mul, mul_one, zero_add, hbase] using heq
  calc
    (∫ x in a..b, f x) ≤ ∫ x in a..a + (n : ℝ), f x :=
      intervalIntegral.integral_mono_interval le_rfl hab hn
        (Filter.Eventually.of_forall hpos) (hf.intervalIntegrable _ _)
    _ = (n : ℝ) * ∫ x in (0 : ℝ)..1, f x := hfull
    _ ≤ (b - a + 1) * ∫ x in (0 : ℝ)..1, f x :=
      mul_le_mul_of_nonneg_right hn' hmean

/-- Orientation-free form, needed for negative linear coefficients. -/
theorem coreDigital_abs_periodic_integral_le (f : ℝ → ℝ) (hf : Continuous f)
    (hp : Function.Periodic f 1) (hpos : ∀ x, 0 ≤ f x) (a b : ℝ) :
    |∫ x in a..b, f x| ≤ (|b - a| + 1) * ∫ x in (0 : ℝ)..1, f x := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hab (fun x _ => hpos x)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact coreDigital_periodic_integral_le f hf hp hpos hab
  · rw [intervalIntegral.integral_symm, abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg hba (fun x _ => hpos x)),
      abs_sub_comm b a, abs_of_nonneg (sub_nonneg.mpr hba)]
    exact coreDigital_periodic_integral_le f hf hp hpos hba

/-- The linear positive-test bound, uniform in the outer phase and slope. -/
theorem coreDigital_linear_insertion_integral_le (f : ℝ → ℝ) (hf : Continuous f)
    (hp : Function.Periodic f 1) (hpos : ∀ x, 0 ≤ f x)
    (O s W : ℝ) (hs : 1 ≤ |s|) (hW : 0 ≤ W) :
    (∫ z in (0 : ℝ)..W, f (O + s * z)) ≤
      (W + 1) * ∫ x in (0 : ℝ)..1, f x := by
  have hspos : 0 < |s| := lt_of_lt_of_le zero_lt_one hs
  have hsne : s ≠ 0 := abs_pos.mp hspos
  have hmean : 0 ≤ ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => hpos x)
  have hid : (∫ z in (0 : ℝ)..W, f (O + s * z)) =
      s⁻¹ * ∫ x in O..s * W + O, f x := by
    simpa only [zero_mul, mul_zero, zero_add, smul_eq_mul, add_comm O] using
      (intervalIntegral.integral_comp_mul_add f hsne O (a := 0) (b := W))
  have hbound := coreDigital_abs_periodic_integral_le f hf hp hpos O (s * W + O)
  have hspan : |s * W + O - O| = |s| * W := by
    rw [add_sub_cancel_right, abs_mul, abs_of_nonneg hW]
  rw [hspan] at hbound
  calc
    (∫ z in (0 : ℝ)..W, f (O + s * z)) ≤
        |∫ z in (0 : ℝ)..W, f (O + s * z)| := le_abs_self _
    _ = |∫ x in O..s * W + O, f x| / |s| := by
      rw [hid, abs_mul, abs_inv, div_eq_mul_inv, mul_comm]
    _ ≤ ((|s| * W + 1) * ∫ x in (0 : ℝ)..1, f x) / |s| :=
      div_le_div_of_nonneg_right hbound hspos.le
    _ ≤ (W + 1) * ∫ x in (0 : ℝ)..1, f x := by
      apply (div_le_iff₀ hspos).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hs) hmean]

/-- Paper parameters: a nonzero integer slope coefficient and t≥1. -/
theorem coreDigital_integer_linear_insertion_integral_le
    (f : ℝ → ℝ) (hf : Continuous f) (hp : Function.Periodic f 1)
    (hpos : ∀ x, 0 ≤ f x) (O t W : ℝ) (b : ℤ)
    (ht : 1 ≤ t) (hb : b ≠ 0) (hW : 0 ≤ W) :
    (∫ z in (0 : ℝ)..W, f (O + t * (b : ℝ) * z)) ≤
      (W + 1) * ∫ x in (0 : ℝ)..1, f x := by
  apply coreDigital_linear_insertion_integral_le f hf hp hpos O (t * b) W _ hW
  rw [abs_mul, abs_of_nonneg (le_trans zero_le_one ht)]
  have hb' : (1 : ℝ) ≤ |(b : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hb)
  nlinarith

/-- Circle-test version: the right-hand side is the actual volume integral
on `AddCircle 1`, matching the invariant-limit consumer. -/
theorem coreDigital_circle_linear_insertion_integral_le
    (f : AddCircle (1 : ℝ) → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x)
    (O s W : ℝ) (hs : 1 ≤ |s|) (hW : 0 ≤ W) :
    (∫ z in (0 : ℝ)..W, f ((O + s * z : ℝ) : AddCircle (1 : ℝ))) ≤
      (W + 1) * ∫ x : AddCircle (1 : ℝ), f x := by
  have hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (1 : ℝ))) 1 := by
    intro x
    dsimp only
    rw [AddCircle.coe_add_period]
  have h := coreDigital_linear_insertion_integral_le
    (fun x : ℝ => f (x : AddCircle (1 : ℝ)))
    (hf.comp (AddCircle.continuous_mk' 1)) hp (fun x => hpos _) O s W hs hW
  have hmean : (∫ x in (0 : ℝ)..1, f (x : AddCircle (1 : ℝ))) =
      ∫ x : AddCircle (1 : ℝ), f x := by
    simpa only [zero_add] using AddCircle.intervalIntegral_preimage (1 : ℝ) 0 f
  rw [hmean] at h
  exact h

/-- Averaging the insertion bound costs only mass and the first physical
span moment. This applies to the unnormalized auxiliary law with mass ≤1. -/
theorem coreDigital_finite_linear_insertion_average_le
    {ι : Type*} (I : Finset ι) (w O s W : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hmass : ∑ i ∈ I, w i ≤ 1)
    (hW : ∀ i ∈ I, 0 ≤ W i) (hs : ∀ i ∈ I, 1 ≤ |s i|)
    {M : ℝ} (hmean : ∑ i ∈ I, w i * W i ≤ M)
    (f : AddCircle (1 : ℝ) → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) :
    (∑ i ∈ I, w i * ∫ z in (0 : ℝ)..W i,
      f ((O i + s i * z : ℝ) : AddCircle (1 : ℝ))) ≤
        (M + 1) * ∫ x : AddCircle (1 : ℝ), f x := by
  have htest : 0 ≤ ∫ x : AddCircle (1 : ℝ), f x := integral_nonneg hpos
  calc
    _ ≤ ∑ i ∈ I, w i * ((W i + 1) * ∫ x : AddCircle (1 : ℝ), f x) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (coreDigital_circle_linear_insertion_integral_le f hf hpos
          (O i) (s i) (W i) (hs i hi) (hW i hi)) (hw i hi)
    _ = ((∑ i ∈ I, w i * W i) + ∑ i ∈ I, w i) *
        ∫ x : AddCircle (1 : ℝ), f x := by
      simp only [← mul_assoc, mul_add, mul_one, Finset.sum_add_distrib,
        Finset.sum_mul, add_mul]
    _ ≤ (M + 1) * ∫ x : AddCircle (1 : ℝ), f x :=
      mul_le_mul_of_nonneg_right (add_le_add hmean hmass) htest

end PrimeGapNormality.Prime
