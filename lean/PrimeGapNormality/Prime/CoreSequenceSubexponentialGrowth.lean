import PrimeGapNormality.Prime.CoreSequenceResiduePassage
import PrimeGapNormality.Prime.CoreCyclicSeriesConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Subexponential growth from growing physical windows

Growing counts in `(X,2X]`, evaluated at `X=a(n)`, force an eventual
finite-step doubling inequality `a(n+k)≤2a(n)` for every fixed `k`.
Choosing `k` so that `2≤q^k` gives a `q^n` majorant by strong induction.
This is the generic S/T growth input: it is weaker than polynomial growth
and uses no prime or rough-number structure.
-/

namespace PrimeGapNormality.Prime.CoreSequenceSubexponentialGrowth

open Finset Filter CoreCyclic
open scoped Topology

noncomputable section

/-- Growth below every fixed exponential rate. -/
def HasSubexponentialGrowth (f : ℕ → ℝ) : Prop :=
  ∀ q : ℝ, 1 < q → ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |f n| ≤ C * q ^ n

/-- A window containing at least `k` later sequence points forces the
`k`-step value below twice the root value. -/
theorem step_le_two_of_window_card
    {a : ℕ → ℕ} (ha : StrictMono a) {n k : ℕ}
    (hcard : k ≤ (seqWindow a (a n)).card) :
    a (n + k) ≤ 2 * a n := by
  have hcount := le_seqCount_two ha n
  have hcardEq := seqWindow_card ha n
  rw [hcardEq] at hcard
  have hlt : n + k < seqCount a (2 * a n) := by omega
  exact (seqCount_lt_iff ha).mp hlt

/-- For every fixed step, growing physical-window counts give the eventual
finite-step doubling recurrence. -/
theorem eventually_step_le_two
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, a (n + k) ≤ 2 * a n := by
  have hcardReal : Tendsto
      (fun n : ℕ ↦ ((seqWindow a (a n)).card : ℝ)) atTop atTop :=
    hcount.comp ha.tendsto_atTop
  filter_upwards [hcardReal.eventually (eventually_ge_atTop (k : ℝ))] with n hn
  apply step_le_two_of_window_card ha
  exact_mod_cast hn

private theorem exists_geometric_majorant
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, (a n : ℝ) ≤ C * q ^ n := by
  obtain ⟨k, hkpow⟩ := pow_unbounded_of_one_lt (2 : ℝ) hq
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := by omega
    subst k
    norm_num at hkpow
  have htwo : (2 : ℝ) ≤ q ^ k := hkpow.le
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp (eventually_step_le_two ha hcount k)
  let C : ℝ := a (n0 + k)
  refine ⟨C, Nat.cast_nonneg _, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hearly : n < n0 + k
      · have han : (a n : ℝ) ≤ C := by
          dsimp only [C]
          exact_mod_cast ha.monotone hearly.le
        have hqpow : (1 : ℝ) ≤ q ^ n := one_le_pow₀ hq.le
        exact han.trans (by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hqpow (Nat.cast_nonneg (a (n0 + k))))
      · have hnbase : n0 ≤ n - k := by omega
        have hnk : n - k < n := Nat.sub_lt (by omega) hkpos
        have hadd : n - k + k = n := Nat.sub_add_cancel (by omega)
        have hrecNat : a n ≤ 2 * a (n - k) := by
          simpa only [hadd] using hn0 (n - k) hnbase
        have hrec : (a n : ℝ) ≤ 2 * (a (n - k) : ℝ) := by
          exact_mod_cast hrecNat
        have hprev := ih (n - k) hnk
        have hnonneg : 0 ≤ C * q ^ (n - k) :=
          mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_lt_one.trans hq).le _)
        calc
          (a n : ℝ) ≤ 2 * (a (n - k) : ℝ) := hrec
          _ ≤ 2 * (C * q ^ (n - k)) :=
            mul_le_mul_of_nonneg_left hprev (by norm_num)
          _ ≤ q ^ k * (C * q ^ (n - k)) :=
            mul_le_mul_of_nonneg_right htwo hnonneg
          _ = C * (q ^ (n - k) * q ^ k) := by ring
          _ = C * q ^ ((n - k) + k) := by rw [pow_add]
          _ = C * q ^ n := by rw [hadd]

/-- Actual sequence positions are subexponential solely from strict
monotonicity and physical-window count growth. -/
theorem sequence_hasSubexponentialGrowth
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a) :
    HasSubexponentialGrowth (fun n ↦ (a n : ℝ)) := by
  intro q hq
  obtain ⟨C, hC, hbound⟩ := exists_geometric_majorant ha hcount q hq
  refine ⟨C, hC, ?_⟩
  intro n
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact hbound n

/-- Consecutive gaps inherit the same every-base geometric property. -/
theorem sequenceGap_hasSubexponentialGrowth
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a) :
    HasSubexponentialGrowth (fun n ↦ (seqGap a n : ℝ)) := by
  intro q hq
  obtain ⟨C, hC, hbound⟩ := exists_geometric_majorant ha hcount q hq
  refine ⟨C * q, mul_nonneg hC (zero_lt_one.trans hq).le, ?_⟩
  intro n
  have hgap : seqGap a n ≤ a (n + 1) := Nat.sub_le _ _
  have hgapReal : (seqGap a n : ℝ) ≤ (a (n + 1) : ℝ) := Nat.cast_le.mpr hgap
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    (seqGap a n : ℝ) ≤ (a (n + 1) : ℝ) := hgapReal
    _ ≤ C * q ^ (n + 1) := hbound (n + 1)
    _ = (C * q) * q ^ n := by rw [pow_succ]; ring

/-- Every subexponentially growing real sequence is summable against every
geometric denominator `rho^n`, using the intermediate rate `sqrt rho`. -/
theorem HasSubexponentialGrowth.summable_div_pow
    {f : ℕ → ℝ} (hf : HasSubexponentialGrowth f)
    {rho : ℝ} (hrho : 1 < rho) :
    Summable (fun n : ℕ ↦ f n / rho ^ n) := by
  let q := Real.sqrt rho
  have hrho0 : 0 < rho := zero_lt_one.trans hrho
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqsq : q ^ 2 = rho := by
    dsimp only [q]
    exact Real.sq_sqrt hrho0.le
  have hq1 : 1 < q := by
    nlinarith
  have hqrho : q < rho := by
    dsimp only [q]
    exact Real.sqrt_lt_self_iff.mpr hrho
  obtain ⟨C, hC, hbound⟩ := hf q hq1
  let r : ℝ := q / rho
  have hr0 : 0 ≤ r := div_nonneg hq0 hrho0.le
  have hr1 : r < 1 := (div_lt_one hrho0).mpr hqrho
  have hgeom : Summable (fun n : ℕ ↦ C * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  apply Summable.of_norm_bounded hgeom
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hrho0 n)]
  calc
    |f n| / rho ^ n ≤ (C * q ^ n) / rho ^ n :=
      div_le_div_of_nonneg_right (hbound n) (pow_nonneg hrho0.le _)
    _ = C * r ^ n := by
      dsimp only [r]
      rw [div_pow]
      ring

theorem sequence_div_pow_summable
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {rho : ℝ} (hrho : 1 < rho) :
    Summable (fun n : ℕ ↦ (a n : ℝ) / rho ^ n) :=
  (sequence_hasSubexponentialGrowth ha hcount).summable_div_pow hrho

theorem sequenceGap_div_pow_summable
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {rho : ℝ} (hrho : 1 < rho) :
    Summable (fun n : ℕ ↦ (seqGap a n : ℝ) / rho ^ n) :=
  (sequenceGap_hasSubexponentialGrowth ha hcount).summable_div_pow hrho

end
end PrimeGapNormality.Prime.CoreSequenceSubexponentialGrowth
