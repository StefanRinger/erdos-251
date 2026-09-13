import PrimeGapNormality.Prime.CoreSequenceSubexponentialGrowth
import PrimeGapNormality.Prime.CoreLocalSeriesRecurrence

/-!
# Local polynomial algebra for subexponential sequences

The generic S/T route naturally gives growth below every fixed exponential,
rather than a polynomial bound.  This file records that this weaker property
is closed under the finite algebra used by a local polynomial tuple and is
still enough for every geometrically weighted local series and boundary.

No statement here assumes a prime sequence, a density estimate, or a new
convergence hypothesis.
-/

namespace PrimeGapNormality.Prime.CoreSequenceSubexponentialGrowth

open Finset Filter MvPolynomial
open CoreCyclic
open scoped BigOperators Classical Topology

noncomputable section

theorem hasSubexponentialGrowth_const (c : ℝ) :
    HasSubexponentialGrowth (fun _ : ℕ ↦ c) := by
  intro q hq
  refine ⟨|c|, abs_nonneg c, ?_⟩
  intro n
  have hpow : (1 : ℝ) ≤ q ^ n := one_le_pow₀ hq.le
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hpow (abs_nonneg c)

theorem HasSubexponentialGrowth.add {f g : ℕ → ℝ}
    (hf : HasSubexponentialGrowth f) (hg : HasSubexponentialGrowth g) :
    HasSubexponentialGrowth (fun n ↦ f n + g n) := by
  intro q hq
  obtain ⟨C, hC, hfC⟩ := hf q hq
  obtain ⟨D, hD, hgD⟩ := hg q hq
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro n
  calc
    |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ C * q ^ n + D * q ^ n := add_le_add (hfC n) (hgD n)
    _ = (C + D) * q ^ n := by ring

theorem HasSubexponentialGrowth.mul {f g : ℕ → ℝ}
    (hf : HasSubexponentialGrowth f) (hg : HasSubexponentialGrowth g) :
    HasSubexponentialGrowth (fun n ↦ f n * g n) := by
  intro q hq
  let r := Real.sqrt q
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = q := by
    dsimp only [r]
    exact Real.sq_sqrt hq0.le
  have hr1 : 1 < r := by nlinarith
  obtain ⟨C, hC, hfC⟩ := hf r hr1
  obtain ⟨D, hD, hgD⟩ := hg r hr1
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  intro n
  rw [abs_mul]
  have hright : 0 ≤ C * r ^ n :=
    mul_nonneg hC (pow_nonneg hr0 _)
  calc
    |f n| * |g n| ≤ (C * r ^ n) * (D * r ^ n) :=
      mul_le_mul (hfC n) (hgD n) (abs_nonneg _) hright
    _ = (C * D) * (r ^ 2) ^ n := by rw [pow_two, mul_pow]; ring
    _ = (C * D) * q ^ n := by rw [hrsq]

theorem HasSubexponentialGrowth.shift {f : ℕ → ℝ}
    (hf : HasSubexponentialGrowth f) (a : ℕ) :
    HasSubexponentialGrowth (fun n ↦ f (n + a)) := by
  intro q hq
  obtain ⟨C, hC, hbound⟩ := hf q hq
  refine ⟨C * q ^ a,
    mul_nonneg hC (pow_nonneg (zero_lt_one.trans hq).le _), ?_⟩
  intro n
  calc
    |f (n + a)| ≤ C * q ^ (n + a) := hbound (n + a)
    _ = (C * q ^ a) * q ^ n := by rw [pow_add]; ring

theorem HasSubexponentialGrowth.natPow {f : ℕ → ℝ}
    (hf : HasSubexponentialGrowth f) (d : ℕ) :
    HasSubexponentialGrowth (fun n ↦ f n ^ d) := by
  induction d with
  | zero => simpa using hasSubexponentialGrowth_const 1
  | succ d ih =>
      simpa only [pow_succ] using ih.mul hf

theorem hasSubexponentialGrowth_finset_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ → ℝ)
    (hf : ∀ i ∈ s, HasSubexponentialGrowth (f i)) :
    HasSubexponentialGrowth (fun n ↦ ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasSubexponentialGrowth_const 0
  | @insert i s hi ih =>
      have hfi : HasSubexponentialGrowth (f i) := hf i (mem_insert_self i s)
      have hfs : HasSubexponentialGrowth (fun n ↦ ∑ j ∈ s, f j n) :=
        ih fun j hj ↦ hf j (mem_insert_of_mem hj)
      simpa only [sum_insert hi] using hfi.add hfs

theorem hasSubexponentialGrowth_fin_choice
    {k : ℕ} (f : Fin k → ℕ → ℝ)
    (hf : ∀ s, HasSubexponentialGrowth (f s)) (s : ℕ → Fin k) :
    HasSubexponentialGrowth (fun n ↦ f (s n) n) := by
  classical
  intro q hq
  let C : Fin k → ℝ := fun i ↦ Classical.choose (hf i q hq)
  have hC (i : Fin k) : 0 ≤ C i :=
    (Classical.choose_spec (hf i q hq)).1
  have hbound (i : Fin k) (n : ℕ) : |f i n| ≤ C i * q ^ n :=
    (Classical.choose_spec (hf i q hq)).2 n
  refine ⟨∑ i, C i, sum_nonneg fun i _ ↦ hC i, ?_⟩
  intro n
  have hterm : C (s n) ≤ ∑ i, C i :=
    single_le_sum (fun i _ ↦ hC i) (mem_univ (s n))
  exact (hbound (s n) n).trans
    (mul_le_mul_of_nonneg_right hterm
      (pow_nonneg (zero_lt_one.trans hq).le _))

/-- Evaluation of a fixed rational multivariate polynomial on translated
windows preserves subexponential growth. -/
theorem hasSubexponentialGrowth_eval₂
    (g : ℕ → ℝ) (hg : HasSubexponentialGrowth g) (p : LocalPoly) :
    HasSubexponentialGrowth (fun n ↦
      eval₂ (algebraMap ℚ ℝ) (fun j ↦ g (n + j)) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simpa using hasSubexponentialGrowth_const ((algebraMap ℚ ℝ) c)
  | add p q hp hq =>
      simpa only [eval₂_add] using hp.add hq
  | mul_X p j hp =>
      have hj : HasSubexponentialGrowth (fun n ↦ g (n + j)) := hg.shift j
      simpa only [eval₂_mul, eval₂_X] using hp.mul hj

/-- A finite periodic tuple of local polynomials remains subexponential on
a subexponential input sequence. -/
theorem localValue_hasSubexponentialGrowth
    {k : ℕ} (hk : 0 < k) (r : Fin k) (g : ℕ → ℝ)
    (hg : HasSubexponentialGrowth g) (F : PeriodicLocal k) :
    HasSubexponentialGrowth (fun n ↦ localValue hk r g F n) := by
  let f : Fin k → ℕ → ℝ := fun s n ↦
    eval₂ (algebraMap ℚ ℝ) (fun j ↦ g (n + j)) (F s)
  have hf : ∀ s, HasSubexponentialGrowth (f s) := fun s ↦
    hasSubexponentialGrowth_eval₂ g hg (F s)
  simpa only [localValue, f] using
    hasSubexponentialGrowth_fin_choice f hf (phaseAt hk r)

/-- The shifted geometric form used in the actual local series. -/
theorem HasSubexponentialGrowth.summable_div_pow_succ
    {f : ℕ → ℝ} (hf : HasSubexponentialGrowth f)
    {rho : ℝ} (hrho : 1 < rho) :
    Summable (fun n : ℕ ↦ f n / rho ^ (n + 1)) := by
  have hs := hf.summable_div_pow hrho
  have hrho0 : rho ≠ 0 := (zero_lt_one.trans hrho).ne'
  refine (hs.mul_left rho⁻¹).congr fun n ↦ ?_
  rw [pow_succ]
  field_simp [hrho0]

/-- Subexponential growth makes every fixed shifted boundary vanish after
division by a geometric denominator. -/
theorem HasSubexponentialGrowth.tendsto_shift_div_pow
    {f : ℕ → ℝ} (hf : HasSubexponentialGrowth f)
    {rho : ℝ} (hrho : 1 < rho) (a : ℕ) :
    Tendsto (fun N : ℕ ↦ f (a + N) / rho ^ N) atTop (nhds 0) := by
  have hshift : HasSubexponentialGrowth (fun N ↦ f (N + a)) := hf.shift a
  have hs := hshift.summable_div_pow hrho
  simpa only [Nat.add_comm] using hs.tendsto_atTop_zero

/-- Absolute convergence of the actual local series under only
subexponential input growth. -/
theorem localSeries_summable_of_subexponential
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (hg : HasSubexponentialGrowth g)
    (F : PeriodicLocal k) (a : ℕ) :
    Summable (fun n : ℕ ↦
      localValue hk r g F (a + n) / (B : ℝ) ^ (n + 1)) := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast (by omega : 1 < B)
  have hlocal := (localValue_hasSubexponentialGrowth hk r g hg F).shift a
  simpa only [Nat.add_comm] using hlocal.summable_div_pow_succ hBreal

/-- Relative-label series use the same finite polynomial algebra, with the
absolute gap window shifted but the labels restarted. -/
theorem relativeLocalSeries_summable_of_subexponential
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (hg : HasSubexponentialGrowth g)
    (F : PeriodicLocal k) (n : ℕ) :
    Summable (fun i : ℕ ↦
      relativeLocalValue hk r g F n i / (B : ℝ) ^ (i + 1)) := by
  have hgn : HasSubexponentialGrowth (fun j ↦ g (n + j)) := by
    simpa only [Nat.add_comm] using hg.shift n
  have hs := localSeries_summable_of_subexponential hB hk r
    (fun j ↦ g (n + j)) hgn F 0
  simpa only [relativeLocalValue, localValue, Nat.zero_add, Nat.add_assoc] using hs

/-- Any fixed local-polynomial boundary, not only the canonical primitive,
vanishes after division by `B^N`. -/
theorem localValue_boundary_tendsto_zero_of_subexponential
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (hg : HasSubexponentialGrowth g)
    (H : PeriodicLocal k) (a : ℕ) :
    Tendsto (fun N : ℕ ↦
      localValue hk r g H (a + N) / (B : ℝ) ^ N) atTop (nhds 0) := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast (by omega : 1 < B)
  exact (localValue_hasSubexponentialGrowth hk r g hg H).tendsto_shift_div_pow
    hBreal a

/-- The primitive boundary used by the cyclic telescope tends to zero under
the subexponential hypothesis. -/
theorem primitive_boundary_tendsto_zero_of_subexponential
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (hg : HasSubexponentialGrowth g)
    (F : PeriodicLocal k) (a : ℕ) :
    Tendsto (fun N : ℕ ↦
      localValue hk r g (primitive hB hk F) (a + N) / (B : ℝ) ^ N)
      atTop (nhds 0) := by
  exact localValue_boundary_tendsto_zero_of_subexponential hB hk r g hg
    (primitive hB hk F) a

/-- Infinite cyclic normal form with subexponential, rather than polynomial,
growth as its sole analytic input. -/
theorem infiniteSeries_normalForm_of_subexponential
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (hg : HasSubexponentialGrowth g)
    (F : PeriodicLocal k) (a : ℕ) :
    (∑' n : ℕ, localValue hk r g F (a + n) / (B : ℝ) ^ (n + 1)) -
        (∑' n : ℕ, localValue hk r g (normalForm hB hk F) (a + n) /
          (B : ℝ) ^ (n + 1)) =
      localValue hk r g (primitive hB hk F) a := by
  have hsF := localSeries_summable_of_subexponential hB hk r g hg F a
  have hsR := localSeries_summable_of_subexponential hB hk r g hg
    (normalForm hB hk F) a
  have hsum : Tendsto
      (fun N : ℕ ↦ finiteSeries B hk r g F a N -
        finiteSeries B hk r g (normalForm hB hk F) a N)
      atTop
      (nhds ((∑' n : ℕ,
          localValue hk r g F (a + n) / (B : ℝ) ^ (n + 1)) -
        (∑' n : ℕ,
          localValue hk r g (normalForm hB hk F) (a + n) /
            (B : ℝ) ^ (n + 1)))) := by
    simpa only [finiteSeries] using
      hsF.hasSum.tendsto_sum_nat.sub hsR.hasSum.tendsto_sum_nat
  have hboundary : Tendsto
      (fun N : ℕ ↦ localValue hk r g (primitive hB hk F) a -
        localValue hk r g (primitive hB hk F) (a + N) / (B : ℝ) ^ N)
      atTop (nhds (localValue hk r g (primitive hB hk F) a)) := by
    simpa using tendsto_const_nhds.sub
      (primitive_boundary_tendsto_zero_of_subexponential hB hk r g hg F a)
  apply tendsto_nhds_unique hsum
  exact hboundary.congr' (Eventually.of_forall fun N ↦
    (finiteSeries_normalForm hB hk r g F a N).symm)

end
end PrimeGapNormality.Prime.CoreSequenceSubexponentialGrowth
