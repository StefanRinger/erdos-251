import PrimeGapNormality.Prime.CoreSubexponentialRecurrence
import PrimeGapNormality.Prime.CoreSequenceSTMeanTail

/-!
# Width-zero integer gap observables

This is the non-polynomial series layer needed by rounded real powers.  A
periodic family `F : Fin k → ℕ → ℤ` is evaluated on the actual gaps,
with relative labels restarted at each series base point.  A uniform linear
bound on positive integer arguments gives convergence from subexponential
gap growth and a first-gap-tail bound on every truncation remainder.

The exact first-`k` correction is integer-valued, so it disappears modulo
one and gives the literal `B^k` circle recurrence.  No polynomial or
distribution hypothesis occurs in this file.
-/

namespace PrimeGapNormality.Prime.CoreIntegerGapObservable

open Finset Filter CoreCyclic
open CoreSequenceSubexponentialGrowth
open scoped Topology BigOperators

noncomputable section

/-- Relative label, absolute gap index. -/
def observableValue {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (g : ℕ → ℕ) (n i : ℕ) : ℤ :=
  F (phaseAt hk r i) (g (n + i))

/-- Infinite series based at `n`, with labels restarted at `r`. -/
def observableSeries (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (g : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑' i : ℕ, (observableValue hk r F g n i : ℝ) / (B : ℝ) ^ (i + 1)

/-- Literal full series at the original origin. -/
def observableFullSeries (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (g : ℕ → ℕ) : ℝ :=
  observableSeries B hk r F g 0

/-- First `L` summands of the relative series. -/
def observableTrunc (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (g : ℕ → ℕ) (n L : ℕ) : ℝ :=
  ∑ i ∈ range L,
    (observableValue hk r F g n i : ℝ) / (B : ℝ) ^ (i + 1)

/-- Tail after the first `L` summands, retaining the continuing labels. -/
def observableTail (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (g : ℕ → ℕ) (n L : ℕ) : ℝ :=
  ∑' j : ℕ,
    (observableValue hk r F g n (L + j) : ℝ) / (B : ℝ) ^ (L + j + 1)

/-- Integer correction exposed by multiplication through one full period. -/
def observableFirstBlockInt (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) (g : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ i ∈ range k,
    (B : ℤ) ^ (k - (i + 1)) * observableValue hk r F g n i

/-- A linearly bounded integer observable preserves subexponential growth
when evaluated on positive subexponential gaps. -/
theorem observableValue_hasSubexponentialGrowth
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : Fin k → ℕ → ℤ)
    {g : ℕ → ℕ} (hgpos : ∀ n, 1 ≤ g n)
    (hg : HasSubexponentialGrowth (fun n ↦ (g n : ℝ)))
    {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    (n : ℕ) :
    HasSubexponentialGrowth
      (fun i ↦ (observableValue hk r F g n i : ℝ)) := by
  have hshift : HasSubexponentialGrowth (fun i ↦ (g (n + i) : ℝ)) := by
    simpa only [Nat.add_comm] using hg.shift n
  intro q hq
  obtain ⟨D, hD, hbound⟩ := hshift q hq
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  intro i
  calc
    |(observableValue hk r F g n i : ℝ)| ≤
        C * (g (n + i) : ℝ) := hF _ _ (hgpos _)
    _ ≤ C * (D * q ^ i) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [abs_of_nonneg (show (0 : ℝ) ≤ (g (n + i) : ℝ) from
          Nat.cast_nonneg _)] using hbound i) hC
    _ = (C * D) * q ^ i := by ring

theorem observableSeries_summable
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {g : ℕ → ℕ} (hgpos : ∀ n, 1 ≤ g n)
    (hg : HasSubexponentialGrowth (fun n ↦ (g n : ℝ)))
    {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    (n : ℕ) :
    Summable (fun i : ℕ ↦
      (observableValue hk r F g n i : ℝ) / (B : ℝ) ^ (i + 1)) := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  exact (observableValue_hasSubexponentialGrowth hk r F hgpos hg hC hF n)
    |>.summable_div_pow_succ hBreal

/-- Exact finite/infinite split at the original truncation rank. -/
theorem observableSeries_eq_trunc_add_tail
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {g : ℕ → ℕ} (hgpos : ∀ n, 1 ≤ g n)
    (hg : HasSubexponentialGrowth (fun n ↦ (g n : ℝ)))
    {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    (n L : ℕ) :
    observableSeries B hk r F g n =
      observableTrunc B hk r F g n L + observableTail B hk r F g n L := by
  let term : ℕ → ℝ := fun i ↦
    (observableValue hk r F g n i : ℝ) / (B : ℝ) ^ (i + 1)
  have hs : Summable term := observableSeries_summable hB hk r F hgpos hg hC hF n
  have hsplit := hs.sum_add_tsum_nat_add L
  unfold observableSeries observableTrunc observableTail
  simpa only [term, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsplit.symm

private theorem abs_tsum_le_tsum_abs {f : ℕ → ℝ}
    (h : Summable fun i ↦ |f i|) : |∑' i, f i| ≤ ∑' i, |f i| := by
  simpa only [Real.norm_eq_abs] using
    (norm_tsum_le_tsum_norm (f := f)
      (by simpa only [Real.norm_eq_abs] using h))

/-- The unbounded rounded-observable tail is controlled by the same first
gap tail used in the paper, with no higher moment. -/
theorem abs_observableTail_le_firstGapTail
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {a : ℕ → ℕ} (ha : StrictMono a)
    (hg : HasSubexponentialGrowth (fun n ↦ (seqGap a n : ℝ)))
    {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    {rho : ℝ} (hrho : 1 < rho) (hrhoB : rho ≤ (B : ℝ))
    (n L : ℕ) :
    |observableTail B hk r F (seqGap a) n L| ≤
      C * rho⁻¹ ^ L * seqGapTail rho a (n + L) := by
  have hgapPos : ∀ m, 1 ≤ seqGap a m := by
    intro m
    unfold seqGap
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.sub_ne_zero_of_lt (ha (Nat.lt_succ_self m)))
  have hsum := observableSeries_summable hB hk r F hgapPos hg hC hF n
  have htailSm : Summable (fun j : ℕ ↦
      (observableValue hk r F (seqGap a) n (L + j) : ℝ) /
        (B : ℝ) ^ (L + j + 1)) := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (summable_nat_add_iff (f := fun i : ℕ ↦
        (observableValue hk r F (seqGap a) n i : ℝ) /
          (B : ℝ) ^ (i + 1)) L).2 hsum
  have hright : Summable (fun j : ℕ ↦
      C * rho⁻¹ ^ L *
        ((seqGap a (n + L + j) : ℝ) / rho ^ (j + 1))) := by
    have hbase := (hg.shift (n + L)).summable_div_pow_succ hrho
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hbase.mul_left (C * rho⁻¹ ^ L)
  have hterm : ∀ j : ℕ,
      |(observableValue hk r F (seqGap a) n (L + j) : ℝ) /
          (B : ℝ) ^ (L + j + 1)| ≤
        C * rho⁻¹ ^ L *
          ((seqGap a (n + L + j) : ℝ) / rho ^ (j + 1)) := by
    intro j
    let g : ℝ := (seqGap a (n + L + j) : ℝ)
    have hg0 : 0 ≤ g := Nat.cast_nonneg _
    have hobs := hF (phaseAt hk r (L + j)) (seqGap a (n + L + j))
      (hgapPos _)
    have hBpos : (0 : ℝ) < B := by positivity
    have hrhopos : 0 < rho := zero_lt_one.trans hrho
    have hpow : rho ^ (L + j + 1) ≤ (B : ℝ) ^ (L + j + 1) :=
      pow_le_pow_left₀ hrhopos.le hrhoB _
    have hdenB : 0 < (B : ℝ) ^ (L + j + 1) := pow_pos hBpos _
    have hdenR : 0 < rho ^ (L + j + 1) := pow_pos hrhopos _
    have hone :
        |(observableValue hk r F (seqGap a) n (L + j) : ℝ) /
            (B : ℝ) ^ (L + j + 1)| ≤
          C * g / (B : ℝ) ^ (L + j + 1) := by
      rw [abs_div, abs_of_pos hdenB]
      exact div_le_div_of_nonneg_right
        (by simpa only [g, observableValue, Nat.add_assoc] using hobs)
        hdenB.le
    have htwo : C * g / (B : ℝ) ^ (L + j + 1) ≤
        C * g / rho ^ (L + j + 1) :=
      div_le_div_of_nonneg_left (mul_nonneg hC hg0) hdenR hpow
    have hfactor : C * g / rho ^ (L + j + 1) =
        C * rho⁻¹ ^ L * (g / rho ^ (j + 1)) := by
      have hrho0 : rho ≠ 0 := hrhopos.ne'
      rw [show L + j + 1 = L + (j + 1) by omega, pow_add, inv_pow]
      field_simp [hrho0, pow_ne_zero L hrho0, pow_ne_zero (j + 1) hrho0] <;> ring
    exact hone.trans (htwo.trans_eq hfactor)
  unfold observableTail
  have habs := abs_tsum_le_tsum_abs htailSm.abs
  have hle := htailSm.abs.tsum_le_tsum hterm hright
  refine habs.trans (hle.trans_eq ?_)
  unfold seqGapTail
  rw [tsum_mul_left]

/-- Relative values advance by one full period exactly. -/
theorem observableValue_add_period
    {k : ℕ} (hk : 0 < k) (r : Fin k) (F : Fin k → ℕ → ℤ)
    (g : ℕ → ℕ) (n i : ℕ) :
    observableValue hk r F g n (i + k) =
      observableValue hk r F g (n + k) i := by
  unfold observableValue
  rw [show i + k = k + i by omega, phaseAt_add_period]
  simp only [Nat.add_assoc]

/-- Exact real recurrence with an explicitly integer first-block correction. -/
theorem observableSeries_add_period
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {g : ℕ → ℕ} (hgpos : ∀ n, 1 ≤ g n)
    (hg : HasSubexponentialGrowth (fun n ↦ (g n : ℝ)))
    {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    (n : ℕ) :
    observableSeries B hk r F g (n + k) =
      (B : ℝ) ^ k * observableSeries B hk r F g n -
        (observableFirstBlockInt B hk r F g n : ℝ) := by
  let term : ℕ → ℝ := fun i ↦
    (observableValue hk r F g n i : ℝ) / (B : ℝ) ^ (i + 1)
  have hs : Summable term := observableSeries_summable hB hk r F hgpos hg hC hF n
  have hsplit := hs.sum_add_tsum_nat_add k
  have htail : (∑' i : ℕ, term (i + k)) =
      observableSeries B hk r F g (n + k) / (B : ℝ) ^ k := by
    have hB0 : (B : ℝ) ≠ 0 := by positivity
    unfold observableSeries
    rw [← tsum_div_const]
    apply tsum_congr
    intro i
    dsimp only [term]
    rw [observableValue_add_period]
    rw [show i + k + 1 = (i + 1) + k by omega, pow_add]
    field_simp [hB0]
  have hfirst : (observableFirstBlockInt B hk r F g n : ℝ) =
      (B : ℝ) ^ k * ∑ i ∈ range k,
        (observableValue hk r F g n i : ℝ) / (B : ℝ) ^ (i + 1) := by
    unfold observableFirstBlockInt
    rw [Int.cast_sum, mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    have hik : i + 1 ≤ k := Nat.succ_le_iff.mpr (mem_range.mp hi)
    have hpow : (B : ℝ) ^ k =
        (B : ℝ) ^ (i + 1) * (B : ℝ) ^ (k - (i + 1)) := by
      rw [← pow_add, Nat.add_sub_of_le hik]
    rw [hpow]
    field_simp [show (B : ℝ) ≠ 0 by positivity]
  change
    (∑ i ∈ range k, term i) + (∑' i : ℕ, term (i + k)) =
      observableSeries B hk r F g n at hsplit
  rw [htail] at hsplit
  rw [hfirst]
  have hBk0 : (B : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by positivity)
  field_simp [hBk0] at hsplit
  linarith

private theorem circle_intCast_eq_zero (z : ℤ) :
    ((z : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  have h := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := z) (x := (1 : ℝ))
  simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using h

/-- Exact period-`k` integer recurrence modulo one. -/
theorem observableSeriesCircle_add_period
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (F : Fin k → ℕ → ℤ) {g : ℕ → ℕ} (hgpos : ∀ n, 1 ≤ g n)
    (hg : HasSubexponentialGrowth (fun n ↦ (g n : ℝ)))
    {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s q, 1 ≤ q → |(F s q : ℝ)| ≤ C * (q : ℝ))
    (n : ℕ) :
    (observableSeries B hk r F g (n + k) : AddCircle (1 : ℝ)) =
      B ^ k • (observableSeries B hk r F g n : AddCircle (1 : ℝ)) := by
  rw [observableSeries_add_period hB hk r F hgpos hg hC hF,
    AddCircle.coe_sub, circle_intCast_eq_zero, sub_zero]
  simpa only [nsmul_eq_mul, Nat.cast_pow] using
    (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := B ^ k)
      (x := observableSeries B hk r F g n))

end
end PrimeGapNormality.Prime.CoreIntegerGapObservable
