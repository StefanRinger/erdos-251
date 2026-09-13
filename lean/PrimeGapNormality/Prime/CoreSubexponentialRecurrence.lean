import PrimeGapNormality.Prime.CoreSubexponentialAlgebra
import PrimeGapNormality.Prime.CoreCyclicOrbitIdentification

/-!
# Cyclic recurrence from subexponential growth

The finite telescope is unchanged.  Subexponential growth is used only to
justify the infinite relative series and the vanishing tail before passing
the exact first-block correction to the circle.
-/

namespace PrimeGapNormality.Prime.CoreSequenceSubexponentialGrowth

open Finset MvPolynomial
open CoreCyclic
open scoped BigOperators

noncomputable section

theorem coreLocalSeries_add_period_of_subexponential
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (hg : HasSubexponentialGrowth g)
    (F : PeriodicLocal k) (n : ℕ) :
    coreLocalSeries B hk r g F (n + k) =
      (B : ℝ) ^ k * coreLocalSeries B hk r g F n -
        coreLocalFirstBlock B hk r g F n := by
  let term : ℕ → ℝ := fun i ↦
    relativeLocalValue hk r g F n i / (B : ℝ) ^ (i + 1)
  have hs : Summable term :=
    relativeLocalSeries_summable_of_subexponential hB hk r g hg F n
  have hsplit := hs.sum_add_tsum_nat_add k
  have htail : (∑' i : ℕ, term (i + k)) =
      coreLocalSeries B hk r g F (n + k) / (B : ℝ) ^ k := by
    have hs' := relativeLocalSeries_summable_of_subexponential
      hB hk r g hg F (n + k)
    have hB0 : (B : ℝ) ≠ 0 := by positivity
    unfold coreLocalSeries
    rw [← tsum_div_const]
    apply tsum_congr
    intro i
    dsimp only [term]
    rw [relativeLocalValue_add_period]
    have hexp : i + k + 1 = (i + 1) + k := by omega
    rw [hexp, pow_add]
    field_simp [hB0]
  have hfirst : coreLocalFirstBlock B hk r g F n =
      (B : ℝ) ^ k *
        ∑ i ∈ range k,
          relativeLocalValue hk r g F n i / (B : ℝ) ^ (i + 1) := by
    have hB0 : (B : ℝ) ≠ 0 := by positivity
    rw [mul_sum]
    unfold coreLocalFirstBlock
    apply sum_congr rfl
    intro i hi
    have hik : i + 1 ≤ k := Nat.succ_le_iff.mpr (mem_range.mp hi)
    have hdecomp : i + 1 + (k - (i + 1)) = k := Nat.add_sub_of_le hik
    have hpow : (B : ℝ) ^ k =
        (B : ℝ) ^ (i + 1) * (B : ℝ) ^ (k - (i + 1)) := by
      rw [← pow_add, hdecomp]
    rw [hpow]
    field_simp [hB0]
  change
    (∑ i ∈ range k,
        relativeLocalValue hk r g F n i / (B : ℝ) ^ (i + 1)) +
        (∑' i : ℕ,
          relativeLocalValue hk r g F n (i + k) /
            (B : ℝ) ^ (i + k + 1)) =
      coreLocalSeries B hk r g F n at hsplit
  rw [htail] at hsplit
  rw [hfirst]
  have hBk0 : (B : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by positivity)
  field_simp [hBk0] at hsplit
  linarith

private theorem coreCircle_intCast_eq_zero_subexp (z : ℤ) :
    ((z : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  have h := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := z) (x := (1 : ℝ))
  simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using h

theorem coreLocalSeriesCircle_add_period_of_intTuple_subexponential
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℤ)
    (hg : HasSubexponentialGrowth (fun n ↦ (g n : ℝ)))
    (F : Fin k → MvPolynomial ℕ ℤ) (n : ℕ) :
    coreLocalSeriesCircle B hk r (fun j ↦ (g j : ℝ)) (mapIntTuple F)
        (n + k) =
      B ^ k • coreLocalSeriesCircle B hk r
        (fun j ↦ (g j : ℝ)) (mapIntTuple F) n := by
  have hrec := coreLocalSeries_add_period_of_subexponential hB hk r
    (fun j ↦ (g j : ℝ)) hg (mapIntTuple F) n
  have hint := coreLocalFirstBlock_mapIntTuple (B := B) hk r g F n
  unfold coreLocalSeriesCircle
  rw [hrec, hint, AddCircle.coe_sub, coreCircle_intCast_eq_zero_subexp,
    sub_zero]
  simpa only [nsmul_eq_mul, Nat.cast_pow] using
    (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := B ^ k)
      (x := coreLocalSeries B hk r (fun j ↦ (g j : ℝ))
        (mapIntTuple F) n))

theorem coreLocalSeriesCircle_progression_of_intTuple_subexponential
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℤ)
    (hg : HasSubexponentialGrowth (fun n ↦ (g n : ℝ)))
    (F : Fin k → MvPolynomial ℕ ℤ) (n₀ t : ℕ) :
    coreLocalSeriesCircle B hk r (fun n ↦ (g n : ℝ)) (mapIntTuple F)
        (n₀ + k * t) =
      (B ^ k) ^ t • coreLocalSeriesCircle B hk r
        (fun n ↦ (g n : ℝ)) (mapIntTuple F) n₀ := by
  apply circleOrbit_of_add_period
  intro n
  exact coreLocalSeriesCircle_add_period_of_intTuple_subexponential
    hB hk r g hg F n

theorem coreLocalSeriesCircle_progression_zero_eq_fullSeries_subexponential
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℤ)
    (hg : HasSubexponentialGrowth (fun n ↦ (g n : ℝ)))
    (F : Fin k → MvPolynomial ℕ ℤ) (t : ℕ) :
    coreLocalSeriesCircle B hk r (fun n ↦ (g n : ℝ)) (mapIntTuple F)
        (k * t) =
      (B ^ k) ^ t •
        (coreCyclicFullSeries B hk r (fun n ↦ (g n : ℝ))
          (mapIntTuple F) : AddCircle (1 : ℝ)) := by
  rw [← coreLocalSeries_zero_eq_fullSeries]
  simpa only [Nat.zero_add, coreLocalSeriesCircle] using
    coreLocalSeriesCircle_progression_of_intTuple_subexponential
      hB hk r g hg F 0 t

end
end PrimeGapNormality.Prime.CoreSequenceSubexponentialGrowth
