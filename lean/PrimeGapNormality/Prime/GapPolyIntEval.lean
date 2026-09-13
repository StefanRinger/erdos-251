import PrimeGapNormality.Prime.Components
import PrimeGapNormality.Prime.EndAPI
import PrimeGapNormality.Prime.GapPolySummable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Integer evaluation of gap polynomials (`TruncatedWeylPack` hint)

`TruncatedWeylPack` needs
`∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z`
for the orbit identity `e(τ(Φ+k)) = e(τ Φ)`. This holds for
integer-coefficient families: either `∀ n k, ∃ z, coeff (P n) k = z`,
or `P n = mapIntPoly (Q n)` with `Q n : ℤ[X]`.

A `mapRatPoly` family evaluates at `primeGap n` in `ℚ`, not necessarily
in `ℤ`. The raw `ℝ[X]` hint therefore fails, and the truncated-orbit
pack wants `ℤ[X]` or a scaled series. Weyl of the unscaled rational
series is already obtained in `GapPolyFromComponents` by component
expansion plus `weylCriterion_add_rat`; this file does not claim
`weylCriterion`.

Clearing a common denominator `D` (product of `ratPolyDenProd` over a
period) yields the integer-coefficient family
`scaledRatPolyFamily P D`, which discharges the hint, with
`gapPolySeries (scaledRatPolyFamily P D) B = D * gapRatPolySeries P B`.
Existing `Independence.weylCriterion_int_mul` /
`weylCriterion_of_mul` transfer Weyl between those two series; not
proved here.

Indexing: Lean `nthPrime 0 = 2` is paper `p_1`.

Source: `TruncatedWeylPack` integer-evaluation `hint`;
`EndAPI.primeGap` / `gapPolySeries` / `mapRatPoly`;
`Components.eval_mapRatPoly_clearDenoms` / `ratPolyDenProd`;
`GapPolyFromComponents.weylCriterion_add_rat` (documentation only).
Contract: API
Audit: GREEN
-/

open Finset Polynomial
open Function (Periodic)

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000

/-! ### Integer polynomials via `algebraMap ℤ ℝ` -/

/-- Coerce an integer polynomial to a real polynomial. -/
noncomputable def mapIntPoly (P : ℤ[X]) : ℝ[X] :=
  P.map (algebraMap ℤ ℝ)

theorem mapIntPoly_coeff (P : ℤ[X]) (n : ℕ) :
    (mapIntPoly P).coeff n = (P.coeff n : ℝ) := by
  unfold mapIntPoly
  rw [coeff_map (algebraMap ℤ ℝ)]
  exact eq_intCast (algebraMap ℤ ℝ) (P.coeff n)

theorem eval_mapIntPoly (P : ℤ[X]) (x : ℕ) :
    eval (x : ℝ) (mapIntPoly P) =
      ((Polynomial.eval (x : ℤ) P : ℤ) : ℝ) := by
  unfold mapIntPoly
  have hx : (x : ℝ) = ((x : ℤ) : ℝ) := Int.cast_natCast x
  rw [hx, eval_map (algebraMap ℤ ℝ) ((x : ℤ) : ℝ)]
  rw [← eq_intCast (algebraMap ℤ ℝ) (x : ℤ), eval₂_at_apply]
  exact eq_intCast (algebraMap ℤ ℝ) (Polynomial.eval (x : ℤ) P)

/-- `ℤ[X]` via `algebraMap` evaluates to an integer at a natural. -/
theorem exists_int_eval_of_mapIntPoly (P : ℤ[X]) (x : ℕ) :
    ∃ z : ℤ, eval (x : ℝ) (mapIntPoly P) = z :=
  ⟨Polynomial.eval (x : ℤ) P, eval_mapIntPoly P x⟩

theorem exists_int_eval_primeGap_of_mapIntPoly (Q : ℤ[X]) (n : ℕ) :
    ∃ z : ℤ, eval (primeGap n : ℝ) (mapIntPoly Q) = z :=
  exists_int_eval_of_mapIntPoly Q (primeGap n)

/-- Family form: `P n = mapIntPoly (Q n)` discharges the
`TruncatedWeylPack` hint. -/
theorem exists_int_eval_primeGap_of_mapIntPoly_family {Q : ℕ → ℤ[X]}
    (n : ℕ) :
    ∃ z : ℤ, eval (primeGap n : ℝ) (mapIntPoly (Q n)) = z :=
  exists_int_eval_of_mapIntPoly (Q n) (primeGap n)

/-! ### Integer coefficients of `ℝ[X]` -/

/-- Recover an integer polynomial from a real polynomial whose
coefficients all lie in `ℤ`. -/
noncomputable def ofIntCoeff (P : ℝ[X])
    (hP : ∀ i, ∃ z : ℤ, P.coeff i = z) : ℤ[X] :=
  ∑ i ∈ range (P.natDegree + 1), C (Classical.choose (hP i)) * X ^ i

private theorem natDegree_lt_of_not_mem_range {R : Type*} [Semiring R]
    {P : R[X]} {n : ℕ} (hn : n ∉ range (P.natDegree + 1)) :
    P.natDegree < n :=
  Nat.add_one_le_iff.mp (Nat.not_lt.mp (mt mem_range.mpr hn))

theorem coeff_ofIntCoeff (P : ℝ[X])
    (hP : ∀ i, ∃ z : ℤ, P.coeff i = z) (n : ℕ) :
    (ofIntCoeff P hP).coeff n =
      if n ∈ range (P.natDegree + 1) then Classical.choose (hP n)
      else 0 := by
  unfold ofIntCoeff
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  exact sum_ite_eq (range (P.natDegree + 1)) n
    (fun i => Classical.choose (hP i))

theorem mapIntPoly_ofIntCoeff (P : ℝ[X])
    (hP : ∀ i, ∃ z : ℤ, P.coeff i = z) :
    mapIntPoly (ofIntCoeff P hP) = P := by
  refine Polynomial.ext fun n => ?_
  rw [mapIntPoly_coeff, coeff_ofIntCoeff]
  by_cases hn : n ∈ range (P.natDegree + 1)
  · rw [if_pos hn]
    exact (Classical.choose_spec (hP n)).symm
  · rw [if_neg hn, Int.cast_zero]
    exact (coeff_eq_zero_of_natDegree_lt
      (natDegree_lt_of_not_mem_range hn)).symm

theorem exists_mapIntPoly_of_int_coeff (P : ℝ[X])
    (hP : ∀ i, ∃ z : ℤ, P.coeff i = z) :
    ∃ Q : ℤ[X], mapIntPoly Q = P :=
  ⟨ofIntCoeff P hP, mapIntPoly_ofIntCoeff P hP⟩

/-- Integer-coefficient polynomials evaluate to integers at naturals.
This is the scalar form of the `TruncatedWeylPack` hint. -/
theorem exists_int_eval_of_int_coeff (P : ℝ[X])
    (hP : ∀ i, ∃ z : ℤ, P.coeff i = z) (x : ℕ) :
    ∃ z : ℤ, eval (x : ℝ) P = z := by
  classical
  rw [eval_eq_sum_range (x : ℝ)]
  let z : ℕ → ℤ := fun i => Classical.choose (hP i) * (x : ℤ) ^ i
  refine ⟨∑ i ∈ range (P.natDegree + 1), z i, ?_⟩
  rw [Int.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  have hi := Classical.choose_spec (hP i)
  have hz : (z i : ℝ) = P.coeff i * (x : ℝ) ^ i := by
    simp only [z]
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    exact (congrArg (fun c : ℝ => c * (x : ℝ) ^ i) hi).symm
  exact hz.symm

/-- Family form of the `TruncatedWeylPack` hint for integer
coefficients. Applied as `exists_int_eval_primeGap_of_int_coeff hP`. -/
theorem exists_int_eval_primeGap_of_int_coeff {P : ℕ → ℝ[X]}
    (hP : ∀ n i, ∃ z : ℤ, (P n).coeff i = z) (n : ℕ) :
    ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z :=
  exists_int_eval_of_int_coeff (P n) (hP n) (primeGap n)

theorem exists_int_eval_primeGap_of_int_coeff_const (P : ℝ[X])
    (hP : ∀ i, ∃ z : ℤ, P.coeff i = z) (n : ℕ) :
    ∃ z : ℤ, eval (primeGap n : ℝ) P = z :=
  exists_int_eval_of_int_coeff P hP (primeGap n)

/-! ### Rational evaluation of `mapRatPoly`

`eval (primeGap n : ℝ) (mapRatPoly (P n))` is rational. That is not
the `TruncatedWeylPack` integer hint. Weyl of `gapRatPolySeries` is
already packaged in `GapPolyFromComponents` via
`weylCriterion_add_rat`; do not pass a raw `mapRatPoly` family as
`hint`. Use `mapIntPoly` or `scaledRatPolyFamily` instead. -/

theorem eval_mapRatPoly_nat (P : ℚ[X]) (x : ℕ) :
    eval (x : ℝ) (mapRatPoly P) =
      ((Polynomial.eval (x : ℚ) P : ℚ) : ℝ) := by
  unfold mapRatPoly
  have hx : (x : ℝ) = ((x : ℚ) : ℝ) := Rat.cast_natCast x
  rw [hx, eval_map (algebraMap ℚ ℝ) ((x : ℚ) : ℝ)]
  rw [← eq_ratCast (algebraMap ℚ ℝ) (x : ℚ), eval₂_at_apply]
  exact eq_ratCast (algebraMap ℚ ℝ) (Polynomial.eval (x : ℚ) P)

theorem exists_rat_eval_of_mapRatPoly (P : ℚ[X]) (x : ℕ) :
    ∃ q : ℚ, eval (x : ℝ) (mapRatPoly P) = q :=
  ⟨Polynomial.eval (x : ℚ) P, eval_mapRatPoly_nat P x⟩

theorem exists_rat_eval_primeGap_of_mapRatPoly {P : ℕ → ℚ[X]} (n : ℕ) :
    ∃ q : ℚ, eval (primeGap n : ℝ) (mapRatPoly (P n)) = q :=
  exists_rat_eval_of_mapRatPoly (P n) (primeGap n)

/-! ### Clearing denominators -/

/-- `ratPolyDenProd P` times a coefficient is an integer. -/
private theorem ratPolyDenProd_mul_coeff (P : ℚ[X]) {i : ℕ}
    (hi : i ∈ range (P.natDegree + 1)) :
    (ratPolyDenProd P : ℝ) * (P.coeff i : ℝ) =
      (((P.coeff i).num *
        (∏ j ∈ (range (P.natDegree + 1)).erase i,
          (P.coeff j).den : ℕ) : ℤ) : ℝ) := by
  unfold ratPolyDenProd
  have hprod :
      (∏ j ∈ range (P.natDegree + 1), (P.coeff j).den) =
        (P.coeff i).den *
          ∏ j ∈ (range (P.natDegree + 1)).erase i, (P.coeff j).den :=
    (mul_prod_erase (range (P.natDegree + 1))
      (fun j => (P.coeff j).den) hi).symm
  rw [hprod]
  have hden :
      ((P.coeff i).den : ℝ) * (P.coeff i : ℝ) =
        ((P.coeff i).num : ℝ) := by
    exact_mod_cast (P.coeff i).den_mul_eq_num
  push_cast
  calc
    ((P.coeff i).den : ℝ) *
          (∏ j ∈ (range (P.natDegree + 1)).erase i,
            (P.coeff j).den : ℝ) *
          (P.coeff i : ℝ)
        = (((P.coeff i).den : ℝ) * (P.coeff i : ℝ)) *
            (∏ j ∈ (range (P.natDegree + 1)).erase i,
              (P.coeff j).den : ℝ) := by
          ring
    _ = ((P.coeff i).num : ℝ) *
          (∏ j ∈ (range (P.natDegree + 1)).erase i,
            (P.coeff j).den : ℝ) := by
          rw [hden]

theorem exists_int_mul_coeff_ratPolyDenProd (P : ℚ[X]) (i : ℕ) :
    ∃ z : ℤ, (ratPolyDenProd P : ℝ) * (P.coeff i : ℝ) = z := by
  by_cases hi : i ∈ range (P.natDegree + 1)
  · exact ⟨_, ratPolyDenProd_mul_coeff P hi⟩
  · have h0 : P.coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (natDegree_lt_of_not_mem_range hi)
    refine ⟨0, ?_⟩
    rw [h0, Rat.cast_zero, mul_zero, Int.cast_zero]

theorem exists_int_eval_mul_ratPolyDenProd (P : ℚ[X]) (x : ℕ) :
    ∃ z : ℤ,
      (ratPolyDenProd P : ℝ) * eval (x : ℝ) (mapRatPoly P) = z := by
  rw [eval_mapRatPoly_clearDenoms]
  let z : ℕ → ℤ := fun i =>
    ((P.coeff i).num *
        (∏ j ∈ (range (P.natDegree + 1)).erase i,
          (P.coeff j).den : ℕ)) *
      (x : ℤ) ^ i
  refine ⟨∑ i ∈ range (P.natDegree + 1), z i, ?_⟩
  rw [Int.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  have hz : (z i : ℝ) =
      (((P.coeff i).num *
          (∏ j ∈ (range (P.natDegree + 1)).erase i,
            (P.coeff j).den : ℕ) : ℤ) : ℝ) *
        (x : ℝ) ^ i := by
    simp only [z]
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  exact hz.symm

/-! ### Scaled integer family -/

/-- Common-denominator scaling of a rational family. Integer
coefficients as soon as `ratPolyDenProd (P n) ∣ D`. -/
noncomputable def scaledRatPolyFamily (P : ℕ → ℚ[X]) (D : ℕ) :
    ℕ → ℝ[X] :=
  fun n => C (D : ℝ) * mapRatPoly (P n)

theorem eval_scaledRatPolyFamily (P : ℕ → ℚ[X]) (D n : ℕ) (x : ℝ) :
    eval x (scaledRatPolyFamily P D n) =
      (D : ℝ) * eval x (mapRatPoly (P n)) := by
  unfold scaledRatPolyFamily
  rw [eval_C_mul]

theorem periodic_scaledRatPolyFamily {P : ℕ → ℚ[X]} {k D : ℕ}
    (hP : Periodic P k) :
    Periodic (scaledRatPolyFamily P D) k :=
  fun n => congrArg (fun Q => C (D : ℝ) * mapRatPoly Q) (hP n)

theorem exists_int_coeff_scaledMapRatPoly {P : ℚ[X]} {D : ℕ}
    (hD : ratPolyDenProd P ∣ D) (i : ℕ) :
    ∃ z : ℤ, (C (D : ℝ) * mapRatPoly P).coeff i = z := by
  rw [coeff_C_mul, mapRatPoly_coeff]
  obtain ⟨t, ht⟩ := hD
  obtain ⟨z, hz⟩ := exists_int_mul_coeff_ratPolyDenProd P i
  refine ⟨(t : ℤ) * z, ?_⟩
  have hDt : (D : ℝ) = (ratPolyDenProd P : ℝ) * (t : ℝ) := by
    rw [ht, Nat.cast_mul]
  rw [hDt, mul_assoc, mul_left_comm, hz]
  rw [Int.cast_mul, Int.cast_natCast]

theorem exists_int_coeff_scaledRatPolyFamily {P : ℕ → ℚ[X]} {D : ℕ}
    (hD : ∀ n, ratPolyDenProd (P n) ∣ D) :
    ∀ n i, ∃ z : ℤ, (scaledRatPolyFamily P D n).coeff i = z :=
  fun n i => exists_int_coeff_scaledMapRatPoly (hD n) i

/-- Scaled rational polynomial: the `TruncatedWeylPack` hint. -/
theorem exists_int_eval_primeGap_scaledRatPolyFamily {P : ℕ → ℚ[X]}
    {D : ℕ} (hD : ∀ n, ratPolyDenProd (P n) ∣ D) (n : ℕ) :
    ∃ z : ℤ,
      eval (primeGap n : ℝ) (scaledRatPolyFamily P D n) = z :=
  exists_int_eval_primeGap_of_int_coeff
    (exists_int_coeff_scaledRatPolyFamily hD) n

theorem exists_int_eval_primeGap_scaledRatPolyFamily_const (P : ℚ[X])
    (n : ℕ) :
    ∃ z : ℤ,
      eval (primeGap n : ℝ)
        (scaledRatPolyFamily (fun _ => P) (ratPolyDenProd P) n) = z :=
  exists_int_eval_primeGap_scaledRatPolyFamily
    (fun _ => dvd_refl (ratPolyDenProd P)) n

/-! ### Periodic common denominator -/

private theorem periodic_nsmul {α : Type*} {f : ℕ → α} {k : ℕ}
    (hf : Periodic f k) (x q : ℕ) : f (x + k * q) = f x := by
  induction q with
  | zero =>
    rw [mul_zero, add_zero]
  | succ q ih =>
    rw [mul_add, mul_one, ← add_assoc, hf, ih]

private theorem periodic_mod {α : Type*} {f : ℕ → α} {k : ℕ}
    (hf : Periodic f k) (n : ℕ) : f n = f (n % k) := by
  have hn : n = n % k + k * (n / k) := (Nat.mod_add_div n k).symm
  have hper := periodic_nsmul hf (n % k) (n / k)
  conv_lhs => rw [hn]
  exact hper

/-- Product of coefficient-denominator products over one period. -/
noncomputable def periodicRatPolyDenProd (P : ℕ → ℚ[X]) (k : ℕ) : ℕ :=
  ∏ r ∈ range k, ratPolyDenProd (P r)

theorem ratPolyDenProd_dvd_periodicRatPolyDenProd {P : ℕ → ℚ[X]}
    {k : ℕ} (hk : 1 ≤ k) (hP : Periodic P k) (n : ℕ) :
    ratPolyDenProd (P n) ∣ periodicRatPolyDenProd P k := by
  have hkpos : 0 < k := Nat.succ_le_iff.mp hk
  have hmem : n % k ∈ range k := mem_range.mpr (Nat.mod_lt n hkpos)
  have heq : P n = P (n % k) := periodic_mod hP n
  rw [heq]
  exact dvd_prod_of_mem (fun r => ratPolyDenProd (P r)) hmem

/-- Periodic rational family: after clearing the period denominator,
the scaled series satisfies the `TruncatedWeylPack` hint. -/
theorem exists_int_eval_primeGap_scaledRatPolyFamily_periodic
    {P : ℕ → ℚ[X]} {k : ℕ} (hk : 1 ≤ k) (hP : Periodic P k) (n : ℕ) :
    ∃ z : ℤ,
      eval (primeGap n : ℝ)
        (scaledRatPolyFamily P (periodicRatPolyDenProd P k) n) = z :=
  exists_int_eval_primeGap_scaledRatPolyFamily
    (fun m => ratPolyDenProd_dvd_periodicRatPolyDenProd hk hP m) n

/-! ### Series identity (Weyl transfers by existing Wall lemmas) -/

theorem eval_scaledRatPolyFamily_div (P : ℕ → ℚ[X]) (B D n : ℕ) :
    eval (primeGap n : ℝ) (scaledRatPolyFamily P D n) /
        (B : ℝ) ^ (n + 1) =
      (D : ℝ) *
        (eval (primeGap n : ℝ) (mapRatPoly (P n)) /
          (B : ℝ) ^ (n + 1)) := by
  rw [eval_scaledRatPolyFamily, mul_div_assoc]

/-- Termwise scaling of the series. If the scaled family is Weyl then
so is the rational series, by `weylCriterion_of_mul` (not claimed
here); conversely `weylCriterion_int_mul`. -/
theorem gapPolySeries_scaledRatPolyFamily {P : ℕ → ℚ[X]} {B : ℕ}
    (D : ℕ)
    (hsm : Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (mapRatPoly (P n)) / (B : ℝ) ^ (n + 1)) :
    gapPolySeries (scaledRatPolyFamily P D) B =
      (D : ℝ) * gapRatPolySeries P B := by
  unfold gapRatPolySeries
  unfold gapPolySeries
  simp_rw [eval_scaledRatPolyFamily_div]
  exact hsm.tsum_mul_left (D : ℝ)

theorem gapPolySeries_scaledRatPolyFamily_const (P : ℚ[X]) {B D : ℕ}
    (hB : 2 ≤ B) :
    gapPolySeries (scaledRatPolyFamily (fun _ => P) D) B =
      (D : ℝ) * gapRatPolySeries (fun _ => P) B :=
  gapPolySeries_scaledRatPolyFamily D
    (gapRatPolySeries_const_summable P hB)

theorem gapPolySeries_scaledRatPolyFamily_periodic
    {P : ℕ → ℚ[X]} {B k D : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (hP : Periodic P k) :
    gapPolySeries (scaledRatPolyFamily P D) B =
      (D : ℝ) * gapRatPolySeries P B :=
  gapPolySeries_scaledRatPolyFamily D
    (gapRatPolySeries_periodic_summable hB hk hP)

end PrimeGapNormality.Prime
