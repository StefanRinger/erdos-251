import PrimeGapNormality.Prime.CoreCyclicSeriesConvergence
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The literal local-series recurrence

Labels in this file are relative to the start of each series.  This matters:
the summand at relative index `i` uses `phaseAt hk r i`, while its gap window
starts at the absolute index `n+i`.  Thus advancing `n` by a whole period
does not silently advance the marked label.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Finset MvPolynomial
open scoped BigOperators

noncomputable section

/-- Evaluation at relative label `i` and absolute gap window `n+i`. -/
def relativeLocalValue {k : ℕ} (hk : 0 < k) (r : Fin k) (g : ℕ → ℝ)
    (F : PeriodicLocal k) (n i : ℕ) : ℝ :=
  eval₂ (algebraMap ℚ ℝ) (fun j ↦ g (n + i + j)) (F (phaseAt hk r i))

/-- The actual infinite local series based at `n`, with labels restarted at
`r`. -/
def coreLocalSeries (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F : PeriodicLocal k) (n : ℕ) : ℝ :=
  ∑' i : ℕ, relativeLocalValue hk r g F n i / (B : ℝ) ^ (i + 1)

/-- The finite correction exposed by multiplying the series by `B^k`. -/
def coreLocalFirstBlock (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F : PeriodicLocal k) (n : ℕ) : ℝ :=
  ∑ i ∈ range k,
    (B : ℝ) ^ (k - (i + 1)) * relativeLocalValue hk r g F n i

theorem phaseAt_add_period {k : ℕ} (hk : 0 < k) (r : Fin k) (i : ℕ) :
    phaseAt hk r (k + i) = phaseAt hk r i := by
  unfold phaseAt
  rw [Function.iterate_add_apply, cyclicSucc_period]

/-- Advancing the relative index by `k` is exactly advancing the absolute
window start by `k`; the label returns to its initial phase. -/
theorem relativeLocalValue_add_period {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F : PeriodicLocal k) (n i : ℕ) :
    relativeLocalValue hk r g F n (i + k) =
      relativeLocalValue hk r g F (n + k) i := by
  unfold relativeLocalValue
  rw [show i + k = k + i by omega, phaseAt_add_period]
  congr 1
  funext j
  congr 1
  omega

theorem relativeLocalSeries_summable {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (hg : HasPolynomialGrowth g)
    (F : PeriodicLocal k) (n : ℕ) :
    Summable fun i : ℕ ↦
      relativeLocalValue hk r g F n i / (B : ℝ) ^ (i + 1) := by
  have hgn : HasPolynomialGrowth fun j ↦ g (n + j) := by
    simpa only [Nat.add_comm] using hg.shift n
  have hs := localSeries_summable hB hk r (fun j ↦ g (n + j))
    hgn F 0
  simpa only [relativeLocalValue, localValue, Nat.zero_add, Nat.add_assoc] using hs

private theorem relativeLocalSeries_tail_eq {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (hg : HasPolynomialGrowth g)
    (F : PeriodicLocal k) (n : ℕ) :
    (∑' i : ℕ,
      relativeLocalValue hk r g F n (i + k) / (B : ℝ) ^ (i + k + 1)) =
      coreLocalSeries B hk r g F (n + k) / (B : ℝ) ^ k := by
  have hs := relativeLocalSeries_summable hB hk r g hg F (n + k)
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  unfold coreLocalSeries
  rw [← tsum_div_const]
  apply tsum_congr
  intro i
  rw [relativeLocalValue_add_period]
  have hexp : i + k + 1 = (i + 1) + k := by omega
  rw [hexp, pow_add]
  field_simp [hB0]

private theorem coreLocalFirstBlock_eq_scale_sum {B k : ℕ} (hB : 2 ≤ B)
    (hk : 0 < k) (r : Fin k) (g : ℕ → ℝ) (F : PeriodicLocal k) (n : ℕ) :
    coreLocalFirstBlock B hk r g F n =
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

/-- The exact real recurrence.  The correction is the displayed first-`k`
sum, with no marked-index or residue-class distribution input. -/
theorem coreLocalSeries_add_period {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (hg : HasPolynomialGrowth g)
    (F : PeriodicLocal k) (n : ℕ) :
    coreLocalSeries B hk r g F (n + k) =
      (B : ℝ) ^ k * coreLocalSeries B hk r g F n -
        coreLocalFirstBlock B hk r g F n := by
  let term : ℕ → ℝ := fun i ↦
    relativeLocalValue hk r g F n i / (B : ℝ) ^ (i + 1)
  have hs : Summable term := relativeLocalSeries_summable hB hk r g hg F n
  have hsplit := hs.sum_add_tsum_nat_add k
  have htail : (∑' i : ℕ, term (i + k)) =
      coreLocalSeries B hk r g F (n + k) / (B : ℝ) ^ k := by
    simpa only [term, Nat.add_assoc] using
      relativeLocalSeries_tail_eq hB hk r g hg F n
  have hfirst := coreLocalFirstBlock_eq_scale_sum hB hk r g F n
  change
    (∑ i ∈ range k,
        relativeLocalValue hk r g F n i / (B : ℝ) ^ (i + 1)) +
        (∑' i : ℕ,
          relativeLocalValue hk r g F n (i + k) / (B : ℝ) ^ (i + k + 1)) =
      coreLocalSeries B hk r g F n at hsplit
  rw [htail] at hsplit
  rw [hfirst]
  have hBk0 : (B : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by positivity)
  field_simp [hBk0] at hsplit
  linarith

/-! ## Integer coefficients and the circle recurrence -/

/-- Embed an actual integer-coefficient tuple into the rational tuple used by
the canonical local algebra. -/
def mapIntTuple {k : ℕ} (F : Fin k → MvPolynomial ℕ ℤ) : PeriodicLocal k :=
  fun s ↦ MvPolynomial.map (algebraMap ℤ ℚ) (F s)

/-- The same relative local evaluation, performed before embedding into
`ℝ`. -/
def relativeLocalValueInt {k : ℕ} (hk : 0 < k) (r : Fin k) (g : ℕ → ℤ)
    (F : Fin k → MvPolynomial ℕ ℤ) (n i : ℕ) : ℤ :=
  eval₂ (RingHom.id ℤ) (fun j ↦ g (n + i + j)) (F (phaseAt hk r i))

private theorem eval₂_map_int_rat_real (p : MvPolynomial ℕ ℤ) (x : ℕ → ℤ) :
    eval₂ (algebraMap ℚ ℝ) (fun j ↦ (x j : ℝ))
        (MvPolynomial.map (algebraMap ℤ ℚ) p) =
      ((eval₂ (RingHom.id ℤ) x p : ℤ) : ℝ) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.map_C, MvPolynomial.eval₂_C, RingHom.id_apply]
      norm_cast
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq, Int.cast_add]
  | mul_X p j hp =>
      simp only [map_mul, map_X, eval₂_mul, eval₂_X, hp, Int.cast_mul]

theorem relativeLocalValue_mapIntTuple {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℤ) (F : Fin k → MvPolynomial ℕ ℤ) (n i : ℕ) :
    relativeLocalValue hk r (fun j ↦ (g j : ℝ)) (mapIntTuple F) n i =
      (relativeLocalValueInt hk r g F n i : ℝ) := by
  unfold relativeLocalValue relativeLocalValueInt mapIntTuple
  exact eval₂_map_int_rat_real _ _

/-- The integer whose real image is the first-block correction. -/
def coreLocalFirstBlockInt (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℤ) (F : Fin k → MvPolynomial ℕ ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ range k,
    (B : ℤ) ^ (k - (i + 1)) * relativeLocalValueInt hk r g F n i

theorem coreLocalFirstBlock_mapIntTuple {B k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℤ) (F : Fin k → MvPolynomial ℕ ℤ) (n : ℕ) :
    coreLocalFirstBlock B hk r (fun j ↦ (g j : ℝ)) (mapIntTuple F) n =
      (coreLocalFirstBlockInt B hk r g F n : ℝ) := by
  unfold coreLocalFirstBlock coreLocalFirstBlockInt
  rw [Int.cast_sum]
  apply sum_congr rfl
  intro i hi
  rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    relativeLocalValue_mapIntTuple]

/-- The local series viewed modulo one. -/
def coreLocalSeriesCircle (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F : PeriodicLocal k) (n : ℕ) : AddCircle (1 : ℝ) :=
  (coreLocalSeries B hk r g F n : AddCircle (1 : ℝ))

private theorem coreCircle_intCast_eq_zero (z : ℤ) :
    ((z : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  have h := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := z) (x := (1 : ℝ))
  simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using h

/-- For integer coefficients and integer gaps, the exact first-block
correction disappears modulo one.  This is the literal `k`-step recurrence
needed by the periodic digital rigidity adapter. -/
theorem coreLocalSeriesCircle_add_period_of_intTuple {B k : ℕ} (hB : 2 ≤ B)
    (hk : 0 < k) (r : Fin k) (g : ℕ → ℤ)
    (hg : HasPolynomialGrowth fun n ↦ (g n : ℝ))
    (F : Fin k → MvPolynomial ℕ ℤ) (n : ℕ) :
    coreLocalSeriesCircle B hk r (fun j ↦ (g j : ℝ)) (mapIntTuple F) (n + k) =
      B ^ k • coreLocalSeriesCircle B hk r (fun j ↦ (g j : ℝ)) (mapIntTuple F) n := by
  have hrec := coreLocalSeries_add_period hB hk r (fun j ↦ (g j : ℝ)) hg
    (mapIntTuple F) n
  have hint := coreLocalFirstBlock_mapIntTuple (B := B) hk r g F n
  unfold coreLocalSeriesCircle
  rw [hrec, hint, AddCircle.coe_sub, coreCircle_intCast_eq_zero, sub_zero]
  simpa only [nsmul_eq_mul, Nat.cast_pow] using
    (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := B ^ k)
      (x := coreLocalSeries B hk r (fun j ↦ (g j : ℝ)) (mapIntTuple F) n))

end

end PrimeGapNormality.Prime.CoreCyclic
