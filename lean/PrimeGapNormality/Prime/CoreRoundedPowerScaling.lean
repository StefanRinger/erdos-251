import PrimeGapNormality.Prime.CoreSubexponentialAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Compact scaling of rounded real powers

This file treats actual integer floors and ceilings.  For a finite periodic
integer combination of powers, it groups the terms having the largest
exponent `a` into `leadingColumn` and proves, uniformly for the period label
and every integer `0 ≤ q ≤ A G`, the compact expansion

`G^(-a) F_s(q) = leadingColumn_s * (q/G)^a + o_A(1)`.

The error is proved from the literal floor/ceiling inequalities and a finite
sum of negative real powers of `G`; no asymptotic expansion is an input.
The same data also give the paper's genuine linear growth bound on positive
integer arguments when all exponents lie in `(0,1]`.
-/

namespace PrimeGapNormality.Prime.CoreRoundedPowerScaling

open Finset Filter
open scoped Topology BigOperators Classical

noncomputable section

inductive RoundKind
  | floor
  | ceil
  deriving DecidableEq

/-- Actual integer floor or ceiling of a nonnegative real power. -/
def roundedPower (kind : RoundKind) (alpha : ℝ) (q : ℕ) : ℤ :=
  match kind with
  | .floor => ⌊(q : ℝ) ^ alpha⌋
  | .ceil => ⌈(q : ℝ) ^ alpha⌉

/-- Actual integer-valued finite periodic combination. -/
def roundedCombination {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (s : Fin k) (q : ℕ) : ℤ :=
  ∑ i, b s i * roundedPower kind (alpha i) q

/-- The same finite combination after the canonical cast to the reals. -/
def roundedCombinationReal {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (s : Fin k) (q : ℕ) : ℝ :=
  ∑ i, (b s i : ℝ) * (roundedPower kind (alpha i) q : ℝ)

theorem roundedCombination_cast {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (s : Fin k) (q : ℕ) :
    (roundedCombination kind alpha b s q : ℝ) =
      roundedCombinationReal kind alpha b s q := by
  simp [roundedCombination, roundedCombinationReal]

/-- Coefficient column obtained by grouping all terms with exponent `a`. -/
def leadingColumn {I : Type*} [Fintype I] {k : ℕ}
    (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (a : ℝ) (s : Fin k) : ℝ :=
  ∑ i, if alpha i = a then (b s i : ℝ) else 0

/-- Both actual rounding operations have error at most one. -/
theorem abs_roundedPower_sub_rpow_le_one
    (kind : RoundKind) (alpha : ℝ) (q : ℕ) :
    |(roundedPower kind alpha q : ℝ) - (q : ℝ) ^ alpha| ≤ 1 := by
  cases kind with
  | floor =>
      unfold roundedPower
      rw [abs_le]
      constructor
      · linarith [Int.lt_floor_add_one ((q : ℝ) ^ alpha)]
      · linarith [Int.floor_le ((q : ℝ) ^ alpha)]
  | ceil =>
      unfold roundedPower
      rw [abs_le]
      constructor
      · linarith [Int.le_ceil ((q : ℝ) ^ alpha)]
      · linarith [Int.ceil_lt_add_one ((q : ℝ) ^ alpha)]

theorem abs_roundedPower_le_rpow_add_one
    (kind : RoundKind) {alpha : ℝ} (q : ℕ) :
    |(roundedPower kind alpha q : ℝ)| ≤ (q : ℝ) ^ alpha + 1 := by
  have hx : 0 ≤ (q : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    |(roundedPower kind alpha q : ℝ)| =
        |((roundedPower kind alpha q : ℝ) - (q : ℝ) ^ alpha) +
          (q : ℝ) ^ alpha| := by congr 1 <;> ring
    _ ≤ |(roundedPower kind alpha q : ℝ) - (q : ℝ) ^ alpha| +
        |(q : ℝ) ^ alpha| := abs_add_le _ _
    _ ≤ 1 + (q : ℝ) ^ alpha :=
      _root_.add_le_add (abs_roundedPower_sub_rpow_le_one kind alpha q)
        (le_of_eq (abs_of_nonneg hx))
    _ = (q : ℝ) ^ alpha + 1 := add_comm _ _

/-- Finite rounded combinations have the actual linear growth asserted in
the paper. -/
theorem roundedCombinationReal_abs_le_linear
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (halpha : ∀ i, 0 < alpha i ∧ alpha i ≤ 1)
    (s : Fin k) {q : ℕ} (hq : 1 ≤ q) :
    |roundedCombinationReal kind alpha b s q| ≤
      (2 * ∑ i, |(b s i : ℝ)|) * (q : ℝ) := by
  have hqR : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
  have hterm (i : I) :
      |(b s i : ℝ) * (roundedPower kind (alpha i) q : ℝ)| ≤
        2 * |(b s i : ℝ)| * (q : ℝ) := by
    have hp : (q : ℝ) ^ alpha i ≤ (q : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hqR (halpha i).2
    have hr := abs_roundedPower_le_rpow_add_one kind q (alpha := alpha i)
    have hrq : |(roundedPower kind (alpha i) q : ℝ)| ≤ 2 * (q : ℝ) :=
      hr.trans (by linarith)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hrq (abs_nonneg _)).trans_eq (by ring)
  unfold roundedCombinationReal
  calc
    |∑ i, (b s i : ℝ) * (roundedPower kind (alpha i) q : ℝ)| ≤
        ∑ i, |(b s i : ℝ) * (roundedPower kind (alpha i) q : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * |(b s i : ℝ)| * (q : ℝ) := sum_le_sum fun i _ ↦ hterm i
    _ = (2 * ∑ i, |(b s i : ℝ)|) * (q : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_mul]

private theorem scaled_rpow_identity {G q a : ℝ} (hG : 0 < G) (hq : 0 ≤ q) :
    G ^ (-a) * q ^ a = (q / G) ^ a := by
  rw [Real.div_rpow hq hG.le, Real.rpow_neg hG.le]
  field_simp [(Real.rpow_pos_of_pos hG a).ne']

private theorem scaled_lower_rpow_le
    {G A q alpha a : ℝ} (hG : 0 < G) (hA : 0 ≤ A) (hq0 : 0 ≤ q)
    (hq : q ≤ A * G) (halpha : 0 < alpha) :
    G ^ (-a) * q ^ alpha ≤ A ^ alpha * G ^ (alpha - a) := by
  have hpow := Real.rpow_le_rpow hq0 hq halpha.le
  rw [Real.mul_rpow hA hG.le] at hpow
  have hs := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hG.le (-a))
  refine hs.trans_eq ?_
  calc
    G ^ (-a) * (A ^ alpha * G ^ alpha) =
        A ^ alpha * (G ^ (-a) * G ^ alpha) := by ring
    _ = A ^ alpha * G ^ (-a + alpha) := by rw [Real.rpow_add hG]
    _ = A ^ alpha * G ^ (alpha - a) := by ring_nf

/-- Explicit finite error envelope for one label. -/
def compactErrorEnvelope {I : Type*} [Fintype I] {k : ℕ}
    (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (a A G : ℝ) (s : Fin k) : ℝ :=
  ∑ i, |(b s i : ℝ)| *
    (G ^ (-a) + if alpha i = a then 0
      else A ^ alpha i * G ^ (alpha i - a))

def uniformCompactErrorEnvelope {I : Type*} [Fintype I] {k : ℕ}
    (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (a A G : ℝ) : ℝ :=
  ∑ s, compactErrorEnvelope alpha b a A G s

/-- Quantitative compact expansion before taking `G → ∞`. -/
theorem roundedCombination_compact_error_le
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a A G : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hG : 0 < G)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    (s : Fin k) (q : ℕ) (hq : (q : ℝ) ≤ A * G) :
    |G ^ (-a) * roundedCombinationReal kind alpha b s q -
        leadingColumn alpha b a s * ((q : ℝ) / G) ^ a| ≤
      compactErrorEnvelope alpha b a A G s := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hdecomp :
      G ^ (-a) * roundedCombinationReal kind alpha b s q -
          leadingColumn alpha b a s * ((q : ℝ) / G) ^ a =
        ∑ i, (G ^ (-a) * ((b s i : ℝ) *
              (roundedPower kind (alpha i) q : ℝ)) -
            if alpha i = a then
              (b s i : ℝ) * ((q : ℝ) / G) ^ a else 0) := by
    unfold roundedCombinationReal leadingColumn
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases hai : alpha i = a
    · simp only [if_pos hai]
    · simp only [if_neg hai, zero_mul, sub_zero]
  rw [hdecomp]
  unfold compactErrorEnvelope
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi ↦ ?_)
  by_cases hai : alpha i = a
  · have hscale := scaled_rpow_identity (a := a) hG hq0
    have heq :
        G ^ (-a) * ((b s i : ℝ) *
            (roundedPower kind (alpha i) q : ℝ)) -
          (b s i : ℝ) * ((q : ℝ) / G) ^ a =
        (b s i : ℝ) * G ^ (-a) *
          ((roundedPower kind (alpha i) q : ℝ) - (q : ℝ) ^ alpha i) := by
      rw [hai, ← hscale]
      ring
    simp only [if_pos hai]
    have hr := abs_roundedPower_sub_rpow_le_one kind (alpha i) q
    have hs0 : 0 ≤ G ^ (-a) := Real.rpow_nonneg hG.le _
    rw [heq]
    calc
      |(b s i : ℝ) * G ^ (-a) *
          ((roundedPower kind (alpha i) q : ℝ) - (q : ℝ) ^ alpha i)| =
        |(b s i : ℝ)| * G ^ (-a) *
          |(roundedPower kind (alpha i) q : ℝ) - (q : ℝ) ^ alpha i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hs0]
      _ ≤ |(b s i : ℝ)| * G ^ (-a) * 1 :=
        mul_le_mul_of_nonneg_left hr
          (mul_nonneg (abs_nonneg _) hs0)
      _ = |(b s i : ℝ)| * (G ^ (-a) + 0) := by ring
  · have haiLt : alpha i < a := (halpha i).2.resolve_left hai
    have hr := abs_roundedPower_le_rpow_add_one kind q (alpha := alpha i)
    have hs := scaled_lower_rpow_le (a := a) hG hA hq0 hq (halpha i).1
    simp only [if_neg hai, sub_zero]
    have hs0 : 0 ≤ G ^ (-a) := Real.rpow_nonneg hG.le _
    have hnonneg : 0 ≤ |(b s i : ℝ)| := abs_nonneg _
    calc
      |G ^ (-a) * ((b s i : ℝ) *
          (roundedPower kind (alpha i) q : ℝ))| =
        G ^ (-a) * |(b s i : ℝ)| *
          |(roundedPower kind (alpha i) q : ℝ)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hs0]
            ring
      _ ≤ G ^ (-a) * |(b s i : ℝ)| * ((q : ℝ) ^ alpha i + 1) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg hs0 hnonneg)
      _ = |(b s i : ℝ)| *
          (G ^ (-a) * (q : ℝ) ^ alpha i + G ^ (-a)) := by ring
      _ ≤ |(b s i : ℝ)| *
          (A ^ alpha i * G ^ (alpha i - a) + G ^ (-a)) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add hs le_rfl) hnonneg
      _ = |(b s i : ℝ)| *
          (G ^ (-a) + A ^ alpha i * G ^ (alpha i - a)) := by ring

private theorem tendsto_finset_sum_nhds_zero
    {J : Type*} (t : Finset J) (f : J → ℝ → ℝ)
    (hf : ∀ j ∈ t, Tendsto (f j) atTop (nhds 0)) :
    Tendsto (fun G ↦ ∑ j ∈ t, f j G) atTop (nhds 0) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds (x := (0 : ℝ))
  | @insert j t hj ih =>
      simp_rw [sum_insert hj]
      simpa only [zero_add] using (hf j (mem_insert_self _ _)).add
        (ih (fun i hi ↦ hf i (mem_insert_of_mem hi)))

/-- The explicit error envelope tends to zero for every fixed compact radius. -/
theorem tendsto_uniformCompactErrorEnvelope_zero
    {I : Type*} [Fintype I] {k : ℕ}
    (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a)) :
    Tendsto (uniformCompactErrorEnvelope alpha b a A) atTop (nhds 0) := by
  unfold uniformCompactErrorEnvelope compactErrorEnvelope
  apply tendsto_finset_sum_nhds_zero univ
  intro s hs
  apply tendsto_finset_sum_nhds_zero univ
  intro i hi
  have hmain := _root_.tendsto_rpow_neg_atTop ha
  by_cases hai : alpha i = a
  · simp only [if_pos hai, add_zero]
    simpa only [mul_zero] using hmain.const_mul |(b s i : ℝ)|
  · have hlt : alpha i < a := (halpha i).2.resolve_left hai
    have hlower := _root_.tendsto_rpow_neg_atTop (sub_pos.mpr hlt)
    have hlower' : Tendsto (fun G : ℝ ↦ G ^ (alpha i - a)) atTop (nhds 0) := by
      simpa only [show alpha i - a = -(a - alpha i) by ring] using hlower
    have hsecond := hlower'.const_mul (A ^ alpha i)
    have hsum := hmain.add hsecond
    simp only [zero_add, mul_zero] at hsum
    simp only [if_neg hai]
    simpa only [mul_zero] using hsum.const_mul |(b s i : ℝ)|

/-- Uniform compact leading-exponent expansion, simultaneously for all
period labels and all integer points `q ≤ A G`. -/
theorem eventually_roundedCombination_compact_expansion
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a A : ℝ} (ha : 0 < a) (haOne : a ≤ 1) (hA : 0 ≤ A)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ G : ℝ in atTop,
      ∀ s : Fin k, ∀ q : ℕ, (q : ℝ) ≤ A * G →
        |G ^ (-a) * roundedCombinationReal kind alpha b s q -
          leadingColumn alpha b a s * ((q : ℝ) / G) ^ a| < ε := by
  intro ε hε
  have hlim := tendsto_uniformCompactErrorEnvelope_zero alpha b ha hA halpha
  filter_upwards [hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hε),
    eventually_gt_atTop (0 : ℝ)] with G hball hG
  intro s q hq
  have hpoint := roundedCombination_compact_error_le kind alpha b ha hA hG halpha s q hq
  have henv0 : 0 ≤ uniformCompactErrorEnvelope alpha b a A G := by
    unfold uniformCompactErrorEnvelope compactErrorEnvelope
    exact sum_nonneg fun t ht ↦ sum_nonneg fun i hi ↦
      mul_nonneg (abs_nonneg _) (add_nonneg (Real.rpow_nonneg hG.le _)
        (by split_ifs <;> positivity))
  have hsingle : compactErrorEnvelope alpha b a A G s ≤
      uniformCompactErrorEnvelope alpha b a A G := by
    unfold uniformCompactErrorEnvelope
    exact single_le_sum (fun t ht ↦ by
      unfold compactErrorEnvelope
      exact sum_nonneg fun i hi ↦
        mul_nonneg (abs_nonneg _) (add_nonneg (Real.rpow_nonneg hG.le _)
          (by split_ifs <;> positivity))) (mem_univ s)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg henv0] at hball
  exact hpoint.trans_lt (hsingle.trans_lt hball)

end
end PrimeGapNormality.Prime.CoreRoundedPowerScaling
