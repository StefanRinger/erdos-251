import PrimeGapNormality.Prime.Fourier
import PrimeGapNormality.Prime.GapPolynomialPhase
import PrimeGapNormality.Prime.GapPolySummable
import PrimeGapNormality.Prime.StatisticalCriterion
import PrimeGapNormality.Prime.WeylMeans
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.MetricSpace.Basic

/-!
# Uniform truncated-orbit packing for `gapPolySeries`

`TruncatedPhaseWeyl` is Cesàro vanishing of `e(τ Φ_L(n))`. The orbit
passage is `WeylMeans.weylCriterion_of_uniform_truncation` /
`cesaroMean_e_trunc`: if the untruncated tail of the phase is uniformly
small, the integer orbit identity upgrades that vanishing to
`weylCriterion B (gapPolySeries P B)`.

The truncated orbit phase is the finite gap-polynomial sum
`seqGapPolyTailTrunc` (paper `Φ_L`). For a constant polynomial it equals
`finiteGapPolyPhase` on the offset list. The two-summand interior of that
finite phase is `freeGapPolyPhase` via
`finiteGapPolyPhase_sub_insertAt`. This module does not assemble model
cancellation or a Kuperberg implication.

Summability of the full series versus its finite truncation is taken
from `GapPolySummable` (or as an explicit `Summable` hypothesis).

Source: `StatisticalCriterion.TruncatedPhaseWeyl`,
`WeylMeans.weylCriterion_of_uniform_truncation`,
`GapPolynomialPhase.finiteGapPolyPhase`.
Contract: API
Audit: GREEN
-/

open Finset Filter Polynomial
open Function (Periodic)
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem e_int (n : ℤ) : e n = 1 := by
  unfold e
  simp only [Complex.ofReal_intCast]
  have h : (2 * Real.pi * Complex.I * (n : ℂ)) = n * (2 * Real.pi * Complex.I) := by
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-! ### Integer evaluations -/

/-- Integer-coefficient polynomials evaluate to integers at naturals. -/
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

theorem exists_int_eval_primeGap_of_int_coeff {P : ℕ → ℝ[X]}
    (hP : ∀ n i, ∃ z : ℤ, (P n).coeff i = z) (n : ℕ) :
    ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z :=
  exists_int_eval_of_int_coeff (P n) (hP n) (primeGap n)

/-! ### Finite Abel / `finiteGapPolyPhase` identification -/

/-- Offset list `x_k = a_{n+k} - a_n` for the finite one-gap phase.
`phasePoint` of this list recovers the offsets, so `realGap` recovers
`seqGap`. -/
def orbitOffsetList (a : ℕ → ℕ) (n L : ℕ) : List ℕ :=
  (List.range L).map (fun k => seqOffset a n (k + 1))

private theorem orbitOffsetList_getD (a : ℕ → ℕ) (n L k : ℕ)
    (hk : k < L) :
    (orbitOffsetList a n L).getD k 0 = seqOffset a n (k + 1) := by
  simp [orbitOffsetList, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range, hk]

theorem phasePoint_orbitOffsetList (a : ℕ → ℕ) (n L k : ℕ)
    (hk : k ≤ L) :
    phasePoint (orbitOffsetList a n L) k = seqOffset a n k := by
  unfold phasePoint
  by_cases h0 : k = 0
  · subst h0
    simp [seqOffset]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero h0
    have hkm : k - 1 < L :=
      lt_of_lt_of_le (Nat.sub_lt hkpos (by decide : (0 : ℕ) < 1)) hk
    rw [if_neg h0, orbitOffsetList_getD a n L (k - 1) hkm,
      Nat.sub_add_cancel hkpos]

theorem realGap_orbitOffsetList {a : ℕ → ℕ} (ha : StrictMono a)
    (n L k : ℕ) (hk : k < L) :
    realGap (orbitOffsetList a n L) k = seqGap a (n + k) := by
  unfold realGap
  have hk1 : k + 1 ≤ L := Nat.succ_le_of_lt hk
  have hk0 : k ≤ L := le_of_lt hk
  rw [phasePoint_orbitOffsetList a n L (k + 1) hk1,
    phasePoint_orbitOffsetList a n L k hk0]
  have hnat := seqOffset_succ_sub ha n k
  have hle : seqOffset a n k ≤ seqOffset a n (k + 1) := by
    have h2 : a (n + k) ≤ a (n + k + 1) :=
      (ha.le_iff_le).mpr (Nat.le_succ (n + k))
    unfold seqOffset
    exact Nat.sub_le_sub_right h2 _
  rw [← Nat.cast_sub hle, hnat]

/-! ### Truncated orbit phase of `gapPolySeries` -/

/-- Infinite tail phase of `gapPolySeries` from index `n` (paper `U_P(n)`). -/
noncomputable def gapPolyOrbitPhase (P : ℕ → ℝ[X]) (B n : ℕ) : ℝ :=
  seqGapPolyTail nthPrime P B n

/-- Finite truncation of the orbit phase (paper `Φ_L(n)`). -/
noncomputable def truncatedOrbitPhase (P : ℕ → ℝ[X]) (B L n : ℕ) : ℝ :=
  seqGapPolyTailTrunc nthPrime P B L n

/-- Integer-corrected truncation of the geometric orbit `B^n θ`.
Definitionally `B^n θ` minus the untruncated tail remainder, so
`|B^n θ - truncatedSeqOrbit|` equals the phase tail. -/
noncomputable def truncatedSeqOrbit (a : ℕ → ℕ) (P : ℕ → ℝ[X])
    (B L n : ℕ) : ℝ :=
  (B : ℝ) ^ n * seqGapPolySeries a P B -
    (seqGapPolyTail a P B n - seqGapPolyTailTrunc a P B L n)

/-- Specialisation of `truncatedSeqOrbit` to `gapPolySeries`. -/
noncomputable def truncatedGapPolyOrbit (P : ℕ → ℝ[X]) (B L n : ℕ) : ℝ :=
  truncatedSeqOrbit nthPrime P B L n

/-- Uniform bound on the untruncated tail of the orbit phase. -/
def UniformOrbitTail (P : ℕ → ℝ[X]) (B : ℕ) (L : ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ n, |gapPolyOrbitPhase P B n - truncatedOrbitPhase P B (L n) n| ≤ ε

theorem truncatedOrbitPhase_const_eq_finiteGapPolyPhase
    (P : ℝ[X]) (B L n : ℕ) :
    truncatedOrbitPhase (fun _ => P) B L n =
      finiteGapPolyPhase P B L (orbitOffsetList nthPrime n L) := by
  unfold truncatedOrbitPhase seqGapPolyTailTrunc finiteGapPolyPhase
  refine sum_congr rfl fun k hk => ?_
  have hkL : k < L := mem_range.mp hk
  rw [realGap_orbitOffsetList nthPrime_strictMono n L k hkL]

theorem truncatedOrbitPhase_zero (P : ℕ → ℝ[X]) (B L : ℕ) :
    truncatedOrbitPhase P B L 0 =
      ∑ n ∈ range L,
        eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1) := by
  unfold truncatedOrbitPhase seqGapPolyTailTrunc
  refine sum_congr rfl fun n _ => ?_
  simp only [Nat.zero_add, seqGap_nthPrime]

/-- Finite truncation versus the full series: the remainder is the
shifted tsum. Requires summability so `gapPolySeries` is that tsum. -/
theorem gapPolySeries_eq_trunc_add_tsum {P : ℕ → ℝ[X]} {B L : ℕ}
    (hsm : Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1)) :
    gapPolySeries P B =
      truncatedOrbitPhase P B L 0 +
        ∑' j : ℕ,
          eval (primeGap (L + j) : ℝ) (P (L + j)) /
            (B : ℝ) ^ (L + j + 1) := by
  have hsplit := hsm.sum_add_tsum_nat_add L
  unfold gapPolySeries
  rw [← hsplit, truncatedOrbitPhase_zero]
  congr 1
  exact tsum_congr fun j => by simp [Nat.add_comm L]

theorem truncatedSeqOrbit_sub (a : ℕ → ℕ) (P : ℕ → ℝ[X]) (B L n : ℕ) :
    (B : ℝ) ^ n * seqGapPolySeries a P B - truncatedSeqOrbit a P B L n =
      seqGapPolyTail a P B n - seqGapPolyTailTrunc a P B L n := by
  unfold truncatedSeqOrbit
  ring

theorem truncatedGapPolyOrbit_sub (P : ℕ → ℝ[X]) (B L n : ℕ) :
    (B : ℝ) ^ n * gapPolySeries P B - truncatedGapPolyOrbit P B L n =
      gapPolyOrbitPhase P B n - truncatedOrbitPhase P B L n := by
  unfold truncatedGapPolyOrbit gapPolyOrbitPhase truncatedOrbitPhase
  rw [gapPolySeries_eq_seq]
  exact truncatedSeqOrbit_sub nthPrime P B L n

/-! ### Integer orbit character -/

theorem e_truncatedSeqOrbit {a : ℕ → ℕ} {P : ℕ → ℝ[X]} {B n L : ℕ}
    {τ : ℤ} (hB : 2 ≤ B)
    (hsm : Summable fun k : ℕ =>
      eval (seqGap a k : ℝ) (P k) / (B : ℝ) ^ (k + 1))
    (hint : ∀ k, ∃ z : ℤ, eval (seqGap a k : ℝ) (P k) = z) :
    e ((τ : ℝ) * truncatedSeqOrbit a P B L n) =
      e ((τ : ℝ) * seqGapPolyTailTrunc a P B L n) := by
  obtain ⟨z, hz⟩ := seqGapPolyTail_orbit_int hB hsm hint n
  have hU : truncatedSeqOrbit a P B L n =
      seqGapPolyTailTrunc a P B L n + (z : ℝ) := by
    unfold truncatedSeqOrbit seqGapPolySeries
    have : (B : ℝ) ^ n * seqGapPolyTail a P B 0 =
        seqGapPolyTail a P B n + z := by linarith [hz]
    rw [this]
    ring
  rw [hU, mul_add, e_add]
  have hintτ : e ((τ : ℝ) * z) = 1 := by
    have : (τ : ℝ) * z = ((τ * z : ℤ) : ℝ) := by
      simp [Int.cast_mul]
    rw [this, e_int]
  rw [hintτ, mul_one]

theorem e_truncatedGapPolyOrbit {P : ℕ → ℝ[X]} {B n L : ℕ} {τ : ℤ}
    (hB : 2 ≤ B)
    (hsm : Summable fun k : ℕ =>
      eval (primeGap k : ℝ) (P k) / (B : ℝ) ^ (k + 1))
    (hint : ∀ k, ∃ z : ℤ, eval (primeGap k : ℝ) (P k) = z) :
    e ((τ : ℝ) * truncatedGapPolyOrbit P B L n) =
      e ((τ : ℝ) * truncatedOrbitPhase P B L n) := by
  have hsm' : Summable fun k : ℕ =>
      eval (seqGap nthPrime k : ℝ) (P k) / (B : ℝ) ^ (k + 1) := by
    simpa [seqGap_nthPrime] using hsm
  have hint' : ∀ k, ∃ z : ℤ, eval (seqGap nthPrime k : ℝ) (P k) = z := by
    simpa [seqGap_nthPrime] using hint
  simpa [truncatedGapPolyOrbit, truncatedOrbitPhase] using
    e_truncatedSeqOrbit (a := nthPrime) (n := n) (L := L) (τ := τ)
      hB hsm' hint'

/-! ### Lipschitz truncation of Cesàro means -/

/-- Uniform phase-tail control passes to Cesàro means of `e(τ ·)` by
`cesaroMean_e_trunc`. -/
theorem cesaroMean_e_trunc_orbitPhase (P : ℕ → ℝ[X]) (B : ℕ)
    (L : ℕ → ℕ) (τ : ℤ) {ε : ℝ} (h : UniformOrbitTail P B L ε)
    (N : ℕ) (hN : 0 < N) :
    ‖cesaroMean (fun n => e ((τ : ℝ) * gapPolyOrbitPhase P B n)) N -
        cesaroMean (fun n =>
          e ((τ : ℝ) * truncatedOrbitPhase P B (L n) n)) N‖ ≤
      2 * Real.pi * |(τ : ℝ)| * ε :=
  cesaroMean_e_trunc τ (fun n => gapPolyOrbitPhase P B n)
    (fun n => truncatedOrbitPhase P B (L n) n) h N hN

/-! ### Orbit passage: uniform truncation to `weylCriterion` -/

/-- Sequence form: `TruncatedPhaseWeyl` plus a uniformly small phase
tail imply Weyl normality of the polynomial series, via
`weylCriterion_of_uniform_truncation`. -/
theorem weylCriterion_of_truncatedPhaseWeyl_uniform
    {a : ℕ → ℕ} {P : ℕ → ℝ[X]} {B : ℕ} (hB : 2 ≤ B)
    (hsm : Summable fun n : ℕ =>
      eval (seqGap a n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hint : ∀ n, ∃ z : ℤ, eval (seqGap a n : ℝ) (P n) = z)
    (hpack : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ → ℕ,
      TruncatedPhaseWeyl a P B L ∧
        ∀ n, |seqGapPolyTail a P B n -
          seqGapPolyTailTrunc a P B (L n) n| ≤ ε) :
    weylCriterion B (seqGapPolySeries a P B) := by
  refine weylCriterion_of_uniform_truncation ?_
  intro τ hτ ε hε
  obtain ⟨L, hΦ, hrem⟩ := hpack ε hε
  refine ⟨fun n => truncatedSeqOrbit a P B (L n) n, ?_, ?_⟩
  · intro n
    have hsub := truncatedSeqOrbit_sub a P B (L n) n
    have :
        |((B : ℝ) ^ n * seqGapPolySeries a P B) -
            truncatedSeqOrbit a P B (L n) n| =
          |seqGapPolyTail a P B n -
            seqGapPolyTailTrunc a P B (L n) n| := by
      rw [hsub]
    rw [this]
    exact hrem n
  · have heq : ∀ n,
        e ((τ : ℝ) * truncatedSeqOrbit a P B (L n) n) =
          e ((τ : ℝ) * seqGapPolyTailTrunc a P B (L n) n) :=
      fun n => e_truncatedSeqOrbit hB hsm hint
    have hfun :
        (fun N : ℕ =>
          cesaroMean (fun n =>
            e ((τ : ℝ) * truncatedSeqOrbit a P B (L n) n)) N) =
          fun N =>
            (∑ n ∈ range N,
              e ((τ : ℝ) * seqGapPolyTailTrunc a P B (L n) n)) / N := by
      funext N
      unfold cesaroMean
      congr 1
      refine sum_congr rfl fun n _ => heq n
    rw [hfun]
    exact hΦ τ hτ

/-- If `TruncatedPhaseWeyl` holds for some truncation whose untruncated
tail is uniformly small, then `gapPolySeries` is Weyl-normal to base
`B`. No Kuperberg input. -/
theorem weylCriterion_gapPolySeries_of_truncatedPhaseWeyl_uniform
    {P : ℕ → ℝ[X]} {B : ℕ} (hB : 2 ≤ B)
    (hsm : Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hint : ∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z)
    (hpack : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ → ℕ,
      TruncatedPhaseWeyl nthPrime P B L ∧ UniformOrbitTail P B L ε) :
    weylCriterion B (gapPolySeries P B) := by
  have hsm' : Summable fun n : ℕ =>
      eval (seqGap nthPrime n : ℝ) (P n) / (B : ℝ) ^ (n + 1) := by
    simpa [seqGap_nthPrime] using hsm
  have hint' : ∀ n, ∃ z : ℤ, eval (seqGap nthPrime n : ℝ) (P n) = z := by
    simpa [seqGap_nthPrime] using hint
  have hpack' : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ → ℕ,
      TruncatedPhaseWeyl nthPrime P B L ∧
        ∀ n, |seqGapPolyTail nthPrime P B n -
          seqGapPolyTailTrunc nthPrime P B (L n) n| ≤ ε := by
    intro ε hε
    obtain ⟨L, hΦ, hrem⟩ := hpack ε hε
    refine ⟨L, hΦ, fun n => ?_⟩
    simpa [UniformOrbitTail, gapPolyOrbitPhase, truncatedOrbitPhase] using hrem n
  have h := weylCriterion_of_truncatedPhaseWeyl_uniform hB hsm' hint' hpack'
  rwa [gapPolySeries_eq_seq]

/-- Constant family: summability from `GapPolySummable`. -/
theorem weylCriterion_gapPolySeries_const_of_truncatedPhaseWeyl_uniform
    (P : ℝ[X]) {B : ℕ} (hB : 2 ≤ B)
    (hint : ∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) P = z)
    (hpack : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ → ℕ,
      TruncatedPhaseWeyl nthPrime (fun _ => P) B L ∧
        UniformOrbitTail (fun _ => P) B L ε) :
    weylCriterion B (gapPolySeries (fun _ => P) B) :=
  weylCriterion_gapPolySeries_of_truncatedPhaseWeyl_uniform hB
    (gapPolySeries_const_summable P hB) hint hpack

/-- Periodic family: summability from `GapPolySummable`. -/
theorem weylCriterion_gapPolySeries_periodic_of_truncatedPhaseWeyl_uniform
    {P : ℕ → ℝ[X]} {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (hP : Periodic P k)
    (hint : ∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z)
    (hpack : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ → ℕ,
      TruncatedPhaseWeyl nthPrime P B L ∧ UniformOrbitTail P B L ε) :
    weylCriterion B (gapPolySeries P B) :=
  weylCriterion_gapPolySeries_of_truncatedPhaseWeyl_uniform hB
    (gapPolySeries_periodic_summable hB hk hP) hint hpack

end PrimeGapNormality.Prime
