import PrimeGapNormality.Prime.Fourier
import PrimeGapNormality.Prime.GapPolySummable
import PrimeGapNormality.Prime.Independence
import PrimeGapNormality.Prime.PeriodicAbel
import PrimeGapNormality.Prime.PrimeSeries
import PrimeGapNormality.Prime.ProgressionLift
import PrimeGapNormality.Prime.StatisticalCriterion
import PrimeGapNormality.Prime.TruncatedWeylPack
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic

/-!
# Consumer pack: first-L cut transfer + model vanishing → Weyl

Assembles the remaining forum-theorem consumer chain. Every unproved
analytic step is a named `Prop` (not an axiom) and is used.

* `ModelTruncatedPhaseVanishing`: mixture of rooted-sieve means of the
  span-cut truncated phase → 0. Slot bounds live in `ModelPhaseMean`;
  they are not discharged here.
* `TruncatedPhaseCutTransfer` is the first-`L` fragment of (eq:S):
  window averages of `truncatedPhaseTestRankCut` (constant family:
  `truncatedPhaseTestCut`) versus the mixture. This is what
  `PrimeShortS` actually proves, for `nthPrime` and `windowG`, under
  named remainders. It is strictly weaker than `ShortPatternS`, which
  quantifies over tests that may read offsets `k > L`.
* `TruncatedPhaseSpanCutVanishing` compares the cut to `e(τ Φ_L)`.
* `TruncatedPhaseRankShiftVanishing` compares rank-indexed coefficients
  `P j` (the offset-only test) to the shifted family `P (n+j)`.
  Discharged when `P` is constant.
* `TruncatedPhaseWindowIndexMatch` compares the physical truncation
  `L_X` to the index profile `L(n) = L_{a_n}`. Named because the
  window-to-Cesàro lift cannot identify them from `Finset`/`Filter` alone.
* `IndexPassageD` converts `I_{a_M}` to dyadic index blocks
  `Ioc M (2M)`; `ProgressionLift.tendsto_cesaro_of_dyadicBlocks` then
  yields `TruncatedPhaseWeyl`.
* `TruncatedWeylPack` plus `UniformOrbitTail` and integer evaluations
  give `weylCriterion B (gapPolySeries P B)`.
* Affine Abel records that a rational correction upgrades gap-poly Weyl
  to a weighted position series. This module does **not** claim
  `weylCriterion B (primePosSeries B)` without that Weyl hypothesis,
  and does **not** claim `KuperbergConj13 → weylCriterion`.

Source: `StatisticalCriterion` (eq:S)/(eq:D); `PrimeShortS`
(`windowAvg_truncatedPhaseTestCut_close_to_mixture`, first-`L`);
`TruncatedWeylPack`; `ProgressionLift.tendsto_cesaro_of_dyadicBlocks`;
`PeriodicAbel.gapPolySeries_affine_eq_abel`.
Contract: API
Audit: GREEN
-/

open Finset Filter Polynomial
open Function (Periodic)
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000

/-! ### Circle character -/

private theorem two_pi_I_mul (x : ℝ) :
    (2 * Real.pi * Complex.I * (x : ℂ) : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) := by
  simp [mul_comm, mul_left_comm, Complex.ofReal_mul]

private theorem pack_norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [two_pi_I_mul, Complex.norm_exp_I_mul_ofReal]

/-! ### Rank-indexed truncated phase tests (offset-only, matching S) -/

/-- Truncated phase as a function of rooted offsets, with coefficients
`P j` on the `j`-th gap from the root. Reads only `v 0,…,v L`, so it
is a first-`L` test in the sense of `PrimeShortS.DependsOnFirstL`. -/
noncomputable def truncatedPhaseTestRank (P : ℕ → ℝ[X]) (B L : ℕ)
    (τ : ℤ) (v : ℕ → ℕ) : ℂ :=
  e ((τ : ℝ) *
    ∑ j ∈ range L,
      eval ((v (j + 1) - v j : ℕ) : ℝ) (P j) / (B : ℝ) ^ (j + 1))

/-- Span cut matching (eq:S). -/
noncomputable def truncatedPhaseTestRankCut (P : ℕ → ℝ[X]) (B L : ℕ)
    (S : ℝ) (τ : ℤ) (v : ℕ → ℕ) : ℂ :=
  if S < v L then 0 else truncatedPhaseTestRank P B L τ v

/-- Rank-indexed truncation: `P j` on `g_{n+j}`, not `P (n+j)`. -/
noncomputable def seqGapPolyTailTruncRank (a : ℕ → ℕ) (P : ℕ → ℝ[X])
    (B L n : ℕ) : ℝ :=
  ∑ j ∈ range L,
    eval (seqGap a (n + j) : ℝ) (P j) / (B : ℝ) ^ (j + 1)

/-- Index-side profile `L(n) = L_{a_n}`, matching paper `L_X` along `a`. -/
noncomputable def indexProfileL (ρ : ℝ) (G : ℕ → ℝ) (a : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  stdProfileL ρ (G (a n))

theorem truncatedPhaseTestRank_const (P : ℝ[X]) (B L : ℕ) (τ : ℤ)
    (v : ℕ → ℕ) :
    truncatedPhaseTestRank (fun _ => P) B L τ v =
      truncatedPhaseTest P B L τ v :=
  rfl

theorem truncatedPhaseTestRankCut_const (P : ℝ[X]) (B L : ℕ) (S : ℝ)
    (τ : ℤ) (v : ℕ → ℕ) :
    truncatedPhaseTestRankCut (fun _ => P) B L S τ v =
      truncatedPhaseTestCut P B L S τ v :=
  rfl

theorem truncatedPhaseTestRank_norm (P : ℕ → ℝ[X]) (B L : ℕ) (τ : ℤ)
    (v : ℕ → ℕ) : ‖truncatedPhaseTestRank P B L τ v‖ ≤ 1 := by
  simpa [truncatedPhaseTestRank] using (pack_norm_e _).le

theorem truncatedPhaseTestRankCut_norm (P : ℕ → ℝ[X]) (B L : ℕ) (S : ℝ)
    (τ : ℤ) (v : ℕ → ℕ) : ‖truncatedPhaseTestRankCut P B L S τ v‖ ≤ 1 := by
  unfold truncatedPhaseTestRankCut
  split_ifs
  · simp
  · exact truncatedPhaseTestRank_norm P B L τ v

theorem truncatedPhaseTestRankCut_span (P : ℕ → ℝ[X]) (B L : ℕ) (S : ℝ)
    (τ : ℤ) (v : ℕ → ℕ) (hv : S < v L) :
    truncatedPhaseTestRankCut P B L S τ v = 0 := by
  simp [truncatedPhaseTestRankCut, hv]

theorem truncatedPhaseTestRank_eq {a : ℕ → ℕ} (ha : StrictMono a)
    (P : ℕ → ℝ[X]) (B L n : ℕ) (τ : ℤ) :
    truncatedPhaseTestRank P B L τ (fun k => seqOffset a n k) =
      e ((τ : ℝ) * seqGapPolyTailTruncRank a P B L n) := by
  unfold truncatedPhaseTestRank seqGapPolyTailTruncRank
  have hsum :
      ∑ j ∈ range L,
          eval ((seqOffset a n (j + 1) - seqOffset a n j : ℕ) : ℝ)
            (P j) / (B : ℝ) ^ (j + 1) =
        ∑ j ∈ range L,
          eval (seqGap a (n + j) : ℝ) (P j) / (B : ℝ) ^ (j + 1) := by
    refine sum_congr rfl fun j _ => ?_
    rw [seqOffset_succ_sub ha]
  rw [hsum]

theorem truncatedPhaseTestRank_prefix (P : ℕ → ℝ[X]) (B L : ℕ)
    (τ : ℤ) {v w : ℕ → ℕ} (h : ∀ k, k ≤ L → v k = w k) :
    truncatedPhaseTestRank P B L τ v = truncatedPhaseTestRank P B L τ w := by
  unfold truncatedPhaseTestRank
  have hsum :
      ∑ j ∈ range L,
          eval ((v (j + 1) - v j : ℕ) : ℝ) (P j) / (B : ℝ) ^ (j + 1) =
        ∑ j ∈ range L,
          eval ((w (j + 1) - w j : ℕ) : ℝ) (P j) / (B : ℝ) ^ (j + 1) := by
    refine sum_congr rfl fun j hj => ?_
    have hjL : j < L := mem_range.mp hj
    have hj1 : j + 1 ≤ L := Nat.succ_le_of_lt hjL
    rw [h j (Nat.le_of_lt hjL), h (j + 1) hj1]
  rw [hsum]

theorem truncatedPhaseTestRankCut_prefix (P : ℕ → ℝ[X]) (B L : ℕ)
    (S : ℝ) (τ : ℤ) {v w : ℕ → ℕ} (h : ∀ k, k ≤ L → v k = w k) :
    truncatedPhaseTestRankCut P B L S τ v =
      truncatedPhaseTestRankCut P B L S τ w := by
  unfold truncatedPhaseTestRankCut
  have hL : v L = w L := h L le_rfl
  split_ifs with hv hw
  · rfl
  · exact (hw (by rwa [← hL])).elim
  · exact (hv (by rwa [hL])).elim
  · exact truncatedPhaseTestRank_prefix P B L τ h

theorem seqGapPolyTailTruncRank_const (a : ℕ → ℕ) (P : ℝ[X])
    (B L n : ℕ) :
    seqGapPolyTailTruncRank a (fun _ => P) B L n =
      seqGapPolyTailTrunc a (fun _ => P) B L n :=
  rfl

/-! ### Named analytic Props (not axioms) -/

/-- Mixture of rooted-sieve means of the span-cut truncated phase
tends to `0`. This is the missing model cancellation of `e(τ Φ_L)`
in first-`L` form. -/
def ModelTruncatedPhaseVanishing (P : ℕ → ℝ[X]) (B : ℕ) (ρ : ℝ)
    (G : ℕ → ℝ) (ω : ℕ → SieveMixture) : Prop :=
  ∀ τ : ℤ, τ ≠ 0 →
    Tendsto (fun X : ℕ =>
      mixtureMean (ω X) (fun y =>
        rootedSieveMean y
          (truncatedPhaseTestRankCut P B
            (stdProfileL ρ (G X)) (stdProfileS ρ (G X)) τ)))
      atTop (𝓝 0)

/-- First-`L` fragment of (eq:S): the span-cut truncated phase
(constant family: `truncatedPhaseTestCut`) has window averages close
to a calibrated mixture of rooted-sieve means. Weaker than
`ShortPatternS`, which also demands tests that read `k > L`.
Matches `PrimeShortS.windowAvg_truncatedPhaseTestCut_close_to_mixture`
on `nthPrime` / `windowG` for constant `P`. -/
def TruncatedPhaseCutTransfer (a : ℕ → ℕ) (P : ℕ → ℝ[X]) (B : ℕ)
    (ρ : ℝ) (G : ℕ → ℝ) : Prop :=
  ∃ ω : ℕ → SieveMixture,
    Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
        ∀ τ : ℤ,
          ‖windowAvg (seqWindow a X) (fun n =>
              truncatedPhaseTestRankCut P B (stdProfileL ρ (G X))
                (stdProfileS ρ (G X)) τ (fun k => seqOffset a n k)) -
            mixtureMean (ω X) (fun y =>
              rootedSieveMean y
                (truncatedPhaseTestRankCut P B
                  (stdProfileL ρ (G X)) (stdProfileS ρ (G X)) τ))‖ < ε

/-- Window average of (cut test − uncut rank test) vanishes. Compares
the first-`L` cut to `e(τ Φ_L^{rank})`. -/
def TruncatedPhaseSpanCutVanishing (a : ℕ → ℕ) (P : ℕ → ℝ[X]) (B : ℕ)
    (ρ : ℝ) (G : ℕ → ℝ) : Prop :=
  ∀ τ : ℤ, τ ≠ 0 →
    Tendsto (fun X : ℕ =>
      windowAvg (seqWindow a X) (fun n =>
        truncatedPhaseTestRankCut P B (stdProfileL ρ (G X))
            (stdProfileS ρ (G X)) τ (fun k => seqOffset a n k) -
          truncatedPhaseTestRank P B (stdProfileL ρ (G X)) τ
            (fun k => seqOffset a n k)))
      atTop (𝓝 0)

/-- Window average of `e(τ Φ_L^{rank}) - e(τ Φ_L)` vanishes. Rank
coefficients `P j` versus the shifted family `P (n+j)`. -/
def TruncatedPhaseRankShiftVanishing (a : ℕ → ℕ) (P : ℕ → ℝ[X]) (B : ℕ)
    (ρ : ℝ) (G : ℕ → ℝ) : Prop :=
  ∀ τ : ℤ, τ ≠ 0 →
    Tendsto (fun X : ℕ =>
      windowAvg (seqWindow a X) (fun n =>
        e ((τ : ℝ) * seqGapPolyTailTruncRank a P B
            (stdProfileL ρ (G X)) n) -
          e ((τ : ℝ) * seqGapPolyTailTrunc a P B
            (stdProfileL ρ (G X)) n)))
      atTop (𝓝 0)

/-- Physical truncation `stdProfileL ρ (G X)` versus the index profile
`stdProfileL ρ (G (a n))` on the window `I_X`. Missing slow-variation
lemma: not a `Finset`/`Filter` identity. -/
def TruncatedPhaseWindowIndexMatch (a : ℕ → ℕ) (P : ℕ → ℝ[X]) (B : ℕ)
    (ρ : ℝ) (G : ℕ → ℝ) : Prop :=
  ∀ τ : ℤ, τ ≠ 0 →
    Tendsto (fun X : ℕ =>
      windowAvg (seqWindow a X) (fun n =>
        e ((τ : ℝ) * seqGapPolyTailTrunc a P B
            (stdProfileL ρ (G X)) n) -
          e ((τ : ℝ) * seqGapPolyTailTrunc a P B
            (indexProfileL ρ G a n) n)))
      atTop (𝓝 0)

/-- Rational Abel correction: weighted position series equals the affine
gap-poly series plus a rational. Motivated by
`PeriodicAbel.gapPolySeries_affine_eq_abel`. -/
def AffineGapAbelCorrectionRat (P : ℕ → ℝ[X]) (B k : ℕ) : Prop :=
  ∃ q : ℚ,
    primePosWeightedSeries
        (fun n => recGapWeight B (affinePeriodicGapWeight P k) (n - 1)) B =
      gapPolySeries P B + (q : ℝ)

/-- Rational Abel correction for the unweighted position series
`∑ p_n B^{-(n+1)}`. -/
def PrimePosAbelCorrectionRat (P : ℕ → ℝ[X]) (B : ℕ) : Prop :=
  ∃ q : ℚ, primePosSeries B = gapPolySeries P B + (q : ℝ)

/-! ### Window averages -/

theorem windowAvg_add (s : Finset ℕ) (f g : ℕ → ℂ) :
    windowAvg s (fun n => f n + g n) = windowAvg s f + windowAvg s g := by
  unfold windowAvg
  rw [sum_add_distrib, add_div]

theorem windowAvg_sub (s : Finset ℕ) (f g : ℕ → ℂ) :
    windowAvg s (fun n => f n - g n) = windowAvg s f - windowAvg s g := by
  unfold windowAvg
  rw [sum_sub_distrib, sub_div]

theorem windowAvg_zero (s : Finset ℕ) :
    windowAvg s (fun _ => (0 : ℂ)) = 0 := by
  unfold windowAvg
  simp

theorem windowAvg_congr (s : Finset ℕ) {f g : ℕ → ℂ}
    (h : ∀ n ∈ s, f n = g n) : windowAvg s f = windowAvg s g := by
  unfold windowAvg
  congr 1
  exact sum_congr rfl h

private theorem tendsto_strictMono_atTop {a : ℕ → ℕ} (ha : StrictMono a) :
    Tendsto a atTop atTop :=
  Filter.tendsto_atTop_atTop.mpr fun t =>
    ⟨t, fun n hn => le_trans hn (strictMono_le_id ha n)⟩

/-! ### Rank shift for constant families -/

theorem truncatedPhaseRankShiftVanishing_const (a : ℕ → ℕ) (P : ℝ[X])
    (B : ℕ) (ρ : ℝ) (G : ℕ → ℝ) :
    TruncatedPhaseRankShiftVanishing a (fun _ => P) B ρ G := by
  intro τ _hτ
  have heq :
      (fun X : ℕ =>
        windowAvg (seqWindow a X) (fun n =>
          e ((τ : ℝ) * seqGapPolyTailTruncRank a (fun _ => P) B
              (stdProfileL ρ (G X)) n) -
            e ((τ : ℝ) * seqGapPolyTailTrunc a (fun _ => P) B
              (stdProfileL ρ (G X)) n))) =
        fun _ => (0 : ℂ) := by
    funext X
    rw [windowAvg_congr (seqWindow a X)
      (f := fun n =>
        e ((τ : ℝ) * seqGapPolyTailTruncRank a (fun _ => P) B
            (stdProfileL ρ (G X)) n) -
          e ((τ : ℝ) * seqGapPolyTailTrunc a (fun _ => P) B
            (stdProfileL ρ (G X)) n))
      (g := fun _ => (0 : ℂ))
      (fun n _ => by rw [seqGapPolyTailTruncRank_const, sub_self])]
    exact windowAvg_zero _
  simpa [heq] using tendsto_const_nhds (x := (0 : ℂ))

theorem truncatedPhaseRankShiftVanishing_of_eq {a : ℕ → ℕ}
    {P : ℕ → ℝ[X]} (hP : ∀ n, P n = P 0) (B : ℕ) (ρ : ℝ) (G : ℕ → ℝ) :
    TruncatedPhaseRankShiftVanishing a P B ρ G := by
  intro τ hτ
  have hfun :
      (fun X : ℕ =>
        windowAvg (seqWindow a X) (fun n =>
          e ((τ : ℝ) * seqGapPolyTailTruncRank a P B
              (stdProfileL ρ (G X)) n) -
            e ((τ : ℝ) * seqGapPolyTailTrunc a P B
              (stdProfileL ρ (G X)) n))) =
        fun X =>
          windowAvg (seqWindow a X) (fun n =>
            e ((τ : ℝ) * seqGapPolyTailTruncRank a (fun _ => P 0) B
                (stdProfileL ρ (G X)) n) -
              e ((τ : ℝ) * seqGapPolyTailTrunc a (fun _ => P 0) B
                (stdProfileL ρ (G X)) n)) := by
    funext X
    refine windowAvg_congr _ fun n _ => ?_
    have hrank :
        seqGapPolyTailTruncRank a P B (stdProfileL ρ (G X)) n =
          seqGapPolyTailTruncRank a (fun _ => P 0) B
            (stdProfileL ρ (G X)) n := by
      unfold seqGapPolyTailTruncRank
      refine sum_congr rfl fun j _ => ?_
      rw [hP j]
    have htrue :
        seqGapPolyTailTrunc a P B (stdProfileL ρ (G X)) n =
          seqGapPolyTailTrunc a (fun _ => P 0) B
            (stdProfileL ρ (G X)) n := by
      unfold seqGapPolyTailTrunc
      refine sum_congr rfl fun j _ => ?_
      rw [hP (n + j)]
    rw [hrank, htrue]
  rw [hfun]
  exact truncatedPhaseRankShiftVanishing_const a (P 0) B ρ G τ hτ

/-! ### First-L cut transfer + model vanishing ⇒ window Weyl -/

/-- Full `ShortPatternS` implies the first-`L` cut transfer. Recorded
so a stronger S-hypothesis still specialises; the consumer does not
require it. -/
theorem truncatedPhaseCutTransfer_of_shortPatternS {a : ℕ → ℕ}
    {P : ℕ → ℝ[X]} {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hS : ShortPatternS a ρ G) :
    TruncatedPhaseCutTransfer a P B ρ G := by
  rcases hS.2.2 with ⟨ω, hcal, htrans⟩
  refine ⟨ω, hcal, fun ε hε => ?_⟩
  obtain ⟨X0, hX0⟩ := htrans ε hε
  refine ⟨X0, fun X hX τ => ?_⟩
  exact hX0 X hX _
    (truncatedPhaseTestRankCut_norm P B (stdProfileL ρ (G X))
      (stdProfileS ρ (G X)) τ)
    (truncatedPhaseTestRankCut_span P B (stdProfileL ρ (G X))
      (stdProfileS ρ (G X)) τ)

theorem tendsto_windowAvg_cut_of_cutTransfer {a : ℕ → ℕ}
    {P : ℕ → ℝ[X]} {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hS : TruncatedPhaseCutTransfer a P B ρ G)
    (hmodel : ∀ ω : ℕ → SieveMixture,
      Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) →
        ModelTruncatedPhaseVanishing P B ρ G ω)
    {τ : ℤ} (hτ : τ ≠ 0) :
    Tendsto (fun X : ℕ =>
      windowAvg (seqWindow a X) (fun n =>
        truncatedPhaseTestRankCut P B (stdProfileL ρ (G X))
          (stdProfileS ρ (G X)) τ (fun k => seqOffset a n k)))
      atTop (𝓝 0) := by
  rcases hS with ⟨ω, hcal, htrans⟩
  have hmix : ModelTruncatedPhaseVanishing P B ρ G ω := hmodel ω hcal
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  obtain ⟨X0, hX0⟩ := htrans (ε / 2) hε2
  have hmixEv := (hmix τ hτ).eventually (Metric.ball_mem_nhds (0 : ℂ) hε2)
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp hmixEv
  filter_upwards [eventually_ge_atTop (max X0 X1)] with X hX
  have hX0' : X0 ≤ X := le_trans (le_max_left X0 X1) hX
  have hX1' : X1 ≤ X := le_trans (le_max_right X0 X1) hX
  let F : (ℕ → ℕ) → ℂ :=
    truncatedPhaseTestRankCut P B (stdProfileL ρ (G X))
      (stdProfileS ρ (G X)) τ
  have hclose := hX0 X hX0' τ
  have hmixX : dist (mixtureMean (ω X) (fun y => rootedSieveMean y F)) 0 <
      ε / 2 := hX1 X hX1'
  have htri :=
    norm_add_le
      (windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k)) -
        mixtureMean (ω X) (fun y => rootedSieveMean y F))
      (mixtureMean (ω X) (fun y => rootedSieveMean y F))
  have hrew :
      windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k)) -
            mixtureMean (ω X) (fun y => rootedSieveMean y F) +
          mixtureMean (ω X) (fun y => rootedSieveMean y F) =
        windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k)) :=
    sub_add_cancel _ _
  rw [hrew] at htri
  have hsum : ‖windowAvg (seqWindow a X)
        (fun n => F (fun k => seqOffset a n k))‖ < ε := by
    have h1 : ‖windowAvg (seqWindow a X)
          (fun n => F (fun k => seqOffset a n k)) -
        mixtureMean (ω X) (fun y => rootedSieveMean y F)‖ < ε / 2 := hclose
    have h2 : ‖mixtureMean (ω X) (fun y => rootedSieveMean y F)‖ < ε / 2 := by
      simpa [dist_eq_norm] using hmixX
    have h12 := add_lt_add h1 h2
    have hεsplit : ε / 2 + ε / 2 = ε := add_halves ε
    rw [hεsplit] at h12
    exact lt_of_le_of_lt htri h12
  simpa [dist_eq_norm, F] using hsum

/-- First-`L` cut transfer plus model vanishing of the truncated
phase, the span-cut comparison, and the rank/shift comparison imply
window truncated-phase Weyl. -/
theorem truncatedPhaseWindowWeyl_of_cutTransfer_model {a : ℕ → ℕ}
    (ha : StrictMono a) {P : ℕ → ℝ[X]} {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hS : TruncatedPhaseCutTransfer a P B ρ G)
    (hmodel : ∀ ω : ℕ → SieveMixture,
      Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) →
        ModelTruncatedPhaseVanishing P B ρ G ω)
    (hcut : TruncatedPhaseSpanCutVanishing a P B ρ G)
    (hshift : TruncatedPhaseRankShiftVanishing a P B ρ G) :
    TruncatedPhaseWindowWeyl a P B ρ G := by
  intro τ hτ
  have hcutWin := tendsto_windowAvg_cut_of_cutTransfer hS hmodel hτ
  have hcutτ := hcut τ hτ
  have hshiftτ := hshift τ hτ
  have hrankEq :
      (fun X : ℕ =>
        windowAvg (seqWindow a X) (fun n =>
          truncatedPhaseTestRank P B (stdProfileL ρ (G X)) τ
            (fun k => seqOffset a n k))) =
        fun X =>
          windowAvg (seqWindow a X) (fun n =>
            e ((τ : ℝ) * seqGapPolyTailTruncRank a P B
              (stdProfileL ρ (G X)) n)) := by
    funext X
    exact windowAvg_congr _ fun n _ =>
      truncatedPhaseTestRank_eq ha P B (stdProfileL ρ (G X)) n τ
  have hrank : Tendsto (fun X : ℕ =>
      windowAvg (seqWindow a X) (fun n =>
        truncatedPhaseTestRank P B (stdProfileL ρ (G X)) τ
          (fun k => seqOffset a n k))) atTop (𝓝 0) := by
    have heq :
        (fun X : ℕ =>
          windowAvg (seqWindow a X) (fun n =>
            truncatedPhaseTestRankCut P B (stdProfileL ρ (G X))
                (stdProfileS ρ (G X)) τ (fun k => seqOffset a n k) -
              truncatedPhaseTestRank P B (stdProfileL ρ (G X)) τ
                (fun k => seqOffset a n k))) =
          fun X =>
            windowAvg (seqWindow a X) (fun n =>
              truncatedPhaseTestRankCut P B (stdProfileL ρ (G X))
                (stdProfileS ρ (G X)) τ (fun k => seqOffset a n k)) -
              windowAvg (seqWindow a X) (fun n =>
                truncatedPhaseTestRank P B (stdProfileL ρ (G X)) τ
                  (fun k => seqOffset a n k)) := by
      funext X
      exact windowAvg_sub _ _ _
    have hdiff : Tendsto (fun X : ℕ =>
        windowAvg (seqWindow a X) (fun n =>
          truncatedPhaseTestRankCut P B (stdProfileL ρ (G X))
              (stdProfileS ρ (G X)) τ (fun k => seqOffset a n k)) -
          windowAvg (seqWindow a X) (fun n =>
            truncatedPhaseTestRank P B (stdProfileL ρ (G X)) τ
              (fun k => seqOffset a n k))) atTop (𝓝 0) := by
      rwa [← heq]
    have hcomb := hcutWin.sub hdiff
    simpa [sub_sub_cancel] using hcomb
  have hrankE : Tendsto (fun X : ℕ =>
      windowAvg (seqWindow a X) (fun n =>
        e ((τ : ℝ) * seqGapPolyTailTruncRank a P B
          (stdProfileL ρ (G X)) n))) atTop (𝓝 0) := by
    rwa [hrankEq] at hrank
  have heqShift :
      (fun X : ℕ =>
        windowAvg (seqWindow a X) (fun n =>
          e ((τ : ℝ) * seqGapPolyTailTruncRank a P B
              (stdProfileL ρ (G X)) n) -
            e ((τ : ℝ) * seqGapPolyTailTrunc a P B
              (stdProfileL ρ (G X)) n))) =
        fun X =>
          windowAvg (seqWindow a X) (fun n =>
            e ((τ : ℝ) * seqGapPolyTailTruncRank a P B
              (stdProfileL ρ (G X)) n)) -
            windowAvg (seqWindow a X) (fun n =>
              e ((τ : ℝ) * seqGapPolyTailTrunc a P B
                (stdProfileL ρ (G X)) n)) := by
    funext X
    exact windowAvg_sub _ _ _
  have hdiff := hshiftτ
  rw [heqShift] at hdiff
  have hcomb := hrankE.sub hdiff
  simpa [sub_sub_cancel] using hcomb

/-- Constant family: the rank/shift comparison is an identity. -/
theorem truncatedPhaseWindowWeyl_const_of_cutTransfer_model {a : ℕ → ℕ}
    (ha : StrictMono a) (P : ℝ[X]) {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hS : TruncatedPhaseCutTransfer a (fun _ => P) B ρ G)
    (hmodel : ∀ ω : ℕ → SieveMixture,
      Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) →
        ModelTruncatedPhaseVanishing (fun _ => P) B ρ G ω)
    (hcut : TruncatedPhaseSpanCutVanishing a (fun _ => P) B ρ G) :
    TruncatedPhaseWindowWeyl a (fun _ => P) B ρ G :=
  truncatedPhaseWindowWeyl_of_cutTransfer_model ha hS hmodel hcut
    (truncatedPhaseRankShiftVanishing_const a P B ρ G)

theorem truncatedPhaseWindowWeyl_nthPrime_of_cutTransfer_model
    {P : ℕ → ℝ[X]} {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hS : TruncatedPhaseCutTransfer nthPrime P B ρ G)
    (hmodel : ∀ ω : ℕ → SieveMixture,
      Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) →
        ModelTruncatedPhaseVanishing P B ρ G ω)
    (hcut : TruncatedPhaseSpanCutVanishing nthPrime P B ρ G)
    (hshift : TruncatedPhaseRankShiftVanishing nthPrime P B ρ G) :
    TruncatedPhaseWindowWeyl nthPrime P B ρ G :=
  truncatedPhaseWindowWeyl_of_cutTransfer_model nthPrime_strictMono hS
    hmodel hcut hshift

/-! ### Window + D ⇒ Cesàro (`TruncatedPhaseWeyl`) -/

private theorem Ioc_subset_Ioc_of_le {M A B : ℕ} (h : A ≤ B) :
    Ioc M A ⊆ Ioc M B :=
  Ioc_subset_Ioc_right h

private theorem card_Ioc_sdiff_le (M A B : ℕ) :
    ((Ioc M A \ Ioc M B).card : ℝ) ≤ |((A : ℝ) - (B : ℝ))| := by
  rcases le_total A B with hAB | hBA
  · have hsub : Ioc M A ⊆ Ioc M B := Ioc_subset_Ioc_of_le hAB
    have hempty : Ioc M A \ Ioc M B = ∅ :=
      sdiff_eq_empty_iff_subset.mpr hsub
    rw [hempty, card_empty, Nat.cast_zero]
    exact abs_nonneg _
  · have hsub : Ioc M B ⊆ Ioc M A := Ioc_subset_Ioc_of_le hBA
    have hsdiff : Ioc M A \ Ioc M B ⊆ Ioc B A := by
      intro x hx
      have hxA := mem_Ioc.mp (mem_sdiff.mp hx).1
      have hxB : x ∉ Ioc M B := (mem_sdiff.mp hx).2
      rw [mem_Ioc] at hxB
      have hxgtB : B < x := by
        have : ¬ x ≤ B := fun hle => hxB ⟨hxA.1, hle⟩
        exact not_le.mp this
      exact mem_Ioc.mpr ⟨hxgtB, hxA.2⟩
    have hcard : (Ioc M A \ Ioc M B).card ≤ (Ioc B A).card :=
      card_le_card hsdiff
    have hIocCard : (Ioc B A).card = A - B := Nat.card_Ioc B A
    have hcast : ((Ioc M A \ Ioc M B).card : ℝ) ≤ ((A - B : ℕ) : ℝ) := by
      rw [hIocCard] at hcard
      exact Nat.cast_le.mpr hcard
    have hsubR : ((A - B : ℕ) : ℝ) = (A : ℝ) - (B : ℝ) :=
      Nat.cast_sub hBA
    have habs : |((A : ℝ) - (B : ℝ))| = (A : ℝ) - (B : ℝ) :=
      abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hBA))
    rw [hsubR] at hcast
    rwa [habs]

private theorem sum_sub_sum_eq_sdiff (s t : Finset ℕ) (g : ℕ → ℂ) :
    ∑ n ∈ s, g n - ∑ n ∈ t, g n =
      ∑ n ∈ s \ t, g n - ∑ n ∈ t \ s, g n := by
  have hs : ∑ n ∈ s, g n = ∑ n ∈ s \ t, g n + ∑ n ∈ s ∩ t, g n := by
    have hunion : (s \ t) ∪ (s ∩ t) = s := sdiff_union_inter s t
    have hdisj : Disjoint (s \ t) (s ∩ t) := disjoint_sdiff_inter s t
    rw [← sum_union hdisj, hunion]
  have ht : ∑ n ∈ t, g n = ∑ n ∈ t \ s, g n + ∑ n ∈ t ∩ s, g n := by
    have hunion : (t \ s) ∪ (t ∩ s) = t := sdiff_union_inter t s
    have hdisj : Disjoint (t \ s) (t ∩ s) := disjoint_sdiff_inter t s
    rw [← sum_union hdisj, hunion]
  have hinter : s ∩ t = t ∩ s := inter_comm _ _
  rw [hs, ht, hinter]
  abel

private theorem norm_sum_unimodular_card (s : Finset ℕ) (g : ℕ → ℂ)
    (hg : ∀ n, ‖g n‖ ≤ 1) : ‖∑ n ∈ s, g n‖ ≤ (s.card : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ n ∈ s, ‖g n‖ ≤ ∑ n ∈ s, (1 : ℝ) :=
    sum_le_sum fun _ _ => hg _
  have hc : (∑ n ∈ s, (1 : ℝ)) = (s.card : ℝ) := by
    rw [sum_const, nsmul_eq_mul, mul_one]
  exact h1.trans_eq hc

private theorem norm_sum_Ioc_sub_le (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (M A B : ℕ) :
    ‖∑ n ∈ Ioc M A, g n - ∑ n ∈ Ioc M B, g n‖ ≤
      2 * |((A : ℝ) - (B : ℝ))| := by
  rw [sum_sub_sum_eq_sdiff]
  have h1 :=
    norm_sum_unimodular_card (Ioc M A \ Ioc M B) g hg
  have h2 :=
    norm_sum_unimodular_card (Ioc M B \ Ioc M A) g hg
  have htri :
      ‖∑ n ∈ Ioc M A \ Ioc M B, g n - ∑ n ∈ Ioc M B \ Ioc M A, g n‖ ≤
        ((Ioc M A \ Ioc M B).card : ℝ) + ((Ioc M B \ Ioc M A).card : ℝ) :=
    (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hc1 := card_Ioc_sdiff_le M A B
  have hc2 := card_Ioc_sdiff_le M B A
  have habs : |((B : ℝ) - (A : ℝ))| = |((A : ℝ) - (B : ℝ))| := abs_sub_comm _ _
  have hc2' : ((Ioc M B \ Ioc M A).card : ℝ) ≤ |((A : ℝ) - (B : ℝ))| := by
    rwa [habs] at hc2
  have hcards := add_le_add hc1 hc2'
  have htwo :
      |((A : ℝ) - (B : ℝ))| + |((A : ℝ) - (B : ℝ))| =
        2 * |((A : ℝ) - (B : ℝ))| := by
    ring
  exact htri.trans (hcards.trans_eq htwo)

private theorem tendsto_window_end_div {a : ℕ → ℕ} (ha : StrictMono a)
    (hD : IndexPassageD a) :
    Tendsto (fun M : ℕ =>
      |(((seqCount a (2 * a M) - 1 : ℕ) : ℝ) - 2 * (M : ℝ))| / M)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun M : ℕ => (1 : ℝ) / M) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have heq :
      (fun M : ℕ =>
        (((seqCount a (2 * a M) - 1 : ℕ) : ℝ) - 2 * (M : ℝ)) / M) =ᶠ[atTop]
        fun M => ((seqCount a (2 * a M) : ℝ) - 2 * M) / M - 1 / M := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hsc : M + 1 ≤ seqCount a (2 * a M) := le_seqCount_two ha M
    have h1le : 1 ≤ seqCount a (2 * a M) :=
      le_trans (Nat.succ_le_succ (Nat.zero_le M)) hsc
    have hcast : ((seqCount a (2 * a M) - 1 : ℕ) : ℝ) =
        (seqCount a (2 * a M) : ℝ) - 1 := by
      rw [Nat.cast_sub h1le, Nat.cast_one]
    have hM0 : (M : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)
    rw [hcast]
    field_simp [hM0]
    ring
  have hlim :
      Tendsto (fun M : ℕ =>
        (((seqCount a (2 * a M) - 1 : ℕ) : ℝ) - 2 * (M : ℝ)) / M)
        atTop (𝓝 0) :=
    Filter.Tendsto.congr' heq.symm (by simpa using hD.sub h1)
  have habs :
      Tendsto (fun M : ℕ =>
        |(((seqCount a (2 * a M) - 1 : ℕ) : ℝ) - 2 * (M : ℝ)) / M|)
        atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, abs_zero] using hlim.norm
  have heqAbs :
      (fun M : ℕ =>
        |(((seqCount a (2 * a M) - 1 : ℕ) : ℝ) - 2 * (M : ℝ))| / M) =ᶠ[atTop]
        fun M =>
          |(((seqCount a (2 * a M) - 1 : ℕ) : ℝ) - 2 * (M : ℝ)) / M| := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hMnn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rw [abs_div, abs_of_nonneg hMnn]
  exact Filter.Tendsto.congr' heqAbs.symm habs

/-- Window truncated-phase Weyl, index passage D, and the named
physical-versus-index truncation match imply Cesàro
`TruncatedPhaseWeyl` along `indexProfileL`. -/
theorem truncatedPhaseWeyl_of_window_index {a : ℕ → ℕ} (ha : StrictMono a)
    {P : ℕ → ℝ[X]} {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hW : TruncatedPhaseWindowWeyl a P B ρ G)
    (hD : IndexPassageD a)
    (hmatch : TruncatedPhaseWindowIndexMatch a P B ρ G) :
    TruncatedPhaseWeyl a P B (indexProfileL ρ G a) := by
  intro τ hτ
  let g : ℕ → ℂ := fun n =>
    e ((τ : ℝ) * seqGapPolyTailTrunc a P B (indexProfileL ρ G a n) n)
  have hg : ∀ n, ‖g n‖ ≤ 1 := fun n => (pack_norm_e _).le
  have hwinTrue := hW τ hτ
  have hmatchτ := hmatch τ hτ
  have heqMatch :
      (fun X : ℕ =>
        windowAvg (seqWindow a X) (fun n =>
          e ((τ : ℝ) * seqGapPolyTailTrunc a P B
              (stdProfileL ρ (G X)) n) -
            g n)) =
        fun X =>
          windowAvg (seqWindow a X) (fun n =>
            e ((τ : ℝ) * seqGapPolyTailTrunc a P B
              (stdProfileL ρ (G X)) n)) -
            windowAvg (seqWindow a X) g := by
    funext X
    exact windowAvg_sub _ _ _
  have hdiff := hmatchτ
  rw [heqMatch] at hdiff
  have hwinG : Tendsto (fun X : ℕ => windowAvg (seqWindow a X) g)
      atTop (𝓝 0) := by
    have hcomb := hwinTrue.sub hdiff
    simpa [sub_sub_cancel] using hcomb
  have hwinM : Tendsto (fun M : ℕ => windowAvg (seqWindow a (a M)) g)
      atTop (𝓝 0) :=
    hwinG.comp (tendsto_strictMono_atTop ha)
  have hcardR := tendsto_seqWindow_card_div ha hD
  have hcardC : Tendsto (fun M : ℕ =>
      ((seqWindow a (a M)).card : ℂ) / M) atTop (𝓝 1) := by
    have hfun :
        (fun M : ℕ => ((seqWindow a (a M)).card : ℂ) / M) =
          fun M => Complex.ofReal (((seqWindow a (a M)).card : ℝ) / M) := by
      funext M
      calc
        ((seqWindow a (a M)).card : ℂ) / M
            = (((seqWindow a (a M)).card : ℝ) : ℂ) / ((M : ℝ) : ℂ) := by
              rw [Complex.ofReal_natCast, Complex.ofReal_natCast]
        _ = Complex.ofReal (((seqWindow a (a M)).card : ℝ) / M) :=
              (Complex.ofReal_div _ _).symm
    rw [hfun]
    have h1 : ((1 : ℝ) : ℂ) = (1 : ℂ) := Complex.ofReal_one
    exact h1 ▸ Filter.tendsto_ofReal_iff.mpr hcardR
  have hprod : Tendsto (fun M : ℕ =>
      windowAvg (seqWindow a (a M)) g *
        (((seqWindow a (a M)).card : ℂ) / M)) atTop (𝓝 0) := by
    simpa using hwinM.mul hcardC
  have heqProd :
      (fun M : ℕ => (∑ n ∈ seqWindow a (a M), g n) / M) =ᶠ[atTop]
        fun M =>
          windowAvg (seqWindow a (a M)) g *
            (((seqWindow a (a M)).card : ℂ) / M) := by
    filter_upwards [eventually_ge_atTop 1] with M _hM
    unfold windowAvg
    by_cases h0 : (seqWindow a (a M)).card = 0
    · have hs : seqWindow a (a M) = ∅ := card_eq_zero.mp h0
      rw [hs, sum_empty, card_empty]
      simp
    · have hc0 : ((seqWindow a (a M)).card : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr h0
      rw [div_mul_div_comm, mul_comm (∑ n ∈ seqWindow a (a M), g n),
        mul_div_mul_left _ _ hc0]
  have hWmean : Tendsto (fun M : ℕ =>
      (∑ n ∈ seqWindow a (a M), g n) / M) atTop (𝓝 0) :=
    Filter.Tendsto.congr' heqProd.symm hprod
  have hIocDiff : Tendsto (fun M : ℕ =>
      (∑ n ∈ Ioc M (2 * M), g n) / M -
        (∑ n ∈ seqWindow a (a M), g n) / M) atTop (𝓝 0) := by
    refine squeeze_zero_norm
      (f := fun M : ℕ =>
        (∑ n ∈ Ioc M (2 * M), g n) / M -
          (∑ n ∈ seqWindow a (a M), g n) / M)
      (a := fun M : ℕ =>
        (2 : ℝ) *
          (|(((seqCount a (2 * a M) - 1 : ℕ) : ℝ) - 2 * (M : ℝ))| / M))
      (fun M => ?_) ?_
    · have hWset : seqWindow a (a M) = Ioc M (seqCount a (2 * a M) - 1) :=
        seqWindow_eq_Ioc ha M
      have hsub :
          (∑ n ∈ Ioc M (2 * M), g n) / M -
            (∑ n ∈ seqWindow a (a M), g n) / M =
          (∑ n ∈ Ioc M (2 * M), g n -
            ∑ n ∈ Ioc M (seqCount a (2 * a M) - 1), g n) / M := by
        rw [hWset, sub_div]
      rw [hsub, norm_div]
      have hMn : ‖(M : ℂ)‖ = (M : ℝ) := Complex.norm_natCast M
      rw [hMn]
      have hle :=
        norm_sum_Ioc_sub_le g hg M (2 * M) (seqCount a (2 * a M) - 1)
      have hcast : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by simp
      have : 2 * |(((2 * M : ℕ) : ℝ) - ((seqCount a (2 * a M) - 1 : ℕ) : ℝ))| /
          M =
          2 *
            (|(((seqCount a (2 * a M) - 1 : ℕ) : ℝ) - 2 * (M : ℝ))| / M) := by
        rw [hcast, abs_sub_comm]
        ring
      have hdiv :
          ‖∑ n ∈ Ioc M (2 * M), g n -
              ∑ n ∈ Ioc M (seqCount a (2 * a M) - 1), g n‖ / M ≤
            2 * |(((2 * M : ℕ) : ℝ) - ((seqCount a (2 * a M) - 1 : ℕ) : ℝ))| /
              M :=
        div_le_div_of_nonneg_right hle (Nat.cast_nonneg M)
      exact hdiv.trans_eq this
    · have h2 : Tendsto (fun M : ℕ =>
          (2 : ℝ) *
            (|(((seqCount a (2 * a M) - 1 : ℕ) : ℝ) - 2 * (M : ℝ))| / M))
          atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul (tendsto_window_end_div ha hD))
      exact h2
  have hIoc : Tendsto (fun M : ℕ =>
      (∑ n ∈ Ioc M (2 * M), g n) / M) atTop (𝓝 0) := by
    have hcomb := hWmean.add hIocDiff
    simpa [sub_add_cancel, add_comm] using hcomb
  simpa [g] using tendsto_cesaro_of_dyadicBlocks g hg hIoc

theorem truncatedPhaseWeyl_nthPrime_of_window_index {P : ℕ → ℝ[X]}
    {B : ℕ} {ρ : ℝ} {G : ℕ → ℝ}
    (hW : TruncatedPhaseWindowWeyl nthPrime P B ρ G)
    (hD : IndexPassageD nthPrime)
    (hmatch : TruncatedPhaseWindowIndexMatch nthPrime P B ρ G) :
    TruncatedPhaseWeyl nthPrime P B (indexProfileL ρ G nthPrime) :=
  truncatedPhaseWeyl_of_window_index nthPrime_strictMono hW hD hmatch

/-! ### Orbit pack: truncated Weyl + uniform tail → `weylCriterion` -/

/-- Direct wrapper of `TruncatedWeylPack`: for every tail budget there
is a truncation that is both Cesàro-vanishing and uniformly close to
the infinite orbit phase. -/
theorem weylCriterion_gapPolySeries_of_uniformOrbitPack {P : ℕ → ℝ[X]}
    {B : ℕ} (hB : 2 ≤ B)
    (hsm : Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hint : ∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z)
    (hpack : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ → ℕ,
      TruncatedPhaseWeyl nthPrime P B L ∧ UniformOrbitTail P B L ε) :
    weylCriterion B (gapPolySeries P B) :=
  weylCriterion_gapPolySeries_of_truncatedPhaseWeyl_uniform hB hsm hint
    hpack

/-- Same pack at a single truncation `L` whose untruncated tail can be
made arbitrarily small. The quantification `∀ ε, UniformOrbitTail L ε`
is the uniform vanishing of the phase remainder at this `L`. -/
theorem weylCriterion_gapPolySeries_of_truncatedPhaseWeyl_uniformOrbit
    {P : ℕ → ℝ[X]} {B : ℕ} (hB : 2 ≤ B)
    (hsm : Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hint : ∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z)
    {L : ℕ → ℕ} (hΦ : TruncatedPhaseWeyl nthPrime P B L)
    (hU : ∀ ε : ℝ, 0 < ε → UniformOrbitTail P B L ε) :
    weylCriterion B (gapPolySeries P B) :=
  weylCriterion_gapPolySeries_of_uniformOrbitPack hB hsm hint
    fun ε hε => ⟨L, hΦ, hU ε hε⟩

/-- Full consumer: first-`L` cut transfer, model vanishing, span-cut,
rank/shift, D, the window/index match, integer evaluations,
summability, and a uniformly small orbit tail at the index profile.
Applies `TruncatedWeylPack`. Does not claim `KuperbergConj13`. -/
theorem weylCriterion_gapPolySeries_of_statisticalConsumer
    {P : ℕ → ℝ[X]} {B : ℕ} (hB : 2 ≤ B) {ρ : ℝ} {G : ℕ → ℝ}
    (hsm : Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hint : ∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z)
    (hS : TruncatedPhaseCutTransfer nthPrime P B ρ G)
    (hmodel : ∀ ω : ℕ → SieveMixture,
      Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) →
        ModelTruncatedPhaseVanishing P B ρ G ω)
    (hcut : TruncatedPhaseSpanCutVanishing nthPrime P B ρ G)
    (hshift : TruncatedPhaseRankShiftVanishing nthPrime P B ρ G)
    (hD : IndexPassageD nthPrime)
    (hmatch : TruncatedPhaseWindowIndexMatch nthPrime P B ρ G)
    (hU : ∀ ε : ℝ, 0 < ε →
      UniformOrbitTail P B (indexProfileL ρ G nthPrime) ε) :
    weylCriterion B (gapPolySeries P B) := by
  have hWin :=
    truncatedPhaseWindowWeyl_nthPrime_of_cutTransfer_model hS hmodel
      hcut hshift
  have hΦ := truncatedPhaseWeyl_nthPrime_of_window_index hWin hD hmatch
  exact weylCriterion_gapPolySeries_of_truncatedPhaseWeyl_uniformOrbit
    hB hsm hint hΦ hU

theorem weylCriterion_gapPolySeries_const_of_statisticalConsumer
    (P : ℝ[X]) {B : ℕ} (hB : 2 ≤ B) {ρ : ℝ} {G : ℕ → ℝ}
    (hint : ∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) P = z)
    (hS : TruncatedPhaseCutTransfer nthPrime (fun _ => P) B ρ G)
    (hmodel : ∀ ω : ℕ → SieveMixture,
      Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) →
        ModelTruncatedPhaseVanishing (fun _ => P) B ρ G ω)
    (hcut : TruncatedPhaseSpanCutVanishing nthPrime (fun _ => P) B ρ G)
    (hD : IndexPassageD nthPrime)
    (hmatch : TruncatedPhaseWindowIndexMatch nthPrime (fun _ => P) B ρ G)
    (hU : ∀ ε : ℝ, 0 < ε →
      UniformOrbitTail (fun _ => P) B
        (indexProfileL ρ G nthPrime) ε) :
    weylCriterion B (gapPolySeries (fun _ => P) B) :=
  weylCriterion_gapPolySeries_of_statisticalConsumer hB
    (gapPolySeries_const_summable P hB) hint hS hmodel hcut
    (truncatedPhaseRankShiftVanishing_const nthPrime P B ρ G) hD hmatch
    hU

theorem weylCriterion_gapPolySeries_periodic_of_statisticalConsumer
    {P : ℕ → ℝ[X]} {B k : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (hP : Periodic P k) {ρ : ℝ} {G : ℕ → ℝ}
    (hint : ∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z)
    (hS : TruncatedPhaseCutTransfer nthPrime P B ρ G)
    (hmodel : ∀ ω : ℕ → SieveMixture,
      Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) →
        ModelTruncatedPhaseVanishing P B ρ G ω)
    (hcut : TruncatedPhaseSpanCutVanishing nthPrime P B ρ G)
    (hshift : TruncatedPhaseRankShiftVanishing nthPrime P B ρ G)
    (hD : IndexPassageD nthPrime)
    (hmatch : TruncatedPhaseWindowIndexMatch nthPrime P B ρ G)
    (hU : ∀ ε : ℝ, 0 < ε →
      UniformOrbitTail P B (indexProfileL ρ G nthPrime) ε) :
    weylCriterion B (gapPolySeries P B) :=
  weylCriterion_gapPolySeries_of_statisticalConsumer hB
    (gapPolySeries_periodic_summable hB hk hP) hint hS hmodel hcut
    hshift hD hmatch hU

theorem weylCriterion_gapPolySeries_of_statisticalConsumer_intCoeff
    {P : ℕ → ℝ[X]} {B : ℕ} (hB : 2 ≤ B) {ρ : ℝ} {G : ℕ → ℝ}
    (hsm : Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hPint : ∀ n i, ∃ z : ℤ, (P n).coeff i = z)
    (hS : TruncatedPhaseCutTransfer nthPrime P B ρ G)
    (hmodel : ∀ ω : ℕ → SieveMixture,
      Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) →
        ModelTruncatedPhaseVanishing P B ρ G ω)
    (hcut : TruncatedPhaseSpanCutVanishing nthPrime P B ρ G)
    (hshift : TruncatedPhaseRankShiftVanishing nthPrime P B ρ G)
    (hD : IndexPassageD nthPrime)
    (hmatch : TruncatedPhaseWindowIndexMatch nthPrime P B ρ G)
    (hU : ∀ ε : ℝ, 0 < ε →
      UniformOrbitTail P B (indexProfileL ρ G nthPrime) ε) :
    weylCriterion B (gapPolySeries P B) :=
  weylCriterion_gapPolySeries_of_statisticalConsumer hB hsm
    (exists_int_eval_primeGap_of_int_coeff hPint) hS hmodel hcut hshift
    hD hmatch hU

/-! ### Optional Abel: affine gap polynomials to position weights -/

private theorem weylCriterion_add_rat_pack {b : ℕ} (hb : 2 ≤ b) {θ : ℝ}
    (q : ℚ) (h : weylCriterion b θ) : weylCriterion b (θ + q) := by
  have hden1 : 1 ≤ q.den := Nat.succ_le_of_lt q.den_pos
  have hdenZ : (q.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr q.den_ne_zero
  have hmul : weylCriterion b ((q.den : ℤ) * θ) := weylCriterion_int_mul hdenZ h
  have hadd : weylCriterion b ((q.den : ℤ) * θ + q.num) :=
    weylCriterion_add_int q.num hmul
  have hqn : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    exact_mod_cast q.den_mul_eq_num
  have hclear :
      (q.den : ℝ) * (θ + (q : ℝ)) = ((q.den : ℤ) : ℝ) * θ + (q.num : ℝ) := by
    have hcast : ((q.den : ℤ) : ℝ) = (q.den : ℝ) := Int.cast_natCast _
    rw [hcast, mul_add, hqn]
  have hscaled : weylCriterion b ((q.den : ℝ) * (θ + (q : ℝ))) := by
    rw [hclear]
    have hcoe :
        ((q.den : ℤ) : ℝ) * θ + (q.num : ℝ) = (q.den : ℤ) * θ + q.num := by
      simp
    rw [hcoe]
    exact hadd
  exact weylCriterion_of_mul hden1 hb hscaled

/-- Gap-poly Weyl plus a rational identity yield Weyl of a weighted
position series. Does not invent the identity. -/
theorem weylCriterion_primePosWeightedSeries_of_gapPoly_rat
    {P : ℕ → ℝ[X]} {B : ℕ} {c : ℕ → ℝ} {q : ℚ} (hB : 2 ≤ B)
    (hW : weylCriterion B (gapPolySeries P B))
    (heq : primePosWeightedSeries c B = gapPolySeries P B + (q : ℝ)) :
    weylCriterion B (primePosWeightedSeries c B) := by
  have h := weylCriterion_add_rat_pack hB q hW
  rwa [heq]

/-- Unweighted position series, still only under an explicit Weyl
hypothesis and a rational correction. -/
theorem weylCriterion_primePosSeries_of_gapPoly_rat {P : ℕ → ℝ[X]}
    {B : ℕ} {q : ℚ} (hB : 2 ≤ B)
    (hW : weylCriterion B (gapPolySeries P B))
    (heq : primePosSeries B = gapPolySeries P B + (q : ℝ)) :
    weylCriterion B (primePosSeries B) := by
  have h := weylCriterion_add_rat_pack hB q hW
  rwa [heq]

/-- The affine identity rearranges to a rational-correction statement. -/
theorem affineGapAbelCorrectionRat_of_geom {P : ℕ → ℝ[X]} {B k : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hP : Periodic P k)
    (hdeg : ∀ n, natDegree (P n) ≤ 1) {q : ℚ}
    (hcorr :
      (nthPrime 0 : ℝ) * affinePeriodicGapWeight P k 0 -
        geomWeightSeries (fun n => (P n).coeff 0) B = (q : ℝ)) :
    AffineGapAbelCorrectionRat P B k := by
  refine ⟨q, ?_⟩
  have hid := gapPolySeries_affine_eq_abel hB hk hP hdeg
  calc
    primePosWeightedSeries
          (fun n => recGapWeight B (affinePeriodicGapWeight P k) (n - 1)) B =
        gapPolySeries P B +
          ((nthPrime 0 : ℝ) * affinePeriodicGapWeight P k 0 -
            geomWeightSeries (fun n => (P n).coeff 0) B) := by
      rw [hid]
      ring
    _ = gapPolySeries P B + (q : ℝ) := by rw [hcorr]

theorem weylCriterion_primePosWeightedSeries_of_affine_gapPoly
    {P : ℕ → ℝ[X]} {B k : ℕ} (hB : 2 ≤ B)
    (hW : weylCriterion B (gapPolySeries P B))
    (hcorr : AffineGapAbelCorrectionRat P B k) :
    weylCriterion B
      (primePosWeightedSeries
        (fun n => recGapWeight B (affinePeriodicGapWeight P k) (n - 1))
          B) := by
  obtain ⟨q, heq⟩ := hcorr
  exact weylCriterion_primePosWeightedSeries_of_gapPoly_rat hB hW heq

theorem weylCriterion_primePosSeries_of_gapPoly
    {P : ℕ → ℝ[X]} {B : ℕ} (hB : 2 ≤ B)
    (hW : weylCriterion B (gapPolySeries P B))
    (hcorr : PrimePosAbelCorrectionRat P B) :
    weylCriterion B (primePosSeries B) := by
  obtain ⟨q, heq⟩ := hcorr
  exact weylCriterion_primePosSeries_of_gapPoly_rat hB hW heq

theorem weylCriterion_primePosSeries_one_of_gapPoly {P : ℕ → ℝ[X]}
    {B : ℕ} {q : ℚ} (hB : 2 ≤ B)
    (hW : weylCriterion B (gapPolySeries P B))
    (heq : primePosWeightedSeries (fun _ => (1 : ℝ)) B =
      gapPolySeries P B + (q : ℝ)) :
    weylCriterion B (primePosSeries B) := by
  have hpos := weylCriterion_primePosWeightedSeries_of_gapPoly_rat
    (c := fun _ => (1 : ℝ)) hB hW heq
  rwa [primePosWeightedSeries_one] at hpos

end PrimeGapNormality.Prime
