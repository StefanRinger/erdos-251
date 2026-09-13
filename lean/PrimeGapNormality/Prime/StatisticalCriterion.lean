import PrimeGapNormality.Prime.EndAPI
import PrimeGapNormality.Prime.EulerProd
import PrimeGapNormality.Prime.Fourier
import PrimeGapNormality.Prime.JointWeyl
import PrimeGapNormality.Prime.WeylMeans
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Basic

/-!
# Named S/T/D statistical criterion (paper `thm:statistical`)

Paper v0.3 § “The common statistical criterion”: consumer conditions
on a general increasing sequence `a`, auxiliary scale `ρ > 1`, and
digit base `B ≥ 2`. These are named `Prop`s, not axioms.

Full packaging `S/T/D ⇒ thm:prime` is not compiled (model
cancellation is missing). Algebraic glue: D identifies
`|I_{a_M}| / M → 1`; truncated-phase tests are admissible for S;
orbit + Lipschitz of `e` upgrade JointWeyl-style truncated vanishing
plus a Cesàro remainder to `weylCriterion` of `gapPolySeries`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:S), (eq:T), (eq:D),
(eq:orbit), `thm:statistical`.
Contract: API
Audit: GREEN
-/

open Finset Filter Polynomial
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000

/-! ### Sequence geometry (paper `g_n`, `A(x)`, `I_X`) -/

/-- Consecutive gap. Paper `g_{n+1}` is Lean `seqGap a n`. -/
def seqGap (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  a (n + 1) - a n

/-- Paper `A(x) = #{n : a_n ≤ x}`. For `StrictMono a` this is exact:
`n ≤ a n`, so it suffices to search `range (x + 1)`. -/
def seqCount (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  ((range (x + 1)).filter (fun n => a n ≤ x)).card

/-- Paper `I_X = {n : X < a_n ≤ 2X}`. -/
def seqWindow (a : ℕ → ℕ) (X : ℕ) : Finset ℕ :=
  (range (2 * X + 1)).filter (fun n => X < a n ∧ a n ≤ 2 * X)

/-- Paper `log_ρ G`. -/
noncomputable def logρ (ρ G : ℝ) : ℝ :=
  Real.log G / Real.log ρ

/-- Paper `L_X = ⌈log_ρ G_X + √(log_ρ G_X)⌉`. -/
noncomputable def stdProfileL (ρ G : ℝ) : ℕ :=
  ⌈logρ ρ G + Real.sqrt (logρ ρ G)⌉₊

/-- Paper `S_X = 4 L_X G_X`. -/
noncomputable def stdProfileS (ρ G : ℝ) : ℝ :=
  4 * (stdProfileL ρ G : ℝ) * G

/-- Paper `T_ρ(n) = ∑_{h≥1} g_{n+h-1} ρ^{-h}`. Lean `n` is 0-based. -/
noncomputable def seqGapTail (ρ : ℝ) (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑' h : ℕ, (seqGap a (n + h) : ℝ) / ρ ^ (h + 1)

/-- Offset tuple from the root `a n`: paper `a_{n+k} - a_n`. -/
def seqOffset (a : ℕ → ℕ) (n k : ℕ) : ℕ :=
  a (n + k) - a n

noncomputable def windowAvg (s : Finset ℕ) (f : ℕ → ℂ) : ℂ :=
  (∑ n ∈ s, f n) / s.card

noncomputable def windowAvgReal (s : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ s, f n) / s.card

theorem strictMono_le_id {a : ℕ → ℕ} (ha : StrictMono a) (n : ℕ) :
    n ≤ a n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (ha (Nat.lt_succ_self n)))

/-- A finite initial segment of `ℕ` is `range (card)`. -/
private theorem initial_eq_range (s : Finset ℕ)
    (hinit : ∀ ⦃n k : ℕ⦄, n ∈ s → k ≤ n → k ∈ s) :
    s = range s.card := by
  by_cases h0 : s.Nonempty
  · let m := s.max' h0
    have hrange : s = range (m + 1) := by
      ext n
      simp only [mem_range, Nat.lt_succ_iff]
      constructor
      · exact fun hn => s.le_max' n hn
      · exact fun hn => hinit (s.max'_mem h0) hn
    rw [hrange, card_range]
  · simp [not_nonempty_iff_eq_empty.mp h0]

theorem seqCount_filter_eq_range {a : ℕ → ℕ} (ha : StrictMono a) (x : ℕ) :
    (range (x + 1)).filter (fun n => a n ≤ x) = range (seqCount a x) := by
  set s := (range (x + 1)).filter (fun n => a n ≤ x)
  have hinit : ∀ ⦃n k : ℕ⦄, n ∈ s → k ≤ n → k ∈ s := by
    intro n k hn hk
    simp only [s, mem_filter, mem_range, Nat.lt_succ_iff] at hn ⊢
    exact ⟨le_trans hk hn.1, le_trans ((ha.le_iff_le).mpr hk) hn.2⟩
  simpa [s, seqCount] using initial_eq_range s hinit

theorem seqCount_lt_iff {a : ℕ → ℕ} (ha : StrictMono a) {x n : ℕ} :
    n < seqCount a x ↔ a n ≤ x := by
  have hset := seqCount_filter_eq_range ha x
  constructor
  · intro hn
    have : n ∈ (range (x + 1)).filter (fun k => a k ≤ x) := by
      rw [hset, mem_range]
      exact hn
    exact (mem_filter.mp this).2
  · intro hle
    have hnX : n ≤ x := le_trans (strictMono_le_id ha n) hle
    have : n ∈ (range (x + 1)).filter (fun k => a k ≤ x) := by
      simp [mem_filter, mem_range, Nat.lt_succ_iff, hnX, hle]
    rw [hset, mem_range] at this
    exact this

theorem seqCount_mono {a : ℕ → ℕ} {x y : ℕ} (hxy : x ≤ y) :
    seqCount a x ≤ seqCount a y := by
  refine card_le_card ?_
  intro n hn
  simp only [seqCount, mem_filter, mem_range, Nat.lt_succ_iff] at hn ⊢
  exact ⟨le_trans hn.1 hxy, le_trans hn.2 hxy⟩

theorem seqCount_apply_self {a : ℕ → ℕ} (ha : StrictMono a) (M : ℕ) :
    seqCount a (a M) = M + 1 := by
  have hlt : M < seqCount a (a M) := (seqCount_lt_iff ha).mpr le_rfl
  have hnot : ¬ a (M + 1) ≤ a M :=
    not_le.mpr (ha (Nat.lt_succ_self M))
  have hge : ¬ M + 1 < seqCount a (a M) := fun h =>
    hnot ((seqCount_lt_iff ha).mp h)
  omega

theorem le_seqCount_two {a : ℕ → ℕ} (ha : StrictMono a) (M : ℕ) :
    M + 1 ≤ seqCount a (2 * a M) := by
  have hle : a M ≤ 2 * a M := Nat.le_mul_of_pos_left (a M) (by decide : 0 < 2)
  rw [← seqCount_apply_self ha M]
  exact seqCount_mono (a := a) hle

theorem seqWindow_eq_Ioc {a : ℕ → ℕ} (ha : StrictMono a) (M : ℕ) :
    seqWindow a (a M) = Ioc M (seqCount a (2 * a M) - 1) := by
  let K := seqCount a (2 * a M)
  have hK : M + 1 ≤ K := le_seqCount_two ha M
  have hKpos : 1 ≤ K := le_trans (Nat.succ_le_succ (Nat.zero_le M)) hK
  have hKpred : K - 1 + 1 = K := Nat.sub_add_cancel hKpos
  ext n
  simp only [seqWindow, mem_filter, mem_range, mem_Ioc, Nat.lt_succ_iff]
  constructor
  · intro h
    have hnM : M < n := (ha.lt_iff_lt).mp h.2.1
    have hnK : n < K := (seqCount_lt_iff ha).mpr h.2.2
    have : n ≤ K - 1 := by
      have : n < K - 1 + 1 := by rwa [hKpred]
      exact Nat.lt_succ_iff.mp this
    exact ⟨hnM, this⟩
  · intro h
    have hnM : M < n := h.1
    have hnltK : n < K := by
      have : n < K - 1 + 1 := Nat.lt_succ_of_le h.2
      rwa [hKpred] at this
    have hak : a n ≤ 2 * a M := (seqCount_lt_iff ha).mp hnltK
    have hnX : n ≤ 2 * a M := le_trans (strictMono_le_id ha n) hak
    exact ⟨hnX, (ha.lt_iff_lt).mpr hnM, hak⟩

theorem seqWindow_card {a : ℕ → ℕ} (ha : StrictMono a) (M : ℕ) :
    (seqWindow a (a M)).card = seqCount a (2 * a M) - (M + 1) := by
  have hK : M + 1 ≤ seqCount a (2 * a M) := le_seqCount_two ha M
  have hle : M ≤ seqCount a (2 * a M) - 1 := by omega
  rw [seqWindow_eq_Ioc ha M, Nat.card_Ioc M (seqCount a (2 * a M) - 1)]
  omega

/-! ### Rooted sieve law `Prob_{0,y}` (paper, before (eq:S)) -/

/-- Primes `p ≤ y` as a subtype. -/
abbrev SievePrime (y : ℕ) := {p : ℕ // p ∈ Nat.primesLE y}

/-- One forbidden nonzero residue modulo each prime `p ≤ y`. -/
abbrev ResidueChoice (y : ℕ) :=
  ∀ p : SievePrime y, Fin (p.val - 1)

instance (y : ℕ) : DecidableEq (SievePrime y) :=
  Subtype.instDecidableEq

instance (y : ℕ) : Fintype (SievePrime y) :=
  Finset.fintypeCoeSort (Nat.primesLE y)

instance (y : ℕ) : Fintype (ResidueChoice y) :=
  Pi.instFintype

/-- Decode a residue choice to a function on all naturals. -/
def residueOfChoice (y : ℕ) (σ : ResidueChoice y) (p : ℕ) : ℕ :=
  if h : p ∈ Nat.primesLE y then (σ ⟨p, h⟩).val + 1 else 0

/-- Nonnegative survivors of the rooted sieve: residue `0` is never
forbidden, so the root `0` always survives. -/
def sieveSurvives (y : ℕ) (r : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ Nat.primesLE y, n % p ≠ r p

instance (y : ℕ) (r : ℕ → ℕ) : DecidablePred (sieveSurvives y r) :=
  fun n => inferInstanceAs (Decidable (∀ p ∈ Nat.primesLE y, n % p ≠ r p))

/-- Ordered survivors `0 = x_0 < x_1 < ⋯`. Lean `k` is paper `x_k`. -/
noncomputable def sievePoint (y : ℕ) (r : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.nth (sieveSurvives y r) k

/-- Discrete `E_{0,y} F(x_0,x_1,…)`: average over residue choices. -/
noncomputable def rootedSieveMean (y : ℕ) (F : (ℕ → ℕ) → ℂ) : ℂ :=
  (∑ σ : ResidueChoice y, F (fun k => sievePoint y (residueOfChoice y σ) k)) /
    (Fintype.card (ResidueChoice y) : ℂ)

/-- Finite mixture `ω_X` of sieve levels `y ≥ 2`. -/
structure SieveMixture where
  support : Finset ℕ
  weight : ℕ → ℝ
  support_nonempty : support.Nonempty
  support_ge_two : ∀ y ∈ support, 2 ≤ y
  weight_nonneg : ∀ y ∈ support, 0 ≤ weight y
  weight_sum : ∑ y ∈ support, weight y = 1

noncomputable def mixtureMean (m : SieveMixture) (μ : ℕ → ℂ) : ℂ :=
  ∑ y ∈ m.support, (m.weight y : ℂ) * μ y

/-- Calibration `sup_{y ∈ supp ω} |V(y)^{-1}/G - 1|`. -/
noncomputable def mixtureCalib (m : SieveMixture) (G : ℝ) : ℝ :=
  m.support.sup' m.support_nonempty
    (fun y => |(eulerProd (y : ℝ))⁻¹ / G - 1|)

/-! ### Named Props S, T, D (not axioms) -/

/-- Paper (eq:S): short-pattern comparison. Uniformly over bounded
span-truncated tests `F` of the first `L_X` offsets,
`Avg_{n ∈ I_X} F(a_{n+1}-a_n,…,a_{n+L_X}-a_n)` equals the `ω_X`-mixture
of rooted-sieve means plus `o(1)`, with V-calibration
`sup_{y ∈ supp ω_X} |V(y)^{-1}/G_X - 1| → 0`. -/
def ShortPatternS (a : ℕ → ℕ) (ρ : ℝ) (G : ℕ → ℝ) : Prop :=
  1 < ρ ∧
    Tendsto G atTop atTop ∧
    ∃ ω : ℕ → SieveMixture,
      Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε → ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
          ∀ F : (ℕ → ℕ) → ℂ,
            (∀ v, ‖F v‖ ≤ 1) →
            (∀ v, stdProfileS ρ (G X) < v (stdProfileL ρ (G X)) → F v = 0) →
            ‖windowAvg (seqWindow a X)
                (fun n => F (fun k => seqOffset a n k)) -
              mixtureMean (ω X) (fun y => rootedSieveMean y F)‖ < ε

/-- Paper (eq:T): actual first gap-tail average
`Avg_{n ∈ I_X} T_ρ(n+L_X) = O_ρ(G_X)`. Includes the paper’s
summability `∑ a_n ρ^{-n} < ∞`. -/
def GapTailT (a : ℕ → ℕ) (ρ : ℝ) (G : ℕ → ℝ) : Prop :=
  1 < ρ ∧
    Tendsto G atTop atTop ∧
    Summable (fun n : ℕ => (a n : ℝ) / ρ ^ n) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ X : ℕ in atTop,
          0 < (seqWindow a X).card ∧
            windowAvgReal (seqWindow a X)
                (fun n => seqGapTail ρ a (n + stdProfileL ρ (G X))) ≤
              C * G X

/-- Paper (eq:D): `A(2 a_M) = 2M + o(M)`. -/
def IndexPassageD (a : ℕ → ℕ) : Prop :=
  Tendsto (fun M : ℕ =>
    ((seqCount a (2 * a M) : ℝ) - 2 * (M : ℝ)) / (M : ℝ))
    atTop (𝓝 0)

/-! ### D identifies window size with the dyadic scale -/

/-- D implies `|I_{a_M}| / M → 1`. -/
theorem tendsto_seqWindow_card_div {a : ℕ → ℕ} (ha : StrictMono a)
    (hD : IndexPassageD a) :
    Tendsto (fun M : ℕ => ((seqWindow a (a M)).card : ℝ) / M) atTop (𝓝 1) := by
  have h1M : Tendsto (fun M : ℕ => (1 : ℝ) / M) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have heq :
      (fun M : ℕ => ((seqWindow a (a M)).card : ℝ) / M) =ᶠ[atTop]
        fun M =>
          ((seqCount a (2 * a M) : ℝ) - 2 * M) / M + 1 - 1 / M := by
    filter_upwards [Filter.eventually_ge_atTop 1] with M hM
    have hM0 : (M : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)
    have hcard := seqWindow_card ha M
    have hK : M + 1 ≤ seqCount a (2 * a M) := le_seqCount_two ha M
    have hcast :
        ((seqCount a (2 * a M) - (M + 1) : ℕ) : ℝ) =
          (seqCount a (2 * a M) : ℝ) - ((M : ℝ) + 1) := by
      rw [Nat.cast_sub hK, Nat.cast_add_one]
    rw [hcard, hcast]
    field_simp [hM0]
    ring
  have hlim :
      Tendsto (fun M : ℕ =>
        ((seqCount a (2 * a M) : ℝ) - 2 * M) / M + 1 - 1 / M)
        atTop (𝓝 (0 + 1 - 0)) :=
    (hD.add tendsto_const_nhds).sub h1M
  exact Filter.Tendsto.congr' heq.symm (by simpa using hlim)

/-! ### JointWeyl-style vanishing of truncated gap-polynomial phases -/

/-- Infinite polynomial tail `U_P(n)`. -/
noncomputable def seqGapPolyTail (a : ℕ → ℕ) (P : ℕ → ℝ[X]) (B n : ℕ) : ℝ :=
  ∑' j : ℕ, eval (seqGap a (n + j) : ℝ) (P (n + j)) / (B : ℝ) ^ (j + 1)

/-- Truncated polynomial tail of relative rank `L`. -/
noncomputable def seqGapPolyTailTrunc (a : ℕ → ℕ) (P : ℕ → ℝ[X])
    (B L n : ℕ) : ℝ :=
  ∑ j ∈ range L, eval (seqGap a (n + j) : ℝ) (P (n + j)) / (B : ℝ) ^ (j + 1)

/-- General-sequence polynomial series. -/
noncomputable def seqGapPolySeries (a : ℕ → ℕ) (P : ℕ → ℝ[X]) (B : ℕ) : ℝ :=
  seqGapPolyTail a P B 0

/-- Cesàro vanishing of `e(τ Φ_L(n))` for every nonzero integer mode.
JointWeyl-style (no geometric `B^n` in the test). -/
def TruncatedPhaseWeyl (a : ℕ → ℕ) (P : ℕ → ℝ[X]) (B : ℕ)
    (L : ℕ → ℕ) : Prop :=
  ∀ τ : ℤ, τ ≠ 0 →
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
        e ((τ : ℝ) * seqGapPolyTailTrunc a P B (L n) n)) / N)
      atTop (𝓝 0)

/-- Window form of truncated-phase vanishing, matching paper
`Avg_{n ∈ I_X}` before the D-passage. -/
def TruncatedPhaseWindowWeyl (a : ℕ → ℕ) (P : ℕ → ℝ[X]) (B : ℕ)
    (ρ : ℝ) (G : ℕ → ℝ) : Prop :=
  ∀ τ : ℤ, τ ≠ 0 →
    Tendsto (fun X : ℕ =>
      windowAvg (seqWindow a X)
        (fun n => e ((τ : ℝ) *
          seqGapPolyTailTrunc a P B (stdProfileL ρ (G X)) n)))
      atTop (𝓝 0)

/-! ### Truncated phases as admissible short-pattern tests for S -/

/-- Gaps recovered from offsets: `x_{j+1} - x_j`. -/
theorem seqOffset_succ_sub {a : ℕ → ℕ} (ha : StrictMono a) (n j : ℕ) :
    seqOffset a n (j + 1) - seqOffset a n j = seqGap a (n + j) := by
  have h0 : a n ≤ a (n + j) := (ha.le_iff_le).mpr (Nat.le_add_right n j)
  have h1 : a (n + j) ≤ a (n + j + 1) :=
    (ha.le_iff_le).mpr (Nat.le_succ (n + j))
  unfold seqOffset seqGap
  rw [← Nat.add_assoc n j 1]
  have hsum := Nat.sub_add_sub_cancel h1 h0
  rw [← hsum, Nat.add_sub_cancel]

/-- Constant-coefficient truncated phase as a function of offsets. -/
noncomputable def truncatedPhaseTest (P : ℝ[X]) (B L : ℕ) (τ : ℤ)
    (v : ℕ → ℕ) : ℂ :=
  e ((τ : ℝ) *
    ∑ j ∈ range L,
      eval ((v (j + 1) - v j : ℕ) : ℝ) P / (B : ℝ) ^ (j + 1))

/-- Span cut `F = 0` if `x_L > S`, matching (eq:S). -/
noncomputable def truncatedPhaseTestCut (P : ℝ[X]) (B L : ℕ) (S : ℝ)
    (τ : ℤ) (v : ℕ → ℕ) : ℂ :=
  if S < v L then 0 else truncatedPhaseTest P B L τ v

theorem truncatedPhaseTest_norm (P : ℝ[X]) (B L : ℕ) (τ : ℤ)
    (v : ℕ → ℕ) : ‖truncatedPhaseTest P B L τ v‖ ≤ 1 := by
  simpa [truncatedPhaseTest] using (norm_e _).le

theorem truncatedPhaseTestCut_norm (P : ℝ[X]) (B L : ℕ) (S : ℝ)
    (τ : ℤ) (v : ℕ → ℕ) : ‖truncatedPhaseTestCut P B L S τ v‖ ≤ 1 := by
  unfold truncatedPhaseTestCut
  split_ifs with h
  · simp
  · exact truncatedPhaseTest_norm P B L τ v

theorem truncatedPhaseTestCut_span (P : ℝ[X]) (B L : ℕ) (S : ℝ)
    (τ : ℤ) (v : ℕ → ℕ) (hv : S < v L) :
    truncatedPhaseTestCut P B L S τ v = 0 := by
  simp [truncatedPhaseTestCut, hv]

theorem truncatedPhaseTest_eq {a : ℕ → ℕ} (ha : StrictMono a)
    (P : ℝ[X]) (B L n : ℕ) (τ : ℤ) :
    truncatedPhaseTest P B L τ (fun k => seqOffset a n k) =
      e ((τ : ℝ) * seqGapPolyTailTrunc a (fun _ => P) B L n) := by
  simp [truncatedPhaseTest, seqGapPolyTailTrunc, seqOffset_succ_sub ha]

/-! ### Orbit identity and truncated-phase packaging -/

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem e_int (n : ℤ) : e n = 1 := by
  unfold e
  simp only [Complex.ofReal_intCast]
  have h : (2 * Real.pi * Complex.I * (n : ℂ)) = n * (2 * Real.pi * Complex.I) := by
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private theorem base_ne_zero {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hB))

theorem seqGapPolyTail_summable_shift {a : ℕ → ℕ} {P : ℕ → ℝ[X]} {B : ℕ}
    (hB : 2 ≤ B)
    (hsm : Summable fun n : ℕ =>
      eval (seqGap a n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (k : ℕ) :
    Summable fun j : ℕ =>
      eval (seqGap a (k + j) : ℝ) (P (k + j)) / (B : ℝ) ^ (j + 1) := by
  have hb0 := base_ne_zero hB
  have hshift :
      Summable fun j : ℕ =>
        eval (seqGap a (j + k) : ℝ) (P (j + k)) / (B : ℝ) ^ (j + k + 1) :=
    (summable_nat_add_iff
        (f := fun n : ℕ =>
          eval (seqGap a n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
        k).mpr
      hsm
  have hshift' :
      Summable fun j : ℕ =>
        eval (seqGap a (k + j) : ℝ) (P (k + j)) / (B : ℝ) ^ (k + j + 1) := by
    simpa [add_comm k] using hshift
  have hfun :
      (fun j : ℕ =>
          eval (seqGap a (k + j) : ℝ) (P (k + j)) / (B : ℝ) ^ (j + 1)) =
        fun j => (B : ℝ) ^ k *
          (eval (seqGap a (k + j) : ℝ) (P (k + j)) /
            (B : ℝ) ^ (k + j + 1)) := by
    funext j
    have hpow : (B : ℝ) ^ (k + j + 1) = (B : ℝ) ^ (j + 1) * (B : ℝ) ^ k := by
      rw [Nat.add_assoc k j 1, add_comm k (j + 1), pow_add]
    have hBj : (B : ℝ) ^ (j + 1) ≠ 0 := pow_ne_zero (j + 1) hb0
    rw [hpow]
    field_simp [hBj]
  rw [hfun]
  exact hshift'.mul_left _

theorem seqGapPolyTail_succ {a : ℕ → ℕ} {P : ℕ → ℝ[X]} {B n : ℕ}
    (hB : 2 ≤ B)
    (hsm : Summable fun j : ℕ =>
      eval (seqGap a (n + j) : ℝ) (P (n + j)) / (B : ℝ) ^ (j + 1)) :
    seqGapPolyTail a P B (n + 1) =
      (B : ℝ) * seqGapPolyTail a P B n -
        eval (seqGap a n : ℝ) (P n) := by
  have hb0 := base_ne_zero hB
  let f : ℕ → ℝ := fun j =>
    eval (seqGap a (n + j) : ℝ) (P (n + j)) / (B : ℝ) ^ (j + 1)
  have hf : Summable f := hsm
  have hsplit : f 0 + ∑' m, f (m + 1) = ∑' m, f m := by
    simpa [sum_range_one] using hf.sum_add_tsum_nat_add 1
  have hf0 : f 0 = eval (seqGap a n : ℝ) (P n) / B := by
    simp [f]
  have hfun :
      (fun m => f (m + 1)) =
        fun m =>
          (eval (seqGap a (n + 1 + m) : ℝ) (P (n + 1 + m)) /
            (B : ℝ) ^ (m + 1)) / B := by
    funext m
    have hn : n + (m + 1) = n + 1 + m := by
      rw [← Nat.add_assoc n m 1, add_right_comm n m 1]
    have hpow : (B : ℝ) ^ ((m + 1) + 1) = (B : ℝ) ^ (m + 1) * (B : ℝ) :=
      pow_succ _ _
    simp only [f]
    rw [hn, hpow]
    field_simp [hb0, pow_ne_zero (m + 1) hb0]
  have htail : ∑' m, f (m + 1) = seqGapPolyTail a P B (n + 1) / B := by
    rw [hfun, tsum_div_const]
    rfl
  have hform : seqGapPolyTail a P B n =
      eval (seqGap a n : ℝ) (P n) / B +
        seqGapPolyTail a P B (n + 1) / B := by
    change ∑' m, f m = _
    rw [← hsplit, hf0, htail]
  have hmul := congrArg (fun x => (B : ℝ) * x) hform
  have hsimp :
      (B : ℝ) *
          (eval (seqGap a n : ℝ) (P n) / B +
            seqGapPolyTail a P B (n + 1) / B) =
        eval (seqGap a n : ℝ) (P n) + seqGapPolyTail a P B (n + 1) := by
    field_simp [hb0]
  rw [hsimp] at hmul
  linarith

theorem seqGapPolyTail_orbit_int {a : ℕ → ℕ} {P : ℕ → ℝ[X]} {B : ℕ}
    (hB : 2 ≤ B)
    (hsm : Summable fun n : ℕ =>
      eval (seqGap a n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hint : ∀ n, ∃ z : ℤ, eval (seqGap a n : ℝ) (P n) = z)
    (n : ℕ) :
    ∃ z : ℤ,
      (B : ℝ) ^ n * seqGapPolyTail a P B 0 - seqGapPolyTail a P B n = z := by
  induction n with
  | zero =>
    exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨p, hp⟩ := hint n
    refine ⟨(B : ℤ) * z + p, ?_⟩
    have hsmn := seqGapPolyTail_summable_shift hB hsm n
    have hrec := seqGapPolyTail_succ (a := a) (P := P) (B := B) (n := n) hB hsmn
    have hBpow : (B : ℝ) ^ (n + 1) = (B : ℝ) * (B : ℝ) ^ n := pow_succ' _ _
    calc
      (B : ℝ) ^ (n + 1) * seqGapPolyTail a P B 0 - seqGapPolyTail a P B (n + 1)
          = (B : ℝ) * ((B : ℝ) ^ n * seqGapPolyTail a P B 0) -
              seqGapPolyTail a P B (n + 1) := by
            rw [hBpow, mul_assoc]
      _ = (B : ℝ) * (seqGapPolyTail a P B n + z) -
            seqGapPolyTail a P B (n + 1) := by
          have : (B : ℝ) ^ n * seqGapPolyTail a P B 0 =
              seqGapPolyTail a P B n + z := by linarith
          rw [this]
      _ = (B : ℝ) * seqGapPolyTail a P B n - seqGapPolyTail a P B (n + 1) +
            (B : ℝ) * z := by
          ring
      _ = eval (seqGap a n : ℝ) (P n) + (B : ℝ) * z := by
          have : (B : ℝ) * seqGapPolyTail a P B n -
              seqGapPolyTail a P B (n + 1) =
              eval (seqGap a n : ℝ) (P n) := by linarith [hrec]
          rw [this]
      _ = (p : ℝ) + (B : ℝ) * z := by rw [hp]
      _ = (((B : ℤ) * z + p : ℤ) : ℝ) := by
          simp [Int.cast_add, Int.cast_mul]
          ring

private theorem e_orbit {a : ℕ → ℕ} {P : ℕ → ℝ[X]} {B n : ℕ} {τ : ℤ}
    (hB : 2 ≤ B)
    (hsm : Summable fun k : ℕ =>
      eval (seqGap a k : ℝ) (P k) / (B : ℝ) ^ (k + 1))
    (hint : ∀ k, ∃ z : ℤ, eval (seqGap a k : ℝ) (P k) = z) :
    e ((τ : ℝ) * (B : ℝ) ^ n * seqGapPolySeries a P B) =
      e ((τ : ℝ) * seqGapPolyTail a P B n) := by
  obtain ⟨z, hz⟩ := seqGapPolyTail_orbit_int hB hsm hint n
  have hsum :
      (τ : ℝ) * (B : ℝ) ^ n * seqGapPolySeries a P B =
        (τ : ℝ) * seqGapPolyTail a P B n + (τ : ℝ) * z := by
    unfold seqGapPolySeries
    have htail :
        (B : ℝ) ^ n * seqGapPolyTail a P B 0 =
          seqGapPolyTail a P B n + (z : ℝ) := by linarith
    calc
      (τ : ℝ) * (B : ℝ) ^ n * seqGapPolyTail a P B 0
          = (τ : ℝ) * ((B : ℝ) ^ n * seqGapPolyTail a P B 0) := by
            rw [mul_assoc]
      _ = (τ : ℝ) * (seqGapPolyTail a P B n + (z : ℝ)) := by
            rw [htail]
      _ = (τ : ℝ) * seqGapPolyTail a P B n + (τ : ℝ) * z := by
            rw [mul_add]
  rw [hsum, e_add]
  have hintτ : e ((τ : ℝ) * z) = 1 := by
    have : (τ : ℝ) * z = ((τ * z : ℤ) : ℝ) := by
      simp [Int.cast_mul]
    rw [this, e_int]
  rw [hintτ, mul_one]

/-- Cesàro vanishing of the infinite tails implies `weylCriterion`
of the polynomial series, by the integer orbit identity. -/
theorem weylCriterion_of_tailVanishing {a : ℕ → ℕ} {P : ℕ → ℝ[X]} {B : ℕ}
    (hB : 2 ≤ B)
    (hsm : Summable fun n : ℕ =>
      eval (seqGap a n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hint : ∀ n, ∃ z : ℤ, eval (seqGap a n : ℝ) (P n) = z)
    (hU : ∀ τ : ℤ, τ ≠ 0 →
      Tendsto (fun N : ℕ =>
        (∑ n ∈ range N, e ((τ : ℝ) * seqGapPolyTail a P B n)) / N)
        atTop (𝓝 0)) :
    weylCriterion B (seqGapPolySeries a P B) := by
  intro τ hτ
  have hfun :
      (fun N : ℕ =>
        (∑ n ∈ range N,
          e ((τ : ℝ) * (B : ℝ) ^ n * seqGapPolySeries a P B)) / N) =
        fun N =>
          (∑ n ∈ range N, e ((τ : ℝ) * seqGapPolyTail a P B n)) / N := by
    funext N
    congr 1
    refine sum_congr rfl fun n _ => e_orbit hB hsm hint
  rw [hfun]
  exact hU τ hτ

/-- Lipschitz remainder: average `|U-U_L| → 0` upgrades truncated
Cesàro vanishing to infinite-tail vanishing. -/
theorem tendsto_tail_of_truncated {a : ℕ → ℕ} {P : ℕ → ℝ[X]} {B : ℕ}
    (L : ℕ → ℕ) {τ : ℤ}
    (hΦ : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
        e ((τ : ℝ) * seqGapPolyTailTrunc a P B (L n) n)) / N)
      atTop (𝓝 0))
    (hrem : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
        |seqGapPolyTail a P B n -
          seqGapPolyTailTrunc a P B (L n) n|) / N)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, e ((τ : ℝ) * seqGapPolyTail a P B n)) / N)
      atTop (𝓝 0) := by
  let φ : ℕ → ℝ := fun n => seqGapPolyTail a P B n
  let U : ℕ → ℝ := fun n => seqGapPolyTailTrunc a P B (L n) n
  let bound : ℕ → ℝ := fun N =>
    (2 * Real.pi * |(τ : ℝ)|) *
      ((∑ n ∈ range N, |φ n - U n|) / N)
  have hlip :
      Tendsto (fun N : ℕ =>
        cesaroMean (fun n => e ((τ : ℝ) * φ n)) N -
          cesaroMean (fun n => e ((τ : ℝ) * U n)) N)
        atTop (𝓝 0) := by
    refine squeeze_zero_norm
      (f := fun N =>
        cesaroMean (fun n => e ((τ : ℝ) * φ n)) N -
          cesaroMean (fun n => e ((τ : ℝ) * U n)) N)
      (a := bound) (fun N => ?hbound) ?htend
    · by_cases hN : N = 0
      · subst hN
        simp [cesaroMean, bound, φ, U]
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
        have hdist :=
          cesaroMean_dist_le_avg
            (fun n => e ((τ : ℝ) * φ n))
            (fun n => e ((τ : ℝ) * U n))
            N hNpos
        have hpt : ∀ n ∈ range N,
            ‖e ((τ : ℝ) * φ n) - e ((τ : ℝ) * U n)‖ ≤
              2 * Real.pi * |(τ : ℝ)| * |φ n - U n| :=
          fun n _ => norm_e_mul_sub τ (φ n) (U n)
        have hsum :
            (∑ n ∈ range N,
              ‖e ((τ : ℝ) * φ n) - e ((τ : ℝ) * U n)‖) / N ≤
              (2 * Real.pi * |(τ : ℝ)|) *
                ((∑ n ∈ range N, |φ n - U n|) / N) := by
          have hs :=
            div_le_div_of_nonneg_right (sum_le_sum hpt) (Nat.cast_nonneg N)
          have hfact :
              (∑ n ∈ range N,
                  2 * Real.pi * |(τ : ℝ)| * |φ n - U n|) / N =
                (2 * Real.pi * |(τ : ℝ)|) *
                  ((∑ n ∈ range N, |φ n - U n|) / N) := by
            rw [← mul_sum, mul_div_assoc]
          exact hs.trans_eq hfact
        exact hdist.trans hsum
    · exact (tendsto_const_nhds.mul hrem).trans_eq (by simp [bound, φ, U])
  have htrunc :
      Tendsto (fun N : ℕ =>
        cesaroMean (fun n => e ((τ : ℝ) * U n)) N)
        atTop (𝓝 0) := by
    simpa [cesaroMean, U] using hΦ
  have hsum :
      Tendsto (fun N : ℕ =>
        cesaroMean (fun n => e ((τ : ℝ) * φ n)) N -
          cesaroMean (fun n => e ((τ : ℝ) * U n)) N +
          cesaroMean (fun n => e ((τ : ℝ) * U n)) N)
        atTop (nhds 0) := by
    simpa using hlip.add htrunc
  refine Filter.Tendsto.congr' ?_ hsum
  refine Eventually.of_forall fun N => ?_
  simp [cesaroMean, φ, U, sub_add_cancel]

/-- Truncated-phase Weyl vanishing plus Cesàro remainder control
implies `weylCriterion` of the gap-polynomial series. S/T/D produce
these inputs in the paper; they are not silent hypotheses here. -/
theorem weylCriterion_of_truncatedPhaseWeyl {a : ℕ → ℕ} {P : ℕ → ℝ[X]}
    {B : ℕ} (hB : 2 ≤ B) {L : ℕ → ℕ}
    (hsm : Summable fun n : ℕ =>
      eval (seqGap a n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hint : ∀ n, ∃ z : ℤ, eval (seqGap a n : ℝ) (P n) = z)
    (hΦ : TruncatedPhaseWeyl a P B L)
    (hrem : ∀ τ : ℤ, τ ≠ 0 →
      Tendsto (fun N : ℕ =>
        (∑ n ∈ range N,
          |seqGapPolyTail a P B n -
            seqGapPolyTailTrunc a P B (L n) n|) / N)
        atTop (𝓝 0)) :
    weylCriterion B (seqGapPolySeries a P B) :=
  weylCriterion_of_tailVanishing hB hsm hint fun τ hτ =>
    tendsto_tail_of_truncated L (hΦ τ hτ) (hrem τ hτ)

theorem seqGap_nthPrime (n : ℕ) : seqGap nthPrime n = primeGap n :=
  rfl

theorem gapPolySeries_eq_seq (P : ℕ → ℝ[X]) (B : ℕ) :
    gapPolySeries P B = seqGapPolySeries nthPrime P B := by
  unfold gapPolySeries seqGapPolySeries seqGapPolyTail
  refine tsum_congr fun j => ?_
  simp [seqGap_nthPrime, Nat.zero_add]

/-- Specialisation to `gapPolySeries`: truncated-phase Weyl vanishing
and remainder control imply the EndAPI series is Weyl-normal. -/
theorem weylCriterion_gapPolySeries_of_truncatedPhaseWeyl
    {P : ℕ → ℝ[X]} {B : ℕ} (hB : 2 ≤ B) {L : ℕ → ℕ}
    (hsm : Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hint : ∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z)
    (hΦ : TruncatedPhaseWeyl nthPrime P B L)
    (hrem : ∀ τ : ℤ, τ ≠ 0 →
      Tendsto (fun N : ℕ =>
        (∑ n ∈ range N,
          |seqGapPolyTail nthPrime P B n -
            seqGapPolyTailTrunc nthPrime P B (L n) n|) / N)
        atTop (𝓝 0)) :
    weylCriterion B (gapPolySeries P B) := by
  have hsm' : Summable fun n : ℕ =>
      eval (seqGap nthPrime n : ℝ) (P n) / (B : ℝ) ^ (n + 1) := by
    simpa [seqGap_nthPrime] using hsm
  have hint' : ∀ n, ∃ z : ℤ, eval (seqGap nthPrime n : ℝ) (P n) = z := by
    simpa [seqGap_nthPrime] using hint
  have h := weylCriterion_of_truncatedPhaseWeyl hB hsm' hint' hΦ hrem
  rwa [gapPolySeries_eq_seq]

/-- Truncated-phase vanishing plus remainder yields the Unit-clock
`JointWeyl` form of the EndAPI series. -/
theorem jointWeyl_gapPolySeries_of_truncatedPhaseWeyl
    {P : ℕ → ℝ[X]} {B : ℕ} (hB : 2 ≤ B) {L : ℕ → ℕ}
    (hsm : Summable fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1))
    (hint : ∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z)
    (hΦ : TruncatedPhaseWeyl nthPrime P B L)
    (hrem : ∀ τ : ℤ, τ ≠ 0 →
      Tendsto (fun N : ℕ =>
        (∑ n ∈ range N,
          |seqGapPolyTail nthPrime P B n -
            seqGapPolyTailTrunc nthPrime P B (L n) n|) / N)
        atTop (𝓝 0)) :
    JointWeyl (fun _ : Unit => B) (fun _ => gapPolySeries P B) :=
  jointWeyl_of_weylCriterion
    (weylCriterion_gapPolySeries_of_truncatedPhaseWeyl hB hsm hint hΦ hrem)

end PrimeGapNormality.Prime
