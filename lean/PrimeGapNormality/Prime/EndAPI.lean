import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Frozen end-theorem API (definitions only)

Shared signatures for the R104/07 assembly. No end theorem is proved
here. `weylCriterion` (in `Fourier`) is the project's base-`b`
normality. Do not weaken that name.

Indexing: `nthPrime 0 = 2` is paper `p_1`. Series start at
`/ B^(n+1)` so the `n = 0` term is the first paper summand.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` §§1–2, (eq:khl),
(eq:ahl), (eq:theta); `rounds/round104/07_grok_full_normality_implementation_order.md`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Polynomial

/-! ### Prime enumeration and series -/

/-- 0-based prime enumeration: `nthPrime 0 = 2`. -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- Consecutive prime gap `g_{n+1}` in paper indexing. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  nthPrime (n + 1) - nthPrime n

/-- Position series `∑_{n≥1} p_n B^{-n}`. -/
noncomputable def primePosSeries (B : ℕ) : ℝ :=
  ∑' n : ℕ, (nthPrime n : ℝ) / (B : ℝ) ^ (n + 1)

/-- Gap-power series `∑_{n≥1} g_n^d B^{-n}`. -/
noncomputable def primeGapPowerSeries (B d : ℕ) : ℝ :=
  ∑' n : ℕ, ((primeGap n : ℝ) ^ d) / (B : ℝ) ^ (n + 1)

/-- Periodic (or arbitrary) one-gap polynomial series. Periodicity of
`P` is a lemma hypothesis, not part of the definition. -/
noncomputable def gapPolySeries (P : ℕ → ℝ[X]) (B : ℕ) : ℝ :=
  ∑' n : ℕ, eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1)

/-- Coerce a rational polynomial to a real polynomial. -/
noncomputable def mapRatPoly (P : ℚ[X]) : ℝ[X] :=
  P.map (algebraMap ℚ ℝ)

/-- Rational-coefficient gap polynomial series. -/
noncomputable def gapRatPolySeries (P : ℕ → ℚ[X]) (B : ℕ) : ℝ :=
  gapPolySeries (fun n => mapRatPoly (P n)) B

/-- 0-based residue/start: paper `Θ_{r+1,d}(n+1)`.
`C^{-m-1}` with `C = B^k` is `B^{-k(m+1)}`. -/
noncomputable def gapPowerTheta (B k r d n : ℕ) : ℝ :=
  ∑' m : ℕ, ((primeGap (n + k * m + r) : ℝ) ^ d) / (B : ℝ) ^ (k * (m + 1))

/-- Paper `W_{r+1,d} = B^{k-(r+1)} Θ_{r+1,d}(1)`, Lean 0-based `r`. -/
noncomputable def gapPowerComponent (B k r d : ℕ) : ℝ :=
  (B : ℝ) ^ (k - 1 - r) * gapPowerTheta B k r d 0

/-! ### Hardy–Littlewood singular series and Kuperberg 1.3 -/

/-- Residue count `ν_E(p) = |E mod p|`. -/
noncomputable def residueCount (E : Finset ℕ) (p : ℕ) : ℕ :=
  (E.image fun h : ℕ => (h : ZMod p)).card

/-- Admissible in the Hardy–Littlewood sense. -/
def hlAdmissible (E : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → residueCount E p < p

/-- Local Euler factor of the singular series. For `p = 0, 1` the
value is unused by products over primes. -/
noncomputable def localHLFactor (E : Finset ℕ) (p : ℕ) : ℝ :=
  if p ≤ 1 then 1
  else
    (1 - (residueCount E p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ E.card

/-- Singular series `𝔖(E)` as an infinite product over `n`, with
non-prime factors equal to `1`. -/
noncomputable def singularSeries (E : Finset ℕ) : ℝ :=
  ∏' n : ℕ, if Nat.Prime n then localHLFactor E n else 1

/-- Tuple count `#{n ≤ x | n+E ⊂ primes}`. -/
noncomputable def hlCount (x : ℕ) (E : Finset ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => ∀ h ∈ E, Nat.Prime (n + h)).card

/-- Logarithmic integral factor `∫_2^x (log t)^{-k} dt`. -/
noncomputable def hlIntegral (x : ℝ) (k : ℕ) : ℝ :=
  ∫ t in (2 : ℝ)..x, Real.log t ^ (-(k : ℝ))

/-- Main term `𝔖(E) ∫_2^x (log t)^{-|E|} dt`. -/
noncomputable def hlMain (x : ℝ) (E : Finset ℕ) : ℝ :=
  singularSeries E * hlIntegral x E.card

/-- Kuperberg's Conjecture 1.3 (indicator form, paper (eq:khl)).
Named `Prop`, not an `axiom`. Threshold `16` makes `log log x > 0`. -/
def KuperbergConj13 : Prop :=
  ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
    ∀ (x : ℕ) (E : Finset ℕ),
      16 ≤ x →
      (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
      (E.card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 →
      hlAdmissible E →
      |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤ K * (x : ℝ) ^ (1 - ε)

/-! ### Window counts and the aggregated AHL budget -/

/-- Paper `C_X(H)`: rooted tuples in `(X, 2X]`. -/
noncomputable def rootedTupleCount (X : ℕ) (H : Finset ℕ) : ℕ :=
  ((Finset.Ioc X (2 * X)).filter
      fun n => Nat.Prime n ∧ ∀ h ∈ H, Nat.Prime (n + h)).card

/-- Paper `M_X(H)`. -/
noncomputable def rootedMainTerm (X : ℕ) (H : Finset ℕ) : ℝ :=
  singularSeries (insert 0 H) * hlIntegral (2 * X : ℝ) (H.card + 1) -
    singularSeries (insert 0 H) * hlIntegral (X : ℝ) (H.card + 1)

/-- `G = log X`, with a floor at `1` so small `X` are well-defined. -/
noncomputable def windowG (X : ℕ) : ℝ :=
  max (Real.log (X : ℝ)) 1

/-- Paper `L = ⌈κ log G + √(κ log G)⌉`. -/
noncomputable def profileL (κ : ℝ) (X : ℕ) : ℕ :=
  ⌈κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X))⌉₊

/-- Paper `S = ⌊4 L G⌋`. -/
noncomputable def profileS (κ : ℝ) (X : ℕ) : ℕ :=
  ⌊(4 : ℝ) * profileL κ X * windowG X⌋₊

/-- Least `r ≥ max(L, ⌈d₀ L⌉)` with `r - L` odd. -/
noncomputable def profileR (L : ℕ) (d0 : ℝ) : ℕ :=
  let t := max L ⌈d0 * (L : ℝ)⌉₊
  if Odd (t - L) then t else t + 1

/-- Search window `Ω_X = {1,…,S}`. -/
noncomputable def windowOmega (κ : ℝ) (X : ℕ) : Finset ℕ :=
  Finset.Icc 1 (profileS κ X)

/-- Dyadic prime count `N_X = π(2X) - π(X)`. -/
noncomputable def windowNX (X : ℕ) : ℕ :=
  Nat.primeCounting (2 * X) - Nat.primeCounting X

/-- One layer of the aggregated positive-part budget. -/
noncomputable def ahlLayer (κ : ℝ) (X j L : ℕ) : ℝ :=
  ∑ H ∈ (windowOmega κ X).powerset.filter fun H => H.card = j,
    (((-1 : ℝ) ^ (j - L + 1)) *
      ((rootedTupleCount X H : ℝ) - rootedMainTerm X H))⁺

/-- Paper `ℰ_X` with cutoff constant `d0`. -/
noncomputable def ahlBudget (κ d0 : ℝ) (X : ℕ) : ℝ :=
  let L := profileL κ X
  let r := profileR L d0
  if windowNX X = 0 then 1
  else
    (1 / (windowNX X : ℝ)) *
      ∑ j ∈ Finset.Icc L r, ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L

/-- Aggregated one-sided hypothesis `AHL_κ` (paper (eq:ahl)), with
explicit Bonferroni cutoff `d0`. -/
def AHL (κ d0 : ℝ) : Prop :=
  Filter.Tendsto (fun X : ℕ => ahlBudget κ d0 X) Filter.atTop (nhds 0)

/-- Kuperberg supplies every fixed profile: every `κ > 0` and every
cutoff `d0 > 0`. -/
def KuperbergImpliesAHL : Prop :=
  KuperbergConj13 → ∀ κ d0 : ℝ, 0 < κ → 0 < d0 → AHL κ d0

end PrimeGapNormality.Prime
