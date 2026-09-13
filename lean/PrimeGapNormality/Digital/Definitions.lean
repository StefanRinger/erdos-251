import PrimeGapNormality.Basic.Sequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Defs

/-!
# Finite digital objects: partial sums, phase, mod-one, circle character, mean

Finite sums use exclusive-end index sets (`Finset.range` / `Ico`). The
inclusive interval `Icc 0 N` is reserved for the position partial sum `A_N`
in GapAlgebra.
-/

open Finset

namespace PrimeGapNormality

/-- Finite gap partial sum `B_K` (Contract 2). Empty at `K = 0`.

Source: `rounds/round47/audit_fst_normality_certificate.py` `test_abel_identity`;
`lean/SOURCE_LEDGER.md` Contract 2.
Contract: API (C2)
Audit: GREEN -/
def gapPartial (a : ℕ → ℕ) (b : ℕ) (K : ℕ) : ℚ :=
  ∑ n ∈ range K, (gap a n : ℚ) / (b : ℚ) ^ (n + 1)

/-- Finite tail phase beginning at first-gap index `j`, length `J`.
Belongs to the anchor `a (j+1)`. Empty at `J = 0`.

Source: `rounds/round47/05_manuscript_v3.tex` (11.2) / ALG-T;
`rounds/round51/00_status.md` §1.3 with GPT first-gap indexing;
`lean/SOURCE_LEDGER.md` Contract 3.
Contract: API (C3)
Audit: GREEN -/
def phase (a : ℕ → ℕ) (b : ℕ) (j J : ℕ) : ℚ :=
  ∑ i ∈ range J, (gap a (j + i) : ℚ) / (b : ℚ) ^ (i + 1)

/-- Integer prefix of the first `j` gaps, as an explicit `ℤ` witness.
Empty at `j = 0`.

Source: same as `phase` (finite decomposition in Contract 3).
Contract: API (C3)
Audit: GREEN -/
def integerPrefix (a : ℕ → ℕ) (b : ℕ) (j : ℕ) : ℤ :=
  ∑ n ∈ range j, (gap a n : ℤ) * (b : ℤ) ^ (j - 1 - n)

/-- Congruence modulo one by an explicit integer offset, not a quotient.

Source: `lean/PROMPT_GROK46_EXTRA_HIGH.md` representation rule 4;
`lean/SOURCE_LEDGER.md` Contract 3.
Contract: API (C3)
Audit: GREEN -/
def IntOffset (x y : ℝ) : Prop :=
  ∃ k : ℤ, x - y = (k : ℝ)

/-- Circle character `e(x) = exp(2πi x)`.

Source: `lean/PROMPT_GROK46_EXTRA_HIGH.md` representation rule 4.
Contract: API (C3)
Audit: GREEN -/
noncomputable def e (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * x)

/-- Finite complex mean. The nonempty proof is part of the type (no empty
default).

Source: `lean/PROMPT_GROK46_EXTRA_HIGH.md` representation rule 6;
`lean/SOURCE_LEDGER.md` Contract 7.
Contract: API (C7)
Audit: GREEN -/
noncomputable def mean {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℂ) : ℂ :=
  have : 0 < s.card := hs.card_pos
  (∑ i ∈ s, f i) / (s.card : ℂ)

end PrimeGapNormality
