import Mathlib.Order.Monotone.Basic

/-!
# Strictly increasing sequences and gaps

Paper `a_n` is Lean `a (n-1)`. Paper `g_n` is Lean `gap a (n-1)`.
-/

namespace PrimeGapNormality

/-- Canonical gap of a zero-based sequence.

Source: `rounds/round47/05_manuscript_v3.tex` (telescoping step in Lemma Mean
tails); `lean/SOURCE_LEDGER.md` Contract 1.
Contract: API (C1)
Audit: GREEN

Nat subtraction is a genuine difference only under `StrictMono a`, which
every algebraic lemma must take explicitly. -/
def gap (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  a (n + 1) - a n

/-- Positivity of gaps. Not a new mathematical claim: `StrictMono` on `ℕ`.

Source: `rounds/round47/05_manuscript_v3.tex` (telescoping step in Lemma Mean
tails); `lean/SOURCE_LEDGER.md` Contract 1.
Contract: API (C1)
Audit: GREEN

Paper `g_n` is Lean `gap a (n-1)`. -/
theorem gap_pos {a : ℕ → ℕ} (ha : StrictMono a) (n : ℕ) : 0 < gap a n := by
  simpa [gap] using Nat.sub_pos_of_lt (ha (Nat.lt_succ_self n))

/-- Cast of a gap to `ℤ` is the true difference. Used by GapAlgebra.

Source: `rounds/round47/05_manuscript_v3.tex` (telescoping step in Lemma Mean
tails); `lean/SOURCE_LEDGER.md` Contract 1.
Contract: API (C1)
Audit: GREEN

Paper `a_n` is Lean `a (n-1)`; the identity is the zero-based difference
`a (n+1) - a n` after `ℤ` cast. -/
theorem gap_int {a : ℕ → ℕ} (ha : StrictMono a) (n : ℕ) :
    (gap a n : ℤ) = (a (n + 1) : ℤ) - a n := by
  unfold gap
  exact Int.ofNat_sub (Nat.le_of_lt (ha (Nat.lt_succ_self n)))

end PrimeGapNormality
