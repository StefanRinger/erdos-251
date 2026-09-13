import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

/-!
# Named arithmetic hypotheses (not axioms)

Source: `rounds/round96/01_gpt_standard_hl_gap_merger.md` §2;
`rounds/round97/01_gpt_khl_merger_independent_audit.md` §§1–2, 10;
`lean/PRIME_SIGNATURES.md` Hypotheses.
Contract: API
Audit: GREEN

Kuperberg Conj. 1.3, intended Tao Conj. 1.3, and a fixed-`B` BFT
parameter slice are later adapters. They are not theorems and not
`axiom`s. Finite kernel lemmas take an explicit discrepancy `δ`.
-/

namespace PrimeGapNormality.Prime

open Finset

/-- Constants of the restricted uniform tuple-count input actually
consumed by the window transfer (R96 §2.2). The counting statement
itself is supplied by a later adapter, not by this structure. -/
structure RestrictedUHL where
  ε : ℝ
  C : ℝ
  Ak : ℝ
  AS : ℝ
  hε : 0 < ε
  hC : 0 ≤ C
  hAk : 0 < Ak
  hAS : 0 < AS

/-- Finite-window inclusion discrepancy: every pattern of size at most
`r+1` differs by at most `δ` between two mass functions on subsets.
This is the local hypothesis the Möbius TV lemma consumes. -/
def InclusionDiscrepancy {α : Type*} [DecidableEq α]
    (S : Finset α) (μ ν : Finset α → ℝ) (r : ℕ) (δ : ℝ) : Prop :=
  ∀ H : Finset α, H ⊆ S → H.card ≤ r + 1 → |μ H - ν H| ≤ δ

/-- One-sided alternating stopped HL mean error, R99/01 (7.2).
`C H` is a raw tuple count, `M H` a main term; both include the root,
so prime-tuple order is `j+1`. Independently audited in R99/06.
This is an open prime hypothesis: not an `axiom`, and **not** implied
by the constants-only `RestrictedUHL` stub. -/
def AlternatingStoppedHL {α : Type*} [DecidableEq α]
    (S : Finset α) (C M : Finset α → ℝ) (L r : ℕ) (ε : ℝ) : Prop :=
  ∀ j : ℕ, L ≤ j → j ≤ r →
    (∑ H ∈ S.powerset.filter (fun H => H.card = j),
        max (((-1 : ℝ) ^ (j - L + 1)) * (C H - M H)) 0)
      ≤ ε * ∑ H ∈ S.powerset.filter (fun H => H.card = j), M H

end PrimeGapNormality.Prime
