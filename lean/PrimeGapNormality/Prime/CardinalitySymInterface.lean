import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# v0.6 — cardinality-symmetric finite mass (shared interface)

Paper `eq:exchangeable`: on a fixed candidate set `A`, configurations
of equal cardinality have equal mass. No de Finetti, no abstract
conditional probability, no infinite exchangeability.

This leaf imports neither `Coupling` nor `ActualRootLaw`, so both the
late-root owner and the spacing/frame owner can use it without the
`bernoulliThin` name clash.

Source: `rounds/round108/06_grok_exact_symmetry_and_st_delta.md` §2.2.
Contract: API
Audit: GREEN
-/

open Finset

namespace PrimeGapNormality.Prime

/-- Finite mass on `A.powerset` that depends only on cardinality. -/
def CardinalitySymmetricMass (A : Finset ℕ) (μ : Finset ℕ → ℝ) : Prop :=
  (∀ E ∈ A.powerset, 0 ≤ μ E) ∧
    (∑ E ∈ A.powerset, μ E = 1) ∧
      ∀ E F : Finset ℕ, E ⊆ A → F ⊆ A → E.card = F.card → μ E = μ F

/-- Layer mass `p_n = ∑_{|E|=n} μ(E)`. -/
noncomputable def cardinalityLayer (A : Finset ℕ) (μ : Finset ℕ → ℝ)
    (n : ℕ) : ℝ :=
  ∑ E ∈ A.powerset.filter (fun E => E.card = n), μ E

/-- Uniform n-subset weight `p_n / binom(M,n)`. Zero when the binomial
vanishes (`n > M` or `M = n = 0` is handled by `Nat.choose`). Do not
invent a positive conditioning event at `p_n = 0`. -/
noncomputable def uniformLayerWeight (A : Finset ℕ) (μ : Finset ℕ → ℝ)
    (n : ℕ) : ℝ :=
  if h : n ≤ A.card ∧ 0 < Nat.choose A.card n then
    cardinalityLayer A μ n / (Nat.choose A.card n : ℝ)
  else
    (0 : ℝ)

theorem uniformLayerWeight_eq_zero_of_choose_eq_zero
    (A : Finset ℕ) (μ : Finset ℕ → ℝ) {n : ℕ}
    (h : Nat.choose A.card n = 0) :
    uniformLayerWeight A μ n = 0 := by
  unfold uniformLayerWeight
  split_ifs with hpos
  · exact (lt_irrefl _ (hpos.2.trans_eq h)).elim
  · rfl

end PrimeGapNormality.Prime
