import PrimeGapNormality.Prime.KuperbergAHL
import Mathlib.Tactic.NormNum

/-!
# G — uniform Kuperberg singleton (`exists ε,K, forall x`)

`KuperbergConj13` already packages **one** pair `ε,K` ranging over all
admissible tuples. `kuperberg_one_point` re-unpacks per `x` and must not
be used as a uniform estimate.

This leaf keeps the shared constants and specialises to `E = {0}`, i.e.
`π(x) = li(x) + O(x^{1-ε})`. No Wiener–Ikehara on this path.
`PrimeCountingAsymp` / `IndexPassageD` glue stays in `IndexPassageFromPNT`.

R105 G.

Source: `rounds/round105/00_grok_repair_priorities.md` G;
`EndAPI.KuperbergConj13`; `KuperbergAHL.kuperberg_one_point`.
Contract: API
Audit: GREEN
-/

open Finset

namespace PrimeGapNormality.Prime

/-- Shared `ε,K` from `hK`, then the singleton bound for every `x ≥ 16`. -/
theorem kuperberg_singleton_uniform (hK : KuperbergConj13) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
      ∀ {x : ℕ}, 16 ≤ x →
        |(Nat.primeCounting x : ℝ) - hlMain (x : ℝ) {0}| ≤
          K * (x : ℝ) ^ (1 - ε) := by
  obtain ⟨ε, K, hε, hKpos, hbound⟩ := hK
  refine ⟨ε, K, hε, hKpos, ?_⟩
  intro x hx
  have hcard :
      (({0} : Finset ℕ).card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 := by
    rw [card_singleton]
    exact_mod_cast (one_le_log_log_pow_three hx)
  have hdiam : ∀ h ∈ ({0} : Finset ℕ), (h : ℝ) ≤ Real.log (x : ℝ) ^ 2 := by
    intro h hh
    have : h = 0 := mem_singleton.mp hh
    subst this
    simpa using sq_nonneg (Real.log (x : ℝ))
  have := hbound x {0} hx hdiam hcard hlAdmissible_singleton_zero
  simpa [hlCount_singleton_zero] using this

end PrimeGapNormality.Prime
