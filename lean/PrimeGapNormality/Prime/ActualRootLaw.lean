import PrimeGapNormality.Prime.StatisticalCriterion

/-!
# G0b — actual finite root-law (not unsieved Bernoulli)

For each sieve cutoff `y` the finite root-law is the pushforward of the
uniform space `Ω_y = ∏_{p≤y}{1,…,p-1}` under
`σ ↦ {n ∈ [1,S] : ∀ p≤y, n mod p ≠ σ_p}`. Root `0` always survives
(not in `[1,S]`). For `y≥2` every positive survivor is even, so any
configuration with an odd offset has mass **exactly** 0.

Independent Bernoulli retention on **all** of `{1,…,S}` is not an
asymptotic model: the odd-offset event has Bernoulli mass `1/2-o(1)`
and root-law mass 0. Do not treat `ConfigShapeDiscrepancy` /
`MixtureSieveVanishing` in that unsieved form as goals.

Correct comparison: expose at `z0`, Bernoulli-thin only the random
survivor set `A_σ₀` with `θ = rootedEulerProdNat z0 y`, then average
over `σ₀`. Coupling TV is a named Prop (`O(S²/z0)`), not an axiom.
Bounded tests only; do not transport unbounded moments.

R105 G0b. Spec regression: odd survivor mass is 0 for `y≥2`.

Source: `rounds/round105/00_grok_repair_priorities.md` G0b;
`StatisticalCriterion.ResidueChoice`; `EulerProd.rootedEulerProdNat`.
Contract: API
Audit: GREEN
-/

open Finset
open scoped Classical

namespace PrimeGapNormality.Prime

/-- Search offsets `{1,…,S}`. -/
def offsetWindow (S : ℕ) : Finset ℕ :=
  Icc 1 S

/-- Finite-window survivors of one residue choice. -/
noncomputable def sieveSurvivorsFin (y : ℕ) (σ : ResidueChoice y) (S : ℕ) :
    Finset ℕ :=
  (offsetWindow S).filter fun n => sieveSurvives y (residueOfChoice y σ) n

/-- Pushforward mass of a configuration `U ⊆ [1,S]`. -/
noncomputable def actualRootLaw (y S : ℕ) (U : Finset ℕ) : ℝ :=
  (((univ : Finset (ResidueChoice y)).filter
      fun σ => sieveSurvivorsFin y σ S = U).card : ℝ) /
    (Fintype.card (ResidueChoice y) : ℝ)

/-- Independent thinning of a **fixed** candidate set `A`.
Named `actualBernoulliThin` so it does not clash with
`Coupling.bernoulliThin` (same namespace, different arity).
No new Bernoulli mathematics: this is only a rename of the G0b mix
ingredient. Coupling keeps the original `bernoulliThin`. -/
noncomputable def actualBernoulliThin (A : Finset ℕ) (θ : ℝ)
    (U : Finset ℕ) : ℝ :=
  if U ⊆ A then
    θ ^ U.card * (1 - θ) ^ (A.card - U.card)
  else
    0

/-- Mixture of Bernoulli thinnings of the `z0`-presieve survivors. -/
noncomputable def presieveBernoulliMix (z0 y S : ℕ) (U : Finset ℕ) : ℝ :=
  (∑ σ : ResidueChoice z0,
      actualBernoulliThin (sieveSurvivorsFin z0 σ S)
        (rootedEulerProdNat z0 y) U) /
    (Fintype.card (ResidueChoice z0) : ℝ)

/-- Named coupling error. Not an axiom. Bounded-test TV only. -/
def ActualRootPresieveTV (z0 y S : ℕ) (C : ℝ) : Prop :=
  ∑ U ∈ (offsetWindow S).powerset,
      |actualRootLaw y S U - presieveBernoulliMix z0 y S U| ≤
    C * (S : ℝ) ^ 2 / (z0 : ℝ)

/-- Arithmetic model mass at a single cutoff: the actual root-law. -/
noncomputable def actualModelMass (y S : ℕ) : Finset ℕ → ℝ :=
  actualRootLaw y S

private theorem two_mem_primesLE_of_two_le {y : ℕ} (hy : 2 ≤ y) :
    2 ∈ Nat.primesLE y :=
  Nat.mem_primesLE.mpr ⟨hy, Nat.prime_two⟩

private theorem residueOfChoice_two (y : ℕ) (σ : ResidueChoice y)
    (h2 : 2 ∈ Nat.primesLE y) :
    residueOfChoice y σ 2 = 1 := by
  have hval : (σ ⟨2, h2⟩).val = 0 := Nat.lt_one_iff.mp (σ ⟨2, h2⟩).isLt
  simp [residueOfChoice, h2, hval]

private theorem odd_not_mem_sieveSurvivorsFin {y S n : ℕ}
    (hy : 2 ≤ y) (hodd : Odd n) (σ : ResidueChoice y) :
    n ∉ sieveSurvivorsFin y σ S := by
  intro hn
  have hsurv : sieveSurvives y (residueOfChoice y σ) n :=
    (mem_filter.mp hn).2
  have h2 := two_mem_primesLE_of_two_le hy
  have hne : n % 2 ≠ residueOfChoice y σ 2 := hsurv 2 h2
  have hres : residueOfChoice y σ 2 = 1 := residueOfChoice_two y σ h2
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  exact hne (hres ▸ hmod)

/-- Spec regression: odd surviving offset ⇒ mass 0 whenever `y ≥ 2`. -/
theorem actualRootLaw_eq_zero_of_odd_mem {y S n : ℕ} {U : Finset ℕ}
    (hy : 2 ≤ y) (hnU : n ∈ U) (hodd : Odd n) :
    actualRootLaw y S U = 0 := by
  have hempty :
      ((univ : Finset (ResidueChoice y)).filter
          fun σ => sieveSurvivorsFin y σ S = U) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro σ hσ
    have hU : sieveSurvivorsFin y σ S = U := (mem_filter.mp hσ).2
    exact odd_not_mem_sieveSurvivorsFin hy hodd σ (hU ▸ hnU)
  simp [actualRootLaw, hempty]

end PrimeGapNormality.Prime
