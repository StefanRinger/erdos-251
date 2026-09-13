import PrimeGapNormality.Prime.CoreActualPattern
import PrimeGapNormality.Prime.CorePositiveComparison

/-! The frozen paper's arithmetic D quantity, with actual tuple counts.
The finite comparison below leaves a summed calibration error. It neither
assumes nor claims that this error vanishes. -/

open Finset

namespace PrimeGapNormality.Prime

noncomputable def coreJanossyTransform (Ω : Finset ℕ) (a : Finset ℕ → ℝ)
    (L r : ℕ) (K : Finset ℕ) : ℝ :=
  if hK : K.Nonempty then
    ∑ D ∈ (Stopped.beforeOutside Ω K hK).powerset.filter (fun D => D.card ≤ r - L),
      (-1 : ℝ) ^ D.card * a (K ∪ D)
  else 0

theorem coreJanossyTransform_div (Ω : Finset ℕ) (a : Finset ℕ → ℝ)
    (L r : ℕ) (K : Finset ℕ) (d : ℝ) :
    coreJanossyTransform Ω (fun H => a H / d) L r K =
      coreJanossyTransform Ω a L r K / d := by
  classical
  unfold coreJanossyTransform
  split_ifs
  · simp only [mul_div_assoc, sum_div]
  · simp

theorem coreActualPatternMass_janossy (X : ℕ) (Ω : Finset ℕ) (L r : ℕ)
    {K : Finset ℕ} (hKΩ : K ⊆ Ω) :
    Stopped.janossyTrunc Ω (coreActualPatternMass X Ω) L r K =
      coreJanossyTransform Ω (fun H => (rootedTupleCount X H : ℝ)) L r K /
        (windowNX X : ℝ) := by
  classical
  rw [← coreJanossyTransform_div]
  unfold Stopped.janossyTrunc coreJanossyTransform
  split_ifs with hK
  · apply sum_congr rfl
    intro D hD
    have hDb : D ⊆ Stopped.beforeOutside Ω K hK :=
      mem_powerset.mp (mem_filter.mp hD).1
    have hDΩ : D ⊆ Ω := hDb.trans (filter_subset _ _)
    rw [coreActualPatternMass_inclusion X (union_subset hKΩ hDΩ)]
  · rfl

/-- D_(X,c), exactly in terms of rooted tuple counts C_X and HL main terms M_X.
The window and odd stop are explicit parameters rather than a larger legacy
profile. At the prime profile the consumer supplies Ω={1,…,floor(6LG/5)}. -/
noncomputable def corePrimeComparisonQuantity (X : ℕ) (Ω : Finset ℕ)
    (L r : ℕ) (c : ℝ) : ℝ :=
  1 - (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
      coreJanossyTransform Ω (fun H => (rootedTupleCount X H : ℝ)) L r K) /
        (windowNX X : ℝ) +
    (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
      max (coreJanossyTransform Ω (fun H => (rootedTupleCount X H : ℝ)) L r K -
        c * coreJanossyTransform Ω (rootedMainTerm X) L r K) 0) /
          (windowNX X : ℝ)

/-- Identification with the finite positive-comparison budget.
Only actual probability normalization needs N_X>0. -/
theorem corePrimeComparisonQuantity_eq_budget {X : ℕ} (hN : 0 < windowNX X)
    (Ω : Finset ℕ) (L r : ℕ) (c : ℝ) :
    Stopped.stoppedPositiveBudgetAgainst Ω (coreActualPatternMass X Ω)
      (fun K => coreJanossyTransform Ω (rootedMainTerm X) L r K / (windowNX X : ℝ))
      L r c = corePrimeComparisonQuantity X Ω L r c := by
  classical
  unfold Stopped.stoppedPositiveBudgetAgainst corePrimeComparisonQuantity
  rw [coreActualPatternMass_total Ω hN]
  have hJ : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L),
      Stopped.janossyTrunc Ω (coreActualPatternMass X Ω) L r K =
        coreJanossyTransform Ω (fun H => (rootedTupleCount X H : ℝ)) L r K /
          (windowNX X : ℝ) := by
    intro K hK
    exact coreActualPatternMass_janossy X Ω L r (mem_powerset.mp (mem_filter.mp hK).1)
  rw [sum_congr rfl hJ, sum_div]
  congr 1
  rw [sum_div]
  apply sum_congr rfl
  intro K hK
  rw [hJ K hK, ← mul_div_assoc, ← sub_div]
  simpa only [zero_div] using
    max_div_div_right (Nat.cast_nonneg (windowNX X))
      (coreJanossyTransform Ω (fun H => (rootedTupleCount X H : ℝ)) L r K -
        c * coreJanossyTransform Ω (rootedMainTerm X) L r K) 0

/-- Actual positive first-L tests and actual span failure, directly from D
and an explicit signed-transform calibration error to the supplied model. -/
theorem corePrime_positive_test_le_comparisonQuantity
    {X L r : ℕ} {Ω : Finset ℕ} {ν : Finset ℕ → ℝ} {c : ℝ}
    {f : Finset ℕ → ℝ}
    (hN : 0 < windowNX X) (hL : 1 ≤ L) (hr : L ≤ r)
    (hpar : Odd (r - L)) (hc : 0 ≤ c)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U)
    (hf0 : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), 0 ≤ f K)
    (hf1 : ∀ K ∈ Ω.powerset.filter (fun K => K.card = L), f K ≤ 1) :
    Stopped.failureMass Ω (coreActualPatternMass X Ω) L +
      (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * Stopped.shortShapeMass Ω (coreActualPatternMass X Ω) L K) ≤
      c * (∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        f K * Stopped.shortShapeMass Ω ν L K) +
      corePrimeComparisonQuantity X Ω L r c +
      c * ∑ K ∈ Ω.powerset.filter (fun K => K.card = L),
        |coreJanossyTransform Ω (rootedMainTerm X) L r K / (windowNX X : ℝ) -
          Stopped.janossyTrunc Ω ν L r K| := by
  have h := Stopped.failure_add_positive_test_le_reference_budget
    (J := fun K => coreJanossyTransform Ω (rootedMainTerm X) L r K / (windowNX X : ℝ))
    hL hr hpar hc (fun U _ => coreActualPatternMass_nonneg X Ω U) hν hf0 hf1
  rwa [corePrimeComparisonQuantity_eq_budget hN Ω L r c] at h

end PrimeGapNormality.Prime
