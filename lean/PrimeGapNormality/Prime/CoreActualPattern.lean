import PrimeGapNormality.Prime.StoppedPrime

/-! The actual prime configuration law on an arbitrary finite offset window.
Unlike the historical `actualConfigMass`, this does not fix the window to
`4 L G`; the frozen `(6/5) L G` window can be supplied directly. -/

open Finset

namespace PrimeGapNormality.Prime

noncomputable def corePrimeRoots (X : ℕ) : Finset ℕ :=
  (Ioc X (2 * X)).filter Nat.Prime

noncomputable def coreActualPattern (Ω : Finset ℕ) (n : ℕ) : Finset ℕ :=
  Ω.filter (fun h => Nat.Prime (n + h))

noncomputable def coreActualPatternMass (X : ℕ) (Ω U : Finset ℕ) : ℝ :=
  (∑ n ∈ corePrimeRoots X, if coreActualPattern Ω n = U then (1 : ℝ) else 0) /
    (windowNX X : ℝ)

theorem coreActualPattern_mem (Ω : Finset ℕ) (n : ℕ) :
    coreActualPattern Ω n ∈ Ω.powerset :=
  mem_powerset.mpr (filter_subset _ _)

theorem coreActualPatternMass_nonneg (X : ℕ) (Ω U : Finset ℕ) :
    0 ≤ coreActualPatternMass X Ω U := by
  classical
  unfold coreActualPatternMass
  exact div_nonneg (sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (Nat.cast_nonneg _)

/-- Exact finite pushforward identity, including the zero-denominator case. -/
theorem coreActualPatternMass_eval (X : ℕ) (Ω : Finset ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ U ∈ Ω.powerset, coreActualPatternMass X Ω U * f U) =
      (∑ n ∈ corePrimeRoots X, f (coreActualPattern Ω n)) / (windowNX X : ℝ) := by
  classical
  unfold coreActualPatternMass
  simp_rw [div_mul_eq_mul_div, sum_mul]
  rw [← sum_div, sum_comm]
  congr 1
  apply sum_congr rfl
  intro n hn
  simp only [ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq, if_pos (coreActualPattern_mem Ω n)]

theorem coreActualPatternMass_total {X : ℕ} (Ω : Finset ℕ)
    (hN : 0 < windowNX X) :
    (∑ U ∈ Ω.powerset, coreActualPatternMass X Ω U) = 1 := by
  have h := coreActualPatternMass_eval X Ω (fun _ => 1)
  have hcard : (corePrimeRoots X).card = windowNX X :=
    (windowNX_eq_card_primes X).symm
  have hden : (windowNX X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simpa only [mul_one, sum_const, nsmul_one, hcard,
    div_self hden] using h

theorem coreActualPattern_subset_iff {Ω H : Finset ℕ} (hH : H ⊆ Ω) (n : ℕ) :
    H ⊆ coreActualPattern Ω n ↔ ∀ h ∈ H, Nat.Prime (n + h) := by
  constructor
  · intro hsub h hh
    exact (mem_filter.mp (hsub hh)).2
  · intro hp h hh
    exact mem_filter.mpr ⟨hH hh, hp h hh⟩

/-- The actual law supplies exactly C_X(H)/N_X, at the supplied window. -/
theorem coreActualPatternMass_inclusion (X : ℕ) {Ω H : Finset ℕ}
    (hH : H ⊆ Ω) :
    Stopped.inclusionMass Ω (coreActualPatternMass X Ω) H =
      (rootedTupleCount X H : ℝ) / (windowNX X : ℝ) := by
  classical
  have h := coreActualPatternMass_eval X Ω (fun U => if H ⊆ U then 1 else 0)
  have hleft :
      (∑ U ∈ Ω.powerset, coreActualPatternMass X Ω U * (if H ⊆ U then 1 else 0)) =
        Stopped.inclusionMass Ω (coreActualPatternMass X Ω) H := by
    simp [Stopped.inclusionMass, sum_filter]
  rw [hleft] at h
  rw [h]
  congr 1
  simp_rw [coreActualPattern_subset_iff hH]
  rw [sum_boole]
  congr 1
  unfold corePrimeRoots rootedTupleCount
  rw [filter_filter]

end PrimeGapNormality.Prime
