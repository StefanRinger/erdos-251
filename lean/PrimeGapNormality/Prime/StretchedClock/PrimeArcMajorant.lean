import PrimeGapNormality.Prime.StretchedClock.UnitArcs
import PrimeGapNormality.Prime.StretchedClock.RestrictedAP

/-! A closed finite arithmetic supplier: actual primes in a rational arc.
The restricted Selberg AP theorem is proved upstream, not assumed here.
The modulus is at most the sieve level so every remaining prime is a unit. -/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset
open scoped Classical
noncomputable section
set_option maxHeartbeats 1000000

def primeArcSet (Y a v : ℕ) (s t : ℝ) : Finset ℕ :=
  (Icc 1 Y).filter fun p => Nat.Prime p ∧
    s ≤ (((v * p) % a : ℕ) : ℝ) / a ∧ (((v * p) % a : ℕ) : ℝ) / a < t

/-- An explicit global-height bound on a half-open rational arc.
It is uniform in the unit multiplier and the endpoints, and uses only
the actual restricted Selberg mass and actual totient. -/
theorem primeArcSet_card_le (Y a R v : ℕ) (ha : 0 < a) (hR : 1 ≤ R)
    (haR : a ≤ R) (hv : v.Coprime a)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ((primeArcSet Y a v s t).card : ℝ) ≤
      (a.totient : ℝ) * (t - s + 16 / Real.sqrt a) *
        ((Y : ℝ) / ((a : ℝ) * restrictedJ a R)) +
      (a : ℝ) * (R : ℝ) ^ 2 + R := by
  let P := primeArcSet Y a v s t
  let bad := P.filter fun p => p ≤ R
  let good := P.filter fun p => R < p
  let U := unitArcResidues a v s t
  let fiber := fun b : ℕ =>
    (Icc 1 Y).filter fun p => Nat.Prime p ∧ R < p ∧ p % a = b % a
  let D : ℝ := (Y : ℝ) / ((a : ℝ) * restrictedJ a R)
  have hD : 0 ≤ D := div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (restrictedJ_nonneg _ _))
  have hsplit : bad.card + good.card = P.card := by
    simpa only [bad, good, Nat.not_le] using
      (Finset.card_filter_add_card_filter_not (s := P) (p := fun p => p ≤ R))
  have hbad : bad.card ≤ R := by
    have hsub : bad ⊆ Icc 1 R := by
      intro p hp
      obtain ⟨hpP, hpR⟩ := mem_filter.mp hp
      have hpY := (mem_filter.mp hpP).1
      exact mem_Icc.mpr ⟨(mem_Icc.mp hpY).1, hpR⟩
    simpa using card_le_card hsub
  have hcover : good ⊆ U.biUnion fiber := by
    intro p hp
    obtain ⟨hpP, hRp⟩ := mem_filter.mp hp
    obtain ⟨hpY, hprime, hps, hpt⟩ := mem_filter.mp hpP
    have hcop : p.Coprime a := by
      apply hprime.coprime_iff_not_dvd.mpr
      intro hdvd
      have hpa := Nat.le_of_dvd ha hdvd
      omega
    have hb : p % a ∈ unitResidues a := by
      apply mem_unitResidues.mpr
      exact ⟨Nat.mod_lt _ ha, ((ZMod.coprime_mod_iff_coprime p a).mpr hcop).symm⟩
    have hmod : (v * (p % a)) % a = (v * p) % a := by
      simp only [Nat.mul_mod, Nat.mod_mod]
    have hbU : p % a ∈ U := by
      apply mem_filter.mpr
      refine ⟨hb, ?_⟩
      simpa only [hmod] using And.intro hps hpt
    apply mem_biUnion.mpr
    refine ⟨p % a, hbU, ?_⟩
    exact mem_filter.mpr ⟨hpY, hprime, hRp, by simp⟩
  have hgood : (good.card : ℝ) ≤
      (U.card : ℝ) * (D + (R : ℝ) ^ 2) := by
    calc
      (good.card : ℝ) ≤ ((U.biUnion fiber).card : ℝ) := Nat.cast_le.mpr (card_le_card hcover)
      _ ≤ ∑ b ∈ U, ((fiber b).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := U) (t := fiber))
      _ ≤ ∑ b ∈ U, (D + (R : ℝ) ^ 2) := by
        exact sum_le_sum (fun b _ => restricted_prime_ap_count_le a R Y b ha hR)
      _ = _ := by simp; ring
  have hUa : (U.card : ℝ) ≤ a := by
    have hsub : U ⊆ range a := (filter_subset _ _).trans (filter_subset _ _)
    simpa using (Nat.cast_le.mpr (card_le_card hsub) :
      (U.card : ℝ) ≤ ((range a).card : ℝ))
  have hUarc : (U.card : ℝ) ≤
      (a.totient : ℝ) * (t - s + 16 / Real.sqrt a) :=
    unitArcResidues_card_le_sqrt ha hv hs hst ht
  have hbadR : (bad.card : ℝ) ≤ R := Nat.cast_le.mpr hbad
  have hsplitR : (P.card : ℝ) = (bad.card : ℝ) + (good.card : ℝ) := by
    exact_mod_cast hsplit.symm
  change (P.card : ℝ) ≤ _
  rw [hsplitR]
  calc
    (bad.card : ℝ) + (good.card : ℝ) ≤
        (R : ℝ) + (U.card : ℝ) * (D + (R : ℝ) ^ 2) := add_le_add hbadR hgood
    _ = (U.card : ℝ) * D + (U.card : ℝ) * (R : ℝ) ^ 2 + R := by ring
    _ ≤ ((a.totient : ℝ) * (t - s + 16 / Real.sqrt a)) * D +
        (a : ℝ) * (R : ℝ) ^ 2 + R := by
      exact _root_.add_le_add
        (_root_.add_le_add (mul_le_mul_of_nonneg_right hUarc hD)
          (mul_le_mul_of_nonneg_right hUa (sq_nonneg (R : ℝ)))) le_rfl
    _ = _ := rfl

/-- The same finite supplier stated with the literal fractional part. -/
theorem prime_fract_arc_count_le (Y a R v : ℕ) (ha : 0 < a) (hR : 1 ≤ R)
    (haR : a ≤ R) (hv : v.Coprime a)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ((((Icc 1 Y).filter fun p => Nat.Prime p ∧
        s ≤ Int.fract ((v : ℝ) * (p : ℝ) / a) ∧
        Int.fract ((v : ℝ) * (p : ℝ) / a) < t).card : ℕ) : ℝ) ≤
      (a.totient : ℝ) * (t - s + 16 / Real.sqrt a) *
        ((Y : ℝ) / ((a : ℝ) * restrictedJ a R)) +
      (a : ℝ) * (R : ℝ) ^ 2 + R := by
  simpa only [fract_mul_div_eq, primeArcSet] using
    primeArcSet_card_le Y a R v ha hR haR hv hs hst ht

end
end PrimeGapNormality.Prime.StretchedClock
