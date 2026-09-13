import PrimeGapNormality.Prime.CoreTwinIndicatorEnd

/-!
# The exact twin-prime equivalence in the scope paragraph

This statement is unconditional. Kuperberg is needed only to establish
the right-hand side, not for the equivalence itself. Both sides concern
the actual prime sequence and literal binary indicator series.
Build and end-type/axiom acceptance are recorded in the external paper ledger.
-/

namespace PrimeGapNormality.Prime.CoreTwinIndicatorEquivalence

open CoreTwinIndicatorEnd CoreTwinGapDensity CoreSparseBinarySeries
noncomputable section

theorem infinite_oneSupport_iff_infinite_twinPrimeStarts :
    Set.Infinite {n : ℕ | twinGapBit n = 1} ↔
      Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} := by
  constructor
  · intro h
    letI : Infinite {n : ℕ // twinGapBit n = 1} := Set.infinite_coe_iff.mpr h
    have hsrc : Infinite {p : ℕ // Nat.Prime p ∧ Nat.Prime (p + 2)} :=
      twinPrimeStartEquivGapOne.infinite_iff.mpr inferInstance
    exact Set.infinite_coe_iff.mp hsrc
  · intro h
    letI : Infinite {p : ℕ // Nat.Prime p ∧ Nat.Prime (p + 2)} :=
      Set.infinite_coe_iff.mpr h
    have hdst : Infinite {n : ℕ // twinGapBit n = 1} :=
      twinPrimeStartEquivGapOne.infinite_iff.mp inferInstance
    exact Set.infinite_coe_iff.mp hdst

/-- The paper's exact iff statement, with no prime-pair infinitude
hypothesis and no conjecture in the theorem type. -/
theorem twinGapBinarySeries_irrational_iff_infinite_twinPrimeStarts :
    Irrational (binarySeries twinGapBit) ↔
      Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} :=
  (binarySeries_irrational_iff_support_infinite
    twinGapBit_isBitSequence twinGapBit_hasZeroOneDensity).trans
      infinite_oneSupport_iff_infinite_twinPrimeStarts

end
end PrimeGapNormality.Prime.CoreTwinIndicatorEquivalence
