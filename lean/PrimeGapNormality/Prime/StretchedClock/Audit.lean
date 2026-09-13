import PrimeGapNormality.Prime.StretchedClock.Normality

/-! Final end-type/axiom gate. The file must actually compile before the
stretched-clock appendix is included in any full-formalization claim. -/

open PrimeGapNormality.Prime.StretchedClock

#print value
#print realStep
#print step
#print position
#print PrimeGapNormality.BFree.IsNormal
#check @value_summable
#print axioms value_summable
#check @position_isEquivalent_index_loglog
#print axioms position_isEquivalent_index_loglog
#check @exists_prime_fract_arc_bound
#print axioms exists_prime_fract_arc_bound
#check @exists_positive_prefix_bound
#print axioms exists_positive_prefix_bound
#check @value_isNormal
#print axioms value_isNormal
