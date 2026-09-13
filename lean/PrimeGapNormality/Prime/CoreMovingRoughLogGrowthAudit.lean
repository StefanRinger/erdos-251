import PrimeGapNormality.Prime.CoreMovingRoughLogGrowth

/-!
# Audit: log-linear growth of the moving-rough enumeration

The first check records the exact minimal premise: only the eventual literal
inequality `z n < n`.  The second is its direct paper-cutoff specialization.
-/

#check @PrimeGapNormality.Prime.CoreMovingRoughLogGrowth.exists_global_logLinear_bound
#check @PrimeGapNormality.Prime.CoreMovingRoughLogGrowth.exists_global_logLinear_bound_zPsi

#print axioms PrimeGapNormality.Prime.CoreMovingRoughLogGrowth.exists_global_logLinear_bound
#print axioms PrimeGapNormality.Prime.CoreMovingRoughLogGrowth.exists_global_logLinear_bound_zPsi
