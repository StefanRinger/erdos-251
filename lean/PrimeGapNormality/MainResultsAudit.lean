import PrimeGapNormality.MainResults

/-!
# Audit of the current accepted headline surface

These checks name actual public endpoints rather than introducing shortened
headline propositions. The import surface remains explicitly narrower than a
complete frozen-paper or release acceptance.
-/

open PrimeGapNormality.Prime

/-! Conditional prime-position normality. -/
#check @CorePeriodicPositionEnd.primePositionSeries_isNormal_of_kuperberg
#print axioms CorePeriodicPositionEnd.primePositionSeries_isNormal_of_kuperberg

/-! Conditional local classification and finite-family relations. -/
#check @corePrime_local_classification_of_D
#check @corePrime_local_classification_of_kuperberg
#check @CoreLocalRelations.jointWeyl_of_independent_normalForms_of_D
#check @CoreCommonPeriodEnd.rational_relation_iff_common_period_of_D
#print axioms corePrime_local_classification_of_kuperberg
#print axioms CoreLocalRelations.jointWeyl_of_independent_normalForms_of_D

/-! Unconditional literal moving-rough classification and position series. -/
#check @CoreRoughLogSlopeClassification.classification
#check @CoreRoughForumThreshold.normal_and_irrational
#print axioms CoreRoughLogSlopeClassification.classification
#print axioms CoreRoughForumThreshold.normal_and_irrational

/-! Literal uncountable rounded prime-gap family. -/
#check @CoreRoundedHeadline.one_Z_linearIndependent_of_kuperberg
#check @CoreRoundedHeadline.Z_isNormal_of_kuperberg
#check @CoreRoundedHeadline.finite_Z_empirical_tendsto_of_kuperberg
#print axioms CoreRoundedHeadline.one_Z_linearIndependent_of_kuperberg

/-! Quantitative star discrepancy and uniform literal digit counts. -/
#check @CorePrimeQuantitativeEnd.primePosition_starDiscrepancy_rate
#check @CorePrimeQuantitativeEnd.primePosition_literal_digit_counts
#print axioms CorePrimeQuantitativeEnd.primePosition_literal_digit_counts
