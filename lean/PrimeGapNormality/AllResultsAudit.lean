/-
# Full-paper endpoint audit surface

Compile and inspect the individual theorem-check surfaces, or their
coverage-preserving batches, before this aggregate audit. Imported audit
messages need their own recorded inspection: an aggregate .olean alone is
not evidence that every printed type was read or matches the paper.

This module declares no mathematical assumptions. The external acceptance
records identify actual source hashes, compiled endpoint types, literal
objects and transitive axioms. Historical target-contract propositions are
not substitutes for the actual theorems checked here.
-/

import PrimeGapNormality.AllResults

/- Accepted headline/conditional-prime and quantitative headline audits. -/
import PrimeGapNormality.MainResultsAudit
import PrimeGapNormality.Prime.CorePrimeLocalScalarAudit
import PrimeGapNormality.Prime.CorePaperConsequencesAudit
import PrimeGapNormality.Prime.CorePrimeQuantitativeAudit
import PrimeGapNormality.Prime.CoreRoundedHeadlineAudit

/- General S/T, real-cutoff, consequence, and eta appendix audits. -/
import PrimeGapNormality.Prime.CoreGeneralSequenceAudit
import PrimeGapNormality.Prime.CoreGeneralPositiveAudit
import PrimeGapNormality.Prime.CorePrimeGeneralBlockDiscrepancyAudit
import PrimeGapNormality.Prime.CorePrimeEtaAsymptoticsAudit
import PrimeGapNormality.Prime.CorePrimeUniformLeadingConstantAudit
import PrimeGapNormality.Prime.CorePaperWorkedExamplesAudit

/- Complete rough supplier/convention and accepted headline audits. -/
import PrimeGapNormality.Prime.CoreRoughSupplierAudit
import PrimeGapNormality.Prime.CoreRoughEveryWindowAudit
import PrimeGapNormality.Prime.CoreRoughExtendedAudit
import PrimeGapNormality.Prime.CoreMovingRoughLogGrowthAudit
import PrimeGapNormality.Prime.CoreRoughScaleDilationAudit
import PrimeGapNormality.Prime.CoreRoughFiniteConventionExtensionsAudit
import PrimeGapNormality.Prime.CoreRoughFiniteConventionConsequencesAudit
import PrimeGapNormality.Prime.CoreRoughHeadlineAudit
import PrimeGapNormality.Prime.CoreRoughLogSlopeClassificationAudit
import PrimeGapNormality.Prime.CoreRoughLittleOProfileAudit
import PrimeGapNormality.Prime.CoreRoughTripleLogProfileAudit
import PrimeGapNormality.Prime.CoreRoughTupleCountFullRangeAudit

/- Prime, arbitrary-mixture, and rough rounded audits. -/
import PrimeGapNormality.Prime.CoreRoundedPrimeAudit
import PrimeGapNormality.Prime.CoreRoundedInfiniteAudit
import PrimeGapNormality.Prime.CoreRoundedPrimeJointAudit
import PrimeGapNormality.Prime.CoreRemainingRoundedAudit
import PrimeGapNormality.Prime.CoreGeneralRoundedPositiveAudit
import PrimeGapNormality.Prime.CoreGeneralRoundedReferenceSharpAudit

/- Sharp finite auxiliary audits. -/
import PrimeGapNormality.Prime.CoreCalibratedFrameMeanSharpAudit
import PrimeGapNormality.Prime.CoreRemainingSharpAudit
import PrimeGapNormality.Prime.CoreCalibratedRetentionSharpAudit
import PrimeGapNormality.Prime.CoreCalibratedModelFiniteSharpAudit
import PrimeGapNormality.Prime.CoreCalibratedModelReferenceSharpAudit
import PrimeGapNormality.Prime.CoreResidueDominationSharpAudit
import PrimeGapNormality.Prime.CoreSelbergEquicontinuousInsertionAudit

/- Positive-density exclusion and named-example audits. -/
import PrimeGapNormality.Prime.CoreRemainingPaperExamplesAudit

/- Direct coverage of the exact mean and simultaneous all-order bound. -/
#check @PrimeGapNormality.Prime.core_rooted_sieve_gap_mean
#print axioms PrimeGapNormality.Prime.core_rooted_sieve_gap_mean
#check @PrimeGapNormality.Prime.CoreCalibratedMixtureMoments.eventually_all_countMoments_le_five
#print axioms PrimeGapNormality.Prime.CoreCalibratedMixtureMoments.eventually_all_countMoments_le_five
