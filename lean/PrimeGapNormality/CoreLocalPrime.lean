import PrimeGapNormality.Prime.CorePrimeLocalNormality
import PrimeGapNormality.Prime.CoreLocalRelations
import PrimeGapNormality.Prime.CorePeriodRefinement
import PrimeGapNormality.Prime.CoreOneGapWeights
import PrimeGapNormality.Prime.CorePrimeLocalClassification
import PrimeGapNormality.Prime.CoreCommonPeriodEnd
import PrimeGapNormality.Prime.CorePeriodicPositionEnd
import PrimeGapNormality.Prime.CorePrimeLocalJointEnd
import PrimeGapNormality.Prime.CoreOneGapPolynomialEnd
import PrimeGapNormality.Prime.CoreGapPowerComponents

/-!
Curated actual local prime-gap core. The public endpoints take only the
explicit D or Kuperberg arithmetic hypothesis and the displayed finite
tuple/base/profile data. They do not accept a model-normality hypothesis.

The separately compiled precise AHL adapter, and its classical PNT import,
are deliberately isolated in `CoreAHLPrime`. This entry does not advertise
the unconditional rough backend, rounded-power or quantitative scope.
Keep `CorePrimeLocalScalarAudit` and the family audit as separate check
targets, rather than printing declarations on every downstream import.
-/
