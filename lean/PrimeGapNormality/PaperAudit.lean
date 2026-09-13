import PrimeGapNormality.AllResultsAudit
import PrimeGapNormality.Prime.StretchedClock.Audit
import PrimeGapNormality.Prime.CorePrimeCountingSeriesAudit
import PrimeGapNormality.Prime.CoreExecutableNormalFormAudit
import PrimeGapNormality.Prime.CoreWeakHLAudit
import PrimeGapNormality.Prime.CoreRoughConstantsAudit
import PrimeGapNormality.Prime.CoreRoughConsequencesAudit
import PrimeGapNormality.Prime.CoreSharpBudgetsAudit
import PrimeGapNormality.Prime.CoreCoordinateVarianceAudit
import PrimeGapNormality.Prime.CorePresieveTwoSidedAudit
import PrimeGapNormality.Prime.CoreRoughUniformDilationAudit

/-! Complete paper audit entry. Each printed type and axiom closure comes
from an actual imported theorem. Inspect the individual audit modules as
well as this collector. -/

#print PrimeGapNormality.Prime.primeCountingTerm
#print PrimeGapNormality.Prime.primeCountingSeries
#print PrimeGapNormality.Prime.CoreWeakHL.UniformError
#print PrimeGapNormality.Prime.CoreWeakHL.ahlSmall_of_uniformError
#print PrimeGapNormality.Prime.CoreWeakHL.coreLinearD_of_uniformError
#print PrimeGapNormality.Prime.CoreCyclic.Executable.evaluateNormalForm
