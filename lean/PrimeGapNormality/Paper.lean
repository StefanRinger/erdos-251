import PrimeGapNormality.AllResults
import PrimeGapNormality.Prime.StretchedClock.Normality
import PrimeGapNormality.Prime.CorePrimeCountingSeries
import PrimeGapNormality.Prime.CoreExecutableNormalFormDegree
import PrimeGapNormality.Prime.CoreWeakHLSharp
import PrimeGapNormality.Prime.CoreRoughConsequences
import PrimeGapNormality.Prime.CoreSharpBudgets
import PrimeGapNormality.Prime.CorePresieveTwoSided
import PrimeGapNormality.Prime.CoreRoughUniformDilation

/-! Complete paper entry point. Includes the main results and the
prime-counting identity, executable normal form and minimum degree, weaker
uniform HL supplier, common roughness constants and finite probability
estimates. The default build includes this module and `PaperAudit`.
An import collector alone is not evidence of theorem coverage: inspect
the actual endpoint types and the source-matched audit. -/
