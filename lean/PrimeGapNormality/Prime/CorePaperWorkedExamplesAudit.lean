import PrimeGapNormality.Prime.CorePaperWorkedExamples

/-!
Audit surface for the two explicit period-one worked examples in the paper.
This file deliberately prints only the final algebraic identities and the
two concrete normality consumers.
-/

namespace PrimeGapNormality.Prime

#check @CorePaperWorkedExamples.primeGap_zero
#print axioms CorePaperWorkedExamples.primeGap_zero

#check @CorePaperWorkedExamples.telescopingNumerator_apply
#check @CorePaperWorkedExamples.normalForm_telescopingNumerator
#check @CorePaperWorkedExamples.fullSeries_Bu0_sub_u1
#print axioms CorePaperWorkedExamples.fullSeries_Bu0_sub_u1

#check @CorePaperWorkedExamples.degreeDropNumerator_apply
#check @CorePaperWorkedExamples.normalForm_degreeDropNumerator
#check @CorePaperWorkedExamples.topDegree_normalForm_degreeDropNumerator
#check @CorePaperWorkedExamples.fullSeries_degreeDropNumerator
#print axioms CorePaperWorkedExamples.fullSeries_degreeDropNumerator

#check @CorePaperWorkedExamples.degreeDrop_isNormal_of_D
#print axioms CorePaperWorkedExamples.degreeDrop_isNormal_of_D

#check @CorePaperWorkedExamples.degreeDrop_isNormal_of_kuperberg
#print axioms CorePaperWorkedExamples.degreeDrop_isNormal_of_kuperberg

end PrimeGapNormality.Prime
