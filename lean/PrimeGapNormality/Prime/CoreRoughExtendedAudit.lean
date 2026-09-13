import PrimeGapNormality.Prime.CoreRoughEveryWindow
import PrimeGapNormality.Prime.CoreRoughAnyRhoTail
import PrimeGapNormality.Prime.CoreRoughEnumerationDensity
import PrimeGapNormality.Prime.CoreRoughFiniteConvention

/-!
# Extended actual rough-supplier audit

Complete public end-type and transitive-axiom surface for the remaining
every-window, every-fixed-tail-base, density/inversion, and finite-initial-
convention clauses. Source-only until centrally compiled and inspected.
-/

open PrimeGapNormality.Prime

/-! ## Literal every-M comparison -/

#print CoreRoughEveryWindow.logGap
#print CoreRoughEveryWindow.smallSpan
#print CoreRoughEveryWindow.prefixMean

#check @CoreRoughEveryWindow.eventually_prefix_comparison
#print axioms CoreRoughEveryWindow.eventually_prefix_comparison
#check @CoreRoughEveryWindow.eventually_prefix_comparison_of_sqrt_error
#print axioms CoreRoughEveryWindow.eventually_prefix_comparison_of_sqrt_error
#check @CoreRoughEveryWindow.exact_dirac_calibration
#print axioms CoreRoughEveryWindow.exact_dirac_calibration

/-! ## Every fixed rho and the paper's actual Euler scale -/

#print CoreRoughAnyRhoTail.syntheticGap

#check @CoreRoughAnyRhoTail.movingRough_meanGapTailT_any_rho
#print axioms CoreRoughAnyRhoTail.movingRough_meanGapTailT_any_rho
#check @CoreRoughAnyRhoTail.movingRough_meanGapTailT_roughScale
#print axioms CoreRoughAnyRhoTail.movingRough_meanGapTailT_roughScale
#check @CoreRoughAnyRhoTail.movingRough_gapTailT_any_rho
#print axioms CoreRoughAnyRhoTail.movingRough_gapTailT_any_rho
#check @CoreRoughAnyRhoTail.movingRough_gapTailT_roughScale
#print axioms CoreRoughAnyRhoTail.movingRough_gapTailT_roughScale

/-! ## Global count, density inversion, and doubling -/

#print CoreRoughInitialCount.initialCount
#print CoreRoughEnumerationDensity.roughEnumeration

#check @CoreRoughInitialCount.tendsto_initialCountNormalized_one
#print axioms CoreRoughInitialCount.tendsto_initialCountNormalized_one
#check @CoreRoughEnumerationDensity.tendsto_roughEnumeration_div_densityScale_one
#print axioms CoreRoughEnumerationDensity.tendsto_roughEnumeration_div_densityScale_one
#check @CoreRoughEnumerationDensity.eventually_roughEnumeration_fourDoubling
#print axioms CoreRoughEnumerationDensity.eventually_roughEnumeration_fourDoubling

/-! ## Arbitrary fixed finite initial convention -/

#check @CoreRoughFiniteConvention.sequencePositiveShapeS
#print axioms CoreRoughFiniteConvention.sequencePositiveShapeS
#check @CoreRoughFiniteConvention.meanGapTailT
#print axioms CoreRoughFiniteConvention.meanGapTailT
#check @CoreRoughFiniteConvention.gapTailT
#print axioms CoreRoughFiniteConvention.gapTailT
#check @CoreRoughFiniteConvention.local_rational_iff_normalForm_zero
#print axioms CoreRoughFiniteConvention.local_rational_iff_normalForm_zero
#check @CoreRoughFiniteConvention.local_classification
#print axioms CoreRoughFiniteConvention.local_classification
#check @CoreRoughFiniteConvention.eventually_prefix_comparison
#print axioms CoreRoughFiniteConvention.eventually_prefix_comparison
#check @CoreRoughFiniteConvention.eventually_prefix_comparison_of_sqrt_error
#print axioms CoreRoughFiniteConvention.eventually_prefix_comparison_of_sqrt_error
