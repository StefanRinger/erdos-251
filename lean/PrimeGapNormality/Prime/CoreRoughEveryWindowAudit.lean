import PrimeGapNormality.Prime.CoreRoughEveryWindow

/-!
# Actual every-window rough comparison: standalone audit surface

This can be accepted independently of the later finite-initial-convention
and arbitrary-rho adapters. Compilation and inspection remain separate
from merely importing this file.
-/

open PrimeGapNormality.Prime

#print CoreRoughEveryWindow.logGap
#print CoreRoughEveryWindow.smallSpan
#print CoreRoughEveryWindow.prefixMean
#print CoreRoughEveryWindow.complexMean
#print actualRootLaw

#check @CoreRoughFullShapeComparison.tendsto_fullShapeError_zero
#print axioms CoreRoughFullShapeComparison.tendsto_fullShapeError_zero
#check @CoreRoughEveryWindow.eventually_prefix_comparison
#print axioms CoreRoughEveryWindow.eventually_prefix_comparison
#check @CoreRoughEveryWindow.eventually_prefix_comparison_of_sqrt_error
#print axioms CoreRoughEveryWindow.eventually_prefix_comparison_of_sqrt_error
#check @CoreRoughEveryWindow.exact_dirac_calibration
#print axioms CoreRoughEveryWindow.exact_dirac_calibration
