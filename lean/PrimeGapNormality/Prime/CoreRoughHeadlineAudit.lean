import PrimeGapNormality.Prime.CoreRoughForumThreshold
import PrimeGapNormality.Prime.CoreRoughJointEnd
import PrimeGapNormality.Prime.CoreRoughDimensionEnd

/-! Separate final rough headline checks. Source-only until the central
build and full transitive end-type audit have actually succeeded. -/

open PrimeGapNormality.Prime

#check @CoreRoughPositionEnd.movingRoughPositionSeries_summable
#print axioms CoreRoughPositionEnd.movingRoughPositionSeries_summable
#check @CoreRoughPositionEnd.movingRoughPositionSeries_normal
#print axioms CoreRoughPositionEnd.movingRoughPositionSeries_normal
#check @CoreRoughForumThreshold.normal_and_irrational
#print axioms CoreRoughForumThreshold.normal_and_irrational
#check @CoreRoughForumThreshold.exists_positive_slope
#print axioms CoreRoughForumThreshold.exists_positive_slope
#check @CoreRoughJointEnd.empirical_tendsto
#print axioms CoreRoughJointEnd.empirical_tendsto
#check @CoreRoughJointEnd.continuous_test_tendsto
#print axioms CoreRoughJointEnd.continuous_test_tendsto
#check @CoreRoughJointEnd.box_frequency
#print axioms CoreRoughJointEnd.box_frequency
#check @CoreRoughDimensionEnd.finrank_seriesSpan
#print axioms CoreRoughDimensionEnd.finrank_seriesSpan
