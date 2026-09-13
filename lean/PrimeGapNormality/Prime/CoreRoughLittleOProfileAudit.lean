import PrimeGapNormality.Prime.CoreRoughLittleOProfile

/-! Source-level audit surface for the universal little-o rough profile. -/

namespace PrimeGapNormality.Prime.CoreRoughLittleOProfileAudit

#check @CoreRoughLittleOProfile.HasLittleOSlopeProfile
#print CoreRoughLittleOProfile.HasLittleOSlopeProfile

#check @CoreRoughLittleOProfile.HasLittleOSlopeProfile.hasSlopeBudget
#print axioms CoreRoughLittleOProfile.HasLittleOSlopeProfile.hasSlopeBudget

#check @CoreRoughLittleOProfile.HasLittleOSlopeProfile.hasSlopeBudget_all
#print axioms CoreRoughLittleOProfile.HasLittleOSlopeProfile.hasSlopeBudget_all

#check @CoreRoughLittleOProfile.movingRough_local_classification
#print axioms CoreRoughLittleOProfile.movingRough_local_classification

end PrimeGapNormality.Prime.CoreRoughLittleOProfileAudit
