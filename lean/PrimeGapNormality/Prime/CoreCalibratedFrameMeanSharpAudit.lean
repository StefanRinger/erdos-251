import PrimeGapNormality.Prime.CoreCalibratedFrameMeanSharp

/-! Source-only audit, pending central compilation and inspection.
The limiting mean two is separate from the still sharper rectangle 8^r.
-/

namespace PrimeGapNormality.Prime
set_option pp.universes false in
#check @CoreCalibratedFrameMeanSharp.eventually_coordinate_le_two_add
set_option pp.universes false in
#check @CoreCalibratedFrameMeanSharp.coordinate_integral_le_two
set_option pp.universes false in
#check @CoreCalibratedFrameMeanSharp.exists_joint_limit_mean_two
#print axioms CoreCalibratedFrameMeanSharp.eventually_coordinate_le_two_add
#print axioms CoreCalibratedFrameMeanSharp.coordinate_integral_le_two
#print axioms CoreCalibratedFrameMeanSharp.exists_joint_limit_mean_two
end PrimeGapNormality.Prime
