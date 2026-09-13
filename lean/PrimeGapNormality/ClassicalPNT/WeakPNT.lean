import PrimeGapNormality.ClassicalPNT.Wiener

/-!
Candidate public wrapper for the pinned classical weak prime number theorem.
This module is source-staged only until the separate compiler and axiom audit succeeds.
-/

namespace PrimeGapNormality.ClassicalPNT

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set LSeries
open scoped Topology

/-- Pinned upstream Wiener-Ikehara consequence, exposed under a project namespace. -/
theorem weakPNT :
    Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) :=
  _root_.WeakPNT

end PrimeGapNormality.ClassicalPNT
