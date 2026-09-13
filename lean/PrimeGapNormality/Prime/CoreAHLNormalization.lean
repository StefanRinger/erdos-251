import PrimeGapNormality.ClassicalPNT.WeakPNT
import PrimeGapNormality.Prime.IndexPassageFromPNT
import PrimeGapNormality.Prime.PrimeCountingNormalization

/-!
# Classical normalization for the AHL comparison route

The AHL-to-D argument needs the scalar normalization `mixZeta X → 1`.
This file supplies it from the source-staged classical weak PNT and the
already verified project conversion

`cumsum Λ / N → 1 → PrimeCountingAsymp → MixZetaTendstoOne`.

It does not assert AHL and does not alter the weaker D-only endpoint.  The
source-staged classical theorem remains subject to its separate compiler and
`#print axioms` audit.
-/

namespace PrimeGapNormality.Prime.CoreAHLNormalization

open Filter ArithmeticFunction
open scoped Topology

/-- The staged weak PNT in the exact project-local `cumsum` notation. -/
theorem classicalWeakPNT_projectCumsum :
    Tendsto (fun N : ℕ ↦
      PrimeGapNormality.Prime.cumsum (fun n ↦ Λ n) N / N) atTop (𝓝 1) := by
  simpa only [PrimeGapNormality.Prime.cumsum, _root_.cumsum] using
    PrimeGapNormality.ClassicalPNT.weakPNT

/-- The exact qualitative prime-counting asymptotic used by the existing
index-passage and normalization APIs. -/
theorem classicalPrimeCountingAsymp : PrimeCountingAsymp :=
  primeCountingAsymp_of_psi classicalWeakPNT_projectCumsum

/-- Definitionally identical mix-side prime-counting normalization. -/
theorem classicalMixPrimeCountingAsymp : MixPrimeCountingAsymp :=
  PrimeCountingNormalization.mixCounting_iff_primeCounting.mpr
    classicalPrimeCountingAsymp

/-- The scalar mass normalization required by the AHL comparison. -/
theorem classicalMixZetaTendstoOne : MixZetaTendstoOne :=
  mixZeta_tendsto_one_of_primeCountingAsymp
    classicalMixPrimeCountingAsymp

/-- Absolute-error form used in the finite D comparison bound. -/
theorem classicalMixZetaAbsTendstoZero :
    Tendsto (fun X : ℕ ↦ |1 - mixZeta X|) atTop (𝓝 0) := by
  have hsub : Tendsto (fun X : ℕ ↦ (1 : ℝ) - mixZeta X) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub classicalMixZetaTendstoOne
  simpa only [abs_zero] using hsub.abs

end PrimeGapNormality.Prime.CoreAHLNormalization
