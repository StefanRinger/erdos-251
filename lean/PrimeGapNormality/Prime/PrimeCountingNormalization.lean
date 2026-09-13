import PrimeGapNormality.Prime.SingletonLi
import PrimeGapNormality.Prime.MixZeta

/-!
# Prime-count normalization under the uniform tuples hypothesis

The two prime-counting asymptotic predicates coincide definitionally.
Their equivalence connects the singleton consequence of Kuperberg's
hypothesis to normalization of the cutoff mixture. The proof reuses the
existing counting and mixture lemmas; it adds no arithmetic assumption.
-/

open Filter
open scoped Topology

namespace PrimeGapNormality.Prime.PrimeCountingNormalization

theorem mixCounting_iff_primeCounting :
    MixPrimeCountingAsymp ↔ PrimeCountingAsymp := Iff.rfl

theorem mixCounting_of_kuperberg (hK : KuperbergConj13) :
    MixPrimeCountingAsymp :=
  mixCounting_iff_primeCounting.mpr (primeCountingAsymp_of_kuperberg hK)

theorem mixZeta_one_of_kuperberg (hK : KuperbergConj13) :
    MixZetaTendstoOne :=
  mixZeta_tendsto_one_of_primeCountingAsymp (mixCounting_of_kuperberg hK)

theorem mixZeta_abs_zero_of_kuperberg (hK : KuperbergConj13) :
    Tendsto (fun X : ℕ => |1 - mixZeta X|) atTop (𝓝 0) := by
  have hζ : Tendsto mixZeta atTop (𝓝 (1 : ℝ)) :=
    mixZeta_one_of_kuperberg hK
  have hsub : Tendsto (fun X : ℕ => (1 : ℝ) - mixZeta X) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hζ
  simpa only [abs_zero] using hsub.abs

end PrimeGapNormality.Prime.PrimeCountingNormalization
