import PrimeGapNormality.Prime.CoreCommonPeriodEnd

/-! Exact rational relations for series initially given with different
periods. This is the same finite common-multiple embedding as the joint
orbit theorem; it consumes no larger degree or arithmetic profile. -/

namespace PrimeGapNormality.Prime.CoreCommonPeriodEnd
open CoreCyclic CorePeriodRefinement Finset
noncomputable section

theorem rational_relation_iff_common_period_of_D
    {I : Type*} [Fintype I] {B l d : ℕ} (hB : 2 ≤ B)
    {k : I → ℕ} (hk : ∀ i, 0 < k i) (hl : 0 < l)
    (hkl : ∀ i, k i ∣ l) (F : ∀ i, PeriodicLocal (k i))
    (hdeg : ∀ i, topDegree (normalForm hB (hk i) (F i)) ≤ d)
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) (q : I → ℚ) :
    (∃ a : ℚ, (∑ i, (q i : ℝ) *
      coreCyclicFullSeries B (hk i) ⟨0, hk i⟩ (fun n => (primeGap n : ℝ)) (F i)) = (a : ℝ)) ↔
      (∑ i, q i • repeatTuple (l := l) (hk i) (normalForm hB (hk i) (F i))) = 0 := by
  have hgdeg : ∀ i, topDegree (normalForm hB hl (family hk l F i)) ≤ d := by
    intro i
    rw [family_effective_degree hB hk hl hkl F i]
    exact hdeg i
  have hnf (i : I) : normalForm hB hl (family hk l F i) =
      repeatTuple (l := l) (hk i) (normalForm hB (hk i) (F i)) :=
    repeat_normalForm hB (hk i) hl (hkl i) (F i)
  have hh := CoreLocalRelations.rational_relation_iff_of_D hB hl ⟨0, hl⟩
    (family hk l F) hgdeg hκ hd0 hc hD q
  simpa only [family_series B hk hl hkl F, hnf] using hh

end
end PrimeGapNormality.Prime.CoreCommonPeriodEnd
