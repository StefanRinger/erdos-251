import PrimeGapNormality.Prime.CorePeriodRefinement
import PrimeGapNormality.Prime.CoreLocalRelations

/-! Families initially presented with different periods. A common multiple
(for example their LCM) changes neither a series value nor its effective
degree. Independence is tested after the explicit common-period embedding.
-/

namespace PrimeGapNormality.Prime.CoreCommonPeriodEnd
open CoreCyclic CorePeriodRefinement
noncomputable section

def family {I : Type*} {k : I → ℕ} (hk : ∀ i, 0 < k i) (l : ℕ)
    (F : ∀ i, PeriodicLocal (k i)) : I → PeriodicLocal l :=
  fun i ↦ repeatTuple (l := l) (hk i) (F i)

theorem family_series (B : ℕ) {I : Type*} {k : I → ℕ}
    (hk : ∀ i, 0 < k i) {l : ℕ} (hl : 0 < l)
    (hkl : ∀ i, k i ∣ l) (F : ∀ i, PeriodicLocal (k i)) (g : ℕ → ℝ) (i : I) :
    coreCyclicFullSeries B hl ⟨0, hl⟩ g (family hk l F i) =
      coreCyclicFullSeries B (hk i) ⟨0, hk i⟩ g (F i) := by
  simpa [family, reduceLabel] using
    repeat_series B (hk i) hl (hkl i) ⟨0, hl⟩ g (F i)

theorem family_effective_degree {B l : ℕ} (hB : 2 ≤ B)
    {I : Type*} {k : I → ℕ} (hk : ∀ i, 0 < k i) (hl : 0 < l)
    (hkl : ∀ i, k i ∣ l) (F : ∀ i, PeriodicLocal (k i)) (i : I) :
    topDegree (normalForm hB hl (family hk l F i)) =
      topDegree (normalForm hB (hk i) (F i)) := by
  rw [family, repeat_normalForm hB (hk i) hl (hkl i),
    repeat_topDegree (hk i) hl (hkl i)]

theorem jointWeyl_of_common_period_of_D
    {I : Type*} [Fintype I] [DecidableEq I] {B l d : ℕ} (hB : 2 ≤ B)
    {k : I → ℕ} (hk : ∀ i, 0 < k i) (hl : 0 < l)
    (hkl : ∀ i, k i ∣ l) (F : ∀ i, PeriodicLocal (k i))
    (hdeg : ∀ i, topDegree (normalForm hB (hk i) (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i ↦
      repeatTuple (l := l) (hk i) (normalForm hB (hk i) (F i))))
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    JointWeyl (fun _ : I ↦ B ^ l)
      (fun i ↦ coreCyclicFullSeries B (hk i) ⟨0, hk i⟩
        (fun n ↦ (primeGap n : ℝ)) (F i)) := by
  have hgdeg : ∀ i, topDegree (normalForm hB hl (family hk l F i)) ≤ d := by
    intro i
    rw [family_effective_degree hB hk hl hkl F i]
    exact hdeg i
  have hglin : LinearIndependent ℚ (fun i ↦ normalForm hB hl (family hk l F i)) := by
    have heq : (fun i ↦ normalForm hB hl (family hk l F i)) =
        (fun i ↦ repeatTuple (l := l) (hk i) (normalForm hB (hk i) (F i))) := by
      funext i
      exact repeat_normalForm hB (hk i) hl (hkl i) (F i)
    rw [heq]
    exact hlin
  have hj := CoreLocalRelations.jointWeyl_of_independent_normalForms_of_D
    hB hl ⟨0, hl⟩ (family hk l F) hgdeg hglin hκ hd0 hc hD
  simpa only [family_series B hk hl hkl F] using hj

end
end PrimeGapNormality.Prime.CoreCommonPeriodEnd
