import PrimeGapNormality.Prime.CoreSequenceSTConsumer
import PrimeGapNormality.Prime.CoreModelSingleSite

/-!
# Window-count growth from uniform positive shape comparison

The first checkpoint exposes only the uniform singleton inclusion bound
of the actual finite root mixture. The small test is chosen after the
physical window, as permitted by the actual S quantifier order.
-/

namespace PrimeGapNormality.Prime.CoreSequenceWindowGrowthFromS

open Finset Filter CoreSequencePattern CoreSequencePatternLaw CoreSequenceSTConsumer
open scoped Classical Topology
noncomputable section

set_option maxHeartbeats 1000000

def pointTest (d : ℕ) (U : Finset ℕ) : ℝ := if d ∈ U then 1 else 0

def shapeMean (Ω : Finset ℕ) (μ : Finset ℕ → ℝ) (L : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ U ∈ Ω.powerset.filter (fun U => U.card = L), f U * Stopped.shortShapeMass Ω μ L U

theorem pointTest_bounds (d : ℕ) (U : Finset ℕ) : 0 ≤ pointTest d U ∧ pointTest d U ≤ 1 := by
  unfold pointTest
  split_ifs <;> norm_num

theorem point_shapeMean_le_inclusion (Ω : Finset ℕ) (μ : Finset ℕ → ℝ)
    (hμ : ∀ U ∈ Ω.powerset, 0 ≤ μ U) (L d : ℕ) :
    shapeMean Ω μ L (pointTest d) ≤ Stopped.inclusionMass Ω μ {d} := by
  rw [shapeMean, firstL_test_eq_pushforward]
  have hincl : Stopped.inclusionMass Ω μ {d} =
      ∑ U ∈ Ω.powerset, μ U * (if d ∈ U then 1 else 0) := by
    simp [Stopped.inclusionMass, Finset.sum_filter]
  rw [hincl]
  apply Finset.sum_le_sum
  intro U hU
  apply mul_le_mul_of_nonneg_left _ (hμ U hU)
  by_cases hcard : L ≤ U.card
  · simp only [hcard, if_true, pointTest]
    by_cases hd : d ∈ Stopped.firstL L U
    · have hdU : d ∈ U := Stopped.firstL_subset hd
      simp [hd, hdU]
    · simp only [hd, if_false]
      split_ifs <;> norm_num
  · simp only [hcard, if_false]
    split_ifs <;> norm_num

theorem exists_successful_span {a : ℕ → ℕ} (ha : StrictMono a) (X S : ℕ) {L : ℕ}
    (hL : 1 ≤ L) (hN : 0 < (seqWindow a X).card)
    (hf : Stopped.failureMass (offsetWindow S) (patternMass a X (offsetWindow S)) L < 1) :
    ∃ n ∈ seqWindow a X, a (n + L) - a n ≤ S := by
  by_contra hn
  push_neg at hn
  simp only [offsetWindow] at hf
  rw [failureMass_eq_span ha X S hL] at hf
  have hsum : (∑ n ∈ seqWindow a X, if a (n + L) - a n ≤ S then (0 : ℝ) else 1) =
      ((seqWindow a X).card : ℝ) := by
    calc
      _ = ∑ n ∈ seqWindow a X, (1 : ℝ) :=
        Finset.sum_congr rfl (fun n hnI => if_neg (not_le.mpr (hn n hnI)))
      _ = _ := by simp
  rw [hsum, div_self (Nat.cast_ne_zero.mpr hN.ne')] at hf
  exact (lt_irrefl (1 : ℝ)) hf

/-- One actual successful root supplies a positive slot d and mass 1/N
for the corresponding point test. -/
theorem exists_point_mass_ge {a : ℕ → ℕ} (ha : StrictMono a) (X S : ℕ) {L : ℕ}
    (hL : 1 ≤ L) (hN : 0 < (seqWindow a X).card)
    (hf : Stopped.failureMass (offsetWindow S) (patternMass a X (offsetWindow S)) L < 1) :
    ∃ d ∈ offsetWindow S,
      (1 : ℝ) / (seqWindow a X).card ≤
        shapeMean (offsetWindow S) (patternMass a X (offsetWindow S)) L (pointTest d) := by
  obtain ⟨n, hn, hspan⟩ := exists_successful_span ha X S hL hN hf
  let d := offset a n 0
  have hdpos : 0 < d := offset_pos ha n 0
  have hdS : d ≤ S := by
    have hh := Nat.sub_le_sub_right (ha.monotone (show n + 0 + 1 ≤ n + L by omega)) (a n)
    exact hh.trans hspan
  have hdprefix : d ∈ prefixSet a n L :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  refine ⟨d, mem_Icc.mpr ⟨hdpos, hdS⟩, ?_⟩
  simp only [shapeMean, offsetWindow]
  rw [firstL_test_eq_prefix_average ha X S hL]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hterm : (1 : ℝ) =
      if a (n + L) - a n ≤ S then pointTest d (prefixSet a n L) else 0 := by
    simp [hspan, pointTest, hdprefix]
  rw [hterm]
  apply Finset.single_le_sum _ hn
  intro i hi
  split_ifs
  · exact (pointTest_bounds d _).1
  · exact le_rfl

private theorem model_nonneg (X S : ℕ) (U : Finset ℕ) : 0 ≤ finiteRootMix X S U := by
  unfold finiteRootMix
  exact div_nonneg
    (Finset.sum_nonneg fun t ht => mul_nonneg (mixWeightV_nonneg t) (actualRootLaw_nonneg _ _ _))
    (mixZ_nonneg X)

/-- The explicit uniform singleton-model premise is the only model helper
not discharged in this first checkpoint. The law remains the literal
finiteRootMix, not an arbitrary substitute probability measure. -/
theorem windowCountToInfinity_of_shapeS_and_singletons
    {a T : ℕ → ℕ} (ha : StrictMono a) {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hT : Tendsto T atTop atTop) (hS : SequencePositiveShapeS a T κ c)
    (hne : ∀ᶠ X : ℕ in atTop, 0 < (seqWindow a X).card)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hsite : ∀ᶠ Y : ℕ in atTop, ∀ d ∈ offsetWindow (ahlSmall_window κ Y),
      Stopped.inclusionMass (offsetWindow (ahlSmall_window κ Y))
        (finiteRootMix Y (ahlSmall_window κ Y)) {d} ≤ η Y) :
    WindowCountToInfinity a := by
  have hnat : Tendsto (fun X : ℕ => (seqWindow a X).card) atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    let ε : ℝ := 1 / (4 * ((M : ℝ) + 1))
    have hε : 0 < ε := by dsimp only [ε]; positivity
    have hεone : ε < 1 := by
      dsimp only [ε]
      apply (div_lt_iff₀ (by positivity)).mpr
      have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg _
      linarith
    have hηc : Tendsto (fun X : ℕ => c * η (T X)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_apply] using (hη.comp hT).const_mul c
    filter_upwards [hS ε hε, hne, hT.eventually hsite,
      hT.eventually (eventually_one_le_profileL hκ),
      hηc.eventually_le_const hε] with X hSX hN hsiteX hL hηX
    have hf0 := hSX (fun _ => 0) (fun U hU => le_rfl) (fun U hU => zero_le_one)
    simp only [zero_mul, sum_const_zero, mul_zero, add_zero, zero_add] at hf0
    obtain ⟨d, hd, hmass⟩ := exists_point_mass_ge ha X (ahlSmall_window κ (T X)) hL hN
      (hf0.trans_lt hεone)
    have hpoint := hSX (pointTest d) (fun U hU => (pointTest_bounds d U).1)
      (fun U hU => (pointTest_bounds d U).2)
    have hfnonneg : 0 ≤ Stopped.failureMass (offsetWindow (ahlSmall_window κ (T X)))
        (patternMass a X (offsetWindow (ahlSmall_window κ (T X)))) (profileL κ (T X)) := by
      unfold Stopped.failureMass
      exact Finset.sum_nonneg fun U hU => patternMass_nonneg _ _ _ _
    have hmodel := (point_shapeMean_le_inclusion (offsetWindow (ahlSmall_window κ (T X)))
      (finiteRootMix (T X) (ahlSmall_window κ (T X)))
      (fun U hU => model_nonneg _ _ U) (profileL κ (T X)) d).trans (hsiteX d hd)
    have hcmodel := mul_le_mul_of_nonneg_left hmodel hc.le
    have hinv : (1 : ℝ) / (seqWindow a X).card ≤ 2 * ε := by
      change Stopped.failureMass (offsetWindow (ahlSmall_window κ (T X)))
          (patternMass a X (offsetWindow (ahlSmall_window κ (T X)))) (profileL κ (T X)) +
        shapeMean (offsetWindow (ahlSmall_window κ (T X)))
          (patternMass a X (offsetWindow (ahlSmall_window κ (T X)))) (profileL κ (T X)) (pointTest d) ≤
        c * shapeMean (offsetWindow (ahlSmall_window κ (T X)))
          (finiteRootMix (T X) (ahlSmall_window κ (T X))) (profileL κ (T X)) (pointTest d) + ε at hpoint
      linarith
    have hNreal : (0 : ℝ) < (seqWindow a X).card := Nat.cast_pos.mpr hN
    have hden := (div_le_iff₀ hNreal).mp hinv
    have hεeq : (4 * ((M : ℝ) + 1)) * ε = 1 := by
      dsimp only [ε]
      field_simp [show (M : ℝ) + 1 ≠ 0 by positivity]
    by_contra hnot
    have hcard : (seqWindow a X).card < M := Nat.lt_of_not_ge hnot
    have hcardR : ((seqWindow a X).card : ℝ) < M := Nat.cast_lt.mpr hcard
    have hmul := mul_le_mul_of_nonneg_left hcardR.le hε.le
    nlinarith
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp hnat

/-- The actual model singleton theorem discharges the first checkpoint's
only model-bound premise. No point-distribution assumption remains. -/
theorem windowCountToInfinity_of_shapeS
    {a T : ℕ → ℕ} (ha : StrictMono a) {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hT : Tendsto T atTop atTop) (hS : SequencePositiveShapeS a T κ c)
    (hne : ∀ᶠ X : ℕ in atTop, 0 < (seqWindow a X).card) : WindowCountToInfinity a := by
  apply windowCountToInfinity_of_shapeS_and_singletons ha hκ hc hT hS hne
    (fun Y : ℕ => ((3 : ℝ) / eulerProdLowerConst) * (Real.log (windowG Y) / windowG Y))
    CoreModelSingleSite.tendsto_modelSingleSite_cap_zero
  filter_upwards [CoreModelSingleSite.eventually_finiteRootMix_singleton_inclusion_le hκ] with Y hY
  intro d hd
  exact hY d (mem_Icc.mp hd).1 (mem_Icc.mp hd).2

/-- The paper's gap-tail input already supplies nonempty physical windows.
Thus actual positive S/T imply growing window counts without an extra
count-growth or model-singleton hypothesis. -/
theorem windowCountToInfinity_of_shapeS_and_gapTail
    {a T : ℕ → ℕ} (ha : StrictMono a) {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hT : Tendsto T atTop atTop) (hS : SequencePositiveShapeS a T κ c)
    {ρ : ℝ} {G : ℕ → ℝ} (hTail : GapTailT a ρ G) : WindowCountToInfinity a := by
  obtain ⟨C, hC, h⟩ := hTail.2.2.2
  exact windowCountToInfinity_of_shapeS ha hκ hc hT hS (h.mono fun X hX => hX.1)

end
end PrimeGapNormality.Prime.CoreSequenceWindowGrowthFromS
