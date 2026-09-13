import PrimeGapNormality.Prime.CoreLocalModelSubsequence
import PrimeGapNormality.Prime.CoreLiftedNormalTuple
import PrimeGapNormality.Prime.CoreLocalOrbitEnd
import PrimeGapNormality.Prime.CoreLocalNormalFormEnd

/-! Final local-polynomial assembly against the actual model theorem.
Work-in-progress release source: not accepted until every imported actual
model supplier and this file compile, and its end types/axioms are audited.
No model, frame, reference or tail assumption is present in the intended
end signatures below. -/

namespace PrimeGapNormality.Prime
open CoreCyclic Finset MvPolynomial
noncomputable section

private theorem coreLocal_clock_ge {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    2 ≤ B ^ k := by
  have hsplit : k = k - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
  rw [hsplit, pow_succ]
  exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))

/-- Integer lifting changes neither the top degree nor the arithmetic
profile. The actual model theorem supplies the only intermediate bound. -/
theorem corePrime_rooted_local_weyl_clock_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (N : PeriodicLocal k) (w : ℕ)
    (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ s i, i ∈ (N s).vars → i ≤ w)
    {κ d0 c : ℝ} (hκ : (topDegree N : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    weylCriterion (B ^ k) (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) N) := by
  let T : PeriodicLocal k := liftedIntegerTuple N
  have hTr : drop hk T = 0 := liftedIntegerTuple_rooted hk N hroot
  have hT : T ≠ 0 := liftedIntegerTuple_ne_zero N hN
  have hTw : ∀ s i, i ∈ (T s).vars → i ≤ w :=
    (liftedIntegerTuple_width_iff N).2 hw
  have hTd : topDegree T = topDegree N := topDegree_liftedIntegerTuple N
  have hκT : (topDegree T : ℝ) / Real.log (B : ℝ) ≤ κ := by rwa [hTd]
  have hmodel := CoreLocalModelSubsequence.coreLocalModelSubsequenceBounds_of_rooted
    hB hk phase T w hTr hT hTw hκT
  have hd : 1 ≤ topDegree T := one_le_topDegree_of_rooted hk T hTr hT
  have hdeg : ∀ s, (T s).totalDegree ≤ topDegree T :=
    fun s ↦ Finset.le_sup (f := fun s ↦ (T s).totalDegree) (mem_univ s)
  have href := coreLocal_subsequenceReference_of_D_and_model
    hB hd hk phase T w hTw hdeg hκT hd0 hc hD hmodel
  have hW := primeLocalFullSeries_weyl_pow_of_subsequence_reference
    hB hk phase (integerTupleLift N).tuple href
  change weylCriterion (B ^ k)
    (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) (liftedIntegerTuple N)) at hW
  rw [coreCyclicFullSeries_liftedIntegerTuple] at hW
  exact weylCriterion_of_mul (by have := liftedIntegerScale_pos N; omega)
    (coreLocal_clock_ge hB hk) hW

private theorem exists_localWidth {k : ℕ} (N : PeriodicLocal k) :
    ∃ w : ℕ, ∀ s i, i ∈ (N s).vars → i ≤ w := by
  let w := Finset.univ.sup (fun s : Fin k ↦ (N s).vars.sup id)
  refine ⟨w, ?_⟩
  intro s i hi
  exact (Finset.le_sup (f := id) hi).trans
    (Finset.le_sup (f := fun s : Fin k ↦ (N s).vars.sup id) (mem_univ s))

/-- Effective-degree form: only the degree of the canonical normal form
enters the D budget. The original polynomial may have higher telescoping
terms, whose actual rational boundary and convergence are already proved. -/
theorem corePrime_local_weyl_clock_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    {κ d0 c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    weylCriterion (B ^ k) (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) := by
  obtain ⟨w, hw⟩ := exists_localWidth (normalForm hB hk F)
  have hW := corePrime_rooted_local_weyl_clock_of_D hB hk phase
    (normalForm hB hk F) w (drop_normalForm hB hk F) hF hw hκ hd0 hc hD
  have hshift := CoreRationalAffine.weylCriterion_add_rat (coreLocal_clock_ge hB hk)
    (primeLocalBoundaryRat hB hk phase F) hW
  rwa [← coreCyclicFullSeries_eq_normalForm_add_boundary hB hk phase F] at hshift

theorem corePrime_local_weyl_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    {κ d0 c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    weylCriterion B (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) :=
  weylCriterion_of_pow hB (by omega : 1 ≤ k)
    (corePrime_local_weyl_clock_of_D hB hk phase F hF hκ hd0 hc hD)

theorem corePrime_local_isNormal_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    {κ d0 c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (corePrime_local_weyl_of_D hB hk phase F hF hκ hd0 hc hD)

theorem corePrime_local_irrational_of_D
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    {κ d0 c : ℝ}
    (hκ : (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    Irrational (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) :=
  weylCriterion_irrational (corePrime_local_weyl_of_D hB hk phase F hF hκ hd0 hc hD)

/-- The literature input discharges the actual D profile at every required
fixed effective degree. No residual model premise is accepted. -/
theorem corePrime_local_weyl_clock_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    (hK : KuperbergConj13) :
    weylCriterion (B ^ k) (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) := by
  let κ : ℝ := (topDegree (normalForm hB hk F) : ℝ) / Real.log (B : ℝ)
  have hd : 0 < topDegree (normalForm hB hk F) :=
    topDegree_pos_of_rooted hk _ (drop_normalForm hB hk F) hF
  have hκ : 0 < κ := div_pos (Nat.cast_pos.mpr hd)
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))
  exact corePrime_local_weyl_clock_of_D hB hk phase F hF (κ := κ) le_rfl
    (by norm_num : (0 : ℝ) < 20) (by norm_num : (1 : ℝ) ≤ 1)
    (coreLinearD_of_kuperberg hK hκ)

theorem corePrime_local_isNormal_of_kuperberg
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : PeriodicLocal k) (hF : normalForm hB hk F ≠ 0)
    (hK : KuperbergConj13) :
    PrimeGapNormality.BFree.IsNormal B
      (coreCyclicFullSeries B hk phase (fun q ↦ (primeGap q : ℝ)) F) :=
  CoreWeylNormality.isNormal_of_weyl hB
    (weylCriterion_of_pow hB (by omega : 1 ≤ k)
      (corePrime_local_weyl_clock_of_kuperberg hB hk phase F hF hK))

end
end PrimeGapNormality.Prime
