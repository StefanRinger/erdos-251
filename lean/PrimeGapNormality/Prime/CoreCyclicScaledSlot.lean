import PrimeGapNormality.Prime.CoreActualCyclicSlot
import PrimeGapNormality.Prime.CorePolynomialScaling
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Compact reciprocal-scale family for a cyclic insertion slot

For a signed action polynomial `p` of total degree at most `d`, set

`Q_(γ,Y) = Σ_e γ^(d-e) · specialize_Y(homogeneousComponent e p)`.

At `γ = 1/G`, this is exactly the simultaneous all-variable rescaling of
the actual slot polynomial by `G^d`.  At `γ = 0`, it is exactly the genuine
degree-`d` homogeneous action (zero if the degree drops).  The coefficient
functions are continuous because the exterior action has finite support.
-/

namespace PrimeGapNormality.Prime.CoreCyclicScaledSlot

open Finset MvPolynomial
open scoped BigOperators Classical Polynomial

noncomputable section

abbrev Frame (w : ℕ) := Fin (2 * w + 1) → ℝ

/-! ## Finite exterior assignment -/

/-- Extend a finite exterior frame by zero away from the actual signed
coordinate box.  Every variable of the action lies inside that box. -/
def finiteExteriorAssignment (w : ℕ) (Y : Frame w) :
    CoreCyclic.OnePoint.ExteriorIndex → ℝ :=
  fun i ↦ if hi : (i : ℤ) ∈ CoreCyclic.OnePoint.FiniteExterior.box w then
    Y (((CoreCyclic.OnePoint.FiniteExterior.box w).orderIsoOfFin
      (CoreCyclic.OnePoint.FiniteExterior.box_card w)).symm ⟨i.val, hi⟩)
  else 0

theorem finiteExteriorAssignment_embedding
    (w : ℕ) (Y : Frame w) (a : Fin (2 * w + 1)) :
    finiteExteriorAssignment w Y
        (CoreCyclic.OnePoint.FiniteExterior.embedding w a) = Y a := by
  have hmem :
      ((CoreCyclic.OnePoint.FiniteExterior.embedding w a :
        CoreCyclic.OnePoint.ExteriorIndex) : ℤ) ∈
          CoreCyclic.OnePoint.FiniteExterior.box w :=
    (CoreCyclic.OnePoint.FiniteExterior.box w).orderEmbOfFin_mem
      (CoreCyclic.OnePoint.FiniteExterior.box_card w) a
  unfold finiteExteriorAssignment
  rw [dif_pos hmem]
  congr 1
  have h := ((CoreCyclic.OnePoint.FiniteExterior.box w).orderIsoOfFin
    (CoreCyclic.OnePoint.FiniteExterior.box_card w)).symm_apply_apply a
  exact h

/-- Finite coordinate corresponding to the central exterior index `0`. -/
def centralIndex (w : ℕ) : Fin (2 * w + 1) :=
  ((CoreCyclic.OnePoint.FiniteExterior.box w).orderIsoOfFin
    (CoreCyclic.OnePoint.FiniteExterior.box_card w)).symm
      ⟨0, CoreCyclic.OnePoint.FiniteExterior.mem_box.2 ⟨by norm_num, by omega⟩⟩

theorem embedding_centralIndex (w : ℕ) :
    CoreCyclic.OnePoint.FiniteExterior.embedding w (centralIndex w) =
      ⟨0, by norm_num⟩ := by
  apply Subtype.ext
  change (CoreCyclic.OnePoint.FiniteExterior.box w).orderEmbOfFin
      (CoreCyclic.OnePoint.FiniteExterior.box_card w) (centralIndex w) = 0
  unfold centralIndex
  have h := ((CoreCyclic.OnePoint.FiniteExterior.box w).orderIsoOfFin
    (CoreCyclic.OnePoint.FiniteExterior.box_card w)).apply_symm_apply
      ⟨0, CoreCyclic.OnePoint.FiniteExterior.mem_box.2 ⟨by norm_num, by omega⟩⟩
  exact congrArg Subtype.val h

theorem frameRank_centralIndex (w J : ℕ) (hJ : 1 ≤ J) :
    CoreCyclic.OnePoint.FiniteExterior.frameRank w J (centralIndex w) = J - 1 := by
  unfold CoreCyclic.OnePoint.FiniteExterior.frameRank
  rw [embedding_centralIndex,
    CoreCyclic.OnePoint.FiniteExterior.deletedRank_zero J hJ]

theorem localFrame_centralIndex (w J : ℕ) (hJ : 1 ≤ J)
    (G : ℝ) (F : Finset ℕ) :
    CoreActualFrameJoint.localFrame w J G F (centralIndex w) =
      (subsetGap F (J - 1) : ℝ) / G := by
  unfold CoreActualFrameJoint.localFrame
  rw [frameRank_centralIndex w J hJ]

theorem continuous_finiteExteriorAssignment_apply
    (w : ℕ) (i : CoreCyclic.OnePoint.ExteriorIndex) :
    Continuous fun Y : Frame w ↦ finiteExteriorAssignment w Y i := by
  by_cases hi : (i : ℤ) ∈ CoreCyclic.OnePoint.FiniteExterior.box w
  · simp only [finiteExteriorAssignment, dif_pos hi]
    exact continuous_apply _
  · simp only [finiteExteriorAssignment, dif_neg hi]
    exact continuous_const

theorem continuous_finiteExteriorAssignment (w : ℕ) :
    Continuous (finiteExteriorAssignment w) :=
  continuous_pi fun i ↦ continuous_finiteExteriorAssignment_apply w i

/-! ## The exact compact polynomial family -/

/-- Reciprocal-scale normalized univariate family. -/
def normalizedActionFamily (w d : ℕ) (p : CoreCyclic.OnePoint.SignedPoly)
    (a : ℝ × Frame w) : ℝ[X] :=
  ∑ e ∈ range (p.totalDegree + 1),
    Polynomial.C (a.1 ^ (d - e)) *
      CoreCyclic.OnePoint.movingSpecialization (homogeneousComponent e p)
        (finiteExteriorAssignment w a.2)

private theorem movingSpecialization_natDegree_le_totalDegree
    (q : CoreCyclic.OnePoint.SignedPoly)
    (y : CoreCyclic.OnePoint.ExteriorIndex → ℝ) :
    (CoreCyclic.OnePoint.movingSpecialization q y).natDegree ≤ q.totalDegree := by
  have hmap : (CoreCyclic.OnePoint.movingSpecialization q y).natDegree ≤
      (CoreCyclic.OnePoint.splitMoving q).natDegree := Polynomial.natDegree_map_le
  have hsplit : (CoreCyclic.OnePoint.splitMoving q).natDegree =
      q.degreeOf (-1 : ℤ) := by
    simpa only [CoreCyclic.OnePoint.splitMoving, AlgEquiv.trans_apply,
      renameEquiv_apply] using
      (MvPolynomial.degreeOf_eq_natDegree (-1 : ℤ) q).symm
  exact hmap.trans (hsplit.trans_le (degreeOf_le_totalDegree q (-1 : ℤ)))

private theorem homogeneousComponent_totalDegree_le
    (q : CoreCyclic.OnePoint.SignedPoly) (e : ℕ) :
    (homogeneousComponent e q).totalDegree ≤ e := by
  by_cases hz : homogeneousComponent e q = 0
  · simp [hz]
  · exact ((homogeneousComponent_isHomogeneous e q).totalDegree hz).le

/-- One common univariate degree bound, including degree-dropping fibres. -/
theorem normalizedActionFamily_natDegree_le
    (w d : ℕ) (p : CoreCyclic.OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (a : ℝ × Frame w) :
    (normalizedActionFamily w d p a).natDegree ≤ d := by
  unfold normalizedActionFamily
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((movingSpecialization_natDegree_le_totalDegree _ _).trans
      ((homogeneousComponent_totalDegree_le p e).trans (by
        have he' : e < p.totalDegree + 1 := mem_range.mp he
        exact (Nat.lt_succ_iff.mp (by
          simpa only [Nat.succ_eq_add_one] using he')).trans hd)))

private theorem continuous_movingSpecialization_coeff
    (w : ℕ) (q : CoreCyclic.OnePoint.SignedPoly) (n : ℕ) :
    Continuous fun Y : Frame w ↦
      (CoreCyclic.OnePoint.movingSpecialization q
        (finiteExteriorAssignment w Y)).coeff n := by
  let qR : MvPolynomial CoreCyclic.OnePoint.ExteriorIndex ℝ :=
    MvPolynomial.map (algebraMap ℚ ℝ)
      ((CoreCyclic.OnePoint.splitMoving q).coeff n)
  have hcont : Continuous fun Y : Frame w ↦
      eval (finiteExteriorAssignment w Y) qR :=
    (MvPolynomial.continuous_eval qR).comp (continuous_finiteExteriorAssignment w)
  convert hcont using 1
  funext Y
  unfold CoreCyclic.OnePoint.movingSpecialization qR
  rw [Polynomial.coeff_map]
  change eval₂ (algebraMap ℚ ℝ) (finiteExteriorAssignment w Y)
      ((CoreCyclic.OnePoint.splitMoving q).coeff n) = _
  rw [← eval₂_eq_eval_map]

/-- Every coefficient is a continuous function of `(γ,Y)`, including on
the face `γ=0`. -/
theorem continuous_normalizedActionFamily_coeff
    (w d : ℕ) (p : CoreCyclic.OnePoint.SignedPoly) (n : ℕ) :
    Continuous fun a : ℝ × Frame w ↦
      (normalizedActionFamily w d p a).coeff n := by
  unfold normalizedActionFamily
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply continuous_finsetSum
  intro e _
  exact (continuous_fst.pow (d - e)).mul
    ((continuous_movingSpecialization_coeff w (homogeneousComponent e p) n).comp
      continuous_snd)

theorem continuous_normalizedActionFamily_eval
    (w d : ℕ) (p : CoreCyclic.OnePoint.SignedPoly) (hd : p.totalDegree ≤ d) :
    Continuous fun z : (ℝ × Frame w) × ℝ ↦
      Polynomial.eval z.2 (normalizedActionFamily w d p z.1) := by
  have hsum : Continuous fun z : (ℝ × Frame w) × ℝ ↦
      ∑ n ∈ range (d + 1),
        (normalizedActionFamily w d p z.1).coeff n * z.2 ^ n := by
    apply continuous_finsetSum
    intro n _
    exact ((continuous_normalizedActionFamily_coeff w d p n).comp continuous_fst).mul
      (continuous_snd.pow n)
  apply hsum.congr
  intro z
  exact (Polynomial.eval_eq_sum_range'
    (lt_of_le_of_lt (normalizedActionFamily_natDegree_le w d p hd z.1)
      (Nat.lt_succ_self d)) z.2).symm

/-- Compact parameter box used by the uniform polynomial insertion theorem. -/
def parameterSet (w : ℕ) (R : ℝ) : Set (ℝ × Frame w) :=
  Set.Icc 0 1 ×ˢ Metric.closedBall 0 R

theorem parameterSet_compact (w : ℕ) (R : ℝ) :
    IsCompact (parameterSet w R) :=
  isCompact_Icc.prod (isCompact_closedBall (0 : Frame w) R)

/-! ## The zero face is the genuine top homogeneous action -/

theorem normalizedActionFamily_zero
    (w d : ℕ) (p : CoreCyclic.OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (Y : Frame w) :
    normalizedActionFamily w d p (0, Y) =
      CoreCyclic.OnePoint.movingSpecialization (homogeneousComponent d p)
        (finiteExteriorAssignment w Y) := by
  unfold normalizedActionFamily
  by_cases htop : p.totalDegree = d
  · subst d
    rw [sum_eq_single p.totalDegree]
    · simp
    · intro e he hne
      have he' := mem_range.mp he
      have hpow : 0 < p.totalDegree - e := by omega
      simp [hpow.ne']
    · simp
  · have hlt : p.totalDegree < d := lt_of_le_of_ne hd htop
    rw [homogeneousComponent_eq_zero d p hlt,
      CoreCyclic.OnePoint.movingSpecialization_zero]
    apply sum_eq_zero
    intro e he
    have he' := mem_range.mp he
    have hpow : 0 < d - e := by omega
    simp [hpow.ne']

/-! ## Exact reciprocal-scale identity -/

private theorem eval₂_homogeneous_scale
    {q : CoreCyclic.OnePoint.SignedPoly} {e : ℕ} (hq : q.IsHomogeneous e)
    (x : ℤ → ℝ) (G : ℝ) :
    eval₂ (algebraMap ℚ ℝ) (fun i ↦ G * x i) q =
      G ^ e * eval₂ (algebraMap ℚ ℝ) x q := by
  simp_rw [eval₂_eq]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro m hm
  change ((q.coeff m : ℚ) : ℝ) *
      CorePolynomialScaling.monomialValue m (fun i ↦ G * x i) =
    G ^ e * (((q.coeff m : ℚ) : ℝ) *
      CorePolynomialScaling.monomialValue m x)
  rw [CorePolynomialScaling.monomialValue_scale]
  have hmdeg : m.degree = e := by
    simpa only [Finsupp.degree_apply] using
      (hq.degree_eq_sum_deg_support hm).symm
  rw [hmdeg]
  ring

private theorem movingSpecialization_homogeneous_scale
    {q : CoreCyclic.OnePoint.SignedPoly} {e : ℕ} (hq : q.IsHomogeneous e)
    (y : CoreCyclic.OnePoint.ExteriorIndex → ℝ) (z G : ℝ) :
    Polynomial.eval (G * z)
        (CoreCyclic.OnePoint.movingSpecialization q (fun i ↦ G * y i)) =
      G ^ e * Polynomial.eval z
        (CoreCyclic.OnePoint.movingSpecialization q y) := by
  rw [CoreCyclic.OnePoint.movingSpecialization_eval,
    CoreCyclic.OnePoint.movingSpecialization_eval]
  have hassignment :
      CoreCyclic.OnePoint.movingAssignment (fun i ↦ G * y i) (G * z) =
        fun i ↦ G * CoreCyclic.OnePoint.movingAssignment y z i := by
    funext i
    by_cases hi : i = (-1 : ℤ)
    · subst i
      simp
    · simp [CoreCyclic.OnePoint.movingAssignment, hi]
  rw [hassignment]
  exact eval₂_homogeneous_scale hq
    (CoreCyclic.OnePoint.movingAssignment y z) G

private theorem inv_pow_gap_mul
    {G : ℝ} (hG : G ≠ 0) {e d : ℕ} (hed : e ≤ d) (x : ℝ) :
    G⁻¹ ^ (d - e) * x = (G ^ e * x) / G ^ d := by
  have hsum : d - e + e = d := Nat.sub_add_cancel hed
  have hpow : G ^ d = G ^ (d - e) * G ^ e := by
    rw [← pow_add, hsum]
  rw [inv_pow, hpow]
  field_simp [pow_ne_zero (d - e) hG, pow_ne_zero e hG] <;> ring

/-- Exact normalization at every nonzero physical scale. -/
theorem normalizedActionFamily_inv_eval
    (w d : ℕ) (p : CoreCyclic.OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (Y : Frame w) {G : ℝ} (hG : G ≠ 0) (z : ℝ) :
    Polynomial.eval z (normalizedActionFamily w d p (G⁻¹, Y)) =
      Polynomial.eval (G * z)
          (CoreCyclic.OnePoint.movingSpecialization p
            (fun i ↦ G * finiteExteriorAssignment w Y i)) /
        G ^ d := by
  have hpSum := sum_homogeneousComponent p
  have hspec : CoreCyclic.OnePoint.movingSpecialization p
        (fun i ↦ G * finiteExteriorAssignment w Y i) =
      ∑ e ∈ range (p.totalDegree + 1),
        CoreCyclic.OnePoint.movingSpecialization (homogeneousComponent e p)
          (fun i ↦ G * finiteExteriorAssignment w Y i) := by
    have h := congrArg (fun q ↦ CoreCyclic.OnePoint.movingSpecialization q
      (fun i ↦ G * finiteExteriorAssignment w Y i)) hpSum
    simp only [CoreCyclic.OnePoint.movingSpecialization, map_sum,
      Polynomial.map_sum] at h
    exact h.symm
  unfold normalizedActionFamily
  rw [Polynomial.eval_finsetSum, hspec, Polynomial.eval_finsetSum,
    Finset.sum_div]
  apply sum_congr rfl
  intro e he
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    movingSpecialization_homogeneous_scale
      (homogeneousComponent_isHomogeneous e p)]
  have he' : e < p.totalDegree + 1 := mem_range.mp he
  have hed : e ≤ d := (Nat.lt_succ_iff.mp (by
    simpa only [Nat.succ_eq_add_one] using he')).trans hd
  exact inv_pow_gap_mul hG hed _

/-! ## Specialization to the actual ordered slot -/

private theorem actualExterior_eq_scaledFinite
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (w J : ℕ)
    (hJ : 1 ≤ J)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (F : Finset ℕ) {G : ℝ} (hG : G ≠ 0)
    {i : CoreCyclic.OnePoint.ExteriorIndex}
    (hi : (i : ℤ) ∈ (CoreCyclic.OnePoint.action B hk w
      (CoreCyclic.phaseAt hk r (J - 1)) P).vars) :
    CoreCyclic.orderedExteriorGap F J i =
      G * finiteExteriorAssignment w
        (CoreActualFrameJoint.localFrame w J G F) i := by
  have hib := CoreCyclic.OnePoint.FiniteExterior.action_vars_bounds
    B hk w (CoreCyclic.phaseAt hk r (J - 1)) P hw hi
  obtain ⟨a, ha⟩ :=
    (CoreCyclic.OnePoint.FiniteExterior.mem_range_embedding_iff w i).2 hib
  rw [← ha, finiteExteriorAssignment_embedding,
    CoreActualCyclicSlot.orderedExteriorGap_embedding w F J hJ]
  unfold CoreActualFrameJoint.localFrame
  field_simp [hG]

private theorem actualMovingPolynomial_eval_eq_scaled
    (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (w J : ℕ)
    (hJ : 1 ≤ J)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (F : Finset ℕ) {G : ℝ} (hG : G ≠ 0) (z : ℝ) :
    Polynomial.eval (G * z)
        (CoreActualCyclicSlot.slotMovingPolynomial B hk r P w J F) =
      Polynomial.eval (G * z)
        (CoreCyclic.OnePoint.movingSpecialization
          (CoreCyclic.OnePoint.action B hk w
            (CoreCyclic.phaseAt hk r (J - 1)) P)
          (fun i ↦ G * finiteExteriorAssignment w
            (CoreActualFrameJoint.localFrame w J G F) i)) := by
  unfold CoreActualCyclicSlot.slotMovingPolynomial
  rw [CoreCyclic.OnePoint.movingSpecialization_eval,
    CoreCyclic.OnePoint.movingSpecialization_eval]
  apply eval₂_congr
  intro i m hi hm
  have hiv : i ∈ (CoreCyclic.OnePoint.action B hk w
      (CoreCyclic.phaseAt hk r (J - 1)) P).vars :=
    (mem_vars_iff_mem_support i).2 ⟨m, mem_support_iff.mpr hm, hi⟩
  by_cases him : i = (-1 : ℤ)
  · subst i
    simp
  · let ie : CoreCyclic.OnePoint.ExteriorIndex := ⟨i, him⟩
    simp only [CoreCyclic.OnePoint.movingAssignment, dif_neg him]
    change CoreCyclic.orderedExteriorGap F J ie =
      G * finiteExteriorAssignment w
        (CoreActualFrameJoint.localFrame w J G F) ie
    exact actualExterior_eq_scaledFinite B hk r P w J hJ hw F hG hiv

/-- The actual selected-slot phase is exactly `outer + θ Q_(1/G,Y)(z)`,
with `θ = G^d / B^(J+1)` and the genuine normalized physical frame `Y`. -/
theorem actualFinitePhase_eq_scaledFamily
    {B : ℕ} (hB : 2 ≤ B) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (P : PeriodicLocal k) (K w J d : ℕ)
    (hwJ : w + 1 ≤ J) (hJK : J < K)
    (hw : ∀ s i, i ∈ (P s).vars → i ≤ w)
    (hd : (CoreCyclic.OnePoint.action B hk w
      (CoreCyclic.phaseAt hk r (J - 1)) P).totalDegree ≤ d)
    (A F : Finset ℕ) (hE : (CoreActualCyclicSlot.slot A F J).Nonempty)
    {G : ℝ} (hG : G ≠ 0) {u : ℕ}
    (hu : u ∈ CoreActualCyclicSlot.slot A F J) :
    CoreActualCyclicSlot.actualFinitePhase B hk r P K (insert u F) =
      CoreActualCyclicSlot.selectedOuter B hk r P K w J A F hE +
        (G ^ d / (B : ℝ) ^ (J + 1)) *
          Polynomial.eval
            (((u : ℝ) - (CoreLinearInsertion.insertionSlot F J).1) / G)
            (normalizedActionFamily w d
              (CoreCyclic.OnePoint.action B hk w
                (CoreCyclic.phaseAt hk r (J - 1)) P)
              (G⁻¹, CoreActualFrameJoint.localFrame w J G F)) := by
  let z : ℝ := ((u : ℝ) - (CoreLinearInsertion.insertionSlot F J).1) / G
  have hslot := CoreActualCyclicSlot.actualFinitePhase_eq_selectedOuter_add_scaled
    hB hk r P K w J hwJ hJK hw A F hE hG hu
  have hJ : 1 ≤ J := by omega
  have hactual := actualMovingPolynomial_eval_eq_scaled
    B hk r P w J hJ hw F hG z
  have hscale := normalizedActionFamily_inv_eval w d
    (CoreCyclic.OnePoint.action B hk w
      (CoreCyclic.phaseAt hk r (J - 1)) P) hd
    (CoreActualFrameJoint.localFrame w J G F) hG z
  change CoreActualCyclicSlot.actualFinitePhase B hk r P K (insert u F) =
    CoreActualCyclicSlot.selectedOuter B hk r P K w J A F hE +
      (G ^ d / (B : ℝ) ^ (J + 1)) *
        Polynomial.eval z
          (normalizedActionFamily w d
            (CoreCyclic.OnePoint.action B hk w
              (CoreCyclic.phaseAt hk r (J - 1)) P)
            (G⁻¹, CoreActualFrameJoint.localFrame w J G F))
  rw [hslot, hactual, hscale]
  have hB0 : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [pow_ne_zero d hG, pow_ne_zero (J + 1) hB0] <;> ring

end

end PrimeGapNormality.Prime.CoreCyclicScaledSlot
