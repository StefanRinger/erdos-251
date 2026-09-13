import PrimeGapNormality.Prime.CoreRoughIntervalSlices
import PrimeGapNormality.Prime.CoreMovingRoughSequence
import PrimeGapNormality.Prime.FiniteRootMixInclusionProduct
import PrimeGapNormality.Prime.CrtNestedCutoffFirstMoment

/-!
# Actual full-slice laws with a common Euler normalization

Both laws are divided by Z=sum_i H V(y_i). The empirical law is not
silently normalized by its actual root count. Its total mass is exactly
that count divided by Z, whereas the true rooted-model mixture has mass one.
-/

namespace PrimeGapNormality.Prime.CoreRoughSliceLaws

open Finset CoreMovingRoughSequence CoreRoughMovingCount CoreRoughIntervalSlices
open scoped Classical
noncomputable section

set_option maxHeartbeats 1000000

def normalization (H q : ℕ) (y : ℕ → ℕ) : ℝ :=
  ∑ i ∈ range q, (H : ℝ) * eulerProdNat (y i)

def anchors (z : ℕ → ℕ) (a H q : ℕ) : Finset ℕ :=
  (Ico a (a + q * H)).filter (IsMovingRough z)

def anchorPattern (z : ℕ → ℕ) (Ω : Finset ℕ) (n : ℕ) : Finset ℕ :=
  Ω.filter (fun h => IsMovingRough z (n + h))

def empiricalLaw (z y : ℕ → ℕ) (a H q S : ℕ) (U : Finset ℕ) : ℝ :=
  (((anchors z a H q).filter
    (fun n => anchorPattern z (offsetWindow S) n = U)).card : ℝ) / normalization H q y

def modelLaw (y : ℕ → ℕ) (H q S : ℕ) (U : Finset ℕ) : ℝ :=
  (∑ i ∈ range q, (H : ℝ) * eulerProdNat (y i) * actualRootLaw (y i) S U) /
    normalization H q y

theorem normalization_nonneg (H q : ℕ) (y : ℕ → ℕ) : 0 ≤ normalization H q y :=
  Finset.sum_nonneg fun i hi => mul_nonneg (Nat.cast_nonneg _) (eulerProdNat_pos _).le

theorem empiricalLaw_nonneg (z y : ℕ → ℕ) (a H q S : ℕ) (U : Finset ℕ) :
    0 ≤ empiricalLaw z y a H q S U :=
  div_nonneg (Nat.cast_nonneg _) (normalization_nonneg H q y)

theorem modelLaw_nonneg (y : ℕ → ℕ) (H q S : ℕ) (U : Finset ℕ) :
    0 ≤ modelLaw y H q S U := by
  unfold modelLaw
  apply div_nonneg _ (normalization_nonneg H q y)
  exact Finset.sum_nonneg fun i hi => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (eulerProdNat_pos _).le) (actualRootLaw_nonneg _ _ _)

theorem anchorPattern_mem (z : ℕ → ℕ) (Ω : Finset ℕ) (n : ℕ) :
    anchorPattern z Ω n ∈ Ω.powerset :=
  Finset.mem_powerset.mpr (Finset.filter_subset _ _)

/-- The exact finite empirical pushforward; empty samples are included. -/
theorem empiricalLaw_eval (z y : ℕ → ℕ) (a H q S : ℕ) (f : Finset ℕ → ℝ) :
    (∑ U ∈ (offsetWindow S).powerset, empiricalLaw z y a H q S U * f U) =
      (∑ n ∈ anchors z a H q, f (anchorPattern z (offsetWindow S) n)) / normalization H q y := by
  have hpoint (U : Finset ℕ) : empiricalLaw z y a H q S U =
      (∑ n ∈ anchors z a H q, if anchorPattern z (offsetWindow S) n = U then (1 : ℝ) else 0) /
        normalization H q y := by
    simp only [empiricalLaw, Finset.sum_boole]
  simp_rw [hpoint, div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (anchorPattern_mem z (offsetWindow S) n)]

theorem empiricalLaw_total (z y : ℕ → ℕ) (a H q S : ℕ) :
    (∑ U ∈ (offsetWindow S).powerset, empiricalLaw z y a H q S U) =
      ((anchors z a H q).card : ℝ) / normalization H q y := by
  simpa only [mul_one, sum_const, nsmul_one] using empiricalLaw_eval z y a H q S (fun _ => 1)

/-- Exact finite disintegration of the true slice mixture. -/
theorem modelLaw_eval (y : ℕ → ℕ) (H q S : ℕ) (f : Finset ℕ → ℝ) :
    (∑ U ∈ (offsetWindow S).powerset, modelLaw y H q S U * f U) =
      (∑ i ∈ range q, (H : ℝ) * eulerProdNat (y i) *
        (∑ U ∈ (offsetWindow S).powerset, actualRootLaw (y i) S U * f U)) /
          normalization H q y := by
  unfold modelLaw
  simp_rw [div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  ring

theorem modelLaw_total (y : ℕ → ℕ) (H q S : ℕ) (hZ : 0 < normalization H q y) :
    (∑ U ∈ (offsetWindow S).powerset, modelLaw y H q S U) = 1 := by
  have hh := modelLaw_eval y H q S (fun _ => 1)
  simp only [mul_one, crtNestFM_actualRootLaw_sum] at hh
  refine hh.trans ?_
  change normalization H q y / normalization H q y = 1
  exact div_self hZ.ne'

theorem subset_anchorPattern_iff (z : ℕ → ℕ) {Ω E : Finset ℕ} (hE : E ⊆ Ω) (n : ℕ) :
    E ⊆ anchorPattern z Ω n ↔ ∀ h ∈ E, IsMovingRough z (n + h) := by
  constructor
  · intro hsub h hh
    exact (mem_filter.mp (hsub hh)).2
  · intro hrough h hh
    exact mem_filter.mpr ⟨hE hh, hrough h hh⟩

theorem anchors_filter_subset_eq_tuple (z : ℕ → ℕ) (a H q S : ℕ)
    {E : Finset ℕ} (hE : E ⊆ offsetWindow S) :
    (anchors z a H q).filter (fun n => E ⊆ anchorPattern z (offsetWindow S) n) =
      movingTupleInterval z (insert 0 E) a (q * H) := by
  ext n
  simp only [anchors, movingTupleInterval, mem_filter, subset_anchorPattern_iff z hE]
  constructor
  · rintro ⟨⟨hnI, hn⟩, hshift⟩
    refine ⟨hnI, ?_⟩
    intro h hh
    rcases mem_insert.mp hh with rfl | hh
    · simpa only [Nat.add_zero, RoughAt, IsMovingRough] using hn
    · exact hshift h hh
  · rintro ⟨hnI, hrough⟩
    refine ⟨⟨hnI, ?_⟩, fun h hh => hrough h (mem_insert_of_mem hh)⟩
    simpa only [Nat.add_zero, RoughAt, IsMovingRough] using hrough 0 (mem_insert_self 0 E)

/-- Empirical inclusions are the literal full-slice moving tuple counts,
with the root adjoined, divided by the Euler normalization. -/
theorem empiricalLaw_inclusion (z y : ℕ → ℕ) (a H q S : ℕ)
    {E : Finset ℕ} (hE : E ⊆ offsetWindow S) :
    Stopped.inclusionMass (offsetWindow S) (empiricalLaw z y a H q S) E =
      ((movingTupleInterval z (insert 0 E) a (q * H)).card : ℝ) / normalization H q y := by
  have hh := empiricalLaw_eval z y a H q S (fun U => if E ⊆ U then 1 else 0)
  have hl : (∑ U ∈ (offsetWindow S).powerset, empiricalLaw z y a H q S U *
      (if E ⊆ U then 1 else 0)) =
      Stopped.inclusionMass (offsetWindow S) (empiricalLaw z y a H q S) E := by
    simp [Stopped.inclusionMass, Finset.sum_filter]
  rw [hl, Finset.sum_boole, anchors_filter_subset_eq_tuple z a H q S hE] at hh
  exact hh

/-- Exact root cancellation supplies the model tuple main term. No
nonzero tuple factor or cutoff-size condition is used. -/
theorem modelLaw_inclusion (y : ℕ → ℕ) (H q S : ℕ)
    {E : Finset ℕ} (hE : E ⊆ offsetWindow S) :
    Stopped.inclusionMass (offsetWindow S) (modelLaw y H q S) E =
      (∑ i ∈ range q, (H : ℝ) * finiteTupleSieveProduct (insert 0 E) (y i)) /
        normalization H q y := by
  have hh := modelLaw_eval y H q S (fun U => if E ⊆ U then 1 else 0)
  have hid (μ : Finset ℕ → ℝ) :
      (∑ U ∈ (offsetWindow S).powerset, μ U * (if E ⊆ U then 1 else 0)) =
        Stopped.inclusionMass (offsetWindow S) μ E := by
    simp [Stopped.inclusionMass, Finset.sum_filter]
  simp only [hid] at hh
  rw [hh]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc, eulerProd_mul_actualRootLaw_inclusionMass (y i) S hE]

/-- Direct finite aggregation of cell count errors into inclusion errors
under the common normalization. This is an elementary aggregation lemma,
not an assumption in the definitions of either law. -/
theorem inclusion_error_of_cell_errors (z y : ℕ → ℕ) (a H q S : ℕ)
    (hZ : 0 < normalization H q y) {E : Finset ℕ} (hE : E ⊆ offsetWindow S)
    (error : ℕ → ℝ)
    (hcell : ∀ i ∈ range q,
      |((movingTupleInterval z (insert 0 E) (a + i * H) H).card : ℝ) -
        (H : ℝ) * finiteTupleSieveProduct (insert 0 E) (y i)| ≤ error i) :
    |Stopped.inclusionMass (offsetWindow S) (empiricalLaw z y a H q S) E -
      Stopped.inclusionMass (offsetWindow S) (modelLaw y H q S) E| ≤
        (∑ i ∈ range q, error i) / normalization H q y := by
  rw [empiricalLaw_inclusion z y a H q S hE, modelLaw_inclusion y H q S hE,
    ← sub_div, abs_div, abs_of_pos hZ]
  apply div_le_div_of_nonneg_right _ hZ.le
  have hsplit : ((movingTupleInterval z (insert 0 E) a (q * H)).card : ℝ) =
      ∑ i ∈ range q, ((movingTupleInterval z (insert 0 E) (a + i * H) H).card : ℝ) := by
    simp only [movingTupleInterval_count_eq]
    exact predicateCount_mul
      (fun n : ℕ => ∀ h ∈ insert 0 E, RoughAt (z (n + h)) (n + h)) a H q
  rw [hsplit, ← Finset.sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hcell)

end
end PrimeGapNormality.Prime.CoreRoughSliceLaws
