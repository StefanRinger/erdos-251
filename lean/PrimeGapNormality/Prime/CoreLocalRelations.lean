import PrimeGapNormality.Prime.CorePrimeLocalNormality
import PrimeGapNormality.Prime.JointWeyl

/-!
# Actual finite-family relations and common-clock joint Weyl

Every nonzero character is treated as one genuine rational combination of
local tuples. Separate scalar normality is never used as a substitute for
joint cancellation. The arithmetic profile and effective-degree budget are
the same for the whole fixed finite family.
-/

namespace PrimeGapNormality.Prime.CoreLocalRelations

open Finset Filter MvPolynomial CoreCyclic
open scoped Topology

noncomputable section

set_option maxHeartbeats 600000

/-- Unconditional summability, including tuples whose original degree is
higher than the effective normal-form degree. -/
theorem primeSeries_summable {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (F : PeriodicLocal k) :
    Summable (fun n : ℕ => localValue hk phase (fun q => (primeGap q : ℝ)) F n /
      (B : ℝ) ^ (n + 1)) :=
  (primeLocalSeries_and_normalForm_summable hB hk phase F).1

private theorem localValue_smul {k : ℕ} (hk : 0 < k) (phase : Fin k)
    (g : ℕ → ℝ) (q : ℚ) (F : PeriodicLocal k) (n : ℕ) :
    localValue hk phase g (q • F) n = (q : ℝ) * localValue hk phase g F n := by
  simp [localValue, Pi.smul_apply, smul_eq_C_mul]

/-- The actual infinite prime-gap series, as a rational linear map.
Additivity uses the proved summability, not formal manipulation of tsums. -/
def primeSeriesLinear {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k) :
    PeriodicLocal k →ₗ[ℚ] ℝ where
  toFun := coreCyclicFullSeries B hk phase (fun q => (primeGap q : ℝ))
  map_add' F H := by
    unfold coreCyclicFullSeries
    simp_rw [localValue_add, add_div]
    exact (primeSeries_summable hB hk phase F).tsum_add
      (primeSeries_summable hB hk phase H)
  map_smul' q F := by
    change coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (q • F) =
      q • coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) F
    unfold coreCyclicFullSeries
    simp_rw [localValue_smul, mul_div_assoc]
    rw [tsum_mul_left, Rat.smul_def]

/-- Exact finite rational-combination identity for the full convergent
series, with no truncation or omitted boundary. -/
theorem fullSeries_sum_smul {I : Type*} [Fintype I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k) (q : I → ℚ) :
    coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (∑ i, q i • F i) =
      ∑ i, (q i : ℝ) * coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (F i) := by
  change primeSeriesLinear hB hk phase (∑ i, q i • F i) =
    ∑ i, (q i : ℝ) * primeSeriesLinear hB hk phase (F i)
  simp only [map_sum, map_smul, Rat.smul_def]

theorem normalForm_sum_smul {I : Type*} [Fintype I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : I → PeriodicLocal k) (q : I → ℚ) :
    normalForm hB hk (∑ i, q i • F i) = ∑ i, q i • normalForm hB hk (F i) := by
  change normalFormLinear hB hk (∑ i, q i • F i) =
    ∑ i, q i • normalFormLinear hB hk (F i)
  simp only [map_sum, map_smul]

/-- A common effective-degree budget is closed under all rational
combinations, including ones with cancellation of their top components. -/
theorem topDegree_normalForm_sum_le {I : Type*} [Fintype I]
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : I → PeriodicLocal k) (q : I → ℚ)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d) :
    topDegree (normalForm hB hk (∑ i, q i • F i)) ≤ d := by
  rw [normalForm_sum_smul]
  unfold topDegree
  apply Finset.sup_le
  intro s hs
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply totalDegree_finsetSum_le
  intro i hi
  exact (totalDegree_smul_le (q i) (normalForm hB hk (F i) s)).trans
    ((Finset.le_sup (f := fun s : Fin k => (normalForm hB hk (F i) s).totalDegree)
      (mem_univ s)).trans (hdeg i))

/-- Actual D gives Weyl for every combination whose canonical class is
nonzero. The profile is fixed before selecting the coefficients. -/
theorem combination_weyl_clock_of_D {I : Type*} [Fintype I]
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c)
    (q : I → ℚ) (hq : (∑ i, q i • normalForm hB hk (F i)) ≠ 0) :
    weylCriterion (B ^ k)
      (∑ i, (q i : ℝ) * coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (F i)) := by
  have hlog : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hκq : (topDegree (normalForm hB hk (∑ i, q i • F i)) : ℝ) /
      Real.log (B : ℝ) ≤ κ :=
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr
      (topDegree_normalForm_sum_le hB hk F q hdeg)) hlog).trans hκ
  have hW := corePrime_local_weyl_clock_of_D hB hk phase (∑ i, q i • F i)
    (by rwa [normalForm_sum_smul]) hκq hd0 hc hD
  rwa [fullSeries_sum_smul hB hk phase F q] at hW

/-- A zero class gives the exact explicitly constructed rational boundary
of the combined tuple, without any arithmetic hypothesis. -/
theorem combination_eq_boundary_of_normalForm_zero {I : Type*} [Fintype I]
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k) (q : I → ℚ)
    (hq : (∑ i, q i • normalForm hB hk (F i)) = 0) :
    (∑ i, (q i : ℝ) * coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (F i)) =
      (primeLocalBoundaryRat hB hk phase (∑ i, q i • F i) : ℝ) := by
  rw [← fullSeries_sum_smul hB hk phase F q]
  exact coreCyclicFullSeries_eq_boundary_of_normalForm_zero hB hk phase _
    (by rwa [normalForm_sum_smul])

/-- All rational relations are exactly the relations of canonical normal
classes, under the one common effective-degree D budget. -/
theorem rational_relation_iff_of_D {I : Type*} [Fintype I]
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) (q : I → ℚ) :
    (∃ a : ℚ, (∑ i, (q i : ℝ) *
      coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (F i)) = (a : ℝ)) ↔
      (∑ i, q i • normalForm hB hk (F i)) = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    by_contra hn
    exact (weylCriterion_irrational
      (combination_weyl_clock_of_D hB hk phase F hdeg hκ hd0 hc hD q hn)) ⟨a, ha.symm⟩
  · intro hq
    exact ⟨primeLocalBoundaryRat hB hk phase (∑ i, q i • F i),
      combination_eq_boundary_of_normalForm_zero hB hk phase F q hq⟩

/-- Q-independent normal classes give the actual common-clock joint Weyl
criterion, by testing every nonzero integer frequency vector. -/
theorem jointWeyl_of_independent_normalForms_of_D
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    JointWeyl (fun _ : I => B ^ k)
      (fun i => coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (F i)) := by
  intro t ht
  have hq : (∑ i, (t i : ℚ) • normalForm hB hk (F i)) ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := ht
    have heq := (Fintype.linearIndependent_iff.mp hlin) (fun i => (t i : ℚ)) hz i
    exact hi (Int.cast_eq_zero.mp heq)
  have hW := combination_weyl_clock_of_D hB hk phase F hdeg hκ hd0 hc hD
    (fun i => (t i : ℚ)) hq
  have hchar := hW 1 (by norm_num)
  have heq (n : ℕ) :
      (∑ i, (t i : ℝ) * ((B ^ k : ℕ) : ℝ) ^ n *
        coreCyclicFullSeries B hk phase (fun q => (primeGap q : ℝ)) (F i)) =
      ((1 : ℤ) : ℝ) * ((B ^ k : ℕ) : ℝ) ^ n *
        (∑ i, ((t i : ℚ) : ℝ) *
          coreCyclicFullSeries B hk phase (fun q => (primeGap q : ℝ)) (F i)) := by
    simp only [Int.cast_one, one_mul, Rat.cast_intCast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa only [heq] using hchar

/-- In particular 1 and the actual series are rationally linearly
independent. This follows from joint cancellation, not individual normality. -/
theorem linearIndependent_one_of_independent_normalForms_of_D
    {I : Type*} [Fintype I] [DecidableEq I]
    {B k d : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    (F : I → PeriodicLocal k)
    (hdeg : ∀ i, topDegree (normalForm hB hk (F i)) ≤ d)
    (hlin : LinearIndependent ℚ (fun i => normalForm hB hk (F i)))
    {κ d0 c : ℝ} (hκ : (d : ℝ) / Real.log (B : ℝ) ≤ κ)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD κ d0 c) :
    LinearIndependent ℚ (fun i : Option I => match i with
      | none => (1 : ℝ)
      | some i => coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ)) (F i)) := by
  have hclock : 2 ≤ B ^ k := by
    have hsplit : k = k - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
    rw [hsplit, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  exact linearIndependent_one_jointWeyl hclock
    (jointWeyl_of_independent_normalForms_of_D hB hk phase F hdeg hlin hκ hd0 hc hD)

end
end PrimeGapNormality.Prime.CoreLocalRelations
