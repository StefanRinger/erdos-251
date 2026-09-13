import PrimeGapNormality.Prime.CoreResidueWindow
import PrimeGapNormality.Prime.CoreDigitalReference

/-!
Actual residue windows are consecutive blocks of their arithmetic
progression. The first progression index is characterized by its minimal
absolute index, avoiding truncated-subtraction ceiling conventions.
-/

namespace PrimeGapNormality.Prime.CoreResidueDigitalReference

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

noncomputable section

private theorem exists_progression_ge {k : ℕ} (hk : 1 ≤ k) (r a : ℕ) :
    ∃ q : ℕ, a ≤ q * k + r % k := by
  refine ⟨a, ?_⟩
  have h : a ≤ a * k := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hk
  omega

/-- First progression index whose absolute index is at least `a`. -/
def start {k : ℕ} (hk : 1 ≤ k) (r a : ℕ) : ℕ :=
  Nat.find (exists_progression_ge hk r a)

theorem start_le_iff {k : ℕ} (hk : 1 ≤ k) (r a q : ℕ) :
    start hk r a ≤ q ↔ a ≤ q * k + r % k := by
  constructor
  · intro hq
    have hstart : a ≤ start hk r a * k + r % k :=
      Nat.find_spec (exists_progression_ge hk r a)
    exact hstart.trans (Nat.add_le_add_right (Nat.mul_le_mul_right k hq) _)
  · intro hq
    exact Nat.find_min' (exists_progression_ge hk r a) hq

theorem lt_start_iff {k : ℕ} (hk : 1 ≤ k) (r a q : ℕ) :
    q < start hk r a ↔ q * k + r % k < a := by
  rw [← not_le, start_le_iff, not_le]

theorem mem_progression_interval {k : ℕ} (hk : 1 ≤ k) (r a N q : ℕ) :
    q ∈ Ico (start hk r a) (start hk r (a + N)) ↔
      a ≤ q * k + r % k ∧ q * k + r % k < a + N := by
  rw [mem_Ico, start_le_iff, lt_start_iff]

/-- Exact sum reindexing for every additive codomain, not just positive
tests. This is a genuine finite bijection of the selected indices. -/
theorem sum_reindex_Ico {E : Type*} [AddCommMonoid E] {k : ℕ}
    (hk : 1 ≤ k) (r a N : ℕ) (g : ℕ → E) :
    (∑ i ∈ coreResidueWindowOffsets k r a N, g (a + i)) =
      ∑ q ∈ Ico (start hk r a) (start hk r (a + N)), g (q * k + r % k) := by
  classical
  have hk0 : 0 < k := by omega
  symm
  apply Finset.sum_bij (fun q _ ↦ q * k + r % k - a)
  · intro q hq
    obtain ⟨hlo, hhi⟩ := (mem_progression_interval hk r a N q).1 hq
    apply mem_coreResidueWindowOffsets.2
    constructor
    · omega
    · rw [Nat.add_sub_cancel' hlo]
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  · intro q hq q' hq' heq
    have hlo := ((mem_progression_interval hk r a N q).1 hq).1
    have hlo' := ((mem_progression_interval hk r a N q').1 hq').1
    have hpoints := congrArg (fun i ↦ a + i) heq
    rw [Nat.add_sub_cancel' hlo, Nat.add_sub_cancel' hlo'] at hpoints
    exact Nat.eq_of_mul_eq_mul_right hk0 (Nat.add_right_cancel hpoints)
  · intro i hi
    obtain ⟨hiN, hmod⟩ := mem_coreResidueWindowOffsets.1 hi
    have hdec : (a + i) / k * k + r % k = a + i := by
      rw [Nat.mul_comm, ← hmod]
      exact Nat.div_add_mod (a + i) k
    refine ⟨(a + i) / k, ?_, ?_⟩
    · apply (mem_progression_interval hk r a N _).2
      rw [hdec]
      omega
    · rw [hdec, Nat.add_sub_cancel_left]
  · intro q hq
    have hlo := ((mem_progression_interval hk r a N q).1 hq).1
    rw [Nat.add_sub_cancel' hlo]

theorem count_eq_end_sub_start {k : ℕ} (hk : 1 ≤ k) (r a N : ℕ) :
    coreResidueWindowCount k r a N = start hk r (a + N) - start hk r a := by
  have h := sum_reindex_Ico hk r a N (fun _ ↦ (1 : ℕ))
  simpa only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico,
    Nat.cast_id, id_eq, coreResidueWindowCount] using h

theorem sum_reindex_range {E : Type*} [AddCommMonoid E] {k : ℕ}
    (hk : 1 ≤ k) (r a N : ℕ) (g : ℕ → E) :
    (∑ i ∈ coreResidueWindowOffsets k r a N, g (a + i)) =
      ∑ q ∈ range (coreResidueWindowCount k r a N),
        g ((start hk r a + q) * k + r % k) := by
  rw [sum_reindex_Ico hk r a N g, sum_Ico_eq_sum_range, count_eq_end_sub_start hk r a N]

def progression (k r : ℕ) (u : ℕ → AddCircle (1 : ℝ)) (q : ℕ) : AddCircle (1 : ℝ) :=
  u (q * k + r % k)

theorem progression_recurrence {C k : ℕ} (r : ℕ) (u : ℕ → AddCircle (1 : ℝ))
    (hu : ∀ n, u (n + k) = C • u n) :
    ∀ q, progression k r u (q + 1) = C • progression k r u q := by
  intro q
  unfold progression
  rw [show (q + 1) * k + r % k = (q * k + r % k) + k by ring, hu]

/-- Exact identification with the conditional average on the original
absolute-index residue class. -/
theorem average_eq_progression {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (f : AddCircle (1 : ℝ) →ᵇ ℝ) (a N : ℕ) :
    coreResidueWindowAverage k r u f a N =
      coreDigitalWindowAverage (progression k r u) f (start hk r a)
        (coreResidueWindowCount k r a N) := by
  unfold coreResidueWindowAverage coreDigitalWindowAverage progression
  rw [sum_reindex_range hk r a N (fun n ↦ f (u n))]

/-- Residue progression lengths diverge uniformly in the starting windows.
This follows from literal complete residue blocks, not index equidistribution. -/
theorem count_tendsto_atTop {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun j ↦ coreResidueWindowCount k r (a j) (N j)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [hN.eventually (eventually_ge_atTop (b * k))] with j hj
  have hk0 : 0 < k := by omega
  have hdiv : b ≤ N j / k := by
    calc
      b = b * k / k := by simp [hk0.ne']
      _ ≤ N j / k := Nat.div_le_div_right hj
  exact hdiv.trans (core_card_range_add_mod_ge (a j) (N j) k r hk0)

end

end PrimeGapNormality.Prime.CoreResidueDigitalReference
