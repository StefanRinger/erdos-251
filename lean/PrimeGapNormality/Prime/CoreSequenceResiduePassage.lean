import PrimeGapNormality.Prime.CoreResidueSubsequenceReference
import PrimeGapNormality.Prime.PhysicalWindowST

/-!
# Residue passage for an arbitrary increasing sequence

For a strictly increasing sequence `a`, the physical dyadic window of
`q ↦ a (q*k+r)` is exactly the corresponding residue slice of the original
index interval

`Ico (seqCount a X) (seqCount a (2*X))`.

If the original physical-window count tends to infinity, elementary residue
counting gives the same property on every fixed progression.  The generic
physical-window-to-Cesàro theorem can then consume the actual
subsequence-reference residue cancellation.  No prime-counting or
rough-number theorem is assumed here.
-/

namespace PrimeGapNormality.Prime.CoreSequenceResiduePassage

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

noncomputable section

/-- Restriction of an arbitrary sequence to one zero-based index residue
class. -/
def residueSequence (a : ℕ → ℕ) (k r q : ℕ) : ℕ :=
  a (q * k + r)

/-- Number of original sequence indices in the physical dyadic window. -/
def seqCountDifference (a : ℕ → ℕ) (X : ℕ) : ℕ :=
  seqCount a (2 * X) - seqCount a X

theorem residueSequence_strictMono {a : ℕ → ℕ} (ha : StrictMono a)
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    StrictMono (residueSequence a k r) := by
  intro q q' hqq'
  apply ha
  have hk0 : 0 < k := by omega
  have hmul : q * k < q' * k := (Nat.mul_lt_mul_right hk0).2 hqq'
  exact Nat.add_lt_add_right hmul r

private theorem mem_seqWindow_strict_iff {a : ℕ → ℕ} (ha : StrictMono a)
    {X n : ℕ} : n ∈ seqWindow a X ↔ X < a n ∧ a n ≤ 2 * X := by
  simp only [seqWindow, mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨le_trans (strictMono_le_id ha n) h.2, h⟩

private theorem seqCount_le_iff_lt_apply {a : ℕ → ℕ} (ha : StrictMono a)
    {X n : ℕ} : seqCount a X ≤ n ↔ X < a n := by
  simpa only [not_lt, not_le] using
    not_congr (seqCount_lt_iff (a := a) ha :
      n < seqCount a X ↔ a n ≤ X)

/-- Every physical window is literally the interval between its two counting
function endpoints. -/
theorem seqWindow_eq_Ico_seqCount {a : ℕ → ℕ} (ha : StrictMono a) (X : ℕ) :
    seqWindow a X = Ico (seqCount a X) (seqCount a (2 * X)) := by
  ext n
  rw [mem_seqWindow_strict_iff ha, mem_Ico,
    seqCount_le_iff_lt_apply ha, seqCount_lt_iff ha]

theorem seqWindow_card_eq_countDifference {a : ℕ → ℕ}
    (ha : StrictMono a) (X : ℕ) :
    (seqWindow a X).card = seqCountDifference a X := by
  rw [seqWindow_eq_Ico_seqCount ha, Nat.card_Ico]
  rfl

theorem seqCount_add_countDifference (a : ℕ → ℕ) (X : ℕ) :
    seqCount a X + seqCountDifference a X = seqCount a (2 * X) := by
  unfold seqCountDifference
  rw [Nat.add_sub_of_le (seqCount_mono (a := a) (by omega))]

/-- Exact physical-window membership for the residue subsequence. -/
theorem mem_seqWindow_residueSequence_iff
    {a : ℕ → ℕ} (ha : StrictMono a) {k r X q : ℕ}
    (hk : 1 ≤ k) (hr : r < k) :
    q ∈ seqWindow (residueSequence a k r) X ↔
      q ∈ Ico
        (CoreResidueDigitalReference.start hk r (seqCount a X))
        (CoreResidueDigitalReference.start hk r (seqCount a (2 * X))) := by
  rw [mem_seqWindow_strict_iff (residueSequence_strictMono ha hk r), mem_Ico,
    CoreResidueDigitalReference.start_le_iff,
    CoreResidueDigitalReference.lt_start_iff, Nat.mod_eq_of_lt hr,
    seqCount_le_iff_lt_apply ha, seqCount_lt_iff ha]
  rfl

/-- The complete finite-set identity for an arbitrary increasing sequence. -/
theorem seqWindow_residueSequence_eq_Ico
    {a : ℕ → ℕ} (ha : StrictMono a) {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < k) (X : ℕ) :
    seqWindow (residueSequence a k r) X =
      Ico
        (CoreResidueDigitalReference.start hk r (seqCount a X))
        (CoreResidueDigitalReference.start hk r (seqCount a (2 * X))) := by
  ext q
  exact mem_seqWindow_residueSequence_iff ha hk hr

/-- Its cardinality is the actual residue count inside the original index
window, with no asymptotic replacement. -/
theorem seqWindow_residueSequence_card_eq
    {a : ℕ → ℕ} (ha : StrictMono a) {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < k) (X : ℕ) :
    (seqWindow (residueSequence a k r) X).card =
      coreResidueWindowCount k r (seqCount a X) (seqCountDifference a X) := by
  rw [seqWindow_residueSequence_eq_Ico ha hk hr, Nat.card_Ico]
  have hcount := CoreResidueDigitalReference.count_eq_end_sub_start
    hk r (seqCount a X) (seqCountDifference a X)
  rw [seqCount_add_countDifference] at hcount
  exact hcount.symm

/-- Original window growth is exactly growth of the natural count
difference. -/
theorem tendsto_seqCountDifference_atTop
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a) :
    Tendsto (seqCountDifference a) atTop atTop := by
  have hreal : Tendsto (fun X : ℕ => (seqCountDifference a X : ℝ))
      atTop atTop := by
    exact hcount.congr' (Eventually.of_forall fun X => by
      rw [seqWindow_card_eq_countDifference ha])
  exact tendsto_natCast_atTop_iff.mp hreal

/-- Residue-subsequence window cardinalities diverge solely from the original
`WindowCountToInfinity` hypothesis and complete residue blocks. -/
theorem tendsto_seqWindow_residueSequence_card_atTop
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {k r : ℕ} (hk : 1 ≤ k) (hr : r < k) :
    Tendsto (fun X => (seqWindow (residueSequence a k r) X).card)
      atTop atTop := by
  have hresidue := CoreResidueDigitalReference.count_tendsto_atTop hk r
    (fun X => seqCount a X) (seqCountDifference a)
    (tendsto_seqCountDifference_atTop ha hcount)
  exact hresidue.congr' (Eventually.of_forall fun X =>
    (seqWindow_residueSequence_card_eq ha hk hr X).symm)

theorem residueSequence_windowCountToInfinity
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {k r : ℕ} (hk : 1 ≤ k) (hr : r < k) :
    WindowCountToInfinity (residueSequence a k r) := by
  unfold WindowCountToInfinity
  have hcast := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (tendsto_seqWindow_residueSequence_card_atTop ha hcount hk hr)
  simpa only [Function.comp_def] using hcast

/-- Exact equality between a physical residue-subsequence average and the
corresponding residue-window average on the original indices. -/
theorem windowAvg_residueSequence_eq_residueWindow
    {a : ℕ → ℕ} (ha : StrictMono a) {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < k) (g : ℕ → ℂ) (X : ℕ) :
    windowAvg (seqWindow (residueSequence a k r) X)
        (fun q => g (q * k + r)) =
      (∑ i ∈ coreResidueWindowOffsets k r (seqCount a X)
          (seqCountDifference a X), g (seqCount a X + i)) /
        (coreResidueWindowCount k r (seqCount a X)
          (seqCountDifference a X) : ℂ) := by
  have hsum := CoreResidueDigitalReference.sum_reindex_Ico hk r
    (seqCount a X) (seqCountDifference a X) g
  rw [seqCount_add_countDifference] at hsum
  have hsum' :
      (∑ q ∈ seqWindow (residueSequence a k r) X, g (q * k + r)) =
        ∑ i ∈ coreResidueWindowOffsets k r (seqCount a X)
          (seqCountDifference a X), g (seqCount a X + i) := by
    rw [seqWindow_residueSequence_eq_Ico ha hk hr]
    simpa only [Nat.mod_eq_of_lt hr] using hsum.symm
  unfold windowAvg
  rw [hsum', seqWindow_residueSequence_card_eq ha hk hr]

/-- Bounded physical-window cancellation on a residue subsequence passes to
its full prefix Cesàro means by the actual generic window-count theorem. -/
theorem cesaro_of_residueSequence_physicalWindow
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {k r : ℕ} (hk : 1 ≤ k) (hr : r < k) (f : ℕ → ℂ)
    (hf : ∀ q, ‖f q‖ ≤ 1)
    (hphysical : PhysicalWindowMeanVanishing (residueSequence a k r) f) :
    CesaroMeanVanishing f :=
  windowCountToCesaro (residueSequence a k r)
    (residueSequence_strictMono ha hk r)
    (residueSequence_windowCountToInfinity ha hcount hk hr)
    f hf hphysical

/-- Residue-window character cancellation on the original index sequence
gives global Cesàro cancellation on `q ↦ a(q*k+r)`. -/
theorem residue_character_cesaro_of_residueWindows
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {k r : ℕ} (hk : 1 ≤ k) (hr : r < k)
    (u : ℕ → AddCircle (1 : ℝ)) (z : ℤ)
    (hresidue : Tendsto (fun X =>
      (∑ i ∈ coreResidueWindowOffsets k r (seqCount a X)
          (seqCountDifference a X), fourier z (u (seqCount a X + i))) /
        (coreResidueWindowCount k r (seqCount a X)
          (seqCountDifference a X) : ℂ)) atTop (𝓝 0)) :
    CesaroMeanVanishing (fun q => fourier z (u (q * k + r))) := by
  apply cesaro_of_residueSequence_physicalWindow ha hcount hk hr
  · intro q
    exact (Circle.norm_coe _).le
  · unfold PhysicalWindowMeanVanishing
    exact hresidue.congr' (Eventually.of_forall fun X =>
      (windowAvg_residueSequence_eq_residueWindow ha hk hr
        (fun n => fourier z (u n)) X).symm)

/-- Fully generic endpoint from the actual subsequence-reference contract.
The reference measure may depend on a proposed subsequence but is fixed
before the test and tolerance, exactly as required by the compiled theorem. -/
theorem residue_character_cesaro_of_subsequence_reference
    {a : ℕ → ℕ} (ha : StrictMono a) (hcount : WindowCountToInfinity a)
    {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k) {r : ℕ} (hr : r < k)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (hbound : CoreResidueDigitalReference.SubsequenceReferenceBounds u
      (fun X => seqCount a X) (seqCountDifference a))
    {z : ℤ} (hz : z ≠ 0) :
    CesaroMeanVanishing (fun q => fourier z (u (q * k + r))) := by
  apply residue_character_cesaro_of_residueWindows ha hcount hk hr u z
  exact CoreResidueDigitalReference.residue_characters_tendsto_zero_of_subsequence_reference
    hC hk r u hu (fun X => seqCount a X) (seqCountDifference a)
    (tendsto_seqCountDifference_atTop ha hcount) hbound hz

end
end PrimeGapNormality.Prime.CoreSequenceResiduePassage
