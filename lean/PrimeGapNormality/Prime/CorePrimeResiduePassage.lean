import PrimeGapNormality.Prime.CoreResidueDigitalReferenceLimit
import PrimeGapNormality.Prime.CorePrimeDensityBounds
import PrimeGapNormality.Prime.PhysicalWindowST

/-!
# Prime residue windows and global Cesàro means

For a fixed residue `r < k`, the increasing sequence
`q ↦ nthPrime (q * k + r)` has a physical dyadic window which is literally
the corresponding arithmetic-progression slice of the prime-index interval
`[π(X), π(2X))`.  Its window count tends to infinity by the unconditional
dyadic prime-count lower bound and elementary residue counting.  Thus the
general window-count-to-Cesàro theorem applies without an index-class
equidistribution or PNT premise.
-/

namespace PrimeGapNormality.Prime.CorePrimeResiduePassage

open Finset Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

noncomputable section

/-- The primes whose zero-based indices lie in the fixed class `r mod k`. -/
def primeResidueSequence (k r q : ℕ) : ℕ :=
  nthPrime (q * k + r)

theorem primeResidueSequence_strictMono {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    StrictMono (primeResidueSequence k r) := by
  intro q q' hqq'
  apply nthPrime_strictMono
  have hk0 : 0 < k := by omega
  have hmul : q * k < q' * k := (Nat.mul_lt_mul_right hk0).2 hqq'
  exact Nat.add_lt_add_right hmul r

private theorem mem_seqWindow_iff {a : ℕ → ℕ} (ha : StrictMono a)
    {X n : ℕ} : n ∈ seqWindow a X ↔ X < a n ∧ a n ≤ 2 * X := by
  simp only [seqWindow, mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨le_trans (strictMono_le_id ha n) h.2, h⟩

/-- Exact membership correspondence between a physical window of the residue
prime sequence and its interval of progression indices. -/
theorem mem_seqWindow_primeResidueSequence_iff {k r X q : ℕ}
    (hk : 1 ≤ k) (hr : r < k) :
    q ∈ seqWindow (primeResidueSequence k r) X ↔
      q ∈ Ico
        (CoreResidueDigitalReference.start hk r (Nat.primeCounting X))
        (CoreResidueDigitalReference.start hk r (Nat.primeCounting (2 * X))) := by
  rw [mem_seqWindow_iff (primeResidueSequence_strictMono hk r), mem_Ico,
    CoreResidueDigitalReference.start_le_iff,
    CoreResidueDigitalReference.lt_start_iff, Nat.mod_eq_of_lt hr]
  simpa only [primeResidueSequence, Finset.mem_Ico] using
    (mem_dyadic_prime_index_iff (n := q * k + r) (X := X)).symm

/-- The complete finite-set identity behind the residue passage. -/
theorem seqWindow_primeResidueSequence_eq_Ico {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < k) (X : ℕ) :
    seqWindow (primeResidueSequence k r) X =
      Ico
        (CoreResidueDigitalReference.start hk r (Nat.primeCounting X))
        (CoreResidueDigitalReference.start hk r (Nat.primeCounting (2 * X))) := by
  ext q
  exact mem_seqWindow_primeResidueSequence_iff hk hr

private theorem primeCounting_add_windowNX (X : ℕ) :
    Nat.primeCounting X + windowNX X = Nat.primeCounting (2 * X) := by
  have hle : Nat.primeCounting X ≤ Nat.primeCounting (2 * X) :=
    Nat.monotone_primeCounting (by omega)
  unfold windowNX
  omega

/-- Its cardinality is exactly the previously constructed residue-window
count, with no asymptotic replacement. -/
theorem seqWindow_primeResidueSequence_card_eq {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < k) (X : ℕ) :
    (seqWindow (primeResidueSequence k r) X).card =
      coreResidueWindowCount k r (Nat.primeCounting X) (windowNX X) := by
  rw [seqWindow_primeResidueSequence_eq_Ico hk hr, Nat.card_Ico]
  have hcount := CoreResidueDigitalReference.count_eq_end_sub_start
    hk r (Nat.primeCounting X) (windowNX X)
  rw [primeCounting_add_windowNX] at hcount
  exact hcount.symm

/-- Residue prime-window cardinalities diverge unconditionally. -/
theorem tendsto_seqWindow_primeResidueSequence_card_atTop {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < k) :
    Tendsto (fun X ↦ (seqWindow (primeResidueSequence k r) X).card)
      atTop atTop := by
  have hcount := CoreResidueDigitalReference.count_tendsto_atTop hk r
    (fun X ↦ Nat.primeCounting X) windowNX
    CorePrimeDensity.tendsto_windowNX_atTop
  exact hcount.congr' (Eventually.of_forall fun X ↦
    (seqWindow_primeResidueSequence_card_eq hk hr X).symm)

/-- Real-valued window-count growth in the exact form consumed by the
physical-window-to-Cesàro bridge. -/
theorem primeResidueSequence_windowCountToInfinity {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < k) :
    WindowCountToInfinity (primeResidueSequence k r) := by
  unfold WindowCountToInfinity
  have hcast := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (tendsto_seqWindow_primeResidueSequence_card_atTop hk hr)
  simpa only [Function.comp_def] using hcast

/-- Exact equality between the physical window average of the reindexed
prime sequence and the residue-window average on the original indices. -/
theorem windowAvg_primeResidueSequence_eq_residueWindow {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < k) (g : ℕ → ℂ) (X : ℕ) :
    windowAvg (seqWindow (primeResidueSequence k r) X)
        (fun q ↦ g (q * k + r)) =
      (∑ i ∈ coreResidueWindowOffsets k r (Nat.primeCounting X) (windowNX X),
          g (Nat.primeCounting X + i)) /
        (coreResidueWindowCount k r (Nat.primeCounting X) (windowNX X) : ℂ) := by
  have hsum := CoreResidueDigitalReference.sum_reindex_Ico hk r
    (Nat.primeCounting X) (windowNX X) g
  rw [primeCounting_add_windowNX] at hsum
  have hsum' :
      (∑ q ∈ seqWindow (primeResidueSequence k r) X, g (q * k + r)) =
        ∑ i ∈ coreResidueWindowOffsets k r (Nat.primeCounting X) (windowNX X),
          g (Nat.primeCounting X + i) := by
    rw [seqWindow_primeResidueSequence_eq_Ico hk hr]
    simpa only [Nat.mod_eq_of_lt hr] using hsum.symm
  unfold windowAvg
  rw [hsum', seqWindow_primeResidueSequence_card_eq hk hr]

/-- Any bounded physical-window cancellation on the actual residue prime
sequence passes to its full prefix Cesàro means. -/
theorem cesaro_of_primeResidue_physicalWindow {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < k) (f : ℕ → ℂ)
    (hf : ∀ q, ‖f q‖ ≤ 1)
    (hphysical : PhysicalWindowMeanVanishing (primeResidueSequence k r) f) :
    CesaroMeanVanishing f :=
  windowCountToCesaro (primeResidueSequence k r)
    (primeResidueSequence_strictMono hk r)
    (primeResidueSequence_windowCountToInfinity hk hr) f hf hphysical

/-- Residue-window Fourier cancellation on the original prime indices gives
global Cesàro cancellation along `q ↦ nthPrime (qk+r)`. -/
theorem primeResidue_character_cesaro_of_residueWindows {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < k) (u : ℕ → AddCircle (1 : ℝ)) (z : ℤ)
    (hresidue : Tendsto (fun X ↦
      (∑ i ∈ coreResidueWindowOffsets k r (Nat.primeCounting X) (windowNX X),
          fourier z (u (Nat.primeCounting X + i))) /
        (coreResidueWindowCount k r (Nat.primeCounting X) (windowNX X) : ℂ))
      atTop (𝓝 0)) :
    CesaroMeanVanishing (fun q ↦ fourier z (u (q * k + r))) := by
  apply cesaro_of_primeResidue_physicalWindow hk hr
  · intro q
    exact (Circle.norm_coe _).le
  · unfold PhysicalWindowMeanVanishing
    exact hresidue.congr' (Eventually.of_forall fun X ↦
      (windowAvg_primeResidueSequence_eq_residueWindow hk hr
        (fun n ↦ fourier z (u n)) X).symm)

/-- Fully packaged use of the green residue-limit theorem. The only analytic
input is the explicit positive reference bound on the original full index
windows; window growth is supplied unconditionally above. -/
theorem primeResidue_character_cesaro_of_reference_bounds
    {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k) {r : ℕ} (hr : r < k)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (σ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure σ]
    (hσ : σ ≪ volume) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
        coreDigitalWindowAverage u f (Nat.primeCounting X) (windowNX X) ≤
          A * (∫ x, f x ∂σ) + ε)
    {z : ℤ} (hz : z ≠ 0) :
    CesaroMeanVanishing (fun q ↦ fourier z (u (q * k + r))) := by
  apply primeResidue_character_cesaro_of_residueWindows hk hr u z
  exact CoreResidueDigitalReference.residue_characters_tendsto_zero
    hC hk r u hu (fun X ↦ Nat.primeCounting X) windowNX
    CorePrimeDensity.tendsto_windowNX_atTop σ hσ hA hbound hz

end

end PrimeGapNormality.Prime.CorePrimeResiduePassage
