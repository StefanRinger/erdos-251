import PrimeGapNormality.Prime.CoreSequenceRangeAgreement
import PrimeGapNormality.Prime.CoreSequenceSTMeanTail

/-!
# Future-gap tails under eventual range agreement

Once two strictly increasing sequences have the same range above a physical
threshold, equal values have equal successors and hence identical entire
futures.  Their geometric gap tails therefore agree term by term at aligned
physical roots.  Reindexing the common physical window transfers the bare
mean-tail condition exactly, with no summability or distribution premise.
-/

namespace PrimeGapNormality.Prime.CoreSequenceTailAgreement

open Filter Set Finset
open scoped Topology Classical

open CoreSequenceRangeAgreement CoreSequenceSTMeanTail

noncomputable section

/-- An index of a value in a sequence range, with an arbitrary default off
the range. -/
def rangeIndex (a : ℕ → ℕ) (v : ℕ) : ℕ :=
  if h : ∃ n, a n = v then Nat.find h else 0

theorem apply_rangeIndex {a : ℕ → ℕ} {v : ℕ} (hv : v ∈ Set.range a) :
    a (rangeIndex a v) = v := by
  change ∃ n, a n = v at hv
  unfold rangeIndex
  rw [dif_pos hv]
  exact Nat.find_spec hv

theorem rangeIndex_eq_of_apply_eq
    {a : ℕ → ℕ} (ha : Function.Injective a) {v n : ℕ}
    (hn : a n = v) : rangeIndex a v = n := by
  apply ha
  rw [apply_rangeIndex (show v ∈ Set.range a from ⟨n, hn⟩), hn]

/-- Equal sufficiently large values in eventually equal ranges have equal
future values at every relative index. -/
theorem future_values_eq_of_range_tail
    {a b : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    {N i j : ℕ}
    (htail : ∀ v, N ≤ v → (v ∈ Set.range a ↔ v ∈ Set.range b))
    (hN : N ≤ a i) (hij : a i = b j) :
    ∀ k : ℕ, a (i + k) = b (j + k) := by
  intro k
  induction k with
  | zero => simpa using hij
  | succ k ih =>
      have haStep : a (i + k) < a (i + (k + 1)) := ha (by omega)
      have hbStep : b (j + k) < b (j + (k + 1)) := hb (by omega)
      have hNa : N ≤ a (i + (k + 1)) :=
        hN.trans (ha.monotone (by omega))
      have hNb : N ≤ b (j + (k + 1)) := by
        calc
          N ≤ a i := hN
          _ = b j := hij
          _ ≤ b (j + (k + 1)) := hb.monotone (by omega)
      have haInB : a (i + (k + 1)) ∈ Set.range b :=
        (htail _ hNa).mp ⟨i + (k + 1), rfl⟩
      obtain ⟨m, hm⟩ := haInB
      have hjm : j + k < m := hb.lt_iff_lt.mp (by
        calc
          b (j + k) = a (i + k) := ih.symm
          _ < a (i + (k + 1)) := haStep
          _ = b m := hm.symm)
      have hba : b (j + (k + 1)) ≤ a (i + (k + 1)) := by
        calc
          b (j + (k + 1)) ≤ b m := hb.monotone (by omega)
          _ = a (i + (k + 1)) := hm
      have hbInA : b (j + (k + 1)) ∈ Set.range a :=
        (htail _ hNb).mpr ⟨j + (k + 1), rfl⟩
      obtain ⟨n, hn⟩ := hbInA
      have hin : i + k < n := ha.lt_iff_lt.mp (by
        calc
          a (i + k) = b (j + k) := ih
          _ < b (j + (k + 1)) := hbStep
          _ = a n := hn.symm)
      have hab : a (i + (k + 1)) ≤ b (j + (k + 1)) := by
        calc
          a (i + (k + 1)) ≤ a n := ha.monotone (by omega)
          _ = b (j + (k + 1)) := hn
      exact le_antisymm hab hba

theorem future_seqGap_eq_of_range_tail
    {a b : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    {N i j : ℕ}
    (htail : ∀ v, N ≤ v → (v ∈ Set.range a ↔ v ∈ Set.range b))
    (hN : N ≤ a i) (hij : a i = b j) (k : ℕ) :
    seqGap a (i + k) = seqGap b (j + k) := by
  have hfuture := future_values_eq_of_range_tail ha hb htail hN hij
  unfold seqGap
  rw [show i + k + 1 = i + (k + 1) by omega,
    show j + k + 1 = j + (k + 1) by omega,
    hfuture k, hfuture (k + 1)]

/-- Gap tails agree term by term; no summability hypothesis is needed for
the congruence of the two `tsum`s. -/
theorem future_seqGapTail_eq_of_range_tail
    {a b : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    {N i j : ℕ}
    (htail : ∀ v, N ≤ v → (v ∈ Set.range a ↔ v ∈ Set.range b))
    (hN : N ≤ a i) (hij : a i = b j) (rho : ℝ) (L : ℕ) :
    seqGapTail rho a (i + L) = seqGapTail rho b (j + L) := by
  unfold seqGapTail
  apply tsum_congr
  intro h
  simp only [Nat.add_assoc,
    future_seqGap_eq_of_range_tail ha hb htail hN hij (L + h)]

private theorem mem_seqWindow_iff
    {a : ℕ → ℕ} (ha : StrictMono a) {X n : ℕ} :
    n ∈ seqWindow a X ↔ X < a n ∧ a n ≤ 2 * X := by
  simp only [seqWindow, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨le_trans (strictMono_le_id ha n) h.2, h⟩

/-- Exact reindexing of future gap tails over a sufficiently late common
physical window. -/
theorem sum_seqGapTail_seqWindow_eq_of_range_tail
    {a b : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    {N X : ℕ}
    (htail : ∀ v, N ≤ v → (v ∈ Set.range a ↔ v ∈ Set.range b))
    (hX : N ≤ X) (rho : ℝ) (L : ℕ) :
    (∑ i ∈ seqWindow a X, seqGapTail rho a (i + L)) =
      ∑ j ∈ seqWindow b X, seqGapTail rho b (j + L) := by
  apply Finset.sum_bij (fun i _ ↦ rangeIndex b (a i))
  · intro i hi
    have hiWindow := (mem_seqWindow_iff ha).mp hi
    have hNi : N ≤ a i := hX.trans hiWindow.1.le
    have hiRangeB : a i ∈ Set.range b :=
      (htail _ hNi).mp ⟨i, rfl⟩
    apply (mem_seqWindow_iff hb).mpr
    simpa only [apply_rangeIndex hiRangeB] using hiWindow
  · intro i hi i' hi' heq
    apply ha.injective
    have hiWindow := (mem_seqWindow_iff ha).mp hi
    have hiWindow' := (mem_seqWindow_iff ha).mp hi'
    have hRange : a i ∈ Set.range b :=
      (htail _ (hX.trans hiWindow.1.le)).mp ⟨i, rfl⟩
    have hRange' : a i' ∈ Set.range b :=
      (htail _ (hX.trans hiWindow'.1.le)).mp ⟨i', rfl⟩
    have hval := congrArg b heq
    simpa only [apply_rangeIndex hRange, apply_rangeIndex hRange'] using hval
  · intro j hj
    have hjWindow := (mem_seqWindow_iff hb).mp hj
    have hNj : N ≤ b j := hX.trans hjWindow.1.le
    have hjRangeA : b j ∈ Set.range a :=
      (htail _ hNj).mpr ⟨j, rfl⟩
    let i := rangeIndex a (b j)
    have hiVal : a i = b j := by
      dsimp only [i]
      exact apply_rangeIndex hjRangeA
    have hi : i ∈ seqWindow a X :=
      (mem_seqWindow_iff ha).mpr (by simpa only [hiVal] using hjWindow)
    refine ⟨i, hi, ?_⟩
    apply hb.injective
    have hiRangeB : a i ∈ Set.range b := ⟨j, hiVal.symm⟩
    rw [apply_rangeIndex hiRangeB, hiVal]
  · intro i hi
    have hiWindow := (mem_seqWindow_iff ha).mp hi
    have hNi : N ≤ a i := hX.trans hiWindow.1.le
    have hiRangeB : a i ∈ Set.range b :=
      (htail _ hNi).mp ⟨i, rfl⟩
    exact future_seqGapTail_eq_of_range_tail ha hb htail hNi
      (apply_rangeIndex hiRangeB).symm rho L

/-- Equality of the actual mean future-gap tails, uniformly in the shift
depth `L`. -/
theorem eventually_windowAvgReal_seqGapTail_eq_of_range_agreement
    {a b : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ v ∈ Set.range b)) (rho : ℝ) :
    ∀ᶠ X : ℕ in atTop, ∀ L : ℕ,
      windowAvgReal (seqWindow a X) (fun i ↦ seqGapTail rho a (i + L)) =
        windowAvgReal (seqWindow b X) (fun j ↦ seqGapTail rho b (j + L)) := by
  rcases eventually_atTop.1 hrange with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N,
    eventually_seqWindow_card_eq_of_range_agreement ha hb hrange]
      with X hX hcardX
  intro L
  unfold windowAvgReal
  rw [sum_seqGapTail_seqWindow_eq_of_range_tail ha hb hN hX,
    hcardX]

/-- The bare mean-gap-tail input is invariant under a finite change of the
enumerated range. -/
theorem meanGapTailT_iff_of_range_agreement
    {a b : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    (hrange : ∀ᶠ v : ℕ in atTop,
      (v ∈ Set.range a ↔ v ∈ Set.range b))
    (rho : ℝ) (G : ℕ → ℝ) :
    MeanGapTailT a rho G ↔ MeanGapTailT b rho G := by
  have hcard := eventually_seqWindow_card_eq_of_range_agreement ha hb hrange
  have htail := eventually_windowAvgReal_seqGapTail_eq_of_range_agreement
    ha hb hrange rho
  constructor
  · rintro ⟨C, hC, hmean⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [hmean, hcard, htail] with X hX hcardX htailX
    constructor
    · rw [← hcardX]
      exact hX.1
    · rw [← htailX (stdProfileL rho (G X))]
      exact hX.2
  · rintro ⟨C, hC, hmean⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [hmean, hcard, htail] with X hX hcardX htailX
    constructor
    · rw [hcardX]
      exact hX.1
    · rw [htailX (stdProfileL rho (G X))]
      exact hX.2

end

end PrimeGapNormality.Prime.CoreSequenceTailAgreement
