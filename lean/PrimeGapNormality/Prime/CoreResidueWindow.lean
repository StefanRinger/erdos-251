import PrimeGapNormality.Prime.CoreDigitalEmpirical
import PrimeGapNormality.Prime.CoreResidueCounting

/-!
# Restricting a finite window to one index residue class

This is a purely finite arithmetic adapter.  It compares a nonnegative
full-window average with the conditional average on the actual indices
`a+i ≡ r (mod k)`.  It assumes no equidistribution of index classes.
-/

open MeasureTheory Filter Finset
open scoped Classical Topology NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

/-- Offsets in `[0,N)` whose actual index `a+i` lies in the residue class
of `r` modulo `k`. -/
def coreResidueWindowOffsets (k r a N : ℕ) : Finset ℕ :=
  (range N).filter fun i => (a + i) % k = r % k

def coreResidueWindowCount (k r a N : ℕ) : ℕ :=
  (coreResidueWindowOffsets k r a N).card

theorem mem_coreResidueWindowOffsets {k r a N i : ℕ} :
    i ∈ coreResidueWindowOffsets k r a N ↔
      i < N ∧ (a + i) % k = r % k := by
  simp [coreResidueWindowOffsets]

/-- Literal arithmetic-progression description of the restricted indices. -/
theorem mem_coreResidueWindowOffsets_iff_progression
    {k r a N i : ℕ} (hk : 1 ≤ k) :
    i ∈ coreResidueWindowOffsets k r a N ↔
      i < N ∧ ∃ q : ℕ, a + i = k * q + r % k := by
  rw [mem_coreResidueWindowOffsets]
  constructor
  · rintro ⟨hi, hmod⟩
    refine ⟨hi, (a + i) / k, ?_⟩
    have hdec : a + i = k * ((a + i) / k) + (a + i) % k :=
      (Nat.div_add_mod (a + i) k).symm
    rwa [hmod] at hdec
  · rintro ⟨hi, q, hq⟩
    refine ⟨hi, ?_⟩
    rw [hq]
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.ne_of_gt hk]

/-- The offset definition and the absolute interval definition have the
same number of points. -/
theorem coreResidueWindowCount_eq_card_Ico (k r a N : ℕ) :
    coreResidueWindowCount k r a N =
      #{n ∈ Ico a (a + N) | n % k = r % k} := by
  let e : ℕ ↪ ℕ := ⟨fun i => a + i, add_right_injective a⟩
  have himage :
      (coreResidueWindowOffsets k r a N).map e =
        (Ico a (a + N)).filter (fun n => n % k = r % k) := by
    ext n
    simp only [Finset.mem_map, mem_coreResidueWindowOffsets, Finset.mem_filter,
      Finset.mem_Ico, e, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, ⟨hi, hmod⟩, rfl⟩
      exact ⟨⟨Nat.le_add_right a i, Nat.add_lt_add_left hi a⟩, hmod⟩
    · rintro ⟨⟨han, hn⟩, hmod⟩
      refine ⟨n - a, ⟨?_, ?_⟩, ?_⟩
      · omega
      · rwa [Nat.add_sub_cancel' han]
      · exact Nat.add_sub_cancel' han
  unfold coreResidueWindowCount
  rw [← card_map e, himage]

/-- Exact interval rounding, in fact with error at most one. -/
theorem coreResidueWindowCount_abs_sub_div_le_one
    (k r a N : ℕ) (hk : 1 ≤ k) :
    |(coreResidueWindowCount k r a N : ℝ) - (N : ℝ) / k| ≤ 1 := by
  rw [coreResidueWindowCount_eq_card_Ico]
  exact core_abs_card_Ico_mod_sub_div a N k r (Nat.zero_lt_of_lt hk)

/-- The requested two-endpoint-error form. -/
theorem coreResidueWindowCount_abs_sub_div_le_two
    (k r a N : ℕ) (hk : 1 ≤ k) :
    |(coreResidueWindowCount k r a N : ℝ) - (N : ℝ) / k| ≤ 2 :=
  (coreResidueWindowCount_abs_sub_div_le_one k r a N hk).trans (by norm_num)

/-- A nonnegative residue-class subsum is at most the full window sum. -/
theorem coreResidueWindow_sum_le_full
    {k r a N : ℕ} {g : ℕ → ℝ}
    (hg : ∀ i ∈ range N, 0 ≤ g i) :
    (∑ i ∈ coreResidueWindowOffsets k r a N, g i) ≤
      ∑ i ∈ range N, g i :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun i hi _ => hg i hi)

/-- Conditional average on the actual arithmetic-progression indices. -/
noncomputable def coreResidueWindowAverage
    (k r : ℕ) (u : ℕ → AddCircle (1 : ℝ))
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (a N : ℕ) : ℝ :=
  (∑ i ∈ coreResidueWindowOffsets k r a N, f (u (a + i))) /
    (coreResidueWindowCount k r a N : ℝ)

/-- Finite conditional-average comparison with the rational slope `N/M`
kept explicit. -/
theorem coreResidueWindowAverage_le_countRatio_mul_full
    {k r : ℕ} (u : ℕ → AddCircle (1 : ℝ))
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) {a N : ℕ}
    (hN : 0 < N) (hM : 0 < coreResidueWindowCount k r a N)
    (hf : ∀ i ∈ range N, 0 ≤ f (u (a + i))) :
    coreResidueWindowAverage k r u f a N ≤
      ((N : ℝ) / coreResidueWindowCount k r a N) *
        coreDigitalWindowAverage u f a N := by
  have hsum := coreResidueWindow_sum_le_full (k := k) (r := r) (a := a) hf
  unfold coreResidueWindowAverage coreDigitalWindowAverage
  calc
    (∑ i ∈ coreResidueWindowOffsets k r a N, f (u (a + i))) /
        (coreResidueWindowCount k r a N : ℝ) ≤
      (∑ i ∈ range N, f (u (a + i))) /
        (coreResidueWindowCount k r a N : ℝ) :=
      div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
    _ = ((N : ℝ) / coreResidueWindowCount k r a N) *
        ((∑ i ∈ range N, f (u (a + i))) / (N : ℝ)) := by
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN),
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)]

/-- Once the window has length at least `2k`, the residue class is nonempty
and its conditioning slope is at most `2k`. -/
theorem coreResidueWindowCount_pos_and_ratio_le_two_mul
    {k r a N : ℕ} (hk : 1 ≤ k) (hN : 2 * k ≤ N) :
    0 < coreResidueWindowCount k r a N ∧
      (N : ℝ) / coreResidueWindowCount k r a N ≤ 2 * (k : ℝ) := by
  let M : ℝ := coreResidueWindowCount k r a N
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hk)
  have hcast : 2 * (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNk : (2 : ℝ) ≤ (N : ℝ) / k :=
    (le_div_iff₀ hkpos).mpr (by simpa only [mul_comm] using hcast)
  have habs := coreResidueWindowCount_abs_sub_div_le_one k r a N hk
  have hlow : (N : ℝ) / k - 1 ≤ M := by
    have := (abs_le.mp habs).1
    dsimp only [M]
    linarith
  have hhalf : (N : ℝ) / (2 * (k : ℝ)) ≤ M := by
    have heq : (N : ℝ) / (2 * (k : ℝ)) = ((N : ℝ) / k) / 2 := by
      field_simp [hkpos.ne']
    rw [heq]
    linarith
  have hMone : (1 : ℝ) ≤ M := by
    exact (by linarith [hNk, hlow])
  have hMpos : 0 < M := zero_lt_one.trans_le hMone
  have hMnat : 0 < coreResidueWindowCount k r a N := by
    exact Nat.cast_pos.mp (by simpa only [M] using hMpos)
  refine ⟨hMnat, ?_⟩
  apply (div_le_iff₀ hMpos).mpr
  have hden : (0 : ℝ) < 2 * (k : ℝ) := mul_pos (by norm_num) hkpos
  have hmul := (div_le_iff₀ hden).mp hhalf
  dsimp only [M] at hmul ⊢
  nlinarith

private theorem coreDigitalWindowAverage_nonneg
    (u : ℕ → AddCircle (1 : ℝ))
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x)
    (a N : ℕ) :
    0 ≤ coreDigitalWindowAverage u f a N := by
  unfold coreDigitalWindowAverage
  exact div_nonneg (sum_nonneg fun i _ => hf _) (Nat.cast_nonneg _)

/-- An eventual positive Lipschitz bound on all full windows restricts to
one actual index residue class with the test-independent constant `2k A`.
This is only a domination adapter, not an index-class equidistribution
statement. -/
theorem coreResidueWindow_lipschitz_bound_of_full
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (u : ℕ → AddCircle (1 : ℝ)) (a N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) {A : ℝ} (_hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤
          A * (∫ x, f x ∂volume) + ε) :
    ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreResidueWindowAverage k r u f (a j) (N j) ≤
          (2 * (k : ℝ) * A) * (∫ x, f x ∂volume) + ε := by
  intro f K hK hf ε hε
  have hkpos : (0 : ℝ) < 2 * (k : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hk))
  have hε' : 0 < ε / (2 * (k : ℝ)) := div_pos hε hkpos
  filter_upwards [hN.eventually (eventually_ge_atTop (2 * k)),
    hbound f K hK hf (ε / (2 * (k : ℝ))) hε'] with j hNj hfull
  have hMR := coreResidueWindowCount_pos_and_ratio_le_two_mul
    (r := r) (a := a j) hk hNj
  have hcond := coreResidueWindowAverage_le_countRatio_mul_full
    (k := k) (r := r) u f (by omega : 0 < N j) hMR.1
    (fun i _ => hf _)
  have hfull0 := coreDigitalWindowAverage_nonneg u f hf (a j) (N j)
  have hrestricted :
      coreResidueWindowAverage k r u f (a j) (N j) ≤
        (2 * (k : ℝ)) * coreDigitalWindowAverage u f (a j) (N j) :=
    hcond.trans (mul_le_mul_of_nonneg_right hMR.2 hfull0)
  calc
    coreResidueWindowAverage k r u f (a j) (N j) ≤
        (2 * (k : ℝ)) * coreDigitalWindowAverage u f (a j) (N j) := hrestricted
    _ ≤ (2 * (k : ℝ)) *
        (A * (∫ x, f x ∂volume) + ε / (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hfull hkpos.le
    _ = (2 * (k : ℝ) * A) * (∫ x, f x ∂volume) + ε := by
      field_simp [hkpos.ne']

end PrimeGapNormality.Prime
