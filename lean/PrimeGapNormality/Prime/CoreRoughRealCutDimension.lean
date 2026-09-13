import PrimeGapNormality.Prime.CoreRoughDimensionProduct
import PrimeGapNormality.Prime.CoreBetaBuchstab
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Real strict-cut dimension input for the finite beta remainder

The integer cut is max(2,ceil(u)-1). Since all pool primes exceed 4k,
this represents the complementary band p ≥ u exactly, with no endpoint
factor loss. Its logarithm loses at most a factor two. The real upper
endpoint may be any Z ≥ y; the final interface uses Z ≤ y+1.
Choosing y < Z ≤ y+1 includes every pool prime strictly.
-/

namespace PrimeGapNormality.Prime.CoreRoughRealCutDimension

open Finset CoreRoughDimensionProduct
open scoped Classical
noncomputable section

set_option maxHeartbeats 800000

def integerCut (u : ℝ) : ℕ := max 2 (⌈u⌉₊ - 1)

theorem integerCut_ge_two (u : ℝ) : 2 ≤ integerCut u := le_max_left _ _

theorem integerCut_le {u : ℝ} {y : ℕ} (hy : 2 ≤ y) (hu : u ≤ (y : ℝ) + 1) :
    integerCut u ≤ y := by
  have hh : ⌈u⌉₊ ≤ y + 1 := Nat.ceil_le.mpr (by simpa only [Nat.cast_add, Nat.cast_one] using hu)
  exact max_le hy (by omega)

theorem real_le_integerCut_add_one {u : ℝ} (hu : 2 ≤ u) :
    u ≤ (integerCut u : ℝ) + 1 := by
  have hc : 1 ≤ ⌈u⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnat : ⌈u⌉₊ ≤ integerCut u + 1 := by
    have := le_max_right 2 (⌈u⌉₊ - 1)
    dsimp [integerCut]
    omega
  exact (Nat.le_ceil u).trans (by exact_mod_cast hnat)

theorem integerCut_lt_iff {u : ℝ} (hu : 2 ≤ u) {p : ℕ} (hp : 2 < p) :
    integerCut u < p ↔ u ≤ (p : ℝ) := by
  have hc : 1 ≤ ⌈u⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  rw [integerCut, max_lt_iff]
  constructor
  · intro h
    exact Nat.ceil_le.mp (by omega : ⌈u⌉₊ ≤ p)
  · intro h
    have hh : ⌈u⌉₊ ≤ p := Nat.ceil_le.mpr h
    exact ⟨hp, by omega⟩

theorem log_integerCut_ge_half {u : ℝ} (hu : 2 ≤ u) :
    Real.log u ≤ 2 * Real.log (integerCut u : ℝ) := by
  have hw : (2 : ℝ) ≤ integerCut u := by exact_mod_cast integerCut_ge_two u
  have hu0 : 0 < u := by linarith
  have huw := real_le_integerCut_add_one hu
  have hs : u ≤ (integerCut u : ℝ) ^ 2 := by nlinarith
  simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hu0 hs

theorem mem_dimensionPrimeBand_iff {a y k p : ℕ} :
    p ∈ dimensionPrimeBand a y k ↔ Nat.Prime p ∧ max a (4 * k) < p ∧ p ≤ y := by
  simp only [dimensionPrimeBand, mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpy, hp⟩, hn⟩
    exact ⟨hp, by by_contra h; exact hn ⟨Nat.not_lt.mp h, hp⟩, hpy⟩
  · rintro ⟨hp, hpa, hpy⟩
    exact ⟨⟨hpy, hp⟩, fun h => Nat.not_le.mpr hpa h.1⟩

/-- Complementary prime bands agree exactly, even at integral u. -/
theorem real_band_eq {a y k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 2 ≤ u) :
    (dimensionPrimeBand a y k).filter (fun p : ℕ => u ≤ (p : ℝ)) =
      dimensionPrimeBand (max a (integerCut u)) y k := by
  ext p
  simp only [mem_filter, mem_dimensionPrimeBand_iff]
  constructor
  · rintro ⟨⟨hp, hmax, hpy⟩, hup⟩
    have hkp : 4 * k < p := (le_max_right _ _).trans_lt hmax
    have hwp := (integerCut_lt_iff hu (by omega : 2 < p)).mpr hup
    exact ⟨hp, max_lt (max_lt ((le_max_left _ _).trans_lt hmax) hwp) hkp, hpy⟩
  · rintro ⟨hp, hmax, hpy⟩
    have hak : max a (integerCut u) < p := (le_max_left _ _).trans_lt hmax
    have hkp : 4 * k < p := (le_max_right _ _).trans_lt hmax
    refine ⟨⟨hp, max_lt ((le_max_left _ _).trans_lt hak) hkp, hpy⟩, ?_⟩
    exact (integerCut_lt_iff hu (by omega : 2 < p)).mp
      ((le_max_right _ _).trans_lt hak)

theorem real_band_inverse_le {a y k : ℕ} (ha : a ≤ y) (hy : 16 ≤ y)
    (hk : 1 ≤ k) (ν : ℕ → ℕ)
    (hν : ∀ p ∈ dimensionPrimeBand a y k, ν p ≤ k)
    {Z : ℝ} (hZ : (y : ℝ) ≤ Z)
    {u : ℝ} (hu : 2 ≤ u) (huy : u ≤ (y : ℝ) + 1) :
    (∏ p ∈ (dimensionPrimeBand a y k).filter (fun p : ℕ => u ≤ (p : ℝ)),
      (1 - (ν p : ℝ) / (p : ℝ)))⁻¹ ≤
        Real.exp (32 * (k : ℝ)) *
          (Real.log Z / Real.log u) ^ k := by
  let w := integerCut u
  have hw : 2 ≤ w := integerCut_ge_two u
  have hwy : w ≤ y := integerCut_le (by omega) huy
  have hsub : dimensionPrimeBand (max a w) y k ⊆ dimensionPrimeBand a y k := by
    rw [← real_band_eq hk hu]
    exact filter_subset _ _
  have hbase := dimensionProduct_inv_le ν
    (hw.trans (le_max_right _ _)) (max_le ha hwy) hy hk
    (fun p hp => hν p (hsub hp))
  have hwR : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hyR : (16 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogw : 0 < Real.log (w : ℝ) := Real.log_pos (by linarith)
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hlogmax : Real.log (w : ℝ) ≤ Real.log ((max a w : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (Nat.cast_le.mpr (le_max_right _ _))
  have hlogyu : Real.log (y : ℝ) ≤ Real.log Z :=
    Real.log_le_log (by linarith) hZ
  have hratio : Real.log (y : ℝ) / Real.log ((max a w : ℕ) : ℝ) ≤
      2 * (Real.log Z / Real.log u) := by
    calc
      _ ≤ Real.log (y : ℝ) / Real.log (w : ℝ) :=
        div_le_div_of_nonneg_left hlogy.le hlogw hlogmax
      _ ≤ Real.log Z / Real.log (w : ℝ) :=
        div_le_div_of_nonneg_right hlogyu hlogw.le
      _ ≤ _ := by
        rw [← mul_div_assoc, div_le_div_iff₀ hlogw hlogu]
        have hh := mul_le_mul_of_nonneg_left (log_integerCut_ge_half hu) hlogZ.le
        dsimp only [w] at *
        nlinarith
  have hpow := pow_le_pow_left₀
    (div_nonneg hlogy.le (hlogw.le.trans hlogmax)) hratio k
  have htwo : (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he k
    simpa only [← Real.exp_nat_mul, mul_one] using hh
  rw [real_band_eq hk hu]
  change (dimensionProduct (max a w) y k ν)⁻¹ ≤ _
  calc
    _ ≤ Real.exp (31 * (k : ℝ)) *
        (2 * (Real.log Z / Real.log u)) ^ k :=
      hbase.trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
    _ = (Real.exp (31 * (k : ℝ)) * 2 ^ k) *
        (Real.log Z / Real.log u) ^ k := by rw [mul_pow]; ring
    _ ≤ (Real.exp (31 * (k : ℝ)) * Real.exp (k : ℝ)) *
        (Real.log Z / Real.log u) ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le)
        (pow_nonneg (div_nonneg hlogZ.le hlogu.le) k)
    _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring

theorem local_rank_ratio_lt_one {a y k p : ℕ} (hk : 1 ≤ k)
    (ν : ℕ → ℕ) (hp : p ∈ dimensionPrimeBand a y k) (hν : ν p ≤ k) :
    (ν p : ℝ) / (p : ℝ) < 1 := by
  obtain ⟨hpprime, hpmax, hpy⟩ := mem_dimensionPrimeBand_iff.mp hp
  have hpk : 4 * k < p := (le_max_right _ _).trans_lt hpmax
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpprime.pos
  rw [div_lt_one hp0]
  exact_mod_cast (by omega : ν p < p)

theorem euler_cut_ratio_eq_inverse_band {a y k : ℕ} (hk : 1 ≤ k)
    (ν : ℕ → ℕ) (hν : ∀ p ∈ dimensionPrimeBand a y k, ν p ≤ k) (u : ℝ) :
    (∏ p ∈ (dimensionPrimeBand a y k).filter (fun p : ℕ => (p : ℝ) < u),
      (1 - (ν p : ℝ) / (p : ℝ))) /
        (∏ p ∈ dimensionPrimeBand a y k, (1 - (ν p : ℝ) / (p : ℝ))) =
      (∏ p ∈ (dimensionPrimeBand a y k).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - (ν p : ℝ) / (p : ℝ)))⁻¹ := by
  have hpos (s : Finset ℕ) (hs : s ⊆ dimensionPrimeBand a y k) :
      0 < ∏ p ∈ s, (1 - (ν p : ℝ) / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    exact sub_pos.mpr (local_rank_ratio_lt_one hk ν (hs hp) (hν p (hs hp)))
  have hl := hpos _ (filter_subset (fun p : ℕ => (p : ℝ) < u) _)
  have hr := hpos _ (filter_subset (fun p : ℕ => u ≤ (p : ℝ)) _)
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (dimensionPrimeBand a y k) (fun p : ℕ => (p : ℝ) < u)
    (fun p : ℕ => 1 - (ν p : ℝ) / (p : ℝ))
  simp only [not_lt] at hsplit
  rw [← hsplit]
  field_simp [hl.ne', hr.ne']

/-- The actual real-cut Euler dimension condition, with the strict
prefix p<u used by the Buchstab suffix identity. -/
theorem real_euler_dimension {a y k : ℕ} (ha : a ≤ y) (hy : 16 ≤ y)
    (hk : 1 ≤ k) (ν : ℕ → ℕ)
    (hν : ∀ p ∈ dimensionPrimeBand a y k, ν p ≤ k)
    {Z : ℝ} (hZlo : (y : ℝ) ≤ Z) (hZhi : Z ≤ (y : ℝ) + 1)
    {u : ℝ} (hu : 2 ≤ u) (huZ : u ≤ Z) :
    (∏ p ∈ (dimensionPrimeBand a y k).filter (fun p : ℕ => (p : ℝ) < u),
      (1 - (ν p : ℝ) / (p : ℝ))) /
        (∏ p ∈ dimensionPrimeBand a y k, (1 - (ν p : ℝ) / (p : ℝ))) ≤
      Real.exp (32 * (k : ℝ)) * (Real.log Z / Real.log u) ^ k := by
  rw [euler_cut_ratio_eq_inverse_band hk ν hν u]
  exact real_band_inverse_le ha hy hk ν hν hZlo hu (huZ.trans hZhi)

/-- The same dimension condition in the literal list-Euler notation of
`CoreBetaRemainderBound`; no new dimension hypothesis is required. -/
theorem list_euler_dimension {a y k : ℕ} (ha : a ≤ y) (hy : 16 ≤ y)
    (hk : 1 ≤ k) (ν : ℕ → ℕ)
    (hν : ∀ p ∈ dimensionPrimeBand a y k, ν p ≤ k)
    (ps : List ℕ) (hn : ps.Nodup) (hps : ps.toFinset = dimensionPrimeBand a y k)
    {Z : ℝ} (hZlo : (y : ℝ) ≤ Z) (hZhi : Z ≤ (y : ℝ) + 1) :
    ∀ u : ℝ, 2 ≤ u → u ≤ Z →
      CoreBetaBuchstab.euler (fun p : ℕ => (ν p : ℝ) / (p : ℝ))
          (ps.filter (fun p : ℕ => decide ((p : ℝ) < u))) /
        CoreBetaBuchstab.euler (fun p : ℕ => (ν p : ℝ) / (p : ℝ)) ps ≤
          Real.exp (32 * (k : ℝ)) * (Real.log Z / Real.log u) ^ k := by
  intro u hu huZ
  have hfull := List.prod_toFinset (fun p : ℕ => 1 - (ν p : ℝ) / (p : ℝ)) hn
  have hcut := List.prod_toFinset (fun p : ℕ => 1 - (ν p : ℝ) / (p : ℝ))
    (hn.filter (fun p : ℕ => decide ((p : ℝ) < u)))
  simp only [List.toFinset_filter, hps, decide_eq_true_eq] at hfull hcut
  unfold CoreBetaBuchstab.euler
  rw [← hfull, ← hcut]
  exact real_euler_dimension ha hy hk ν hν hZlo hZhi hu huZ

end
end PrimeGapNormality.Prime.CoreRoughRealCutDimension
