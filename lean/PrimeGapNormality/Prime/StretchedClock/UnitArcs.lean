import PrimeGapNormality.Prime.StretchedClock.UnitPermutation
import Mathlib.Analysis.Real.Sqrt

/-! Coprime residues in a half-open arc represented inside `[0,1]`.
These intervals include the full period and form the partitions needed by
positive circle tests. No continuity of fractional part at the seam is used. -/

namespace PrimeGapNormality.Prime.StretchedClock

open Finset
open scoped Classical
noncomputable section

def unitArcResidues (a v : ℕ) (s t : ℝ) : Finset ℕ :=
  (unitResidues a).filter fun b =>
    s ≤ (((v * b) % a : ℕ) : ℝ) / a ∧ (((v * b) % a : ℕ) : ℝ) / a < t

theorem unitArcResidues_card_eq {a v : ℕ} (ha : 0 < a) (hv : v.Coprime a)
    (s t : ℝ) :
    (unitArcResidues a v s t).card =
      ((unitResidues a).filter fun b : ℕ => s ≤ (b : ℝ) / a ∧ (b : ℝ) / a < t).card := by
  simpa only [unitArcResidues, Set.mem_setOf_eq] using
    unitResidues_filter_mul_mod_card ha hv {b : ℕ | s ≤ (b : ℝ) / a ∧ (b : ℝ) / a < t}

private theorem unit_arc_filter_eq_interval {a : ℕ} (ha : 0 < a)
    {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 1) :
    (unitResidues a).filter (fun b : ℕ => s ≤ (b : ℝ) / a ∧ (b : ℝ) / a < t) =
      (Ico ⌈(a : ℝ) * s⌉₊ ⌈(a : ℝ) * t⌉₊).filter fun b => a.Coprime b := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hhi : ⌈(a : ℝ) * t⌉₊ ≤ a := by
    apply Nat.ceil_le.mpr
    simpa using mul_le_mul_of_nonneg_left ht haR.le
  ext b
  simp only [mem_filter, mem_unitResidues, mem_Ico]
  have hlo : ⌈(a : ℝ) * s⌉₊ ≤ b ↔ s ≤ (b : ℝ) / a := by
    rw [Nat.ceil_le, le_div_iff₀ haR]
    simp only [mul_comm]
  have hupper : b < ⌈(a : ℝ) * t⌉₊ ↔ (b : ℝ) / a < t := by
    rw [Nat.lt_ceil, div_lt_iff₀ haR]
    simp only [mul_comm]
  constructor
  · rintro ⟨⟨hb, hcop⟩, hs, ht'⟩
    exact ⟨⟨hlo.mpr hs, hupper.mpr ht'⟩, hcop⟩
  · rintro ⟨⟨hs, ht'⟩, hcop⟩
    exact ⟨⟨ht'.trans_le hhi, hcop⟩, hlo.mp hs, hupper.mp ht'⟩

/-- The elementary Möbius arc bound before converting its error to `a^(-1/2)`. -/
theorem unitArcResidues_card_le {a v : ℕ} (ha : 0 < a) (hv : v.Coprime a)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ((unitArcResidues a v s t).card : ℝ) ≤
      (a.totient : ℝ) * (t - s) + 1 + (2 : ℝ) ^ a.primeFactors.card := by
  let lo : ℕ := ⌈(a : ℝ) * s⌉₊
  let hi : ℕ := ⌈(a : ℝ) * t⌉₊
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hlohi : lo ≤ hi := Nat.ceil_mono (mul_le_mul_of_nonneg_left hst haR.le)
  have hcount : (unitArcResidues a v s t).card = unitCount a lo (hi - lo) := by
    rw [unitArcResidues_card_eq ha hv, unit_arc_filter_eq_interval ha hst ht]
    simp only [unitCount, Nat.add_sub_of_le hlohi, lo, hi]
  have hlen : ((hi - lo : ℕ) : ℝ) ≤ (a : ℝ) * (t - s) + 1 := by
    rw [Nat.cast_sub hlohi]
    have hloR := Nat.le_ceil ((a : ℝ) * s)
    have hhiR := Nat.ceil_lt_add_one (mul_nonneg haR.le (hs.trans hst))
    change ((hi : ℕ) : ℝ) < (a : ℝ) * t + 1 at hhiR
    change (a : ℝ) * s ≤ (lo : ℝ) at hloR
    nlinarith
  have hphi0 : (0 : ℝ) ≤ a.totient := Nat.cast_nonneg _
  have hphi : (a.totient : ℝ) / a ≤ 1 :=
    (div_le_one haR).mpr (Nat.cast_le.mpr (Nat.totient_le a))
  have hbound := (abs_le.mp (abs_unitCount_sub_density_le ha lo (hi - lo))).2
  rw [hcount]
  have hmajor := mul_le_mul_of_nonneg_right hlen (div_nonneg hphi0 haR.le)
  have heq : ((a : ℝ) * (t - s) + 1) * ((a.totient : ℝ) / a) =
      (a.totient : ℝ) * (t - s) + (a.totient : ℝ) / a := by
    field_simp [haR.ne'] <;> ring
  rw [heq] at hmajor
  have hleft : ((hi - lo : ℕ) : ℝ) * ((a.totient : ℝ) / a) =
      ((hi - lo : ℕ) : ℝ) * (a.totient : ℝ) / a := by ring
  rw [hleft] at hmajor
  linarith

/-- Explicit relative coprime-count error. -/
theorem two_pow_primeFactors_div_totient_le {a : ℕ} (ha : 0 < a) :
    (2 : ℝ) ^ a.primeFactors.card / a.totient ≤ 8 / Real.sqrt a := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hphi : (0 : ℝ) < a.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr ha)
  have hsqrt : 0 < Real.sqrt (a : ℝ) := Real.sqrt_pos.mpr haR
  have hc : (4 : ℝ) ^ a.primeFactors.card * (a : ℝ) ≤
      64 * (a.totient : ℝ) ^ 2 := by
    exact_mod_cast four_pow_card_primeFactors_mul_le_totient_sq ha
  have hpow : ((2 : ℝ) ^ a.primeFactors.card) ^ 2 =
      (4 : ℝ) ^ a.primeFactors.card := by
    rw [pow_two, ← mul_pow]
    norm_num
  have he : ((2 : ℝ) ^ a.primeFactors.card * Real.sqrt (a : ℝ)) ^ 2 ≤
      (8 * (a.totient : ℝ)) ^ 2 := by
    rw [mul_pow, hpow, Real.sq_sqrt haR.le]
    nlinarith
  have hnonneg : 0 ≤ (2 : ℝ) ^ a.primeFactors.card * Real.sqrt (a : ℝ) :=
    mul_nonneg (pow_nonneg (by norm_num) _) hsqrt.le
  have hroot : (2 : ℝ) ^ a.primeFactors.card * Real.sqrt (a : ℝ) ≤
      8 * (a.totient : ℝ) := by nlinarith
  exact (div_le_div_iff₀ hphi hsqrt).mpr hroot

/-- Uniform arc majorant, independent of the unit multiplier. -/
theorem unitArcResidues_card_le_sqrt {a v : ℕ} (ha : 0 < a) (hv : v.Coprime a)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ((unitArcResidues a v s t).card : ℝ) ≤
      (a.totient : ℝ) * (t - s + 16 / Real.sqrt a) := by
  have hphi : (0 : ℝ) < a.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr ha)
  have hpower : (1 : ℝ) ≤ (2 : ℝ) ^ a.primeFactors.card :=
    one_le_pow₀ (by norm_num)
  have herr := (div_le_iff₀ hphi).mp (two_pow_primeFactors_div_totient_le ha)
  have hcount := unitArcResidues_card_le ha hv hs hst ht
  simp only [div_eq_mul_inv] at herr hcount ⊢
  nlinarith

/-- The natural-residue phase is exactly the usual fractional-part phase. -/
theorem fract_mul_div_eq (a v b : ℕ) :
    Int.fract ((v : ℝ) * (b : ℝ) / a) = (((v * b) % a : ℕ) : ℝ) / a := by
  rw [← Nat.cast_mul, Int.fract_div_natCast_eq_div_natCast_mod]

end
end PrimeGapNormality.Prime.StretchedClock
