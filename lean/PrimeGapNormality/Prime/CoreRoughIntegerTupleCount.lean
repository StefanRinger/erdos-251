import PrimeGapNormality.Prime.CoreRoughTupleCountFullRange
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic

/-!
# The finite rough-tuple bound for integer intervals and integer shifts

A common shift normalizes E into natural numbers. A separate interval
translation differs from its negative by a multiple of the actual prime
modulus. Thus every sieving condition is identical, not approximately
translated. Interval length, shift cardinality and local Euler factors
are preserved. Negative n+h and zero are treated by literal divisibility.
-/
namespace PrimeGapNormality.Prime.CoreRoughIntegerTupleCount
open Finset CoreRoughShiftResidues
open scoped Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def shiftOffset (E : Finset ℤ) : ℤ := ∑ h ∈ E, |h|
def normalizedShift (E : Finset ℤ) (h : ℤ) : ℕ := (h + shiftOffset E).toNat
def normalizedShifts (E : Finset ℤ) : Finset ℕ := E.image (normalizedShift E)

theorem shiftOffset_nonneg (E : Finset ℤ) : 0 ≤ shiftOffset E :=
  Finset.sum_nonneg fun h _hh => abs_nonneg h

theorem normalizedShift_cast (E : Finset ℤ) {h : ℤ} (hh : h ∈ E) :
    (normalizedShift E h : ℤ) = h + shiftOffset E := by
  have habs : |h| ≤ shiftOffset E :=
    Finset.single_le_sum (fun z hz => abs_nonneg z) hh
  have hnon : 0 ≤ h + shiftOffset E := by linarith [neg_le_abs h]
  exact Int.toNat_of_nonneg hnon

theorem normalizedShifts_card (E : Finset ℤ) : (normalizedShifts E).card = E.card := by
  unfold normalizedShifts
  apply Finset.card_image_of_injOn
  intro h hh g hg he
  have he' := congrArg (fun n : ℕ => (n : ℤ)) he
  rw [normalizedShift_cast E hh, normalizedShift_cast E hg] at he'
  omega

def integerResidueCount (E : Finset ℤ) (p : ℕ) : ℕ :=
  (E.image (fun h : ℤ => (h : ZMod p))).card

def integerTupleSieveProduct (E : Finset ℤ) (y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y, (1 - (integerResidueCount E p : ℝ) / (p : ℝ))

theorem residueCount_normalizedShifts (E : Finset ℤ) (p : ℕ) :
    residueCount (normalizedShifts E) p = integerResidueCount E p := by
  have hsets :
      (normalizedShifts E).image (fun h : ℕ => (h : ZMod p)) =
        (E.image (fun h : ℤ => (h : ZMod p))).image
          (fun x : ZMod p => x + (shiftOffset E : ZMod p)) := by
    rw [normalizedShifts, Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro h hh
    have he := congrArg (fun z : ℤ => (z : ZMod p)) (normalizedShift_cast E hh)
    simpa only [Function.comp_apply, Int.cast_natCast, Int.cast_add] using he
  unfold residueCount integerResidueCount
  rw [hsets, Finset.card_image_of_injective _
    (fun x z hxz => add_right_cancel hxz)]

theorem tupleProduct_normalizedShifts (E : Finset ℤ) (y : ℕ) :
    finiteTupleSieveProduct (normalizedShifts E) y = integerTupleSieveProduct E y := by
  unfold finiteTupleSieveProduct integerTupleSieveProduct
  simp only [residueCount_normalizedShifts]

def integerAvoids (E : Finset ℤ) (y : ℕ) (n : ℤ) : Prop :=
  ∀ h ∈ E, ∀ p : ℕ, Nat.Prime p → p ≤ y → ¬ (p : ℤ) ∣ n + h

def integerAvoidedInterval (E : Finset ℤ) (y : ℕ) (a : ℤ) (H : ℕ) : Finset ℤ :=
  (Ico a (a + (H : ℤ))).filter (integerAvoids E y)

/-- Number of full product periods used by the translation. -/
def periodMultiplier (E : Finset ℤ) (a : ℤ) : ℤ := |a| + shiftOffset E + 1
def intervalTranslation (E : Finset ℤ) (y : ℕ) (a : ℤ) : ℤ :=
  periodMultiplier E a * (primorial y : ℤ) - shiftOffset E
def naturalStart (E : Finset ℤ) (y : ℕ) (a : ℤ) : ℕ :=
  (a + intervalTranslation E y a).toNat

theorem translated_start_pos (E : Finset ℤ) (y : ℕ) (a : ℤ) :
    1 ≤ a + intervalTranslation E y a := by
  have hP : (1 : ℤ) ≤ (primorial y : ℤ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (primorial_ne_zero y))
  have hq : 0 ≤ periodMultiplier E a := by
    unfold periodMultiplier
    linarith [abs_nonneg a, shiftOffset_nonneg E]
  have hmul : periodMultiplier E a ≤ periodMultiplier E a * (primorial y : ℤ) :=
    le_mul_of_one_le_right hq hP
  unfold intervalTranslation periodMultiplier at *
  linarith [neg_le_abs a]

theorem naturalStart_cast (E : Finset ℤ) (y : ℕ) (a : ℤ) :
    (naturalStart E y a : ℤ) = a + intervalTranslation E y a :=
  Int.toNat_of_nonneg ((by omega : (0 : ℤ) ≤ 1).trans (translated_start_pos E y a))

theorem translated_divisibility (E : Finset ℤ) (y : ℕ) (a n : ℤ)
    (hn : 0 ≤ n + intervalTranslation E y a) {h : ℤ} (hh : h ∈ E)
    {p : ℕ} (hp : Nat.Prime p) (hpy : p ≤ y) :
    p ∣ (n + intervalTranslation E y a).toNat + normalizedShift E h ↔
      (p : ℤ) ∣ n + h := by
  have hnp : ((n + intervalTranslation E y a).toNat : ℤ) =
      n + intervalTranslation E y a := Int.toNat_of_nonneg hn
  have he : (((n + intervalTranslation E y a).toNat + normalizedShift E h : ℕ) : ℤ) =
      n + h + periodMultiplier E a * (primorial y : ℤ) := by
    rw [Nat.cast_add, hnp, normalizedShift_cast E hh]
    unfold intervalTranslation
    ring
  have hP : (primorial y : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (hp.dvd_primorial_iff.mpr hpy)
  have hmod := congrArg (fun z : ℤ => (z : ZMod p)) he
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, hP, mul_zero, add_zero] at hmod
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hmod,
    Int.cast_add]

theorem translated_avoidance (E : Finset ℤ) (y : ℕ) (a n : ℤ)
    (hn : 0 ≤ n + intervalTranslation E y a) :
    CoreRoughMixedCRT.avoids (forbiddenResidues (normalizedShifts E)) (Nat.primesLE y)
        (n + intervalTranslation E y a).toNat ↔ integerAvoids E y n := by
  rw [avoids_forbiddenResidues_iff]
  constructor
  · intro hgood h hh p hp hpy
    have hh' : normalizedShift E h ∈ normalizedShifts E := Finset.mem_image.mpr ⟨h, hh, rfl⟩
    exact fun hd => hgood _ hh' p hp hpy ((translated_divisibility E y a n hn hh hp hpy).mpr hd)
  · intro hgood g hg p hp hpy hd
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
    exact hgood h hh p hp hpy ((translated_divisibility E y a n hn hh hp hpy).mp hd)

/-- Actual cardinality-preserving interval translation. -/
theorem integerAvoidedInterval_card_eq (E : Finset ℤ) (y : ℕ) (a : ℤ) (H : ℕ) :
    (integerAvoidedInterval E y a H).card =
      (avoidedInterval (normalizedShifts E) y (naturalStart E y a) H).card := by
  let c := intervalTranslation E y a
  have hs : (naturalStart E y a : ℤ) = a + c := naturalStart_cast E y a
  have hstart : 0 ≤ a + c := (by omega : (0 : ℤ) ≤ 1).trans (translated_start_pos E y a)
  apply Finset.card_bij (fun n _ => (n + c).toNat)
  · intro n hn
    obtain ⟨hnI, hnGood⟩ := Finset.mem_filter.mp hn
    have hi := Finset.mem_Ico.mp hnI
    have hnon : 0 ≤ n + c := by omega
    have hncast : ((n + c).toNat : ℤ) = n + c := Int.toNat_of_nonneg hnon
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Ico.mpr
      constructor
      · exact_mod_cast (show (naturalStart E y a : ℤ) ≤ ((n + c).toNat : ℤ) by omega)
      · exact_mod_cast (show ((n + c).toNat : ℤ) < (naturalStart E y a : ℤ) + (H : ℤ) by omega)
    · exact (translated_avoidance E y a n hnon).mpr hnGood
  · intro n hn m hm hnm
    have hin := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
    have him := Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1
    have hnc : ((n + c).toNat : ℤ) = n + c := Int.toNat_of_nonneg (by omega)
    have hmc : ((m + c).toNat : ℤ) = m + c := Int.toNat_of_nonneg (by omega)
    have he := congrArg (fun q : ℕ => (q : ℤ)) hnm
    rw [hnc, hmc] at he
    omega
  · intro m hm
    obtain ⟨hmI, hmGood⟩ := Finset.mem_filter.mp hm
    have him := Finset.mem_Ico.mp hmI
    have hmlo : (naturalStart E y a : ℤ) ≤ (m : ℤ) := by exact_mod_cast him.1
    have hmhi : (m : ℤ) < (naturalStart E y a : ℤ) + (H : ℤ) := by exact_mod_cast him.2
    let n : ℤ := (m : ℤ) - c
    have hnon : 0 ≤ n + c := by dsimp only [n]; omega
    have heq : (n + c).toNat = m := by dsimp only [n]; simp
    refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ?_, ?_⟩, heq⟩
    · dsimp only [n]
      omega
    · apply (translated_avoidance E y a n hnon).mp
      change CoreRoughMixedCRT.avoids (forbiddenResidues (normalizedShifts E))
        (Nat.primesLE y) (n + c).toNat
      rw [heq]
      exact hmGood

theorem integerAvoidedInterval_error (E : Finset ℤ) (hE : 1 ≤ E.card)
    {y : ℕ} (hy : 4 ≤ y) {R : ℝ}
    (hlevel : ((y : ℝ) + 1 / 2) ^ (9 * E.card + 1) ≤ R) (a : ℤ) (H : ℕ) :
    |((integerAvoidedInterval E y a H).card : ℝ) - (H : ℝ) * integerTupleSieveProduct E y| ≤
      (H : ℝ) * integerTupleSieveProduct E y *
        Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log ((y : ℝ) + 1 / 2)) +
      Real.exp (10 * (E.card : ℝ)) * R * (1 + Real.log R) ^ (E.card - 1) := by
  have hn : 1 ≤ (normalizedShifts E).card := by rwa [normalizedShifts_card]
  have hl : ((y : ℝ) + 1 / 2) ^ (9 * (normalizedShifts E).card + 1) ≤ R := by
    rwa [normalizedShifts_card]
  have hh := CoreRoughTupleCountFullRange.avoidedInterval_error_half
    (normalizedShifts E) hn hy hl (naturalStart E y a) H
  simpa only [← integerAvoidedInterval_card_eq, normalizedShifts_card,
    tupleProduct_normalizedShifts] using hh

def integerAvoidedIntervalReal (E : Finset ℤ) (y a : ℝ) (H : ℕ) : Finset ℤ :=
  (Ico (⌊a⌋ : ℤ) (⌊a⌋ + (H : ℤ))).filter
    (fun n => ∀ h ∈ E, ∀ p : ℕ, Nat.Prime p → (p : ℝ) ≤ y → ¬(p : ℤ) ∣ n + h)

/-- Real cutoff, arbitrary integer interval start and signed shifts. -/
theorem integerAvoidedInterval_error_realCutoff (E : Finset ℤ) (hE : 1 ≤ E.card)
    {y R : ℝ} (hy : 4 * (E.card : ℝ) < y)
    (hlevel : ((⌊y⌋₊ : ℝ) + 1 / 2) ^ (9 * E.card + 1) ≤ R) (a : ℤ) (H : ℕ) :
    |((integerAvoidedIntervalReal E y (a : ℝ) H).card : ℝ) -
        (H : ℝ) * integerTupleSieveProduct E ⌊y⌋₊| ≤
      (H : ℝ) * integerTupleSieveProduct E ⌊y⌋₊ *
        Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log ((⌊y⌋₊ : ℝ) + 1 / 2)) +
      Real.exp (10 * (E.card : ℝ)) * R * (1 + Real.log R) ^ (E.card - 1) := by
  have hc : (1 : ℝ) ≤ E.card := by exact_mod_cast hE
  have hy0 : 0 ≤ y := by linarith
  have hy4 : (4 : ℝ) ≤ y := by linarith
  have hfloor : 4 ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy0).mpr (by exact_mod_cast hy4)
  have heq : integerAvoidedIntervalReal E y (a : ℝ) H =
      integerAvoidedInterval E ⌊y⌋₊ a H := by
    ext n
    simp only [integerAvoidedIntervalReal, integerAvoidedInterval, integerAvoids,
      Int.floor_intCast, Finset.mem_filter, Nat.le_floor_iff hy0]
  rw [heq]
  exact integerAvoidedInterval_error E hE hfloor hlevel a H

/-- A saturated local factor annihilates BOTH the literal integer count and
Euler product, without division by that factor. -/
theorem count_and_product_zero_of_local_full (E : Finset ℤ) {p y : ℕ}
    (hp : Nat.Prime p) (hpy : p ≤ y) (hfull : integerResidueCount E p = p)
    (a : ℤ) (H : ℕ) :
    (integerAvoidedInterval E y a H).card = 0 ∧ integerTupleSieveProduct E y = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hres : E.image (fun h : ℤ => (h : ZMod p)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, ZMod.card, integerResidueCount] using hfull.ge
  constructor
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have hgood := (Finset.mem_filter.mp hn).2
    obtain ⟨h, hh, he⟩ := Finset.mem_image.mp
      (show -(n : ZMod p) ∈ E.image (fun h : ℤ => (h : ZMod p)) by rw [hres]; exact Finset.mem_univ _)
    apply hgood h hh p hp hpy
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_add, he, add_neg_cancel]
  · unfold integerTupleSieveProduct
    apply Finset.prod_eq_zero (Nat.mem_primesLE.mpr ⟨hpy, hp⟩)
    rw [hfull, div_self (Nat.cast_ne_zero.mpr hp.ne_zero), sub_self]

end
end PrimeGapNormality.Prime.CoreRoughIntegerTupleCount
