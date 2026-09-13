import PrimeGapNormality.Prime.CoreRoughTupleCount
import PrimeGapNormality.Prime.CoreRoughEulerStability
import PrimeGapNormality.Prime.SingularSeriesTail

/-!
# Finite tuple counts between two literal moving cutoffs

The moving interval is sandwiched pointwise between the two static
intervals. Euler stability is multiplied through, never divided by a
possibly zero tuple product. No smallness assumption on the beta error is
needed for the lower bound.
-/

namespace PrimeGapNormality.Prime.CoreRoughMovingCount

open Finset CoreMovingRoughSequence CoreRoughShiftResidues CoreRoughTupleCount
open scoped Classical
noncomputable section

set_option maxHeartbeats 800000

def movingTupleInterval (z : ℕ → ℕ) (E : Finset ℕ) (a H : ℕ) : Finset ℕ :=
  (Ico a (a + H)).filter (fun n => ∀ h ∈ E, RoughAt (z (n + h)) (n + h))

theorem roughAt_mono {u v n : ℕ} (huv : u ≤ v) (h : RoughAt v n) : RoughAt u n :=
  ⟨h.1, fun p hp hd => huv.trans_lt (h.2 p hp hd)⟩

theorem static_subset_moving (z : ℕ → ℕ) (E : Finset ℕ) (a H : ℕ) (yu : ℕ)
    (hupper : ∀ n ∈ Ico a (a + H), ∀ h ∈ E, z (n + h) ≤ yu) :
    translatedRoughInterval E yu a H ⊆ movingTupleInterval z E a H := by
  intro n hn
  obtain ⟨hnI, hn⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hnI, fun h hh => roughAt_mono (hupper n hnI h hh) (hn h hh)⟩

theorem moving_subset_static (z : ℕ → ℕ) (E : Finset ℕ) (a H : ℕ) (yl : ℕ)
    (hlower : ∀ n ∈ Ico a (a + H), ∀ h ∈ E, yl ≤ z (n + h)) :
    movingTupleInterval z E a H ⊆ translatedRoughInterval E yl a H := by
  intro n hn
  obtain ⟨hnI, hn⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hnI, fun h hh => roughAt_mono (hlower n hnI h hh) (hn h hh)⟩

def betaError (k : ℕ) (R : ℝ) (y : ℕ) : ℝ :=
  Real.exp (299 * (k : ℝ) - Real.log R / Real.log ((y : ℝ) + 1 / 2))

/-- A common positive logarithmic level gives a larger beta error at the
upper cutoff. -/
theorem betaError_mono (k : ℕ) {R : ℝ} (hR : 1 ≤ R) {yl yu : ℕ}
    (hyl : 16 ≤ yl) (hlyu : yl ≤ yu) : betaError k R yl ≤ betaError k R yu := by
  have hylR : (16 : ℝ) ≤ yl := by exact_mod_cast hyl
  have hlogl : 0 < Real.log ((yl : ℝ) + 1 / 2) := Real.log_pos (by linarith)
  have hlogs : Real.log ((yl : ℝ) + 1 / 2) ≤ Real.log ((yu : ℝ) + 1 / 2) :=
    Real.log_le_log (by linarith) (_root_.add_le_add (Nat.cast_le.mpr hlyu) le_rfl)
  apply Real.exp_le_exp.mpr
  exact sub_le_sub_left
    (div_le_div_of_nonneg_left (Real.log_nonneg hR) hlogl hlogs) _

/-- Actual moving-cutoff tuple count. The finite hypotheses say exactly
which two static cutoffs enclose every translated argument, and bound the
sum of new prime hazards. Neither is a distribution/shape oracle. -/
theorem movingTupleInterval_error
    (z : ℕ → ℕ) (E : Finset ℕ) (hE : 1 ≤ E.card) (a H : ℕ) (ha : 1 ≤ a)
    {yl yu : ℕ} (hyl : 16 ≤ yl) (hlyu : yl ≤ yu)
    (hcut : ∀ n ∈ Ico a (a + H), ∀ h ∈ E, yl ≤ z (n + h) ∧ z (n + h) ≤ yu)
    {δ R : ℝ} (hδhalf : δ ≤ 1 / 2)
    (hband : ∑ p ∈ Nat.primesLE yu \ Nat.primesLE yl,
      (residueCount E p : ℝ) / (p : ℝ) ≤ δ)
    (hlevel : ((yu : ℝ) + 1 / 2) ^ (9 * E.card + 1) ≤ R) :
    |((movingTupleInterval z E a H).card : ℝ) - (H : ℝ) * finiteTupleSieveProduct E yl| ≤
      (H : ℝ) * finiteTupleSieveProduct E yl *
        (δ + Real.exp (299 * (E.card : ℝ) - Real.log R / Real.log ((yu : ℝ) + 1 / 2))) +
      Real.exp (10 * (E.card : ℝ)) * R * (1 + Real.log R) ^ (E.card - 1) := by
  have hyu : 16 ≤ yu := hyl.trans hlyu
  have hyuR : (16 : ℝ) ≤ yu := by exact_mod_cast hyu
  have hylR : (16 : ℝ) ≤ yl := by exact_mod_cast hyl
  have hZ : 1 < (yu : ℝ) + 1 / 2 := by linarith
  have hR : 1 < R := hZ.trans_le
    ((le_self_pow₀ hZ.le (by omega : 9 * E.card + 1 ≠ 0)).trans hlevel)
  have hlowlevel : ((yl : ℝ) + 1 / 2) ^ (9 * E.card + 1) ≤ R :=
    (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (yl : ℝ) + 1 / 2)
      (_root_.add_le_add (Nat.cast_le.mpr hlyu) le_rfl) _).trans hlevel
  have hstaticl := translatedRoughInterval_error_half E hE hyl hlowlevel a H ha
  have hstaticu := translatedRoughInterval_error_half E hE hyu hlevel a H ha
  have hlcount : ((movingTupleInterval z E a H).card : ℝ) ≤
      (translatedRoughInterval E yl a H).card :=
    Nat.cast_le.mpr (Finset.card_le_card
      (moving_subset_static z E a H yl (fun n hn h hh => (hcut n hn h hh).1)))
  have hucount : ((translatedRoughInterval E yu a H).card : ℝ) ≤
      (movingTupleInterval z E a H).card :=
    Nat.cast_le.mpr (Finset.card_le_card
      (static_subset_moving z E a H yu (fun n hn h hh => (hcut n hn h hh).2)))
  have hstable := CoreRoughEulerStability.finiteTupleSieveProduct_bounds E hlyu hband
  have hVl := finiteTupleSieveProduct_nonneg E yl
  have hVu := finiteTupleSieveProduct_nonneg E yu
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hband0 : 0 ≤ ∑ p ∈ Nat.primesLE yu \ Nat.primesLE yl,
      (residueCount E p : ℝ) / (p : ℝ) := Finset.sum_nonneg
    (fun p hp => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hδ0 : 0 ≤ δ := hband0.trans hband
  have hemono := betaError_mono E.card hR.le hyl hlyu
  have hlupper := (abs_le.mp hstaticl).2
  have hulower := (abs_le.mp hstaticu).1
  have hlscale := mul_le_mul_of_nonneg_left hstable.1 hH
  have huscale := mul_le_mul_of_nonneg_left hstable.2 hH
  have he0 : 0 ≤ betaError E.card R yu := (Real.exp_pos _).le
  have heprod := mul_le_mul_of_nonneg_right huscale he0
  have hsmallError := mul_le_mul_of_nonneg_left hemono (mul_nonneg hH hVl)
  have hdelta := mul_nonneg (mul_nonneg hH hVl) hδ0
  dsimp only [betaError] at hemono he0 heprod hsmallError
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith

/-- A covering prime below the lower cutoff forces exact vanishing of
the moving count as well as the lower-cutoff main product. -/
theorem movingTupleInterval_zero_of_local_full
    (z : ℕ → ℕ) (E : Finset ℕ) (a H : ℕ) (ha : 1 ≤ a)
    {yl p : ℕ} (hp : Nat.Prime p) (hpy : p ≤ yl)
    (hlower : ∀ n ∈ Ico a (a + H), ∀ h ∈ E, yl ≤ z (n + h))
    (hfull : forbiddenResidues E p = Finset.univ) :
    (movingTupleInterval z E a H).card = 0 ∧ finiteTupleSieveProduct E yl = 0 := by
  have hh := count_and_product_zero_of_local_full (H := H) E ha hp hpy hfull
  refine ⟨?_, hh.2⟩
  have hle := Finset.card_le_card (moving_subset_static z E a H yl hlower)
  rw [hh.1] at hle
  exact Nat.eq_zero_of_le_zero hle

end
end PrimeGapNormality.Prime.CoreRoughMovingCount
