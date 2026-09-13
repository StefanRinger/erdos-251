import PrimeGapNormality.Prime.CoreIntegerGapInsertion
import PrimeGapNormality.Prime.CoreRoundedPowerScaling
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Uniform rounded-power approximation on an actual insertion slot

The exact adjacent-gap action from `CoreIntegerGapInsertion` is scaled by
`G^a`.  The compact expansion of each rounded combination then gives the
continuous leading action

`Q_s(W,z) = B b_s z^a + b_(s+1) (W-z)^a`.

The approximation is uniform over every integer split of a slot of width at
most `A G`, and over all period labels.  A separate theorem transfers this
real error through the quotient map and any fixed Lipschitz circle test.
The discontinuous rounded functions themselves are never used as weak-
convergence test functions.
-/

namespace PrimeGapNormality.Prime.CoreRoundedSlotApproximation

open Finset Filter CoreCyclic
open CoreRoundedPowerScaling CoreIntegerGapInsertion
open scoped Topology Classical NNReal BoundedContinuousFunction

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

/-- Continuous leading two-gap action on a normalized slot. -/
def leadingPairAction
    (B : ℕ) {I : Type*} [Fintype I] {k : ℕ} (hk : 0 < k)
    (alpha : I → ℝ) (b : Fin k → I → ℤ) (a : ℝ)
    (s : Fin k) (W z : ℝ) : ℝ :=
  (B : ℝ) * leadingColumn alpha b a s * z ^ a +
    leadingColumn alpha b a (cyclicSucc hk s) * (W - z) ^ a

private theorem pairActionInt_cast
    (B : ℕ) {I : Type*} [Fintype I] {k : ℕ} (hk : 0 < k)
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    (s : Fin k) (left right : ℕ) :
    (pairActionInt B hk s (roundedCombination kind alpha b) left right : ℝ) =
      (B : ℝ) * roundedCombinationReal kind alpha b s left +
        roundedCombinationReal kind alpha b (cyclicSucc hk s) right := by
  unfold pairActionInt
  rw [Int.cast_add, Int.cast_mul, Int.cast_natCast,
    roundedCombination_cast, roundedCombination_cast]

private theorem scale_mul_inv_scale {G a : ℝ} (hG : 0 < G) :
    G ^ a * G ^ (-a) = 1 := by
  rw [← Real.rpow_add hG]
  simp

/-- Uniform real approximation of the exact integer pair action. -/
theorem eventually_pairAction_scaled_approx
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a A : ℝ} (ha : 0 < a) (haOne : a ≤ 1) (hA : 0 ≤ A)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    {B : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ G : ℝ in atTop,
      ∀ s : Fin k, ∀ left right j : ℕ,
        ((left + right : ℕ) : ℝ) ≤ A * G →
        1 ≤ G ^ a / (B : ℝ) ^ (j + 1) →
        G ^ a / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k →
        |(pairActionInt B hk s (roundedCombination kind alpha b) left right : ℝ) /
              (B : ℝ) ^ (j + 1) -
            (G ^ a / (B : ℝ) ^ (j + 1)) *
              leadingPairAction B hk alpha b a s
                (((left + right : ℕ) : ℝ) / G) ((left : ℝ) / G)| < ε := by
  intro ε hε
  let M : ℝ := (B : ℝ) ^ k * ((B : ℝ) + 1)
  have hM : 0 < M := by dsimp only [M]; positivity
  let δ : ℝ := ε / M
  have hδ : 0 < δ := div_pos hε hM
  have happ := eventually_roundedCombination_compact_expansion
    kind alpha b ha haOne hA halpha δ hδ
  filter_upwards [happ, eventually_gt_atTop (0 : ℝ)] with G happrox hG
  intro s left right j hwidth hthetaLo hthetaHi
  have hleftWidth : (left : ℝ) ≤ A * G :=
    (Nat.cast_le.mpr (by omega : left ≤ left + right)).trans hwidth
  have hrightWidth : (right : ℝ) ≤ A * G :=
    (Nat.cast_le.mpr (by omega : right ≤ left + right)).trans hwidth
  have hleft := happrox s left hleftWidth
  have hright := happrox (cyclicSucc hk s) right hrightWidth
  let theta : ℝ := G ^ a / (B : ℝ) ^ (j + 1)
  let eu : ℝ := G ^ (-a) * roundedCombinationReal kind alpha b s left -
    leadingColumn alpha b a s * ((left : ℝ) / G) ^ a
  let ev : ℝ := G ^ (-a) *
      roundedCombinationReal kind alpha b (cyclicSucc hk s) right -
    leadingColumn alpha b a (cyclicSucc hk s) * ((right : ℝ) / G) ^ a
  have heu : |eu| < δ := by simpa only [eu] using hleft
  have hev : |ev| < δ := by simpa only [ev] using hright
  have htheta0 : 0 ≤ theta := zero_le_one.trans (by simpa only [theta] using hthetaLo)
  have hthetaUpper : theta < (B : ℝ) ^ k := by
    simpa only [theta] using hthetaHi
  have hrightCoord :
      (((left + right : ℕ) : ℝ) / G) - (left : ℝ) / G =
        (right : ℝ) / G := by
    push_cast
    ring
  have hscaled :
      (pairActionInt B hk s (roundedCombination kind alpha b) left right : ℝ) /
          (B : ℝ) ^ (j + 1) =
        theta * ((B : ℝ) *
            (G ^ (-a) * roundedCombinationReal kind alpha b s left) +
          G ^ (-a) * roundedCombinationReal kind alpha b (cyclicSucc hk s) right) := by
    rw [pairActionInt_cast]
    dsimp only [theta]
    have hinv := scale_mul_inv_scale hG (a := a)
    have hden : (B : ℝ) ^ (j + 1) ≠ 0 := by positivity
    calc
      ((B : ℝ) * roundedCombinationReal kind alpha b s left +
          roundedCombinationReal kind alpha b (cyclicSucc hk s) right) /
            (B : ℝ) ^ (j + 1) =
        (G ^ a / (B : ℝ) ^ (j + 1)) *
          (G ^ (-a) * ((B : ℝ) * roundedCombinationReal kind alpha b s left +
            roundedCombinationReal kind alpha b (cyclicSucc hk s) right)) := by
              field_simp [hden]
              rw [mul_assoc, hinv, mul_one]
      _ = (G ^ a / (B : ℝ) ^ (j + 1)) *
          ((B : ℝ) *
              (G ^ (-a) * roundedCombinationReal kind alpha b s left) +
            G ^ (-a) * roundedCombinationReal kind alpha b
              (cyclicSucc hk s) right) := by ring
  have herror :
      (pairActionInt B hk s (roundedCombination kind alpha b) left right : ℝ) /
            (B : ℝ) ^ (j + 1) -
          theta * leadingPairAction B hk alpha b a s
            (((left + right : ℕ) : ℝ) / G) ((left : ℝ) / G) =
        theta * ((B : ℝ) * eu + ev) := by
    rw [hscaled]
    unfold leadingPairAction
    rw [hrightCoord]
    dsimp only [eu, ev]
    ring
  rw [herror, abs_mul, abs_of_nonneg htheta0]
  have hinner : |(B : ℝ) * eu + ev| < ((B : ℝ) + 1) * δ := by
    calc
      |(B : ℝ) * eu + ev| ≤ |(B : ℝ) * eu| + |ev| := abs_add_le _ _
      _ = (B : ℝ) * |eu| + |ev| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg B)]
      _ < (B : ℝ) * δ + δ :=
        add_lt_add (mul_lt_mul_of_pos_left heu (by positivity)) hev
      _ = ((B : ℝ) + 1) * δ := by ring
  have hinner0 : 0 < ((B : ℝ) + 1) * δ := by positivity
  calc
    theta * |(B : ℝ) * eu + ev| <
        theta * (((B : ℝ) + 1) * δ) :=
      mul_lt_mul_of_pos_left hinner (zero_lt_one.trans_le hthetaLo)
    _ < (B : ℝ) ^ k * (((B : ℝ) + 1) * δ) :=
      mul_lt_mul_of_pos_right hthetaUpper hinner0
    _ = ε := by
      dsimp only [δ, M]
      field_simp [hM.ne']

private theorem circle_dist_add_coe_le (O : Circle) (x y : ℝ) :
    dist (O + (x : Circle)) (O + (y : Circle)) ≤ |x - y| := by
  rw [dist_add_left]
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem lipschitz_circleTest_add_error
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    (O : Circle) (x y : ℝ) :
    |f (O + (x : Circle)) - f (O + (y : Circle))| ≤
      K * |x - y| := by
  have h := hK.dist_le_mul (O + (x : Circle)) (O + (y : Circle))
  rw [Real.dist_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (circle_dist_add_coe_le O x y) K.coe_nonneg)

/-- Actual inserted finite phases are uniformly indistinguishable, under a
Lipschitz circle test, from the continuous leading slot action. -/
theorem eventually_actualFiniteObservablePhase_test_approx
    {I : Type*} [Fintype I] {k : ℕ}
    (kind : RoundKind) (alpha : I → ℝ) (b : Fin k → I → ℤ)
    {a A : ℝ} (ha : 0 < a) (haOne : a ≤ 1) (hA : 0 ≤ A)
    (halpha : ∀ i, 0 < alpha i ∧ (alpha i = a ∨ alpha i < a))
    {B : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (r : Fin k)
    (f : Circle →ᵇ ℝ) {Kf : ℝ≥0} (hKf : LipschitzWith Kf f) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ G : ℝ in atTop,
      ∀ L j : ℕ, 1 ≤ j → j < L →
      ∀ Aset frame : Finset ℕ,
      ∀ hE : (CoreActualCyclicSlot.slot Aset frame j).Nonempty,
      ∀ u ∈ CoreActualCyclicSlot.slot Aset frame j,
      (((CoreLinearInsertion.insertionSlot frame j).2 -
          (CoreLinearInsertion.insertionSlot frame j).1 : ℕ) : ℝ) ≤ A * G →
      1 ≤ G ^ a / (B : ℝ) ^ (j + 1) →
      G ^ a / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k →
      |f (actualFiniteObservablePhase B hk r
            (roundedCombination kind alpha b) L (insert u frame) : Circle) -
        f ((selectedObservableOuter B hk r (roundedCombination kind alpha b)
              L j Aset frame hE : Circle) +
          (((G ^ a / (B : ℝ) ^ (j + 1)) *
            leadingPairAction B hk alpha b a (phaseAt hk r (j - 1))
              ((((CoreLinearInsertion.insertionSlot frame j).2 -
                (CoreLinearInsertion.insertionSlot frame j).1 : ℕ) : ℝ) / G)
              (((u - (CoreLinearInsertion.insertionSlot frame j).1 : ℕ) : ℝ) / G) : ℝ) :
            Circle))| ≤ Kf * ε := by
  intro ε hε
  have happ := eventually_pairAction_scaled_approx kind alpha b ha haOne hA halpha
    hB hk ε hε
  filter_upwards [happ, eventually_gt_atTop (0 : ℝ)] with G happrox hG
  intro L j hj hjL Aset frame hE u hu hwidth hthetaLo hthetaHi
  have huSlot := mem_openSlot.mp hu
  have hleft : (CoreLinearInsertion.insertionSlot frame j).1 ≤ u := huSlot.2.1.le
  have hright : u ≤ (CoreLinearInsertion.insertionSlot frame j).2 := huSlot.2.2.le
  let ql := u - (CoreLinearInsertion.insertionSlot frame j).1
  let qr := (CoreLinearInsertion.insertionSlot frame j).2 - u
  have hsum : ql + qr =
      (CoreLinearInsertion.insertionSlot frame j).2 -
        (CoreLinearInsertion.insertionSlot frame j).1 := by
    dsimp only [ql, qr]
    omega
  have hpair := happrox (phaseAt hk r (j - 1)) ql qr j
    (by simpa only [hsum] using hwidth) hthetaLo hthetaHi
  have hphase := actualFiniteObservablePhase_eq_outer_add hB hk r
    (roundedCombination kind alpha b) hj hjL Aset frame hE hu
  have hphaseCircle := congrArg (fun x : ℝ ↦ (x : Circle)) hphase
  simp only [AddCircle.coe_add] at hphaseCircle
  rw [hphaseCircle]
  have htest := lipschitz_circleTest_add_error f hKf
    (selectedObservableOuter B hk r (roundedCombination kind alpha b)
      L j Aset frame hE)
    ((pairActionInt B hk (phaseAt hk r (j - 1))
      (roundedCombination kind alpha b) ql qr : ℝ) / (B : ℝ) ^ (j + 1))
    ((G ^ a / (B : ℝ) ^ (j + 1)) *
      leadingPairAction B hk alpha b a (phaseAt hk r (j - 1))
        (((ql + qr : ℕ) : ℝ) / G) ((ql : ℝ) / G))
  have hbound := htest.trans
    (mul_le_mul_of_nonneg_left hpair.le Kf.coe_nonneg)
  rw [hsum] at hbound
  simpa only [ql, qr] using hbound

end
end PrimeGapNormality.Prime.CoreRoundedSlotApproximation
