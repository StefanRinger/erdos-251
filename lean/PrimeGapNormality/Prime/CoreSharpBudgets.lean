import PrimeGapNormality.Prime.CoreRoughRemainderScalar
import PrimeGapNormality.Prime.CoreCalibratedMixtureMoments
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Exact finite constants displayed in V1's stopped-comparison section.
Only the model factorial moments enter.  No actual high moment is assumed.
-/
namespace PrimeGapNormality.Prime.CoreSharpBudgets
open Filter Finset
open scoped Topology Classical
noncomputable section

def momentExponent : ℝ := 6 + Real.log 5
def remainderBase : ℝ := (5 * Real.exp 1) ^ 20 / (19 : ℝ) ^ 19

theorem choose_div_factorial {j L : ℕ} (h : L ≤ j) :
    (j.choose L : ℝ) / (j.factorial : ℝ) =
      1 / ((L.factorial : ℝ) * ((j - L).factorial : ℝ)) := by
  have hf : (j.choose L : ℝ) * (L.factorial : ℝ) *
      ((j - L).factorial : ℝ) = (j.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  apply (div_eq_div_iff
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))
    (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero L))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j - L))))).2
  simpa only [one_mul, mul_assoc] using hf

theorem choose_factorial_term {j L : ℕ} (h : L ≤ j) (a : ℝ) :
    (j.choose L : ℝ) * (a ^ j / (j.factorial : ℝ)) =
      (a ^ L / (L.factorial : ℝ)) *
        (a ^ (j - L) / ((j - L).factorial : ℝ)) := by
  calc
    _ = ((j.choose L : ℝ) / (j.factorial : ℝ)) * a ^ j := by ring
    _ = (1 / ((L.factorial : ℝ) * ((j - L).factorial : ℝ))) * a ^ j := by
      rw [choose_div_factorial h]
    _ = _ := by
      have hp : a ^ j = a ^ L * a ^ (j - L) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      ring

theorem weighted_moment_bound {L r : ℕ} (hL : 1 ≤ L) (hr : L ≤ r)
    (Q : ℕ → ℝ)
    (hQ : ∀ j ∈ Icc L r, Q j ≤ (5 * (L : ℝ)) ^ j / (j.factorial : ℝ)) :
    (∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * Q j) ≤
      Real.exp (5 * (L : ℝ)) * (5 * (L : ℝ)) ^ L / (L.factorial : ℝ) := by
  let a : ℝ := 5 * L
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpoint (j : ℕ) (hj : j ∈ Icc L r) :
      ((j - 1).choose (L - 1) : ℝ) * Q j ≤
        (a ^ L / (L.factorial : ℝ)) *
          (a ^ (j - L) / ((j - L).factorial : ℝ)) := by
    have hjL := (mem_Icc.mp hj).1
    have hc : ((j - 1).choose (L - 1) : ℝ) ≤ (j.choose L : ℝ) := by
      have hp := Nat.choose_eq_choose_pred_add (by omega : 0 < j) (by omega : 0 < L)
      exact_mod_cast (show (j - 1).choose (L - 1) ≤ j.choose L by omega)
    calc
      _ ≤ ((j - 1).choose (L - 1) : ℝ) *
          (a ^ j / (j.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hQ j hj) (Nat.cast_nonneg _)
      _ ≤ (j.choose L : ℝ) * (a ^ j / (j.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hc (div_nonneg (pow_nonneg ha _) (Nat.cast_nonneg _))
      _ = _ := choose_factorial_term hjL a
  have hsum := sum_le_sum hpoint
  have hindex : (∑ j ∈ Icc L r, a ^ (j - L) / ((j - L).factorial : ℝ)) =
      ∑ t ∈ range (r + 1 - L), a ^ t / (t.factorial : ℝ) := by
    apply sum_bij (fun j _ => j - L)
    · intro j hj
      have hj' := mem_Icc.mp hj
      exact mem_range.mpr (by omega)
    · intro j hj k hk he
      have hj' := mem_Icc.mp hj
      have hk' := mem_Icc.mp hk
      omega
    · intro t ht
      have ht' := mem_range.mp ht
      refine ⟨L + t, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj
      rfl
  rw [← mul_sum, hindex] at hsum
  have he := Real.sum_le_exp_of_nonneg ha (r + 1 - L)
  have hh := hsum.trans (mul_le_mul_of_nonneg_left he
    (div_nonneg (pow_nonneg ha _) (Nat.cast_nonneg _)))
  exact hh.trans_eq (by dsimp [a]; ring)

theorem moment_envelope_le {L : ℕ} :
    Real.exp (5 * (L : ℝ)) * (5 * (L : ℝ)) ^ L / (L.factorial : ℝ) ≤
      Real.exp (momentExponent * (L : ℝ)) := by
  have hst := Real.pow_div_factorial_le_exp (x := (L : ℝ)) (Nat.cast_nonneg L) L
  have hpow : (5 : ℝ) ^ L = Real.exp ((L : ℝ) * Real.log 5) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  calc
    _ = Real.exp (5 * (L : ℝ)) * (5 : ℝ) ^ L *
        ((L : ℝ) ^ L / (L.factorial : ℝ)) := by rw [mul_pow]; ring
    _ ≤ Real.exp (5 * (L : ℝ)) * (5 : ℝ) ^ L * Real.exp (L : ℝ) :=
      mul_le_mul_of_nonneg_left hst (by positivity)
    _ = _ := by rw [hpow, ← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [momentExponent]; ring

theorem weighted_moment_bound_sharp {L r : ℕ} (hL : 1 ≤ L) (hr : L ≤ r)
    (Q : ℕ → ℝ)
    (hQ : ∀ j ∈ Icc L r, Q j ≤ (5 * (L : ℝ)) ^ j / (j.factorial : ℝ)) :
    (∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * Q j) ≤
      Real.exp ((6 + Real.log 5) * (L : ℝ)) :=
  (weighted_moment_bound hL hr Q hQ).trans moment_envelope_le

theorem remainder_scalar_eq {L r : ℕ} (hL : 1 ≤ L) (hr : L ≤ r) :
    (r.choose (L - 1) : ℝ) * (5 * (L : ℝ)) ^ (r + 1) /
        ((r + 1).factorial : ℝ) =
      (5 * (L : ℝ)) ^ (r + 1) /
        (((r + 1 : ℕ) : ℝ) * ((L - 1).factorial : ℝ) *
          ((r - L + 1).factorial : ℝ)) := by
  have hc := choose_div_factorial (show L - 1 ≤ r by omega)
  have hs : r - (L - 1) = r - L + 1 := by omega
  rw [hs] at hc
  rw [Nat.factorial_succ, Nat.cast_mul]
  calc
    _ = ((r.choose (L - 1) : ℝ) / (r.factorial : ℝ)) *
        (5 * (L : ℝ)) ^ (r + 1) / ((r + 1 : ℕ) : ℝ) := by ring
    _ = _ := by rw [hc]; ring

theorem remainder_fraction_factor {L r : ℕ} (hL : 1 ≤ L) (hr : L ≤ r) :
    (5 * (L : ℝ)) ^ (r + 1) /
        (((r + 1 : ℕ) : ℝ) * ((L - 1).factorial : ℝ) *
          ((r - L + 1).factorial : ℝ)) =
      ((L : ℝ) / ((r + 1 : ℕ) : ℝ)) * (5 : ℝ) ^ L *
        ((L : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ)) *
        ((5 * (L : ℝ)) ^ (r - L + 1) / ((r - L + 1).factorial : ℝ)) := by
  have hsplit : r + 1 = L + (r - L + 1) := by omega
  have hpower : (5 * (L : ℝ)) ^ (r + 1) =
      (5 : ℝ) ^ L * (L : ℝ) * (L : ℝ) ^ (L - 1) *
        (5 * (L : ℝ)) ^ (r - L + 1) := by
    rw [hsplit, pow_add, mul_pow]
    have hp : (L : ℝ) ^ L = (L : ℝ) ^ (L - 1) * L := by
      simpa only [Nat.sub_add_cancel hL] using (pow_succ (L : ℝ) (L - 1))
    rw [hp]
    ring
  rw [hpower]
  ring

theorem remainder_fraction_le_sharp {L r : ℕ} (hL : 2 ≤ L) (hr : 20 * L ≤ r) :
    (5 * (L : ℝ)) ^ (r + 1) /
        (((r + 1 : ℕ) : ℝ) * ((L - 1).factorial : ℝ) *
          ((r - L + 1).factorial : ℝ)) ≤ (1 / 20 : ℝ) * remainderBase ^ L := by
  let q := r - L + 1
  have hq : 19 * L ≤ q := by dsimp [q]; omega
  have hqpos : 0 < q := by omega
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hqpos
  have hLr : L ≤ r := by omega
  have hratio : (L : ℝ) / ((r + 1 : ℕ) : ℝ) ≤ 1 / 20 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos r))).2
    have hh : ((20 * L : ℕ) : ℝ) ≤ r := Nat.cast_le.mpr hr
    push_cast at *
    linarith
  have he : Real.exp 1 < 11 / 4 := Real.exp_one_lt_d9.trans (by norm_num)
  have hb0 : 0 ≤ 5 * Real.exp 1 / 19 := by positivity
  have hb1 : 5 * Real.exp 1 / 19 ≤ 1 := by linarith
  have hbase : Real.exp 1 * ((5 * L : ℕ) : ℝ) / q ≤ 5 * Real.exp 1 / 19 := by
    apply (div_le_iff₀ hqR).2
    have hh : ((19 * L : ℕ) : ℝ) ≤ q := Nat.cast_le.mpr hq
    have hmul := mul_le_mul_of_nonneg_left hh (Real.exp_pos 1).le
    push_cast at hmul ⊢
    nlinarith only [hmul]
  have hmoment : (5 * (L : ℝ)) ^ q / (q.factorial : ℝ) ≤
      (5 * Real.exp 1 / 19) ^ (19 * L) := by
    have hs := CoreRoughRemainderScalar.nat_pow_div_factorial_le_exp_ratio (5 * L) q hqpos
    calc
      _ ≤ (Real.exp 1 * ((5 * L : ℕ) : ℝ) / q) ^ q := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs
      _ ≤ (5 * Real.exp 1 / 19) ^ q := pow_le_pow_left₀ (by positivity) hbase q
      _ ≤ (5 * Real.exp 1 / 19) ^ (19 * L) := pow_le_pow_of_le_one hb0 hb1 hq
  have hst := Real.pow_div_factorial_le_exp (x := (L : ℝ)) (Nat.cast_nonneg L) (L - 1)
  have hfirst : (5 : ℝ) ^ L * ((L : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ)) ≤
      (5 * Real.exp 1) ^ L := by
    calc
      _ ≤ (5 : ℝ) ^ L * Real.exp (L : ℝ) := mul_le_mul_of_nonneg_left hst (by positivity)
      _ = _ := by
        have hexp : Real.exp (L : ℝ) = Real.exp 1 ^ L := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        rw [mul_pow, hexp]
  rw [remainder_fraction_factor (by omega) hLr]
  change ((L : ℝ) / ((r + 1 : ℕ) : ℝ)) * (5 : ℝ) ^ L *
    ((L : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ)) *
    ((5 * (L : ℝ)) ^ q / (q.factorial : ℝ)) ≤ _
  calc
    _ = ((L : ℝ) / ((r + 1 : ℕ) : ℝ)) *
        ((5 : ℝ) ^ L * ((L : ℝ) ^ (L - 1) / ((L - 1).factorial : ℝ))) *
        ((5 * (L : ℝ)) ^ q / (q.factorial : ℝ)) := by ring
    _ ≤ (1 / 20 : ℝ) * (5 * Real.exp 1) ^ L *
        (5 * Real.exp 1 / 19) ^ (19 * L) := by
      apply mul_le_mul
      · exact mul_le_mul hratio hfirst (by positivity) (by positivity)
      · exact hmoment
      · positivity
      · positivity
    _ = (1 / 20 : ℝ) * remainderBase ^ L := by
      rw [pow_mul, mul_assoc, ← mul_pow]
      congr 1
      unfold remainderBase
      rw [div_pow]
      have hp : (5 * Real.exp 1) * (5 * Real.exp 1) ^ 19 = (5 * Real.exp 1) ^ 20 := by ring
      rw [← mul_div_assoc, hp]

theorem remainderBase_pos : 0 < remainderBase := by unfold remainderBase; positivity

theorem remainderBase_lt_one : remainderBase < 1 := by
  have he : Real.exp 1 < 11 / 4 := Real.exp_one_lt_d9.trans (by norm_num)
  have hpower : (5 * Real.exp 1) ^ 20 ≤ (55 / 4 : ℝ) ^ 20 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 20
  unfold remainderBase
  apply (div_lt_one (by norm_num : (0 : ℝ) < 19 ^ 19)).2
  exact hpower.trans_lt (by norm_num)

theorem model_remainder_le_sharp (Ω : Finset ℕ) (ν : Finset ℕ → ℝ)
    {L r : ℕ} (hL : 2 ≤ L) (hr : 20 * L ≤ r)
    (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U)
    (hm : Stopped.countMoment Ω ν (r + 1) ≤
      (5 * (L : ℝ)) ^ (r + 1) / ((r + 1).factorial : ℝ)) :
    Stopped.modelRemainder Ω ν L r ≤ (1 / 20 : ℝ) *
      ((5 * Real.exp 1) ^ 20 / (19 : ℝ) ^ 19) ^ L := by
  have h0 := Stopped.modelRemainder_le (by omega : 1 ≤ L) (by omega : L ≤ r) hν
  have h1 := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (r.choose (L - 1)))
  have h2 : (r.choose (L - 1) : ℝ) *
      ((5 * (L : ℝ)) ^ (r + 1) / ((r + 1).factorial : ℝ)) ≤
        (1 / 20 : ℝ) * remainderBase ^ L := by
    rw [← mul_div_assoc, remainder_scalar_eq (by omega) (by omega)]
    exact remainder_fraction_le_sharp hL hr
  exact (h0.trans h1).trans h2

theorem profile_model_remainder_le_sharp (Ω : Finset ℕ) (ν : Finset ℕ → ℝ)
    {L : ℕ} (hL : 2 ≤ L) (hν : ∀ U ∈ Ω.powerset, 0 ≤ ν U)
    (hm : Stopped.countMoment Ω ν (profileR L 20 + 1) ≤
      (5 * (L : ℝ)) ^ (profileR L 20 + 1) /
        ((profileR L 20 + 1).factorial : ℝ)) :
    Stopped.modelRemainder Ω ν L (profileR L 20) ≤
      (1 / 20 : ℝ) * ((5 * Real.exp 1) ^ 20 / (19 : ℝ) ^ 19) ^ L :=
  model_remainder_le_sharp Ω ν hL
    (CoreRoughRemainderScalar.profileR_twenty_bounds L).1 hν hm

/-- Actual normalized calibrated mixtures supply the two paper-sharp
budgets.  One eventual threshold precedes every stopped order r, and no
model moment bound remains an assumption. -/
theorem eventually_actual_model_sharp_budgets
    {G : ℕ → ℝ} {M : ℕ → ℕ} {κ : ℝ}
    (hG : Tendsto G atTop atTop) (hκ : 0 < κ)
    (hM : Tendsto (fun X => (M X : ℝ) / Real.log (G X)) atTop (𝓝 κ))
    {w : ℕ → ℕ → ℝ} (hw : ∀ X y, 0 ≤ w X y)
    (hsum : ∀ X, ∑' y : ℕ, w X y = 1)
    (hcal : CoreCalibratedMixtureFiniteSupport.UniformCalibration w G) :
    ∀ᶠ X : ℕ in atTop,
      (∀ r : ℕ, 1 ≤ M X → M X ≤ r →
        (∑ j ∈ Icc (M X) r, ((j - 1).choose (M X - 1) : ℝ) *
          Stopped.countMoment
            (offsetWindow (CoreCalibratedMixtureProfile.physicalSpan G M X))
            (CoreCalibratedMixtureMoments.law (w X)
              (CoreCalibratedMixtureProfile.physicalSpan G M X)) j) ≤
          Real.exp ((6 + Real.log 5) * (M X : ℝ))) ∧
      (2 ≤ M X →
        Stopped.modelRemainder
          (offsetWindow (CoreCalibratedMixtureProfile.physicalSpan G M X))
          (CoreCalibratedMixtureMoments.law (w X)
            (CoreCalibratedMixtureProfile.physicalSpan G M X))
          (M X) (profileR (M X) 20) ≤
          (1 / 20 : ℝ) * ((5 * Real.exp 1) ^ 20 / (19 : ℝ) ^ 19) ^ (M X)) := by
  filter_upwards [CoreCalibratedMixtureMoments.eventually_all_countMoments_le_five
    hG hκ hM hw hsum hcal] with X hX
  constructor
  · intro r hMX hr
    exact weighted_moment_bound_sharp hMX hr _ (fun j _ => hX j)
  · intro hMX
    apply profile_model_remainder_le_sharp _ _ hMX
    · intro U _
      exact CoreCalibratedMixtureMoments.law_nonneg (w X) (hw X) _ U
    · exact hX _

end
end PrimeGapNormality.Prime.CoreSharpBudgets
