import PrimeGapNormality.Prime.FiniteSelbergAsymptoticCap
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A Selberg reciprocal-prime cap on short translated intervals

This module proves a generous uniform bound for actual primes in
`[a,a+M)`, with `a` on the scale of `y` and `M≤y`.  It uses only the
compiled finite Selberg cap.  No quantitative PNT or short-interval prime
estimate is assumed.
-/

namespace PrimeGapNormality.Prime.CoreRoughPrimeBand

open Filter Finset
open scoped Topology

noncomputable section

/-- Actual primes in the half-open natural interval `[a,a+M)`. -/
def primeIco (a M : ℕ) : Finset ℕ :=
  (Ico a (a + M)).filter Nat.Prime

/-- Positive translated offsets used by the finite Selberg cap. -/
def translatedPrimeOffsets (a M : ℕ) : Finset ℕ :=
  (Icc 1 M).filter (fun n ↦ Nat.Prime (a + n))

/-- Actual reciprocal mass of the prime interval. -/
def primeIcoReciprocal (a M : ℕ) : ℝ :=
  ∑ p ∈ primeIco a M, (p : ℝ)⁻¹

private theorem primeIco_card_le_offsets_add_one (a M : ℕ) :
    (primeIco a M).card ≤ (translatedPrimeOffsets a M).card + 1 := by
  let target := insert a ((translatedPrimeOffsets a M).image (fun n ↦ a + n))
  have hsub : primeIco a M ⊆ target := by
    intro p hp
    have hp' := mem_filter.mp hp
    have hpI := mem_Ico.mp hp'.1
    by_cases hpa : p = a
    · subst p
      exact mem_insert_self _ _
    · have hap : a < p := lt_of_le_of_ne hpI.1 (Ne.symm hpa)
      let n := p - a
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hap)
      have hnM : n ≤ M := by dsimp only [n]; omega
      have hsum : a + n = p := by
        dsimp only [n]
        exact Nat.add_sub_of_le hpI.1
      have hnPrime : Nat.Prime (a + n) := by
        rw [hsum]
        exact hp'.2
      apply mem_insert_of_mem
      apply mem_image.mpr
      refine ⟨n, ?_, hsum⟩
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hn1, hnM⟩, hnPrime⟩
  calc
    (primeIco a M).card ≤ target.card := card_le_card hsub
    _ ≤ (((translatedPrimeOffsets a M).image (fun n ↦ a + n)).card + 1) :=
      card_insert_le _ _
    _ ≤ (translatedPrimeOffsets a M).card + 1 :=
      Nat.add_le_add_right card_image_le 1

private theorem primeIcoReciprocal_le_card
    {y a M : ℕ} (hy : 1 ≤ y) (hya : y ≤ 2 * a) :
    primeIcoReciprocal a M ≤ (primeIco a M).card * (2 / (y : ℝ)) := by
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (zero_lt_one.trans_le hy)
  unfold primeIcoReciprocal
  calc
    ∑ p ∈ primeIco a M, (p : ℝ)⁻¹ ≤
        ∑ _p ∈ primeIco a M, (2 / (y : ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hpI := mem_Ico.mp (mem_filter.mp hp).1
      have hpNat : 0 < p := by
        have : y ≤ 2 * p := hya.trans (Nat.mul_le_mul_left 2 hpI.1)
        omega
      have hpPos : (0 : ℝ) < p := Nat.cast_pos.mpr hpNat
      have hyp : (y : ℝ) ≤ 2 * (p : ℝ) := by
        exact_mod_cast hya.trans (Nat.mul_le_mul_left 2 hpI.1)
      have hdiv : (y : ℝ) / (p : ℝ) ≤ 2 :=
        (div_le_iff₀ hpPos).2 hyp
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hypos).2
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hdiv
    _ = (primeIco a M).card * (2 / (y : ℝ)) := by
      rw [sum_const, nsmul_eq_mul]

private theorem translatedPrimeOffsets_avoids
    {a M R : ℕ} (hRa : R ≤ a) :
    ∀ q ∈ Nat.primesLE R, ∃ c : ℕ,
      ∀ n ∈ translatedPrimeOffsets a M, n % q ≠ c % q := by
  intro q hq
  have hqPrime := Nat.prime_of_mem_primesLE hq
  letI : NeZero q := ⟨hqPrime.ne_zero⟩
  let c : ℕ := (-((a : ℕ) : ZMod q)).val
  refine ⟨c, ?_⟩
  intro n hn heq
  have hnPrime := (mem_filter.mp hn).2
  have hncast : (n : ZMod q) = (c : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff' n c q).mpr heq
  have hccast : (c : ZMod q) = -((a : ℕ) : ZMod q) := by
    dsimp only [c]
    exact ZMod.natCast_zmod_val _
  have hzero : ((a + n : ℕ) : ZMod q) = 0 := by
    push_cast
    rw [hncast, hccast, add_neg_cancel]
  have hdiv : q ∣ a + n :=
    (ZMod.natCast_eq_zero_iff (a + n) q).mp hzero
  have heqPrime : q = a + n :=
    (Nat.prime_dvd_prime_iff_eq hqPrime hnPrime).mp hdiv
  have hqle : q ≤ R := (Nat.mem_primesLE.mp hq).1
  have hn1 : 1 ≤ n := (mem_Icc.mp (mem_filter.mp hn).1).1
  have : q < a + n := (hqle.trans hRa).trans_lt (Nat.lt_add_of_pos_right hn1)
  exact this.ne heqPrime

private theorem two_mul_selbergRadius_le
    {M : ℕ} (hM : 4 ≤ M) : 2 * selbergRadius M ≤ M := by
  have hMR : (4 : ℝ) ≤ M := Nat.cast_le.mpr hM
  have hMpos : (0 : ℝ) < M := zero_lt_four.trans_le hMR
  have hlog : (1 : ℝ) ≤ Real.log (M : ℝ) := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h3M : (3 : ℝ) ≤ M := (by norm_num : (3 : ℝ) ≤ 4).trans hMR
    exact (Real.le_log_iff_exp_le hMpos).mpr (hexp.le.trans h3M)
  have hsqrt : Real.sqrt (M : ℝ) ≤ (M : ℝ) / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have harg0 : 0 ≤ Real.sqrt (M : ℝ) / Real.log (M : ℝ) :=
    div_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans hlog)
  have hfloor : (selbergRadius M : ℝ) ≤
      Real.sqrt (M : ℝ) / Real.log (M : ℝ) := by
    exact Nat.floor_le harg0
  have hdiv : Real.sqrt (M : ℝ) / Real.log (M : ℝ) ≤
      Real.sqrt (M : ℝ) := by
    exact div_le_self (Real.sqrt_nonneg _) hlog
  have hcast : (2 * selbergRadius M : ℕ) ≤ M := by
    exact_mod_cast (calc
      (2 : ℝ) * (selbergRadius M : ℝ) ≤
          2 * (Real.sqrt (M : ℝ) / Real.log (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hfloor (by norm_num)
      _ ≤ 2 * Real.sqrt (M : ℝ) :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ ≤ (M : ℝ) := by linarith)
  simpa only [Nat.mul_comm] using hcast

private theorem logM_ge_half_logy
    {y M : ℕ} (hy : 1 ≤ y)
    (hMy : Real.sqrt (y : ℝ) ≤ (M : ℝ)) :
    Real.log (y : ℝ) / 2 ≤ Real.log (M : ℝ) := by
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (zero_lt_one.trans_le hy)
  have hsqrtPos : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.2 hypos
  calc
    Real.log (y : ℝ) / 2 = Real.log (Real.sqrt (y : ℝ)) := by
      rw [Real.log_sqrt hypos.le]
    _ ≤ Real.log (M : ℝ) := Real.log_le_log hsqrtPos hMy

/-- Uniform reciprocal-prime cap on `[a,a+M)`.  The constants are generous
and absolute; the outer eventual threshold is independent of `a,M`. -/
theorem eventually_primeIcoReciprocal_le :
    ∀ᶠ y : ℕ in atTop, ∀ a M : ℕ, y ≤ 2 * a → M ≤ y →
      primeIcoReciprocal a M ≤
        12 * (M : ℝ) / ((y : ℝ) * Real.log (y : ℝ)) +
          12 / Real.sqrt (y : ℝ) := by
  have hcap := eventually_finiteSelberg_card_le_two_add_eps
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp hcap
  have hsqrtTop : Tendsto (fun y : ℕ ↦ Real.sqrt (y : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 16,
    hsqrtTop.eventually (eventually_ge_atTop (M0 : ℝ))] with y hy16 hsqrtM0
  intro a M hya hMy
  have hy1 : 1 ≤ y := le_trans (by norm_num) hy16
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (zero_lt_one.trans_le hy1)
  have hsqrtPos : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.2 hypos
  have hrecipCard := primeIcoReciprocal_le_card
    (y := y) (a := a) (M := M) hy1 hya
  by_cases hlarge : Real.sqrt (y : ℝ) ≤ (M : ℝ)
  · have hM0Nat : M0 ≤ M := by
      exact_mod_cast hsqrtM0.trans hlarge
    have hM4 : 4 ≤ M := by
      have hsqrt4 : (4 : ℝ) ≤ Real.sqrt (y : ℝ) := by
        exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) hypos.le).2
          (by exact_mod_cast hy16)
      exact_mod_cast hsqrt4.trans hlarge
    have hRa : selbergRadius M ≤ a := by
      have htwoR := two_mul_selbergRadius_le hM4
      have : 2 * selbergRadius M ≤ 2 * a := htwoR.trans (hMy.trans hya)
      omega
    have hA : translatedPrimeOffsets a M ⊆ Icc 1 M := filter_subset _ _
    have hAavoid := translatedPrimeOffsets_avoids (M := M) hRa
    have hcardA := hM0 M hM0Nat (translatedPrimeOffsets a M) hA hAavoid
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (Nat.one_lt_cast.mpr (le_trans (by norm_num) hy16))
    have hlogM := logM_ge_half_logy hy1 hlarge
    have hlogMpos : 0 < Real.log (M : ℝ) :=
      (half_pos hlogy).trans_le hlogM
    have hcardP : ((primeIco a M).card : ℝ) ≤
        3 * (M : ℝ) / Real.log (M : ℝ) + 1 := by
      have hcardCast : ((primeIco a M).card : ℝ) ≤
          ((translatedPrimeOffsets a M).card : ℝ) + 1 := by
        exact_mod_cast primeIco_card_le_offsets_add_one a M
      have hcapThree : ((translatedPrimeOffsets a M).card : ℝ) ≤
          3 * (M : ℝ) / Real.log (M : ℝ) := by
        simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using hcardA
      exact hcardCast.trans (_root_.add_le_add hcapThree le_rfl)
    have hcardP' : ((primeIco a M).card : ℝ) ≤
        6 * (M : ℝ) / Real.log (y : ℝ) + 1 := by
      have hmain : 3 * (M : ℝ) / Real.log (M : ℝ) ≤
          6 * (M : ℝ) / Real.log (y : ℝ) := by
        have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
        apply (div_le_iff₀ hlogMpos).2
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hlogy).2
        nlinarith
      exact hcardP.trans (_root_.add_le_add hmain le_rfl)
    have htwoYnonneg : 0 ≤ (2 : ℝ) / (y : ℝ) :=
      div_nonneg (by norm_num) hypos.le
    have hscaled := mul_le_mul_of_nonneg_right hcardP' htwoYnonneg
    have hsqrtLeY : Real.sqrt (y : ℝ) ≤ (y : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr (Nat.one_le_cast.mpr hy1))
    calc
      primeIcoReciprocal a M ≤
          (primeIco a M).card * (2 / (y : ℝ)) := hrecipCard
      _ ≤ (6 * (M : ℝ) / Real.log (y : ℝ) + 1) *
          (2 / (y : ℝ)) := hscaled
      _ = 12 * (M : ℝ) / ((y : ℝ) * Real.log (y : ℝ)) +
          2 / (y : ℝ) := by field_simp [hypos.ne', hlogy.ne']; ring
      _ ≤ 12 * (M : ℝ) / ((y : ℝ) * Real.log (y : ℝ)) +
          12 / Real.sqrt (y : ℝ) := by
        apply _root_.add_le_add le_rfl
        exact (div_le_div_of_nonneg_left (by norm_num) hsqrtPos hsqrtLeY).trans
          (div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 12)
            hsqrtPos.le)
  · have hMsmall : (M : ℝ) < Real.sqrt (y : ℝ) := lt_of_not_ge hlarge
    have hcard : (primeIco a M).card ≤ M := by
      have hsub : primeIco a M ⊆ Ico a (a + M) := filter_subset _ _
      have hc := card_le_card hsub
      rwa [Nat.card_Ico, Nat.add_sub_cancel_left] at hc
    have hcardR : ((primeIco a M).card : ℝ) ≤ M := Nat.cast_le.mpr hcard
    have hnonneg : 0 ≤ (2 : ℝ) / (y : ℝ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hcardR
      hnonneg
    have hsqrtSq : Real.sqrt (y : ℝ) * Real.sqrt (y : ℝ) = (y : ℝ) :=
      Real.mul_self_sqrt hypos.le
    have hsmall : (M : ℝ) * (2 / (y : ℝ)) ≤
        12 / Real.sqrt (y : ℝ) := by
      apply (le_div_iff₀ hsqrtPos).2
      have hrewrite :
          (M : ℝ) * (2 / (y : ℝ)) * Real.sqrt (y : ℝ) =
            (M : ℝ) * 2 / Real.sqrt (y : ℝ) := by
        field_simp [hypos.ne', hsqrtPos.ne'] <;>
          nlinarith [Real.sq_sqrt hypos.le]
      rw [hrewrite]
      apply (div_le_iff₀ hsqrtPos).2
      nlinarith
    exact hrecipCard.trans (hscaled.trans
      (hsmall.trans (_root_.le_add_of_nonneg_left
        (div_nonneg (by positivity)
          (mul_nonneg hypos.le (Real.log_nonneg
            (Nat.one_le_cast.mpr hy1)))))))

end

end PrimeGapNormality.Prime.CoreRoughPrimeBand
