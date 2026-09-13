import PrimeGapNormality.Prime.CorePresieveCountRate
import PrimeGapNormality.Prime.PresieveSmallEarlyOffDiagonal

/-! Uniform upper conditional mean for the genuine rooted presieve.
The automatic survival of a candidate divisible by a middle prime is paid
by an additive 2S/w budget, before any early residue fibre is averaged.
-/
namespace PrimeGapNormality.Prime.CorePresieveTwoSided
open Finset Filter CorePresieveGlobalCountLimit
open scoped Topology Classical
noncomputable section

theorem prod_difference_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hab : ∀ i ∈ s, a i ≤ b i) (hb : ∀ i ∈ s, b i ≤ 1) :
    (∏ i ∈ s, b i) - (∏ i ∈ s, a i) ≤ ∑ i ∈ s, (b i - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (mem_insert_self _ _)
    have habi := hab i (mem_insert_self _ _)
    have hbi := hb i (mem_insert_self _ _)
    have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (mem_insert_of_mem hj)
    have habs : ∀ j ∈ s, a j ≤ b j := fun j hj => hab j (mem_insert_of_mem hj)
    have hbs : ∀ j ∈ s, b j ≤ 1 := fun j hj => hb j (mem_insert_of_mem hj)
    have hprod : (∏ j ∈ s, b j) ≤ 1 := prod_le_one
      (fun j hj => (has j hj).trans (habs j hj)) hbs
    have hsum : 0 ≤ ∑ j ∈ s, (b j - a j) :=
      sum_nonneg fun j hj => sub_nonneg.mpr (habs j hj)
    have h1 := mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr habi)
    have h2 := mul_le_mul_of_nonneg_left (ih has habs hbs) hai
    have h3 := mul_le_mul_of_nonneg_right (habi.trans hbi) hsum
    rw [prod_insert hi, prod_insert hi, sum_insert hi]
    nlinarith only [h1, h2, h3]

theorem local_mass_eq {S : ℕ} (p : SievePrime S) (n : ℕ) :
    earlyPresieveOneLocalMass p n =
      (1 - ((p.val : ℝ) - 1)⁻¹) +
        (if p.val ∣ n then ((p.val : ℝ) - 1)⁻¹ else 0) := by
  rw [← earlyPresievePairLocalMass_self p n,
    earlyPresievePairLocalMass_eq_rooted_cases]
  have hp := Nat.prime_of_mem_primesLE p.property
  have hpR : (1 : ℝ) < p.val := Nat.one_lt_cast.mpr hp.one_lt
  by_cases hd : p.val ∣ n
  · simp only [Nat.dvd_iff_mod_eq_zero.mp hd, if_true, if_pos hd]
    ring
  · have hn : n % p.val ≠ 0 := fun h => hd (Nat.dvd_iff_mod_eq_zero.mpr h)
    simp only [hn, if_false, if_true, if_neg hd, add_zero]
    rw [Nat.cast_sub hp.two_le, Nat.cast_sub hp.one_le]
    push_cast
    field_simp [show (p.val : ℝ) - 1 ≠ 0 by linarith]
    ring

theorem middle_product_upper (S w : ℕ) (hw : 2 ≤ w) (n : ℕ) :
    (∏ p : MiddlePrime w S,
      earlyPresieveOneLocalMass ⟨p.val, sdiff_subset p.property⟩ n) ≤
      rootedEulerProdNat w S +
        ∑ p : MiddlePrime w S,
          if p.val ∣ n then ((p.val : ℝ) - 1)⁻¹ else 0 := by
  let a := fun p : MiddlePrime w S => 1 - ((p.val : ℝ) - 1)⁻¹
  let b := fun p : MiddlePrime w S =>
    earlyPresieveOneLocalMass ⟨p.val, sdiff_subset p.property⟩ n
  have ha : ∀ p : MiddlePrime w S, 0 ≤ a p := by
    intro p
    have hp : (2 : ℝ) ≤ p.val := Nat.cast_le.mpr
      (Nat.prime_of_mem_primesLE (sdiff_subset p.property)).two_le
    have h1 : ((p.val : ℝ) - 1)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 (by linarith)
    dsimp [a]
    linarith
  have heq (p : MiddlePrime w S) : b p - a p =
      if p.val ∣ n then ((p.val : ℝ) - 1)⁻¹ else 0 := by
    dsimp [b, a]
    rw [local_mass_eq]
    ring
  have hab : ∀ p : MiddlePrime w S, a p ≤ b p := by
    intro p
    have hp : (1 : ℝ) < p.val := Nat.one_lt_cast.mpr
      (Nat.prime_of_mem_primesLE (sdiff_subset p.property)).one_lt
    have hh : 0 ≤ b p - a p := by rw [heq]; split_ifs <;> positivity
    linarith
  have hh := prod_difference_le_sum univ a b (fun p _ => ha p)
    (fun p _ => hab p) (fun p _ => earlyPresieveOneLocalMass_le_one _ n)
  have hprod : (∏ p : MiddlePrime w S, a p) = rootedEulerProdNat w S := by
    dsimp only [a]
    exact Finset.prod_coe_sort (Nat.primesLE S \ Nat.primesLE w)
      (fun p : ℕ => 1 - ((p : ℝ) - 1)⁻¹)
  simp_rw [heq] at hh
  rw [hprod] at hh
  dsimp only [b] at hh
  linarith

theorem divisor_boost_sum_le (S w : ℕ) (hw : 1 ≤ w) {A : Finset ℕ}
    (hA : A ⊆ Icc 1 S) :
    (∑ n ∈ A, ∑ p : MiddlePrime w S,
      if p.val ∣ n then ((p.val : ℝ) - 1)⁻¹ else 0) ≤ 2 * (S : ℝ) / w := by
  rw [sum_comm]
  have hpoint (p : MiddlePrime w S) :
      (∑ n ∈ A, if p.val ∣ n then ((p.val : ℝ) - 1)⁻¹ else 0) ≤
        2 * (S : ℝ) * ((p.val : ℝ)⁻¹) ^ 2 := by
    have hp := Nat.prime_of_mem_primesLE (sdiff_subset p.property)
    have hp0 : (0 : ℝ) < p.val := Nat.cast_pos.mpr hp.pos
    have hp2 : (2 : ℝ) ≤ p.val := Nat.cast_le.mpr hp.two_le
    have hcard : ((A.filter (fun n => p.val ∣ n)).card : ℝ) ≤ (S : ℝ) / p.val := by
      have hs : A.filter (fun n => p.val ∣ n) ⊆
          (Icc 1 S).filter (fun n => p.val ∣ n) := filter_subset_filter _ hA
      have hi : Icc 1 S = Ioc 0 S := by ext n; simp only [mem_Icc, mem_Ioc]; omega
      have hc := Nat.cast_le (α := ℝ).mpr (card_le_card hs)
      rw [hi, Nat.Ioc_filter_dvd_card_eq_div] at hc
      exact hc.trans Nat.cast_div_le
    have hinv : ((p.val : ℝ) - 1)⁻¹ ≤ 2 / p.val := by
      apply (inv_le_iff_one_le_mul₀ (by linarith : (0 : ℝ) < (p.val : ℝ) - 1)).2
      rw [show (2 / (p.val : ℝ)) * ((p.val : ℝ) - 1) =
        (2 * ((p.val : ℝ) - 1)) / p.val by ring]
      apply (le_div_iff₀ hp0).2
      linarith
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    calc
      _ ≤ ((S : ℝ) / p.val) * (2 / p.val) :=
        mul_le_mul hcard hinv (inv_nonneg.mpr (by linarith))
          (div_nonneg (Nat.cast_nonneg S) hp0.le)
      _ = _ := by ring
  have htail : (∑ p : MiddlePrime w S, ((p.val : ℝ)⁻¹) ^ 2) ≤ (w : ℝ)⁻¹ := by
    have heq : (∑ p : MiddlePrime w S, ((p.val : ℝ)⁻¹) ^ 2) =
        ∑ p ∈ Nat.primesLE S \ Nat.primesLE w, ((p : ℝ)⁻¹) ^ 2 :=
      Finset.sum_coe_sort (Nat.primesLE S \ Nat.primesLE w)
        (fun p : ℕ => ((p : ℝ)⁻¹) ^ 2)
    rw [heq]
    exact (sum_le_sum_of_subset_of_nonneg (primesLE_sdiff_subset_Icc w S)
      (fun n _ _ => sq_nonneg ((n : ℝ)⁻¹))).trans (sum_inv_sq_Icc_succ_le hw)
  exact (sum_le_sum (fun p _ => hpoint p)).trans (by
    rw [← mul_sum]
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left htail (by positivity : (0 : ℝ) ≤ 2 * S))

theorem middle_mean_upper (S w : ℕ) (hw : 2 ≤ w) {A : Finset ℕ}
    (hA : A ⊆ Icc 1 S) :
    middlePresieveUniformMean S w A ≤
      (A.card : ℝ) * rootedEulerProdNat w S + 2 * (S : ℝ) / w := by
  rw [middlePresieveUniformMean_eq_sum_prod]
  have hh := sum_le_sum (fun n (_ : n ∈ A) => middle_product_upper S w hw n)
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hh
  exact hh.trans (add_le_add le_rfl (divisor_boost_sum_le S w (by omega) hA))

theorem tendsto_middle_boost_zero :
    Tendsto (fun S : ℕ => 2 / ((early S : ℝ) * eulerProdNat S)) atTop (𝓝 0) := by
  have hlarge : Tendsto (fun S : ℕ => (early S : ℝ) * eulerProdNat S) atTop atTop := by
    apply tendsto_atTop_mono (fun S => ?_) tendsto_early_mul_euler_sq_atTop
    have hV0 := (eulerProdNat_pos S).le
    have hV1 : eulerProdNat S ≤ 1 := by
      have hzero : eulerProdNat 0 = 1 := by
        rw [eulerProdNat, Nat.primesLE_zero, prod_empty]
      exact (eulerProdNat_mono (Nat.zero_le S)).trans_eq hzero
    exact mul_le_mul_of_nonneg_left (by nlinarith : eulerProdNat S ^ 2 ≤ eulerProdNat S)
      (Nat.cast_nonneg _)
  have hh := (tendsto_inv_atTop_zero.comp hlarge).const_mul (2 : ℝ)
  simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using hh

/-- Both sides of the conditional mean are located at SV(S), uniformly
over every exposed early residue fibre, before the tail test is chosen. -/
theorem eventually_middle_mean_abs_sub {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ S : ℕ in atTop, ∀ τ : ResidueChoice (early S),
      |middlePresieveUniformMean S (early S)
          (earlyPresieveSurvivors S (early S) τ) -
        (S : ℝ) * eulerProdNat S| ≤ ε * ((S : ℝ) * eulerProdNat S) := by
  have hδ : 0 < ε / 4 := by positivity
  have hroot := (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).comp tendsto_early_atTop
  filter_upwards [eventually_middle_mean_ge hε hε1,
    eventually_early_relative_error hδ,
    (tendsto_order.mp hroot).2 (ε / 4) hδ,
    (tendsto_order.mp tendsto_middle_boost_zero).2 (ε / 4) hδ,
    eventually_early_le_window, tendsto_early_atTop.eventually_ge_atTop 2]
    with S hlo hearly hroot hboost hwS hw
  intro τ
  apply abs_le.mpr
  constructor
  · have hh := hlo τ
    linarith
  · let A := earlyPresieveSurvivors S (early S) τ
    let V : ℝ := (S : ℝ) * eulerProdNat S
    have hVw := eulerProdNat_pos (early S)
    have hVS := eulerProdNat_pos S
    have hA : (A.card : ℝ) ≤ (1 + ε / 4) * ((S : ℝ) * eulerProdNat (early S)) := by
      have hh := (abs_lt.mp (hearly τ)).2
      dsimp [A]
      linarith
    have hratio : 0 ≤ eulerProdNat S / eulerProdNat (early S) := by positivity
    have hrootU : rootedEulerProdNat (early S) S ≤
        (1 + ε / 4) * (eulerProdNat S / eulerProdNat (early S)) := by
      have hh := (abs_le.mp (rootedEulerProdNat_rel_div hw hwS)).2
      have hscale := mul_le_mul_of_nonneg_right hroot.le hratio
      change 4 / (early S : ℝ) * (eulerProdNat S / eulerProdNat (early S)) ≤
        (ε / 4) * (eulerProdNat S / eulerProdNat (early S)) at hscale
      nlinarith only [hh, hscale]
    have hp := mul_le_mul hA hrootU (rootedEulerProdNat_pos hw).le (by positivity)
    have hmul : ((1 + ε / 4) * ((S : ℝ) * eulerProdNat (early S))) *
        ((1 + ε / 4) * (eulerProdNat S / eulerProdNat (early S))) =
        (1 + ε / 4) ^ 2 * V := by dsimp [V]; field_simp [hVw.ne'] <;> ring
    rw [hmul] at hp
    have hboostU : 2 * (S : ℝ) / early S ≤ (ε / 4) * V := by
      have hh := mul_le_mul_of_nonneg_right hboost.le
        (show 0 ≤ V from mul_nonneg (Nat.cast_nonneg _) hVS.le)
      have hcancel : (2 / ((early S : ℝ) * eulerProdNat S)) * V =
          2 * (S : ℝ) / early S := by
        dsimp [V]
        field_simp [hVS.ne', Nat.cast_ne_zero.mpr (by omega : early S ≠ 0)] <;> ring
      rwa [hcancel] at hh
    have hmean := middle_mean_upper S (early S) hw
      (earlyPresieveSurvivors_subset_Icc S (early S) τ)
    have hcoef : (1 + ε / 4) ^ 2 + ε / 4 ≤ 1 + ε := by nlinarith
    have hfinal := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ V from mul_nonneg (Nat.cast_nonneg _) hVS.le)
    change middlePresieveUniformMean S (early S) A - V ≤ ε * V
    nlinarith only [hmean, hp, hboostU, hfinal]

theorem eventually_middle_mean_abs_sub_any {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℕ in atTop, ∀ τ : ResidueChoice (early S),
      |middlePresieveUniformMean S (early S)
          (earlyPresieveSurvivors S (early S) τ) -
        (S : ℝ) * eulerProdNat S| ≤ ε * ((S : ℝ) * eulerProdNat S) := by
  filter_upwards [eventually_middle_mean_abs_sub
    (lt_min hε zero_lt_one) (min_le_right ε 1)] with S hS
  intro τ
  exact (hS τ).trans (mul_le_mul_of_nonneg_right (min_le_left ε 1)
    (mul_nonneg (Nat.cast_nonneg _) (eulerProdNat_pos S).le))

end
end PrimeGapNormality.Prime.CorePresieveTwoSided
