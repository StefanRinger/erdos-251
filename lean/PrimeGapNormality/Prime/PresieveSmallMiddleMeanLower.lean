import PrimeGapNormality.Prime.PresieveSmallEarlyBrunScale
import PrimeGapNormality.Prime.PresieveSmallEarlyMiddleSplit

/-!
# A lower bound for the conditional middle-presieve mean

Each candidate avoids a uniform nonzero forbidden class with probability
at least `1 - 1/(p-1)`.  Candidates divisible by `p` survive automatically;
discarding that positive boost gives a valid lower bound for every fixed
early survivor set.  Independence gives the product bound, which is then
calibrated by the existing quantitative rooted Euler-product estimate.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

private theorem middle_local_mass_lower {S w : ℕ}
    (p : MiddlePrime w S) (n : ℕ) :
    1 - ((p.val : ℝ) - 1)⁻¹ ≤
      earlyPresieveOneLocalMass ⟨p.val, sdiff_subset p.property⟩ n := by
  let q := p.val - 1
  let bad := (univ : Finset (Fin q)).filter fun a => n % p.val = a.val + 1
  let good := (univ : Finset (Fin q)).filter fun a => n % p.val ≠ a.val + 1
  have hbad : bad.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Fin.ext
    omega
  have hsplit : bad.card + good.card = q := by
    simpa only [bad, good, card_univ, Fintype.card_fin] using
      (card_filter_add_card_filter_not (s := (univ : Finset (Fin q)))
        (fun a => n % p.val = a.val + 1))
  have hq : 0 < q := Nat.sub_pos_of_lt
    (Nat.prime_of_mem_primesLE (sdiff_subset p.property)).one_lt
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hgood : (q : ℝ) - 1 ≤ (good.card : ℝ) := by
    have hN : q ≤ good.card + 1 := by omega
    have hR : (q : ℝ) ≤ (good.card : ℝ) + 1 := by exact_mod_cast hN
    linarith
  rw [earlyPresieveOneLocalMass_eq_card]
  change 1 - ((p.val : ℝ) - 1)⁻¹ ≤ (good.card : ℝ) / q
  have hqeq : (q : ℝ) = (p.val : ℝ) - 1 := by
    dsimp only [q]
    rw [Nat.cast_sub (Nat.le_of_lt
      (Nat.prime_of_mem_primesLE (sdiff_subset p.property)).one_lt), Nat.cast_one]
  rw [← hqeq]
  apply (le_div_iff₀ hqR).mpr
  have heq : (1 - (q : ℝ)⁻¹) * q = (q : ℝ) - 1 := by
    field_simp [hqR.ne']
  rwa [heq]

/-- Exact product expression for the conditional mean.  No interval or
nondivisibility condition is imposed on the fixed candidate set. -/
theorem middlePresieveUniformMean_eq_sum_prod (S w : ℕ) (A : Finset ℕ) :
    middlePresieveUniformMean S w A =
      ∑ n ∈ A, ∏ p : MiddlePrime w S,
        earlyPresieveOneLocalMass ⟨p.val, sdiff_subset p.property⟩ n := by
  have hmass : ∀ υ : MiddleResidueChoice w S,
      (∏ p : MiddlePrime w S, uniformFin (υ p)) =
        (Fintype.card (MiddleResidueChoice w S) : ℝ)⁻¹ := by
    intro υ
    unfold uniformFin
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
    simp only [Fintype.card_fin]
  have hind : ∀ (υ : MiddleResidueChoice w S) (n : ℕ),
      (if ∀ p : MiddlePrime w S, n % p.val ≠ (υ p).val + 1 then (1 : ℝ) else 0) =
        ∏ p : MiddlePrime w S,
          earlyPresieveLocalIndicator ⟨p.val, sdiff_subset p.property⟩ n (υ p) := by
    intro υ n
    unfold earlyPresieveLocalIndicator
    rw [Fintype.prod_boole]
  have hweighted : middlePresieveUniformMean S w A =
      ∑ υ : MiddleResidueChoice w S,
        (∏ p : MiddlePrime w S, uniformFin (υ p)) *
          ((middlePresieveSurvivors S w A υ).card : ℝ) := by
    simp_rw [hmass]
    unfold middlePresieveUniformMean
    rw [div_eq_mul_inv, ← mul_sum, mul_comm]
  rw [hweighted]
  simp only [middlePresieveSurvivors, Finset.natCast_card_filter]
  simp_rw [mul_sum, hind]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  simp_rw [← Finset.prod_mul_distrib]
  unfold earlyPresieveOneLocalMass
  rw [Fintype.prod_sum]

/-- Every exposed candidate set has conditional mean at least its
cardinality times the rooted middle retention. -/
theorem middlePresieveUniformMean_ge_card_mul_rooted
    (S w : ℕ) (A : Finset ℕ) (hw : 2 ≤ w) :
    (A.card : ℝ) * rootedEulerProdNat w S ≤
      middlePresieveUniformMean S w A := by
  have hlocal0 : ∀ p : MiddlePrime w S,
      0 ≤ 1 - ((p.val : ℝ) - 1)⁻¹ := by
    intro p
    have hp := Nat.prime_of_mem_primesLE (sdiff_subset p.property)
    have hpR : (2 : ℝ) ≤ p.val := Nat.cast_le.mpr hp.two_le
    have hinv : ((p.val : ℝ) - 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  have hprod : ∀ n : ℕ, rootedEulerProdNat w S ≤
      ∏ p : MiddlePrime w S,
        earlyPresieveOneLocalMass ⟨p.val, sdiff_subset p.property⟩ n := by
    intro n
    have hbound := prod_le_prod (s := (univ : Finset (MiddlePrime w S))) (fun p _ => hlocal0 p)
      (fun p _ => middle_local_mass_lower p n)
    have heq : (∏ p : MiddlePrime w S, (1 - ((p.val : ℝ) - 1)⁻¹)) =
        rootedEulerProdNat w S := by
      exact Finset.prod_coe_sort (Nat.primesLE S \ Nat.primesLE w)
        (fun p : ℕ => 1 - ((p : ℝ) - 1)⁻¹)
    rw [heq] at hbound
    exact hbound
  rw [middlePresieveUniformMean_eq_sum_prod]
  calc
    (A.card : ℝ) * rootedEulerProdNat w S = ∑ _n ∈ A, rootedEulerProdNat w S := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum fun n _ => hprod n

/-- Quantitative Euler calibration for the conditional lower mean. -/
theorem middlePresieveUniformMean_ge_card_mul_euler
    (S w : ℕ) (A : Finset ℕ) (hw : 2 ≤ w) (hwS : w ≤ S) :
    (A.card : ℝ) * ((1 - 4 / w) * (eulerProdNat S / eulerProdNat w)) ≤
      middlePresieveUniformMean S w A := by
  have hrel := (abs_le.mp (rootedEulerProdNat_rel_div hw hwS)).1
  have hroot : (1 - 4 / (w : ℝ)) * (eulerProdNat S / eulerProdNat w) ≤
      rootedEulerProdNat w S := by nlinarith
  exact (mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg A.card)).trans
    (middlePresieveUniformMean_ge_card_mul_rooted S w A hw)

/-- The early cutoff lies below the full small window eventually. -/
theorem eventually_presieveW_le_ahlSmall_window {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, presieveW (windowG X) ≤ ahlSmall_window κ X := by
  have hlogpow : Tendsto (fun G : ℝ => Real.log G ^ (4 : ℕ) / G)
      atTop (nhds 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp
      Real.tendsto_log_atTop
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with G hG
    simp only [Function.comp_apply, Real.exp_neg, Real.exp_log hG, div_eq_mul_inv]
  filter_upwards [(hlogpow.comp tendsto_windowG_atTop).eventually (gt_mem_nhds zero_lt_one),
    eventually_windowG_le_ahlSmall_window hκ,
    tendsto_windowG_atTop.eventually_ge_atTop 1] with X hsmall hS hG
  have hGpos : 0 < windowG X := zero_lt_one.trans_le hG
  have hpow : Real.log (windowG X) ^ (4 : ℕ) ≤ windowG X := by
    have h := (div_lt_iff₀ hGpos).mp hsmall
    simpa only [one_mul] using h.le
  have hw : (presieveW (windowG X) : ℝ) ≤ Real.log (windowG X) ^ (4 : ℕ) := by
    rw [presieveW_eq]
    exact Nat.floor_le (by positivity)
  exact_mod_cast hw.trans (hpow.trans hS)

/-- The conditional middle mean has the required main-term lower bound
uniformly in every early residue fibre. -/
theorem eventually_middlePresieveUniformMean_ge_main
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ X : ℕ in atTop,
      ∀ τ : ResidueChoice (presieveW (windowG X)),
        (1 - ε) * ((ahlSmall_window κ X : ℝ) * eulerProdNat (ahlSmall_window κ X)) ≤
          middlePresieveUniformMean (ahlSmall_window κ X) (presieveW (windowG X))
            (earlyPresieveSurvivors (ahlSmall_window κ X) (presieveW (windowG X)) τ) := by
  have hδ : 0 < ε / 3 := by positivity
  have htail : Tendsto (fun X : ℕ => (4 : ℝ) / presieveW (windowG X))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).comp tendsto_presieveW_windowG_atTop
  filter_upwards [eventually_earlyPresieve_survivorCount_relative_error_lt hκ hδ,
    htail.eventually (gt_mem_nhds hδ),
    eventually_presieveW_le_ahlSmall_window hκ,
    tendsto_presieveW_windowG_atTop.eventually_ge_atTop 2] with X hcount htail hwS hw
  intro τ
  let S := ahlSmall_window κ X
  let w := presieveW (windowG X)
  let A := earlyPresieveSurvivors S w τ
  have hVw : 0 < eulerProdNat w := eulerProdNat_pos _
  have hVS : 0 < eulerProdNat S := eulerProdNat_pos _
  have hδ1 : 0 ≤ 1 - ε / 3 := by linarith
  have hA : (1 - ε / 3) * ((S : ℝ) * eulerProdNat w) ≤ (A.card : ℝ) := by
    have h := (abs_lt.mp (hcount τ)).1
    dsimp only [A, S, w]
    nlinarith
  have hroot : (1 - ε / 3) * (eulerProdNat S / eulerProdNat w) ≤
      rootedEulerProdNat w S := by
    have h := (abs_le.mp (rootedEulerProdNat_rel_div hw hwS)).1
    have hq : 0 ≤ eulerProdNat S / eulerProdNat w := div_nonneg hVS.le hVw.le
    have hmul := mul_le_mul_of_nonneg_right htail.le hq
    dsimp only [w, S] at hq ⊢
    nlinarith
  have hbound := mul_le_mul hA hroot
    (mul_nonneg hδ1 (div_nonneg hVS.le hVw.le)) (Nat.cast_nonneg A.card)
  have heq :
      ((1 - ε / 3) * ((S : ℝ) * eulerProdNat w)) *
          ((1 - ε / 3) * (eulerProdNat S / eulerProdNat w)) =
        ((1 - ε / 3) * (1 - ε / 3)) * ((S : ℝ) * eulerProdNat S) := by
    field_simp [hVw.ne'] <;> ring
  rw [heq] at hbound
  have hcoef : 1 - ε ≤ (1 - ε / 3) * (1 - ε / 3) := by nlinarith
  exact (mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (Nat.cast_nonneg S) hVS.le)).trans
      (hbound.trans (middlePresieveUniformMean_ge_card_mul_rooted S w A hw))

end

end PrimeGapNormality.Prime
