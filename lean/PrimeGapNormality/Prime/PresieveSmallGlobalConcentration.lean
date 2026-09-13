import PrimeGapNormality.Prime.PresieveSmallMiddleMeanLower

/-!
# Global lower-tail concentration after exposing the early primes

The middle primes satisfy `p ≤ S`, so their squared sensitivities sum
to at most `16 S²/w`.  The exact early/middle product decomposition
then averages the conditional tail bound over the exposed fibres.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

theorem middleWidthSq_nonneg (S w : ℕ) : 0 ≤ middleWidthSq S w := by
  exact sum_nonneg fun _ _ => sq_nonneg _

/-- Using `p ≤ S` absorbs the `+1` in each sensitivity without a
logarithmic remainder. -/
theorem middleWidthSq_le (S w : ℕ) (hw : 1 ≤ w) :
    middleWidthSq S w ≤ 16 * (S : ℝ) ^ 2 / w := by
  have hsum : middleWidthSq S w =
      ∑ p ∈ Nat.primesLE S \ Nat.primesLE w, residueWidth (S : ℝ) p ^ 2 := by
    unfold middleWidthSq
    exact Finset.sum_coe_sort (Nat.primesLE S \ Nat.primesLE w)
      (fun p : ℕ => residueWidth (S : ℝ) (p : ℝ) ^ 2)
  rw [hsum]
  have hpoint : ∀ p ∈ Nat.primesLE S \ Nat.primesLE w,
      residueWidth (S : ℝ) p ^ 2 ≤ 16 * (S : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 2 := by
    intro p hp
    have hpprime := Nat.prime_of_mem_primesLE (sdiff_subset hp)
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpprime.pos
    have hpS : (p : ℝ) ≤ S := Nat.cast_le.mpr (Nat.le_of_mem_primesLE (sdiff_subset hp))
    have hratio : (1 : ℝ) ≤ (S : ℝ) / p := (one_le_div hp0).mpr hpS
    rw [residueWidth_sq]
    have hsq : ((S : ℝ) / p + 1) ^ 2 ≤ (2 * ((S : ℝ) / p)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    calc
      4 * ((S : ℝ) / p + 1) ^ 2 ≤ 4 * (2 * ((S : ℝ) / p)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 16 * (S : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 2 := by
        rw [div_eq_mul_inv]
        ring
  have htail : ∑ p ∈ Nat.primesLE S \ Nat.primesLE w, ((p : ℝ)⁻¹) ^ 2 ≤ (w : ℝ)⁻¹ := by
    exact (sum_le_sum_of_subset_of_nonneg (primesLE_sdiff_subset_Icc w S)
      (fun n _ _ => sq_nonneg ((n : ℝ)⁻¹))).trans
        (sum_inv_sq_Icc_succ_le hw)
  calc
    ∑ p ∈ Nat.primesLE S \ Nat.primesLE w, residueWidth (S : ℝ) p ^ 2 ≤
        ∑ p ∈ Nat.primesLE S \ Nat.primesLE w,
          16 * (S : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 2 := sum_le_sum hpoint
    _ = 16 * (S : ℝ) ^ 2 *
        ∑ p ∈ Nat.primesLE S \ Nat.primesLE w, ((p : ℝ)⁻¹) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ 16 * (S : ℝ) ^ 2 * (w : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 16 * (S : ℝ) ^ 2 / w := (div_eq_mul_inv _ _).symm

private theorem exp_neg_div_le_div {u W : ℝ} (hu : 0 < u) (hW : 0 < W) :
    Real.exp (-u ^ 2 / W) ≤ W / u ^ 2 := by
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
  have hx : 0 < u ^ 2 / W := div_pos hu2 hW
  have hle : u ^ 2 / W ≤ Real.exp (u ^ 2 / W) := by
    linarith [Real.add_one_le_exp (u ^ 2 / W)]
  have h := one_div_le_one_div_of_le hx hle
  simpa only [one_div, ← Real.exp_neg, inv_div, neg_div] using h

/-- The conditional exponential bound also gives the convenient
second-moment-shaped bound `width/u²`, including the zero-width case. -/
theorem middlePresieve_uniform_lowerTail_le_width_div_sq
    (S w : ℕ) {A : Finset ℕ} (hA : A ⊆ Icc 1 S) {u : ℝ} (hu : 0 < u) :
    (((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
        u ≤ middlePresieveUniformMean S w A -
          ((middlePresieveSurvivors S w A υ).card : ℝ)).card : ℝ) /
        (Fintype.card (MiddleResidueChoice w S) : ℝ) ≤
      middleWidthSq S w / u ^ 2 := by
  have h := middlePresieve_uniform_lowerTail S w hA hu
  by_cases hW : middleWidthSq S w = 0
  · simpa only [hW, if_true, zero_div] using h
  · rw [if_neg hW] at h
    exact h.trans (exp_neg_div_le_div hu
      (lt_of_le_of_ne (middleWidthSq_nonneg S w) (Ne.symm hW)))

/-- Uniform mass of a low full-presieve survivor count. -/
def presieveSmallGlobalLowerMass (S : ℕ) (a : ℝ) : ℝ :=
  (((univ : Finset (ResidueChoice S)).filter fun σ =>
      ((presieveSurvivors S σ).card : ℝ) < a).card : ℝ) /
    (Fintype.card (ResidueChoice S) : ℝ)

theorem presieveSmallGlobalLowerMass_nonneg (S : ℕ) (a : ℝ) :
    0 ≤ presieveSmallGlobalLowerMass S a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Aggregate the conditional lower-tail bound over the exact uniform
early/middle product.  The mean hypothesis is explicit and finite. -/
theorem presieveSmallGlobalLowerMass_le_of_mean
    (S w : ℕ) (hwS : w ≤ S) {a u : ℝ} (hu : 0 < u)
    (hmean : ∀ τ : ResidueChoice w,
      a + u ≤ middlePresieveUniformMean S w (earlyPresieveSurvivors S w τ)) :
    presieveSmallGlobalLowerMass S a ≤ middleWidthSq S w / u ^ 2 := by
  let B := middleWidthSq S w / u ^ 2
  have hCearly : (0 : ℝ) < Fintype.card (ResidueChoice w) :=
    Nat.cast_pos.mpr (residueChoice_card_pos w)
  have hCmiddle : (0 : ℝ) < Fintype.card (MiddleResidueChoice w S) := by
    have hnat : 0 < Fintype.card (MiddleResidueChoice w S) := by
      rw [Fintype.card_pi]
      exact prod_pos fun p _ => by
        rw [Fintype.card_fin]
        exact Nat.sub_pos_of_lt
          (Nat.prime_of_mem_primesLE (sdiff_subset p.property)).one_lt
    exact Nat.cast_pos.mpr hnat
  have hpoint : ∀ τ : ResidueChoice w,
      (((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
        ((presieveSurvivors S (earlyMiddleGlue w S hwS τ υ)).card : ℝ) < a).card : ℝ) ≤
      (Fintype.card (MiddleResidueChoice w S) : ℝ) * B := by
    intro τ
    have hsub :
        ((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
          ((presieveSurvivors S (earlyMiddleGlue w S hwS τ υ)).card : ℝ) < a) ⊆
        ((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
          u ≤ middlePresieveUniformMean S w (earlyPresieveSurvivors S w τ) -
            ((middlePresieveSurvivors S w (earlyPresieveSurvivors S w τ) υ).card : ℝ)) := by
      intro υ hυ
      have hlow := (mem_filter.mp hυ).2
      rw [presieveSurvivors_earlyMiddleGlue] at hlow
      exact mem_filter.mpr ⟨mem_univ _, by linarith [hmean τ]⟩
    have htail := middlePresieve_uniform_lowerTail_le_width_div_sq S w
      (earlyPresieveSurvivors_subset_Icc S w τ) hu
    have hcount := (div_le_iff₀ hCmiddle).mp htail
    exact (Nat.cast_le.mpr (card_le_card hsub)).trans (by
      simpa only [B, mul_comm] using hcount)
  unfold presieveSmallGlobalLowerMass
  rw [earlyMiddle_card_filter_eq_sum w S hwS,
    earlyMiddle_residueChoice_card w S hwS, Nat.cast_mul, Nat.cast_sum]
  apply (div_le_iff₀ (mul_pos hCearly hCmiddle)).mpr
  calc
    _ ≤ ∑ _τ : ResidueChoice w,
        (Fintype.card (MiddleResidueChoice w S) : ℝ) * B :=
      sum_le_sum fun τ _ => hpoint τ
    _ = _ := by
      rw [sum_const, card_univ, nsmul_eq_mul]
      dsimp only [B]
      ring

private theorem eventually_log_ahlSmall_window_le {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (ahlSmall_window κ X : ℝ) ≤
        (Real.log (3 * (κ + 1)) + 2) * Real.log (windowG X) := by
  filter_upwards [tendsto_windowG_atTop.eventually_ge_atTop (Real.exp 1),
    (tendsto_ahlSmall_window_atTop hκ).eventually_ge_atTop 1] with X hG hS
  let G := windowG X
  have hGpos : 0 < G := (Real.exp_pos 1).trans_le hG
  have ht : 1 ≤ Real.log G := by
    simpa using Real.log_le_log (Real.exp_pos 1) hG
  have hG1 : 1 ≤ G := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hG
  have hx : 0 ≤ κ * Real.log G := mul_nonneg hκ.le (zero_le_one.trans ht)
  have hsqrt : Real.sqrt (κ * Real.log G) ≤ κ * Real.log G + 1 := by
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg (κ * Real.log G),
      sq_nonneg (κ * Real.log G)]
  have hceil : (profileL κ X : ℝ) ≤
      κ * Real.log G + Real.sqrt (κ * Real.log G) + 1 :=
    (Nat.ceil_lt_add_one (add_nonneg hx (Real.sqrt_nonneg _))).le
  have hlogG : Real.log G ≤ G := (Real.log_le_sub_one_of_pos hGpos).trans (by linarith)
  have hκlog := mul_le_mul_of_nonneg_left hlogG hκ.le
  have hL : (profileL κ X : ℝ) ≤ 2 * (κ + 1) * G := by nlinarith
  have hfloor : (ahlSmall_window κ X : ℝ) ≤
      (6 / 5 : ℝ) * (profileL κ X : ℝ) * G := by
    rw [ahlSmall_window_eq]
    exact Nat.floor_le (by positivity)
  have hSup : (ahlSmall_window κ X : ℝ) ≤ (3 * (κ + 1)) * G ^ 2 := by
    calc
      (ahlSmall_window κ X : ℝ) ≤ (6 / 5 : ℝ) * (profileL κ X : ℝ) * G := hfloor
      _ ≤ (6 / 5 : ℝ) * (2 * (κ + 1) * G) * G :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL (by norm_num)) hGpos.le
      _ ≤ (3 * (κ + 1)) * G ^ 2 := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ κ + 1) (sq_nonneg G)]
  have hCpos : 0 < 3 * (κ + 1) := by positivity
  have hClog : 0 ≤ Real.log (3 * (κ + 1)) := Real.log_nonneg (by linarith)
  calc
    Real.log (ahlSmall_window κ X : ℝ) ≤ Real.log ((3 * (κ + 1)) * G ^ 2) :=
      Real.log_le_log (Nat.cast_pos.mpr hS) hSup
    _ = Real.log (3 * (κ + 1)) + 2 * Real.log G := by
      rw [Real.log_mul hCpos.ne' (pow_ne_zero _ hGpos.ne'), Real.log_pow]
      norm_num
    _ ≤ (Real.log (3 * (κ + 1)) + 2) * Real.log G := by
      nlinarith [mul_nonneg hClog (sub_nonneg.mpr ht)]

/-- The reciprocal variance scale vanishes with the canonical early
cutoff.  Only the weak Mertens lower bound is needed. -/
theorem tendsto_presieveW_mul_eulerProd_sq_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ => (presieveW (windowG X) : ℝ) *
      eulerProdNat (ahlSmall_window κ X) ^ 2) atTop atTop := by
  let C := Real.log (3 * (κ + 1)) + 2
  have hClog : 0 ≤ Real.log (3 * (κ + 1)) := Real.log_nonneg (by linarith)
  have hC : 0 < C := by dsimp only [C]; linarith
  have hc : 0 < eulerProdLowerConst := eulerProdLowerConst_pos
  let K := eulerProdLowerConst ^ 2 / (2 * C ^ 2)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hlim : Tendsto (fun X : ℕ => K * Real.log (windowG X) ^ (2 : ℕ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hK).mpr
      ((tendsto_pow_atTop (by omega : (2 : ℕ) ≠ 0)).comp
        (Real.tendsto_log_atTop.comp tendsto_windowG_atTop))
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_log_ahlSmall_window_le hκ,
    (tendsto_ahlSmall_window_atTop hκ).eventually_ge_atTop 16,
    (Real.tendsto_log_atTop.comp tendsto_windowG_atTop).eventually_ge_atTop 2] with X hlogS hS ht
  let t := Real.log (windowG X)
  let S := ahlSmall_window κ X
  let w := presieveW (windowG X)
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have ht4 : (2 : ℝ) ≤ t ^ (4 : ℕ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ht 4
    norm_num at h
    linarith
  have hw : t ^ (4 : ℕ) / 2 ≤ (w : ℝ) := by
    have hf : t ^ (4 : ℕ) < (w : ℝ) + 1 := by
      simpa only [w, presieveW_eq, t] using Nat.lt_floor_add_one (t ^ (4 : ℕ))
    linarith
  have hlogpos : 0 < Real.log (S : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (by omega))
  have hden : 0 < C * t := mul_pos hC htpos
  have hV : eulerProdLowerConst / (C * t) ≤ eulerProdNat S := by
    exact (div_le_div_of_nonneg_left hc.le hlogpos hlogS).trans
      (eulerProdNat_ge_mul_inv_log hS)
  have hV0 : 0 ≤ eulerProdLowerConst / (C * t) := div_nonneg hc.le hden.le
  have hmul := mul_le_mul hw (pow_le_pow_left₀ hV0 hV 2)
    (sq_nonneg _) (Nat.cast_nonneg w)
  have heq : (t ^ (4 : ℕ) / 2) * (eulerProdLowerConst / (C * t)) ^ 2 = K * t ^ 2 := by
    dsimp only [K]
    field_simp [hC.ne', htpos.ne'] <;> ring
  rw [heq] at hmul
  exact hmul

theorem tendsto_inv_presieveW_mul_eulerProd_sq {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ => ((presieveW (windowG X) : ℝ) *
      eulerProdNat (ahlSmall_window κ X) ^ 2)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_presieveW_mul_eulerProd_sq_atTop hκ)

/-- Concrete global lower-tail concentration for the small window,
after averaging over every rooted residue choice through `S`. -/
theorem tendsto_presieveSmallGlobalLowerMass {κ ε : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Tendsto (fun X : ℕ => presieveSmallGlobalLowerMass (ahlSmall_window κ X)
      ((1 - ε) * ((ahlSmall_window κ X : ℝ) * eulerProdNat (ahlSmall_window κ X))))
      atTop (nhds 0) := by
  have hlim : Tendsto (fun X : ℕ => (64 / ε ^ 2 : ℝ) *
      ((presieveW (windowG X) : ℝ) * eulerProdNat (ahlSmall_window κ X) ^ 2)⁻¹)
      atTop (nhds 0) := by
    simpa using (tendsto_inv_presieveW_mul_eulerProd_sq hκ).const_mul (64 / ε ^ 2)
  refine squeeze_zero' (Eventually.of_forall fun X => presieveSmallGlobalLowerMass_nonneg _ _) ?_ hlim
  filter_upwards [eventually_middlePresieveUniformMean_ge_main hκ
      (by positivity : 0 < ε / 2) (by linarith : ε / 2 ≤ 1),
    eventually_presieveW_le_ahlSmall_window hκ,
    tendsto_presieveW_windowG_atTop.eventually_ge_atTop 1,
    (tendsto_ahlSmall_window_atTop hκ).eventually_ge_atTop 1] with X hmean hwS hw hS
  let S := ahlSmall_window κ X
  let w := presieveW (windowG X)
  let M := (S : ℝ) * eulerProdNat S
  have hSpos : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hVpos : 0 < eulerProdNat S := eulerProdNat_pos S
  have hM : 0 < M := mul_pos hSpos hVpos
  have hu : 0 < (ε / 2) * M := mul_pos (by positivity) hM
  have hm : ∀ τ : ResidueChoice w,
      (1 - ε) * M + (ε / 2) * M ≤
        middlePresieveUniformMean S w (earlyPresieveSurvivors S w τ) := by
    intro τ
    convert hmean τ using 1 <;> dsimp only [M, S, w] <;> ring
  have hmass := presieveSmallGlobalLowerMass_le_of_mean S w hwS hu hm
  have hwidth := div_le_div_of_nonneg_right (middleWidthSq_le S w hw) (sq_nonneg ((ε / 2) * M))
  have heq : (16 * (S : ℝ) ^ 2 / w) / ((ε / 2) * M) ^ 2 =
      (64 / ε ^ 2 : ℝ) * ((w : ℝ) * eulerProdNat S ^ 2)⁻¹ := by
    have hwpos : (0 : ℝ) < w := Nat.cast_pos.mpr hw
    dsimp only [M]
    field_simp [hε.ne', hSpos.ne', hVpos.ne', hwpos.ne'] <;> ring
  rw [heq] at hwidth
  exact hmass.trans hwidth

end

end PrimeGapNormality.Prime
