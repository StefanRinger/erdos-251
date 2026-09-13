import PrimeGapNormality.Prime.CorePresieveTwoSidedMean

/-! Public bounded-difference interface for the actual middle survivor count.
The elementary finite proof is copied from the existing private proof in
PresieveSmallEarlyMiddleSplit, with no private-name references. -/
namespace PrimeGapNormality.Prime.CorePresieveTwoSided
open Finset Filter
open scoped Topology Classical
noncomputable section

private theorem middle_card_filter_mod_le (S : ℕ) {A : Finset ℕ}
    (hA : A ⊆ Icc 1 S) (p r : ℕ) (hp : 0 < p) :
    ((A.filter fun n => n % p = r % p).card : ℝ) ≤
      (S : ℝ) / p + 1 := by
  have hsub :
      A.filter (fun n => n % p = r % p) ⊆
        (Ico 1 (1 + S)).filter (fun n => n % p = r % p) := by
    intro n hn
    have hnA := (mem_filter.mp hn).1
    have hnI := mem_Icc.mp (hA hnA)
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨hnI.1, ?_⟩, (mem_filter.mp hn).2⟩
    omega
  have hcard :
      ((A.filter fun n => n % p = r % p).card : ℝ) ≤
        (((Ico 1 (1 + S)).filter fun n => n % p = r % p).card : ℝ) :=
    Nat.cast_le.mpr (card_le_card hsub)
  exact hcard.trans (by
    simpa [Nat.add_comm] using card_Ico_mod_le_real 1 S p r hp)

theorem middlePresieve_count_lipschitz (S w : ℕ)
    {A : Finset ℕ} (hA : A ⊆ Icc 1 S)
    (υ : MiddleResidueChoice w S) (p : MiddlePrime w S)
    (a b : Fin (p.val - 1)) :
    |((middlePresieveSurvivors S w A (Function.update υ p a)).card : ℝ) -
        ((middlePresieveSurvivors S w A (Function.update υ p b)).card : ℝ)| ≤
      residueWidth (S : ℝ) p.val := by
  let U := middlePresieveSurvivors S w A (Function.update υ p a)
  let V := middlePresieveSurvivors S w A (Function.update υ p b)
  have hUV : U \ V ⊆ A.filter (fun n => n % p.val = b.val + 1) := by
    intro n hn
    have hnU := mem_filter.mp (mem_sdiff.mp hn).1
    have hnV : ¬n ∈ V := (mem_sdiff.mp hn).2
    refine mem_filter.mpr ⟨hnU.1, ?_⟩
    by_contra hne
    apply hnV
    refine mem_filter.mpr ⟨hnU.1, ?_⟩
    intro q
    by_cases hqp : q = p
    · subst q
      simpa [Function.update_self] using hne
    · have hq := hnU.2 q
      simpa [Function.update_of_ne hqp] using hq
  have hVU : V \ U ⊆ A.filter (fun n => n % p.val = a.val + 1) := by
    intro n hn
    have hnV := mem_filter.mp (mem_sdiff.mp hn).1
    have hnU : ¬n ∈ U := (mem_sdiff.mp hn).2
    refine mem_filter.mpr ⟨hnV.1, ?_⟩
    by_contra hne
    apply hnU
    refine mem_filter.mpr ⟨hnV.1, ?_⟩
    intro q
    by_cases hqp : q = p
    · subst q
      simpa [Function.update_self] using hne
    · have hq := hnV.2 q
      simpa [Function.update_of_ne hqp] using hq
  have habs :
      |(U.card : ℝ) - (V.card : ℝ)| ≤
        ((U \ V).card : ℝ) + ((V \ U).card : ℝ) := by
    have hU := card_sdiff_add_card_inter U V
    have hV := card_sdiff_add_card_inter V U
    have hinter : U ∩ V = V ∩ U := inter_comm _ _
    have hUR : (U.card : ℝ) = (U \ V).card + (U ∩ V).card := by
      exact_mod_cast hU.symm
    have hVR : (V.card : ℝ) = (V \ U).card + (U ∩ V).card := by
      rw [hinter]
      exact_mod_cast hV.symm
    rw [hUR, hVR]
    have h1 : 0 ≤ ((U \ V).card : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ ((V \ U).card : ℝ) := Nat.cast_nonneg _
    have htri := abs_sub_le ((U \ V).card : ℝ) 0 ((V \ U).card : ℝ)
    simpa [abs_of_nonneg h1, abs_of_nonneg h2, sub_zero, zero_sub,
      abs_neg] using htri
  have hpprime : Nat.Prime p.val :=
    Nat.prime_of_mem_primesLE (sdiff_subset p.property)
  have ha : a.val + 1 < p.val := by
    have := a.isLt
    omega
  have hb : b.val + 1 < p.val := by
    have := b.isLt
    omega
  have hca :
      (((A.filter fun n => n % p.val = a.val + 1).card : ℕ) : ℝ) ≤
        (S : ℝ) / p.val + 1 := by
    have h := middle_card_filter_mod_le S hA p.val (a.val + 1) hpprime.pos
    simpa [Nat.mod_eq_of_lt ha] using h
  have hcb :
      (((A.filter fun n => n % p.val = b.val + 1).card : ℕ) : ℝ) ≤
        (S : ℝ) / p.val + 1 := by
    have h := middle_card_filter_mod_le S hA p.val (b.val + 1) hpprime.pos
    simpa [Nat.mod_eq_of_lt hb] using h
  have hdiff :
      ((U \ V).card : ℝ) + ((V \ U).card : ℝ) ≤
        2 * ((S : ℝ) / p.val + 1) := by
    have h1 : ((U \ V).card : ℝ) ≤
        ((A.filter fun n => n % p.val = b.val + 1).card : ℝ) :=
      Nat.cast_le.mpr (card_le_card hUV)
    have h2 : ((V \ U).card : ℝ) ≤
        ((A.filter fun n => n % p.val = a.val + 1).card : ℝ) :=
      Nat.cast_le.mpr (card_le_card hVU)
    nlinarith
  exact habs.trans (hdiff.trans_eq
    (residueWidth_eq (S : ℝ) (p.val : ℝ)).symm)

end
end PrimeGapNormality.Prime.CorePresieveTwoSided

