import PrimeGapNormality.Prime.PresieveSmallGlobalLower
import PrimeGapNormality.Prime.CardinalitySymMass

/-!
# Early/middle product split for the rooted small presieve

For `w ≤ S`, the full rooted residue space through `S` is the product of
the exposed coordinates `p ≤ w` and the middle coordinates `w < p ≤ S`.
This file makes that finite equivalence public and proves the conditional
bounded-difference estimate on the middle fibre.

The conditional mean is deliberately kept exact.  It is not in general
`|A| * rootedEulerProdNat w S`: a candidate divisible by a middle prime
survives that rooted coordinate automatically.  Comparing the exact mean
with the Euler main term is therefore a separate (one-sided) calibration
step, not part of Hoeffding.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-! ## The finite early/middle product -/

/-- Middle primes `w < p ≤ S`. -/
abbrev MiddlePrime (w S : ℕ) := LatePrime w S

/-- Rooted forbidden-residue choices on the middle primes. -/
abbrev MiddleResidueChoice (w S : ℕ) := LateResidueChoice w S

private theorem earlyMiddle_primesLE_subset {w S : ℕ} (hwS : w ≤ S) :
    Nat.primesLE w ⊆ Nat.primesLE S :=
  Nat.primesLE_mono hwS

/-- Glue exposed and middle rooted residue choices into the full choice. -/
def earlyMiddleGlue (w S : ℕ) (hwS : w ≤ S)
    (τ : ResidueChoice w) (υ : MiddleResidueChoice w S) : ResidueChoice S :=
  fun p =>
    if hp : p.val ∈ Nat.primesLE w then
      τ ⟨p.val, hp⟩
    else
      υ ⟨p.val, mem_sdiff.mpr ⟨p.property, hp⟩⟩

/-- Restriction of a full choice to the exposed coordinates. -/
def earlyMiddleRestrictEarly (w S : ℕ) (hwS : w ≤ S)
    (ρ : ResidueChoice S) : ResidueChoice w :=
  fun p => ρ ⟨p.val, earlyMiddle_primesLE_subset hwS p.property⟩

/-- Restriction of a full choice to the middle coordinates. -/
def earlyMiddleRestrictMiddle (w S : ℕ) (_hwS : w ≤ S)
    (ρ : ResidueChoice S) : MiddleResidueChoice w S :=
  fun p => ρ ⟨p.val, sdiff_subset p.property⟩

/-- Public finite product equivalence
`ResidueChoice w × MiddleResidueChoice w S ≃ ResidueChoice S`. -/
def earlyMiddleResidueEquiv (w S : ℕ) (hwS : w ≤ S) :
    ResidueChoice w × MiddleResidueChoice w S ≃ ResidueChoice S where
  toFun := fun pair => earlyMiddleGlue w S hwS pair.1 pair.2
  invFun := fun ρ =>
    (earlyMiddleRestrictEarly w S hwS ρ,
      earlyMiddleRestrictMiddle w S hwS ρ)
  left_inv := by
    rintro ⟨τ, υ⟩
    refine Prod.ext ?_ ?_
    · funext p
      simp [earlyMiddleRestrictEarly, earlyMiddleGlue, p.property]
    · funext p
      have hp : p.val ∉ Nat.primesLE w := (mem_sdiff.mp p.property).2
      simp [earlyMiddleRestrictMiddle, earlyMiddleGlue, hp]
  right_inv := by
    intro ρ
    funext p
    by_cases hp : p.val ∈ Nat.primesLE w
    · simp [earlyMiddleGlue, earlyMiddleRestrictEarly, hp]
    · simp [earlyMiddleGlue, earlyMiddleRestrictMiddle, hp]

/-- Cardinality factorization induced by `earlyMiddleResidueEquiv`. -/
theorem earlyMiddle_residueChoice_card (w S : ℕ) (hwS : w ≤ S) :
    Fintype.card (ResidueChoice S) =
      Fintype.card (ResidueChoice w) *
        Fintype.card (MiddleResidueChoice w S) := by
  rw [← Fintype.card_congr (earlyMiddleResidueEquiv w S hwS),
    Fintype.card_prod]

/-- Exact fibre-cardinality formula for an arbitrary decidable event on
the full rooted residue space. -/
theorem earlyMiddle_card_filter_eq_sum (w S : ℕ) (hwS : w ≤ S)
    (P : ResidueChoice S → Prop) [DecidablePred P] :
    ((univ : Finset (ResidueChoice S)).filter P).card =
      ∑ τ : ResidueChoice w,
        ((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
          P (earlyMiddleGlue w S hwS τ υ)).card := by
  let e := earlyMiddleResidueEquiv w S hwS
  have hleft :
      ((univ : Finset (ResidueChoice S)).filter P).card =
        ((univ : Finset
          (ResidueChoice w × MiddleResidueChoice w S)).filter fun pair =>
            P (e pair)).card := by
    refine card_equiv e.symm ?_
    intro ρ
    simp only [mem_filter, mem_univ, true_and]
    rw [e.apply_symm_apply]
  rw [hleft]
  have hprod :
      ((univ : Finset
          (ResidueChoice w × MiddleResidueChoice w S)).filter fun pair =>
            P (e pair)).card =
        ∑ pair : ResidueChoice w × MiddleResidueChoice w S,
          if P (e pair) then (1 : ℕ) else 0 := by
    exact (sum_boole (R := ℕ) _ _).symm
  rw [hprod, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro τ _hτ
  change (∑ υ : MiddleResidueChoice w S,
      if P (earlyMiddleGlue w S hwS τ υ) then (1 : ℕ) else 0) = _
  exact sum_boole (R := ℕ) _ _

/-! ## Conditional middle survivors -/

/-- Survivors in a fixed set after applying only `w < p ≤ S`. -/
def middlePresieveSurvivors (S w : ℕ) (A : Finset ℕ)
    (υ : MiddleResidueChoice w S) : Finset ℕ :=
  A.filter fun n =>
    ∀ p : MiddlePrime w S, n % p.val ≠ (υ p).val + 1

theorem middlePresieveSurvivors_subset (S w : ℕ) (A : Finset ℕ)
    (υ : MiddleResidueChoice w S) :
    middlePresieveSurvivors S w A υ ⊆ A :=
  filter_subset _ _

theorem earlyMiddle_residueOfChoice_early {w S : ℕ} (hwS : w ≤ S)
    (τ : ResidueChoice w) (υ : MiddleResidueChoice w S) {p : ℕ}
    (hp : p ∈ Nat.primesLE w) :
    residueOfChoice S (earlyMiddleGlue w S hwS τ υ) p =
      residueOfChoice w τ p := by
  have hpS : p ∈ Nat.primesLE S := earlyMiddle_primesLE_subset hwS hp
  simp [residueOfChoice, earlyMiddleGlue, hpS, hp]

theorem earlyMiddle_residueOfChoice_middle {w S : ℕ} (hwS : w ≤ S)
    (τ : ResidueChoice w) (υ : MiddleResidueChoice w S) {p : ℕ}
    (hp : p ∈ Nat.primesLE S \ Nat.primesLE w) :
    residueOfChoice S (earlyMiddleGlue w S hwS τ υ) p =
      (υ ⟨p, hp⟩).val + 1 := by
  have hpS : p ∈ Nat.primesLE S := sdiff_subset hp
  have hpw : p ∉ Nat.primesLE w := (mem_sdiff.mp hp).2
  simp [residueOfChoice, earlyMiddleGlue, hpS, hpw]

/-- Applying the glued full choice equals first exposing `p ≤ w`, then
filtering the exposed set by `w < p ≤ S`. -/
theorem presieveSurvivors_earlyMiddleGlue (w S : ℕ) (hwS : w ≤ S)
    (τ : ResidueChoice w) (υ : MiddleResidueChoice w S) :
    presieveSurvivors S (earlyMiddleGlue w S hwS τ υ) =
      middlePresieveSurvivors S w (earlyPresieveSurvivors S w τ) υ := by
  ext n
  simp only [presieveSurvivors, earlyPresieveSurvivors,
    middlePresieveSurvivors, mem_filter]
  constructor
  · intro hn
    refine ⟨⟨hn.1, ?_⟩, ?_⟩
    · intro p
      have h := hn.2 p.val (earlyMiddle_primesLE_subset hwS p.property)
      rw [earlyMiddle_residueOfChoice_early hwS τ υ p.property] at h
      simpa [residueOfChoice, p.property] using h
    · intro p
      have h := hn.2 p.val (sdiff_subset p.property)
      rwa [earlyMiddle_residueOfChoice_middle hwS τ υ p.property] at h
  · intro hn
    refine ⟨hn.1.1, ?_⟩
    intro p hpS
    by_cases hpw : p ∈ Nat.primesLE w
    · have h := hn.1.2 ⟨p, hpw⟩
      rw [earlyMiddle_residueOfChoice_early hwS τ υ hpw]
      simpa [residueOfChoice, hpw] using h
    · have hp : p ∈ Nat.primesLE S \ Nat.primesLE w :=
        mem_sdiff.mpr ⟨hpS, hpw⟩
      have h := hn.2 ⟨p, hp⟩
      rwa [earlyMiddle_residueOfChoice_middle hwS τ υ hp]

/-- The concrete survivor-event fibre count is the sum of its conditional
middle-fibre counts. -/
theorem earlyMiddle_survivor_card_filter_eq_sum (w S : ℕ) (hwS : w ≤ S)
    (Q : Finset ℕ → Prop) [DecidablePred Q] :
    ((univ : Finset (ResidueChoice S)).filter fun ρ =>
        Q (presieveSurvivors S ρ)).card =
      ∑ τ : ResidueChoice w,
        ((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
          Q (middlePresieveSurvivors S w
            (earlyPresieveSurvivors S w τ) υ)).card := by
  rw [earlyMiddle_card_filter_eq_sum w S hwS]
  apply sum_congr rfl
  intro τ _hτ
  apply congrArg Finset.card
  ext υ
  simp only [mem_filter, mem_univ, true_and]
  rw [presieveSurvivors_earlyMiddleGlue w S hwS τ υ]

/-! ## Conditional bounded differences on the middle fibre -/

/-- The exact squared-width sum for the coordinates `w < p ≤ S`. -/
def middleWidthSq (S w : ℕ) : ℝ :=
  ∑ p : MiddlePrime w S, residueWidth (S : ℝ) p.val ^ 2

/-- Exact uniform conditional mean after the early fibre has been fixed. -/
def middlePresieveUniformMean (S w : ℕ) (A : Finset ℕ) : ℝ :=
  (∑ υ : MiddleResidueChoice w S,
      ((middlePresieveSurvivors S w A υ).card : ℝ)) /
    (Fintype.card (MiddleResidueChoice w S) : ℝ)

private theorem middleChoice_uniform_product_mass (w S : ℕ)
    (υ : MiddleResidueChoice w S) :
    (∏ p : MiddlePrime w S, uniformFin (υ p)) =
      (Fintype.card (MiddleResidueChoice w S) : ℝ)⁻¹ := by
  unfold uniformFin
  rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
  simp only [Fintype.card_fin]

private theorem middlePresieve_negative_expectation (S w : ℕ)
    (A : Finset ℕ) :
    ∑ υ : MiddleResidueChoice w S,
        (∏ p : MiddlePrime w S, uniformFin (υ p)) *
          (-((middlePresieveSurvivors S w A υ).card : ℝ)) =
      -middlePresieveUniformMean S w A := by
  simp_rw [middleChoice_uniform_product_mass]
  unfold middlePresieveUniformMean
  rw [div_eq_mul_inv]
  calc
    ∑ υ : MiddleResidueChoice w S,
        (Fintype.card (MiddleResidueChoice w S) : ℝ)⁻¹ *
          (-((middlePresieveSurvivors S w A υ).card : ℝ)) =
      (Fintype.card (MiddleResidueChoice w S) : ℝ)⁻¹ *
        ∑ υ : MiddleResidueChoice w S,
          (-((middlePresieveSurvivors S w A υ).card : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
    _ = (Fintype.card (MiddleResidueChoice w S) : ℝ)⁻¹ *
        (-(∑ υ : MiddleResidueChoice w S,
          ((middlePresieveSurvivors S w A υ).card : ℝ))) := by
      rw [Finset.sum_neg_distrib]
    _ = -((∑ υ : MiddleResidueChoice w S,
          ((middlePresieveSurvivors S w A υ).card : ℝ)) *
        (Fintype.card (MiddleResidueChoice w S) : ℝ)⁻¹) := by ring

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

private theorem middlePresieve_count_lipschitz (S w : ℕ)
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

/-- The arbitrary-index one-sided Hoeffding theorem, instantiated on a
fixed exposed fibre and only the middle coordinates. -/
theorem middlePresieve_piCoord_lowerTail (S w : ℕ) {A : Finset ℕ}
    (hA : A ⊆ Icc 1 S) {u : ℝ} (hu : 0 < u) :
    PiCoordBoundedDiffOneSided
      (fun _p : MiddlePrime w S => uniformFin)
      (fun υ : MiddleResidueChoice w S =>
        -((middlePresieveSurvivors S w A υ).card : ℝ))
      (fun p : MiddlePrime w S => residueWidth (S : ℝ) p.val) u := by
  apply piCoord_bounded_diff_one_sided
  · intro p a
    exact uniformFin_nonneg a
  · intro p
    have hp : Nat.Prime p.val :=
      Nat.prime_of_mem_primesLE (sdiff_subset p.property)
    exact uniformFin_sum (Nat.sub_pos_of_lt hp.one_lt)
  · intro p
    exact residueWidth_nonneg (Nat.cast_nonneg S)
      (Nat.cast_pos.mpr
        (Nat.prime_of_mem_primesLE (sdiff_subset p.property)).pos)
  · intro υ p a b
    have h := middlePresieve_count_lipschitz S w hA υ p a b
    simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using h
  · exact hu

/-- Conditional uniform lower-tail bound on the middle fibre.  The
Hoeffding exponent is exactly `-u² / middleWidthSq S w`; equivalently the
constant in the exponent is `1` for the widths `2(S/p+1)`. -/
theorem middlePresieve_uniform_lowerTail (S w : ℕ) {A : Finset ℕ}
    (hA : A ⊆ Icc 1 S) {u : ℝ} (hu : 0 < u) :
    (((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
        u ≤ middlePresieveUniformMean S w A -
          ((middlePresieveSurvivors S w A υ).card : ℝ)).card : ℝ) /
        (Fintype.card (MiddleResidueChoice w S) : ℝ) ≤
      if middleWidthSq S w = 0 then 0
      else Real.exp (-u ^ 2 / middleWidthSq S w) := by
  have h := middlePresieve_piCoord_lowerTail S w hA hu
  unfold PiCoordBoundedDiffOneSided at h
  rw [middlePresieve_negative_expectation] at h
  have hfilter :
      (univ : Finset (MiddleResidueChoice w S)).filter (fun υ =>
          u ≤ -((middlePresieveSurvivors S w A υ).card : ℝ) -
            -middlePresieveUniformMean S w A) =
        (univ : Finset (MiddleResidueChoice w S)).filter (fun υ =>
          u ≤ middlePresieveUniformMean S w A -
            ((middlePresieveSurvivors S w A υ).card : ℝ)) := by
    ext υ
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> intro hυ <;> linarith
  rw [hfilter] at h
  simp_rw [middleChoice_uniform_product_mass] at h
  have hmass :
      ∑ υ ∈ (univ : Finset (MiddleResidueChoice w S)).filter (fun υ =>
          u ≤ middlePresieveUniformMean S w A -
            ((middlePresieveSurvivors S w A υ).card : ℝ)),
          (Fintype.card (MiddleResidueChoice w S) : ℝ)⁻¹ =
        (((univ : Finset (MiddleResidueChoice w S)).filter fun υ =>
          u ≤ middlePresieveUniformMean S w A -
            ((middlePresieveSurvivors S w A υ).card : ℝ)).card : ℝ) /
          (Fintype.card (MiddleResidueChoice w S) : ℝ) := by
    rw [sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [hmass] at h
  unfold middleWidthSq
  exact h

end

end PrimeGapNormality.Prime
