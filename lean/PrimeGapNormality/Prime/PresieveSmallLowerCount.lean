import PrimeGapNormality.Prime.FiniteRootMixSmallFailure
import PrimeGapNormality.Prime.ResidueHoeffdingPi
import PrimeGapNormality.Prime.PresieveWindowS

/-!
# Concrete lower-count concentration for the small presieve

This file closes the type-level bridge between the abstract categorical
bounded-difference theorem and the actual uniform `ResidueChoice S`
space.  The survivor count is reindexed along `Fintype.equivFin`, its
coordinate widths are the genuine `2(S/p+1)`, and the product mass is
identified with uniform counting measure.

This does not assert that the resulting full-range exponential bound
tends to zero.  For that one must expose the primes through
`z₀=(log G)^4`, establish the uniform Bonferroni/CRT estimate for their
survivor count, and apply this concentration argument only to the
remaining coordinates.  That global-presieve mean estimate is not an
existing theorem in the imported API.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-- Canonical finite reindexing of the actual sieve-prime coordinates. -/
def presieveSmallIndexEquiv (S : ℕ) :
    SievePrime S ≃ Fin (Fintype.card (SievePrime S)) :=
  Fintype.equivFin (SievePrime S)

/-- Prime modulus after the canonical finite reindexing. -/
def presieveSmallModuli (S : ℕ)
    (i : Fin (Fintype.card (SievePrime S))) : ℕ :=
  (presieveSmallIndexEquiv S).symm i

/-- Reindex an actual `ResidueChoice S` as the `Fin n`-indexed product
used by `residuePiAvoidCount`. -/
def presieveSmallReindex (S : ℕ) :
    ResidueChoice S ≃
      (∀ i : Fin (Fintype.card (SievePrime S)),
        Fin (presieveSmallModuli S i - 1)) :=
  (presieveSmallIndexEquiv S).piCongrLeft'
    (fun p : SievePrime S => Fin (p.val - 1))

private theorem presieveSmall_decode_reindex (S : ℕ)
    (σ : ResidueChoice S) (i : Fin (Fintype.card (SievePrime S))) :
    decodeResidue (presieveSmallModuli S) (presieveSmallReindex S σ) i =
      residueOfChoice S σ ((presieveSmallIndexEquiv S).symm i).val := by
  change (σ ((presieveSmallIndexEquiv S).symm i)).val + 1 =
    residueOfChoice S σ ((presieveSmallIndexEquiv S).symm i).val
  simp [residueOfChoice, ((presieveSmallIndexEquiv S).symm i).property]

private theorem presieveSmall_residueOfChoice_lt (S : ℕ)
    (σ : ResidueChoice S) (p : SievePrime S) :
    residueOfChoice S σ p.val < p.val := by
  unfold residueOfChoice
  rw [dif_pos p.property]
  have hp_index : (⟨p.val, p.property⟩ : SievePrime S) = p :=
    Subtype.ext rfl
  rw [hp_index]
  have hval := (σ p).isLt
  change (σ p).val < p.val - 1 at hval
  have hp2 : 2 ≤ p.val := Nat.two_le_of_mem_primesLE p.property
  omega

/-- The reindexed residue count is definitionally the concrete
`presieveSurvivors` count on `Icc 1 S`. -/
theorem presieveSmall_count_eq_reindexed (S : ℕ) (σ : ResidueChoice S) :
    ((presieveSurvivors S σ).card : ℝ) =
      residuePiAvoidCount (presieveSmallModuli S) 1 S
        (presieveSmallReindex S σ) := by
  rw [residuePiAvoidCount_window]
  apply congrArg Nat.cast
  unfold presieveSurvivors residueAvoidCount
  apply congrArg Finset.card
  ext n
  simp only [mem_filter]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have hs := h.2
    unfold sieveSurvives at hs
    intro i
    let p := (presieveSmallIndexEquiv S).symm i
    have hp := hs p.val p.property
    have hmod : residueOfChoice S σ p.val % p.val =
        residueOfChoice S σ p.val :=
      Nat.mod_eq_of_lt (presieveSmall_residueOfChoice_lt S σ p)
    rw [presieveSmall_decode_reindex]
    simpa [presieveSmallModuli, p, hmod] using hp
  · intro h
    refine ⟨h.1, ?_⟩
    unfold sieveSurvives
    intro p hp
    let i := presieveSmallIndexEquiv S ⟨p, hp⟩
    have hi := h.2 i
    rw [presieveSmall_decode_reindex] at hi
    have hmod : residueOfChoice S σ p % p = residueOfChoice S σ p :=
      Nat.mod_eq_of_lt
        (presieveSmall_residueOfChoice_lt S σ ⟨p, hp⟩)
    simpa [presieveSmallModuli, i, hmod] using hi

/-- The actual presieve survivor count has the genuine categorical
coordinate diameter `2(S/p+1)`. -/
theorem presieveSmall_count_lipschitz (S : ℕ) (σ : ResidueChoice S)
    (p : SievePrime S) (a b : Fin (p.val - 1)) :
    |((presieveSurvivors S (Function.update σ p a)).card : ℝ) -
        ((presieveSurvivors S (Function.update σ p b)).card : ℝ)| ≤
      residueWidth (S : ℝ) p.val := by
  let e := presieveSmallIndexEquiv S
  let i := e p
  let τa := presieveSmallReindex S (Function.update σ p a)
  let τb := presieveSmallReindex S (Function.update σ p b)
  have hp : 0 < presieveSmallModuli S i := by
    change 0 < ((e.symm (e p) : SievePrime S) : ℕ)
    simpa only [e.symm_apply_apply] using
      (Nat.prime_of_mem_primesLE p.property).pos
  have hτ : Function.update τb i (τa i) = τa := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
    · rw [Function.update_of_ne hji]
      have hjp : e.symm j ≠ p := by
        intro hjp
        apply hji
        calc
          j = e (e.symm j) := (e.apply_symm_apply j).symm
          _ = e p := congrArg e hjp
      change Function.update σ p b (e.symm j) =
        Function.update σ p a (e.symm j)
      rw [Function.update_of_ne hjp, Function.update_of_ne hjp]
  have hτb : Function.update τb i (τb i) = τb := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
    · rw [Function.update_of_ne hji]
  have h := residuePiAvoidCount_lipschitz
    (presieveSmallModuli S) 1 S τb i (τa i) (τb i) hp
  rw [hτ, hτb] at h
  rw [presieveSmall_count_eq_reindexed,
    presieveSmall_count_eq_reindexed]
  have hi : presieveSmallModuli S i = p.val := by
    change ((e.symm (e p) : SievePrime S) : ℕ) = p.val
    simpa only [e.symm_apply_apply]
  simpa only [τa, τb, hi] using h

/-- Uniform mean of the actual presieve survivor count. -/
def presieveSmallUniformMean (S : ℕ) : ℝ :=
  (∑ σ : ResidueChoice S, ((presieveSurvivors S σ).card : ℝ)) /
    (Fintype.card (ResidueChoice S) : ℝ)

/-- The categorical product mass is exactly reciprocal cardinality on
the actual `ResidueChoice S` space. -/
theorem presieveSmall_uniform_product_mass (S : ℕ) (σ : ResidueChoice S) :
    (∏ p : SievePrime S, uniformFin (σ p)) =
      (Fintype.card (ResidueChoice S) : ℝ)⁻¹ := by
  unfold uniformFin
  rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
  simp only [Fintype.card_fin]

/-- The product expectation of the negative survivor count is the
negative normalized counting mean. -/
theorem presieveSmall_negative_expectation (S : ℕ) :
    ∑ σ : ResidueChoice S,
        (∏ p : SievePrime S, uniformFin (σ p)) *
          (-((presieveSurvivors S σ).card : ℝ)) =
      -presieveSmallUniformMean S := by
  simp_rw [presieveSmall_uniform_product_mass]
  calc
    ∑ σ : ResidueChoice S,
        (Fintype.card (ResidueChoice S) : ℝ)⁻¹ *
          (-((presieveSurvivors S σ).card : ℝ)) =
      (Fintype.card (ResidueChoice S) : ℝ)⁻¹ *
        ∑ σ : ResidueChoice S,
          (-((presieveSurvivors S σ).card : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
    _ = (Fintype.card (ResidueChoice S) : ℝ)⁻¹ *
        (-(∑ σ : ResidueChoice S,
          ((presieveSurvivors S σ).card : ℝ))) := by
      rw [Finset.sum_neg_distrib]
    _ = -presieveSmallUniformMean S := by
      unfold presieveSmallUniformMean
      rw [div_eq_mul_inv]
      ring

/-- Fully concrete instantiation of the arbitrary-index categorical
McDiarmid theorem.  All coordinate laws, widths, and update bounds are
discharged for `ResidueChoice S`; the only argument is the positive
deviation size. -/
theorem presieveSmall_piCoord_lowerTail (S : ℕ) {u : ℝ} (hu : 0 < u) :
    PiCoordBoundedDiffOneSided
      (fun _p : SievePrime S => uniformFin)
      (fun σ : ResidueChoice S =>
        -((presieveSurvivors S σ).card : ℝ))
      (fun p : SievePrime S => residueWidth (S : ℝ) p.val) u := by
  apply piCoord_bounded_diff_one_sided
  · intro p a
    exact uniformFin_nonneg a
  · intro p
    exact uniformFin_sum
      (Nat.sub_pos_of_lt (Nat.prime_of_mem_primesLE p.property).one_lt)
  · intro p
    exact residueWidth_nonneg (Nat.cast_nonneg S)
      (Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE p.property).pos)
  · intro σ p a b
    have h := presieveSmall_count_lipschitz S σ p a b
    simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using h
  · exact hu

/-- Uniform lower-tail concentration for the actual survivor count,
centered at its exact uniform mean.  This is the concrete counting-mass
form of `presieveSmall_piCoord_lowerTail`. -/
theorem presieveSmall_uniform_lowerTail (S : ℕ) {u : ℝ} (hu : 0 < u) :
    (((univ : Finset (ResidueChoice S)).filter fun σ =>
        u ≤ presieveSmallUniformMean S -
          ((presieveSurvivors S σ).card : ℝ)).card : ℝ) /
        (Fintype.card (ResidueChoice S) : ℝ) ≤
      if ∑ p : SievePrime S, residueWidth (S : ℝ) p.val ^ 2 = 0 then 0
      else Real.exp (-u ^ 2 /
        ∑ p : SievePrime S, residueWidth (S : ℝ) p.val ^ 2) := by
  have h := presieveSmall_piCoord_lowerTail S hu
  unfold PiCoordBoundedDiffOneSided at h
  rw [presieveSmall_negative_expectation] at h
  have hfilter :
      (univ : Finset (ResidueChoice S)).filter (fun σ =>
          u ≤ -((presieveSurvivors S σ).card : ℝ) -
            -presieveSmallUniformMean S) =
        (univ : Finset (ResidueChoice S)).filter (fun σ =>
          u ≤ presieveSmallUniformMean S -
            ((presieveSurvivors S σ).card : ℝ)) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> intro hσ <;> linarith
  rw [hfilter] at h
  simp_rw [presieveSmall_uniform_product_mass] at h
  have hmass :
      ∑ σ ∈ (univ : Finset (ResidueChoice S)).filter (fun σ =>
          u ≤ presieveSmallUniformMean S -
            ((presieveSurvivors S σ).card : ℝ)),
          (Fintype.card (ResidueChoice S) : ℝ)⁻¹ =
        (((univ : Finset (ResidueChoice S)).filter fun σ =>
          u ≤ presieveSmallUniformMean S -
            ((presieveSurvivors S σ).card : ℝ)).card : ℝ) /
          (Fintype.card (ResidueChoice S) : ℝ) := by
    rw [sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [hmass] at h
  exact h

end

end PrimeGapNormality.Prime
