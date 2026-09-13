import PrimeGapNormality.Prime.PresieveSmallLowerCount

/-!
# The finite early presieve: exact rooted moments and Chebyshev

This file isolates the hypothesis-free finite part of the global
presieve lower-count argument.  The early coordinates are the primes
`p ≤ w`; for an early choice `τ : ResidueChoice w`,
`earlyPresieveSurvivors S w τ` is the paper's exposed set
`A_τ ⊆ [1,S]`.

The rooted law chooses a uniform *nonzero* forbidden residue.  Thus a
candidate divisible by `p` survives that coordinate with probability
one, and the one- and two-point factors below deliberately retain that
dependence.  In particular, this file does not replace the rooted
first moment by `S * eulerProdNat w`, and it does not claim a lower
bound for every `τ`.

The main finite results are:

* `earlyPresieve_uniformMean_eq_exact`: exact first moment;
* `earlyPresieve_uniformSecondMoment_eq_exact`: exact second moment;
* `earlyPresieve_uniformVariance_eq_exact`: exact variance;
* `earlyPresieve_chebyshev`: a quantitative exceptional-mass bound.

All probability-space and independence assumptions are discharged by
finite product counting.  The remaining analytic step toward the
paper's global lower count is to estimate the explicit rooted
one-point and two-point products in these theorems (equivalently, the paper's
Bonferroni/CRT estimate through `w = presieveW (windowG X)`).
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### The exposed early fibre -/

/-- A point survives all exposed coordinates `p ≤ w`. -/
def earlyPresieveSurvives (w : ℕ) (τ : ResidueChoice w) (n : ℕ) : Prop :=
  ∀ p : SievePrime w, n % p.val ≠ (τ p).val + 1

/-- The exposed survivor set `A_τ ⊆ Icc 1 S`. -/
def earlyPresieveSurvivors (S w : ℕ) (τ : ResidueChoice w) : Finset ℕ :=
  (Icc 1 S).filter (earlyPresieveSurvives w τ)

theorem earlyPresieveSurvivors_subset_Icc (S w : ℕ)
    (τ : ResidueChoice w) :
    earlyPresieveSurvivors S w τ ⊆ Icc 1 S :=
  filter_subset _ _

/-- The typed early-coordinate predicate is the existing sieve
predicate through `w`. -/
theorem earlyPresieveSurvives_iff_sieveSurvives (w : ℕ)
    (τ : ResidueChoice w) (n : ℕ) :
    earlyPresieveSurvives w τ n ↔
      sieveSurvives w (residueOfChoice w τ) n := by
  constructor
  · intro h p hp
    have hmod := h ⟨p, hp⟩
    simpa [residueOfChoice, hp] using hmod
  · intro h p
    have hp := h p.val p.property
    simpa [residueOfChoice, p.property] using hp

/-- At `w = S` the exposed set is the existing full small-presieve
survivor set. -/
theorem earlyPresieveSurvivors_self_eq_presieveSurvivors (S : ℕ)
    (τ : ResidueChoice S) :
    earlyPresieveSurvivors S S τ = presieveSurvivors S τ := by
  unfold earlyPresieveSurvivors presieveSurvivors
  ext n
  simp only [Finset.mem_filter]
  rw [earlyPresieveSurvives_iff_sieveSurvives]

/-! ### Exact rooted one- and two-point factors -/

/-- The `0`/`1` indicator that `n` survives the coordinate `p` when
the chosen forbidden residue is `a+1`. -/
def earlyPresieveLocalIndicator {w : ℕ} (p : SievePrime w)
    (n : ℕ) (a : Fin (p.val - 1)) : ℝ :=
  if n % p.val ≠ a.val + 1 then 1 else 0

/-- Exact rooted one-point survival mass at a single early prime. -/
def earlyPresieveOneLocalMass {w : ℕ} (p : SievePrime w)
    (n : ℕ) : ℝ :=
  ∑ a : Fin (p.val - 1), uniformFin a *
    earlyPresieveLocalIndicator p n a

/-- Exact rooted two-point survival mass at a single early prime. -/
def earlyPresievePairLocalMass {w : ℕ} (p : SievePrime w)
    (n m : ℕ) : ℝ :=
  ∑ a : Fin (p.val - 1), uniformFin a *
    (earlyPresieveLocalIndicator p n a *
      earlyPresieveLocalIndicator p m a)

/-- Exact rooted one-point survival probability through `w`. -/
def earlyPresieveOneWeight (w n : ℕ) : ℝ :=
  ∏ p : SievePrime w, earlyPresieveOneLocalMass p n

/-- Exact rooted joint survival probability through `w`. -/
def earlyPresievePairWeight (w n m : ℕ) : ℝ :=
  ∏ p : SievePrime w, earlyPresievePairLocalMass p n m

/-- The one-prime factor is literally the proportion of allowed
nonzero residues.  This makes the special factor `1` when `p ∣ n`
visible without imposing a nondivisibility hypothesis. -/
theorem earlyPresieveOneLocalMass_eq_card {w : ℕ}
    (p : SievePrime w) (n : ℕ) :
    earlyPresieveOneLocalMass p n =
      (((univ : Finset (Fin (p.val - 1))).filter fun a =>
          n % p.val ≠ a.val + 1).card : ℝ) /
        (p.val - 1 : ℕ) := by
  unfold earlyPresieveOneLocalMass earlyPresieveLocalIndicator uniformFin
  calc
    ∑ a : Fin (p.val - 1),
        ((p.val - 1 : ℕ) : ℝ)⁻¹ *
          (if n % p.val ≠ a.val + 1 then 1 else 0) =
      ((p.val - 1 : ℕ) : ℝ)⁻¹ *
        ∑ a : Fin (p.val - 1),
          (if n % p.val ≠ a.val + 1 then 1 else 0) := by
            rw [Finset.mul_sum]
    _ = ((p.val - 1 : ℕ) : ℝ)⁻¹ *
        (((univ : Finset (Fin (p.val - 1))).filter fun a =>
          n % p.val ≠ a.val + 1).card : ℝ) := by
            rw [Finset.sum_boole]
    _ = (((univ : Finset (Fin (p.val - 1))).filter fun a =>
          n % p.val ≠ a.val + 1).card : ℝ) /
        (p.val - 1 : ℕ) := by
          rw [div_eq_mul_inv]
          ring

/-- The two-prime factor is the proportion of nonzero residues which
avoid both candidates. -/
theorem earlyPresievePairLocalMass_eq_card {w : ℕ}
    (p : SievePrime w) (n m : ℕ) :
    earlyPresievePairLocalMass p n m =
      (((univ : Finset (Fin (p.val - 1))).filter fun a =>
          n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1).card : ℝ) /
        (p.val - 1 : ℕ) := by
  unfold earlyPresievePairLocalMass earlyPresieveLocalIndicator uniformFin
  have hind : ∀ a : Fin (p.val - 1),
      (if n % p.val ≠ a.val + 1 then (1 : ℝ) else 0) *
          (if m % p.val ≠ a.val + 1 then (1 : ℝ) else 0) =
        if n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1
          then 1 else 0 := by
    intro a
    by_cases hn : n % p.val ≠ a.val + 1 <;>
      by_cases hm : m % p.val ≠ a.val + 1 <;> simp [hn, hm]
  simp_rw [hind]
  calc
    ∑ a : Fin (p.val - 1),
        ((p.val - 1 : ℕ) : ℝ)⁻¹ *
          (if n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1
            then 1 else 0) =
      ((p.val - 1 : ℕ) : ℝ)⁻¹ *
        ∑ a : Fin (p.val - 1),
          (if n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1
            then 1 else 0) := by
              rw [Finset.mul_sum]
    _ = ((p.val - 1 : ℕ) : ℝ)⁻¹ *
        (((univ : Finset (Fin (p.val - 1))).filter fun a =>
          n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1).card : ℝ) := by
            rw [Finset.sum_boole]
    _ = (((univ : Finset (Fin (p.val - 1))).filter fun a =>
          n % p.val ≠ a.val + 1 ∧ m % p.val ≠ a.val + 1).card : ℝ) /
        (p.val - 1 : ℕ) := by
          rw [div_eq_mul_inv]
          ring

private theorem earlyPresieve_indicator_eq_prod (w n : ℕ)
    (τ : ResidueChoice w) :
    (if earlyPresieveSurvives w τ n then (1 : ℝ) else 0) =
      ∏ p : SievePrime w, earlyPresieveLocalIndicator p n (τ p) := by
  unfold earlyPresieveSurvives earlyPresieveLocalIndicator
  rw [Fintype.prod_boole]
  by_cases h : ∀ p : SievePrime w, n % p.val ≠ (τ p).val + 1 <;>
    simp [h]

private theorem earlyPresieve_weighted_indicator (w n : ℕ) :
    ∑ τ : ResidueChoice w,
        (∏ p : SievePrime w, uniformFin (τ p)) *
          (if earlyPresieveSurvives w τ n then (1 : ℝ) else 0) =
      earlyPresieveOneWeight w n := by
  simp_rw [earlyPresieve_indicator_eq_prod]
  unfold earlyPresieveOneWeight earlyPresieveOneLocalMass
  calc
    ∑ τ : ResidueChoice w,
        (∏ p : SievePrime w, uniformFin (τ p)) *
          ∏ p : SievePrime w, earlyPresieveLocalIndicator p n (τ p) =
      ∑ τ : ResidueChoice w, ∏ p : SievePrime w,
        uniformFin (τ p) * earlyPresieveLocalIndicator p n (τ p) := by
          simp_rw [Finset.prod_mul_distrib]
    _ = ∏ p : SievePrime w, ∑ a : Fin (p.val - 1),
        uniformFin a * earlyPresieveLocalIndicator p n a := by
          rw [Fintype.prod_sum]

private theorem earlyPresieve_weighted_pair_indicator (w n m : ℕ) :
    ∑ τ : ResidueChoice w,
        (∏ p : SievePrime w, uniformFin (τ p)) *
          ((if earlyPresieveSurvives w τ n then (1 : ℝ) else 0) *
            (if earlyPresieveSurvives w τ m then (1 : ℝ) else 0)) =
      earlyPresievePairWeight w n m := by
  simp_rw [earlyPresieve_indicator_eq_prod]
  unfold earlyPresievePairWeight earlyPresievePairLocalMass
  calc
    ∑ τ : ResidueChoice w,
        (∏ p : SievePrime w, uniformFin (τ p)) *
          ((∏ p : SievePrime w, earlyPresieveLocalIndicator p n (τ p)) *
            ∏ p : SievePrime w, earlyPresieveLocalIndicator p m (τ p)) =
      ∑ τ : ResidueChoice w, ∏ p : SievePrime w,
        uniformFin (τ p) *
          (earlyPresieveLocalIndicator p n (τ p) *
            earlyPresieveLocalIndicator p m (τ p)) := by
              simp_rw [Finset.prod_mul_distrib]
    _ = ∏ p : SievePrime w, ∑ a : Fin (p.val - 1),
        uniformFin a *
          (earlyPresieveLocalIndicator p n a *
            earlyPresieveLocalIndicator p m a) := by
              rw [Fintype.prod_sum]

/-! ### Exact first and second moments -/

/-- Uniform counting mean of the exposed survivor count. -/
def earlyPresieveUniformMean (S w : ℕ) : ℝ :=
  (∑ τ : ResidueChoice w, ((earlyPresieveSurvivors S w τ).card : ℝ)) /
    (Fintype.card (ResidueChoice w) : ℝ)

/-- Uniform counting second moment of the exposed survivor count. -/
def earlyPresieveUniformSecondMoment (S w : ℕ) : ℝ :=
  (∑ τ : ResidueChoice w,
      ((earlyPresieveSurvivors S w τ).card : ℝ) ^ 2) /
    (Fintype.card (ResidueChoice w) : ℝ)

/-- Exact uniform variance of the exposed survivor count. -/
def earlyPresieveUniformVariance (S w : ℕ) : ℝ :=
  earlyPresieveUniformSecondMoment S w -
    earlyPresieveUniformMean S w ^ 2

private theorem earlyPresieve_card_eq_indicator_sum (S w : ℕ)
    (τ : ResidueChoice w) :
    ((earlyPresieveSurvivors S w τ).card : ℝ) =
      ∑ n ∈ Icc 1 S,
        if earlyPresieveSurvives w τ n then (1 : ℝ) else 0 := by
  unfold earlyPresieveSurvivors
  rw [Finset.natCast_card_filter]

private theorem earlyPresieve_uniformMean_eq_weighted (S w : ℕ) :
    earlyPresieveUniformMean S w =
      ∑ τ : ResidueChoice w,
        (∏ p : SievePrime w, uniformFin (τ p)) *
          ((earlyPresieveSurvivors S w τ).card : ℝ) := by
  simp_rw [presieveSmall_uniform_product_mass]
  unfold earlyPresieveUniformMean
  rw [div_eq_mul_inv]
  calc
    (∑ τ : ResidueChoice w,
        ((earlyPresieveSurvivors S w τ).card : ℝ)) *
          (Fintype.card (ResidueChoice w) : ℝ)⁻¹ =
      (Fintype.card (ResidueChoice w) : ℝ)⁻¹ *
        ∑ τ : ResidueChoice w,
          ((earlyPresieveSurvivors S w τ).card : ℝ) := by ring
    _ = ∑ τ : ResidueChoice w,
        (Fintype.card (ResidueChoice w) : ℝ)⁻¹ *
          ((earlyPresieveSurvivors S w τ).card : ℝ) := by
            rw [Finset.mul_sum]

/-- Exact first moment, obtained solely by finite product counting. -/
theorem earlyPresieve_uniformMean_eq_exact (S w : ℕ) :
    earlyPresieveUniformMean S w =
      ∑ n ∈ Icc 1 S, earlyPresieveOneWeight w n := by
  rw [earlyPresieve_uniformMean_eq_weighted]
  simp_rw [earlyPresieve_card_eq_indicator_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => earlyPresieve_weighted_indicator w n

private theorem earlyPresieve_uniformSecondMoment_eq_weighted (S w : ℕ) :
    earlyPresieveUniformSecondMoment S w =
      ∑ τ : ResidueChoice w,
        (∏ p : SievePrime w, uniformFin (τ p)) *
          ((earlyPresieveSurvivors S w τ).card : ℝ) ^ 2 := by
  simp_rw [presieveSmall_uniform_product_mass]
  unfold earlyPresieveUniformSecondMoment
  rw [div_eq_mul_inv]
  calc
    (∑ τ : ResidueChoice w,
        ((earlyPresieveSurvivors S w τ).card : ℝ) ^ 2) *
          (Fintype.card (ResidueChoice w) : ℝ)⁻¹ =
      (Fintype.card (ResidueChoice w) : ℝ)⁻¹ *
        ∑ τ : ResidueChoice w,
          ((earlyPresieveSurvivors S w τ).card : ℝ) ^ 2 := by ring
    _ = ∑ τ : ResidueChoice w,
        (Fintype.card (ResidueChoice w) : ℝ)⁻¹ *
          ((earlyPresieveSurvivors S w τ).card : ℝ) ^ 2 := by
            rw [Finset.mul_sum]

/-- Exact second moment, including the diagonal and every rooted
two-point correlation. -/
theorem earlyPresieve_uniformSecondMoment_eq_exact (S w : ℕ) :
    earlyPresieveUniformSecondMoment S w =
      ∑ n ∈ Icc 1 S, ∑ m ∈ Icc 1 S,
        earlyPresievePairWeight w n m := by
  rw [earlyPresieve_uniformSecondMoment_eq_weighted]
  simp_rw [earlyPresieve_card_eq_indicator_sum, pow_two,
    Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ =>
    earlyPresieve_weighted_pair_indicator w n m

/-- Exact variance in terms of the rooted one- and two-point factors. -/
theorem earlyPresieve_uniformVariance_eq_exact (S w : ℕ) :
    earlyPresieveUniformVariance S w =
      (∑ n ∈ Icc 1 S, ∑ m ∈ Icc 1 S,
        earlyPresievePairWeight w n m) -
      (∑ n ∈ Icc 1 S, earlyPresieveOneWeight w n) ^ 2 := by
  unfold earlyPresieveUniformVariance
  rw [earlyPresieve_uniformMean_eq_exact,
    earlyPresieve_uniformSecondMoment_eq_exact]

/-! ### A finite uniform Chebyshev inequality -/

private theorem finite_uniform_chebyshev {Omega : Type*} [Fintype Omega]
    (f : Omega → ℝ) (hOmega : 0 < Fintype.card Omega)
    {u : ℝ} (hu : 0 < u) :
    (((univ : Finset Omega).filter fun x =>
        u ≤ |f x - (Fintype.card Omega : ℝ)⁻¹ * ∑ y : Omega, f y|).card : ℝ) /
        (Fintype.card Omega : ℝ) ≤
      (((Fintype.card Omega : ℝ)⁻¹ * ∑ x : Omega, f x ^ 2) -
          ((Fintype.card Omega : ℝ)⁻¹ * ∑ x : Omega, f x) ^ 2) /
        u ^ 2 := by
  let C : ℝ := Fintype.card Omega
  let mu : ℝ := C⁻¹ * ∑ x : Omega, f x
  let v : ℝ := C⁻¹ * ∑ x : Omega, f x ^ 2 - mu ^ 2
  let bad : Finset Omega := univ.filter fun x => u ≤ |f x - mu|
  have hCpos : 0 < C := by
    dsimp [C]
    exact_mod_cast hOmega
  have hCne : C ≠ 0 := hCpos.ne'
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
  have hdevsum : ∑ x : Omega, (f x - mu) ^ 2 = C * v := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [v, mu]
    field_simp [hCne]
    ring
  have hbad : u ^ 2 * (bad.card : ℝ) ≤
      ∑ x ∈ bad, (f x - mu) ^ 2 := by
    calc
      u ^ 2 * (bad.card : ℝ) = ∑ _x ∈ bad, u ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ x ∈ bad, (f x - mu) ^ 2 := by
        exact Finset.sum_le_sum fun x hx => by
          have hx' : u ≤ |f x - mu| := (Finset.mem_filter.mp hx).2
          exact sq_le_sq.mpr (by simpa [abs_of_pos hu] using hx')
  have hsubset : ∑ x ∈ bad, (f x - mu) ^ 2 ≤
      ∑ x : Omega, (f x - mu) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  have hmain : u ^ 2 * (bad.card : ℝ) ≤ C * v := by
    rw [← hdevsum]
    exact hbad.trans hsubset
  change (bad.card : ℝ) / C ≤ v / u ^ 2
  rw [div_le_div_iff₀ hCpos hu2]
  nlinarith

/-- Quantitative exceptional-mass bound for early choices.  No
fibrewise lower bound is asserted: only the uniform mass of choices
outside a band around the exact rooted mean is controlled. -/
theorem earlyPresieve_chebyshev (S w : ℕ) {u : ℝ} (hu : 0 < u) :
    (((univ : Finset (ResidueChoice w)).filter fun τ =>
        u ≤ |((earlyPresieveSurvivors S w τ).card : ℝ) -
          earlyPresieveUniformMean S w|).card : ℝ) /
        (Fintype.card (ResidueChoice w) : ℝ) ≤
      earlyPresieveUniformVariance S w / u ^ 2 := by
  have h := finite_uniform_chebyshev
    (fun τ : ResidueChoice w =>
      ((earlyPresieveSurvivors S w τ).card : ℝ))
    (residueChoice_card_pos w) hu
  have hcardR :
      (Fintype.card (ResidueChoice w) : ℝ) =
        ∏ p : SievePrime w, (p.val - 1 : ℕ) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    simp only [Fintype.card_fin]
    rw [Nat.cast_prod]
  rw [hcardR]
  unfold earlyPresieveUniformVariance earlyPresieveUniformSecondMoment
    earlyPresieveUniformMean
  rw [hcardR]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- The one-sided lower-count form needed after exposing the early
coordinates. -/
theorem earlyPresieve_lowerTail_chebyshev (S w : ℕ) {u : ℝ}
    (hu : 0 < u) :
    (((univ : Finset (ResidueChoice w)).filter fun τ =>
        u ≤ earlyPresieveUniformMean S w -
          ((earlyPresieveSurvivors S w τ).card : ℝ)).card : ℝ) /
        (Fintype.card (ResidueChoice w) : ℝ) ≤
      earlyPresieveUniformVariance S w / u ^ 2 := by
  let lower : Finset (ResidueChoice w) :=
    univ.filter fun τ => u ≤ earlyPresieveUniformMean S w -
      ((earlyPresieveSurvivors S w τ).card : ℝ)
  let dev : Finset (ResidueChoice w) :=
    univ.filter fun τ => u ≤
      |((earlyPresieveSurvivors S w τ).card : ℝ) -
        earlyPresieveUniformMean S w|
  have hsub : lower ⊆ dev := by
    intro τ hτ
    have hlow : u ≤ earlyPresieveUniformMean S w -
        ((earlyPresieveSurvivors S w τ).card : ℝ) :=
      (Finset.mem_filter.mp hτ).2
    have hnonneg : 0 ≤ earlyPresieveUniformMean S w -
        ((earlyPresieveSurvivors S w τ).card : ℝ) := hu.le.trans hlow
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [abs_sub_comm, abs_of_nonneg hnonneg]
    exact hlow
  have hcard : (lower.card : ℝ) ≤ (dev.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hden : 0 ≤ (Fintype.card (ResidueChoice w) : ℝ) :=
    Nat.cast_nonneg _
  have hdiv : (lower.card : ℝ) /
      (Fintype.card (ResidueChoice w) : ℝ) ≤
      (dev.card : ℝ) /
        (Fintype.card (ResidueChoice w) : ℝ) :=
    div_le_div_of_nonneg_right hcard hden
  change (lower.card : ℝ) /
      (Fintype.card (ResidueChoice w) : ℝ) ≤ _
  exact hdiv.trans (earlyPresieve_chebyshev S w hu)

theorem earlyPresieve_uniformVariance_nonneg (S w : ℕ) :
    0 ≤ earlyPresieveUniformVariance S w := by
  have h := earlyPresieve_chebyshev S w (u := 1) (by norm_num)
  have hmass : 0 ≤
      (((univ : Finset (ResidueChoice w)).filter fun τ =>
        (1 : ℝ) ≤ |((earlyPresieveSurvivors S w τ).card : ℝ) -
          earlyPresieveUniformMean S w|).card : ℝ) /
        (Fintype.card (ResidueChoice w) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simpa using hmass.trans h

end

end PrimeGapNormality.Prime
