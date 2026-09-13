import PrimeGapNormality.Prime.PresieveSmallEarlyMean

/-!
# The diagonal part of the rooted early-presieve variance

This file rewrites the exact variance from
`PresieveSmallGlobalLower` as a sum of rooted covariances and closes
its diagonal part at the paper scales.  The diagonal is harmless:
its total is at most the first moment, whereas the square of the main
term is larger by a factor tending to infinity.

This is deliberately not presented as the full global presieve
variance estimate.  The remaining term is the sum over distinct
candidate pairs.  In the paper that term is controlled by the
uniform Brun/CRT estimate through the early cutoff (and the
bounded-difference estimate is used only after conditioning, for the
later coordinates).  A direct bounded-difference estimate over all
early primes loses the required logarithmic factors.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Probability bounds for the exact rooted one-point factors -/

theorem earlyPresieveOneLocalMass_nonneg {w : ℕ}
    (p : SievePrime w) (n : ℕ) :
    0 ≤ earlyPresieveOneLocalMass p n := by
  rw [earlyPresieveOneLocalMass_eq_card]
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem earlyPresieveOneLocalMass_le_one {w : ℕ}
    (p : SievePrime w) (n : ℕ) :
    earlyPresieveOneLocalMass p n ≤ 1 := by
  have hp : Nat.Prime p.val := Nat.prime_of_mem_primesLE p.property
  have hdenN : 0 < p.val - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hdenR : (0 : ℝ) < (p.val - 1 : ℕ) := Nat.cast_pos.mpr hdenN
  rw [earlyPresieveOneLocalMass_eq_card]
  apply (div_le_one hdenR).2
  have hcardN :
      ((univ : Finset (Fin (p.val - 1))).filter fun a =>
        n % p.val ≠ a.val + 1).card ≤ p.val - 1 := by
    have hsub :
        ((univ : Finset (Fin (p.val - 1))).filter fun a =>
          n % p.val ≠ a.val + 1) ⊆ univ := by
      intro a _ha
      exact Finset.mem_univ a
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card hsub
  exact_mod_cast hcardN

theorem earlyPresieveOneWeight_nonneg (w n : ℕ) :
    0 ≤ earlyPresieveOneWeight w n := by
  unfold earlyPresieveOneWeight
  exact Finset.prod_nonneg fun p _ => earlyPresieveOneLocalMass_nonneg p n

theorem earlyPresieveOneWeight_le_one (w n : ℕ) :
    earlyPresieveOneWeight w n ≤ 1 := by
  unfold earlyPresieveOneWeight
  exact Finset.prod_le_one
    (fun p _ => earlyPresieveOneLocalMass_nonneg p n)
    (fun p _ => earlyPresieveOneLocalMass_le_one p n)

/-! ### Exact local identities retained by the rooted law -/

/-- Joint survival of a candidate with itself is its one-point
survival probability. -/
theorem earlyPresievePairLocalMass_self {w : ℕ}
    (p : SievePrime w) (n : ℕ) :
    earlyPresievePairLocalMass p n n =
      earlyPresieveOneLocalMass p n := by
  unfold earlyPresievePairLocalMass earlyPresieveOneLocalMass
  apply Finset.sum_congr rfl
  intro a _ha
  unfold earlyPresieveLocalIndicator
  by_cases h : n % p.val ≠ a.val + 1 <;> simp [h]

/-- A candidate divisible by the rooted prime survives that
coordinate automatically, so the joint factor reduces to the other
candidate's factor. -/
theorem earlyPresievePairLocalMass_of_dvd_left {w : ℕ}
    (p : SievePrime w) (n m : ℕ) (hn : p.val ∣ n) :
    earlyPresievePairLocalMass p n m =
      earlyPresieveOneLocalMass p m := by
  have hnmod : n % p.val = 0 := Nat.dvd_iff_mod_eq_zero.mp hn
  unfold earlyPresievePairLocalMass earlyPresieveOneLocalMass
  apply Finset.sum_congr rfl
  intro a _ha
  unfold earlyPresieveLocalIndicator
  simp [hnmod]

theorem earlyPresievePairLocalMass_of_dvd_right {w : ℕ}
    (p : SievePrime w) (n m : ℕ) (hm : p.val ∣ m) :
    earlyPresievePairLocalMass p n m =
      earlyPresieveOneLocalMass p n := by
  have hmmod : m % p.val = 0 := Nat.dvd_iff_mod_eq_zero.mp hm
  unfold earlyPresievePairLocalMass earlyPresieveOneLocalMass
  apply Finset.sum_congr rfl
  intro a _ha
  unfold earlyPresieveLocalIndicator
  simp [hmmod]

theorem earlyPresievePairWeight_self (w n : ℕ) :
    earlyPresievePairWeight w n n = earlyPresieveOneWeight w n := by
  unfold earlyPresievePairWeight earlyPresieveOneWeight
  apply Finset.prod_congr rfl
  intro p _hp
  exact earlyPresievePairLocalMass_self p n

/-! ### Covariance decomposition -/

/-- The covariance kernel of two candidate-survival indicators under
the uniform rooted residue law through `w`. -/
def earlyPresieveCovariance (w n m : ℕ) : ℝ :=
  earlyPresievePairWeight w n m -
    earlyPresieveOneWeight w n * earlyPresieveOneWeight w m

/-- The exact global variance is the double sum of its covariance
kernel.  This is the useful form for separating equal and distinct
candidate pairs. -/
theorem earlyPresieve_uniformVariance_eq_covariance_sum (S w : ℕ) :
    earlyPresieveUniformVariance S w =
      ∑ n ∈ Icc 1 S, ∑ m ∈ Icc 1 S,
        earlyPresieveCovariance w n m := by
  rw [earlyPresieve_uniformVariance_eq_exact]
  unfold earlyPresieveCovariance
  rw [pow_two, Finset.sum_mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← Finset.sum_sub_distrib]

/-- The diagonal covariance contribution. -/
def earlyPresieveDiagonalVariance (S w : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 S,
    (earlyPresieveOneWeight w n - earlyPresieveOneWeight w n ^ 2)

/-- The remaining covariance over distinct candidate pairs. -/
def earlyPresieveOffDiagonalCovariance (S w : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 S, ∑ m ∈ (Icc 1 S).erase n,
    earlyPresieveCovariance w n m

theorem earlyPresieveCovariance_self (w n : ℕ) :
    earlyPresieveCovariance w n n =
      earlyPresieveOneWeight w n - earlyPresieveOneWeight w n ^ 2 := by
  rw [earlyPresieveCovariance, earlyPresievePairWeight_self, pow_two]

/-- Exact separation of the harmless diagonal from the genuine
two-point correlation problem. -/
theorem earlyPresieve_uniformVariance_eq_diagonal_add_offDiagonal
    (S w : ℕ) :
    earlyPresieveUniformVariance S w =
      earlyPresieveDiagonalVariance S w +
        earlyPresieveOffDiagonalCovariance S w := by
  rw [earlyPresieve_uniformVariance_eq_covariance_sum]
  unfold earlyPresieveDiagonalVariance earlyPresieveOffDiagonalCovariance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have herase := Finset.sum_erase_add
    (s := Icc 1 S) (f := fun m => earlyPresieveCovariance w n m) hn
  calc
    ∑ m ∈ Icc 1 S, earlyPresieveCovariance w n m =
        (∑ m ∈ (Icc 1 S).erase n, earlyPresieveCovariance w n m) +
          earlyPresieveCovariance w n n := herase.symm
    _ = (earlyPresieveOneWeight w n - earlyPresieveOneWeight w n ^ 2) +
        ∑ m ∈ (Icc 1 S).erase n,
          earlyPresieveCovariance w n m := by
      rw [earlyPresieveCovariance_self]
      ring

theorem earlyPresieveDiagonalVariance_nonneg (S w : ℕ) :
    0 ≤ earlyPresieveDiagonalVariance S w := by
  unfold earlyPresieveDiagonalVariance
  apply Finset.sum_nonneg
  intro n _hn
  have h0 := earlyPresieveOneWeight_nonneg w n
  have h1 := earlyPresieveOneWeight_le_one w n
  nlinarith

/-- The diagonal variance is bounded by the exact first moment. -/
theorem earlyPresieveDiagonalVariance_le_mean (S w : ℕ) :
    earlyPresieveDiagonalVariance S w ≤
      earlyPresieveUniformMean S w := by
  rw [earlyPresieve_uniformMean_eq_exact]
  unfold earlyPresieveDiagonalVariance
  apply Finset.sum_le_sum
  intro n _hn
  exact sub_le_self _ (sq_nonneg _)

/-! ### The diagonal is negligible at the paper scales -/

theorem tendsto_earlyPresieveDiagonalVariance_div_main_sq
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      earlyPresieveDiagonalVariance (ahlSmall_window κ X)
          (presieveW (windowG X)) /
        (((ahlSmall_window κ X : ℝ) *
          eulerProdNat (presieveW (windowG X))) ^ 2))
      atTop (nhds 0) := by
  let main : ℕ → ℝ := fun X =>
    (ahlSmall_window κ X : ℝ) *
      eulerProdNat (presieveW (windowG X))
  let mean : ℕ → ℝ := fun X =>
    earlyPresieveUniformMean (ahlSmall_window κ X)
      (presieveW (windowG X))
  have hmain : Tendsto main atTop atTop := by
    simpa only [main] using tendsto_ahlSmall_earlyPresieve_main_atTop hκ
  have hmean : Tendsto (fun X => mean X / main X) atTop (nhds 1) := by
    simpa only [mean, main] using
      tendsto_earlyPresieveUniformMean_div_main hκ
  have hinv : Tendsto (fun X => (main X)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hmain
  have hmajor' : Tendsto (fun X =>
      (mean X / main X) * (main X)⁻¹) atTop (nhds 0) := by
    simpa using hmean.mul hinv
  have hpos : ∀ᶠ X in atTop, 0 < main X :=
    hmain.eventually (eventually_gt_atTop 0)
  have hmajor : Tendsto (fun X => mean X / main X ^ 2)
      atTop (nhds 0) := by
    apply hmajor'.congr'
    filter_upwards [hpos] with X hX
    have hX0 : main X ≠ 0 := hX.ne'
    field_simp [hX0]
  refine squeeze_zero' ?_ ?_ hmajor
  · exact Eventually.of_forall fun X =>
      div_nonneg (earlyPresieveDiagonalVariance_nonneg _ _)
        (sq_nonneg _)
  · exact Eventually.of_forall fun X =>
      div_le_div_of_nonneg_right
        (earlyPresieveDiagonalVariance_le_mean _ _) (sq_nonneg _)

end

end PrimeGapNormality.Prime
