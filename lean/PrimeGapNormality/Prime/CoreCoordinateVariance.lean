import PrimeGapNormality.Prime.ResidueHoeffding

/-!
# The exact quarter-variance bounded-difference inequality

Finite laws are the actual nonnegative, normalized coordinate masses from
`ResidueHoeffding`. Variance is the actual weighted centered square. A
finite Popoviciu estimate and the exact conditional-variance decomposition
give the constant `1/4`, without passing through an exponential tail bound.
-/

namespace PrimeGapNormality.Prime

open Finset
open scoped Classical

set_option maxHeartbeats 800000

/-- Actual variance of a function under a finite law. -/
noncomputable def finVariance {Ω : Type*} [Fintype Ω] (μ F : Ω → ℝ) : ℝ :=
  finExpect μ (fun x => (F x - finExpect μ F) ^ 2)

/-- Actual variance under the independent coordinate product law. -/
noncomputable def piVariance {n : ℕ} {α : Fin n → Type} [∀ i, Fintype (α i)]
    (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) : ℝ :=
  finVariance (piMass μ) F

private theorem finExpect_add_v {Ω : Type*} [Fintype Ω] (μ F G : Ω → ℝ) :
    finExpect μ (fun x => F x + G x) = finExpect μ F + finExpect μ G := by
  simp [finExpect, mul_add, sum_add_distrib]

private theorem finExpect_sub_v {Ω : Type*} [Fintype Ω] (μ F G : Ω → ℝ) :
    finExpect μ (fun x => F x - G x) = finExpect μ F - finExpect μ G := by
  simp [finExpect, mul_sub, sum_sub_distrib]

private theorem finExpect_mul_v {Ω : Type*} [Fintype Ω] (μ F : Ω → ℝ) (a : ℝ) :
    finExpect μ (fun x => a * F x) = a * finExpect μ F := by
  unfold finExpect
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  ring

private theorem finExpect_mono_v {Ω : Type*} [Fintype Ω] (μ F G : Ω → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (h : ∀ x, F x ≤ G x) : finExpect μ F ≤ finExpect μ G :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hμ x)

theorem finExpect_centered_sq {Ω : Type*} [Fintype Ω] (μ F : Ω → ℝ)
    (hμ1 : ∑ x, μ x = 1) (a : ℝ) :
    finExpect μ (fun x => (F x - a) ^ 2) =
      finExpect μ (fun x => F x ^ 2) - 2 * a * finExpect μ F + a ^ 2 := by
  have hf : (fun x => (F x - a) ^ 2) =
      fun x => (F x ^ 2 - (2 * a) * F x) + a ^ 2 := by
    funext x
    ring
  rw [hf, finExpect_add_v, finExpect_sub_v, finExpect_mul_v,
    finExpect_const μ _ hμ1]

theorem finVariance_eq_secondMoment {Ω : Type*} [Fintype Ω] (μ F : Ω → ℝ)
    (hμ1 : ∑ x, μ x = 1) :
    finVariance μ F = finExpect μ (fun x => F x ^ 2) - (finExpect μ F) ^ 2 := by
  rw [finVariance, finExpect_centered_sq μ F hμ1]
  ring

/-- Finite Popoviciu inequality, proved by centering at the interval midpoint. -/
theorem finVariance_le_quarter_of_interval {Ω : Type*} [Fintype Ω]
    (μ F : Ω → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (a c : ℝ) (hF : ∀ x, a ≤ F x ∧ F x ≤ a + c) :
    finVariance μ F ≤ c ^ 2 / 4 := by
  have hs : ∀ x, (F x - (a + c / 2)) ^ 2 ≤ c ^ 2 / 4 := by
    intro x
    have := mul_nonneg (sub_nonneg.mpr (hF x).1) (sub_nonneg.mpr (hF x).2)
    nlinarith
  have hav := finExpect_mono_v μ (fun x => (F x - (a + c / 2)) ^ 2)
    (fun _ => c ^ 2 / 4) hμ0 hs
  rw [finExpect_const μ _ hμ1, finExpect_centered_sq μ F hμ1] at hav
  rw [finVariance_eq_secondMoment μ F hμ1]
  nlinarith [sq_nonneg (finExpect μ F - (a + c / 2))]

theorem finVariance_le_quarter_of_diameter {Ω : Type*} [Fintype Ω]
    (μ F : Ω → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (c : ℝ) (hc : 0 ≤ c) (hF : ∀ x y, |F x - F y| ≤ c) :
    finVariance μ F ≤ c ^ 2 / 4 := by
  letI : Nonempty Ω := nonempty_of_mass_one hμ1
  obtain ⟨a, ha⟩ := interval_slice_of_lipschitz F hc hF
  exact finVariance_le_quarter_of_interval μ F hμ0 hμ1 a c ha

/-- Exact one-coordinate conditional-variance identity for the actual finite sums. -/
theorem piVariance_snoc {n : ℕ} {α : Fin (n + 1) → Type}
    [∀ i, Fintype (α i)] (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ)
    (hμ1 : ∀ i, ∑ a, μ i a = 1) :
    piVariance μ F =
      piExpect (fun i a => μ i.castSucc a)
        (fun y => finVariance (μ (Fin.last n)) (fun a => F (Fin.snoc y a))) +
      piVariance (fun i a => μ i.castSucc a) (snocCondExpect μ F) := by
  let μ' : ∀ i : Fin n, α i.castSucc → ℝ := fun i a => μ i.castSucc a
  have hm : ∑ y, piMass μ' y = 1 :=
    piMass_sum n (fun i => α i.castSucc) μ' (fun i => hμ1 i.castSucc)
  have hvar : ∀ y : ∀ i : Fin n, α i.castSucc,
      finVariance (μ (Fin.last n)) (fun a => F (Fin.snoc y a)) =
        snocCondExpect μ (fun x => F x ^ 2) y - snocCondExpect μ F y ^ 2 := by
    intro y
    exact finVariance_eq_secondMoment _ _ (hμ1 (Fin.last n))
  rw [piVariance, finVariance_eq_secondMoment _ _ (piMass_sum _ _ μ hμ1)]
  change piExpect μ (fun x => F x ^ 2) - piExpect μ F ^ 2 = _
  rw [piExpect_snoc μ (fun x => F x ^ 2), piExpect_snoc μ F]
  simp_rw [hvar]
  change finExpect (piMass μ') (snocCondExpect μ (fun x => F x ^ 2)) -
      finExpect (piMass μ') (snocCondExpect μ F) ^ 2 =
    finExpect (piMass μ') (fun y => snocCondExpect μ (fun x => F x ^ 2) y -
      snocCondExpect μ F y ^ 2) + finVariance (piMass μ') (snocCondExpect μ F)
  rw [finExpect_sub_v, finVariance_eq_secondMoment _ _ hm]
  ring

/-- Exact quarter-variance estimate for every finite independent product law. -/
theorem piFin_bounded_diff_variance :
    ∀ (n : ℕ) (α : Fin n → Type) [∀ i, Fintype (α i)]
      (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) (c : Fin n → ℝ),
      (∀ i a, 0 ≤ μ i a) →
      (∀ i, ∑ a : α i, μ i a = 1) →
      (∀ i, 0 ≤ c i) →
      (∀ (x : ∀ i, α i) (i : Fin n) (a b : α i),
        |F (Function.update x i a) - F (Function.update x i b)| ≤ c i) →
      piVariance μ F ≤ (∑ i : Fin n, c i ^ 2) / 4 := by
  intro n
  induction n with
  | zero =>
      intro α _ μ F c _ _ _ _
      letI : Unique (∀ i : Fin 0, α i) := Pi.uniqueOfIsEmpty _
      have hmass : piMass μ default = 1 := by simp [piMass]
      simp [piVariance, finVariance, finExpect, Fintype.sum_unique, hmass]
  | succ n ih =>
      intro α _ μ F c hμ0 hμ1 hc hLip
      let μ' : ∀ i : Fin n, α i.castSucc → ℝ := fun i a => μ i.castSucc a
      let G := snocCondExpect μ F
      have hm : ∑ y, piMass μ' y = 1 :=
        piMass_sum n (fun i => α i.castSucc) μ' (fun i => hμ1 i.castSucc)
      have hm0 : ∀ y, 0 ≤ piMass μ' y :=
        fun y => prod_nonneg fun i _ => hμ0 i.castSucc (y i)
      have hLipG : ∀ (y : ∀ i : Fin n, α i.castSucc) (i : Fin n)
          (a b : α i.castSucc),
          |G (Function.update y i a) - G (Function.update y i b)| ≤ c i.castSucc := by
        intro y i a b
        have hpt : ∀ z : α (Fin.last n),
            |F (Fin.snoc (Function.update y i a) z) -
              F (Fin.snoc (Function.update y i b) z)| ≤ c i.castSucc := by
          intro z
          simpa only [Fin.snoc_update] using hLip (Fin.snoc y z) i.castSucc a b
        have hsub : G (Function.update y i a) - G (Function.update y i b) =
            ∑ z : α (Fin.last n), μ (Fin.last n) z *
              (F (Fin.snoc (Function.update y i a) z) -
                F (Fin.snoc (Function.update y i b) z)) := by
          simp [G, snocCondExpect, mul_sub, sum_sub_distrib]
        rw [hsub]
        calc
          _ ≤ ∑ z : α (Fin.last n), |μ (Fin.last n) z *
              (F (Fin.snoc (Function.update y i a) z) -
                F (Fin.snoc (Function.update y i b) z))| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ z : α (Fin.last n), μ (Fin.last n) z * c i.castSucc := by
            apply sum_le_sum
            intro z _
            rw [abs_mul, abs_of_nonneg (hμ0 (Fin.last n) z)]
            exact mul_le_mul_of_nonneg_left (hpt z) (hμ0 (Fin.last n) z)
          _ = c i.castSucc := by rw [← sum_mul, hμ1, one_mul]
      have hG := ih (fun i => α i.castSucc) μ' G (fun i => c i.castSucc)
        (fun i a => hμ0 i.castSucc a) (fun i => hμ1 i.castSucc)
        (fun i => hc i.castSucc) hLipG
      have hslice : ∀ y : ∀ i : Fin n, α i.castSucc,
          finVariance (μ (Fin.last n)) (fun a => F (Fin.snoc y a)) ≤
            c (Fin.last n) ^ 2 / 4 := by
        intro y
        apply finVariance_le_quarter_of_diameter _ _ (hμ0 (Fin.last n))
          (hμ1 (Fin.last n)) _ (hc (Fin.last n))
        intro a b
        simpa only [Fin.update_snoc_last] using hLip (Fin.snoc y a) (Fin.last n) a b
      have hav : piExpect μ'
          (fun y => finVariance (μ (Fin.last n)) (fun a => F (Fin.snoc y a))) ≤
          c (Fin.last n) ^ 2 / 4 := by
        exact (finExpect_mono_v (piMass μ') _ _ hm0 hslice).trans_eq
          (finExpect_const (piMass μ') _ hm)
      rw [piVariance_snoc μ F hμ1, Fin.sum_univ_castSucc]
      change piExpect μ' _ + piVariance μ' G ≤ _
      linarith

/-- Fully expanded endpoint: there is no abstract variance or tail hypothesis. -/
theorem piFin_centered_square_le_quarter {n : ℕ} {α : Fin n → Type}
    [∀ i, Fintype (α i)] (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ)
    (c : Fin n → ℝ) (hμ0 : ∀ i a, 0 ≤ μ i a)
    (hμ1 : ∀ i, ∑ a : α i, μ i a = 1) (hc : ∀ i, 0 ≤ c i)
    (hLip : ∀ (x : ∀ i, α i) (i : Fin n) (a b : α i),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i) :
    (∑ x : (∀ i, α i), (∏ i, μ i (x i)) *
      (F x - ∑ y : (∀ i, α i), (∏ i, μ i (y i)) * F y) ^ 2) ≤
      (∑ i : Fin n, c i ^ 2) / 4 :=
  piFin_bounded_diff_variance n α μ F c hμ0 hμ1 hc hLip

end PrimeGapNormality.Prime
