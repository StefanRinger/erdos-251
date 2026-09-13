import PrimeGapNormality.Prime.SelbergHarmonicJ
import Mathlib.NumberTheory.Divisors

/-!
# The finite optimal Selberg weights

For the finite Selberg upper-bound argument, put

`y r = μ(r) / (φ(r) J(R))` and
`lambda d = d * ∑_{1 ≤ m ≤ R / d} μ(m) y(d*m)`.

The support finset below records precisely the summands for which `d*m` is
squarefree.  On this support, `d` and `m` are squarefree and coprime.  The
product map `(e,m) ↦ e*m`, for `e ∣ d`, is injective; this is the finite
combinatorial core used to compare the absolute weight with `selbergJR R`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace PrimeGapNormality.Prime

noncomputable section

/-- The finite diagonal variables used by the optimal Selberg weight. -/
def finiteSelbergY (R r : ℕ) : ℝ :=
  (ArithmeticFunction.moebius r : ℝ) / ((r.totient : ℝ) * selbergJR R)

/-- The finite optimal Selberg coefficient at `d`. -/
def finiteSelbergWeight (R d : ℕ) : ℝ :=
  (d : ℝ) * ∑ m ∈ Icc 1 (R / d),
    (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R (d * m)

/-- The nonzero-support candidate for the inner sum defining
`finiteSelbergWeight`. -/
def finiteSelbergWeightSupport (R d : ℕ) : Finset ℕ :=
  (Icc 1 (R / d)).filter fun m => Squarefree (d * m)

/-- Pairs used in the comparison with `J(R)`: a divisor `e` of `d` and an
inner variable `m` for which `d*m` is squarefree. -/
def finiteSelbergPairs (R d : ℕ) : Finset (ℕ × ℕ) :=
  d.divisors.product (finiteSelbergWeightSupport R d)

/-- The positive inner mass appearing after taking the absolute value of a
squarefree Selberg coefficient. -/
def finiteSelbergCoprimeMass (R d : ℕ) : ℝ :=
  ∑ m ∈ finiteSelbergWeightSupport R d, (m.totient : ℝ)⁻¹

theorem finiteSelbergY_eq_zero_of_not_squarefree {R r : ℕ}
    (hr : ¬ Squarefree r) :
    finiteSelbergY R r = 0 := by
  rw [finiteSelbergY, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hr]
  simp

theorem finiteSelbergWeight_eq_zero_of_not_squarefree {R d : ℕ}
    (hd : ¬ Squarefree d) :
    finiteSelbergWeight R d = 0 := by
  unfold finiteSelbergWeight
  have hsum :
      ∑ m ∈ Icc 1 (R / d),
          (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R (d * m) = 0 := by
    apply sum_eq_zero
    intro m hm
    rw [finiteSelbergY_eq_zero_of_not_squarefree]
    · simp
    · exact fun hdm => hd hdm.of_mul_left
  rw [hsum, mul_zero]

theorem finiteSelbergWeight_eq_zero_of_lt {R d : ℕ} (hRd : R < d) :
    finiteSelbergWeight R d = 0 := by
  have hdiv : R / d = 0 := Nat.div_eq_of_lt hRd
  simp [finiteSelbergWeight, hdiv]

theorem finiteSelbergWeightSupport_spec {R d m : ℕ}
    (hm : m ∈ finiteSelbergWeightSupport R d) :
    m ∈ Icc 1 (R / d) ∧ Squarefree (d * m) :=
  mem_filter.mp hm

theorem finiteSelbergWeightSupport_coprime {R d m : ℕ}
    (hm : m ∈ finiteSelbergWeightSupport R d) :
    d.Coprime m :=
  (Nat.squarefree_mul_iff.mp (finiteSelbergWeightSupport_spec hm).2).1

theorem finiteSelbergWeightSupport_squarefree_left {R d m : ℕ}
    (hm : m ∈ finiteSelbergWeightSupport R d) :
    Squarefree d :=
  (Nat.squarefree_mul_iff.mp (finiteSelbergWeightSupport_spec hm).2).2.1

theorem finiteSelbergWeightSupport_squarefree_right {R d m : ℕ}
    (hm : m ∈ finiteSelbergWeightSupport R d) :
    Squarefree m :=
  (Nat.squarefree_mul_iff.mp (finiteSelbergWeightSupport_spec hm).2).2.2

/-- Distinct pairs `(e,m)`, with `e ∣ d` and `d*m` squarefree, have
distinct products.  Coprimality recovers each divisor component by Euclid's
lemma; cancellation then recovers `m`. -/
theorem finiteSelbergPairs_mul_injOn (R d : ℕ) :
    Set.InjOn (fun z : ℕ × ℕ => z.1 * z.2) (finiteSelbergPairs R d : Set (ℕ × ℕ)) := by
  intro z₁ hz₁ z₂ hz₂ hprod
  rcases z₁ with ⟨e₁, m₁⟩
  rcases z₂ with ⟨e₂, m₂⟩
  change e₁ * m₁ = e₂ * m₂ at hprod
  change (e₁, m₁) ∈ finiteSelbergPairs R d at hz₁
  change (e₂, m₂) ∈ finiteSelbergPairs R d at hz₂
  rw [finiteSelbergPairs] at hz₁ hz₂
  rcases Finset.mem_product.mp hz₁ with ⟨he₁, hm₁⟩
  rcases Finset.mem_product.mp hz₂ with ⟨he₂, hm₂⟩
  have he₁d : e₁ ∣ d := Nat.dvd_of_mem_divisors he₁
  have he₂d : e₂ ∣ d := Nat.dvd_of_mem_divisors he₂
  have hdm₁ : d.Coprime m₁ := finiteSelbergWeightSupport_coprime hm₁
  have hdm₂ : d.Coprime m₂ := finiteSelbergWeightSupport_coprime hm₂
  have he₁m₂ : e₁.Coprime m₂ := Nat.Coprime.of_dvd_left he₁d hdm₂
  have he₂m₁ : e₂.Coprime m₁ := Nat.Coprime.of_dvd_left he₂d hdm₁
  have he₁e₂ : e₁ ∣ e₂ := by
    apply he₁m₂.dvd_of_dvd_mul_right
    rw [← hprod]
    exact dvd_mul_right e₁ m₁
  have he₂e₁ : e₂ ∣ e₁ := by
    apply he₂m₁.dvd_of_dvd_mul_right
    rw [hprod]
    exact dvd_mul_right e₂ m₂
  have he : e₁ = e₂ := Nat.dvd_antisymm he₁e₂ he₂e₁
  subst e₂
  have hd0 : d ≠ 0 := (Nat.mem_divisors.mp he₁).2
  have he₁0 : e₁ ≠ 0 := by
    intro he₁
    subst e₁
    exact hd0 (zero_dvd_iff.mp he₁d)
  have hm : m₁ = m₂ := mul_left_cancel₀ he₁0 hprod
  subst m₂
  rfl

theorem finiteSelbergPairs_mul_mem_Icc {R d : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ finiteSelbergPairs R d) :
    z.1 * z.2 ∈ Icc 1 R := by
  rcases z with ⟨e, m⟩
  rw [finiteSelbergPairs] at hz
  rcases Finset.mem_product.mp hz with ⟨he, hm⟩
  have hed : e ∣ d := Nat.dvd_of_mem_divisors he
  have hd0 : d ≠ 0 := (Nat.mem_divisors.mp he).2
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos hed hdpos
  have hmIcc := (finiteSelbergWeightSupport_spec hm).1
  have hmpos : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hmIcc).1
  have he_le : e ≤ d := Nat.le_of_dvd hdpos hed
  have hm_le : m ≤ R / d := (mem_Icc.mp hmIcc).2
  refine mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hepos.ne' hmpos.ne'), ?_⟩
  calc
    e * m ≤ d * (R / d) := Nat.mul_le_mul he_le hm_le
    _ ≤ R := by simpa [Nat.mul_comm] using Nat.mul_div_le R d

theorem finiteSelbergPairs_mul_squarefree {R d : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ finiteSelbergPairs R d) :
    Squarefree (z.1 * z.2) := by
  rcases z with ⟨e, m⟩
  rw [finiteSelbergPairs] at hz
  rcases Finset.mem_product.mp hz with ⟨he, hm⟩
  have hed : e ∣ d := Nat.dvd_of_mem_divisors he
  have hdm : Squarefree (d * m) := (finiteSelbergWeightSupport_spec hm).2
  have hdsq : Squarefree d := hdm.of_mul_left
  have hmsq : Squarefree m := hdm.of_mul_right
  have hcop : e.Coprime m :=
    Nat.Coprime.of_dvd_left hed (Nat.coprime_of_squarefree_mul hdm)
  exact (Nat.squarefree_mul hcop).mpr ⟨hdsq.squarefree_of_dvd hed, hmsq⟩

theorem finiteSelbergPairs_mul_term {R d : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ finiteSelbergPairs R d) :
    selbergJR_term (z.1 * z.2) = (((z.1 * z.2).totient : ℝ))⁻¹ :=
  selbergJR_term_eq_inv_totient (finiteSelbergPairs_mul_squarefree hz)

/-- The distinct squarefree products supplied by `finiteSelbergPairs` form a
subsum of `J(R)`. -/
theorem finiteSelbergPairs_sum_le_selbergJR (R d : ℕ) :
    ∑ z ∈ finiteSelbergPairs R d, selbergJR_term (z.1 * z.2) ≤ selbergJR R := by
  let f : ℕ × ℕ → ℕ := fun z => z.1 * z.2
  have hinj : Set.InjOn f (finiteSelbergPairs R d : Set (ℕ × ℕ)) := by
    simpa [f] using finiteSelbergPairs_mul_injOn R d
  have hsubset : (finiteSelbergPairs R d).image f ⊆ Icc 1 R := by
    intro n hn
    rcases mem_image.mp hn with ⟨z, hz, rfl⟩
    simpa [f] using finiteSelbergPairs_mul_mem_Icc hz
  calc
    ∑ z ∈ finiteSelbergPairs R d, selbergJR_term (z.1 * z.2) =
        ∑ n ∈ (finiteSelbergPairs R d).image f, selbergJR_term n := by
          rw [sum_image hinj]
    _ ≤ ∑ n ∈ Icc 1 R, selbergJR_term n := by
      apply sum_le_sum_of_subset_of_nonneg hsubset
      intro n hnIcc hnImage
      exact selbergJR_term_nonneg
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hnIcc).1)
    _ = selbergJR R := rfl

/-- For squarefree `d`, the divisor reciprocal identity used by the finite
Selberg weight estimate. -/
theorem sum_divisors_inv_totient_eq_div_totient {d : ℕ} (hd : Squarefree d) :
    ∑ e ∈ d.divisors, (e.totient : ℝ)⁻¹ = (d : ℝ) * (d.totient : ℝ)⁻¹ := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hreverse :
      ∑ e ∈ d.divisors, ((d / e).totient : ℝ)⁻¹ =
        ∑ e ∈ d.divisors, (e.totient : ℝ)⁻¹ :=
    Nat.sum_div_divisors d (fun e => (e.totient : ℝ)⁻¹)
  rw [← hreverse]
  calc
    ∑ e ∈ d.divisors, ((d / e).totient : ℝ)⁻¹ =
        ∑ e ∈ d.divisors, (e.totient : ℝ) * (d.totient : ℝ)⁻¹ := by
      apply sum_congr rfl
      intro e he
      have hed : e ∣ d := Nat.dvd_of_mem_divisors he
      have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos hed hdpos
      have hqpos : 0 < d / e := Nat.div_pos (Nat.le_of_dvd hdpos hed) hepos
      have hprod : Squarefree (e * (d / e)) := by
        rw [Nat.mul_div_cancel' hed]
        exact hd
      have hcop : e.Coprime (d / e) := Nat.coprime_of_squarefree_mul hprod
      have htot : d.totient = e.totient * (d / e).totient := by
        rw [← Nat.totient_mul hcop, Nat.mul_div_cancel' hed]
      have hephi : (e.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hepos).ne'
      have hqphi : ((d / e).totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hqpos).ne'
      rw [htot, Nat.cast_mul]
      field_simp
    _ = (∑ e ∈ d.divisors, (e.totient : ℝ)) * (d.totient : ℝ)⁻¹ := by
      rw [sum_mul]
    _ = (d : ℝ) * (d.totient : ℝ)⁻¹ := by
      rw [← Nat.cast_sum, Nat.sum_totient]

theorem finiteSelbergPairs_sum_eq (R d : ℕ) :
    ∑ z ∈ finiteSelbergPairs R d, selbergJR_term (z.1 * z.2) =
      (∑ e ∈ d.divisors, (e.totient : ℝ)⁻¹) * finiteSelbergCoprimeMass R d := by
  calc
    ∑ z ∈ finiteSelbergPairs R d, selbergJR_term (z.1 * z.2) =
        ∑ e ∈ d.divisors, ∑ m ∈ finiteSelbergWeightSupport R d,
          selbergJR_term (e * m) := by
      rw [finiteSelbergPairs]
      exact Finset.sum_product d.divisors (finiteSelbergWeightSupport R d)
        (fun z => selbergJR_term (z.1 * z.2))
    _ = ∑ e ∈ d.divisors, ∑ m ∈ finiteSelbergWeightSupport R d,
          (e.totient : ℝ)⁻¹ * (m.totient : ℝ)⁻¹ := by
      apply sum_congr rfl
      intro e he
      apply sum_congr rfl
      intro m hm
      have hed : e ∣ d := Nat.dvd_of_mem_divisors he
      have hdm : Squarefree (d * m) := (finiteSelbergWeightSupport_spec hm).2
      have hcop : e.Coprime m :=
        Nat.Coprime.of_dvd_left hed (Nat.coprime_of_squarefree_mul hdm)
      have hem : Squarefree (e * m) :=
        (Nat.squarefree_mul hcop).mpr
          ⟨hdm.of_mul_left.squarefree_of_dvd hed, hdm.of_mul_right⟩
      rw [selbergJR_term_eq_inv_totient hem, Nat.totient_mul hcop, Nat.cast_mul,
        mul_inv_rev, mul_comm]
    _ = (∑ e ∈ d.divisors, (e.totient : ℝ)⁻¹) *
        finiteSelbergCoprimeMass R d := by
      unfold finiteSelbergCoprimeMass
      rw [sum_mul]
      apply sum_congr rfl
      intro e he
      rw [mul_sum]

/-- The exact finite subsum comparison behind `|lambda d| ≤ 1`. -/
theorem finiteSelberg_scaled_mass_le_selbergJR (R : ℕ) {d : ℕ}
    (hd : Squarefree d) :
    (d : ℝ) * (d.totient : ℝ)⁻¹ * finiteSelbergCoprimeMass R d ≤ selbergJR R := by
  calc
    (d : ℝ) * (d.totient : ℝ)⁻¹ * finiteSelbergCoprimeMass R d =
        (∑ e ∈ d.divisors, (e.totient : ℝ)⁻¹) * finiteSelbergCoprimeMass R d := by
          rw [sum_divisors_inv_totient_eq_div_totient hd]
    _ = ∑ z ∈ finiteSelbergPairs R d, selbergJR_term (z.1 * z.2) :=
      (finiteSelbergPairs_sum_eq R d).symm
    _ ≤ selbergJR R := finiteSelbergPairs_sum_le_selbergJR R d

private theorem finiteSelberg_inner_sum_eq_support (R d : ℕ) :
    ∑ m ∈ Icc 1 (R / d),
        (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R (d * m) =
      ∑ m ∈ finiteSelbergWeightSupport R d,
        (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R (d * m) := by
  symm
  apply sum_subset
  · exact filter_subset _ _
  · intro m hmIcc hmSupport
    have hnot : ¬ Squarefree (d * m) := by
      intro hsq
      exact hmSupport (mem_filter.mpr ⟨hmIcc, hsq⟩)
    rw [finiteSelbergY_eq_zero_of_not_squarefree hnot]
    simp

private theorem finiteSelberg_inner_term_eq {R d m : ℕ}
    (hm : m ∈ finiteSelbergWeightSupport R d) :
    (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R (d * m) =
      (ArithmeticFunction.moebius d : ℝ) * (d.totient : ℝ)⁻¹ *
        (m.totient : ℝ)⁻¹ * (selbergJR R)⁻¹ := by
  have hcop : d.Coprime m := finiteSelbergWeightSupport_coprime hm
  have hmsq : Squarefree m := finiteSelbergWeightSupport_squarefree_right hm
  have hmu : ArithmeticFunction.moebius (d * m) =
      ArithmeticFunction.moebius d * ArithmeticFunction.moebius m :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hmusqZ : ArithmeticFunction.moebius m ^ 2 = 1 :=
    ArithmeticFunction.moebius_sq_eq_one_of_squarefree hmsq
  have hmusqR :
      (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius m : ℝ) = 1 := by
    simpa [pow_two] using congrArg (fun z : ℤ => (z : ℝ)) hmusqZ
  rw [finiteSelbergY, hmu, Nat.totient_mul hcop, Int.cast_mul, Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    (ArithmeticFunction.moebius m : ℝ) *
        ((ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius m : ℝ) *
          ((selbergJR R)⁻¹ * ((m.totient : ℝ)⁻¹ * (d.totient : ℝ)⁻¹))) =
        (ArithmeticFunction.moebius d : ℝ) *
          ((ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius m : ℝ)) *
          (d.totient : ℝ)⁻¹ * (m.totient : ℝ)⁻¹ * (selbergJR R)⁻¹ := by
            ring
    _ = (ArithmeticFunction.moebius d : ℝ) * (d.totient : ℝ)⁻¹ *
        (m.totient : ℝ)⁻¹ * (selbergJR R)⁻¹ := by
      rw [hmusqR]
      ring

theorem finiteSelbergWeight_eq_of_squarefree {R d : ℕ} (hd : Squarefree d) :
    finiteSelbergWeight R d =
      (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) * (d.totient : ℝ)⁻¹ *
        (selbergJR R)⁻¹ * finiteSelbergCoprimeMass R d := by
  rw [finiteSelbergWeight, finiteSelberg_inner_sum_eq_support]
  calc
    (d : ℝ) * ∑ m ∈ finiteSelbergWeightSupport R d,
        (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R (d * m) =
      (d : ℝ) * ∑ m ∈ finiteSelbergWeightSupport R d,
        (ArithmeticFunction.moebius d : ℝ) * (d.totient : ℝ)⁻¹ *
          (m.totient : ℝ)⁻¹ * (selbergJR R)⁻¹ := by
            apply congrArg ((d : ℝ) * ·)
            apply sum_congr rfl
            intro m hm
            exact finiteSelberg_inner_term_eq hm
    _ = (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) * (d.totient : ℝ)⁻¹ *
        (selbergJR R)⁻¹ * finiteSelbergCoprimeMass R d := by
      unfold finiteSelbergCoprimeMass
      rw [mul_sum, mul_sum]
      apply sum_congr rfl
      intro m hm
      ring

/-- Every finite optimal Selberg coefficient has absolute value at most one.
No side condition on `d` is needed: nonsquarefree `d`, and also `d > R`,
give zero coefficients. -/
theorem finiteSelbergWeight_abs_le_one {R d : ℕ} (hR : 1 ≤ R) :
    |finiteSelbergWeight R d| ≤ 1 := by
  by_cases hd : Squarefree d
  · let A : ℝ :=
      (d : ℝ) * (d.totient : ℝ)⁻¹ * finiteSelbergCoprimeMass R d
    have hJ : 0 < selbergJR R := selbergJR_pos hR
    have hmass : 0 ≤ finiteSelbergCoprimeMass R d := by
      apply sum_nonneg
      intro m hm
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    have hA : 0 ≤ A := by
      dsimp [A]
      positivity
    have hAle : A ≤ selbergJR R := by
      simpa [A, mul_assoc] using finiteSelberg_scaled_mass_le_selbergJR R hd
    have hmuZ : |ArithmeticFunction.moebius d| = 1 :=
      ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd
    have hmuR : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
      rw [← Int.cast_abs, hmuZ]
      norm_num
    have hweight : finiteSelbergWeight R d =
        (ArithmeticFunction.moebius d : ℝ) * (A / selbergJR R) := by
      rw [finiteSelbergWeight_eq_of_squarefree hd]
      simp only [div_eq_mul_inv]
      dsimp [A]
      ring
    rw [hweight, abs_mul, hmuR, one_mul, abs_of_nonneg (div_nonneg hA hJ.le)]
    exact (div_le_one hJ).mpr hAle
  · rw [finiteSelbergWeight_eq_zero_of_not_squarefree hd, abs_zero]
    exact zero_le_one

end

end PrimeGapNormality.Prime
