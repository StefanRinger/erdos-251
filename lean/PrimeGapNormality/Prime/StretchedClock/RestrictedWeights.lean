import PrimeGapNormality.Prime.StretchedClock.RestrictedSelberg

/-! The actual coprimality-filtered optimal finite Selberg weights. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset
open scoped ArithmeticFunction.Moebius
noncomputable section
set_option maxHeartbeats 1000000

def restrictedY (a R r : ℕ) : ℝ :=
  if r.Coprime a then
    (ArithmeticFunction.moebius r : ℝ) / ((r.totient : ℝ) * restrictedJ a R)
  else 0

def restrictedWeight (a R d : ℕ) : ℝ :=
  (d : ℝ) * ∑ m ∈ Icc 1 (R / d),
    (ArithmeticFunction.moebius m : ℝ) * restrictedY a R (d * m)

def restrictedWeightSupport (a R d : ℕ) : Finset ℕ :=
  (finiteSelbergWeightSupport R d).filter fun m => m.Coprime a

def restrictedPairs (a R d : ℕ) : Finset (ℕ × ℕ) :=
  d.divisors.product (restrictedWeightSupport a R d)

def restrictedCoprimeMass (a R d : ℕ) : ℝ :=
  ∑ m ∈ restrictedWeightSupport a R d, (m.totient : ℝ)⁻¹

theorem restrictedY_zero_of_not_coprime {a R r : ℕ} (hr : ¬ r.Coprime a) :
    restrictedY a R r = 0 := by simp [restrictedY, hr]

theorem restrictedY_zero_of_not_squarefree {a R r : ℕ} (hr : ¬ Squarefree r) :
    restrictedY a R r = 0 := by
  simp [restrictedY, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hr]

theorem restrictedWeight_zero_of_not_coprime {a R d : ℕ} (hd : ¬ d.Coprime a) :
    restrictedWeight a R d = 0 := by
  unfold restrictedWeight
  have hz : ∀ m : ℕ, restrictedY a R (d * m) = 0 := by
    intro m
    apply restrictedY_zero_of_not_coprime
    intro hdm
    exact hd (Nat.Coprime.of_dvd_left (dvd_mul_right d m) hdm)
  simp only [hz, mul_zero, sum_const_zero]

theorem restrictedWeight_zero_of_not_squarefree {a R d : ℕ} (hd : ¬ Squarefree d) :
    restrictedWeight a R d = 0 := by
  unfold restrictedWeight
  have hz : ∀ m : ℕ, restrictedY a R (d * m) = 0 := by
    intro m
    exact restrictedY_zero_of_not_squarefree (fun hdm => hd hdm.of_mul_left)
  simp only [hz, mul_zero, sum_const_zero]

theorem restrictedWeight_zero_of_lt {a R d : ℕ} (hd : R < d) :
    restrictedWeight a R d = 0 := by
  simp [restrictedWeight, Nat.div_eq_of_lt hd]

theorem restrictedWeight_zero_of_not_mem {a R d : ℕ} (hd : d ∉ Icc 1 R) :
    restrictedWeight a R d = 0 := by
  by_cases hd0 : d = 0
  · subst d
    simp [restrictedWeight]
  · apply restrictedWeight_zero_of_lt
    have hpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    by_contra hnot
    exact hd (mem_Icc.mpr ⟨hpos, Nat.le_of_not_gt hnot⟩)

theorem restrictedPairs_subset (a R d : ℕ) :
    restrictedPairs a R d ⊆ finiteSelbergPairs R d := by
  intro z hz
  obtain ⟨he, hm⟩ := mem_product.mp hz
  exact mem_product.mpr ⟨he, (mem_filter.mp hm).1⟩

theorem restrictedPairs_sum_le (a R d : ℕ) (hd : d.Coprime a) :
    ∑ z ∈ restrictedPairs a R d, selbergJR_term (z.1 * z.2) ≤ restrictedJ a R := by
  let f : ℕ × ℕ → ℕ := fun z => z.1 * z.2
  have hinj : Set.InjOn f (restrictedPairs a R d : Set (ℕ × ℕ)) :=
    (finiteSelbergPairs_mul_injOn R d).mono (restrictedPairs_subset a R d)
  have hsub : (restrictedPairs a R d).image f ⊆ restrictedDivisors a R := by
    intro n hn
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hn
    obtain ⟨he, hm⟩ := mem_product.mp hz
    have heco : z.1.Coprime a :=
      Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_divisors he) hd
    have hmco : z.2.Coprime a := (mem_filter.mp hm).2
    exact mem_restrictedDivisors.mpr
      ⟨finiteSelbergPairs_mul_mem_Icc (restrictedPairs_subset a R d hz),
        Nat.Coprime.mul_left heco hmco⟩
  calc
    _ = ∑ n ∈ (restrictedPairs a R d).image f, selbergJR_term n := by
      rw [sum_image hinj]
    _ ≤ ∑ n ∈ restrictedDivisors a R, selbergJR_term n := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro n hn hnot
      exact selbergJR_term_nonneg (by
        have := (mem_Icc.mp (mem_restrictedDivisors.mp hn).1).1
        omega)
    _ = restrictedJ a R := rfl

theorem restrictedPairs_sum_eq (a R d : ℕ) :
    ∑ z ∈ restrictedPairs a R d, selbergJR_term (z.1 * z.2) =
      (∑ e ∈ d.divisors, (e.totient : ℝ)⁻¹) * restrictedCoprimeMass a R d := by
  calc
    _ = ∑ e ∈ d.divisors, ∑ m ∈ restrictedWeightSupport a R d,
        selbergJR_term (e * m) := by
      exact Finset.sum_product d.divisors (restrictedWeightSupport a R d)
        (fun z => selbergJR_term (z.1 * z.2))
    _ = ∑ e ∈ d.divisors, ∑ m ∈ restrictedWeightSupport a R d,
        (e.totient : ℝ)⁻¹ * (m.totient : ℝ)⁻¹ := by
      apply sum_congr rfl
      intro e he
      apply sum_congr rfl
      intro m hm
      have hm' : m ∈ finiteSelbergWeightSupport R d := (mem_filter.mp hm).1
      have hed := Nat.dvd_of_mem_divisors he
      have hdm := (finiteSelbergWeightSupport_spec hm').2
      have hcop : e.Coprime m :=
        Nat.Coprime.of_dvd_left hed (Nat.coprime_of_squarefree_mul hdm)
      have hem : Squarefree (e * m) :=
        (Nat.squarefree_mul hcop).mpr
          ⟨hdm.of_mul_left.squarefree_of_dvd hed, hdm.of_mul_right⟩
      rw [selbergJR_term_eq_inv_totient hem, Nat.totient_mul hcop, Nat.cast_mul,
        mul_inv_rev, mul_comm]
    _ = _ := by
      unfold restrictedCoprimeMass
      rw [sum_mul]
      exact sum_congr rfl fun e he => (mul_sum _ _ _).symm

theorem restricted_scaled_mass_le (a R : ℕ) {d : ℕ}
    (hdsq : Squarefree d) (hd : d.Coprime a) :
    (d : ℝ) * (d.totient : ℝ)⁻¹ * restrictedCoprimeMass a R d ≤ restrictedJ a R := by
  rw [← sum_divisors_inv_totient_eq_div_totient hdsq,
    ← restrictedPairs_sum_eq]
  exact restrictedPairs_sum_le a R d hd

theorem restricted_inner_sum_eq_support (a R d : ℕ) (hd : d.Coprime a) :
    (∑ m ∈ Icc 1 (R / d),
      (ArithmeticFunction.moebius m : ℝ) * restrictedY a R (d * m)) =
    ∑ m ∈ restrictedWeightSupport a R d,
      (ArithmeticFunction.moebius m : ℝ) * restrictedY a R (d * m) := by
  symm
  apply sum_subset
  · exact (filter_subset _ _).trans (filter_subset _ _)
  · intro m hm hnot
    by_cases hsq : Squarefree (d * m)
    · have hmco : ¬ m.Coprime a := by
        intro hco
        apply hnot
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨hm, hsq⟩, hco⟩
      have hdmco : ¬ (d * m).Coprime a := by
        intro hco
        exact hmco (Nat.Coprime.of_dvd_left (dvd_mul_left m d) hco)
      rw [restrictedY_zero_of_not_coprime hdmco, mul_zero]
    · rw [restrictedY_zero_of_not_squarefree hsq, mul_zero]

theorem restricted_inner_term_eq {a R d m : ℕ} (hd : d.Coprime a)
    (hm : m ∈ restrictedWeightSupport a R d) :
    (ArithmeticFunction.moebius m : ℝ) * restrictedY a R (d * m) =
      (ArithmeticFunction.moebius d : ℝ) * (d.totient : ℝ)⁻¹ *
        (m.totient : ℝ)⁻¹ * (restrictedJ a R)⁻¹ := by
  have hm' : m ∈ finiteSelbergWeightSupport R d := (mem_filter.mp hm).1
  have hdmco : (d * m).Coprime a := Nat.Coprime.mul_left hd (mem_filter.mp hm).2
  have hcop := finiteSelbergWeightSupport_coprime hm'
  have hmsq := finiteSelbergWeightSupport_squarefree_right hm'
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hmusq : (ArithmeticFunction.moebius m : ℝ) *
      (ArithmeticFunction.moebius m : ℝ) = 1 := by
    simpa [pow_two] using congrArg (fun z : ℤ => (z : ℝ))
      (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hmsq)
  rw [restrictedY, if_pos hdmco, hmu, Nat.totient_mul hcop, Int.cast_mul, Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (ArithmeticFunction.moebius d : ℝ) *
        ((ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius m : ℝ)) *
        (d.totient : ℝ)⁻¹ * (m.totient : ℝ)⁻¹ * (restrictedJ a R)⁻¹ := by ring
    _ = _ := by rw [hmusq]; ring

theorem restrictedWeight_eq_of_squarefree {a R d : ℕ}
    (hdsq : Squarefree d) (hd : d.Coprime a) :
    restrictedWeight a R d =
      (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) * (d.totient : ℝ)⁻¹ *
        (restrictedJ a R)⁻¹ * restrictedCoprimeMass a R d := by
  rw [restrictedWeight, restricted_inner_sum_eq_support a R d hd]
  calc
    _ = (d : ℝ) * ∑ m ∈ restrictedWeightSupport a R d,
        (ArithmeticFunction.moebius d : ℝ) * (d.totient : ℝ)⁻¹ *
          (m.totient : ℝ)⁻¹ * (restrictedJ a R)⁻¹ := by
      apply congrArg ((d : ℝ) * ·)
      exact sum_congr rfl fun m hm => restricted_inner_term_eq hd hm
    _ = _ := by
      unfold restrictedCoprimeMass
      rw [mul_sum, mul_sum]
      exact sum_congr rfl fun m hm => by ring

/-- The bound holds for every d; nonsquarefree and noncoprime d have zero weight. -/
theorem restrictedWeight_abs_le_one (a : ℕ) {R d : ℕ} (hR : 1 ≤ R) :
    |restrictedWeight a R d| ≤ 1 := by
  by_cases hd : d.Coprime a
  · by_cases hdsq : Squarefree d
    · let A := (d : ℝ) * (d.totient : ℝ)⁻¹ * restrictedCoprimeMass a R d
      have hJ := restrictedJ_pos a hR
      have hmass : 0 ≤ restrictedCoprimeMass a R d :=
        sum_nonneg fun m hm => inv_nonneg.mpr (Nat.cast_nonneg _)
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hAle : A ≤ restrictedJ a R := restricted_scaled_mass_le a R hdsq hd
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
        rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hdsq]
        norm_num
      have he : restrictedWeight a R d =
          (ArithmeticFunction.moebius d : ℝ) * (A / restrictedJ a R) := by
        rw [restrictedWeight_eq_of_squarefree hdsq hd]
        dsimp [A]
        simp only [div_eq_mul_inv]
        ring
      rw [he, abs_mul, hmu, one_mul, abs_of_nonneg (div_nonneg hA hJ.le)]
      exact (div_le_one hJ).mpr hAle
    · rw [restrictedWeight_zero_of_not_squarefree hdsq, abs_zero]
      exact zero_le_one
  · rw [restrictedWeight_zero_of_not_coprime hd, abs_zero]
    exact zero_le_one

end
end PrimeGapNormality.Prime.StretchedClock
