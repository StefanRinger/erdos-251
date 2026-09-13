import PrimeGapNormality.Prime.CoreWeakHLProfile

namespace PrimeGapNormality.Prime.CoreWeakHL
open Finset Filter
open scoped Topology
noncomputable section

theorem eventually_order_fits {κ A : ℝ} (hκ : 0 < κ) (hA : 40 * κ < A) :
    ∀ᶠ X : ℕ in atTop,
      (profileR (profileL κ X) 20 : ℝ) + 1 ≤ (A / 2) * ell X := by
  filter_upwards [ell_atTop.eventually_gt_atTop 0,
    (rooted_rank_ratio hκ).eventually
      (gt_mem_nhds (show 20 * κ < A / 2 by linarith))] with X hX h
  exact ((div_lt_iff₀ hX).mp h).le

theorem rooted_error_of_uniform_bound {κ A C : ℝ} {x₀ X : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbound : ∀ x : ℕ, x₀ ≤ x → ∀ E : Finset ℕ,
      (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
      (E.card : ℝ) ≤ (A / 2) * Real.log (Real.log (x : ℝ)) →
      hlAdmissible E →
      |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤
        C * (x : ℝ) * Real.exp (-A * Real.log (Real.log (x : ℝ)) ^ 2))
    (hfit : ProfileFits κ 20 X) (hx₀ : x₀ ≤ X)
    (horder : (profileR (profileL κ X) 20 : ℝ) + 1 ≤ (A / 2) * ell X)
    {H : Finset ℕ} (hH : H ⊆ windowOmega κ X)
    (hr : H.card ≤ profileR (profileL κ X) 20) :
    |(rootedTupleCount X H : ℝ) - rootedMainTerm X H| ≤
      3 * C * (X : ℝ) * Real.exp (-A * ell X ^ 2) := by
  have hX : 16 ≤ X := hfit.1
  have hX3 : 3 ≤ X := by omega
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have h0 : 0 ∉ H := zero_notMem_of_subset_windowOmega hH
  have hcard : (insert 0 H).card = H.card + 1 := card_insert_of_notMem h0
  have hcardX : (insert 0 H).card ≤ X := by
    rw [hcard]
    exact (Nat.succ_le_succ hr).trans hfit.2.2.2
  by_cases hadm : hlAdmissible (insert 0 H)
  · have hdiam : ∀ h ∈ insert 0 H, (h : ℝ) ≤ Real.log (X : ℝ) ^ 2 := by
      intro h hh
      rcases mem_insert.mp hh with rfl | hh
      · simpa using sq_nonneg (Real.log (X : ℝ))
      · exact (Nat.cast_le.mpr (le_profileS_of_mem_windowOmega (hH hh))).trans hfit.2.1
    have hcardR : ((insert 0 H).card : ℝ) ≤
        (A / 2) * Real.log (Real.log (X : ℝ)) := by
      rw [hcard, Nat.cast_add_one]
      rw [ell_eq_loglog hX3] at horder
      exact (add_le_add (Nat.cast_le.mpr hr) (le_refl (1 : ℝ))).trans horder
    have hlogpos : 0 < Real.log (X : ℝ) :=
      lt_trans (by norm_num) (one_lt_log_of_three_le hX3)
    have hlogle : Real.log (X : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show X ≤ 2 * X by omega))
    have hlle : Real.log (Real.log (X : ℝ)) ≤
        Real.log (Real.log ((2 * X : ℕ) : ℝ)) := Real.log_le_log hlogpos hlogle
    have hellpos : 0 ≤ Real.log (Real.log (X : ℝ)) :=
      le_of_lt (lt_trans (by norm_num) (one_lt_log_log_of_sixteen_le hX))
    have hdiam2 : ∀ h ∈ insert 0 H, (h : ℝ) ≤
        Real.log ((2 * X : ℕ) : ℝ) ^ 2 := fun h hh =>
      (hdiam h hh).trans (pow_le_pow_left₀ hlogpos.le hlogle 2)
    have hcard2 := hcardR.trans (mul_le_mul_of_nonneg_left hlle (by positivity : 0 ≤ A / 2))
    have he₁ := hbound X hx₀ (insert 0 H) hdiam hcardR hadm
    have he₂ := hbound (2 * X) (by omega) (insert 0 H) hdiam2 hcard2 hadm
    have hexp : Real.exp (-A * Real.log (Real.log ((2 * X : ℕ) : ℝ)) ^ 2) ≤
        Real.exp (-A * Real.log (Real.log (X : ℝ)) ^ 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hellpos hlle 2) (neg_nonpos.mpr hA)
    have he₂' := he₂.trans (mul_le_mul_of_nonneg_left hexp
      (show 0 ≤ C * ((2 * X : ℕ) : ℝ) by positivity))
    have he := rooted_error_le_endpoints h0 he₁ (by simpa using he₂')
    rw [ell_eq_loglog hX3]
    convert he using 1 <;> push_cast <;> ring
  · rw [rooted_error_eq_zero_of_not_hlAdmissible h0 hadm hcardX, abs_zero]
    positivity

end
end PrimeGapNormality.Prime.CoreWeakHL
