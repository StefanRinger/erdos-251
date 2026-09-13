import PrimeGapNormality.Prime.CoreDigitalEmpirical
import Mathlib.Analysis.Fourier.AddCircle

/-! From the actual positive window-test criterion to every nonzero circle
character. The upstream positive bound remains explicit, not assumed as a
new prime or model theorem. -/

open MeasureTheory Filter Finset
open scoped Topology ENNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

set_option backward.isDefEq.respectTransparency false in
theorem coreDigitalWindowMeasure_integral_complex
    (u : ℕ → AddCircle (1 : ℝ)) (a : ℕ) {N : ℕ} (hN : 0 < N)
    (f : AddCircle (1 : ℝ) →ᵇ ℂ) :
    (∫ x, f x ∂(coreDigitalWindowMeasure u a N : Measure (AddCircle (1 : ℝ)))) =
      (∑ i ∈ range N, f (u (a + i))) / (N : ℂ) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hm : Measurable (fun i : Fin N => u (a + (i : ℕ))) := measurable_of_finite _
  have hmeasure :
      (coreDigitalWindowMeasure u a N : Measure (AddCircle (1 : ℝ))) =
        ((PMF.uniformOfFintype (Fin N)).map (fun i : Fin N => u (a + (i : ℕ)))).toMeasure := by
    unfold coreDigitalWindowMeasure
    rw [dif_pos hN]
    rfl
  rw [hmeasure, ← PMF.toMeasure_map (fun i : Fin N => u (a + (i : ℕ)))
      (PMF.uniformOfFintype (Fin N)) hm, integral_map hm.aemeasurable
    f.continuous.aestronglyMeasurable, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast, ← Finset.mul_sum]
  have hs := Fin.sum_univ_eq_sum_range (fun j : ℕ => f (u (a + j))) N
  rw [hs, div_eq_mul_inv, mul_comm]

theorem coreDigital_nonzero_character_integral {q : ℤ} (hq : q ≠ 0) :
    (∫ x : AddCircle (1 : ℝ), fourier q x) = 0 :=
  integral_eq_zero_of_add_right_eq_neg
    (fourier_add_half_inv_index hq (by norm_num : (0 : ℝ) < 1))

theorem coreDigital_window_character_tendsto_zero
    {C : ℕ} (hC : 2 ≤ C)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + 1) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hNpos : ∀ j, 0 < N j)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤ A * ∫ x, f x ∂volume + ε)
    {q : ℤ} (hq : q ≠ 0) :
    Tendsto (fun j => (∑ i ∈ range (N j), fourier q (u (a j + i))) / (N j : ℂ))
      atTop (𝓝 0) := by
  have hm := coreDigital_window_measures_tendsto_volume hC u hu a N hN
    (fun j => coreDigitalWindowMeasure u (a j) (N j))
    (fun j f => coreDigitalWindowMeasure_integral u (a j) (hNpos j) f) hA hbound
  let f : AddCircle (1 : ℝ) →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact (fourier q)
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hm f
  have hc : (coreCircleVolume : Measure (AddCircle (1 : ℝ))) = volume := rfl
  simp only [coreDigitalWindowMeasure_integral_complex u _ (hNpos _), hc] at ht
  change Tendsto (fun j => (∑ i ∈ range (N j), fourier q (u (a j + i))) / (N j : ℂ))
    atTop (𝓝 (∫ x : AddCircle (1 : ℝ), fourier q x)) at ht
  rwa [coreDigital_nonzero_character_integral hq] at ht

end PrimeGapNormality.Prime
