import PrimeGapNormality.Prime.CoreDigitalLipschitz

/-!
# Periodic digital recurrence

This extends the invariant-limit consumer from the one-step recurrence to
the literal periodic recurrence `u (n + k) = C • u n`.  The full-window
defect is an exact difference of two `k`-endpoint sums.  No distribution of
prime indices modulo `k` is used or assumed here.
-/

open MeasureTheory Filter Finset
open scoped Classical Topology ENNReal NNReal BoundedContinuousFunction

namespace PrimeGapNormality.Prime

local instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp⟩

private theorem sum_range_shift_sub_eq_endpoint_sums
    (g : ℕ → ℝ) (N k : ℕ) :
    (∑ i ∈ range N, g (i + k)) - ∑ i ∈ range N, g i =
      (∑ j ∈ range k, g (N + j)) - ∑ j ∈ range k, g j := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep :
          (∑ i ∈ range N, g (i + (k + 1))) -
              ∑ i ∈ range N, g (i + k) =
            g (N + k) - g k := by
        rw [← sum_sub_distrib]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          Nat.zero_add, Nat.add_zero] using sum_range_sub (fun i => g (i + k)) N
      calc
        (∑ i ∈ range N, g (i + (k + 1))) - ∑ i ∈ range N, g i =
            ((∑ i ∈ range N, g (i + (k + 1))) -
              ∑ i ∈ range N, g (i + k)) +
            ((∑ i ∈ range N, g (i + k)) - ∑ i ∈ range N, g i) := by ring
        _ = (g (N + k) - g k) +
            ((∑ j ∈ range k, g (N + j)) - ∑ j ∈ range k, g j) := by
          rw [hstep, ih]
        _ = (∑ j ∈ range (k + 1), g (N + j)) -
            ∑ j ∈ range (k + 1), g j := by
          rw [sum_range_succ, sum_range_succ]
          ring

/-- Under the literal `k`-step recurrence, the finite-window defect is the
difference of its two `k`-endpoint sums. -/
theorem coreDigitalPeriodicWindowAverage_defect {C k : ℕ}
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (a N : ℕ) :
    coreDigitalWindowAverage u
        (f.compContinuous ⟨fun x => C • x, continuous_nsmul C⟩) a N -
      coreDigitalWindowAverage u f a N =
        ((∑ j ∈ range k, f (u (a + N + j))) -
          ∑ j ∈ range k, f (u (a + j))) / (N : ℝ) := by
  unfold coreDigitalWindowAverage
  rw [← sub_div]
  congr 1
  have hfirst :
      (∑ i ∈ range N,
        (f.compContinuous ⟨fun x => C • x, continuous_nsmul C⟩) (u (a + i))) =
      ∑ i ∈ range N, f (u (a + (i + k))) := by
    apply sum_congr rfl
    intro i _
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    rw [← hu (a + i), Nat.add_assoc]
  rw [hfirst]
  simpa only [Nat.add_assoc] using
    sum_range_shift_sub_eq_endpoint_sums (fun n => f (u (a + n))) N k

private theorem norm_endpoint_sum_le
    (u : ℕ → AddCircle (1 : ℝ)) (f : AddCircle (1 : ℝ) →ᵇ ℝ)
    (a k : ℕ) :
    ‖∑ j ∈ range k, f (u (a + j))‖ ≤ (k : ℝ) * ‖f‖ := by
  calc
    ‖∑ j ∈ range k, f (u (a + j))‖ ≤
        ∑ j ∈ range k, ‖f (u (a + j))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range k, ‖f‖ :=
      sum_le_sum fun j _ => f.norm_coe_le_norm (u (a + j))
    _ = (k : ℝ) * ‖f‖ := by simp

/-- Uniform `k`-endpoint boundary estimate. -/
theorem coreDigitalPeriodicWindowAverage_defect_bound {C k : ℕ}
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (f : AddCircle (1 : ℝ) →ᵇ ℝ) (a N : ℕ) :
    ‖coreDigitalWindowAverage u
        (f.compContinuous ⟨fun x => C • x, continuous_nsmul C⟩) a N -
      coreDigitalWindowAverage u f a N‖ ≤
        (2 * (k : ℝ) * ‖f‖) / (N : ℝ) := by
  rw [coreDigitalPeriodicWindowAverage_defect u hu, norm_div, Real.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  calc
    ‖(∑ j ∈ range k, f (u (a + N + j))) -
        ∑ j ∈ range k, f (u (a + j))‖ ≤
        ‖∑ j ∈ range k, f (u (a + N + j))‖ +
          ‖∑ j ∈ range k, f (u (a + j))‖ := norm_sub_le _ _
    _ ≤ (k : ℝ) * ‖f‖ + (k : ℝ) * ‖f‖ :=
      add_le_add (by
        simpa only [Nat.add_assoc] using norm_endpoint_sum_le u f (a + N) k)
        (norm_endpoint_sum_le u f a k)
    _ = 2 * (k : ℝ) * ‖f‖ := by ring

/-- Every weak probability limit of growing full windows is invariant under
`x ↦ C • x`, derived from the literal `k`-step recurrence. -/
theorem coreDigitalPeriodic_invariant_of_window_limit {C k : ℕ}
    (_hk : 1 ≤ k)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hlim : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a j) (N j)) atTop
        (𝓝 (∫ x, f x ∂μ))) :
    MeasurePreserving (fun x : AddCircle (1 : ℝ) => C • x) μ μ := by
  have hc : Continuous (fun x : AddCircle (1 : ℝ) => C • x) := continuous_nsmul C
  refine ⟨hc.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hc.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  let g := f.compContinuous ⟨fun x => C • x, hc⟩
  have hzero : Tendsto (fun j =>
      coreDigitalWindowAverage u g (a j) (N j) -
        coreDigitalWindowAverage u f (a j) (N j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun j => coreDigitalPeriodicWindowAverage_defect_bound u hu f (a j) (N j))
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN)
  have heq := tendsto_nhds_unique ((hlim g).sub (hlim f)) hzero
  exact sub_eq_zero.mp heq

/-- Absolute continuity identifies every such periodic weak limit with
circle volume. -/
theorem coreDigitalPeriodic_window_limit_eq_volume {C k : ℕ}
    (hC : 2 ≤ C) (hk : 1 ≤ k)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hlim : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a j) (N j)) atTop
        (𝓝 (∫ x, f x ∂μ)))
    (hac : μ ≪ volume) : μ = volume :=
  coreDigital_eq_volume_of_invariant_ac hC μ
    (coreDigitalPeriodic_invariant_of_window_limit hk u hu a N hN μ hlim) hac

/-- Positive Lipschitz bounds imply volume identification for a periodic
weak window limit. -/
theorem coreDigitalPeriodic_window_limit_eq_volume_of_lipschitz_bounds
    {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ]
    (hlim : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a j) (N j)) atTop
        (𝓝 (∫ x, f x ∂μ)))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤
          A * ∫ x, f x ∂volume + ε) :
    μ = volume := by
  apply coreDigitalPeriodic_window_limit_eq_volume hC hk u hu a N hN μ hlim
  apply Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal A)
  letI : IsFiniteMeasure (ENNReal.ofReal A •
      (volume : Measure (AddCircle (1 : ℝ)))) := ⟨by simp [Measure.smul_apply]⟩
  apply coreDigital_measure_le_of_positive_lipschitz_tests
  intro f K hK hf
  rw [integral_smul_measure, ENNReal.toReal_ofReal hA, smul_eq_mul]
  apply le_of_forall_pos_le_add
  intro ε hε
  exact le_of_tendsto (hlim f) (hbound f K hK hf ε hε)

/-- Positive Lipschitz control forces the actual growing full-window
empirical probability measures to volume. -/
theorem coreDigitalPeriodic_window_measures_tendsto_of_lipschitz_bounds
    {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hNpos : ∀ j, 0 < N j)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤
          A * ∫ x, f x ∂volume + ε) :
    Tendsto (fun j => coreDigitalWindowMeasure u (a j) (N j)) atTop
      (𝓝 coreCircleVolume) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  obtain ⟨φ, hφ, hlim⟩ := hμ.tendsto_subseq
  have htest : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ,
      Tendsto (fun j => coreDigitalWindowAverage u f (a (φ j)) (N (φ j)))
        atTop (𝓝 (∫ x, f x ∂(μ : Measure (AddCircle (1 : ℝ))))) := by
    intro f
    have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
    simpa only [Function.comp_apply,
      coreDigitalWindowMeasure_integral u _ (hNpos _)] using ht
  have heq := coreDigitalPeriodic_window_limit_eq_volume_of_lipschitz_bounds
    hC hk u hu (a ∘ φ) (N ∘ φ) (hN.comp hφ.tendsto_atTop)
    (μ : Measure (AddCircle (1 : ℝ))) htest hA
    (fun f K hK hf ε hε => hφ.tendsto_atTop.eventually (hbound f K hK hf ε hε))
  exact Subtype.ext heq

/-- Consequently every nonzero circle character has zero full-window mean.
This does not assert equidistribution of the residue-class subsequence
`u (k n)` or of the `C`-orbit of `u 0`. -/
theorem coreDigitalPeriodic_window_character_tendsto_zero_of_lipschitz_bounds
    {C k : ℕ} (hC : 2 ≤ C) (hk : 1 ≤ k)
    (u : ℕ → AddCircle (1 : ℝ)) (hu : ∀ n, u (n + k) = C • u n)
    (a N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hNpos : ∀ j, 0 < N j)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ f : AddCircle (1 : ℝ) →ᵇ ℝ, ∀ K : ℝ≥0,
      LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        coreDigitalWindowAverage u f (a j) (N j) ≤
          A * ∫ x, f x ∂volume + ε)
    {q : ℤ} (hq : q ≠ 0) :
    Tendsto (fun j => (∑ i ∈ range (N j), fourier q (u (a j + i))) /
      (N j : ℂ)) atTop (𝓝 0) := by
  have hm := coreDigitalPeriodic_window_measures_tendsto_of_lipschitz_bounds
    hC hk u hu a N hN hNpos hA hbound
  let f : AddCircle (1 : ℝ) →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact (fourier q)
  have ht :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hm f
  have hc : (coreCircleVolume : Measure (AddCircle (1 : ℝ))) = volume := rfl
  simp only [coreDigitalWindowMeasure_integral_complex u _ (hNpos _), hc] at ht
  change Tendsto (fun j => (∑ i ∈ range (N j), fourier q (u (a j + i))) /
    (N j : ℂ)) atTop (𝓝 (∫ x : AddCircle (1 : ℝ), fourier q x)) at ht
  rwa [coreDigital_nonzero_character_integral hq] at ht

end PrimeGapNormality.Prime
