import PrimeGapNormality.Prime.MertensLaplaceKernel
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated convergence for the Mertens step error

This is the analytic error estimate needed after the logarithmic change of
variables in the Abelian bridge.  The only asymptotic input is convergence of
the discrete Mertens remainder.  Its convergence supplies a global bound; the
remaining discrepancy caused by `floor (exp (u / t))` is controlled directly,
including the interval on which that floor is equal to one.
-/

namespace PrimeGapNormality.Prime

open Asymptotics Filter MeasureTheory Set

noncomputable section

/-- The two logarithms introduced by replacing `exp x` by its natural floor
have the same asymptotics. -/
private theorem tendsto_floor_exp_log_error_atTop :
    Tendsto
      (fun x : ℝ =>
        Real.log (Real.log (⌊Real.exp x⌋₊ : ℝ)) - Real.log x)
      atTop (nhds 0) := by
  have hfloorRatio :
      Tendsto (fun x : ℝ => (⌊Real.exp x⌋₊ : ℝ) / Real.exp x)
        atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop.comp Real.tendsto_exp_atTop
  have hlogFloorDivExp :
      Tendsto (fun x : ℝ =>
        Real.log ((⌊Real.exp x⌋₊ : ℝ) / Real.exp x)) atTop (nhds 0) := by
    have hcomp :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
        hfloorRatio
    change Tendsto
      (fun x : ℝ => Real.log ((⌊Real.exp x⌋₊ : ℝ) / Real.exp x))
      atTop (nhds (Real.log 1)) at hcomp
    simpa only [Real.log_one] using hcomp
  have hfloorNat : Tendsto (fun x : ℝ => ⌊Real.exp x⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop
  have hfloorCast :
      Tendsto (fun x : ℝ => (⌊Real.exp x⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloorNat
  have hfloorne : ∀ᶠ x : ℝ in atTop, (⌊Real.exp x⌋₊ : ℝ) ≠ 0 :=
    hfloorCast.eventually_ne_atTop 0
  have hxne : ∀ᶠ x : ℝ in atTop, x ≠ 0 :=
    (eventually_gt_atTop (0 : ℝ)).mono fun _ hx => hx.ne'
  have hratio :
      Tendsto
        (fun x : ℝ => Real.log (⌊Real.exp x⌋₊ : ℝ) / x)
        atTop (nhds 1) := by
    have hlogRatio :
        Tendsto
          (fun x : ℝ =>
            Real.log ((⌊Real.exp x⌋₊ : ℝ) / Real.exp x) / x)
          atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, zero_mul] using
        hlogFloorDivExp.mul (tendsto_inv_atTop_zero :
          Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))
    have hadd : Tendsto
        (fun x : ℝ => 1 +
          Real.log ((⌊Real.exp x⌋₊ : ℝ) / Real.exp x) / x)
        atTop (nhds 1) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).add hlogRatio
    refine hadd.congr' ?_
    filter_upwards [hfloorne, hxne] with x hfx hx
    rw [Real.log_div hfx (Real.exp_ne_zero x), Real.log_exp]
    field_simp [hx]
    ring
  have houter :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hnum :
      Tendsto (fun x : ℝ => Real.log (⌊Real.exp x⌋₊ : ℝ)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp hfloorCast
  have hnumne :
      ∀ᶠ x : ℝ in atTop, Real.log (⌊Real.exp x⌋₊ : ℝ) ≠ 0 :=
    hnum.eventually_ne_atTop 0
  simpa only [Real.log_one] using houter.congr' (by
    filter_upwards [hnumne, hxne] with x hnx hx
    exact Real.log_div hnx hx)

/-- A bound for the floor--log discrepancy which is uniform for
`0 < t < 1`.  When `u / t < log 2`, the floor is exactly one and the
discrepancy is `-log (u / t)`; this is the source of the integrable
`|log u|` term. -/
private theorem abs_floor_exp_log_error_le
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (ht1 : t < 1) :
    |Real.log (Real.log (⌊Real.exp (u / t)⌋₊ : ℝ)) -
        Real.log (u / t)| ≤
      1 + |Real.log u| := by
  let x : ℝ := u / t
  let N : ℕ := ⌊Real.exp x⌋₊
  have hx : 0 < x := div_pos hu ht
  have hlog2lt : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    convert h using 1 <;> norm_num
  rcases le_or_gt (Real.log (2 : ℝ)) x with hlarge | hsmall
  · have hexp2 : (2 : ℝ) ≤ Real.exp x := by
      calc
        (2 : ℝ) = Real.exp (Real.log 2) :=
          (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp x := (Real.exp_le_exp).2 hlarge
    have hN2 : 2 ≤ N := by
      apply (Nat.le_floor_iff' (by norm_num : (2 : ℕ) ≠ 0)).2
      simpa [N] using hexp2
    have hNRpos : (0 : ℝ) < N := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hN2)
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN2)
    have hfloorle : (N : ℝ) ≤ Real.exp x := by
      simpa [N] using Nat.floor_le (Real.exp_pos x).le
    have hlogNle : Real.log (N : ℝ) ≤ x := by
      simpa only [Real.log_exp] using Real.log_le_log hNRpos hfloorle
    have hexplt : Real.exp x < (N : ℝ) + 1 := by
      simpa [N] using (Nat.lt_floor_add_one (Real.exp x))
    have hxltlogsuc : x < Real.log ((N : ℝ) + 1) := by
      rw [← Real.log_exp x]
      exact Real.log_lt_log (Real.exp_pos x) hexplt
    have hsucsqNat : N + 1 ≤ N * N := by
      calc
        N + 1 ≤ N + N := Nat.add_le_add_left (by omega : 1 ≤ N) N
        _ = 2 * N := by omega
        _ ≤ N * N := Nat.mul_le_mul_right N hN2
    have hsucsq : (N : ℝ) + 1 ≤ (N : ℝ) * N := by
      exact_mod_cast hsucsqNat
    have hlogsucle :
        Real.log ((N : ℝ) + 1) ≤ 2 * Real.log (N : ℝ) := by
      calc
        Real.log ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) * N) :=
          Real.log_le_log (by positivity) hsucsq
        _ = 2 * Real.log (N : ℝ) := by
          rw [Real.log_mul hNRpos.ne' hNRpos.ne']
          ring
    have hxlt : x < 2 * Real.log (N : ℝ) := hxltlogsuc.trans_le hlogsucle
    have hhalf : (1 / 2 : ℝ) < Real.log (N : ℝ) / x := by
      rw [lt_div_iff₀ hx]
      linarith
    have hratiole : Real.log (N : ℝ) / x ≤ 1 :=
      (div_le_one hx).2 hlogNle
    have hlower := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hhalf.le
    have hupper := Real.log_le_log (div_pos hlogNpos hx) hratiole
    have hlower' : -1 ≤
        Real.log (Real.log (N : ℝ)) - Real.log x := by
      rw [Real.log_div hlogNpos.ne' hx.ne'] at hlower hupper
      have hhalfLog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hhalfLog] at hlower
      linarith
    have hupper' :
        Real.log (Real.log (N : ℝ)) - Real.log x ≤ 0 := by
      rw [Real.log_div hlogNpos.ne' hx.ne'] at hupper
      simpa only [Real.log_one] using hupper
    have hone :
        |Real.log (Real.log (N : ℝ)) - Real.log x| ≤ 1 :=
      abs_le.mpr ⟨hlower', hupper'.trans zero_le_one⟩
    simpa only [x, N] using hone.trans (le_add_of_nonneg_right (abs_nonneg _))
  · have hexplt2 : Real.exp x < (2 : ℝ) := by
      calc
        Real.exp x < Real.exp (Real.log 2) := (Real.exp_lt_exp).2 hsmall
        _ = 2 := Real.exp_log (by norm_num)
    have hNlt2 : N < 2 := by
      apply (Nat.floor_lt' (by norm_num : (2 : ℕ) ≠ 0)).2
      simpa [N] using hexplt2
    have hexp1 : (1 : ℝ) ≤ Real.exp x := by
      calc
        (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp x := (Real.exp_le_exp).2 hx.le
    have hN1 : 1 ≤ N := by
      rw [Nat.one_le_floor_iff]
      simpa [N] using hexp1
    have hNeq : N = 1 := by omega
    have hx1 : x < 1 := hsmall.trans hlog2lt
    have hux : u < x := by
      change u < u / t
      rw [lt_div_iff₀ ht]
      exact mul_lt_of_lt_one_right hu ht1
    have hu1 : u < 1 := hux.trans hx1
    have hlogule : Real.log u ≤ Real.log x :=
      Real.log_le_log hu hux.le
    have hlogunonpos : Real.log u ≤ 0 := Real.log_nonpos hu.le hu1.le
    have hlogxnonpos : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1.le
    have habs : |Real.log x| ≤ |Real.log u| := by
      rw [abs_of_nonpos hlogxnonpos, abs_of_nonpos hlogunonpos]
      linarith
    have hsmallBound :
        |Real.log (Real.log (N : ℝ)) - Real.log x| ≤ |Real.log u| := by
      simpa [hNeq] using habs
    simpa only [x, N] using
      hsmallBound.trans (le_add_of_nonneg_left zero_le_one)

/-- Dominated convergence for the full Mertens step error.  No boundedness
hypothesis is needed: the required global bound follows from `hB`. -/
theorem tendsto_integral_mertens_step_error
    {B : ℝ}
    (hB : Tendsto (fun N : ℕ =>
      mertensPrimeReciprocalSum N - Real.log (Real.log N))
      atTop (nhds B)) :
    Tendsto (fun t : ℝ =>
      ∫ u in Set.Ioi 0, Real.exp (-u) *
        (mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊
          - Real.log (u / t) - B))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let R : ℕ → ℝ := fun N =>
    mertensPrimeReciprocalSum N - Real.log (Real.log N) - B
  have hR : Tendsto R atTop (nhds 0) := by
    simpa only [R, sub_self] using hB.sub_const B
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ N : ℕ, ‖R N‖ ≤ C := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto R hR).exists_norm_le
    exact ⟨C, fun N => hC (R N) ⟨N, rfl⟩⟩
  let bound : ℝ → ℝ := fun u =>
    (C + 1) * Real.exp (-u) + Real.exp (-u) * |Real.log u|
  have hlogabs : Integrable
      (fun u : ℝ => Real.exp (-u) * |Real.log u|)
      (volume.restrict (Ioi 0)) := by
    have habs : Integrable
        (fun u : ℝ => |Real.exp (-u) * Real.log u|)
        (volume.restrict (Ioi 0)) :=
      integrableOn_exp_neg_mul_log_Ioi_zero.abs
    refine habs.congr (Eventually.of_forall fun u => ?_)
    change |Real.exp (-u) * Real.log u| =
      Real.exp (-u) * |Real.log u|
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hboundInt : Integrable bound (volume.restrict (Ioi 0)) := by
    exact (integrableOn_exp_neg_Ioi_zero.const_mul (C + 1)).add hlogabs
  have hmeas : ∀ t : ℝ,
      AEStronglyMeasurable
        (fun u : ℝ => Real.exp (-u) *
          (mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊
            - Real.log (u / t) - B))
        (volume.restrict (Ioi 0)) := by
    intro t
    have hindex : Measurable (fun u : ℝ => ⌊Real.exp (u / t)⌋₊) :=
      (Real.measurable_exp.comp (measurable_id.div_const t)).nat_floor
    have hsum : Measurable
        (fun u : ℝ => mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊) :=
      (measurable_of_countable mertensPrimeReciprocalSum).comp hindex
    have hlogdiv : Measurable (fun u : ℝ => Real.log (u / t)) :=
      Real.measurable_log.comp (measurable_id.div_const t)
    have hfull : Measurable
        (fun u : ℝ => Real.exp (-u) *
          (mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊ -
            Real.log (u / t) - B)) :=
      (Real.measurable_exp.comp measurable_neg).mul
        ((hsum.sub hlogdiv).sub measurable_const)
    exact hfull.aestronglyMeasurable
  have hdom : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      ∀ᵐ u ∂volume.restrict (Ioi 0),
        ‖Real.exp (-u) *
          (mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊
            - Real.log (u / t) - B)‖ ≤ bound u := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    let N : ℕ := ⌊Real.exp (u / t)⌋₊
    have hdecomp :
        mertensPrimeReciprocalSum N - Real.log (u / t) - B =
          R N +
            (Real.log (Real.log (N : ℝ)) - Real.log (u / t)) := by
      simp only [R]
      ring
    have hinside :
        |mertensPrimeReciprocalSum N - Real.log (u / t) - B| ≤
          C + 1 + |Real.log u| := by
      rw [hdecomp]
      calc
        |R N + (Real.log (Real.log (N : ℝ)) - Real.log (u / t))| ≤
            |R N| +
              |Real.log (Real.log (N : ℝ)) - Real.log (u / t)| :=
          abs_add_le _ _
        _ ≤ C + (1 + |Real.log u|) :=
          add_le_add (by simpa only [Real.norm_eq_abs] using hC N)
            (abs_floor_exp_log_error_le hu ht.1 ht.2)
        _ = C + 1 + |Real.log u| := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (-u))]
    change Real.exp (-u) *
        |mertensPrimeReciprocalSum N - Real.log (u / t) - B| ≤ bound u
    rw [show bound u = Real.exp (-u) * (C + 1 + |Real.log u|) by
      simp only [bound]
      ring]
    exact mul_le_mul_of_nonneg_left hinside (Real.exp_pos (-u)).le
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioi 0),
      Tendsto
        (fun t : ℝ => Real.exp (-u) *
          (mertensPrimeReciprocalSum ⌊Real.exp (u / t)⌋₊
            - Real.log (u / t) - B))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hxt : Tendsto (fun t : ℝ => u / t)
        (nhdsWithin 0 (Ioi 0)) atTop := by
      simpa only [div_eq_mul_inv] using
        Tendsto.const_mul_atTop hu tendsto_inv_nhdsGT_zero
    have hN : Tendsto (fun t : ℝ => ⌊Real.exp (u / t)⌋₊)
        (nhdsWithin 0 (Ioi 0)) atTop :=
      tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp hxt)
    have hrem : Tendsto
        (fun t : ℝ => R ⌊Real.exp (u / t)⌋₊)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := hR.comp hN
    have herr : Tendsto
        (fun t : ℝ =>
          Real.log (Real.log (⌊Real.exp (u / t)⌋₊ : ℝ)) -
            Real.log (u / t))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      tendsto_floor_exp_log_error_atTop.comp hxt
    have hsum := hrem.add herr
    have hmul := (tendsto_const_nhds (x := Real.exp (-u))).mul hsum
    convert hmul using 1
    · funext t
      simp only [R]
      ring
    · simp
  have hDCT :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := nhdsWithin 0 (Ioi 0)) (G := ℝ)
      (μ := volume.restrict (Ioi 0)) bound
      (Eventually.of_forall hmeas) hdom hboundInt hpoint
  rw [MeasureTheory.integral_zero] at hDCT
  exact hDCT

end

end PrimeGapNormality.Prime
