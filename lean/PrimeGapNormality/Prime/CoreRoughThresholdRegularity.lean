import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite regularity from the paper's weighted derivative condition

The literal condition `0 ≤ t Ψ'(t) ≤ C Ψ(t)` is converted into an
ordinary Grönwall bound on a positive interval.  No ratio estimate or
threshold-density conclusion is assumed.
-/

namespace PrimeGapNormality.Prime.CoreRoughThresholdRegularity

open Set Filter
open scoped Topology

noncomputable section

private theorem deriv_nonneg_of_weighted
    {t d : ℝ} (ht : 0 < t) (h : 0 ≤ t * d) : 0 ≤ d :=
  nonneg_of_mul_nonneg_right h ht

/-- Finite local comparison supplied by the actual weighted derivative
hypothesis.  The exponential form is deliberately weaker than the sharp
power `(v/u)^C`, but is sufficient on logarithmic physical windows. -/
theorem psi_interval_comparison
    {Ψ dΨ : ℝ → ℝ} {u v C : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hC : 0 ≤ C)
    (hpos : ∀ t ∈ Icc u v, 0 < Ψ t)
    (hderiv : ∀ t ∈ Icc u v, HasDerivAt Ψ (dΨ t) t)
    (hweighted : ∀ t ∈ Icc u v,
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t) :
    Ψ u ≤ Ψ v ∧
      Ψ v ≤ Ψ u * Real.exp (C * (v - u) / u) := by
  have huMem : u ∈ Icc u v := ⟨le_rfl, huv⟩
  have hvMem : v ∈ Icc u v := ⟨huv, le_rfl⟩
  have hcont : ContinuousOn Ψ (Icc u v) := by
    intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  have hdif : DifferentiableOn ℝ Ψ (interior (Icc u v)) := by
    intro t ht
    exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hderivNonneg : ∀ t ∈ interior (Icc u v), 0 ≤ deriv Ψ t := by
    intro t ht
    have htI : t ∈ Icc u v := interior_subset ht
    have htpos : 0 < t := hu.trans_le htI.1
    rw [(hderiv t htI).deriv]
    exact deriv_nonneg_of_weighted htpos (hweighted t htI).1
  have hmono : MonotoneOn Ψ (Icc u v) :=
    monotoneOn_of_deriv_nonneg (convex_Icc u v) hcont hdif hderivNonneg
  have hlower : Ψ u ≤ Ψ v := hmono huMem hvMem huv
  have hright : ∀ t ∈ Ico u v,
      HasDerivWithinAt Ψ (dΨ t) (Ici t) t := by
    intro t ht
    exact (hderiv t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico u v,
      ‖dΨ t‖ ≤ (C / u) * ‖Ψ t‖ := by
    intro t ht
    have htI : t ∈ Icc u v := ⟨ht.1, ht.2.le⟩
    have htpos : 0 < t := hu.trans_le ht.1
    have hΨpos : 0 < Ψ t := hpos t htI
    have hd0 : 0 ≤ dΨ t :=
      deriv_nonneg_of_weighted htpos (hweighted t htI).1
    have hfirst : dΨ t ≤ C * Ψ t / t :=
      (le_div_iff₀ htpos).2 (by
        simpa only [mul_comm] using (hweighted t htI).2)
    have hnum : 0 ≤ C * Ψ t := mul_nonneg hC hΨpos.le
    have hsecond : C * Ψ t / t ≤ C * Ψ t / u :=
      div_le_div_of_nonneg_left hnum hu ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg hd0, Real.norm_eq_abs,
      abs_of_pos hΨpos]
    calc
      dΨ t ≤ C * Ψ t / t := hfirst
      _ ≤ C * Ψ t / u := hsecond
      _ = (C / u) * Ψ t := by ring
  have hstart : ‖Ψ u‖ ≤ Ψ u := by
    rw [Real.norm_eq_abs, abs_of_pos (hpos u huMem)]
  have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := Ψ) (f' := dΨ) (δ := Ψ u) (K := C / u) (ε := 0)
    (a := u) (b := v) hcont hright hstart (by simpa only [add_zero] using hbound) v hvMem
  have hupper : Ψ v ≤ Ψ u * Real.exp ((C / u) * (v - u)) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (hpos v hvMem),
      gronwallBound_ε0] using hgronwall
  constructor
  · exact hlower
  · calc
      Ψ v ≤ Ψ u * Real.exp ((C / u) * (v - u)) := hupper
      _ = Ψ u * Real.exp (C * (v - u) / u) := by ring

/-- Convenient endpoint-ratio form of the same finite comparison. -/
theorem psi_interval_ratio_bounds
    {Ψ dΨ : ℝ → ℝ} {u v C : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hC : 0 ≤ C)
    (hpos : ∀ t ∈ Icc u v, 0 < Ψ t)
    (hderiv : ∀ t ∈ Icc u v, HasDerivAt Ψ (dΨ t) t)
    (hweighted : ∀ t ∈ Icc u v,
      0 ≤ t * dΨ t ∧ t * dΨ t ≤ C * Ψ t) :
    1 ≤ Ψ v / Ψ u ∧
      Ψ v / Ψ u ≤ Real.exp (C * (v - u) / u) := by
  have hcmp := psi_interval_comparison hu huv hC hpos hderiv hweighted
  have hΨu := hpos u ⟨le_rfl, huv⟩
  constructor
  · exact (le_div_iff₀ hΨu).2 (by simpa only [one_mul] using hcmp.1)
  · exact (div_le_iff₀ hΨu).2 (by simpa only [mul_comm] using hcmp.2)

end

end PrimeGapNormality.Prime.CoreRoughThresholdRegularity
