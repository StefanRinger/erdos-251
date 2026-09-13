import PrimeGapNormality.Prime.MertensConstant

/-!
# The remaining Abelian bridge for Mertens II

The zeta side of the comparison is now unconditional: the exact Euler
decomposition, the zeta asymptotic, and dominated convergence of the
prime-power correction identify the right limit of the prime Dirichlet
series as `-mertensPrimeCorrectionConstant`.

The only remaining analytic input is the Abelian implication from the
already proved discrete reciprocal-prime limit to that same Dirichlet
limit.  The final section proves that this implication immediately forces
the desired value of the discrete constant; it is kept visibly conditional
and is not presented as the final theorem.
-/

namespace PrimeGapNormality.Prime

open Filter Set

noncomputable section

/-- Unconditional right limit of the prime Dirichlet series, obtained from
the exact logarithmic Euler decomposition. -/
theorem tendsto_mertensPrimeDirichlet_add_log_sub_one :
    Tendsto
      (fun s : ℝ => mertensPrimeDirichlet s + Real.log (s - 1))
      (nhdsWithin 1 (Ioi 1))
      (nhds (-mertensPrimeCorrectionConstant)) := by
  have hraw := tendsto_log_riemannZeta_add_log_sub_one.sub
    tendsto_mertensPrimeCorrectionDirichlet
  have hraw' : Tendsto
      (fun s : ℝ =>
        (Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1)) -
          mertensPrimeCorrectionDirichlet s)
      (nhdsWithin 1 (Ioi 1))
      (nhds (-mertensPrimeCorrectionConstant)) := by
    simpa using hraw
  refine hraw'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [log_riemannZeta_eq_mertensPrime_add_correction hs]
  ring

/-- If the Abelian bridge has been established at a candidate discrete
limit `B`, uniqueness against the unconditional zeta-side limit identifies
`B` exactly. -/
theorem mertens_discrete_limit_value_of_abelian
    {B : ℝ}
    (hAbel : Tendsto
      (fun s : ℝ => mertensPrimeDirichlet s + Real.log (s - 1))
      (nhdsWithin 1 (Ioi 1))
      (nhds (B - Real.eulerMascheroniConstant))) :
    B = Real.eulerMascheroniConstant - mertensPrimeCorrectionConstant := by
  have huniq := tendsto_nhds_unique hAbel
    tendsto_mertensPrimeDirichlet_add_log_sub_one
  linarith

/-- Exact final reduction: a proof of the single Abelian implication for
arbitrary discrete limit values yields the fully identified Mertens-II
limit.  This theorem deliberately exposes, rather than hides, that remaining
analytic implication. -/
theorem mertensPrimeReciprocalSum_tendsto_of_abelian_bridge
    (hBridge : ∀ {B : ℝ},
      Tendsto
        (fun N : ℕ =>
          mertensPrimeReciprocalSum N - Real.log (Real.log N))
        atTop (nhds B) →
      Tendsto
        (fun s : ℝ => mertensPrimeDirichlet s + Real.log (s - 1))
        (nhdsWithin 1 (Ioi 1))
        (nhds (B - Real.eulerMascheroniConstant))) :
    Tendsto
      (fun N : ℕ =>
        mertensPrimeReciprocalSum N - Real.log (Real.log N))
      atTop
      (nhds
        (Real.eulerMascheroniConstant - mertensPrimeCorrectionConstant)) := by
  obtain ⟨B, hB⟩ := exists_tendsto_mertensPrimeReciprocalSum_sub_log_log
  have hvalue := mertens_discrete_limit_value_of_abelian (hBridge hB)
  rwa [← hvalue]

/-
The first and only remaining unconditional theorem is exactly:

  theorem tendsto_mertensPrimeDirichlet_add_log_sub_one_of_discrete
    {B : ℝ}
    (hB : Tendsto
      (fun N : ℕ => mertensPrimeReciprocalSum N - Real.log (Real.log N))
      atTop (nhds B)) :
    Tendsto
      (fun s : ℝ => mertensPrimeDirichlet s + Real.log (s - 1))
      (nhdsWithin 1 (Ioi 1))
      (nhds (B - Real.eulerMascheroniConstant))

Its proof requires the Abelian/Laplace passage for
`A(x) = sum_{p <= x} 1/p = log log x + B + o(1)` and the normalized integral
`integral exp(-u) * log u = -gamma`.  The zeta-side comparison and the final
uniqueness argument are fully discharged above.  No placeholder proposition
for this bridge is declared here.
-/

end

end PrimeGapNormality.Prime
