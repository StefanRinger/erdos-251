import PrimeGapNormality.Prime.PrimeSeries
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Paper condition D for primes (Chebyshev, no Kuperberg)

Paper D is `A(2 a_M) = 2M + o(M)` with `A(x) = #{n : a_n ≤ x}`. For
primes, `A = π`. Lean `nthPrime 0 = 2` is paper `p_1`, so
`π(nthPrime M) = M+1` exactly and the correctly indexed form is
`π(2 p_M) = 2(M+1) + o(M)`. The paper's `2M` and this `2(M+1)` differ
by `2/M → 0`.

Mathlib Chebyshev (`pi_ge`, `eventually_primeCounting_le`) gives the
sandwich `1-ε ≤ π(2 p_M)/(M+1) ≤ 4+ε`. The PNT-scale `Prop`
`IndexPassage nthPrime` (`π(2 p_M)/M → 2`) is not a Chebyshev theorem.
Dyadic counts `m_X = π(2X)-π(X)` (EndAPI `windowNX`) have Chebyshev
leading coefficient `2 log 2 - log 4 = 0`, so there is an
`O(X/log X)` upper bound but no matching positive Chebyshev lower
bound; Bertrand still gives `m_X ≥ 1`.

Source: `rounds/round104/01_gpt_paper_v0_2.tex` (eq:D); EndAPI
`nthPrime`; PrimeSeries Galois inversion; mathlib Chebyshev.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Filter
open scoped Topology

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### Paper D as a named `Prop` -/

/-- Paper D: `A(2 a_M) = 2M + o(M)` with `A = π`. Lean `M` is 0-based.
The displayed `2 * M` is the paper formula; see
`primeCounting_nthPrime` for the identity `π(nthPrime M) = M+1`. -/
def IndexPassage (a : ℕ → ℕ) : Prop :=
  Tendsto (fun M : ℕ => ((Nat.primeCounting (2 * a M) : ℝ) - 2 * M) / M)
    atTop (nhds 0)

/-- 0-based normalisation of D: `π(2 a_M) = 2(M+1) + o(M)`. -/
def IndexPassageSucc (a : ℕ → ℕ) : Prop :=
  Tendsto (fun M : ℕ =>
      ((Nat.primeCounting (2 * a M) : ℝ) - 2 * ((M : ℝ) + 1)) / M)
    atTop (nhds 0)

/-! ### Exact indexing -/

theorem primeCounting'_nthPrime (n : ℕ) :
    Nat.primeCounting' (nthPrime n) = n := by
  simpa [nthPrime] using Nat.primeCounting'_nth_eq n

theorem prime_nthPrime (n : ℕ) : Nat.Prime (nthPrime n) := by
  simpa [nthPrime] using Nat.prime_nth_prime n

/-- Exact Galois identity: there are `M+1` primes `≤ nthPrime M`. -/
theorem primeCounting_nthPrime (n : ℕ) :
    Nat.primeCounting (nthPrime n) = n + 1 := by
  have hp : Nat.Prime (nthPrime n) := prime_nthPrime n
  have hcount : Nat.count Nat.Prime (nthPrime n) = n :=
    primeCounting'_nthPrime n
  change Nat.count Nat.Prime (nthPrime n + 1) = n + 1
  rw [Nat.count_succ, hcount]
  simp [hp]

theorem primeCounting_nthPrime_cast (n : ℕ) :
    (Nat.primeCounting (nthPrime n) : ℝ) = (n : ℝ) + 1 := by
  rw [primeCounting_nthPrime, Nat.cast_add_one]

theorem nthPrime_le_iff_lt_primeCounting (n x : ℕ) :
    nthPrime n ≤ x ↔ n < Nat.primeCounting x :=
  (nthPrime_le_iff_succ_le_pi n x).trans Nat.succ_le_iff.symm

theorem two_mul_nthPrime_cast (M : ℕ) :
    ((2 * nthPrime M : ℕ) : ℝ) = 2 * (nthPrime M : ℝ) := by
  simp

theorem two_mul_cast (X : ℕ) : ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := by
  simp

theorem nthPrime_two_le (M : ℕ) : 2 ≤ nthPrime M :=
  nthPrime_zero.symm.trans_le (nthPrime_mono (Nat.zero_le M))

theorem nthPrime_one_lt_cast (M : ℕ) : (1 : ℝ) < nthPrime M := by
  have : (2 : ℕ) ≤ nthPrime M := nthPrime_two_le M
  exact_mod_cast lt_of_lt_of_le (by decide : (1 : ℕ) < 2) this

theorem nthPrime_cast_pos (M : ℕ) : (0 : ℝ) < nthPrime M :=
  lt_trans (by norm_num) (nthPrime_one_lt_cast M)

/-! ### Equivalence of the two D normalisations -/

private theorem indexPassage_add_two_div (a : ℕ → ℕ) (M : ℕ) :
    ((Nat.primeCounting (2 * a M) : ℝ) - 2 * M) / M =
      ((Nat.primeCounting (2 * a M) : ℝ) - 2 * ((M : ℝ) + 1)) / M +
        2 / M := by
  by_cases hM : M = 0
  · subst hM
    simp
  · have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
    field_simp [hM0]
    ring

theorem indexPassage_iff_indexPassageSucc (a : ℕ → ℕ) :
    IndexPassage a ↔ IndexPassageSucc a := by
  unfold IndexPassage IndexPassageSucc
  have h2 : Tendsto (fun M : ℕ => (2 : ℝ) / M) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  constructor
  · intro hf
    have hsub : Tendsto (fun M : ℕ =>
        ((Nat.primeCounting (2 * a M) : ℝ) - 2 * M) / M - 2 / M)
        atTop (nhds 0) := by
      simpa using hf.sub h2
    exact hsub.congr fun M => by
      rw [indexPassage_add_two_div a M, add_sub_cancel_right]
  · intro hg
    have hadd : Tendsto (fun M : ℕ =>
        ((Nat.primeCounting (2 * a M) : ℝ) - 2 * ((M : ℝ) + 1)) / M + 2 / M)
        atTop (nhds 0) := by
      simpa using hg.add h2
    exact hadd.congr fun M => (indexPassage_add_two_div a M).symm

theorem indexPassage_iff_tendsto_two (a : ℕ → ℕ) :
    IndexPassage a ↔
      Tendsto (fun M : ℕ => (Nat.primeCounting (2 * a M) : ℝ) / M)
        atTop (nhds 2) := by
  unfold IndexPassage
  constructor
  · intro hf
    have hsum : Tendsto (fun M : ℕ =>
        ((Nat.primeCounting (2 * a M) : ℝ) - 2 * M) / M + 2)
        atTop (nhds 2) := by
      simpa using hf.add (tendsto_const_nhds (x := (2 : ℝ)))
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hM0]
    all_goals ring
  · intro hg
    have hsub : Tendsto (fun M : ℕ =>
        (Nat.primeCounting (2 * a M) : ℝ) / M - 2)
        atTop (nhds 0) := by
      simpa using hg.sub (tendsto_const_nhds (x := (2 : ℝ)))
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hM0]

/-! ### Chebyshev constants -/

theorem two_mul_log_two_eq_log_four : 2 * Real.log 2 = Real.log 4 := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
  rw [h4, Real.log_pow]
  norm_cast

private theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

private theorem log_four_pos : 0 < Real.log 4 := by
  rw [← two_mul_log_two_eq_log_four]
  exact mul_pos (by norm_num) log_two_pos

theorem tendsto_nthPrime_atTop : Tendsto nthPrime atTop atTop :=
  tendsto_atTop_atTop_of_monotone nthPrime_mono fun b =>
    ⟨b, (Nat.le_add_right b 2).trans (nthPrime_ge_add_two b)⟩

theorem tendsto_nthPrime_cast_atTop :
    Tendsto (fun M : ℕ => (nthPrime M : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_nthPrime_atTop

theorem tendsto_two_mul_nthPrime_atTop :
    Tendsto (fun M : ℕ => 2 * nthPrime M) atTop atTop :=
  tendsto_atTop_atTop_of_monotone
    (fun _ _ h => Nat.mul_le_mul_left 2 (nthPrime_mono h)) fun b =>
      ⟨b, ((Nat.le_add_right b 2).trans (nthPrime_ge_add_two b)).trans
        (Nat.le_mul_of_pos_left (nthPrime b) (by omega : 0 < 2))⟩

theorem tendsto_log_nthPrime_atTop :
    Tendsto (fun M : ℕ => Real.log (nthPrime M : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_nthPrime_cast_atTop

private theorem tendsto_inv_nthPrime :
    Tendsto (fun M : ℕ => (nthPrime M : ℝ)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_nthPrime_cast_atTop

private theorem tendsto_log_nthPrime_div_self :
    Tendsto (fun M : ℕ => Real.log (nthPrime M : ℝ) / (nthPrime M : ℝ))
      atTop (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  exact (h0.comp tendsto_nthPrime_cast_atTop).congr fun M => Function.comp_apply

/-- `log p_M / log(2 p_M) → 1`. -/
theorem tendsto_log_nthPrime_div_log_two_mul :
    Tendsto (fun M : ℕ =>
        Real.log (nthPrime M : ℝ) / Real.log (2 * (nthPrime M : ℝ)))
      atTop (nhds 1) := by
  have hlog := tendsto_log_nthPrime_atTop
  have hc : Tendsto (fun M : ℕ => Real.log 2 / Real.log (nthPrime M : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp hlog).const_mul (Real.log 2)
  have hadd : Tendsto (fun M : ℕ =>
      (1 : ℝ) + Real.log 2 / Real.log (nthPrime M : ℝ))
      atTop (nhds (1 + 0)) :=
    (tendsto_const_nhds (x := (1 : ℝ))).add hc
  have hinv : Tendsto (fun M : ℕ =>
      ((1 : ℝ) + Real.log 2 / Real.log (nthPrime M : ℝ))⁻¹)
      atTop (nhds ((1 : ℝ) + 0)⁻¹) :=
    hadd.inv₀ (by norm_num)
  have hrew :
      (fun M : ℕ =>
          ((1 : ℝ) + Real.log 2 / Real.log (nthPrime M : ℝ))⁻¹) =ᶠ[atTop]
        fun M =>
          Real.log (nthPrime M : ℝ) /
            (Real.log 2 + Real.log (nthPrime M : ℝ)) := by
    filter_upwards [hlog.eventually_gt_atTop (0 : ℝ)] with M hx
    have hx0 : Real.log (nthPrime M : ℝ) ≠ 0 := hx.ne'
    field_simp [hx0]
    ring
  have hlim : Tendsto (fun M : ℕ =>
      Real.log (nthPrime M : ℝ) /
        (Real.log 2 + Real.log (nthPrime M : ℝ)))
      atTop (nhds 1) := by
    simpa [add_zero, inv_one] using hinv.congr' hrew
  refine hlim.congr' ?_
  filter_upwards [tendsto_nthPrime_cast_atTop.eventually_gt_atTop (0 : ℝ)]
    with M hp
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne']

private theorem tendsto_log_two_mul_succ_div_nthPrime :
    Tendsto (fun M : ℕ =>
      Real.log (2 * (nthPrime M : ℝ) + 1) / (nthPrime M : ℝ))
      atTop (nhds 0) := by
  have hlogp := tendsto_log_nthPrime_div_self
  have h4p : Tendsto (fun M : ℕ => Real.log 4 / (nthPrime M : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_nthPrime.const_mul (Real.log 4)
  have hsum : Tendsto (fun M : ℕ =>
      Real.log 4 / (nthPrime M : ℝ) +
        Real.log (nthPrime M : ℝ) / (nthPrime M : ℝ))
      atTop (nhds 0) := by
    simpa using h4p.add hlogp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ))) hsum (fun M => ?lo) (fun M => ?hi)
  · refine div_nonneg ?_ (Nat.cast_nonneg _)
    have h1 : (1 : ℝ) ≤ 2 * (nthPrime M : ℝ) + 1 := by
      linarith [nthPrime_cast_pos M]
    exact Real.log_nonneg h1
  · have hppos : (0 : ℝ) < nthPrime M := nthPrime_cast_pos M
    have hargpos : (0 : ℝ) < 2 * (nthPrime M : ℝ) + 1 := by linarith
    have hlearg : 2 * (nthPrime M : ℝ) + 1 ≤ 4 * (nthPrime M : ℝ) := by
      linarith [nthPrime_one_lt_cast M]
    have hlogle : Real.log (2 * (nthPrime M : ℝ) + 1) ≤
        Real.log (4 * (nthPrime M : ℝ)) :=
      Real.log_le_log hargpos hlearg
    have hlog4 : Real.log (4 * (nthPrime M : ℝ)) =
        Real.log 4 + Real.log (nthPrime M : ℝ) :=
      Real.log_mul (by norm_num) hppos.ne'
    have : Real.log (2 * (nthPrime M : ℝ) + 1) / (nthPrime M : ℝ) ≤
        (Real.log 4 + Real.log (nthPrime M : ℝ)) / (nthPrime M : ℝ) :=
      div_le_div_of_nonneg_right (hlogle.trans_eq hlog4) (Nat.cast_nonneg _)
    simpa [add_div] using this

private theorem tendsto_log_succ_div_nthPrime :
    Tendsto (fun M : ℕ =>
      Real.log ((nthPrime M : ℝ) + 1) / (nthPrime M : ℝ))
      atTop (nhds 0) := by
  have hlogp := tendsto_log_nthPrime_div_self
  have h2p : Tendsto (fun M : ℕ => Real.log 2 / (nthPrime M : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_nthPrime.const_mul (Real.log 2)
  have hsum : Tendsto (fun M : ℕ =>
      Real.log 2 / (nthPrime M : ℝ) +
        Real.log (nthPrime M : ℝ) / (nthPrime M : ℝ))
      atTop (nhds 0) := by
    simpa using h2p.add hlogp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ))) hsum (fun M => ?lo) (fun M => ?hi)
  · refine div_nonneg ?_ (Nat.cast_nonneg _)
    have hp : (1 : ℝ) < nthPrime M := nthPrime_one_lt_cast M
    have harg : (1 : ℝ) ≤ (nthPrime M : ℝ) + 1 :=
      le_trans (le_of_lt hp) (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
    exact Real.log_nonneg harg
  · have hppos : (0 : ℝ) < nthPrime M := nthPrime_cast_pos M
    have hargpos : (0 : ℝ) < (nthPrime M : ℝ) + 1 := by linarith
    have hlearg : (nthPrime M : ℝ) + 1 ≤ 2 * (nthPrime M : ℝ) := by
      linarith [nthPrime_one_lt_cast M]
    have hlogle : Real.log ((nthPrime M : ℝ) + 1) ≤
        Real.log (2 * (nthPrime M : ℝ)) :=
      Real.log_le_log hargpos hlearg
    have hlog2 : Real.log (2 * (nthPrime M : ℝ)) =
        Real.log 2 + Real.log (nthPrime M : ℝ) :=
      Real.log_mul (by norm_num) hppos.ne'
    have : Real.log ((nthPrime M : ℝ) + 1) / (nthPrime M : ℝ) ≤
        (Real.log 2 + Real.log (nthPrime M : ℝ)) / (nthPrime M : ℝ) :=
      div_le_div_of_nonneg_right (hlogle.trans_eq hlog2) (Nat.cast_nonneg _)
    simpa [add_div] using this

/-! ### Mathlib Chebyshev on `ℕ` -/

theorem eventually_primeCounting_le_nat {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤
        (Real.log 4 + ε) * n / Real.log n := by
  have h := (Chebyshev.eventually_primeCounting_le hε).natCast_atTop
  filter_upwards [h, eventually_ge_atTop 2] with n hn hn2
  have hfloor : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  simpa [hfloor] using hn

/-! ### Comparison functions for the index ratio -/

/-- Chebyshev lower comparison for `π(2 p_M)/(M+1)`. Tends to
`2 log 2 / (log 4 + η)`. -/
noncomputable def chebyshevLowerRatio (η : ℝ) (M : ℕ) : ℝ :=
  (2 * Real.log 2 -
      Real.log (2 * (nthPrime M : ℝ) + 1) / (nthPrime M : ℝ)) *
    (Real.log (nthPrime M : ℝ) / Real.log (2 * (nthPrime M : ℝ))) /
      (Real.log 4 + η)

/-- Chebyshev upper comparison for `π(2 p_M)/(M+1)`. Tends to
`2 (log 4 + η) / log 2`. -/
noncomputable def chebyshevUpperRatio (η : ℝ) (M : ℕ) : ℝ :=
  (2 * (Real.log 4 + η) / Real.log 2) *
    (Real.log (nthPrime M : ℝ) / Real.log (2 * (nthPrime M : ℝ))) /
      (1 - Real.log ((nthPrime M : ℝ) + 1) /
        ((nthPrime M : ℝ) * Real.log 2))

theorem tendsto_chebyshevLowerRatio {η : ℝ} (hη : 0 < η) :
    Tendsto (chebyshevLowerRatio η) atTop
      (nhds (2 * Real.log 2 / (Real.log 4 + η))) := by
  have ha : Tendsto (fun M : ℕ =>
      2 * Real.log 2 -
        Real.log (2 * (nthPrime M : ℝ) + 1) / (nthPrime M : ℝ))
      atTop (nhds (2 * Real.log 2)) := by
    simpa using
      (tendsto_const_nhds (x := (2 * Real.log 2 : ℝ))).sub
        tendsto_log_two_mul_succ_div_nthPrime
  have hb := tendsto_log_nthPrime_div_log_two_mul
  have hab := ha.mul hb
  have hlim : Tendsto (fun M : ℕ =>
      (2 * Real.log 2 -
          Real.log (2 * (nthPrime M : ℝ) + 1) / (nthPrime M : ℝ)) *
        (Real.log (nthPrime M : ℝ) / Real.log (2 * (nthPrime M : ℝ))) /
          (Real.log 4 + η))
      atTop (nhds (2 * Real.log 2 / (Real.log 4 + η))) := by
    simpa [mul_one] using hab.div_const (Real.log 4 + η)
  exact hlim.congr fun M => by unfold chebyshevLowerRatio; rfl

theorem tendsto_chebyshevUpperRatio {η : ℝ} (hη : 0 < η) :
    Tendsto (chebyshevUpperRatio η) atTop
      (nhds (2 * (Real.log 4 + η) / Real.log 2)) := by
  have hb := tendsto_log_nthPrime_div_log_two_mul
  have hfrac : Tendsto (fun M : ℕ =>
      Real.log ((nthPrime M : ℝ) + 1) /
        ((nthPrime M : ℝ) * Real.log 2)) atTop (nhds 0) := by
    have h1 := tendsto_log_succ_div_nthPrime
    have hfun :
        (fun M : ℕ =>
            Real.log ((nthPrime M : ℝ) + 1) /
              ((nthPrime M : ℝ) * Real.log 2)) =
          fun M =>
            (Real.log ((nthPrime M : ℝ) + 1) / (nthPrime M : ℝ)) /
              Real.log 2 := by
      funext M
      have hp0 : (nthPrime M : ℝ) ≠ 0 := (nthPrime_cast_pos M).ne'
      have hlog : Real.log 2 ≠ 0 := log_two_pos.ne'
      field_simp [hp0, hlog]
    rw [hfun]
    have hdiv := h1.div_const (Real.log 2)
    simpa using hdiv
  have hden : Tendsto (fun M : ℕ =>
      (1 : ℝ) - Real.log ((nthPrime M : ℝ) + 1) /
        ((nthPrime M : ℝ) * Real.log 2)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hfrac
  have hnum : Tendsto (fun M : ℕ =>
      (2 * (Real.log 4 + η) / Real.log 2) *
        (Real.log (nthPrime M : ℝ) / Real.log (2 * (nthPrime M : ℝ))))
      atTop (nhds (2 * (Real.log 4 + η) / Real.log 2)) := by
    simpa using
      (tendsto_const_nhds
        (x := (2 * (Real.log 4 + η) / Real.log 2 : ℝ))).mul hb
  have hlim : Tendsto (fun M : ℕ =>
      ((2 * (Real.log 4 + η) / Real.log 2) *
        (Real.log (nthPrime M : ℝ) / Real.log (2 * (nthPrime M : ℝ)))) /
        (1 - Real.log ((nthPrime M : ℝ) + 1) /
          ((nthPrime M : ℝ) * Real.log 2)))
      atTop (nhds (2 * (Real.log 4 + η) / Real.log 2)) := by
    have hdiv := hnum.div hden (by norm_num)
    have hpt := hdiv.congr fun M => rfl
    rw [div_one] at hpt
    exact hpt
  exact hlim.congr fun M => by unfold chebyshevUpperRatio; rfl

private theorem chebyshevLowerRatio_le_index_ratio {η : ℝ} (hη : 0 < η)
    {M : ℕ}
    (hπle : (Nat.primeCounting (nthPrime M) : ℝ) ≤
      (Real.log 4 + η) * (nthPrime M : ℝ) / Real.log (nthPrime M : ℝ))
    (hnum : 0 ≤
      2 * (nthPrime M : ℝ) * Real.log 2 -
        Real.log (2 * (nthPrime M : ℝ) + 1)) :
    chebyshevLowerRatio η M ≤
      (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) := by
  set p : ℝ := (nthPrime M : ℝ)
  have hppos : 0 < p := nthPrime_cast_pos M
  have hlogp : 0 < Real.log p := Real.log_pos (nthPrime_one_lt_cast M)
  have hlog2p : 0 < Real.log (2 * p) :=
    Real.log_pos (by linarith [nthPrime_one_lt_cast M])
  have hC : 0 < Real.log 4 + η := add_pos log_four_pos hη
  have hπid : (Nat.primeCounting (nthPrime M) : ℝ) = (M : ℝ) + 1 :=
    primeCounting_nthPrime_cast M
  rw [hπid] at hπle
  have hMpos : 0 < (M : ℝ) + 1 := by positivity
  have hrecip :
      Real.log p / ((Real.log 4 + η) * p) ≤ 1 / ((M : ℝ) + 1) := by
    have h1 := one_div_le_one_div_of_le hMpos hπle
    have hrew : 1 / ((Real.log 4 + η) * p / Real.log p) =
        Real.log p / ((Real.log 4 + η) * p) := by
      field_simp [hC.ne', hppos.ne', hlogp.ne']
    rwa [hrew] at h1
  have hπge : (2 * p * Real.log 2 - Real.log (2 * p + 1)) / Real.log (2 * p) ≤
      (Nat.primeCounting (2 * nthPrime M) : ℝ) := by
    have hge := Chebyshev.pi_ge (2 * nthPrime M)
    have hcast : ((2 * nthPrime M : ℕ) : ℝ) = 2 * p := by
      simp [p, Nat.cast_mul]
    have hsucc : ((2 * nthPrime M + 1 : ℕ) : ℝ) = 2 * p + 1 := by
      simp [p, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simpa [hcast, hsucc] using hge
  have hπnn : 0 ≤ (Nat.primeCounting (2 * nthPrime M) : ℝ) :=
    Nat.cast_nonneg _
  have hBnn : 0 ≤ Real.log p / ((Real.log 4 + η) * p) :=
    div_nonneg hlogp.le (mul_nonneg hC.le hppos.le)
  have hprod :=
    mul_le_mul hπge hrecip hBnn hπnn
  have hL : chebyshevLowerRatio η M =
      ((2 * p * Real.log 2 - Real.log (2 * p + 1)) / Real.log (2 * p)) *
        (Real.log p / ((Real.log 4 + η) * p)) := by
    unfold chebyshevLowerRatio
    have hp_eq : (nthPrime M : ℝ) = p := rfl
    simp only [hp_eq]
    have hp0 : p ≠ 0 := hppos.ne'
    have hlog2p0 : Real.log (2 * p) ≠ 0 := hlog2p.ne'
    have hC0 : Real.log 4 + η ≠ 0 := hC.ne'
    have hsplit :
        2 * Real.log 2 - Real.log (2 * p + 1) / p =
          (2 * p * Real.log 2 - Real.log (2 * p + 1)) / p := by
      field_simp [hp0]
    rw [hsplit]
    conv =>
      lhs
      rw [div_mul_div_comm, div_div]
    conv =>
      rhs
      rw [div_mul_div_comm]
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hp0 hlog2p0) hC0)
      (mul_ne_zero hlog2p0 (mul_ne_zero hC0 hp0))]
    ring
  have hdiv : (Nat.primeCounting (2 * nthPrime M) : ℝ) * (1 / ((M : ℝ) + 1)) =
      (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) := by
    field_simp [hMpos.ne']
  rw [hL, ← hdiv]
  exact hprod

private theorem index_ratio_le_chebyshevUpperRatio {η : ℝ} (hη : 0 < η)
    {M : ℕ}
    (hπ2 : (Nat.primeCounting (2 * nthPrime M) : ℝ) ≤
      (Real.log 4 + η) * (2 * (nthPrime M : ℝ)) /
        Real.log (2 * (nthPrime M : ℝ)))
    (hden : 0 <
      (nthPrime M : ℝ) * Real.log 2 - Real.log ((nthPrime M : ℝ) + 1)) :
    (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) ≤
      chebyshevUpperRatio η M := by
  set p : ℝ := (nthPrime M : ℝ)
  have hppos : 0 < p := nthPrime_cast_pos M
  have hlogp : 0 < Real.log p := Real.log_pos (nthPrime_one_lt_cast M)
  have hlog2p : 0 < Real.log (2 * p) :=
    Real.log_pos (by linarith [nthPrime_one_lt_cast M])
  have hC : 0 < Real.log 4 + η := add_pos log_four_pos hη
  have hπlo : (p * Real.log 2 - Real.log (p + 1)) / Real.log p ≤
      (M : ℝ) + 1 := by
    have hge := Chebyshev.pi_ge (nthPrime M)
    have hπid : (Nat.primeCounting (nthPrime M) : ℝ) = (M : ℝ) + 1 :=
      primeCounting_nthPrime_cast M
    have hsucc : ((nthPrime M + 1 : ℕ) : ℝ) = p + 1 := by
      simp [p, Nat.cast_add, Nat.cast_one]
    simpa [hπid, hsucc] using hge
  have hMpos : 0 < (M : ℝ) + 1 := by positivity
  have hApos : 0 < (p * Real.log 2 - Real.log (p + 1)) / Real.log p :=
    div_pos hden hlogp
  have hrecip : 1 / ((M : ℝ) + 1) ≤
      Real.log p / (p * Real.log 2 - Real.log (p + 1)) := by
    have h1 := one_div_le_one_div_of_le hApos hπlo
    have hrew : 1 / ((p * Real.log 2 - Real.log (p + 1)) / Real.log p) =
        Real.log p / (p * Real.log 2 - Real.log (p + 1)) := by
      field_simp [hden.ne', hlogp.ne']
    rwa [hrew] at h1
  have hUπnn : 0 ≤ (Real.log 4 + η) * (2 * p) / Real.log (2 * p) :=
    div_nonneg (mul_nonneg hC.le (mul_nonneg (by norm_num) hppos.le))
      hlog2p.le
  have hRnn : 0 ≤ 1 / ((M : ℝ) + 1) := div_nonneg (by norm_num) hMpos.le
  have hprod := mul_le_mul hπ2 hrecip hRnn hUπnn
  have hU : chebyshevUpperRatio η M =
      ((Real.log 4 + η) * (2 * p) / Real.log (2 * p)) *
        (Real.log p / (p * Real.log 2 - Real.log (p + 1))) := by
    unfold chebyshevUpperRatio
    have hp_eq : (nthPrime M : ℝ) = p := rfl
    simp only [hp_eq]
    have hp0 : p ≠ 0 := hppos.ne'
    have hlog2p0 : Real.log (2 * p) ≠ 0 := hlog2p.ne'
    have hC0 : Real.log 4 + η ≠ 0 := hC.ne'
    have hlog20 : Real.log 2 ≠ 0 := log_two_pos.ne'
    have hden0 : p * Real.log 2 - Real.log (p + 1) ≠ 0 := hden.ne'
    have hpl : p * Real.log 2 ≠ 0 := mul_ne_zero hp0 hlog20
    have hsplit :
        (1 : ℝ) - Real.log (p + 1) / (p * Real.log 2) =
          (p * Real.log 2 - Real.log (p + 1)) / (p * Real.log 2) := by
      field_simp [hp0, hlog20]
    rw [hsplit, div_div_eq_mul_div]
    conv =>
      rhs
      rw [mul_div_assoc']
    rw [div_eq_div_iff hden0 hden0]
    field_simp [hp0, hlog2p0, hC0, hlog20, hden0, hpl]
  have hdiv : (Nat.primeCounting (2 * nthPrime M) : ℝ) * (1 / ((M : ℝ) + 1)) =
      (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) := by
    field_simp [hMpos.ne']
  rw [hU, ← hdiv]
  exact hprod

/-! ### Pointwise Chebyshev numerators -/

private theorem eventually_chebyshev_num_two_nthPrime_nonneg :
    ∀ᶠ M : ℕ in atTop,
      0 ≤ 2 * (nthPrime M : ℝ) * Real.log 2 -
        Real.log (2 * (nthPrime M : ℝ) + 1) := by
  have ha : Tendsto (fun M : ℕ =>
      2 * Real.log 2 -
        Real.log (2 * (nthPrime M : ℝ) + 1) / (nthPrime M : ℝ))
      atTop (nhds (2 * Real.log 2 - 0)) :=
    tendsto_const_nhds.sub tendsto_log_two_mul_succ_div_nthPrime
  have hpos : 0 < 2 * Real.log 2 - 0 := by
    simpa using mul_pos (by norm_num : (0 : ℝ) < 2) log_two_pos
  filter_upwards [ha.eventually_const_lt hpos,
    tendsto_nthPrime_cast_atTop.eventually_gt_atTop (0 : ℝ)] with M hM hp
  have hp0 : (nthPrime M : ℝ) ≠ 0 := hp.ne'
  have hmul : 0 < (nthPrime M : ℝ) *
      (2 * Real.log 2 -
        Real.log (2 * (nthPrime M : ℝ) + 1) / (nthPrime M : ℝ)) :=
    mul_pos hp hM
  have hrew : (nthPrime M : ℝ) *
        (2 * Real.log 2 -
          Real.log (2 * (nthPrime M : ℝ) + 1) / (nthPrime M : ℝ)) =
      2 * (nthPrime M : ℝ) * Real.log 2 -
        Real.log (2 * (nthPrime M : ℝ) + 1) := by
    field_simp [hp0]
  simpa [hrew] using hmul.le

private theorem eventually_chebyshev_den_nthPrime_pos :
    ∀ᶠ M : ℕ in atTop,
      0 < (nthPrime M : ℝ) * Real.log 2 - Real.log ((nthPrime M : ℝ) + 1) := by
  have ha : Tendsto (fun M : ℕ =>
      Real.log 2 - Real.log ((nthPrime M : ℝ) + 1) / (nthPrime M : ℝ))
      atTop (nhds (Real.log 2 - 0)) :=
    tendsto_const_nhds.sub tendsto_log_succ_div_nthPrime
  have hpos : 0 < Real.log 2 - 0 := by simpa using log_two_pos
  filter_upwards [ha.eventually_const_lt hpos,
    tendsto_nthPrime_cast_atTop.eventually_gt_atTop (0 : ℝ)] with M hM hp
  have hp0 : (nthPrime M : ℝ) ≠ 0 := hp.ne'
  have hmul : 0 < (nthPrime M : ℝ) *
      (Real.log 2 - Real.log ((nthPrime M : ℝ) + 1) / (nthPrime M : ℝ)) :=
    mul_pos hp hM
  have hrew : (nthPrime M : ℝ) *
        (Real.log 2 - Real.log ((nthPrime M : ℝ) + 1) / (nthPrime M : ℝ)) =
      (nthPrime M : ℝ) * Real.log 2 - Real.log ((nthPrime M : ℝ) + 1) := by
    field_simp [hp0]
  simpa [hrew] using hmul

private theorem eventually_index_ratio_ge_lower {η : ℝ} (hη : 0 < η) :
    ∀ᶠ M : ℕ in atTop,
      chebyshevLowerRatio η M ≤
        (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) := by
  have hπ := tendsto_nthPrime_atTop.eventually
    (eventually_primeCounting_le_nat hη)
  filter_upwards [hπ, eventually_chebyshev_num_two_nthPrime_nonneg]
    with M hπle hnum
  exact chebyshevLowerRatio_le_index_ratio hη hπle hnum

private theorem eventually_index_ratio_le_upper {η : ℝ} (hη : 0 < η) :
    ∀ᶠ M : ℕ in atTop,
      (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) ≤
        chebyshevUpperRatio η M := by
  have hπ2 := tendsto_two_mul_nthPrime_atTop.eventually
    (eventually_primeCounting_le_nat hη)
  filter_upwards [hπ2, eventually_chebyshev_den_nthPrime_pos] with M hπ2le hden
  have hcast : ((2 * nthPrime M : ℕ) : ℝ) = 2 * (nthPrime M : ℝ) :=
    two_mul_nthPrime_cast M
  have hπ2' : (Nat.primeCounting (2 * nthPrime M) : ℝ) ≤
      (Real.log 4 + η) * (2 * (nthPrime M : ℝ)) /
        Real.log (2 * (nthPrime M : ℝ)) := by
    simpa [hcast] using hπ2le
  exact index_ratio_le_chebyshevUpperRatio hη hπ2' hden

private theorem one_sub_lt_chebyshev_lower_limit {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (1 : ℝ) - ε < 2 * Real.log 2 / (Real.log 4 + ε * Real.log 2) := by
  have ha : 0 < Real.log 2 := log_two_pos
  rw [← two_mul_log_two_eq_log_four]
  have hC : 0 < 2 * Real.log 2 + ε * Real.log 2 := by
    have : 0 < ε * Real.log 2 := mul_pos hε0 ha
    linarith
  rw [lt_div_iff₀ hC]
  have hexp : (1 - ε) * (2 * Real.log 2 + ε * Real.log 2) =
      2 * Real.log 2 - (ε + ε * ε) * Real.log 2 := by ring
  rw [hexp]
  have hsum : 0 < ε + ε * ε :=
    add_pos_of_pos_of_nonneg hε0 (mul_nonneg hε0.le hε0.le)
  have : 0 < (ε + ε * ε) * Real.log 2 := mul_pos hsum ha
  linarith

private theorem chebyshev_upper_limit_eq {ε : ℝ} :
    2 * (Real.log 4 + ε * Real.log 2 / 4) / Real.log 2 = 4 + ε / 2 := by
  rw [← two_mul_log_two_eq_log_four]
  have ha : Real.log 2 ≠ 0 := log_two_pos.ne'
  field_simp [ha]
  ring

private theorem chebyshev_upper_limit_lt {ε : ℝ} (hε : 0 < ε) :
    2 * (Real.log 4 + ε * Real.log 2 / 4) / Real.log 2 < 4 + ε := by
  rw [chebyshev_upper_limit_eq]
  linarith

/-- Chebyshev form of D for primes: `1-ε ≤ π(2 p_M)/(M+1) ≤ 4+ε`.
This is the unconditional substitute for paper `π(2 p_M) = 2(M+1)+o(M)`.
The constants `1` and `4` are `2 log 2 / log 4` and `2 log 4 / log 2`. -/
theorem chebyshev_index_passage {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      1 - ε ≤
          (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) ∧
        (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) ≤
          4 + ε := by
  have hηu : 0 < ε * Real.log 2 / 4 := by
    exact div_pos (mul_pos hε log_two_pos) (by norm_num)
  have hupper := eventually_index_ratio_le_upper hηu
  have hUlim := tendsto_chebyshevUpperRatio hηu
  have hUlt : 2 * (Real.log 4 + ε * Real.log 2 / 4) / Real.log 2 < 4 + ε :=
    chebyshev_upper_limit_lt hε
  have hupper' : ∀ᶠ M : ℕ in atTop,
      (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) ≤ 4 + ε := by
    filter_upwards [hupper, hUlim.eventually_lt_const hUlt] with M hle hU
    exact hle.trans (le_of_lt hU)
  have hlower' : ∀ᶠ M : ℕ in atTop,
      1 - ε ≤
        (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) := by
    by_cases hε1 : (1 : ℝ) ≤ ε
    · refine Eventually.of_forall fun M => ?_
      have hnn : 0 ≤
          (Nat.primeCounting (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) :=
        div_nonneg (Nat.cast_nonneg _) (by positivity)
      exact le_trans (sub_nonpos.mpr hε1) hnn
    · push Not at hε1
      have hηl : 0 < ε * Real.log 2 := mul_pos hε log_two_pos
      have hLlim := tendsto_chebyshevLowerRatio hηl
      have hLgt : (1 : ℝ) - ε <
          2 * Real.log 2 / (Real.log 4 + ε * Real.log 2) :=
        one_sub_lt_chebyshev_lower_limit hε hε1
      have hlower := eventually_index_ratio_ge_lower hηl
      filter_upwards [hlower, hLlim.eventually_const_lt hLgt]
        with M hle hL
      exact (le_of_lt hL).trans hle
  filter_upwards [hlower', hupper'] with M hl hu
  exact ⟨hl, hu⟩

/-! ### Dyadic index counts `m_X = π(2X) - π(X)` -/

theorem windowNX_card_Ico (X : ℕ) :
    windowNX X =
      (Finset.Ico (Nat.primeCounting X)
        (Nat.primeCounting (2 * X))).card := by
  rw [windowNX, Nat.card_Ico]

theorem windowNX_cast (X : ℕ) :
    (windowNX X : ℝ) =
      (Nat.primeCounting (2 * X) : ℝ) - Nat.primeCounting X := by
  have hle : Nat.primeCounting X ≤ Nat.primeCounting (2 * X) :=
    Nat.monotone_primeCounting (by omega : X ≤ 2 * X)
  rw [windowNX, Nat.cast_sub hle]

theorem mem_dyadic_prime_index_iff {n X : ℕ} :
    n ∈ Finset.Ico (Nat.primeCounting X) (Nat.primeCounting (2 * X)) ↔
      X < nthPrime n ∧ nthPrime n ≤ 2 * X := by
  constructor
  · intro h
    rw [Finset.mem_Ico] at h
    refine ⟨?_, (nthPrime_le_iff_lt_primeCounting n (2 * X)).mpr h.2⟩
    have : ¬ n < Nat.primeCounting X := not_lt.mpr h.1
    rw [← nthPrime_le_iff_lt_primeCounting] at this
    exact lt_of_not_ge this
  · intro ⟨hlt, hle⟩
    rw [Finset.mem_Ico]
    refine ⟨?_, (nthPrime_le_iff_lt_primeCounting n (2 * X)).mp hle⟩
    exact le_of_not_gt fun hn =>
      hlt.not_ge ((nthPrime_le_iff_lt_primeCounting n X).mpr hn)

/-- Bertrand: `m_X ≥ 1` for `X > 0`. Chebyshev constants cancel on
`(X, 2X]`, so this is the unconditional lower bound available here. -/
theorem windowNX_pos_of_pos {X : ℕ} (hX : 0 < X) : 0 < windowNX X := by
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul X (ne_of_gt hX)
  have hsub : Nat.primesLE X ⊆ Nat.primesLE (2 * X) :=
    Nat.primesLE_mono (by omega : X ≤ 2 * X)
  have hpX : p ∉ Nat.primesLE X := by
    simp [Nat.mem_primesLE, hp, not_le.mpr hlt]
  have hp2 : p ∈ Nat.primesLE (2 * X) := Nat.mem_primesLE.mpr ⟨hle, hp⟩
  have hss : Nat.primesLE X ⊂ Nat.primesLE (2 * X) := by
    refine (Finset.ssubset_iff_subset_ne).2 ⟨hsub, ?_⟩
    intro heq
    exact hpX (heq.symm ▸ hp2)
  have hcard := card_lt_card hss
  rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
    at hcard
  exact Nat.sub_pos_of_lt hcard

/-- Chebyshev upper bound: `m_X = O(X / log X)`. The matching lower
bound `m_X ≫ X / log X` is not a Chebyshev theorem
(`2 log 2 - log 4 = 0`). -/
theorem eventually_windowNX_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      (windowNX X : ℝ) ≤
        (2 * (Real.log 4 + ε)) * (X : ℝ) / Real.log X := by
  have h2 : Tendsto (fun X : ℕ => 2 * X) atTop atTop :=
    tendsto_atTop_atTop_of_monotone
      (fun _ _ h => Nat.mul_le_mul_left 2 h)
      fun n => ⟨n, Nat.le_mul_of_pos_left n (by omega : 0 < 2)⟩
  have hπ := h2.eventually (eventually_primeCounting_le_nat hε)
  filter_upwards [hπ, eventually_ge_atTop 3] with X hπ2 hX
  have hxpos : (0 : ℝ) < X :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 3) hX)
  have hX1 : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hX)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  have hcast : ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := two_mul_cast X
  have hπ2' : (Nat.primeCounting (2 * X) : ℝ) ≤
      (Real.log 4 + ε) * (2 * (X : ℝ)) / Real.log (2 * (X : ℝ)) := by
    simpa [hcast] using hπ2
  have hwin : (windowNX X : ℝ) ≤ (Nat.primeCounting (2 * X) : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have hXle2 : (X : ℝ) ≤ 2 * (X : ℝ) := by
    have hx0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    linarith
  have hlogle : Real.log (X : ℝ) ≤ Real.log (2 * (X : ℝ)) :=
    Real.log_le_log hxpos hXle2
  have hC : 0 ≤ Real.log 4 + ε := add_nonneg log_four_pos.le hε.le
  have hdiv : (Real.log 4 + ε) * (2 * (X : ℝ)) / Real.log (2 * (X : ℝ)) ≤
      (Real.log 4 + ε) * (2 * (X : ℝ)) / Real.log (X : ℝ) :=
    div_le_div_of_nonneg_left
      (mul_nonneg hC (mul_nonneg (by norm_num) hxpos.le)) hlogX hlogle
  have htarget : (Real.log 4 + ε) * (2 * (X : ℝ)) / Real.log (X : ℝ) =
      (2 * (Real.log 4 + ε)) * (X : ℝ) / Real.log (X : ℝ) := by ring
  linarith [hwin, hπ2', hdiv, htarget]

end PrimeGapNormality.Prime
