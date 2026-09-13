import PrimeGapNormality.Prime.ModelConcentration
import PrimeGapNormality.Prime.ResidueMcDiarmid
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Categorical residue Hoeffding (v0.4 Paket 4 / R105 E)

Boolean McDiarmid in `ModelConcentration` / `ResidueMcDiarmid` is the
thinning stage. Middle-stage residues live in `Fin (p-1)`, not `{0,1}`.
This leaf does **not** encode a `p`-valued coordinate as `log p` bits.

Route: convexity of `x ↦ exp(t x)` dominates any finite law on an
interval `[a,a+c]` by the two endpoints; the centred two-point law is
`two_point_mgf_le`. One coordinate of a product is then a slice of
diameter `c_i`. Repeating that step by `Fin.snoc` gives a dependent
product `Π_{i : Fin n} α i`. Widths instantiate to public
`residueWidth = 2(h/p+1)`.

The tail is `exp(-u² / Σ c_i²)`, not the sharp `2u²` constant.

Source: `rounds/round105/00_grok_repair_priorities.md` E;
`rounds/round105/02_gpt_model_audit.md` §3;
`rounds/round106/09_gpt_v04_lean_audit_and_grok_order.md` Paket 4;
`ModelConcentration.two_point_mgf_le`; `ResidueMcDiarmid.residueWidth`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 800000

/-! ### Scalar endpoint / secant domination -/

/-- Convexity of the exponential: on `[a,a+c]` the graph lies below the
secant through the endpoints. -/
theorem exp_mul_endpoint_secant {a c x t : ℝ} (hc : 0 < c)
    (hx0 : a ≤ x) (hx1 : x ≤ a + c) :
    Real.exp (t * x) ≤
      ((a + c - x) / c) * Real.exp (t * a) +
        ((x - a) / c) * Real.exp (t * (a + c)) := by
  set θ := (x - a) / c
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hx0) hc.le
  have hx1' : x ≤ c + a := by simpa [add_comm] using hx1
  have hθ1 : θ ≤ 1 := (div_le_one hc).mpr (sub_le_iff_le_add.mpr hx1')
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hsum : (1 - θ) + θ = 1 := by ring
  have hθc : θ * c = x - a := by
    simpa [θ] using div_mul_cancel₀ (x - a) hc.ne'
  have hx : t * x = (1 - θ) * (t * a) + θ * (t * (a + c)) := by
    have hx' : x = (1 - θ) * a + θ * (a + c) := by
      have hxθ : x = θ * c + a := by
        rw [hθc]
        ring
      rw [hxθ]
      ring
    rw [hx']
    ring
  have hconv :=
    convexOn_exp.2 (Set.mem_univ (t * a)) (Set.mem_univ (t * (a + c)))
      h1θ hθ0 hsum
  have hconv' :
      Real.exp ((1 - θ) * (t * a) + θ * (t * (a + c))) ≤
        (1 - θ) * Real.exp (t * a) + θ * Real.exp (t * (a + c)) := by
    simpa [smul_eq_mul] using hconv
  have hθrew : 1 - θ = (a + c - x) / c := by
    have hmul : (1 - θ) * c = a + c - x := by
      calc
        (1 - θ) * c = c - θ * c := by ring
        _ = c - (x - a) := by rw [hθc]
        _ = a + c - x := by ring
    exact (eq_div_iff hc.ne').mpr hmul
  rw [← hx] at hconv'
  simpa [hθrew, θ] using hconv'

/-- Finite-space expectation. -/
noncomputable def finExpect {Ω : Type*} [Fintype Ω] (μ F : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, μ ω * F ω

theorem finExpect_const {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (a : ℝ)
    (hμ1 : ∑ ω : Ω, μ ω = 1) :
    finExpect μ (fun _ => a) = a := by
  unfold finExpect
  rw [← sum_mul, hμ1, one_mul]

theorem nonempty_of_mass_one {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ}
    (hμ1 : ∑ ω : Ω, μ ω = 1) : Nonempty Ω := by
  by_contra h
  have : IsEmpty Ω := not_nonempty_iff.mp h
  have h0 : ∑ ω : Ω, μ ω = 0 := by
    rw [univ_eq_empty, sum_empty]
  exact one_ne_zero (hμ1.symm.trans h0)

/-- Uncentred MGF of a finite law supported in `[a,a+c]`. -/
theorem interval_law_mgf_le {Ω : Type*} [Fintype Ω] (μ F : Ω → ℝ)
    {a c t : ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω : Ω, μ ω = 1)
    (hlo : ∀ ω, a ≤ F ω) (hhi : ∀ ω, F ω ≤ a + c) (hc : 0 ≤ c) :
    ∑ ω : Ω, μ ω * Real.exp (t * F ω) ≤
      Real.exp (t * finExpect μ F + t ^ 2 * c ^ 2 / 4) := by
  rcases eq_or_lt_of_le hc with hc0 | hc
  · subst hc0
    have hF : ∀ ω, F ω = a := fun ω => le_antisymm (by simpa using hhi ω) (hlo ω)
    have hE : finExpect μ F = a := by
      unfold finExpect
      have hpt : ∀ ω, μ ω * F ω = μ ω * a := fun ω => by rw [hF ω]
      rw [sum_congr rfl fun ω _ => hpt ω, ← sum_mul, hμ1, one_mul]
    have hpt : ∀ ω, μ ω * Real.exp (t * F ω) = μ ω * Real.exp (t * a) :=
      fun ω => by rw [hF ω]
    rw [sum_congr rfl fun ω _ => hpt ω, ← sum_mul, hμ1, one_mul]
    simp [hE]
  · have hsum_a : ∑ ω : Ω, μ ω * a = a := by
      rw [← sum_mul, hμ1, one_mul]
    have hE_lo : a ≤ finExpect μ F := by
      have hle : ∑ ω : Ω, μ ω * a ≤ ∑ ω : Ω, μ ω * F ω :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hlo ω) (hμ0 ω)
      unfold finExpect
      rwa [hsum_a] at hle
    have hsum_hi : ∑ ω : Ω, μ ω * (a + c) = a + c := by
      rw [← sum_mul, hμ1, one_mul]
    have hE_hi : finExpect μ F ≤ a + c := by
      have hle : ∑ ω : Ω, μ ω * F ω ≤ ∑ ω : Ω, μ ω * (a + c) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hhi ω) (hμ0 ω)
      unfold finExpect
      rwa [hsum_hi] at hle
    set q := (finExpect μ F - a) / c
    have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hE_lo) hc.le
    have hE_hi' : finExpect μ F ≤ c + a := by simpa [add_comm] using hE_hi
    have hq1 : q ≤ 1 := (div_le_one hc).mpr (sub_le_iff_le_add.mpr hE_hi')
    have hsec : ∀ ω,
        μ ω * Real.exp (t * F ω) ≤
          μ ω *
            (((a + c - F ω) / c) * Real.exp (t * a) +
              ((F ω - a) / c) * Real.exp (t * (a + c))) :=
      fun ω =>
        mul_le_mul_of_nonneg_left
          (exp_mul_endpoint_secant hc (hlo ω) (hhi ω)) (hμ0 ω)
    have hsum := sum_le_sum (s := (univ : Finset Ω)) fun ω _ => hsec ω
    have hdiv : ∀ ω, μ ω * ((F ω - a) / c) = (μ ω * (F ω - a)) / c :=
      fun ω => by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
    have hdiv' : ∀ ω, μ ω * ((a + c - F ω) / c) = (μ ω * (a + c - F ω)) / c :=
      fun ω => by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
    have hsumq :
        ∑ ω : Ω, μ ω * ((F ω - a) / c) = q := by
      simp_rw [hdiv, div_eq_mul_inv]
      rw [← sum_mul]
      have hlin : ∑ ω : Ω, μ ω * (F ω - a) = finExpect μ F - a := by
        simp [finExpect, mul_sub, sum_sub_distrib, hsum_a]
      rw [hlin]
      simp [q, div_eq_mul_inv]
    have hsum1q :
        ∑ ω : Ω, μ ω * ((a + c - F ω) / c) = 1 - q := by
      simp_rw [hdiv', div_eq_mul_inv]
      rw [← sum_mul]
      have hlin : ∑ ω : Ω, μ ω * (a + c - F ω) = a + c - finExpect μ F := by
        simp [finExpect, mul_sub, sum_sub_distrib, hsum_hi]
      rw [hlin]
      have hqc : q * c = finExpect μ F - a :=
        div_mul_cancel₀ (finExpect μ F - a) hc.ne'
      have hnum : a + c - finExpect μ F = (1 - q) * c := by
        linarith
      rw [hnum, mul_inv_cancel_right₀ hc.ne']
    have hsplit :
        ∑ ω : Ω,
            μ ω *
              (((a + c - F ω) / c) * Real.exp (t * a) +
                ((F ω - a) / c) * Real.exp (t * (a + c))) =
          (1 - q) * Real.exp (t * a) + q * Real.exp (t * (a + c)) := by
      have hpt : ∀ ω,
          μ ω *
              (((a + c - F ω) / c) * Real.exp (t * a) +
                ((F ω - a) / c) * Real.exp (t * (a + c))) =
            (μ ω * ((a + c - F ω) / c)) * Real.exp (t * a) +
              (μ ω * ((F ω - a) / c)) * Real.exp (t * (a + c)) :=
        fun ω => by ring
      rw [sum_congr (s₁ := (univ : Finset Ω)) (s₂ := univ) rfl fun ω _ => hpt ω,
        sum_add_distrib]
      have h1 :
          ∑ ω : Ω, (μ ω * ((a + c - F ω) / c)) * Real.exp (t * a) =
            (1 - q) * Real.exp (t * a) := by
        rw [← sum_mul, hsum1q]
      have h2 :
          ∑ ω : Ω, (μ ω * ((F ω - a) / c)) * Real.exp (t * (a + c)) =
            q * Real.exp (t * (a + c)) := by
        rw [← sum_mul, hsumq]
      rw [h1, h2]
    have htp :=
      two_point_mgf_le (q := q) (x0 := a) (x1 := a + c) (t := t) hq0 hq1
    have hm : (1 - q) * a + q * (a + c) = finExpect μ F := by
      have hqc : q * c = finExpect μ F - a :=
        div_mul_cancel₀ (finExpect μ F - a) hc.ne'
      linarith
    have hδ : a + c - a = c := by ring
    have htp' :
        (1 - q) * Real.exp (t * a) + q * Real.exp (t * (a + c)) ≤
          Real.exp (t * finExpect μ F + t ^ 2 * c ^ 2 / 4) := by
      simpa [hm, hδ] using htp
    exact hsum.trans ((le_of_eq hsplit).trans htp')

/-- Centred MGF of a finite law supported in an interval of length `c`. -/
theorem interval_law_centered_mgf_le {Ω : Type*} [Fintype Ω] (μ F : Ω → ℝ)
    {a c t : ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω : Ω, μ ω = 1)
    (hlo : ∀ ω, a ≤ F ω) (hhi : ∀ ω, F ω ≤ a + c) (hc : 0 ≤ c) :
    ∑ ω : Ω, μ ω * Real.exp (t * (F ω - finExpect μ F)) ≤
      Real.exp (t ^ 2 * c ^ 2 / 4) := by
  have hmgf := interval_law_mgf_le μ F hμ0 hμ1 hlo hhi hc (t := t)
  have hfact :
      ∑ ω : Ω, μ ω * Real.exp (t * (F ω - finExpect μ F)) =
        Real.exp (-t * finExpect μ F) *
          ∑ ω : Ω, μ ω * Real.exp (t * F ω) := by
    have hpt : ∀ ω,
        μ ω * Real.exp (t * (F ω - finExpect μ F)) =
          Real.exp (-t * finExpect μ F) * (μ ω * Real.exp (t * F ω)) :=
      fun ω => by
        have : t * (F ω - finExpect μ F) = t * F ω + (-t * finExpect μ F) :=
          by ring
        rw [this, Real.exp_add]
        ring
    rw [sum_congr rfl fun ω _ => hpt ω, ← mul_sum]
  have hmul :=
    mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg (-t * finExpect μ F))
  have hrew :
      Real.exp (-t * finExpect μ F) *
          Real.exp (t * finExpect μ F + t ^ 2 * c ^ 2 / 4) =
        Real.exp (t ^ 2 * c ^ 2 / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfact]
  exact hmul.trans (le_of_eq hrew)

/-- One-sided tail of an interval law. Same shape as
`bernoulli_bounded_diff_one_sided`, width `c` in place of `Σ c_i`. -/
theorem interval_law_one_sided {Ω : Type*} [Fintype Ω] (μ F : Ω → ℝ)
    {a c u : ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω : Ω, μ ω = 1)
    (hlo : ∀ ω, a ≤ F ω) (hhi : ∀ ω, F ω ≤ a + c) (hc : 0 ≤ c)
    (hu : 0 < u) :
    ∑ ω ∈ univ.filter (fun ω => u ≤ F ω - finExpect μ F), μ ω
      ≤ if c = 0 then 0 else Real.exp (-u ^ 2 / c ^ 2) := by
  by_cases hc0 : c = 0
  · subst hc0
    have hF : ∀ ω, F ω = a := fun ω => le_antisymm (by simpa using hhi ω) (hlo ω)
    have hE : finExpect μ F = a := by
      unfold finExpect
      have hpt : ∀ ω, μ ω * F ω = μ ω * a := fun ω => by rw [hF ω]
      rw [sum_congr rfl fun ω _ => hpt ω, ← sum_mul, hμ1, one_mul]
    have hempty :
        univ.filter (fun ω : Ω => u ≤ F ω - finExpect μ F) = ∅ := by
      apply eq_empty_of_forall_notMem
      intro ω hω
      have : u ≤ 0 := by
        simpa [hF ω, hE] using (mem_filter.mp hω).2
      exact (not_le_of_gt hu) this
    simp [hempty]
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hσ : 0 < c ^ 2 := sq_pos_of_pos hcpos
    set t := (2 : ℝ) * u / c ^ 2
    have ht : 0 ≤ t :=
      div_nonneg (mul_nonneg (by norm_num) hu.le) hσ.le
    have hmarkov :=
      exp_markov_finset (univ : Finset Ω) μ
        (fun ω => F ω - finExpect μ F) (u := u) ht fun ω _ => hμ0 ω
    have hmgf := interval_law_centered_mgf_le μ F hμ0 hμ1 hlo hhi hc (t := t)
    have hexp :
        Real.exp (-t * u) * Real.exp (t ^ 2 * c ^ 2 / 4) =
          Real.exp (-u ^ 2 / c ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      have hc20 : c ^ 2 ≠ 0 := hσ.ne'
      simp only [t]
      field_simp [hc20]
      ring
    have hstep :=
      (mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg (-t * u))).trans
        (le_of_eq hexp)
    simpa [hc0] using hmarkov.trans hstep

/-! ### Lipschitz slice sits in an interval of length `c` -/

/-- A function of diameter `c` on a nonempty finite type takes values in
some interval `[m, m+c]`. -/
theorem interval_slice_of_lipschitz {α : Type*} [Fintype α] [Nonempty α]
    (F : α → ℝ) {c : ℝ} (_hc : 0 ≤ c)
    (hLip : ∀ a b : α, |F a - F b| ≤ c) :
    ∃ m, ∀ a, m ≤ F a ∧ F a ≤ m + c := by
  obtain ⟨a0, _, ha0⟩ := exists_min_image (univ : Finset α) F univ_nonempty
  refine ⟨F a0, fun a => ⟨ha0 a (mem_univ a), ?_⟩⟩
  have hle : F a - F a0 ≤ |F a - F a0| := le_abs_self _
  have habs : |F a - F a0| ≤ c := hLip a a0
  linarith

/-! ### One-coordinate step on an independent product slice -/

/-- Conditional mean of the distinguished coordinate. -/
noncomputable def condExpect {Ω α : Type*} [Fintype α]
    (μα : α → ℝ) (F : Ω → α → ℝ) (ω : Ω) : ℝ :=
  ∑ a : α, μα a * F ω a

theorem pairExpect_eq_cond {Ω α : Type*} [Fintype Ω] [Fintype α]
    (μΩ : Ω → ℝ) (μα : α → ℝ) (F : Ω → α → ℝ) :
    ∑ ω : Ω, ∑ a : α, μΩ ω * μα a * F ω a =
      finExpect μΩ (condExpect μα F) := by
  unfold finExpect condExpect
  refine sum_congr rfl fun ω _ => ?_
  simp [mul_assoc, ← mul_sum]

/-- Averaging one independent coordinate of width `c` costs
`exp(t² c² / 4)` in the MGF. -/
theorem one_coord_mgf_step {Ω α : Type*} [Fintype Ω] [Fintype α]
    [Nonempty α] (μΩ : Ω → ℝ) (μα : α → ℝ) (F : Ω → α → ℝ) {c t : ℝ}
    (hΩ0 : ∀ ω, 0 ≤ μΩ ω) (hΩ1 : ∑ ω : Ω, μΩ ω = 1)
    (hα0 : ∀ a, 0 ≤ μα a) (hα1 : ∑ a : α, μα a = 1)
    (hc : 0 ≤ c)
    (hLip : ∀ ω a b, |F ω a - F ω b| ≤ c) :
    ∑ ω : Ω, ∑ a : α, μΩ ω * μα a * Real.exp (t * F ω a) ≤
      Real.exp (t ^ 2 * c ^ 2 / 4) *
        ∑ ω : Ω, μΩ ω * Real.exp (t * condExpect μα F ω) := by
  have hpt : ∀ ω,
      ∑ a : α, μΩ ω * μα a * Real.exp (t * F ω a) ≤
        μΩ ω * Real.exp (t * condExpect μα F ω + t ^ 2 * c ^ 2 / 4) := by
    intro ω
    have hfactor :
        ∑ a : α, μΩ ω * μα a * Real.exp (t * F ω a) =
          μΩ ω * ∑ a : α, μα a * Real.exp (t * F ω a) := by
      simp [mul_assoc, ← mul_sum]
    rw [hfactor]
    obtain ⟨m, hm⟩ :=
      interval_slice_of_lipschitz (fun a => F ω a) hc (fun a b => hLip ω a b)
    have hlo : ∀ a, m ≤ F ω a := fun a => (hm a).1
    have hhi : ∀ a, F ω a ≤ m + c := fun a => (hm a).2
    have hmgf :=
      interval_law_mgf_le μα (fun a => F ω a) hα0 hα1 hlo hhi hc (t := t)
    have hE : finExpect μα (fun a => F ω a) = condExpect μα F ω := rfl
    have hmgf' :
        ∑ a : α, μα a * Real.exp (t * F ω a) ≤
          Real.exp (t * condExpect μα F ω + t ^ 2 * c ^ 2 / 4) := by
      simpa [hE] using hmgf
    exact mul_le_mul_of_nonneg_left hmgf' (hΩ0 ω)
  have hsum := sum_le_sum (s := (univ : Finset Ω)) fun ω _ => hpt ω
  have hrew :
      ∑ ω : Ω, μΩ ω * Real.exp (t * condExpect μα F ω + t ^ 2 * c ^ 2 / 4) =
        Real.exp (t ^ 2 * c ^ 2 / 4) *
          ∑ ω : Ω, μΩ ω * Real.exp (t * condExpect μα F ω) := by
    have hpt' : ∀ ω,
        μΩ ω * Real.exp (t * condExpect μα F ω + t ^ 2 * c ^ 2 / 4) =
          Real.exp (t ^ 2 * c ^ 2 / 4) *
            (μΩ ω * Real.exp (t * condExpect μα F ω)) :=
      fun ω => by
        rw [Real.exp_add]
        ring
    rw [sum_congr rfl fun ω _ => hpt' ω, ← mul_sum]
  exact hsum.trans (le_of_eq hrew)

/-- Centred one-coordinate step: the reduced observable is the
conditional mean. -/
theorem one_coord_centered_mgf_step {Ω α : Type*} [Fintype Ω] [Fintype α]
    [Nonempty α] (μΩ : Ω → ℝ) (μα : α → ℝ) (F : Ω → α → ℝ) {c t : ℝ}
    (hΩ0 : ∀ ω, 0 ≤ μΩ ω) (hΩ1 : ∑ ω : Ω, μΩ ω = 1)
    (hα0 : ∀ a, 0 ≤ μα a) (hα1 : ∑ a : α, μα a = 1)
    (hc : 0 ≤ c)
    (hLip : ∀ ω a b, |F ω a - F ω b| ≤ c) :
    ∑ ω : Ω, ∑ a : α, μΩ ω * μα a *
        Real.exp (t * (F ω a - finExpect μΩ (condExpect μα F))) ≤
      Real.exp (t ^ 2 * c ^ 2 / 4) *
        ∑ ω : Ω, μΩ ω *
          Real.exp (t * (condExpect μα F ω -
            finExpect μΩ (condExpect μα F))) := by
  set E := finExpect μΩ (condExpect μα F)
  have hmgf := one_coord_mgf_step μΩ μα F hΩ0 hΩ1 hα0 hα1 hc hLip (t := t)
  have hfact :
      ∑ ω : Ω, ∑ a : α, μΩ ω * μα a * Real.exp (t * (F ω a - E)) =
        Real.exp (-t * E) *
          ∑ ω : Ω, ∑ a : α, μΩ ω * μα a * Real.exp (t * F ω a) := by
    have hω : ∀ ω,
        ∑ a : α, μΩ ω * μα a * Real.exp (t * (F ω a - E)) =
          Real.exp (-t * E) *
            ∑ a : α, μΩ ω * μα a * Real.exp (t * F ω a) := by
      intro ω
      have hpt : ∀ a,
          μΩ ω * μα a * Real.exp (t * (F ω a - E)) =
            Real.exp (-t * E) *
              (μΩ ω * μα a * Real.exp (t * F ω a)) :=
        fun a => by
          have : t * (F ω a - E) = t * F ω a + (-t * E) := by ring
          rw [this, Real.exp_add]
          ring
      rw [sum_congr rfl fun a _ => hpt a, ← mul_sum]
    rw [sum_congr rfl fun ω _ => hω ω, ← mul_sum]
  have hmul :=
    mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg (-t * E))
  have hrew :
      Real.exp (-t * E) *
          (Real.exp (t ^ 2 * c ^ 2 / 4) *
            ∑ ω : Ω, μΩ ω * Real.exp (t * condExpect μα F ω)) =
        Real.exp (t ^ 2 * c ^ 2 / 4) *
          ∑ ω : Ω, μΩ ω * Real.exp (t * (condExpect μα F ω - E)) := by
    have hpt : ∀ ω,
        μΩ ω * Real.exp (t * (condExpect μα F ω - E)) =
          Real.exp (-t * E) * (μΩ ω * Real.exp (t * condExpect μα F ω)) :=
      fun ω => by
        have : t * (condExpect μα F ω - E) =
            t * condExpect μα F ω + (-t * E) := by ring
        rw [this, Real.exp_add]
        ring
    have hsum :
        ∑ ω : Ω, μΩ ω * Real.exp (t * (condExpect μα F ω - E)) =
          Real.exp (-t * E) *
            ∑ ω : Ω, μΩ ω * Real.exp (t * condExpect μα F ω) := by
      rw [sum_congr rfl fun ω _ => hpt ω, ← mul_sum]
    calc
      Real.exp (-t * E) *
          (Real.exp (t ^ 2 * c ^ 2 / 4) *
            ∑ ω : Ω, μΩ ω * Real.exp (t * condExpect μα F ω))
          = Real.exp (t ^ 2 * c ^ 2 / 4) *
              (Real.exp (-t * E) *
                ∑ ω : Ω, μΩ ω * Real.exp (t * condExpect μα F ω)) := by
            ring
      _ = Real.exp (t ^ 2 * c ^ 2 / 4) *
            ∑ ω : Ω, μΩ ω * Real.exp (t * (condExpect μα F ω - E)) := by
          rw [← hsum]
  rw [hfact]
  exact hmul.trans (le_of_eq hrew)

/-! ### Dependent finite product `Π_{i : Fin n} α i` -/

/-- Product mass on a dependent `Fin n` coordinate space. -/
noncomputable def piMass {n : ℕ} {α : Fin n → Type} [∀ i, Fintype (α i)]
    (μ : ∀ i, α i → ℝ) (x : ∀ i, α i) : ℝ :=
  ∏ i, μ i (x i)

noncomputable def piExpect {n : ℕ} {α : Fin n → Type} [∀ i, Fintype (α i)]
    (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) : ℝ :=
  ∑ x : (∀ i, α i), piMass μ x * F x

theorem piMass_snoc {n : ℕ} {α : Fin (n + 1) → Type} [∀ i, Fintype (α i)]
    (μ : ∀ i, α i → ℝ) (y : ∀ i : Fin n, α i.castSucc)
    (a : α (Fin.last n)) :
    piMass μ (Fin.snoc y a) =
      piMass (fun i b => μ i.castSucc b) y * μ (Fin.last n) a := by
  unfold piMass
  rw [Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem sum_pi_snoc {n : ℕ} {α : Fin (n + 1) → Type} [∀ i, Fintype (α i)]
    (f : (∀ i, α i) → ℝ) :
    ∑ x : (∀ i, α i), f x =
      ∑ y : (∀ i : Fin n, α i.castSucc),
        ∑ a : α (Fin.last n), f (Fin.snoc y a) := by
  have hcomp := Equiv.sum_comp (Fin.snocEquiv α) f
  have hfun :
      ∑ p : α (Fin.last n) × (∀ i : Fin n, α i.castSucc),
          f (Fin.snocEquiv α p) =
        ∑ p : α (Fin.last n) × (∀ i : Fin n, α i.castSucc),
          f (Fin.snoc p.2 p.1) :=
    rfl
  have hprod :=
    Fintype.sum_prod_type_right
      (fun p : α (Fin.last n) × (∀ i : Fin n, α i.castSucc) =>
        f (Fin.snoc p.2 p.1))
  calc
    ∑ x : (∀ i, α i), f x
        = ∑ p : α (Fin.last n) × (∀ i : Fin n, α i.castSucc),
            f (Fin.snocEquiv α p) := hcomp.symm
    _ = ∑ p : α (Fin.last n) × (∀ i : Fin n, α i.castSucc),
          f (Fin.snoc p.2 p.1) := hfun
    _ = ∑ y : (∀ i : Fin n, α i.castSucc),
          ∑ a : α (Fin.last n), f (Fin.snoc y a) := hprod

noncomputable def snocCondExpect {n : ℕ} {α : Fin (n + 1) → Type}
    [∀ i, Fintype (α i)] (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ)
    (y : ∀ i : Fin n, α i.castSucc) : ℝ :=
  ∑ a : α (Fin.last n), μ (Fin.last n) a * F (Fin.snoc y a)

theorem piExpect_snoc {n : ℕ} {α : Fin (n + 1) → Type} [∀ i, Fintype (α i)]
    (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) :
    piExpect μ F =
      piExpect (fun i b => μ i.castSucc b) (snocCondExpect μ F) := by
  unfold piExpect
  rw [sum_pi_snoc]
  refine sum_congr rfl fun y _ => ?_
  have hmass :
      ∀ a, piMass μ (Fin.snoc y a) =
        piMass (fun i b => μ i.castSucc b) y * μ (Fin.last n) a :=
    fun a => piMass_snoc μ y a
  have hpt :
      ∑ a : α (Fin.last n), piMass μ (Fin.snoc y a) * F (Fin.snoc y a) =
        piMass (fun i b => μ i.castSucc b) y *
          snocCondExpect μ F y := by
    have hpt' : ∀ a,
        piMass μ (Fin.snoc y a) * F (Fin.snoc y a) =
          piMass (fun i b => μ i.castSucc b) y *
            (μ (Fin.last n) a * F (Fin.snoc y a)) :=
      fun a => by
        rw [hmass a]
        ring
    rw [sum_congr rfl fun a _ => hpt' a]
    unfold snocCondExpect
    simp [mul_assoc, ← mul_sum]
  exact hpt

theorem piMass_sum :
    ∀ (n : ℕ) (α : Fin n → Type) [∀ i, Fintype (α i)] (μ : ∀ i, α i → ℝ),
      (∀ i, ∑ a : α i, μ i a = 1) →
      ∑ x : (∀ i, α i), piMass μ x = 1 := by
  intro n
  induction n with
  | zero =>
    intro α _ μ hμ1
    have : Unique (∀ i : Fin 0, α i) := Pi.uniqueOfIsEmpty _
    rw [Fintype.sum_unique]
    simp [piMass]
  | succ n ih =>
    intro α _ μ hμ1
    rw [sum_pi_snoc]
    have hinner :
        ∀ y : (∀ i : Fin n, α i.castSucc),
          ∑ a : α (Fin.last n), piMass μ (Fin.snoc y a) =
            piMass (fun i b => μ i.castSucc b) y := by
      intro y
      have hpt : ∀ a,
          piMass μ (Fin.snoc y a) =
            piMass (fun i b => μ i.castSucc b) y * μ (Fin.last n) a :=
        fun a => piMass_snoc μ y a
      rw [sum_congr rfl fun a _ => hpt a, ← mul_sum, hμ1 (Fin.last n),
        mul_one]
    rw [sum_congr rfl fun y _ => hinner y]
    convert ih (fun i => α i.castSucc) (fun i b => μ i.castSucc b)
      (fun i => hμ1 i.castSucc)

private theorem abs_telescope (f : ℕ → ℝ) (n : ℕ) :
    |f n - f 0| ≤ ∑ k ∈ range n, |f (k + 1) - f k| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htri : |f (n + 1) - f 0| ≤ |f (n + 1) - f n| + |f n - f 0| :=
      abs_sub_le _ _ _
    calc
      |f (n + 1) - f 0|
          ≤ |f (n + 1) - f n| + |f n - f 0| := htri
      _ ≤ |f (n + 1) - f n| + ∑ k ∈ range n, |f (k + 1) - f k| :=
        _root_.add_le_add_right ih |f (n + 1) - f n|
      _ = ∑ k ∈ range (n + 1), |f (k + 1) - f k| := by
        rw [sum_range_succ, add_comm]

/-- Walk from `x` to `y` by replacing the first `k` dependent coordinates. -/
def piCoordMix {n : ℕ} {α : Fin n → Type} (x y : ∀ i, α i) (k : ℕ) :
    ∀ i, α i :=
  fun i => if i.val < k then y i else x i

theorem piCoordMix_zero {n : ℕ} {α : Fin n → Type} (x y : ∀ i, α i) :
    piCoordMix x y 0 = x := by
  funext i
  simp [piCoordMix]

theorem piCoordMix_length {n : ℕ} {α : Fin n → Type} (x y : ∀ i, α i) :
    piCoordMix x y n = y := by
  funext i
  simp [piCoordMix, i.isLt]

theorem piCoordMix_succ {n : ℕ} {α : Fin n → Type} (x y : ∀ i, α i)
    {k : ℕ} (hk : k < n) :
    piCoordMix x y (k + 1) =
      Function.update (piCoordMix x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
  funext i
  by_cases hieq : i.val = k
  · have hi : i = ⟨k, hk⟩ := Fin.ext hieq
    rw [hi, Function.update_self, piCoordMix]
    simp [Nat.lt_succ_self k]
  · have hne : i ≠ ⟨k, hk⟩ := fun h => hieq (congrArg Fin.val h)
    rw [Function.update_of_ne hne, piCoordMix, piCoordMix]
    by_cases hlt : i.val < k
    · have hlt' : i.val < k + 1 := Nat.lt_succ_of_lt hlt
      simp [hlt, hlt']
    · have hlt' : ¬ i.val < k + 1 := by omega
      simp [hlt, hlt']

/-- Changing one coordinate costs `c i`, hence the displacement is at
most `∑ c_i`. -/
theorem piFin_coord_diameter {n : ℕ} {α : Fin n → Type}
    [∀ i, Fintype (α i)] (F : (∀ i, α i) → ℝ) (c : Fin n → ℝ)
    (hLip : ∀ (x : ∀ i, α i) (i : Fin n) (a b : α i),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i)
    (x y : ∀ i, α i) :
    |F y - F x| ≤ ∑ i : Fin n, c i := by
  have hstep : ∀ k : ℕ, (hk : k < n) →
      |F (piCoordMix x y (k + 1)) - F (piCoordMix x y k)| ≤
        c ⟨k, hk⟩ :=
    fun k hk => by
      have hmix := piCoordMix_succ (α := α) x y hk
      rw [hmix]
      have hxk : piCoordMix x y k ⟨k, hk⟩ = x ⟨k, hk⟩ := by
        simp [piCoordMix]
      have hx : F (piCoordMix x y k) =
          F (Function.update (piCoordMix x y k) ⟨k, hk⟩ (x ⟨k, hk⟩)) := by
        rw [← hxk, Function.update_eq_self]
      rw [hx]
      exact hLip (piCoordMix x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) (x ⟨k, hk⟩)
  have hchain :
      |F (piCoordMix x y n) - F (piCoordMix x y 0)| ≤
        ∑ k ∈ range n, |F (piCoordMix x y (k + 1)) - F (piCoordMix x y k)| :=
    abs_telescope (fun k => F (piCoordMix x y k)) n
  rw [piCoordMix_length, piCoordMix_zero] at hchain
  refine hchain.trans ?_
  rw [sum_fin_eq_sum_range]
  refine sum_le_sum fun k hk => ?_
  have hk' : k < n := mem_range.mp hk
  have hite : (if h : k < n then c ⟨k, h⟩ else 0) = c ⟨k, hk'⟩ := dif_pos hk'
  rw [hite]
  exact hstep k hk'

/-- Product bounded-differences MGF on `Π_{i : Fin n} α i`. -/
theorem piFin_bounded_diff_mgf :
    ∀ (n : ℕ) (α : Fin n → Type) [∀ i, Fintype (α i)]
      (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) (c : Fin n → ℝ) (t : ℝ),
      (∀ i a, 0 ≤ μ i a) →
      (∀ i, ∑ a : α i, μ i a = 1) →
      (∀ i, 0 ≤ c i) →
      (∀ (x : ∀ i, α i) (i : Fin n) (a b : α i),
        |F (Function.update x i a) - F (Function.update x i b)| ≤ c i) →
      ∑ x : (∀ i, α i),
          piMass μ x * Real.exp (t * (F x - piExpect μ F))
        ≤ Real.exp (t ^ 2 * (∑ i : Fin n, c i ^ 2) / 4) := by
  intro n
  induction n with
  | zero =>
    intro α _ μ F c t _hμ0 _hμ1 _hc _hLip
    have : Unique (∀ i : Fin 0, α i) := Pi.uniqueOfIsEmpty _
    have hmass : piMass μ default = 1 := by simp [piMass]
    have hE : piExpect μ F = F default := by
      unfold piExpect
      rw [Fintype.sum_unique, hmass, one_mul]
    rw [Fintype.sum_unique]
    simp [hmass, hE, sub_self, Real.exp_zero]
  | succ n ih =>
    intro α _ μ F c t hμ0 hμ1 hc hLip
    have : Nonempty (α (Fin.last n)) :=
      nonempty_of_mass_one (hμ1 (Fin.last n))
    set μ' : ∀ i : Fin n, α i.castSucc → ℝ := fun i b => μ i.castSucc b
    set c' : Fin n → ℝ := fun i => c i.castSucc
    set G : (∀ i : Fin n, α i.castSucc) → ℝ := snocCondExpect μ F
    have hμ'0 : ∀ (i : Fin n) (a : α i.castSucc), 0 ≤ μ' i a :=
      fun i a => hμ0 i.castSucc a
    have hμ'1 : ∀ i : Fin n, ∑ a : α i.castSucc, μ' i a = 1 :=
      fun i => by
        dsimp [μ']
        convert hμ1 i.castSucc
    have hc' : ∀ i, 0 ≤ c' i := fun i => hc i.castSucc
    have hLipG :
        ∀ (y : ∀ i : Fin n, α i.castSucc) (i : Fin n)
          (a b : α i.castSucc),
          |G (Function.update y i a) - G (Function.update y i b)| ≤
            c' i := by
      intro y i a b
      have hpt : ∀ z : α (Fin.last n),
          |F (Fin.snoc (Function.update y i a) z) -
            F (Fin.snoc (Function.update y i b) z)| ≤
            c i.castSucc := by
        intro z
        have h1 :
            Fin.snoc (Function.update y i a) z =
              Function.update (Fin.snoc y z) i.castSucc a := by
          rw [Fin.snoc_update]
        have h2 :
            Fin.snoc (Function.update y i b) z =
              Function.update (Fin.snoc y z) i.castSucc b := by
          rw [Fin.snoc_update]
        rw [h1, h2]
        exact hLip (Fin.snoc y z) i.castSucc a b
      have hsub :
          G (Function.update y i a) - G (Function.update y i b) =
            ∑ z : α (Fin.last n),
              μ (Fin.last n) z *
                (F (Fin.snoc (Function.update y i a) z) -
                  F (Fin.snoc (Function.update y i b) z)) := by
        simp [G, snocCondExpect, mul_sub, sum_sub_distrib]
      have habs :
          |G (Function.update y i a) - G (Function.update y i b)| ≤
            ∑ z : α (Fin.last n),
              μ (Fin.last n) z *
                |F (Fin.snoc (Function.update y i a) z) -
                  F (Fin.snoc (Function.update y i b) z)| := by
        rw [hsub]
        refine (abs_sum_le_sum_abs
            (fun z =>
              μ (Fin.last n) z *
                (F (Fin.snoc (Function.update y i a) z) -
                  F (Fin.snoc (Function.update y i b) z)))
            univ).trans ?_
        refine le_of_eq (sum_congr rfl fun z _ => ?_)
        rw [abs_mul, abs_of_nonneg (hμ0 (Fin.last n) z)]
      have hbound :
          ∑ z : α (Fin.last n),
              μ (Fin.last n) z *
                |F (Fin.snoc (Function.update y i a) z) -
                  F (Fin.snoc (Function.update y i b) z)| ≤
            ∑ z : α (Fin.last n), μ (Fin.last n) z * c i.castSucc :=
        sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (hpt z) (hμ0 (Fin.last n) z)
      have hsumc :
          ∑ z : α (Fin.last n), μ (Fin.last n) z * c i.castSucc =
            c i.castSucc := by
        rw [← sum_mul, hμ1 (Fin.last n), one_mul]
      exact habs.trans (hbound.trans (le_of_eq hsumc))
    have ihG :=
      ih (fun i => α i.castSucc) μ' G c' t hμ'0 hμ'1 hc' hLipG
    have hμΩ1 :
        ∑ y : (∀ i : Fin n, α i.castSucc), piMass μ' y = 1 :=
      piMass_sum n (fun i => α i.castSucc) μ' hμ'1
    have hμΩ0 : ∀ y : (∀ i : Fin n, α i.castSucc), 0 ≤ piMass μ' y :=
      fun y => prod_nonneg fun i _ => hμ'0 i (y i)
    have hLipLast :
        ∀ (y : ∀ i : Fin n, α i.castSucc) (a b : α (Fin.last n)),
          |F (Fin.snoc y a) - F (Fin.snoc y b)| ≤ c (Fin.last n) := by
      intro y a b
      have hyb : Fin.snoc y b =
          Function.update (Fin.snoc y a) (Fin.last n) b :=
        (Fin.update_snoc_last (p := y) (x := a) (z := b)).symm
      have hya : Fin.snoc y a =
          Function.update (Fin.snoc y a) (Fin.last n) a := by
        have hupd :=
          Function.update_eq_self (Fin.last n) (Fin.snoc y a)
        rw [Fin.snoc_last] at hupd
        exact hupd.symm
      have hgoal := hLip (Fin.snoc y a) (Fin.last n) a b
      rw [← hya, ← hyb] at hgoal
      exact hgoal
    have hE : piExpect μ F = piExpect μ' G := by
      dsimp [μ', G]
      exact piExpect_snoc (α := α) μ F
    have hsplit :
        ∑ x : (∀ i, α i),
            piMass μ x * Real.exp (t * (F x - piExpect μ F)) =
          ∑ y : (∀ i : Fin n, α i.castSucc), ∑ a : α (Fin.last n),
            piMass μ' y * μ (Fin.last n) a *
              Real.exp (t * (F (Fin.snoc y a) - piExpect μ F)) := by
      rw [sum_pi_snoc]
      refine sum_congr rfl fun y _ => ?_
      refine sum_congr rfl fun a _ => ?_
      simp [piMass_snoc, μ']
    have hstep :=
      one_coord_centered_mgf_step
        (Ω := ∀ i : Fin n, α i.castSucc)
        (α := α (Fin.last n)) (μΩ := piMass μ') (μα := μ (Fin.last n))
        (F := fun y a => F (Fin.snoc y a)) (c := c (Fin.last n)) (t := t)
        hμΩ0 hμΩ1 (hμ0 (Fin.last n)) (hμ1 (Fin.last n)) (hc (Fin.last n))
        hLipLast
    have hGcond : condExpect (μ (Fin.last n)) (fun y a => F (Fin.snoc y a))
        = G := by
      funext y
      simp [condExpect, G, snocCondExpect]
    have hEcond : finExpect (piMass μ') G = piExpect μ' G := rfl
    have hstep' :
        ∑ y : (∀ i : Fin n, α i.castSucc), ∑ a : α (Fin.last n),
            piMass μ' y * μ (Fin.last n) a *
              Real.exp (t * (F (Fin.snoc y a) - piExpect μ F)) ≤
          Real.exp (t ^ 2 * c (Fin.last n) ^ 2 / 4) *
            ∑ y : (∀ i : Fin n, α i.castSucc),
              piMass μ' y * Real.exp (t * (G y - piExpect μ' G)) := by
      rw [hE]
      rw [hGcond] at hstep
      rw [hEcond] at hstep
      exact hstep
    have hσ :
        t ^ 2 * c (Fin.last n) ^ 2 / 4 +
            t ^ 2 * (∑ i : Fin n, c' i ^ 2) / 4 =
          t ^ 2 * (∑ i : Fin (n + 1), c i ^ 2) / 4 := by
      rw [Fin.sum_univ_castSucc]
      simp [c']
      ring
    calc
      ∑ x : (∀ i, α i),
          piMass μ x * Real.exp (t * (F x - piExpect μ F))
          = ∑ y : (∀ i : Fin n, α i.castSucc), ∑ a : α (Fin.last n),
              piMass μ' y * μ (Fin.last n) a *
                Real.exp (t * (F (Fin.snoc y a) - piExpect μ F)) :=
            hsplit
      _ ≤ Real.exp (t ^ 2 * c (Fin.last n) ^ 2 / 4) *
            ∑ y : (∀ i : Fin n, α i.castSucc),
              piMass μ' y * Real.exp (t * (G y - piExpect μ' G)) :=
            hstep'
      _ ≤ Real.exp (t ^ 2 * c (Fin.last n) ^ 2 / 4) *
            Real.exp (t ^ 2 * (∑ i : Fin n, c' i ^ 2) / 4) :=
            mul_le_mul_of_nonneg_left ihG (Real.exp_nonneg _)
      _ = Real.exp (t ^ 2 * (∑ i : Fin (n + 1), c i ^ 2) / 4) := by
          rw [← Real.exp_add, hσ]

/-- One-sided product tail `exp(-u² / Σ c_i²)`. -/
theorem piFin_bounded_diff_one_sided {n : ℕ} {α : Fin n → Type}
    [∀ i, Fintype (α i)] (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ)
    (c : Fin n → ℝ) {u : ℝ}
    (hμ0 : ∀ i a, 0 ≤ μ i a) (hμ1 : ∀ i, ∑ a : α i, μ i a = 1)
    (hc : ∀ i, 0 ≤ c i)
    (hLip : ∀ (x : ∀ i, α i) (i : Fin n) (a b : α i),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i)
    (hu : 0 < u) :
    ∑ x ∈ univ.filter
        (fun x : (∀ i, α i) => u ≤ F x - piExpect μ F),
      piMass μ x
      ≤ if ∑ i : Fin n, c i ^ 2 = 0 then 0
        else Real.exp (-u ^ 2 / ∑ i : Fin n, c i ^ 2) := by
  have hmass0 : ∀ x, 0 ≤ piMass μ x := fun x =>
    prod_nonneg fun i _ => hμ0 i (x i)
  by_cases hσ : ∑ i : Fin n, c i ^ 2 = 0
  · have hc0 : ∀ i, c i = 0 := by
      intro i
      have hsum :=
        (sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hσ i
          (mem_univ i)
      exact sq_eq_zero_iff.mp hsum
    have hconst : ∀ x y, F x = F y := fun x y => by
      have hdiam := piFin_coord_diameter F c hLip x y
      have hsum0 : ∑ i : Fin n, c i = 0 := by
        simp [hc0]
      have : |F y - F x| ≤ 0 := by
        simpa [hsum0] using hdiam
      have hyx : F y = F x :=
        sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))
      exact hyx.symm
    have hE : ∀ x, piExpect μ F = F x := by
      intro x
      unfold piExpect
      have hpt : ∀ y, piMass μ y * F y = piMass μ y * F x := fun y => by
        rw [hconst y x]
      rw [sum_congr rfl fun y _ => hpt y, ← sum_mul, piMass_sum n α μ hμ1,
        one_mul]
    have hempty :
        univ.filter (fun x : (∀ i, α i) => u ≤ F x - piExpect μ F) = ∅ := by
      apply eq_empty_of_forall_notMem
      intro x hx
      have : u ≤ 0 := by
        simpa [hE x] using (mem_filter.mp hx).2
      exact (not_le_of_gt hu) this
    simp [hσ, hempty]
  · have hσnn : 0 ≤ ∑ i : Fin n, c i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have hσpos : 0 < ∑ i : Fin n, c i ^ 2 := hσnn.lt_of_ne (Ne.symm hσ)
    set σ := ∑ i : Fin n, c i ^ 2
    set t := (2 : ℝ) * u / σ
    have ht : 0 ≤ t :=
      div_nonneg (mul_nonneg (by norm_num) hu.le) hσpos.le
    have hmarkov :=
      exp_markov_finset (univ : Finset (∀ i, α i)) (piMass μ)
        (fun x => F x - piExpect μ F) (u := u) ht fun x _ => hmass0 x
    have hmgf := piFin_bounded_diff_mgf n α μ F c t hμ0 hμ1 hc hLip
    have hexp :
        Real.exp (-t * u) * Real.exp (t ^ 2 * σ / 4) =
          Real.exp (-u ^ 2 / σ) := by
      rw [← Real.exp_add]
      congr 1
      have hσ0 : σ ≠ 0 := ne_of_gt hσpos
      simp only [t]
      field_simp [hσ0]
      ring
    have hstep :=
      (mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg (-t * u))).trans
        (le_of_eq hexp)
    have : ∑ x ∈ univ.filter
          (fun x : (∀ i, α i) => u ≤ F x - piExpect μ F),
        piMass μ x
        ≤ Real.exp (-u ^ 2 / σ) := hmarkov.trans hstep
    simpa [hσ, σ] using this

/-! ### Residue widths `2(h/p+1)` on `Fin (p-1)` coordinates -/

/-- Two updates of the same residue coordinate: the public one-sided
Lipschitz of `residueAvoidCount` implies diameter `residueWidth`. -/
theorem residueAvoidCount_two_update_le {n : ℕ} (moduli : Fin n → ℕ)
    (a h : ℕ) (σ : Fin n → ℕ) (i : Fin n) (b₁ b₂ : ℕ)
    (hp : 0 < moduli i) :
    |((residueAvoidCount moduli (Ico a (a + h))
          (Function.update σ i b₁) : ℝ) -
        (residueAvoidCount moduli (Ico a (a + h))
          (Function.update σ i b₂) : ℝ))| ≤
      residueWidth h (moduli i) := by
  have hτ :
      Function.update (Function.update σ i b₂) i b₁ =
        Function.update σ i b₁ := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp [Function.update_self]
    · simp [Function.update_of_ne hji]
  have hle :=
    residueAvoidCount_lipschitz moduli a h (Function.update σ i b₂) i b₁ hp
  simpa [hτ] using hle

/-- Decode a categorical residue `Fin (p-1)` to a forbidden class in
`{1,…,p-1}`. -/
def decodeResidue {n : ℕ} (moduli : Fin n → ℕ)
    (σ : ∀ i, Fin (moduli i - 1)) : Fin n → ℕ :=
  fun i => (σ i).val + 1

theorem decodeResidue_update {n : ℕ} (moduli : Fin n → ℕ)
    (σ : ∀ i, Fin (moduli i - 1)) (i : Fin n) (b : Fin (moduli i - 1)) :
    decodeResidue moduli (Function.update σ i b) =
      Function.update (decodeResidue moduli σ) i (b.val + 1) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [decodeResidue, Function.update_self]
  · simp [decodeResidue, Function.update_of_ne hji]

/-- Survivor count as a function of categorical residues `Fin (p_i-1)`. -/
noncomputable def residuePiAvoidCount {n : ℕ} (moduli : Fin n → ℕ)
    (a h : ℕ) (σ : ∀ i, Fin (moduli i - 1)) : ℝ :=
  residueAvoidCount moduli (Ico a (a + h)) (decodeResidue moduli σ)

theorem residuePiAvoidCount_lipschitz {n : ℕ} (moduli : Fin n → ℕ)
    (a h : ℕ) (σ : ∀ i, Fin (moduli i - 1)) (i : Fin n)
    (b₁ b₂ : Fin (moduli i - 1)) (hp : 0 < moduli i) :
    |residuePiAvoidCount moduli a h (Function.update σ i b₁) -
        residuePiAvoidCount moduli a h (Function.update σ i b₂)| ≤
      residueWidth h (moduli i) := by
  unfold residuePiAvoidCount
  rw [decodeResidue_update, decodeResidue_update]
  exact residueAvoidCount_two_update_le moduli a h
    (decodeResidue moduli σ) i (b₁.val + 1) (b₂.val + 1) hp

/-- Uniform mass on `Fin k`. -/
noncomputable def uniformFin {k : ℕ} (_ : Fin k) : ℝ :=
  (k : ℝ)⁻¹

theorem uniformFin_nonneg {k : ℕ} (a : Fin k) : 0 ≤ uniformFin a :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

theorem uniformFin_sum {k : ℕ} (hk : 0 < k) :
    ∑ a : Fin k, uniformFin a = 1 := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  simp [uniformFin, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hk0]

theorem moduli_pred_pos {n : ℕ} {moduli : Fin n → ℕ} {i : Fin n}
    (hp : 2 ≤ moduli i) : 0 < moduli i - 1 :=
  Nat.sub_pos_of_lt (lt_of_lt_of_le (by omega : (1 : ℕ) < 2) hp)

/-- Categorical product MGF for the residue survivor count, with public
widths `c_i = 2(h/p_i+1)` and uniform `Fin (p_i-1)` coordinates. -/
theorem residuePi_uniform_mgf {n : ℕ} (moduli : Fin n → ℕ) (a h : ℕ)
    (t : ℝ) (hp : ∀ i, 2 ≤ moduli i) :
    ∑ σ : (∀ i, Fin (moduli i - 1)),
        piMass (fun i => uniformFin) σ *
          Real.exp (t *
            (residuePiAvoidCount moduli a h σ -
              piExpect (fun i => uniformFin)
                (residuePiAvoidCount moduli a h)))
      ≤ Real.exp (t ^ 2 *
          (∑ i : Fin n, residueWidth (h : ℝ) (moduli i) ^ 2) / 4) := by
  refine piFin_bounded_diff_mgf n (fun i => Fin (moduli i - 1))
      (fun i => uniformFin) (residuePiAvoidCount moduli a h)
      (fun i => residueWidth (h : ℝ) (moduli i)) t ?_ ?_ ?_ ?_
  · intro i b
    exact uniformFin_nonneg b
  · intro i
    exact uniformFin_sum (moduli_pred_pos (hp i))
  · intro i
    exact residueWidth_nonneg (Nat.cast_nonneg h)
      (Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : (0 : ℕ) < 2) (hp i)))
  · intro σ i b₁ b₂
    exact residuePiAvoidCount_lipschitz moduli a h σ i b₁ b₂
      (lt_of_lt_of_le (by omega : (0 : ℕ) < 2) (hp i))

set_option maxHeartbeats 2000000 in
theorem residuePi_uniform_one_sided {n : ℕ} (moduli : Fin n → ℕ)
    (a h : ℕ) {u : ℝ} (hp : ∀ i, 2 ≤ moduli i) (hu : 0 < u) :
    ∑ σ ∈ univ.filter (fun σ : (∀ i, Fin (moduli i - 1)) =>
        u ≤ residuePiAvoidCount moduli a h σ -
          piExpect (fun i => uniformFin)
            (residuePiAvoidCount moduli a h)),
      piMass (fun i => uniformFin) σ
      ≤ if ∑ i : Fin n, residueWidth (h : ℝ) (moduli i) ^ 2 = 0 then 0
        else Real.exp (-u ^ 2 /
          ∑ i : Fin n, residueWidth (h : ℝ) (moduli i) ^ 2) := by
  have hμ0 : ∀ i (b : Fin (moduli i - 1)), 0 ≤ uniformFin b :=
    fun _ b => uniformFin_nonneg b
  have hμ1 : ∀ i, ∑ a : Fin (moduli i - 1), uniformFin a = 1 :=
    fun i => uniformFin_sum (moduli_pred_pos (hp i))
  have hc : ∀ i, 0 ≤ residueWidth (h : ℝ) (moduli i) :=
    fun i => residueWidth_nonneg (Nat.cast_nonneg h)
      (Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : (0 : ℕ) < 2) (hp i)))
  have hLip :
      ∀ (σ : ∀ i, Fin (moduli i - 1)) (i : Fin n)
        (b₁ b₂ : Fin (moduli i - 1)),
        |residuePiAvoidCount moduli a h (Function.update σ i b₁) -
            residuePiAvoidCount moduli a h (Function.update σ i b₂)| ≤
          residueWidth (h : ℝ) (moduli i) :=
    fun σ i b₁ b₂ =>
      residuePiAvoidCount_lipschitz moduli a h σ i b₁ b₂
        (lt_of_lt_of_le (by omega : (0 : ℕ) < 2) (hp i))
  exact piFin_bounded_diff_one_sided (fun i => uniformFin)
      (residuePiAvoidCount moduli a h)
      (fun i => residueWidth (h : ℝ) (moduli i)) hμ0 hμ1 hc hLip hu

/-! ### Remaining reindex: `SievePrime`/`ResidueChoice` is not `Fin n` -/

/-- One-sided product tail on an arbitrary finite index `ι` (the shape of
`ResidueChoice y = Π_{p≤y} Fin(p-1)`). This is `piFin_bounded_diff_one_sided`
after `Fintype.equivFin ι`; not a Boolean rename and not a `log p` bit
encoding. -/
def PiCoordBoundedDiffOneSided {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] [Fintype (∀ i, α i)]
    (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) (c : ι → ℝ) (u : ℝ) : Prop :=
  ∑ x ∈ univ.filter (fun x : (∀ i, α i) =>
      u ≤ F x - ∑ y : (∀ i, α i), (∏ i, μ i (y i)) * F y),
    (∏ i, μ i (x i))
    ≤
      if ∑ i : ι, c i ^ 2 = 0 then 0
      else Real.exp (-u ^ 2 / ∑ i : ι, c i ^ 2)

end PrimeGapNormality.Prime
