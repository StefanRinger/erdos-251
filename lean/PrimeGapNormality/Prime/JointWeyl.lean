import PrimeGapNormality.Prime.Independence
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.Hausdorff

/-!
# Joint Weyl criterion and common-clock Q-independence

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`rounds/round100/03_gpt_multibase_core_second_read.md`;
`rounds/round99/04_gpt_cross_base_independence_moonshot.md` §§3–4;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN

`JointWeyl` is the integer-frequency Weyl criterion for a finite family
of clocks. On a **single** integer base `B ≥ 2` it yields Q-independence
of `1, θ_i` and Weyl-normality of nonzero rational combinations.
Distinct bases do **not** imply Q-independence of the starting values
(R100/03 §4). This module does not assemble `α_2, α_4` and does not
replace `linearIndependent_one_normal_notNormal`.
-/

open Finset
open Filter (Tendsto atTop)
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 400000

/-! ### Circle-character and Cesàro helpers -/

/-- Integers map to `1` under the circle character.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
private theorem e_int (n : ℤ) : e n = 1 := by
  unfold e
  simp only [Complex.ofReal_intCast]
  have h : (2 * Real.pi * Complex.I * (n : ℂ)) = n * (2 * Real.pi * Complex.I) := by
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- `e(B^n k) = 1` for `k ∈ ℤ`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
private theorem e_nat_pow_int (B n : ℕ) (k : ℤ) :
    e ((B : ℝ) ^ n * (k : ℝ)) = 1 := by
  have h : (B : ℝ) ^ n * (k : ℝ) = (((B : ℤ) ^ n * k : ℤ) : ℝ) := by
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [h, e_int]

/-- Cesàro means of the constant `1` tend to `1`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
private theorem tendsto_one_div_nat :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (1 : ℂ)) / N) atTop (𝓝 1) := by
  have heq :
      (fun N : ℕ => (∑ n ∈ range N, (1 : ℂ)) / N) =ᶠ[atTop]
        fun _ => (1 : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
    simp [sum_const, nsmul_eq_mul, hN0]
  exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

/-- Clearing one rational against the product of all denominators.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
private theorem den_prod_clears {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℚ) (j : ι) :
    ((∏ i, (g i).den : ℕ) : ℝ) * (g j : ℝ) =
      (((g j).num * (∏ i ∈ univ.erase j, (g i).den : ℕ) : ℤ) : ℝ) := by
  have hmem : j ∈ (univ : Finset ι) := mem_univ j
  have hprod :
      (∏ i, (g i).den) = (g j).den * ∏ i ∈ univ.erase j, (g i).den :=
    (mul_prod_erase univ (fun i => (g i).den) hmem).symm
  set p : ℕ := ∏ i ∈ univ.erase j, (g i).den
  rw [hprod]
  have hcast : (((g j).den * p : ℕ) : ℝ) = ((g j).den : ℝ) * (p : ℝ) :=
    Nat.cast_mul _ _
  have hden : ((g j).den : ℝ) * (g j : ℝ) = ((g j).num : ℝ) := by
    exact_mod_cast (g j).den_mul_eq_num
  have hright :
      (((g j).num * p : ℤ) : ℝ) = ((g j).num : ℝ) * (p : ℝ) := by
    rw [Int.cast_mul, Int.cast_natCast]
  rw [hcast, hright]
  calc
    ((g j).den : ℝ) * (p : ℝ) * (g j : ℝ)
        = (((g j).den : ℝ) * (g j : ℝ)) * (p : ℝ) := by ring
    _ = ((g j).num : ℝ) * (p : ℝ) := by rw [hden]

/-- A vanishing integer multiple of a numerator forces the rational to vanish.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
private theorem rat_eq_zero_of_num_mul_dens {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℚ) (j : ι)
    (h : (g j).num * (∏ i ∈ univ.erase j, (g i).den : ℕ) = 0) :
    g j = 0 := by
  have hpos : 0 < (∏ i ∈ univ.erase j, (g i).den : ℕ) :=
    prod_pos fun i _ => (g i).den_pos
  have hden : ((∏ i ∈ univ.erase j, (g i).den : ℕ) : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr hpos.ne'
  have hnum : (g j).num = 0 := (mul_eq_zero.mp h).resolve_right hden
  exact Rat.zero_iff_num_zero.mpr hnum

/-- Transport Weyl along an equality of phases.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
private theorem weylCriterion_of_eq {b : ℕ} {θ φ : ℝ} (heq : θ = φ)
    (h : weylCriterion b θ) : weylCriterion b φ :=
  heq ▸ h

/-- Rational scalars act on `ℝ` by the coercion.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
private theorem rat_smul_real (q : ℚ) (x : ℝ) : q • x = (q : ℝ) * x := by
  simp [Algebra.smul_def]

/-! ### Joint Weyl criterion -/

/-- Integer-frequency joint Weyl criterion for a finite family of clocks.

Empty `I`: `∃ i, t i ≠ 0` is false, so the statement holds vacuously.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
def JointWeyl {I : Type*} [Fintype I] [DecidableEq I]
    (b : I → ℕ) (θ : I → ℝ) : Prop :=
  ∀ t : I → ℤ, (∃ i, t i ≠ 0) →
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
        e (∑ i : I, (t i : ℝ) * (b i : ℝ) ^ n * θ i)) / N)
      atTop (𝓝 0)

/-- A single Weyl-normal sequence is jointly Weyl on `Unit`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
theorem jointWeyl_of_weylCriterion {b : ℕ} {θ : ℝ}
    (h : weylCriterion b θ) :
    JointWeyl (fun _ : Unit => b) (fun _ => θ) := by
  intro t ht
  have hτ : t default ≠ 0 := by
    obtain ⟨i, hi⟩ := ht
    rwa [Unique.eq_default i] at hi
  have hfun :
      (fun N : ℕ =>
        (∑ n ∈ range N,
          e (∑ i : Unit, (t i : ℝ) * (b : ℝ) ^ n * θ)) / N) =
        fun N =>
          (∑ n ∈ range N, e ((t default : ℝ) * (b : ℝ) ^ n * θ)) / N := by
    funext N
    congr 1
    refine sum_congr rfl fun n _ => ?_
    have hsum :
        ∑ i : Unit, (t i : ℝ) * (b : ℝ) ^ n * θ =
          (t default : ℝ) * (b : ℝ) ^ n * θ :=
      Fintype.sum_unique _
    rw [hsum]
  rw [hfun]
  exact h (t default) hτ

/-- Factor a common power out of a joint phase.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
private theorem joint_phase_mul_pow {I : Type*} [Fintype I]
    (t : I → ℤ) (B : ℕ) (θ : I → ℝ) (n : ℕ) :
    ∑ i, (t i : ℝ) * (B : ℝ) ^ n * θ i =
      (B : ℝ) ^ n * ∑ i, (t i : ℝ) * θ i := by
  have hterm : ∀ i, (t i : ℝ) * (B : ℝ) ^ n * θ i =
      (B : ℝ) ^ n * ((t i : ℝ) * θ i) := by
    intro i
    ring
  simp_rw [hterm, ← mul_sum]

/-- Integer affine relation on a common clock is trivial.

If `t ≠ 0` then `∑ t_i θ_i = -a0 ∈ ℤ`, so each character is `1` and the
Cesàro mean is `1`, contradicting JointWeyl. If `t = 0` then `a0 = 0`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
theorem no_integer_affine_relation
    {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} (hB : 2 ≤ B) {θ : I → ℝ}
    (h : JointWeyl (fun _ : I => B) θ)
    (a0 : ℤ) (t : I → ℤ)
    (hrel : (a0 : ℝ) + ∑ i, (t i : ℝ) * θ i = 0) :
    a0 = 0 ∧ ∀ i, t i = 0 := by
  have := hB
  by_cases ht : ∃ i, t i ≠ 0
  · have hlin : ∑ i, (t i : ℝ) * θ i = - (a0 : ℝ) := by linarith
    have hone : ∀ n : ℕ,
        e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * θ i) = 1 := by
      intro n
      have hphase :
          ∑ i, (t i : ℝ) * (B : ℝ) ^ n * θ i = (B : ℝ) ^ n * (-(a0 : ℝ)) := by
        rw [joint_phase_mul_pow, hlin]
      have hneg : -(a0 : ℝ) = ((-a0 : ℤ) : ℝ) := by simp
      rw [hphase, hneg, e_nat_pow_int]
    have heq :
        (fun N : ℕ =>
          (∑ n ∈ range N,
            e (∑ i : I, (t i : ℝ) * (B : ℝ) ^ n * θ i)) / N) =
          fun N => (∑ n ∈ range N, (1 : ℂ)) / N := by
      funext N
      congr 1
      exact sum_congr rfl fun n _ => hone n
    have h0 := h t ht
    rw [heq] at h0
    exact (one_ne_zero (tendsto_nhds_unique tendsto_one_div_nat h0)).elim
  · have ht0 : ∀ i, t i = 0 := fun i => by
      by_contra hi
      exact ht ⟨i, hi⟩
    have hsum : ∑ i, (t i : ℝ) * θ i = 0 :=
      sum_eq_zero fun i _ => by simp [ht0 i]
    have ha : (a0 : ℝ) = 0 := by linarith
    exact ⟨Int.cast_eq_zero.mp ha, ht0⟩

/-- Common-clock JointWeyl implies `ℚ`-independence of `1, θ_i`.

Clear denominators, then apply `no_integer_affine_relation`. Empty `I`
reduces to independence of `{1}`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
theorem linearIndependent_one_jointWeyl
    {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} (hB : 2 ≤ B) {θ : I → ℝ}
    (h : JointWeyl (fun _ : I => B) θ) :
    LinearIndependent ℚ (fun i : Option I =>
      match i with | none => (1 : ℝ) | some i => θ i) := by
  let v : Option I → ℝ := fun i =>
    match i with
    | none => (1 : ℝ)
    | some i => θ i
  have hvnone : v none = 1 := rfl
  have hvsome : ∀ i, v (some i) = θ i := fun _ => rfl
  rw [Fintype.linearIndependent_iff]
  intro g hg x
  have hsum : ∑ j, (g j : ℝ) * v j = 0 := by
    have : ∑ j, g j • v j = 0 := hg
    simp_rw [rat_smul_real] at this
    exact this
  have hsplit :
      ∑ j, (g j : ℝ) * v j =
        (g none : ℝ) * v none + ∑ i, (g (some i) : ℝ) * v (some i) :=
    Fintype.sum_option _
  have hv : (g none : ℝ) + ∑ i, (g (some i) : ℝ) * θ i = 0 := by
    have := hsum
    rw [hsplit, hvnone, mul_one] at this
    simp_rw [hvsome] at this
    exact this
  let D : ℕ := ∏ j : Option I, (g j).den
  let a0 : ℤ := (g none).num * (∏ j ∈ univ.erase none, (g j).den : ℕ)
  let t : I → ℤ := fun i =>
    (g (some i)).num * (∏ j ∈ univ.erase (some i), (g j).den : ℕ)
  have hDnone : (D : ℝ) * (g none : ℝ) = a0 := den_prod_clears g none
  have hDi : ∀ i, (D : ℝ) * (g (some i) : ℝ) = t i := fun i =>
    den_prod_clears g (some i)
  have hrel : (a0 : ℝ) + ∑ i, (t i : ℝ) * θ i = 0 := by
    have hexp :
        (D : ℝ) * ((g none : ℝ) + ∑ i, (g (some i) : ℝ) * θ i) =
          (a0 : ℝ) + ∑ i, (t i : ℝ) * θ i := by
      rw [mul_add, hDnone, mul_sum]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, hDi i]
    have h0 :
        (D : ℝ) * ((g none : ℝ) + ∑ i, (g (some i) : ℝ) * θ i) = 0 := by
      simp [hv]
    linarith
  obtain ⟨ha0, ht⟩ := no_integer_affine_relation hB h a0 t hrel
  have hall : ∀ j : Option I, g j = 0 := by
    intro j
    cases j with
    | none => exact rat_eq_zero_of_num_mul_dens g none ha0
    | some i => exact rat_eq_zero_of_num_mul_dens g (some i) (ht i)
  exact hall x

/-- Integer combination of jointly Weyl coordinates is itself Weyl-normal.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
private theorem weylCriterion_integerCombination
    {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} {θ : I → ℝ} {t : I → ℤ}
    (h : JointWeyl (fun _ : I => B) θ) (ht : ∃ i, t i ≠ 0) :
    weylCriterion B (∑ i, (t i : ℝ) * θ i) := by
  intro τ hτ
  have ht' : ∃ i, τ * t i ≠ 0 := by
    obtain ⟨i, hi⟩ := ht
    exact ⟨i, mul_ne_zero hτ hi⟩
  have hphase : ∀ n : ℕ,
      (τ : ℝ) * (B : ℝ) ^ n * ∑ i, (t i : ℝ) * θ i =
        ∑ i, ((τ * t i : ℤ) : ℝ) * (B : ℝ) ^ n * θ i := by
    intro n
    have hterm : ∀ i,
        ((τ : ℝ) * (B : ℝ) ^ n) * ((t i : ℝ) * θ i) =
          ((τ * t i : ℤ) : ℝ) * (B : ℝ) ^ n * θ i := by
      intro i
      push_cast
      ring
    rw [mul_sum]
    exact sum_congr rfl fun i _ => hterm i
  have hfun :
      (fun N : ℕ =>
        (∑ n ∈ range N,
          e ((τ : ℝ) * (B : ℝ) ^ n * ∑ i, (t i : ℝ) * θ i)) / N) =
        fun N =>
          (∑ n ∈ range N,
            e (∑ i, ((τ * t i : ℤ) : ℝ) * (B : ℝ) ^ n * θ i)) / N := by
    funext N
    congr 1
    exact sum_congr rfl fun n _ => by rw [hphase n]
  rw [hfun]
  exact h (fun i => τ * t i) ht'

/-- A nonzero rational combination of jointly Weyl coordinates is Weyl-normal.

Clear denominators to an integer combination, then lift by
`weylCriterion_of_mul`.

Source: `rounds/round101/02_grok_multibase_common_clock_update.md` §2;
`lean/PRIME_SIGNATURES.md` JointWeyl.
Contract: API
Audit: GREEN -/
theorem weylCriterion_linearCombination
    {I : Type*} [Fintype I] [DecidableEq I]
    {B : ℕ} (hB : 2 ≤ B) {θ : I → ℝ} {q : I → ℚ}
    (h : JointWeyl (fun _ : I => B) θ) (hq : ∃ i, q i ≠ 0) :
    weylCriterion B (∑ i, (q i : ℝ) * θ i) := by
  let D : ℕ := ∏ i, (q i).den
  let t : I → ℤ := fun i =>
    (q i).num * (∏ j ∈ univ.erase i, (q j).den : ℕ)
  have hDpos : 0 < D := prod_pos fun i _ => (q i).den_pos
  have hD1 : 1 ≤ D := Nat.succ_le_of_lt hDpos
  have ht : ∃ i, t i ≠ 0 := by
    obtain ⟨k, hk⟩ := hq
    refine ⟨k, ?_⟩
    have hnum : (q k).num ≠ 0 := mt Rat.zero_iff_num_zero.mpr hk
    have hpos : 0 < (∏ j ∈ univ.erase k, (q j).den : ℕ) :=
      prod_pos fun j _ => (q j).den_pos
    have hden : ((∏ j ∈ univ.erase k, (q j).den : ℕ) : ℤ) ≠ 0 :=
      Int.natCast_ne_zero.mpr hpos.ne'
    exact mul_ne_zero hnum hden
  have hmul : ∑ i, (t i : ℝ) * θ i = (D : ℝ) * ∑ i, (q i : ℝ) * θ i := by
    have hti : ∀ i, (t i : ℝ) = (D : ℝ) * (q i : ℝ) := fun i =>
      (den_prod_clears q i).symm
    have hterm : ∀ i, (t i : ℝ) * θ i = (D : ℝ) * ((q i : ℝ) * θ i) := by
      intro i
      rw [hti i]
      ring
    simp_rw [hterm, ← mul_sum]
  have hInt : weylCriterion B (∑ i, (t i : ℝ) * θ i) :=
    weylCriterion_integerCombination h ht
  have hDθ : weylCriterion B ((D : ℝ) * ∑ i, (q i : ℝ) * θ i) :=
    weylCriterion_of_eq hmul hInt
  exact weylCriterion_of_mul hD1 hB hDθ

end PrimeGapNormality.Prime
