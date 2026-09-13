import PrimeGapNormality.Basic.Sequence
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# B-free families, survival density, enumeration, position series, normality

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §1; `lean/BFREE_SOURCE_LEDGER.md`.
Contract: API
Audit: GREEN (definitions)

Paper `a_n` is Lean `enum F (n-1)`. The Lean series with exponent `n+1` is the
paper series `∑_{n≥1} a_n b^{-n}`.
-/

open scoped Topology
set_option linter.dupNamespace false
open Classical

namespace PrimeGapNormality.BFree

open PrimeGapNormality Finset Filter

/-- An infinite pairwise coprime exclusion family with summable reciprocals.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (1);
`lean/BFREE_SIGNATURES.md`.
Contract: API
Audit: GREEN -/
structure AdmissibleFamily where
  d : ℕ → ℕ
  two_le : ∀ i, 2 ≤ d i
  pairwise_coprime : Pairwise fun i j => Nat.Coprime (d i) (d j)
  summable : Summable fun i => (1 : ℝ) / d i

/-- Positive integers divisible by no member of the family.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §1.
Contract: API
Audit: GREEN -/
def BFree (F : AdmissibleFamily) (n : ℕ) : Prop :=
  0 < n ∧ ∀ i, ¬ F.d i ∣ n

/-- Survival density as the convergent Euler product. Equal to Haar(`A`) in
`ProductRotation`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (1).
Contract: API
Audit: GREEN -/
noncomputable def rho (F : AdmissibleFamily) : ℝ :=
  ∏' i, (1 - (F.d i : ℝ)⁻¹)

/-- Canonical increasing enumeration of `BFree F`. Defined for every family;
theorems that treat it as a genuine listing take infinitude.

Source: `lean/BFREE_SIGNATURES.md`.
Contract: API
Audit: GREEN

Index: paper `a_1` is Lean `enum F 0`. -/
noncomputable def enum (F : AdmissibleFamily) : ℕ → ℕ :=
  Nat.nth (BFree F)

/-- Ordered position series. Equals paper `∑_{n≥1} a_n b^{-n}`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (2).
Contract: API
Audit: GREEN

Index: Lean exponent `n+1` with 0-based `n`. -/
noncomputable def posSeries (F : AdmissibleFamily) (b : ℕ) : ℝ :=
  ∑' n, (enum F n : ℝ) / (b : ℝ) ^ (n + 1)

/-- Ordered gap series. Paper `β_b`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (22).
Contract: C5
Audit: GREEN -/
noncomputable def gapSeries (F : AdmissibleFamily) (b : ℕ) : ℝ :=
  ∑' n, (gap (enum F) n : ℝ) / (b : ℝ) ^ (n + 1)

/-- Half-open base-`b` cylinder of length `K` and integer value `v < b^K`.
At `K = 0` this is `Ico 0 1`.

Source: `rounds/round89/04_grok_squarefree_bfree_formalisation_prompt.md` §3.
Contract: API
Audit: GREEN -/
def digitCylinder (b K v : ℕ) : Set ℝ :=
  Set.Ico ((v : ℝ) / (b : ℝ) ^ K) ((v + 1 : ℝ) / (b : ℝ) ^ K)

/-- Standard Borel normality in base `b`: every finite word has frequency
`b^{-K}` along `fract(b^n α)`. The empty word (`K = 0`) has frequency `1`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (2);
`lean/BFREE_SIGNATURES.md`.
Contract: API
Audit: GREEN -/
def IsNormal (b : ℕ) (α : ℝ) : Prop :=
  ∀ K v : ℕ, v < b ^ K →
    Tendsto (fun N : ℕ =>
      (((range N).filter (fun n =>
          Int.fract ((b : ℝ) ^ n * α) ∈ digitCylinder b K v)).card : ℝ) / N)
      atTop (𝓝 ((b : ℝ) ^ K)⁻¹)

/-! ### Elementary consequences of admissibility -/

theorem d_pos (F : AdmissibleFamily) (i : ℕ) : 0 < F.d i :=
  lt_of_lt_of_le (by decide : (0 : ℕ) < 2) (F.two_le i)

theorem d_ne_zero (F : AdmissibleFamily) (i : ℕ) : F.d i ≠ 0 :=
  (d_pos F i).ne'

theorem d_cast_ne_zero (F : AdmissibleFamily) (i : ℕ) : (F.d i : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (d_ne_zero F i)

theorem one_div_d_nonneg (F : AdmissibleFamily) (i : ℕ) :
    0 ≤ (1 : ℝ) / F.d i :=
  one_div_nonneg.mpr (Nat.cast_nonneg _)

theorem one_div_d_le_half (F : AdmissibleFamily) (i : ℕ) :
    (1 : ℝ) / F.d i ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ F.d i := Nat.cast_le.mpr (F.two_le i)
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2

theorem one_div_d_lt_one (F : AdmissibleFamily) (i : ℕ) :
    (1 : ℝ) / F.d i < 1 :=
  (one_div_d_le_half F i).trans_lt (by norm_num)

theorem one_div_d_eq_inv (F : AdmissibleFamily) (i : ℕ) :
    (1 : ℝ) / F.d i = (F.d i : ℝ)⁻¹ :=
  one_div (F.d i : ℝ)

theorem survivalFactor_pos (F : AdmissibleFamily) (i : ℕ) :
    0 < 1 - (F.d i : ℝ)⁻¹ := by
  have h : (F.d i : ℝ)⁻¹ < 1 := by
    rw [← one_div_d_eq_inv]
    exact one_div_d_lt_one F i
  linarith

theorem survivalFactor_le_one (F : AdmissibleFamily) (i : ℕ) :
    1 - (F.d i : ℝ)⁻¹ ≤ 1 := by
  have : 0 ≤ (F.d i : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  linarith

/-- Pairwise coprimality plus `d i ≥ 2` forces injectivity.

Source: `lean/BFREE_SIGNATURES.md`.
Contract: API
Audit: GREEN -/
theorem d_injective (F : AdmissibleFamily) : Function.Injective F.d := by
  intro i j h
  by_contra hij
  have hc : Nat.Coprime (F.d i) (F.d j) := F.pairwise_coprime hij
  rw [h] at hc
  have hgcd : Nat.gcd (F.d j) (F.d j) = 1 := hc
  rw [Nat.gcd_self] at hgcd
  have : 2 ≤ (1 : ℕ) := hgcd ▸ F.two_le j
  exact (by decide : ¬ 2 ≤ 1) this

theorem d_not_one (F : AdmissibleFamily) (i : ℕ) : F.d i ≠ 1 :=
  fun h => (by decide : ¬ 2 ≤ 1) (h ▸ F.two_le i)

/-- `1` survives every exclusion modulus.

Source: `lean/BFREE_SIGNATURES.md`.
Contract: API
Audit: GREEN

Index: paper `a_1 = 1`. -/
theorem bfree_one (F : AdmissibleFamily) : BFree F 1 := by
  refine ⟨Nat.succ_pos 0, fun i hdiv => ?_⟩
  have : F.d i = 1 := Nat.eq_one_of_dvd_one hdiv
  exact d_not_one F i this

theorem not_bfree_zero (F : AdmissibleFamily) : ¬ BFree F 0 := by
  intro h
  exact (lt_irrefl 0) h.1

/-- Weierstrass product inequality on a finite set.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §9 (union bound);
`lean/BFREE_SOURCE_LEDGER.md` Squarefree.
Contract: API
Audit: GREEN -/
theorem prod_one_sub_ge_one_sub_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h0s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (mem_insert_of_mem hi)
    have h1s : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (mem_insert_of_mem hi)
    have ha0 : 0 ≤ f a := h0 a (mem_insert_self a s)
    have ha1 : f a ≤ 1 := h1 a (mem_insert_self a s)
    have ih' := ih h0s h1s
    have hP : 0 ≤ ∏ i ∈ s, (1 - f i) :=
      prod_nonneg fun i hi => sub_nonneg.mpr (h1s i hi)
    have hfac : 0 ≤ 1 - f a := sub_nonneg.mpr ha1
    rw [prod_insert ha, sum_insert ha]
    have hmul : (1 - f a) * (∏ i ∈ s, (1 - f i)) ≥
        (1 - f a) * (1 - ∑ i ∈ s, f i) :=
      mul_le_mul_of_nonneg_left ih' hfac
    have hbase : 1 - (f a + ∑ i ∈ s, f i) ≤ (1 - f a) * (1 - ∑ i ∈ s, f i) := by
      have hextra : 0 ≤ f a * ∑ i ∈ s, f i :=
        mul_nonneg ha0 (sum_nonneg fun i hi => h0s i hi)
      have hexp : (1 - f a) * (1 - ∑ i ∈ s, f i) =
          1 - (f a + ∑ i ∈ s, f i) + f a * ∑ i ∈ s, f i := by ring
      linarith
    exact hbase.trans hmul

theorem multipliable_rho (F : AdmissibleFamily) :
    Multipliable fun i => (1 : ℝ) - (F.d i : ℝ)⁻¹ := by
  simpa [sub_eq_add_neg, one_div] using
    (Real.multipliable_one_add_of_summable (f := fun i => -((1 : ℝ) / F.d i))
      F.summable.neg)

/-- `1 - ∑ 1/d i ≤ ρ`. The union bound used for density thresholds.

Source: `rounds/round89/03_gpt_core_audit_and_lean_architecture.md` §3.
Contract: API
Audit: GREEN -/
theorem rho_ge_one_sub_tsum (F : AdmissibleFamily) :
    1 - ∑' i, (1 : ℝ) / F.d i ≤ rho F := by
  have hf0 : ∀ i, 0 ≤ (1 : ℝ) / F.d i := one_div_d_nonneg F
  have hf1 : ∀ i, (1 : ℝ) / F.d i ≤ 1 := fun i => (one_div_d_lt_one F i).le
  have hfin : ∀ s : Finset ℕ,
      1 - ∑' i, (1 : ℝ) / F.d i ≤ ∏ i ∈ s, (1 - (F.d i : ℝ)⁻¹) := by
    intro s
    have hsum_le : ∑ i ∈ s, (1 : ℝ) / F.d i ≤ ∑' i, (1 : ℝ) / F.d i :=
      F.summable.sum_le_tsum s (fun i _ => hf0 i)
    have hW := prod_one_sub_ge_one_sub_sum s (fun i => (1 : ℝ) / F.d i)
      (fun i _ => hf0 i) (fun i _ => hf1 i)
    have : (fun i => 1 - (F.d i : ℝ)⁻¹) = fun i => 1 - (1 : ℝ) / F.d i := by
      funext i; simp [one_div]
    simpa [this] using (le_trans (sub_le_sub_left hsum_le 1) hW)
  exact ge_of_tendsto (multipliable_rho F).hasProd (Eventually.of_forall hfin)

/-- Survival density is strictly positive.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (1);
`rounds/round92/05_grok_positive_carry_update.md` §2.
Contract: API
Audit: GREEN -/
theorem rho_pos (F : AdmissibleFamily) : 0 < rho F := by
  have hf : Summable fun i => -((1 : ℝ) / F.d i) := F.summable.neg
  have hlog := Real.summable_log_one_add_of_summable hf
  have hfn : ∀ i, 0 < (1 : ℝ) - (F.d i : ℝ)⁻¹ := survivalFactor_pos F
  have hlog' : Summable fun i => Real.log (1 - (F.d i : ℝ)⁻¹) := by
    convert hlog using 1
    ext i
    simp [sub_eq_add_neg, one_div]
  have hprod := Real.rexp_tsum_eq_tprod hfn hlog'
  rw [rho, ← hprod]
  exact Real.exp_pos _

theorem digitCylinder_empty_word (b : ℕ) :
    digitCylinder b 0 0 = Set.Ico (0 : ℝ) 1 := by
  simp [digitCylinder]

end PrimeGapNormality.BFree
